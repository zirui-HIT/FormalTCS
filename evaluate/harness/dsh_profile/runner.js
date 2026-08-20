/**
 * Resumable one-turn driver for the Evaluate benchmark harness.
 *
 * `@deepseek-ai/dsh-headless` always mints a fresh random session id, so a
 * plain `dsh --profile headless` invocation cannot continue an earlier
 * conversation. This plugin mirrors that runner but takes the session id from
 * the caller: the first turn creates the session, every later turn resumes it
 * through the persistence backend so the model sees the whole prior log.
 *
 * All inputs arrive through the environment, so nothing turn-specific has to be
 * baked into the profile's patch layer:
 *   DSH_EVAL_SESSION_ID   caller-owned session id, stable across turns
 *   DSH_EVAL_RESUME       "1" resumes the persisted session, anything else creates it
 *   DSH_EVAL_PROMPT_FILE  UTF-8 file holding this turn's task text
 *   DSH_EVAL_RESULT_FILE  where the machine-readable turn result is written
 *
 * The result file is the contract with the Python adapter; stdout stays
 * human-readable (the final assistant text, as headless prints it).
 *
 * @module Evaluate/harness/dsh_profile/runner
 */

import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";

import { installModelSelection } from "@deepseek-ai/dsh-agent";
import { createUserMessage } from "@deepseek-ai/dsh-llm";
import { SessionId } from "@deepseek-ai/dsh-session";

/** Stable Cordis plugin name. */
export const name = "evaluate-runner";

/** Core services the turn needs before it can start. */
export const inject = ["agentDefaultModel", "agents", "sessions"];

/** Process streams the runner writes to. */
const internals = {
	stdout: process.stdout,
	stderr: process.stderr,
};

/** Zero-valued usage record in the benchmark's four-field shape. */
function emptyUsage() {
	return {
		input_tokens: 0,
		cache_creation_input_tokens: 0,
		cache_read_input_tokens: 0,
		output_tokens: 0,
	};
}

/**
 * Read one required environment value.
 * @param key - environment variable name.
 * @returns the value.
 * @throws when the variable is unset or empty.
 */
function requireEnv(key) {
	const value = process.env[key];
	if (value === undefined || value === "") throw new Error(`evaluate-runner: ${key} is not set`);
	return value;
}

/**
 * Fold this turn's assistant messages into the final text, the turn outcome and
 * the accumulated token usage.
 *
 * Only events at or after `firstSeq` belong to this turn, which keeps a resumed
 * session from re-reporting the tokens earlier turns already billed.
 * @param events - the session's durable log.
 * @param firstSeq - sequence number the turn started at.
 * @returns the last assistant text, the turn-end reason, and summed usage.
 */
function summarize(events, firstSeq) {
	let started = false;
	let text = "";
	let reason;
	const usage = emptyUsage();
	for (const event of events) {
		if (event.seq < firstSeq) continue;
		if (event.type === "turn/start") {
			started = true;
			continue;
		}
		if (!started) continue;
		if (event.type === "assistant/message") {
			const joined = event.data.message.content
				.filter((block) => block.type === "text")
				.map((block) => block.text)
				.join("");
			if (joined !== "") text = joined;
			const step = event.data.usage;
			if (step !== undefined) {
				usage.input_tokens += step.inputTokens ?? 0;
				usage.output_tokens += step.outputTokens ?? 0;
				usage.cache_read_input_tokens += step.cacheReadTokens ?? 0;
				usage.cache_creation_input_tokens += step.cacheWriteTokens ?? 0;
			}
		}
		if (event.type === "turn/end") reason = event.data.reason;
	}
	return { text, reason, usage };
}

/**
 * Persist the turn result where the Python adapter reads it.
 * @param path - destination file.
 * @param payload - the JSON-serializable turn result.
 */
function writeResult(path, payload) {
	mkdirSync(dirname(path), { recursive: true });
	writeFileSync(path, JSON.stringify(payload) + "\n", "utf8");
}

/**
 * Create or resume the caller's session, run one turn on it, and record the
 * outcome.
 * @param ctx - plugin context carrying the agent registry, default model and sessions.
 * @param io - process-facing effects (streams plus the launcher's exit request).
 */
async function run(ctx, io) {
	await ctx.get("loader")?.await();
	const agents = ctx.get("agents");
	const defaultModel = ctx.get("agentDefaultModel");
	const sessions = ctx.get("sessions");
	if (agents === undefined || defaultModel === undefined || sessions === undefined) {
		throw new Error("evaluate-runner: agents, agentDefaultModel and sessions must all be available");
	}
	const id = requireEnv("DSH_EVAL_SESSION_ID");
	const resultFile = requireEnv("DSH_EVAL_RESULT_FILE");
	const task = readFileSync(requireEnv("DSH_EVAL_PROMPT_FILE"), "utf8");
	const resume = process.env.DSH_EVAL_RESUME === "1";
	const selection = defaultModel.currentSelection();
	const agentOptions = { provider: selection.provider, model: selection.model };
	const setup = (agentCtx) => {
		installModelSelection(agentCtx, { current: selection, assembled: undefined });
	};
	const sessionId = SessionId(id);
	const { agent } = resume
		? await agents.resume({ resumeSessionId: sessionId, agentOptions, setup })
		: await agents.create({ sessionId, meta: { cwd: process.cwd() }, agentOptions, setup });
	await agent.whenIdle();
	const firstSeq = agent.session.seq;
	agent.followup(
		createUserMessage({ content: [{ type: "text", text: task }], source: { kind: "user" } }),
	);
	await agent.whenIdle();
	await sessions.flush(agent.session);
	const outcome = summarize(agent.session.events, firstSeq);
	const completed = outcome.reason?.kind === "completed";
	const error =
		outcome.reason?.kind === "error"
			? { code: outcome.reason.error.code, message: outcome.reason.error.message }
			: outcome.reason === undefined
				? { code: "NO_TURN", message: "the turn produced no turn/end event" }
				: { code: String(outcome.reason.kind).toUpperCase(), message: `turn ended as "${outcome.reason.kind}"` };
	writeResult(resultFile, {
		status: completed ? "completed" : "failed",
		text: outcome.text,
		session_id: id,
		usage: outcome.usage,
		...(completed ? {} : { error }),
	});
	io.stdout.write(outcome.text + "\n");
	if (!completed) io.stderr.write(`dsh: ${error.code}: ${error.message}\n`);
	io.exit(completed ? 0 : 1);
}

/**
 * Mount the resumable one-turn driver.
 * @param ctx - plugin context; the launcher must have provided `appExit`.
 */
export function apply(ctx) {
	const exit = ctx.get("appExit");
	if (exit === undefined) throw new Error("evaluate-runner: the launcher must provide ctx.appExit before the tree mounts");
	const io = { stdout: internals.stdout, stderr: internals.stderr, exit };
	run(ctx, io).catch((error) => {
		const message = error instanceof Error ? error.message : String(error);
		io.stderr.write(`dsh: ${message}\n`);
		const resultFile = process.env.DSH_EVAL_RESULT_FILE;
		if (resultFile !== undefined && resultFile !== "") {
			try {
				writeResult(resultFile, {
					status: "failed",
					text: "",
					session_id: process.env.DSH_EVAL_SESSION_ID ?? "",
					usage: emptyUsage(),
					error: { code: "RUNNER_FAILED", message },
				});
			} catch {
				/* the adapter falls back to the process exit code and the transcript */
			}
		}
		io.exit(1);
	});
}
