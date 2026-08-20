import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Set.Defs

set_option linter.all false

def relu_activation (t : ℝ) : ℝ := max 0 t

structure affine_layer (inputDim outputDim : ℕ) where
  weights : Matrix (Fin outputDim) (Fin inputDim) ℝ
  bias : Fin outputDim → ℝ

def affine_layer_apply {inputDim outputDim : ℕ}
    (layer : affine_layer inputDim outputDim) (x : Fin inputDim → ℝ) :
    Fin outputDim → ℝ :=
  fun j => Matrix.mulVec layer.weights x j + layer.bias j

def relu_affine_layer_apply {inputDim outputDim : ℕ}
    (layer : affine_layer inputDim outputDim) (x : Fin inputDim → ℝ) :
    Fin outputDim → ℝ :=
  fun j => relu_activation (affine_layer_apply layer x j)

inductive fully_connected_relu_network : ℕ → ℕ → Type
  | output {inputDim : ℕ} (layer : affine_layer inputDim 1) :
      fully_connected_relu_network inputDim 1
  | hidden {inputDim hiddenDim depth : ℕ}
      (layer : affine_layer inputDim hiddenDim)
      (tail : fully_connected_relu_network hiddenDim depth) :
      fully_connected_relu_network inputDim (depth + 1)

def fully_connected_relu_network_eval :
    {inputDim depth : ℕ} → fully_connected_relu_network inputDim depth →
      (Fin inputDim → ℝ) → ℝ
  | _, _, .output layer, x => affine_layer_apply layer x 0
  | _, _, .hidden layer tail, x =>
      fully_connected_relu_network_eval tail (relu_affine_layer_apply layer x)

def fully_connected_relu_network_width :
    {inputDim depth : ℕ} → fully_connected_relu_network inputDim depth → ℕ
  | _, _, .output _ => 0
  | _, _, .hidden (hiddenDim := hiddenDim) _ tail =>
      max hiddenDim (fully_connected_relu_network_width tail)

noncomputable def coordinate_maximum {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin d)).Nonempty then
    Finset.univ.sup' h x
  else
    0

def unit_hypercube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.Icc (fun _ => 0) (fun _ => 1)

noncomputable def depth_width_lower_bound (d k : ℕ) : ℝ :=
  (1 / 10 : ℝ) *
    Real.rpow (d : ℝ) (1 + 1 / ((2 : ℝ) ^ (k - 2) - 1))

theorem depthk {d k : ℕ}
    (network : fully_connected_relu_network d k)
    (depth_lower : 3 ≤ k)
    (depth_upper : (k : ℝ) ≤ Real.logb 2 (Real.logb 2 (d : ℝ)))
    (computes_maximum : ∀ x ∈ unit_hypercube d,
      fully_connected_relu_network_eval network x = coordinate_maximum x) :
    depth_width_lower_bound d k ≤ (fully_connected_relu_network_width network : ℝ) := by sorry
