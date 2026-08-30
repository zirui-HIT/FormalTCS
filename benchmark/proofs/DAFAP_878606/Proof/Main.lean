import Architect
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.RepresentationTheory.Invariants

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory ENNReal

@[blueprint "def:l2-orthonormal-family"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space and let $r\in\mathbb N$. A family
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ of real-valued functions on $\mathcal X$ is
  \emph{$L^2(\mathcal X,\mu)$-orthonormal} if
  \[
    \int_{\mathcal X}\varphi_\ell(x)\,\varphi_{\ell'}(x)\,d\mu(x)=\delta_{\ell\ell'}
    \qquad\text{for all }\ell,\ell'\in[r],
  \]
  where $\delta_{\ell\ell'}$ equals $1$ if $\ell=\ell'$ and $0$ otherwise. The linear span of such a
  family is an $r$-dimensional subspace $\mathcal F\subset L^2(\mathcal X,\mu)$, and every subspace
  considered in this blueprint is presented in this way. -/)
  (title := /-- Orthonormal family in $L^2(\mathcal X,\mu)$ -/)
  (latexEnv := "definition")]
def l2_orthonormal_family {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) : Prop :=
  ∀ l l' : Fin r, ∫ x, phi l x * phi l' x ∂mu = if l = l' then 1 else 0

@[blueprint "def:coeff-to-fun"
  (statement := /-- Let $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be a family of real-valued functions on
  $\mathcal X$. For a coefficient vector $c\in\mathbb R^r$, viewed as an element of the Euclidean
  space $\ell^2([r])$, the associated element of the span of $\varphi$ is
  \[
    \iota_\varphi(c):\mathcal X\to\mathbb R,\qquad
    \iota_\varphi(c)(x):=\sum_{\ell=1}^r c_\ell\,\varphi_\ell(x).
  \]
  When $\varphi$ is $L^2$-orthonormal in the sense of \cref{def:l2-orthonormal-family}, the map
  $\iota_\varphi$ is a linear isometry from $\mathbb R^r$ onto $\mathcal F$, so coefficient vectors
  are a faithful representation of elements of $\mathcal F$. -/)
  (title := /-- Synthesis map from coefficients to functions -/)
  (latexEnv := "definition")]
noncomputable def coeff_to_fun {X : Type*} {r : ℕ} (phi : Fin r → X → ℝ)
    (c : EuclideanSpace ℝ (Fin r)) : X → ℝ :=
  fun x => ∑ l, c l * phi l x

@[blueprint "def:l2-sq-dist"
  (statement := /-- Let $\mu$ be a measure on $\mathcal X$, let $\varphi=(\varphi_\ell)_{\ell\in[r]}$
  be a family of real-valued functions on $\mathcal X$, and let $c,d\in\mathbb R^r$. The squared
  $L^2(\mathcal X,\mu)$ distance between the corresponding elements of the span of $\varphi$ is
  \[
    D_{\mu,\varphi}(c,d):=\int_{\mathcal X}\bigl(\iota_\varphi(c)(x)-\iota_\varphi(d)(x)\bigr)^2\,d\mu(x),
  \]
  with $\iota_\varphi$ as in \cref{def:coeff-to-fun}. All error quantities in the main theorems are
  expressed through this quantity, so they are genuine $L^2(\mathcal X)$ errors. -/)
  (title := /-- Squared $L^2(\mathcal X)$ distance of two coefficient vectors -/)
  (latexEnv := "definition")]
noncomputable def l2_sq_dist {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (c d : EuclideanSpace ℝ (Fin r)) : ℝ :=
  ∫ x, (coeff_to_fun phi c x - coeff_to_fun phi d x) ^ 2 ∂mu

@[blueprint "def:target-coeff"
  (statement := /-- Let $\mu$ be a measure on $\mathcal X$, let $\varphi=(\varphi_\ell)_{\ell\in[r]}$
  be $L^2(\mathcal X,\mu)$-orthonormal in the sense of \cref{def:l2-orthonormal-family}, and let
  $f^\star:\mathcal X\to\mathbb R$. The coefficient vector of the $L^2(\mathcal X)$-orthogonal
  projection $\Pi_{\mathcal F}f^\star$ onto $\mathcal F=\operatorname{span}\varphi$ is
  \[
    \theta(f^\star)\in\mathbb R^r,\qquad
    \theta(f^\star)_\ell:=\langle f^\star,\varphi_\ell\rangle_{L^2(\mathcal X)}
    =\int_{\mathcal X}f^\star(x)\,\varphi_\ell(x)\,d\mu(x).
  \]
  Thus $\iota_\varphi(\theta(f^\star))=\Pi_{\mathcal F}f^\star$, the intermediate target denoted
  $f_{\mathcal F}$ in the source proof. -/)
  (title := /-- Coefficients of the projected target $\Pi_{\mathcal F}f^\star$ -/)
  (latexEnv := "definition")]
noncomputable def target_coeff {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (fstar : X → ℝ) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun l => ∫ x, fstar x * phi l x ∂mu

@[blueprint "def:density-coeff-estimator"
  (statement := /-- Let $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be a family of real-valued functions on
  $\mathcal X$ and let $x_1,\dots,x_n\in\mathcal X$. The \emph{projection density estimator} is the
  element of $\mathcal F$ with coefficient vector
  \[
    \widehat\theta\in\mathbb R^r,\qquad
    \widehat\theta_\ell:=\frac1n\sum_{i=1}^n\varphi_\ell(x_i),
  \]
  that is, $\widehat f=\iota_\varphi(\widehat\theta)=\sum_{\ell=1}^r\widehat\theta_\ell\varphi_\ell$
  with $\iota_\varphi$ as in \cref{def:coeff-to-fun}. -/)
  (title := /-- Projection density estimator (coefficient form) -/)
  (latexEnv := "definition")]
noncomputable def density_coeff_estimator {X : Type*} {r : ℕ} (phi : Fin r → X → ℝ) {n : ℕ}
    (xs : Fin n → X) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun l => (n : ℝ)⁻¹ * ∑ i, phi l (xs i)

@[blueprint "def:regression-coeff-estimator"
  (statement := /-- Let $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be a family of real-valued functions on
  $\mathcal X$, let $f^\star:\mathcal X\to\mathbb R$, and let
  $(x_1,\varepsilon_1),\dots,(x_n,\varepsilon_n)\in\mathcal X\times\mathbb R$, so that the observed
  responses are $y_i=f^\star(x_i)+\varepsilon_i$. The \emph{projection regression estimator} is the
  element of $\mathcal F$ with coefficient vector
  \[
    \widehat\beta\in\mathbb R^r,\qquad
    \widehat\beta_\ell:=\frac1n\sum_{i=1}^n y_i\,\varphi_\ell(x_i)
    =\frac1n\sum_{i=1}^n\bigl(f^\star(x_i)+\varepsilon_i\bigr)\varphi_\ell(x_i),
  \]
  that is, $\widehat f=\iota_\varphi(\widehat\beta)$ with $\iota_\varphi$ as in
  \cref{def:coeff-to-fun}. Representing a sample as the pair $(x_i,\varepsilon_i)$ rather than
  $(x_i,y_i)$ makes the independence of the design point and the noise explicit. -/)
  (title := /-- Projection regression estimator (coefficient form) -/)
  (latexEnv := "definition")]
noncomputable def regression_coeff_estimator {X : Type*} {r : ℕ} (phi : Fin r → X → ℝ)
    (fstar : X → ℝ) {n : ℕ} (zs : Fin n → X × ℝ) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun l => (n : ℝ)⁻¹ * ∑ i, (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1)

@[blueprint "def:augmented-density-coeff-estimator"
  (statement := /-- Let $G$ be a group acting on $\mathcal X$, let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be a family of real-valued functions on $\mathcal X$, let
  $S=(g_1,\dots,g_{|S|})\in G^{|S|}$ and let $x_1,\dots,x_n\in\mathcal X$. Augmenting each sample
  $x_i$ by its transformed copies $\{gx_i:g\in S\}$ and forming the projection density
  estimator of \cref{def:density-coeff-estimator} on the resulting $n|S|$ points gives the
  coefficient vector
  \[
    \widehat\theta^{\,S}\in\mathbb R^r,\qquad
    \widehat\theta^{\,S}_\ell:=\frac{1}{n|S|}\sum_{i=1}^n\sum_{j=1}^{|S|}\varphi_\ell(g_jx_i),
  \]
  and $\widehat f_S:=\iota_\varphi(\widehat\theta^{\,S})$. This is the augmentation convention of
  the target theorem, in which each sample $x_i$ is replaced by the copies $\{gx_i:g\in S\}$. When
  $S$ is an i.i.d. uniform sample from a finite group $G$, the tuple
  $(g_1^{-1},\dots,g_{|S|}^{-1})$ has the same law as $S$, because $g\mapsto g^{-1}$ is a bijection
  of $G$ and therefore preserves the uniform distribution; hence the estimator formed from the
  copies $\{g^{-1}x_i:g\in S\}$ has the same distribution as $\widehat\theta^{\,S}$, and the two
  conventions yield the same expected errors in every statement below. -/)
  (title := /-- Partially augmented projection density estimator -/)
  (latexEnv := "definition")]
noncomputable def augmented_density_coeff_estimator {X : Type*} {G : Type*} [Group G]
    [MulAction G X] {r : ℕ} (phi : Fin r → X → ℝ) {m n : ℕ} (S : Fin m → G) (xs : Fin n → X) :
    EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun l => ((n : ℝ) * (m : ℝ))⁻¹ * ∑ i, ∑ j, phi l (S j • xs i)

@[blueprint "def:augmented-regression-coeff-estimator"
  (statement := /-- Let $G$ be a group acting on $\mathcal X$, let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be a family of real-valued functions on $\mathcal X$, let
  $f^\star:\mathcal X\to\mathbb R$, let $S=(g_1,\dots,g_{|S|})\in G^{|S|}$, and let
  $(x_1,\varepsilon_1),\dots,(x_n,\varepsilon_n)\in\mathcal X\times\mathbb R$ with
  $y_i=f^\star(x_i)+\varepsilon_i$. Augmenting each design point $x_i$ by
  $\{gx_i:g\in S\}$ while keeping its response $y_i$, and forming the projection regression
  estimator of \cref{def:regression-coeff-estimator}, gives the coefficient vector
  \[
    \widehat\beta^{\,S}\in\mathbb R^r,\qquad
    \widehat\beta^{\,S}_\ell:=\frac{1}{n|S|}\sum_{i=1}^n\sum_{j=1}^{|S|}y_i\,\varphi_\ell(g_jx_i),
  \]
  and $\widehat f_S:=\iota_\varphi(\widehat\beta^{\,S})$. The augmentation convention is the one
  used in \cref{def:augmented-density-coeff-estimator}. -/)
  (title := /-- Partially augmented projection regression estimator -/)
  (latexEnv := "definition")]
noncomputable def augmented_regression_coeff_estimator {X : Type*} {G : Type*} [Group G]
    [MulAction G X] {r : ℕ} (phi : Fin r → X → ℝ) (fstar : X → ℝ) {m n : ℕ} (S : Fin m → G)
    (zs : Fin n → X × ℝ) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun l =>
    ((n : ℝ) * (m : ℝ))⁻¹ * ∑ i, ∑ j, (fstar (zs i).1 + (zs i).2) * phi l (S j • (zs i).1)

@[blueprint "def:group-average-operator"
  (statement := /-- Let $G$ be a finite group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be a
  representation of $G$ on the Euclidean space $\mathbb R^r$. The \emph{full averaging operator} is
  \[
    \Pi_G:\mathbb R^r\to\mathbb R^r,\qquad
    \Pi_G c:=\frac{1}{|G|}\sum_{g\in G}\rho(g)c
    =\mathbb E_{g\sim\mathrm{Unif}(G)}\bigl[\rho(g)c\bigr].
  \]
  This is the coefficient-space form of the operator $\Pi_G=\mathbb E_g[T_g]$ of the source proof. -/)
  (title := /-- Full group-averaging operator $\Pi_G$ -/)
  (latexEnv := "definition")]
noncomputable def group_average_operator {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (c : EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℝ (Fin r) :=
  ((Fintype.card G : ℝ))⁻¹ • ∑ g : G, rho g c

@[blueprint "def:empirical-average-operator"
  (statement := /-- Let $G$ be a group, let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be a representation of
  $G$ on $\mathbb R^r$, and let $S=(g_1,\dots,g_{|S|})\in G^{|S|}$. The \emph{empirical averaging
  operator} associated with $S$ is
  \[
    \Pi_S:\mathbb R^r\to\mathbb R^r,\qquad
    \Pi_S c:=\frac{1}{|S|}\sum_{j=1}^{|S|}\rho(g_j)c .
  \]
  This is the coefficient-space form of the operator
  $\Pi_S=\frac{1}{|S|}\sum_{g\in S}T_g$ of the source proof. -/)
  (title := /-- Empirical averaging operator $\Pi_S$ -/)
  (latexEnv := "definition")]
noncomputable def empirical_average_operator {G : Type*} [Group G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) {m : ℕ} (S : Fin m → G)
    (c : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℝ (Fin r) :=
  (m : ℝ)⁻¹ • ∑ j, rho (S j) c

@[blueprint "def:invariant-projection"
  (statement := /-- Let $G$ be a group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be a
  representation of $G$ on the Euclidean space $\mathbb R^r$. Let
  \[
    (\mathbb R^r)^G:=\{c\in\mathbb R^r:\rho(g)c=c\ \text{for all }g\in G\}
  \]
  be the subspace of invariant vectors, which is the coefficient-space form of
  $\mathcal F^G$. Since $(\mathbb R^r)^G$ is a finite-dimensional, hence closed, subspace of a
  Hilbert space, the orthogonal projection onto it exists; we write
  $\Pi_{\mathcal F^G}:\mathbb R^r\to\mathbb R^r$ for this orthogonal projection. -/)
  (title := /-- Orthogonal projection onto the invariant subspace -/)
  (latexEnv := "definition")]
noncomputable def invariant_projection {G : Type*} [Group G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) :
    EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
  rho.invariants.starProjection

@[blueprint "def:orthogonal-representation"
  (statement := /-- Let $G$ be a group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be a
  representation of $G$ on the Euclidean space $\mathbb R^r$. We say that $\rho$ is
  \emph{orthogonal}, equivalently that it is a unitary representation, if
  \[
    \|\rho(g)c\|=\|c\|\qquad\text{for all }g\in G\text{ and all }c\in\mathbb R^r .
  \]
  This is the hypothesis referred to in the source proof by the phrase ``the action is
  isometric''. -/)
  (title := /-- Orthogonal (unitary) representation -/)
  (latexEnv := "definition")]
def orthogonal_representation {G : Type*} [Group G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) : Prop :=
  ∀ (g : G) (c : EuclideanSpace ℝ (Fin r)), ‖rho g c‖ = ‖c‖

@[blueprint "def:implements-lifted-action"
  (statement := /-- Let $G$ be a group acting on $\mathcal X$, let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be a family of real-valued functions on
  $\mathcal X$, and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be a representation of $G$ on
  $\mathbb R^r$. We say that $\rho$ \emph{implements the lifted action} on
  $\mathcal F=\operatorname{span}\varphi$ if
  \[
    \iota_\varphi(\rho(g)c)(x)=\iota_\varphi(c)(g^{-1}x)
    \qquad\text{for every }g\in G,\ c\in\mathbb R^r\text{ and }x\in\mathcal X,
  \]
  with $\iota_\varphi$ as in
  \cref{def:coeff-to-fun}. This single hypothesis encodes both that $\mathcal F$ is closed under the
  action of $G$, that is $T_gf\in\mathcal F$ for all $f\in\mathcal F$ and $g\in G$ where
  $(T_gf)(x)=f(g^{-1}x)$, and that $\rho(g)$ is the matrix of $T_g$ in the basis $\varphi$. The
  identity is imposed at every point $x\in\mathcal X$ rather than only $\mu$-almost everywhere,
  because the estimators of \cref{def:density-coeff-estimator} and
  \cref{def:augmented-density-coeff-estimator} evaluate the functions $\varphi_\ell$ at the
  individual sample points $x_i$ and at their transformed copies $g_jx_i$; an identity valid only
  off a $\mu$-null set carries no information at those prescribed points, and consequently does not
  relate the two estimators. Every representation-theoretic construction of $\mathcal F$ from a
  basis $\varphi$ satisfies the pointwise identity, so this is the form in which the closedness of
  $\mathcal F$ under $G$ is used throughout. -/)
  (title := /-- Coefficient representation of the lifted action $T_g$ -/)
  (latexEnv := "definition")]
def implements_lifted_action {X : Type*} {G : Type*} [Group G]
    [MulAction G X] {r : ℕ} (phi : Fin r → X → ℝ)
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) : Prop :=
  ∀ (g : G) (c : EuclideanSpace ℝ (Fin r)) (x : X),
    coeff_to_fun phi (rho g c) x = coeff_to_fun phi c (g⁻¹ • x)

@[blueprint "def:iid-expectation"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$, let
  $n\in\mathbb N$, and let $\Psi:\mathcal Y^n\to\mathbb R$. The expectation of $\Psi$ under $n$
  independent identically distributed draws from $\nu$ is
  \[
    \mathbb E_{y_{1:n}\stackrel{\text{i.i.d.}}{\sim}\nu}\bigl[\Psi(y_1,\dots,y_n)\bigr]
    :=\int_{\mathcal Y^n}\Psi\,d\nu^{\otimes n},
  \]
  where $\nu^{\otimes n}$ is the $n$-fold product measure. -/)
  (title := /-- Expectation under an i.i.d. sample -/)
  (latexEnv := "definition")]
noncomputable def iid_expectation {Y : Type*} [MeasurableSpace Y] (nu : Measure Y) (n : ℕ)
    (Psi : (Fin n → Y) → ℝ) : ℝ :=
  ∫ ys, Psi ys ∂(Measure.pi fun _ : Fin n => nu)

@[blueprint "def:uniform-group-expectation"
  (statement := /-- Let $G$ be a finite nonempty group, let $m\in\mathbb N$, and let
  $\Psi:G^m\to\mathbb R$. The expectation of $\Psi$ under $m$ independent draws from the uniform
  distribution on $G$ is
  \[
    \mathbb E_{S\sim\mathrm{Unif}(G)^{\otimes m}}[\Psi(S)]
    :=\frac{1}{|G|^m}\sum_{S\in G^m}\Psi(S).
  \]
  Here $S=(g_1,\dots,g_m)$ ranges over all $m$-tuples of elements of $G$, so that the augmentation
  set of the main theorem is an i.i.d. uniform sample of size $m=|S|$. -/)
  (title := /-- Expectation over an i.i.d. uniform augmentation set -/)
  (latexEnv := "definition")]
noncomputable def uniform_group_expectation {G : Type*} [Fintype G] (m : ℕ)
    (Psi : (Fin m → G) → ℝ) : ℝ :=
  ((Fintype.card G : ℝ) ^ m)⁻¹ * ∑ S : Fin m → G, Psi S

@[blueprint "def:centered-noise"
  (statement := /-- Let $\eta$ be a measure on $\mathbb R$ and let $\sigma\in\mathbb R$. We say that
  $\eta$ is a \emph{centered noise law with variance $\sigma^2$} if $\eta$ is a probability measure,
  the functions $e\mapsto e$ and $e\mapsto e^2$ are $\eta$-integrable, and
  \[
    \int_{\mathbb R}e\,d\eta(e)=0,
    \qquad
    \int_{\mathbb R}e^2\,d\eta(e)=\sigma^2 .
  \]
  In the regression model the noise variables $\varepsilon_1,\dots,\varepsilon_n$ are i.i.d. draws
  from $\eta$, independent of the design points, which is enforced by sampling each pair
  $(x_i,\varepsilon_i)$ from the product measure $\mu\otimes\eta$. -/)
  (title := /-- Centered noise law with variance $\sigma^2$ -/)
  (latexEnv := "definition")]
def centered_noise (eta : Measure ℝ) (sigma : ℝ) : Prop :=
  IsProbabilityMeasure eta ∧
    (∫ e, e ∂eta) = 0 ∧
    (∫ e, e ^ 2 ∂eta) = sigma ^ 2 ∧
    Integrable (fun e : ℝ => e) eta ∧
    Integrable (fun e : ℝ => e ^ 2) eta

@[blueprint "lem:sq-sum-mul-eq-double-sum"
  (statement := /-- Let $r\in\mathbb N$ and let $e,\psi:[r]\to\mathbb R$ be real-valued families.
  Then
  \[
    \Bigl(\sum_{\ell=1}^re_\ell\psi_\ell\Bigr)^2
    =\sum_{\ell=1}^r\sum_{\ell'=1}^re_\ell e_{\ell'}\,\psi_\ell\psi_{\ell'} .
  \]
  -/)
  (proof := /-- Writing the square as a product of the sum with itself and expanding the product of
  the two finite sums by distributivity gives
  \[
    \Bigl(\sum_{\ell=1}^re_\ell\psi_\ell\Bigr)^2
    =\Bigl(\sum_{\ell=1}^re_\ell\psi_\ell\Bigr)\Bigl(\sum_{\ell'=1}^re_{\ell'}\psi_{\ell'}\Bigr)
    =\sum_{\ell=1}^r\sum_{\ell'=1}^r(e_\ell\psi_\ell)(e_{\ell'}\psi_{\ell'}).
  \]
  For each fixed pair $(\ell,\ell')$ the commutativity and associativity of multiplication in
  $\mathbb R$ give
  $(e_\ell\psi_\ell)(e_{\ell'}\psi_{\ell'})=e_\ell e_{\ell'}\,\psi_\ell\psi_{\ell'}$, so the two
  double sums agree term by term. -/)
  (title := /-- Square of a finite linear combination as a double sum -/)
  (latexEnv := "lemma")]
lemma sq_sum_mul_eq_double_sum {r : ℕ} (e psi : Fin r → ℝ) :
    (∑ l, e l * psi l) ^ 2 = ∑ l, ∑ l', e l * e l' * (psi l * psi l') := by
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun l' _ => by ring

@[blueprint "lem:l2-sq-dist-eq-gram-sum"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space, let $r\in\mathbb N$, and let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be a family of real-valued functions with
  $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every $\ell\in[r]$. Then for all coefficient vectors
  $c,d\in\mathbb R^r$ the squared $L^2(\mathcal X)$ distance of \cref{def:l2-sq-dist} expands as
  \[
    D_{\mu,\varphi}(c,d)
    =\sum_{\ell=1}^r\sum_{\ell'=1}^r(c_\ell-d_\ell)(c_{\ell'}-d_{\ell'})
      \int_{\mathcal X}\varphi_\ell(x)\varphi_{\ell'}(x)\,d\mu(x).
  \]
  -/)
  (proof := /-- Fix $\ell,\ell'\in[r]$. Since $\varphi_\ell$ and $\varphi_{\ell'}$ both lie in
  $L^2(\mathcal X,\mu)$ and $\tfrac12+\tfrac12=1$, the Hölder inequality shows that the product
  $\varphi_\ell\varphi_{\ell'}$ lies in $L^1(\mathcal X,\mu)$, that is, it is $\mu$-integrable;
  consequently so is every constant multiple of it, and hence so is each of the finite sums
  $x\mapsto\sum_{\ell'=1}^r(c_\ell-d_\ell)(c_{\ell'}-d_{\ell'})\varphi_\ell(x)\varphi_{\ell'}(x)$.

  Next we expand the integrand pointwise. Fix $x\in\mathcal X$. By \cref{def:coeff-to-fun} and
  linearity of finite sums,
  \[
    \iota_\varphi(c)(x)-\iota_\varphi(d)(x)
    =\sum_{\ell=1}^rc_\ell\varphi_\ell(x)-\sum_{\ell=1}^rd_\ell\varphi_\ell(x)
    =\sum_{\ell=1}^r(c_\ell-d_\ell)\varphi_\ell(x),
  \]
  so applying \cref{lem:sq-sum-mul-eq-double-sum} with $e_\ell:=c_\ell-d_\ell$ and
  $\psi_\ell:=\varphi_\ell(x)$ yields
  \[
    \bigl(\iota_\varphi(c)(x)-\iota_\varphi(d)(x)\bigr)^2
    =\sum_{\ell=1}^r\sum_{\ell'=1}^r(c_\ell-d_\ell)(c_{\ell'}-d_{\ell'})
      \varphi_\ell(x)\varphi_{\ell'}(x).
  \]
  Integrating this identity and using the integrability established above, the integral of the
  finite double sum may be taken term by term, and the constants
  $(c_\ell-d_\ell)(c_{\ell'}-d_{\ell'})$ may be pulled out of each integral. This gives exactly the
  asserted formula for $D_{\mu,\varphi}(c,d)$ as defined in \cref{def:l2-sq-dist}. -/)
  (title := /-- Gram expansion of the squared $L^2$ distance -/)
  (latexEnv := "lemma")]
lemma l2_sq_dist_eq_gram_sum {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (hmem : ∀ l, MemLp (phi l) 2 mu) (c d : EuclideanSpace ℝ (Fin r)) :
    l2_sq_dist mu phi c d
      = ∑ l, ∑ l', (c l - d l) * (c l' - d l') * ∫ x, phi l x * phi l' x ∂mu := by
  have hint : ∀ l l' : Fin r, Integrable (fun x => phi l x * phi l' x) mu :=
    fun l l' => (hmem l).integrable_mul (hmem l')
  have hpt : ∀ x : X, (coeff_to_fun phi c x - coeff_to_fun phi d x) ^ 2
      = ∑ l, ∑ l', (c l - d l) * (c l' - d l') * (phi l x * phi l' x) := by
    intro x
    have hlin : coeff_to_fun phi c x - coeff_to_fun phi d x
        = ∑ l, (c l - d l) * phi l x := by
      simp [coeff_to_fun, sub_mul, Finset.sum_sub_distrib]
    rw [hlin, sq_sum_mul_eq_double_sum]
  unfold l2_sq_dist
  simp only [hpt]
  rw [integral_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun l' _ => (hint l l').const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun l' _ => (hint l l').const_mul _]
  exact Finset.sum_congr rfl fun l' _ => integral_const_mul _ _

@[blueprint "lem:parseval-coeff-norm"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space, let $r\in\mathbb N$, and let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family} with $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every
  $\ell\in[r]$. Then for all coefficient vectors $c,d\in\mathbb R^r$,
  \[
    D_{\mu,\varphi}(c,d)=\|c-d\|^2 ,
  \]
  where $D_{\mu,\varphi}$ is the squared $L^2(\mathcal X)$ distance of \cref{def:l2-sq-dist} and
  $\|\cdot\|$ is the Euclidean norm on $\mathbb R^r$. -/)
  (proof := /-- Set $e:=c-d$, so that $e_\ell=c_\ell-d_\ell$ for every $\ell\in[r]$. Unfolding the
  orthonormality hypothesis of \cref{def:l2-orthonormal-family} gives, for all $\ell,\ell'\in[r]$,
  \[
    \int_{\mathcal X}\varphi_\ell(x)\varphi_{\ell'}(x)\,d\mu(x)=\delta_{\ell\ell'},
  \]
  which equals $1$ when $\ell=\ell'$ and $0$ otherwise.

  Since $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every $\ell\in[r]$, the Gram expansion of
  \cref{lem:l2-sq-dist-eq-gram-sum} applies to the pair $(c,d)$ and yields
  \[
    D_{\mu,\varphi}(c,d)
    =\sum_{\ell=1}^r\sum_{\ell'=1}^re_\ell e_{\ell'}
      \int_{\mathcal X}\varphi_\ell(x)\varphi_{\ell'}(x)\,d\mu(x).
  \]
  Substituting the orthonormality values above, every term with $\ell\neq\ell'$ vanishes and each
  diagonal term contributes $e_\ell e_\ell$, so the inner sum collapses for each fixed $\ell$ and
  \[
    D_{\mu,\varphi}(c,d)=\sum_{\ell=1}^re_\ell^2 .
  \]
  On the other hand, the squared Euclidean norm on $\mathbb R^r$ is given by
  $\|e\|^2=\sum_{\ell=1}^re_\ell^2$, and $e_\ell=c_\ell-d_\ell$ is precisely the $\ell$-th
  coordinate of $c-d$. Comparing the two displayed expressions gives
  $D_{\mu,\varphi}(c,d)=\|c-d\|^2$. -/)
  (title := /-- Parseval identity: $L^2$ distance equals Euclidean distance of coefficients -/)
  (latexEnv := "lemma")]
lemma parseval_coeff_norm {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (hphi : l2_orthonormal_family mu phi)
    (hmem : ∀ l, MemLp (phi l) 2 mu) (c d : EuclideanSpace ℝ (Fin r)) :
    l2_sq_dist mu phi c d = ‖c - d‖ ^ 2 := by
  have horth : ∀ l l' : Fin r, (∫ x, phi l x * phi l' x ∂mu) = if l = l' then 1 else 0 := hphi
  rw [l2_sq_dist_eq_gram_sum mu phi hmem c d, EuclideanSpace.real_norm_sq_eq]
  simp [horth, sq]

@[blueprint "lem:representation-orthogonal-of-measure-preserving"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space, let $G$ be a group acting on
  $\mathcal X$ such that for every $g\in G$ the map $x\mapsto g\cdot x$ preserves $\mu$, let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family} with $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every
  $\ell\in[r]$, and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be a representation implementing the
  lifted action in the sense of \cref{def:implements-lifted-action}. Then $\rho$ is orthogonal in
  the sense of \cref{def:orthogonal-representation}, that is $\|\rho(g)c\|=\|c\|$ for all $g\in G$
  and all $c\in\mathbb R^r$. -/)
  (proof := /-- Fix $g\in G$ and $c\in\mathbb R^r$. Applying \cref{lem:parseval-coeff-norm} with the
  pair $(\rho(g)c,0)$ gives
  \[
    \|\rho(g)c\|^2=\int_{\mathcal X}\bigl(\iota_\varphi(\rho(g)c)(x)\bigr)^2\,d\mu(x),
  \]
  and applying it with the pair $(c,0)$ gives
  $\|c\|^2=\int_{\mathcal X}(\iota_\varphi(c)(x))^2\,d\mu(x)$. By
  \cref{def:implements-lifted-action} we have
  $\iota_\varphi(\rho(g)c)(x)=\iota_\varphi(c)(g^{-1}x)$ for every $x\in\mathcal X$, so the two
  integrands coincide with the function $x\mapsto(\iota_\varphi(c)(g^{-1}x))^2$, whence
  \[
    \|\rho(g)c\|^2=\int_{\mathcal X}\bigl(\iota_\varphi(c)(g^{-1}x)\bigr)^2\,d\mu(x).
  \]
  The map $x\mapsto g^{-1}\cdot x$ preserves $\mu$ by hypothesis, and it is a measurable
  automorphism of $\mathcal X$: it is a bijection with inverse $x\mapsto g\cdot x$, and both maps are
  measurable because they are $\mu$-preserving by hypothesis. In particular $x\mapsto g^{-1}\cdot x$
  is a measurable embedding, so the change of variables formula for measure-preserving measurable
  embeddings gives
  \[
    \int_{\mathcal X}\bigl(\iota_\varphi(c)(g^{-1}x)\bigr)^2\,d\mu(x)
    =\int_{\mathcal X}\bigl(\iota_\varphi(c)(x)\bigr)^2\,d\mu(x)
    =\|c\|^2 .
  \]
  Therefore $\|\rho(g)c\|^2=\|c\|^2$, and since both norms are nonnegative, $\|\rho(g)c\|=\|c\|$. -/)
  (title := /-- Measure-preserving actions induce orthogonal representations -/)
  (latexEnv := "lemma")]
lemma representation_orthogonal_of_measure_preserving {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {G : Type*} [Group G] [MulAction G X] {r : ℕ} (phi : Fin r → X → ℝ)
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r)))
    (hact : ∀ g : G, MeasurePreserving (fun x : X => g • x) mu mu)
    (hphi : l2_orthonormal_family mu phi) (hmem : ∀ l, MemLp (phi l) 2 mu)
    (himpl : implements_lifted_action phi rho) :
    orthogonal_representation rho := by
  have hemb : ∀ g : G, MeasurableEmbedding (fun x : X => g • x) := fun g =>
    MeasurableEquiv.measurableEmbedding
      { toEquiv := MulAction.toPerm g
        measurable_toFun := (hact g).measurable
        measurable_invFun := (hact g⁻¹).measurable }
  have hint : ∀ (g : G) (F : X → ℝ), ∫ x, F (g • x) ∂mu = ∫ x, F x ∂mu := fun g F =>
    (hact g).integral_comp (hemb g) F
  have hsq : ∀ d : EuclideanSpace ℝ (Fin r),
      ‖d‖ ^ 2 = ∫ x, coeff_to_fun phi d x ^ 2 ∂mu := by
    intro d
    have h0 := parseval_coeff_norm mu phi hphi hmem d 0
    rw [sub_zero] at h0
    rw [← h0, l2_sq_dist]
    simp [coeff_to_fun]
  intro g c
  have hpt : ∀ x : X, coeff_to_fun phi (rho g c) x = coeff_to_fun phi c (g⁻¹ • x) :=
    himpl g c
  have hsqeq : ‖rho g c‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [hsq (rho g c), hsq c]
    simp only [hpt]
    exact hint g⁻¹ fun x => coeff_to_fun phi c x ^ 2
  exact (pow_left_inj₀ (norm_nonneg (rho g c)) (norm_nonneg c) two_ne_zero).mp hsqeq

@[blueprint "lem:group-average-eq-invariant-projection"
  (statement := /-- Let $G$ be a finite group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be an
  orthogonal representation of $G$ on the Euclidean space $\mathbb R^r$, in the sense of
  \cref{def:orthogonal-representation}. Then the full averaging operator $\Pi_G$ of
  \cref{def:group-average-operator} coincides with the orthogonal projection $\Pi_{\mathcal F^G}$
  onto the invariant subspace of \cref{def:invariant-projection}:
  \[
    \Pi_G c=\Pi_{\mathcal F^G}c\qquad\text{for all }c\in\mathbb R^r .
  \]
  -/)
  (proof := /-- Write $V:=(\mathbb R^r)^G=\{v\in\mathbb R^r:\rho(g)v=v\text{ for all }g\in G\}$ for
  the invariant subspace, as in \cref{def:invariant-projection}, and fix $c\in\mathbb R^r$. Since
  $\Pi_{\mathcal F^G}$ is by definition the orthogonal projection onto the closed subspace $V$, it
  suffices to establish the two conditions that characterize that projection at the vector $c$,
  namely $\Pi_Gc\in V$ and $c-\Pi_Gc\in V^{\perp}$; the projection is then uniquely determined by
  them.

  Step 1: $\Pi_Gc\in V$. Fix $h\in G$. Since each $\rho(g)$ is linear and $\rho$ is a group
  homomorphism, and using the definition of $\Pi_G$ from \cref{def:group-average-operator},
  \[
    \rho(h)\Pi_Gc=\frac{1}{|G|}\sum_{g\in G}\rho(h)\rho(g)c=\frac{1}{|G|}\sum_{g\in G}\rho(hg)c .
  \]
  The left translation $g\mapsto hg$ is a bijection of the finite group $G$ onto itself, so
  reindexing the sum along this bijection gives
  $\sum_{g\in G}\rho(hg)c=\sum_{g'\in G}\rho(g')c$, whence $\rho(h)\Pi_Gc=\Pi_Gc$. As $h\in G$ was
  arbitrary, $\Pi_Gc\in V$.

  Step 2: $c-\Pi_Gc\in V^{\perp}$. Let $u\in V$; we must show $\langle u,c-\Pi_Gc\rangle=0$. Since
  $\rho$ is orthogonal in the sense of \cref{def:orthogonal-representation}, that is
  $\|\rho(g)v\|=\|v\|$ for all $g\in G$ and all $v\in\mathbb R^r$, each linear map $\rho(g)$ is an
  isometry and therefore preserves the inner product:
  $\langle\rho(g)v,\rho(g)w\rangle=\langle v,w\rangle$ for all $v,w\in\mathbb R^r$. Applying this
  with $v:=u$ and $w:=c$, and then using $\rho(g)u=u$, which holds because $u\in V$, we get
  \[
    \langle u,\rho(g)c\rangle=\langle\rho(g)u,\rho(g)c\rangle=\langle u,c\rangle
    \qquad\text{for every }g\in G .
  \]
  Hence, by additivity of the inner product in its second argument and its homogeneity with respect
  to real scalars,
  \[
    \langle u,\Pi_Gc\rangle=\frac{1}{|G|}\sum_{g\in G}\langle u,\rho(g)c\rangle
    =\frac{1}{|G|}\,|G|\,\langle u,c\rangle=\langle u,c\rangle,
  \]
  where the last equality uses $|G|\neq0$, valid because $G$ is a nonempty finite group. Therefore
  $\langle u,c-\Pi_Gc\rangle=\langle u,c\rangle-\langle u,\Pi_Gc\rangle=0$, and since $u\in V$ was
  arbitrary, $c-\Pi_Gc\in V^{\perp}$.

  By Steps 1 and 2, the vector $\Pi_Gc$ lies in $V$ and $c-\Pi_Gc$ lies in $V^{\perp}$, which is
  exactly the characterization of the orthogonal projection of $c$ onto $V$. Consequently
  $\Pi_{\mathcal F^G}c=\Pi_Gc$, that is $\Pi_Gc=\Pi_{\mathcal F^G}c$. -/)
  (title := /-- The averaging operator is the orthogonal projection onto the invariants -/)
  (latexEnv := "lemma")]
lemma group_average_eq_invariant_projection {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (hrho : orthogonal_representation rho)
    (c : EuclideanSpace ℝ (Fin r)) :
    group_average_operator rho c = invariant_projection rho c := by
  have hmem : group_average_operator rho c ∈ rho.invariants := by
    rw [Representation.mem_invariants]
    intro h
    simp only [group_average_operator, map_smul, map_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul])
  have horth : c - group_average_operator rho c ∈ rho.invariantsᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hinner : ∀ g : G, inner ℝ u ((rho g) c) = inner ℝ u c := by
      intro g
      rw [← (LinearMap.norm_map_iff_inner_map_map (rho g)).1 (hrho g) u c,
        (Representation.mem_invariants _ _).1 hu g]
    rw [inner_sub_right, group_average_operator, real_inner_smul_right, inner_sum]
    simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [Nat.cast_ne_zero.2 (Fintype.card_ne_zero (α := G))]
  exact (Submodule.eq_starProjection_of_mem_orthogonal hmem horth).symm

@[blueprint "lem:norm-sub-invariant-projection-le"
  (statement := /-- Let $G$ be a group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be a
  representation of $G$ on the Euclidean space $\mathbb R^r$. Let $\Pi_{\mathcal F^G}$ be the
  orthogonal projection onto the invariant subspace $(\mathbb R^r)^G$, as in
  \cref{def:invariant-projection}. Then for every $c\in\mathbb R^r$ and every invariant vector
  $b\in(\mathbb R^r)^G$,
  \[
    \|c-\Pi_{\mathcal F^G}c\|\le\|c-b\| .
  \]
  -/)
  (proof := /-- Write $V:=(\mathbb R^r)^G$ for the invariant subspace, so that $b\in V$ by
  hypothesis, and recall from \cref{def:invariant-projection} that $\Pi_{\mathcal F^G}$ is the
  orthogonal projection onto $V$. The orthogonal projection realizes the distance from $c$ to $V$,
  that is,
  \[
    \|c-\Pi_{\mathcal F^G}c\|=\inf_{v\in V}\|c-v\| ,
  \]
  which is the variational characterization of the orthogonal projection onto a subspace admitting
  an orthogonal projection; here $V$ admits one because it is a subspace of the
  finite-dimensional Hilbert space $\mathbb R^r$.

  It therefore suffices to bound this infimum by the single value $\|c-b\|$. The set
  $\{\|c-v\|:v\in V\}$ is bounded below by $0$, since every norm is nonnegative, so the infimum
  over the nonempty index set $V$ is a genuine greatest lower bound and hence is at most the value
  attained at any particular index. Applying this at the index $b\in V$ gives
  \[
    \|c-\Pi_{\mathcal F^G}c\|=\inf_{v\in V}\|c-v\|\le\|c-b\| ,
  \]
  which is the assertion. -/)
  (title := /-- Minimality of the orthogonal projection onto the invariants -/)
  (latexEnv := "lemma")]
lemma norm_sub_invariant_projection_le {G : Type*} [Group G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (c b : EuclideanSpace ℝ (Fin r))
    (hb : b ∈ rho.invariants) :
    ‖c - invariant_projection rho c‖ ≤ ‖c - b‖ := by
  rw [invariant_projection, Submodule.starProjection_minimal]
  refine ciInf_le ⟨0, ?_⟩ (⟨b, hb⟩ : rho.invariants)
  rintro y ⟨x, rfl⟩
  exact norm_nonneg _

@[blueprint "lem:integral-pi-eval"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$, let
  $n\in\mathbb N$, let $i\in[n]$ and let $f:\mathcal Y\to\mathbb R$ be
  $\nu$-almost everywhere strongly measurable. Then
  \[
    \int_{\mathcal Y^n}f(y_i)\,d\nu^{\otimes n}(y_{1:n})=\int_{\mathcal Y}f\,d\nu .
  \]
  -/)
  (proof := /-- The coordinate projection $\pi_i:\mathcal Y^n\to\mathcal Y$, $y_{1:n}\mapsto y_i$, is
  measurable and pushes $\nu^{\otimes n}$ forward to $\nu$, because $\nu$ is a probability measure.
  Since $f$ is almost everywhere strongly measurable for $\nu$, hence for the pushforward measure
  $(\pi_i)_*\nu^{\otimes n}=\nu$, the change-of-variables formula for the Bochner integral gives
  \[
    \int_{\mathcal Y}f\,d\bigl((\pi_i)_*\nu^{\otimes n}\bigr)
    =\int_{\mathcal Y^n}f(\pi_i(y_{1:n}))\,d\nu^{\otimes n}(y_{1:n}).
  \]
  Rewriting $(\pi_i)_*\nu^{\otimes n}=\nu$ on the left-hand side and $\pi_i(y_{1:n})=y_i$ on the
  right-hand side yields the claim. -/)
  (title := /-- Integral of a single coordinate under the i.i.d. product measure -/)
  (latexEnv := "lemma")]
lemma integral_pi_eval {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {n : ℕ} (i : Fin n) (f : Y → ℝ)
    (hf : AEStronglyMeasurable f nu) :
    ∫ ys, f (ys i) ∂(Measure.pi fun _ : Fin n => nu) = ∫ y, f y ∂nu := by
  have hmp := measurePreserving_eval (fun _ : Fin n => nu) i
  have h := integral_map (φ := fun ys : Fin n → Y => ys i)
    (μ := Measure.pi fun _ : Fin n => nu) (f := f)
    (measurable_pi_apply i).aemeasurable (by rwa [hmp.map_eq])
  rw [hmp.map_eq] at h
  exact h.symm

@[blueprint "lem:integrable-pair-mul"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$ and let
  $f,g:\mathcal Y\to\mathbb R$ be $\nu$-integrable. Then the separated product
  $(y_1,y_2)\mapsto f(y_1)g(y_2)$ is $\nu\otimes\nu$-integrable on $\mathcal Y\times\mathcal Y$. -/)
  (proof := /-- The two coordinate projections are quasi measure preserving from
  $\nu\otimes\nu$ to $\nu$, so $(y_1,y_2)\mapsto f(y_1)$ and $(y_1,y_2)\mapsto g(y_2)$ are
  $\nu\otimes\nu$-almost everywhere strongly measurable, and hence so is their product. It remains to
  check that the product has finite integral, i.e. that
  $\int^-\|f(y_1)g(y_2)\|\,d(\nu\otimes\nu)<\infty$, where $\int^-$ denotes the lower Lebesgue
  integral of an $[0,\infty]$-valued function. Multiplicativity of the extended norm gives
  $\|f(y_1)g(y_2)\|=\|f(y_1)\|\,\|g(y_2)\|$ pointwise, and for a separated product of two
  nonnegative measurable functions the lower Lebesgue integral over $\nu\otimes\nu$ factors as
  \[
    \int^-\|f(y_1)\|\,\|g(y_2)\|\,d(\nu\otimes\nu)
    =\Bigl(\int^-\|f\|\,d\nu\Bigr)\Bigl(\int^-\|g\|\,d\nu\Bigr).
  \]
  Both factors are finite because $f$ and $g$ are $\nu$-integrable, and a product of two finite
  elements of $[0,\infty]$ is finite. -/)
  (title := /-- Integrability of a separated product on a product measure -/)
  (latexEnv := "lemma")]
lemma integrable_pair_mul {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {f g : Y → ℝ} (hf : Integrable f nu) (hg : Integrable g nu) :
    Integrable (fun z : Y × Y => f z.1 * g z.2) (nu.prod nu) := by
  have hf1 : AEStronglyMeasurable (fun z : Y × Y => f z.1) (nu.prod nu) :=
    hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hg1 : AEStronglyMeasurable (fun z : Y × Y => g z.2) (nu.prod nu) :=
    hg.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  refine ⟨hf1.mul hg1, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcalc : ∫⁻ z : Y × Y, ‖f z.1 * g z.2‖ₑ ∂(nu.prod nu)
      = (∫⁻ y, ‖f y‖ₑ ∂nu) * ∫⁻ y, ‖g y‖ₑ ∂nu := by
    rw [← lintegral_prod_mul hf.1.enorm hg.1.enorm]
    exact lintegral_congr fun z => by rw [enorm_mul]
  rw [hcalc]
  exact ENNReal.mul_lt_top (hasFiniteIntegral_iff_enorm.mp hf.2)
    (hasFiniteIntegral_iff_enorm.mp hg.2)

@[blueprint "lem:integral-pair-mul-of-nonneg"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$ and let
  $f,g:\mathcal Y\to\mathbb R$ be $\nu$-almost everywhere strongly measurable and nonnegative
  $\nu$-almost everywhere. Then
  \[
    \int_{\mathcal Y\times\mathcal Y}f(y_1)g(y_2)\,d(\nu\otimes\nu)(y_1,y_2)
    =\Bigl(\int_{\mathcal Y}f\,d\nu\Bigr)\Bigl(\int_{\mathcal Y}g\,d\nu\Bigr).
  \]
  -/)
  (proof := /-- Since the coordinate projections are quasi measure preserving from $\nu\otimes\nu$
  to $\nu$, the functions $(y_1,y_2)\mapsto f(y_1)$ and $(y_1,y_2)\mapsto g(y_2)$ are
  $\nu\otimes\nu$-almost everywhere strongly measurable and $\nu\otimes\nu$-almost everywhere
  nonnegative; consequently their product is $\nu\otimes\nu$-almost everywhere nonnegative, being an
  almost everywhere product of two nonnegative quantities. For a nonnegative almost everywhere
  strongly measurable function the Bochner integral equals the real part of the lower Lebesgue
  integral of its nonnegative extension, so all three integrals in the claim may be rewritten in
  that form. Because $f(y_1)\ge0$ almost everywhere, the nonnegative extension of the product
  factors pointwise almost everywhere as the product of the nonnegative extensions, and for a
  separated product of two nonnegative measurable functions the lower Lebesgue integral over
  $\nu\otimes\nu$ equals the product of the two lower Lebesgue integrals. Finally the passage to
  real values is multiplicative on $[0,\infty]$, which turns that product of lower Lebesgue
  integrals into the product of the two Bochner integrals. -/)
  (title := /-- Factorization of a nonnegative separated product integral -/)
  (latexEnv := "lemma")]
lemma integral_pair_mul_of_nonneg {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {f g : Y → ℝ} (hf : AEStronglyMeasurable f nu)
    (hg : AEStronglyMeasurable g nu) (hf0 : 0 ≤ᵐ[nu] f) (hg0 : 0 ≤ᵐ[nu] g) :
    ∫ z : Y × Y, f z.1 * g z.2 ∂(nu.prod nu) = (∫ y, f y ∂nu) * ∫ y, g y ∂nu := by
  have hf1 : AEStronglyMeasurable (fun z : Y × Y => f z.1) (nu.prod nu) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hg1 : AEStronglyMeasurable (fun z : Y × Y => g z.2) (nu.prod nu) :=
    hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hf0' : ∀ᵐ z : Y × Y ∂(nu.prod nu), 0 ≤ f z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hf0
  have hg0' : ∀ᵐ z : Y × Y ∂(nu.prod nu), 0 ≤ g z.2 :=
    Measure.quasiMeasurePreserving_snd.ae hg0
  have hprod0 : 0 ≤ᵐ[nu.prod nu] fun z : Y × Y => f z.1 * g z.2 := by
    filter_upwards [hf0', hg0'] with z h1 h2 using mul_nonneg h1 h2
  rw [integral_eq_lintegral_of_nonneg_ae hprod0 (hf1.mul hg1),
    integral_eq_lintegral_of_nonneg_ae hf0 hf, integral_eq_lintegral_of_nonneg_ae hg0 hg,
    ← ENNReal.toReal_mul,
    ← lintegral_prod_mul hf.aemeasurable.ennreal_ofReal hg.aemeasurable.ennreal_ofReal]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hf0'] with z h1
  rw [ENNReal.ofReal_mul h1]

@[blueprint "lem:measure-preserving-pair-eval"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$, let
  $n\in\mathbb N$ and let $i,j\in[n]$ with $i\neq j$. Then the map
  $\mathcal Y^n\to\mathcal Y\times\mathcal Y$, $y_{1:n}\mapsto(y_i,y_j)$, pushes $\nu^{\otimes n}$
  forward to $\nu\otimes\nu$. -/)
  (proof := /-- Write $T(y_{1:n}):=(y_i,y_j)$; it is measurable, being the pairing of two coordinate
  projections. Since $\nu\otimes\nu$ is determined by its values on measurable rectangles, it
  suffices to prove that $T_*\nu^{\otimes n}(s\times t)=\nu(s)\,\nu(t)$ for all measurable
  $s,t\subset\mathcal Y$. By measurability of $T$,
  $T_*\nu^{\otimes n}(s\times t)=\nu^{\otimes n}\bigl(T^{-1}(s\times t)\bigr)$, and
  \[
    T^{-1}(s\times t)=\{y_{1:n}:y_i\in s,\ y_j\in t\}=\prod_{k=1}^n u_k,
    \qquad u_k:=\begin{cases}s,&k=i,\\ t,&k=j,\\ \mathcal Y,&\text{otherwise},\end{cases}
  \]
  where the description of $u_j$ uses $i\neq j$. Each $u_k$ is measurable, so the defining property
  of the product measure gives $\nu^{\otimes n}\bigl(\prod_k u_k\bigr)=\prod_k\nu(u_k)$. In this
  product all factors with $k\neq i$ and $k\neq j$ equal $\nu(\mathcal Y)=1$ because $\nu$ is a
  probability measure, so, using $i\neq j$ once more, the product reduces to
  $\nu(u_i)\,\nu(u_j)=\nu(s)\,\nu(t)$, as required. -/)
  (title := /-- Two distinct coordinates of an i.i.d. sample are jointly distributed as $\nu\otimes\nu$ -/)
  (latexEnv := "lemma")]
lemma measure_preserving_pair_eval {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (fun ys : Fin n → Y => (ys i, ys j))
      (Measure.pi fun _ : Fin n => nu) (nu.prod nu) := by
  classical
  have hmeas : Measurable fun ys : Fin n → Y => (ys i, ys j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  refine ⟨hmeas, ?_⟩
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  have hpre : (fun ys : Fin n → Y => (ys i, ys j)) ⁻¹' (s ×ˢ t)
      = Set.univ.pi fun k => if k = i then s else if k = j then t else Set.univ := by
    ext ys
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi]
    refine ⟨fun h k => ?_, fun h => ⟨?_, ?_⟩⟩
    · by_cases hk : k = i
      · simpa [hk] using h.1
      · by_cases hk' : k = j
        · simp only [hk', if_neg hij.symm, if_pos rfl]
          exact h.2
        · simp [hk, hk']
    · simpa using h i
    · have := h j
      simpa [hij.symm] using this
  rw [Measure.map_apply hmeas (hs.prod ht), hpre, Measure.pi_pi]
  have hval := Fintype.prod_eq_mul (f := fun k : Fin n =>
      nu (if k = i then s else if k = j then t else Set.univ)) i j hij ?_
  · simpa [hij.symm] using hval
  · intro k hk
    simp [hk.1, hk.2]

@[blueprint "lem:integral-pair-mul"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$ and let
  $f,g:\mathcal Y\to\mathbb R$ be $\nu$-integrable. Then
  \[
    \int_{\mathcal Y\times\mathcal Y}f(y_1)g(y_2)\,d(\nu\otimes\nu)(y_1,y_2)
    =\Bigl(\int_{\mathcal Y}f\,d\nu\Bigr)\Bigl(\int_{\mathcal Y}g\,d\nu\Bigr).
  \]
  -/)
  (proof := /-- Write $f^+:=\max(f,0)$ and $f^-:=\max(-f,0)$, and likewise $g^\pm$ for $g$. All four
  functions are nonnegative everywhere, and each is $\nu$-integrable as the positive or negative part
  of an integrable function. Moreover $f=f^+-f^-$ and $g=g^+-g^-$ pointwise: if $f(y)\ge0$ then
  $f^+(y)=f(y)$ and $f^-(y)=0$, while if $f(y)\le0$ then $f^+(y)=0$ and $f^-(y)=-f(y)$. Integrating
  the identity $f=f^+-f^-$ and using additivity of the integral on integrable functions gives
  $\int f\,d\nu=\int f^+\,d\nu-\int f^-\,d\nu$, and similarly for $g$.

  Expanding the product pointwise on $\mathcal Y\times\mathcal Y$,
  \[
    f(y_1)g(y_2)=\bigl(f^+(y_1)g^+(y_2)-f^+(y_1)g^-(y_2)\bigr)
      -\bigl(f^-(y_1)g^+(y_2)-f^-(y_1)g^-(y_2)\bigr).
  \]
  Each of the four separated products is $\nu\otimes\nu$-integrable by
  \cref{lem:integrable-pair-mul}, so the integral of the right-hand side splits into the four
  corresponding integrals by additivity, and each of them factors by
  \cref{lem:integral-pair-mul-of-nonneg} because the factors are nonnegative and almost everywhere
  strongly measurable. Therefore
  \[
    \int f(y_1)g(y_2)\,d(\nu\otimes\nu)
    =\Bigl(\int f^+\Bigr)\Bigl(\int g^+\Bigr)-\Bigl(\int f^+\Bigr)\Bigl(\int g^-\Bigr)
     -\Bigl(\int f^-\Bigr)\Bigl(\int g^+\Bigr)+\Bigl(\int f^-\Bigr)\Bigl(\int g^-\Bigr),
  \]
  which is exactly the expansion of
  $\bigl(\int f^+-\int f^-\bigr)\bigl(\int g^+-\int g^-\bigr)=\bigl(\int f\bigr)\bigl(\int g\bigr)$. -/)
  (title := /-- Factorization of a separated product integral -/)
  (latexEnv := "lemma")]
lemma integral_pair_mul {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {f g : Y → ℝ} (hf : Integrable f nu) (hg : Integrable g nu) :
    ∫ z : Y × Y, f z.1 * g z.2 ∂(nu.prod nu) = (∫ y, f y ∂nu) * ∫ y, g y ∂nu := by
  have hfp : Integrable (fun y => max (f y) 0) nu := hf.pos_part
  have hfn : Integrable (fun y => max (-f y) 0) nu := hf.neg_part
  have hgp : Integrable (fun y => max (g y) 0) nu := hg.pos_part
  have hgn : Integrable (fun y => max (-g y) 0) nu := hg.neg_part
  have hnn : ∀ h : Y → ℝ, 0 ≤ᵐ[nu] fun y => max (h y) 0 :=
    fun h => Filter.Eventually.of_forall fun y => le_max_right _ _
  have hsplit : ∀ (h : Y → ℝ) (y : Y), h y = max (h y) 0 - max (-h y) 0 := by
    intro h y
    rcases le_total 0 (h y) with hy | hy
    · rw [max_eq_left hy, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right hy, max_eq_left (by linarith)]
      ring
  have hmean : ∀ (h : Y → ℝ), Integrable h nu →
      ∫ y, h y ∂nu = (∫ y, max (h y) 0 ∂nu) - ∫ y, max (-h y) 0 ∂nu := by
    intro h hh
    rw [← integral_sub hh.pos_part hh.neg_part]
    exact integral_congr_ae (Filter.Eventually.of_forall (hsplit h))
  have hI1 : Integrable (fun z : Y × Y => max (f z.1) 0 * max (g z.2) 0) (nu.prod nu) :=
    integrable_pair_mul nu hfp hgp
  have hI2 : Integrable (fun z : Y × Y => max (f z.1) 0 * max (-g z.2) 0) (nu.prod nu) :=
    integrable_pair_mul nu hfp hgn
  have hI3 : Integrable (fun z : Y × Y => max (-f z.1) 0 * max (g z.2) 0) (nu.prod nu) :=
    integrable_pair_mul nu hfn hgp
  have hI4 : Integrable (fun z : Y × Y => max (-f z.1) 0 * max (-g z.2) 0) (nu.prod nu) :=
    integrable_pair_mul nu hfn hgn
  have hexp : ∫ z : Y × Y, f z.1 * g z.2 ∂(nu.prod nu)
      = ∫ z : Y × Y, (max (f z.1) 0 * max (g z.2) 0 - max (f z.1) 0 * max (-g z.2) 0)
          - (max (-f z.1) 0 * max (g z.2) 0 - max (-f z.1) 0 * max (-g z.2) 0) ∂(nu.prod nu) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show f z.1 * g z.2 = _
    rw [hsplit f z.1, hsplit g z.2]
    ring
  rw [hexp]
  rw [show ∫ z : Y × Y, (max (f z.1) 0 * max (g z.2) 0 - max (f z.1) 0 * max (-g z.2) 0)
          - (max (-f z.1) 0 * max (g z.2) 0 - max (-f z.1) 0 * max (-g z.2) 0) ∂(nu.prod nu)
        = ∫ z : Y × Y, ((fun w : Y × Y => max (f w.1) 0 * max (g w.2) 0)
              - fun w : Y × Y => max (f w.1) 0 * max (-g w.2) 0) z
            - ((fun w : Y × Y => max (-f w.1) 0 * max (g w.2) 0)
              - fun w : Y × Y => max (-f w.1) 0 * max (-g w.2) 0) z ∂(nu.prod nu) from rfl]
  rw [integral_sub (hI1.sub hI2) (hI3.sub hI4)]
  simp only [Pi.sub_apply]
  rw [integral_sub hI1 hI2, integral_sub hI3 hI4,
    integral_pair_mul_of_nonneg nu hfp.1 hgp.1 (hnn f) (hnn g),
    integral_pair_mul_of_nonneg nu hfp.1 hgn.1 (hnn f) (hnn (fun y => -g y)),
    integral_pair_mul_of_nonneg nu hfn.1 hgp.1 (hnn (fun y => -f y)) (hnn g),
    integral_pair_mul_of_nonneg nu hfn.1 hgn.1 (hnn (fun y => -f y)) (hnn (fun y => -g y)),
    hmean f hf, hmean g hg]
  ring

@[blueprint "lem:integral-pi-cross-term"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$, let
  $n\in\mathbb N$, let $\psi:\mathcal Y\to\mathbb R$ be $\nu$-integrable and write
  $\bar\psi:=\int_{\mathcal Y}\psi\,d\nu$. Then for all $i,j\in[n]$ with $i\neq j$,
  \[
    \int_{\mathcal Y^n}\bigl(\psi(y_i)-\bar\psi\bigr)\bigl(\psi(y_j)-\bar\psi\bigr)
      \,d\nu^{\otimes n}(y_{1:n})=0 .
  \]
  -/)
  (proof := /-- Put $\chi:=\psi-\bar\psi$, which is $\nu$-integrable as the difference of the
  integrable function $\psi$ and a constant, the latter being integrable because $\nu$ is a
  probability measure and hence finite. Its mean vanishes:
  $\int_{\mathcal Y}\chi\,d\nu=\int_{\mathcal Y}\psi\,d\nu-\bar\psi\,\nu(\mathcal Y)=\bar\psi-\bar\psi=0$,
  using additivity of the integral and $\nu(\mathcal Y)=1$.

  By \cref{lem:measure-preserving-pair-eval}, the map $y_{1:n}\mapsto(y_i,y_j)$ pushes
  $\nu^{\otimes n}$ forward to $\nu\otimes\nu$, since $i\neq j$. The function
  $(w_1,w_2)\mapsto\chi(w_1)\chi(w_2)$ is $\nu\otimes\nu$-integrable by
  \cref{lem:integrable-pair-mul}, so the change-of-variables formula for the Bochner integral along
  this pushforward gives
  \[
    \int_{\mathcal Y^n}\chi(y_i)\chi(y_j)\,d\nu^{\otimes n}
    =\int_{\mathcal Y\times\mathcal Y}\chi(w_1)\chi(w_2)\,d(\nu\otimes\nu).
  \]
  By \cref{lem:integral-pair-mul} the right-hand side equals
  $\bigl(\int_{\mathcal Y}\chi\,d\nu\bigr)^2=0$. -/)
  (title := /-- Vanishing of the cross terms of an empirical mean -/)
  (latexEnv := "lemma")]
lemma integral_pi_cross_term {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {n : ℕ} {i j : Fin n} (hij : i ≠ j) (psi : Y → ℝ)
    (hpsi : Integrable psi nu) :
    ∫ ys, (psi (ys i) - ∫ y, psi y ∂nu) * (psi (ys j) - ∫ y, psi y ∂nu)
        ∂(Measure.pi fun _ : Fin n => nu) = 0 := by
  set c : ℝ := ∫ y, psi y ∂nu with hc
  have hchi : Integrable (fun y => psi y - c) nu := hpsi.sub (integrable_const c)
  have hchi0 : ∫ y, (psi y - c) ∂nu = 0 := by
    rw [integral_sub hpsi (integrable_const c), integral_const]
    simp [hc]
  have hmp := measure_preserving_pair_eval nu (n := n) hij
  have hint : Integrable (fun w : Y × Y => (psi w.1 - c) * (psi w.2 - c)) (nu.prod nu) :=
    integrable_pair_mul nu hchi hchi
  have hchg : ∫ ys, (psi (ys i) - c) * (psi (ys j) - c) ∂(Measure.pi fun _ : Fin n => nu)
      = ∫ w : Y × Y, (psi w.1 - c) * (psi w.2 - c) ∂(nu.prod nu) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hint.1)]
  rw [hchg, integral_pair_mul nu hchi hchi, hchi0, mul_zero]

@[blueprint "lem:integral-pi-diagonal-term"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$, let
  $n\in\mathbb N$, let $\psi:\mathcal Y\to\mathbb R$ satisfy $\psi\in L^2(\mathcal Y,\nu)$ and write
  $\bar\psi:=\int_{\mathcal Y}\psi\,d\nu$. Then for every $i\in[n]$,
  \[
    \int_{\mathcal Y^n}\bigl(\psi(y_i)-\bar\psi\bigr)^2\,d\nu^{\otimes n}(y_{1:n})
    \;\le\;\int_{\mathcal Y}\psi^2\,d\nu .
  \]
  -/)
  (proof := /-- Since $\psi\in L^2(\mathcal Y,\nu)$ and $\nu$ is a probability measure, the function
  $y\mapsto(\psi(y)-\bar\psi)^2$ is $\nu$-integrable, because $\psi-\bar\psi$ lies in
  $L^2(\mathcal Y,\nu)$ as the difference of $\psi$ and a constant; likewise $\psi^2$ is
  $\nu$-integrable. By \cref{lem:integral-pi-eval} applied to the integrable function
  $y\mapsto(\psi(y)-\bar\psi)^2$,
  \[
    \int_{\mathcal Y^n}\bigl(\psi(y_i)-\bar\psi\bigr)^2\,d\nu^{\otimes n}
    =\int_{\mathcal Y}\bigl(\psi-\bar\psi\bigr)^2\,d\nu .
  \]
  Expanding the square and using additivity of the integral together with
  $\int_{\mathcal Y}\psi\,d\nu=\bar\psi$ and $\nu(\mathcal Y)=1$,
  \[
    \int_{\mathcal Y}\bigl(\psi-\bar\psi\bigr)^2\,d\nu
    =\int_{\mathcal Y}\psi^2\,d\nu-2\bar\psi\int_{\mathcal Y}\psi\,d\nu+\bar\psi^{\,2}
    =\int_{\mathcal Y}\psi^2\,d\nu-\bar\psi^{\,2}.
  \]
  Since $\bar\psi^{\,2}\ge0$, the right-hand side is at most $\int_{\mathcal Y}\psi^2\,d\nu$. -/)
  (title := /-- Diagonal terms of an empirical mean are bounded by the second moment -/)
  (latexEnv := "lemma")]
lemma integral_pi_diagonal_term {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {n : ℕ} (i : Fin n) (psi : Y → ℝ) (hpsi : MemLp psi 2 nu) :
    ∫ ys, (psi (ys i) - ∫ y, psi y ∂nu) ^ 2 ∂(Measure.pi fun _ : Fin n => nu)
      ≤ ∫ y, (psi y) ^ 2 ∂nu := by
  set c : ℝ := ∫ y, psi y ∂nu with hc
  have hpsiInt : Integrable psi nu := hpsi.integrable one_le_two
  have hchiLp : MemLp (fun y => psi y - c) 2 nu := hpsi.sub (memLp_const c)
  have hsqInt : Integrable (fun y => (psi y - c) ^ 2) nu := hchiLp.integrable_sq
  have hpsiSq : Integrable (fun y => psi y ^ 2) nu := hpsi.integrable_sq
  have heval : ∫ ys, (psi (ys i) - c) ^ 2 ∂(Measure.pi fun _ : Fin n => nu)
      = ∫ y, (psi y - c) ^ 2 ∂nu :=
    integral_pi_eval nu i _ hsqInt.1
  have hexpand : ∫ y, (psi y - c) ^ 2 ∂nu = (∫ y, psi y ^ 2 ∂nu) - c ^ 2 := by
    have hrw : ∀ y : Y, (psi y - c) ^ 2 = psi y ^ 2 - (2 * c) * psi y + c ^ 2 := by
      intro y; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
      show ∫ y, (psi y ^ 2 - (2 * c) * psi y + c ^ 2) ∂nu
          = ∫ y, ((fun w => psi w ^ 2) - fun w => (2 * c) * psi w) y + c ^ 2 ∂nu from rfl,
      integral_add ((hpsiSq.sub ((hpsiInt.const_mul (2 * c))))) (integrable_const _)]
    simp only [Pi.sub_apply]
    rw [integral_sub hpsiSq (hpsiInt.const_mul (2 * c)), integral_const, integral_const_mul]
    simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul, ← hc]
    ring
  rw [heval, hexpand]
  nlinarith [sq_nonneg c]

@[blueprint "lem:iid-mean-squared-error"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$, let
  $n\in\mathbb N$ with $n>0$, and let $\psi:\mathcal Y\to\mathbb R$ satisfy
  $\psi\in L^2(\mathcal Y,\nu)$. Then, with the i.i.d. expectation of
  \cref{def:iid-expectation},
  \[
    \mathbb E_{y_{1:n}\stackrel{\text{i.i.d.}}{\sim}\nu}
    \Bigl[\Bigl(\frac1n\sum_{i=1}^n\psi(y_i)-\int_{\mathcal Y}\psi\,d\nu\Bigr)^2\Bigr]
    \;\le\;\frac1n\int_{\mathcal Y}\psi^2\,d\nu .
  \]
  -/)
  (proof := /-- Write $\bar\psi:=\int_{\mathcal Y}\psi\,d\nu$, which is finite because
  $\psi\in L^2(\mathcal Y,\nu)$ and $\nu$ is a probability measure, and set
  $\chi:=\psi-\bar\psi$. Since $n>0$ we have $n\neq0$ as a real number. The function $\chi$ lies in
  $L^2(\mathcal Y,\nu)$, being the difference of $\psi$ and a constant, and therefore, for each
  $i\in[n]$, the coordinate function $y_{1:n}\mapsto\chi(y_i)$ lies in
  $L^2(\mathcal Y^n,\nu^{\otimes n})$, because the coordinate projection pushes $\nu^{\otimes n}$
  forward to $\nu$. Consequently, for all $i,j\in[n]$ the product
  $y_{1:n}\mapsto\chi(y_i)\chi(y_j)$ is $\nu^{\otimes n}$-integrable, as a product of two
  $L^2$ functions.

  \emph{Step 1: pointwise expansion.} For every $y_{1:n}\in\mathcal Y^n$, summing the constant
  $\bar\psi$ over the $n$ indices gives $\sum_{i=1}^n\chi(y_i)=\sum_{i=1}^n\psi(y_i)-n\bar\psi$,
  hence, dividing by $n\neq0$,
  \[
    \frac1n\sum_{i=1}^n\psi(y_i)-\bar\psi=\frac1n\sum_{i=1}^n\chi(y_i).
  \]
  Expanding the square of this sum as a double sum yields
  \[
    \Bigl(\frac1n\sum_{i=1}^n\psi(y_i)-\bar\psi\Bigr)^2
    =\frac{1}{n^2}\sum_{i=1}^n\sum_{j=1}^n\chi(y_i)\chi(y_j).
  \]

  \emph{Step 2: integration term by term.} Integrating the previous identity over
  $\mathcal Y^n$ against $\nu^{\otimes n}$ and using that all $n^2$ summands are integrable, so that
  the integral of the finite double sum is the double sum of the integrals, gives
  \[
    \mathbb E_{y_{1:n}}\Bigl[\Bigl(\frac1n\sum_{i=1}^n\psi(y_i)-\bar\psi\Bigr)^2\Bigr]
    =\frac{1}{n^2}\sum_{i=1}^n\sum_{j=1}^n
      \int_{\mathcal Y^n}\chi(y_i)\chi(y_j)\,d\nu^{\otimes n}.
  \]

  \emph{Step 3: the off-diagonal terms vanish.} Fix $i\in[n]$. For every $j\neq i$ we have
  $\int_{\mathcal Y^n}\chi(y_i)\chi(y_j)\,d\nu^{\otimes n}=0$ by
  \cref{lem:integral-pi-cross-term}, applied to the $\nu$-integrable function $\psi$; here $\psi$ is
  $\nu$-integrable because it lies in $L^2(\mathcal Y,\nu)$ and $\nu$ is a probability measure.
  Hence the inner sum over $j$ reduces to its single term $j=i$, which equals
  $\int_{\mathcal Y^n}\chi(y_i)^2\,d\nu^{\otimes n}$, so
  \[
    \mathbb E_{y_{1:n}}\Bigl[\Bigl(\frac1n\sum_{i=1}^n\psi(y_i)-\bar\psi\Bigr)^2\Bigr]
    =\frac{1}{n^2}\sum_{i=1}^n\int_{\mathcal Y^n}\chi(y_i)^2\,d\nu^{\otimes n}.
  \]

  \emph{Step 4: bounding the diagonal terms.} By \cref{lem:integral-pi-diagonal-term}, for every
  $i\in[n]$ we have $\int_{\mathcal Y^n}\chi(y_i)^2\,d\nu^{\otimes n}\le\int_{\mathcal Y}\psi^2\,d\nu$.
  Summing these $n$ inequalities gives
  $\sum_{i=1}^n\int_{\mathcal Y^n}\chi(y_i)^2\,d\nu^{\otimes n}\le n\int_{\mathcal Y}\psi^2\,d\nu$.
  Multiplying by the nonnegative factor $1/n^2$ preserves the inequality, and
  $\frac{1}{n^2}\cdot n\int_{\mathcal Y}\psi^2\,d\nu=\frac1n\int_{\mathcal Y}\psi^2\,d\nu$ because
  $n\neq0$. This is the claimed bound. -/)
  (title := /-- Mean squared error of an empirical mean -/)
  (latexEnv := "lemma")]
lemma iid_mean_squared_error {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n) (psi : Y → ℝ) (hpsi : MemLp psi 2 nu) :
    iid_expectation nu n
        (fun ys => ((n : ℝ)⁻¹ * ∑ i, psi (ys i) - ∫ y, psi y ∂nu) ^ 2)
      ≤ (n : ℝ)⁻¹ * ∫ y, (psi y) ^ 2 ∂nu := by
  set c : ℝ := ∫ y, psi y ∂nu with hc
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hchiLp : MemLp (fun y => psi y - c) 2 nu := hpsi.sub (memLp_const c)
  have hM : ∀ i : Fin n, MemLp (fun ys : Fin n → Y => psi (ys i) - c) 2
      (Measure.pi fun _ : Fin n => nu) := fun i =>
    hchiLp.comp_measurePreserving (measurePreserving_eval _ i)
  have hInt : ∀ i j : Fin n, Integrable
      (fun ys : Fin n → Y => (psi (ys i) - c) * (psi (ys j) - c))
      (Measure.pi fun _ : Fin n => nu) := fun i j => (hM i).integrable_mul (hM j)
  have hpoint : ∀ ys : Fin n → Y, ((n : ℝ)⁻¹ * ∑ i, psi (ys i) - c) ^ 2
      = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i, ∑ j, (psi (ys i) - c) * (psi (ys j) - c) := by
    intro ys
    have hsum : ∑ i, (psi (ys i) - c) = (∑ i, psi (ys i)) - (n : ℝ) * c := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.card_univ]
    have hshift : (n : ℝ)⁻¹ * ∑ i, psi (ys i) - c
        = (n : ℝ)⁻¹ * ∑ i, (psi (ys i) - c) := by
      rw [hsum]
      field_simp
    rw [hshift, ← Finset.sum_mul_sum]
    ring
  have hexpand : iid_expectation nu n
      (fun ys => ((n : ℝ)⁻¹ * ∑ i, psi (ys i) - c) ^ 2)
      = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i, ∑ j,
          ∫ ys, (psi (ys i) - c) * (psi (ys j) - c) ∂(Measure.pi fun _ : Fin n => nu) := by
    rw [iid_expectation, integral_congr_ae (Filter.Eventually.of_forall hpoint),
      integral_const_mul, integral_finset_sum _ fun i _ =>
        integrable_finset_sum _ fun j _ => hInt i j]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    exact integral_finset_sum _ fun j _ => hInt i j
  have hrow : ∀ i : Fin n, ∑ j,
      ∫ ys, (psi (ys i) - c) * (psi (ys j) - c) ∂(Measure.pi fun _ : Fin n => nu)
      = ∫ ys, (psi (ys i) - c) ^ 2 ∂(Measure.pi fun _ : Fin n => nu) := by
    intro i
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hj =>
      integral_pi_cross_term nu (Ne.symm hj) psi (hpsi.integrable one_le_two)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ys => (sq (psi (ys i) - c)).symm)
  have hdiag : ∑ i : Fin n,
      ∫ ys, (psi (ys i) - c) ^ 2 ∂(Measure.pi fun _ : Fin n => nu)
      ≤ (n : ℝ) * ∫ y, (psi y) ^ 2 ∂nu := by
    have hbound : ∑ i : Fin n, ∫ ys, (psi (ys i) - c) ^ 2 ∂(Measure.pi fun _ : Fin n => nu)
        ≤ ∑ _i : Fin n, ∫ y, (psi y) ^ 2 ∂nu :=
      Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        integral_pi_diagonal_term nu i psi hpsi
    simpa [Finset.card_univ, mul_comm] using hbound
  rw [hexpand, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hrow i]
  have hstep : (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i : Fin n,
      ∫ ys, (psi (ys i) - c) ^ 2 ∂(Measure.pi fun _ : Fin n => nu)
      ≤ (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ((n : ℝ) * ∫ y, (psi y) ^ 2 ∂nu) := by
    have hpos : (0 : ℝ) < (n : ℝ)⁻¹ * (n : ℝ)⁻¹ := by
      have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      positivity
    exact mul_le_mul_of_nonneg_left hdiag hpos.le
  refine hstep.trans_eq ?_
  field_simp

@[blueprint "lem:density-ess-sup-ae-bound"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space and let $f^\star:\mathcal X\to\mathbb R$
  satisfy $\|f^\star\|_\infty\neq\infty$, where $\|f^\star\|_\infty\in[0,\infty]$ denotes the
  essential supremum of $|f^\star|$ with respect to $\mu$. Then
  \[
    f^\star(x)\;\le\;\|f^\star\|_\infty
    \qquad\text{for }\mu\text{-almost every }x\in\mathcal X,
  \]
  the right-hand side being read as a real number. -/)
  (proof := /-- By the defining property of the essential supremum, the inequality
  $|f^\star(x)|\le\|f^\star\|_\infty$ holds in $[0,\infty]$ for $\mu$-almost every $x$. Fix such an
  $x$. Since $\|f^\star\|_\infty\neq\infty$ by hypothesis, the passage from $[0,\infty]$ to real
  numbers is monotone on the pair of values involved, so $|f^\star(x)|\le\|f^\star\|_\infty$ also
  holds as an inequality of real numbers; here we use that the real value of
  $|f^\star(x)|\in[0,\infty]$ is $|f^\star(x)|$, because $|f^\star(x)|\ge0$. Combining this with the
  elementary inequality $f^\star(x)\le|f^\star(x)|$ yields
  $f^\star(x)\le\|f^\star\|_\infty$. As the set of such $x$ has full measure, this proves the
  claim. -/)
  (title := /-- Almost-everywhere bound by the essential supremum -/)
  (latexEnv := "lemma")]
lemma density_ess_sup_ae_bound {X : Type*} [MeasurableSpace X] (mu : Measure X) (fstar : X → ℝ)
    (hfinf : eLpNormEssSup fstar mu ≠ ∞) :
    ∀ᵐ x ∂mu, fstar x ≤ (eLpNormEssSup fstar mu).toReal := by
  filter_upwards [enorm_ae_le_eLpNormEssSup fstar mu] with x hx
  have h1 : ‖fstar x‖ₑ.toReal ≤ (eLpNormEssSup fstar mu).toReal := ENNReal.toReal_mono hfinf hx
  have h2 : ‖fstar x‖ₑ.toReal = |fstar x| := by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]
  exact le_trans (le_abs_self _) (h2 ▸ h1)

@[blueprint "lem:orthonormal-integral-sq-eq-one"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space and let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family}. Then for every $\ell\in[r]$,
  \[
    \int_{\mathcal X}\varphi_\ell(x)^2\,d\mu(x)=1 .
  \]  -/)
  (proof := /-- Fix $\ell\in[r]$ and apply the orthonormality hypothesis of
  \cref{def:l2-orthonormal-family} with the pair of indices $(\ell,\ell)$; it gives
  $\int_{\mathcal X}\varphi_\ell(x)\varphi_\ell(x)\,d\mu(x)=\delta_{\ell\ell}=1$, since the
  Kronecker symbol takes the value $1$ on equal indices. Because
  $\varphi_\ell(x)^2=\varphi_\ell(x)\varphi_\ell(x)$ pointwise, the two integrands agree, and the
  displayed identity follows. -/)
  (title := /-- Unit $L^2$ norm of an orthonormal family member -/)
  (latexEnv := "lemma")]
lemma orthonormal_integral_sq_eq_one {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (hphi : l2_orthonormal_family mu phi) (l : Fin r) :
    ∫ x, (phi l x) ^ 2 ∂mu = 1 := by
  simpa [pow_two] using hphi l l

@[blueprint "lem:density-integral-eq-integral-mul"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space and let $f^\star:\mathcal X\to\mathbb R$
  be $\mu$-almost everywhere measurable with $f^\star\ge0$ $\mu$-almost everywhere. Write
  $\nu:=f^\star\,d\mu$ for the measure with density $x\mapsto\max(f^\star(x),0)$, viewed in
  $[0,\infty]$, with respect to $\mu$. Then for every $g:\mathcal X\to\mathbb R$,
  \[
    \int_{\mathcal X}g\,d\nu=\int_{\mathcal X}f^\star(x)\,g(x)\,d\mu(x),
  \]
  where both sides are Bochner integrals, taken to be $0$ when the integrand is not
  integrable. -/)
  (proof := /-- The density $x\mapsto\max(f^\star(x),0)$, viewed as a map into $[0,\infty]$, is
  $\mu$-almost everywhere measurable because $f^\star$ is, and it is finite everywhere, hence
  $\mu$-almost everywhere finite. The change-of-density formula for Bochner integrals with respect
  to a measure with an almost everywhere measurable, almost everywhere finite density therefore
  applies and gives
  \[
    \int_{\mathcal X}g\,d\nu=\int_{\mathcal X}\max(f^\star(x),0)\,g(x)\,d\mu(x),
  \]
  with $\max(f^\star(x),0)$ denoting the real value of the density at $x$. For $\mu$-almost every
  $x$ we have $f^\star(x)\ge0$ and hence $\max(f^\star(x),0)=f^\star(x)$, so the two integrands
  agree $\mu$-almost everywhere. Since the Bochner integral only depends on the $\mu$-almost
  everywhere equivalence class of the integrand, the right-hand side equals
  $\int_{\mathcal X}f^\star g\,d\mu$, which is the stated identity. -/)
  (title := /-- Integration against a nonnegative density -/)
  (latexEnv := "lemma")]
lemma density_integral_eq_integral_mul {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (fstar : X → ℝ) (hf0 : ∀ᵐ x ∂mu, 0 ≤ fstar x) (hfmeas : AEMeasurable fstar mu)
    (g : X → ℝ) :
    ∫ x, g x ∂(mu.withDensity fun x => ENNReal.ofReal (fstar x))
      = ∫ x, fstar x * g x ∂mu := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hfmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hf0] with x hx
  simp [ENNReal.toReal_ofReal hx]

@[blueprint "lem:density-second-moment-bound"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space, let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family} with $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every
  $\ell\in[r]$, and let $f^\star:\mathcal X\to\mathbb R$ satisfy
  $f^\star\ge0$ $\mu$-almost everywhere, $f^\star\in L^2(\mathcal X,\mu)$ and
  $\|f^\star\|_{\infty}<\infty$, where $\|f^\star\|_\infty$ denotes the essential supremum of
  $|f^\star|$ with respect to $\mu$. Then for every $\ell\in[r]$,
  \[
    \int_{\mathcal X}\varphi_\ell(x)^2\,d\nu(x)\;\le\;\|f^\star\|_\infty ,
  \]
  where $\nu$ denotes the measure with density $f^\star$ with respect to $\mu$, so that the
  left-hand side is the second moment of $\varphi_\ell$ under $\nu$ and equals
  $\int_{\mathcal X}\varphi_\ell^2f^\star\,d\mu$. -/)
  (proof := /-- Fix $\ell\in[r]$ and abbreviate $M:=\|f^\star\|_\infty$, a real number by
  hypothesis.

  First, $\int_{\mathcal X}M\varphi_\ell^2\,d\mu=M$. Indeed, the constant $M$ may be pulled out of
  the integral, and $\int_{\mathcal X}\varphi_\ell^2\,d\mu=1$ by
  \cref{lem:orthonormal-integral-sq-eq-one}, so the left-hand side equals $M\cdot1=M$.

  Next, since $f^\star$ is $\mu$-almost everywhere measurable, being in $L^2(\mathcal X,\mu)$, and
  $f^\star\ge0$ $\mu$-almost everywhere, \cref{lem:density-integral-eq-integral-mul} applied to the
  function $g=\varphi_\ell^2$ gives
  \[
    \int_{\mathcal X}\varphi_\ell^2\,d\nu=\int_{\mathcal X}f^\star\varphi_\ell^2\,d\mu .
  \]
  It therefore suffices to prove
  $\int_{\mathcal X}f^\star\varphi_\ell^2\,d\mu\le\int_{\mathcal X}M\varphi_\ell^2\,d\mu$, and we do
  so by monotonicity of the Bochner integral for a nonnegative integrand dominated by an integrable
  one. The three required inputs are verified as follows.

  The integrand on the left is nonnegative $\mu$-almost everywhere: for $\mu$-almost every $x$ we
  have $f^\star(x)\ge0$, and $\varphi_\ell(x)^2\ge0$ holds for every $x$, so the product
  $f^\star(x)\varphi_\ell(x)^2$ is nonnegative.

  The dominating integrand $x\mapsto M\varphi_\ell(x)^2$ is $\mu$-integrable: since
  $\varphi_\ell\in L^2(\mathcal X,\mu)$, the function $\varphi_\ell^2$ is $\mu$-integrable, and
  multiplying an integrable function by the constant $M$ preserves integrability.

  Finally, the domination holds $\mu$-almost everywhere: by
  \cref{lem:density-ess-sup-ae-bound} we have $f^\star(x)\le M$ for $\mu$-almost every $x$, and
  multiplying this inequality by the nonnegative factor $\varphi_\ell(x)^2$ gives
  $f^\star(x)\varphi_\ell(x)^2\le M\varphi_\ell(x)^2$ for $\mu$-almost every $x$.

  Combining the three inputs yields
  $\int_{\mathcal X}f^\star\varphi_\ell^2\,d\mu\le\int_{\mathcal X}M\varphi_\ell^2\,d\mu=M$, which is
  the stated bound. -/)
  (title := /-- Second moment of a basis function under the target density -/)
  (latexEnv := "lemma")]
lemma density_second_moment_bound {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (hphi : l2_orthonormal_family mu phi) (fstar : X → ℝ)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ fstar x) (hfmem : MemLp fstar 2 mu)
    (hfinf : eLpNormEssSup fstar mu ≠ ∞) (hmem : ∀ l, MemLp (phi l) 2 mu) (l : Fin r) :
    ∫ x, (phi l x) ^ 2 ∂(mu.withDensity fun x => ENNReal.ofReal (fstar x))
      ≤ (eLpNormEssSup fstar mu).toReal := by
  set M : ℝ := (eLpNormEssSup fstar mu).toReal
  have hMint : ∫ x, M * (phi l x) ^ 2 ∂mu = M := by
    rw [integral_const_mul, orthonormal_integral_sq_eq_one mu phi hphi l, mul_one]
  rw [density_integral_eq_integral_mul mu fstar hf0 hfmem.aemeasurable
    (fun x => (phi l x) ^ 2), ← hMint]
  refine integral_mono_of_nonneg ?_ (((hmem l).integrable_sq).const_mul M) ?_
  · filter_upwards [hf0] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  · filter_upwards [density_ess_sup_ae_bound mu fstar hfinf] with x hx
    exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

@[blueprint "lem:abs-le-ess-sup-ae"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space, let $f:\mathcal X\to\mathbb R$, and
  assume that the essential supremum $\|f\|_{L^\infty(\mathcal X,\mu)}$ is finite. Then
  \[
    |f(x)|\le\|f\|_{L^\infty(\mathcal X,\mu)}
    \qquad\text{for }\mu\text{-almost every }x\in\mathcal X .
  \] -/)
  (proof := /-- By the very definition of the essential supremum as an essential supremum of the
  extended norm, the inequality $\|f(x)\|_{\mathrm e}\le\|f\|_{L^\infty(\mathcal X,\mu)}$ holds in
  $[0,\infty]$ for $\mu$-almost every $x\in\mathcal X$. Fix such an $x$. Since
  $\|f\|_{L^\infty(\mathcal X,\mu)}$ is finite by hypothesis, the canonical projection
  $[0,\infty]\to\mathbb R$ is monotone on the pair of values under consideration, so it preserves
  this inequality. Finally, the extended norm $\|f(x)\|_{\mathrm e}$ is the image of the nonnegative
  real number $|f(x)|$ under the canonical embedding $[0,\infty)\hookrightarrow[0,\infty]$, and the
  projection $[0,\infty]\to\mathbb R$ inverts that embedding on nonnegative reals; hence the
  left-hand side becomes exactly $|f(x)|$, which is the claimed inequality. -/)
  (title := /-- Almost everywhere bound by the essential supremum -/)
  (latexEnv := "lemma")]
lemma abs_le_ess_sup_ae {X : Type*} [MeasurableSpace X] (mu : Measure X) (f : X → ℝ)
    (hf : eLpNormEssSup f mu ≠ ∞) :
    ∀ᵐ x ∂mu, |f x| ≤ (eLpNormEssSup f mu).toReal := by
  filter_upwards [MeasureTheory.ae_le_eLpNormEssSup (f := f) (μ := mu)] with x hx
  have h := ENNReal.toReal_mono hf hx
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg (f x))] at h

@[blueprint "lem:noise-sq-integrable-of-affine-sq"
  (statement := /-- Let $\eta$ be a probability measure on $\mathbb R$, let $c,a\in\mathbb R$ with
  $a\ne0$, and assume that the function $\varepsilon\mapsto\bigl((c+\varepsilon)a\bigr)^2$ is
  $\eta$-integrable. Then the function $\varepsilon\mapsto\varepsilon^2$ is $\eta$-integrable. -/)
  (proof := /-- Since $a\ne0$, the number $(a^2)^{-1}$ is well defined, and multiplying the
  $\eta$-integrable function $\varepsilon\mapsto\bigl((c+\varepsilon)a\bigr)^2$ by this constant
  again yields an $\eta$-integrable function. For every $\varepsilon\in\mathbb R$ we have
  $(a^2)^{-1}\bigl((c+\varepsilon)a\bigr)^2=(c+\varepsilon)^2$, because
  $\bigl((c+\varepsilon)a\bigr)^2=(c+\varepsilon)^2a^2$ and $a^2\ne0$. Hence the function
  $\varepsilon\mapsto(c+\varepsilon)^2$ is $\eta$-integrable.

  The function $\varepsilon\mapsto c+\varepsilon$ is continuous, hence strongly measurable, and for
  such a real-valued function integrability of its square is equivalent to membership in
  $L^2(\mathbb R,\eta)$; therefore $\varepsilon\mapsto c+\varepsilon$ belongs to
  $L^2(\mathbb R,\eta)$. Because $\eta$ is a probability measure, in particular a finite measure,
  the constant function $\varepsilon\mapsto c$ belongs to $L^2(\mathbb R,\eta)$ as well, and
  $L^2(\mathbb R,\eta)$ is closed under differences, so
  $\varepsilon\mapsto(c+\varepsilon)-c=\varepsilon$ belongs to $L^2(\mathbb R,\eta)$. Membership of
  a real-valued function in $L^2$ implies integrability of its square, which gives the
  $\eta$-integrability of $\varepsilon\mapsto\varepsilon^2$. -/)
  (title := /-- Square integrability of the noise from an affine second moment -/)
  (latexEnv := "lemma")]
lemma noise_sq_integrable_of_affine_sq (eta : Measure ℝ) [IsProbabilityMeasure eta] (c a : ℝ)
    (ha : a ≠ 0) (hint : Integrable (fun e => ((c + e) * a) ^ 2) eta) :
    Integrable (fun e : ℝ => e ^ 2) eta := by
  have h1 : Integrable (fun e => (c + e) ^ 2) eta := by
    have h : Integrable (fun e => (a ^ 2)⁻¹ * ((c + e) * a) ^ 2) eta := hint.const_mul _
    refine h.congr (Filter.Eventually.of_forall fun e => ?_)
    field_simp [mul_pow]
  have h2 : MemLp (fun e : ℝ => c + e) 2 eta :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h1
  have hc : MemLp (fun _ : ℝ => c) 2 eta := memLp_const _
  have h3 : MemLp (fun e : ℝ => e) 2 eta := by
    have h := h2.sub hc
    have heq : ((fun e : ℝ => c + e) - fun _ : ℝ => c) = fun e : ℝ => e := by
      funext e
      simp
    rwa [heq] at h
  exact h3.integrable_sq

@[blueprint "lem:affine-noise-sq-integrable"
  (statement := /-- Let $\eta$ be a probability measure on $\mathbb R$ such that
  $\varepsilon\mapsto\varepsilon^2$ is $\eta$-integrable, and let $c,a\in\mathbb R$. Then the
  function $\varepsilon\mapsto\bigl((c+\varepsilon)a\bigr)^2$ is $\eta$-integrable. -/)
  (proof := /-- The identity function on $\mathbb R$ is continuous, hence strongly measurable, so
  the assumed $\eta$-integrability of $\varepsilon\mapsto\varepsilon^2$ is equivalent to membership
  of $\varepsilon\mapsto\varepsilon$ in $L^2(\mathbb R,\eta)$. Since $\eta$ is a probability
  measure and $1\le2$, membership in $L^2(\mathbb R,\eta)$ implies $\eta$-integrability; hence
  $\varepsilon\mapsto\varepsilon$ is $\eta$-integrable.

  Consequently the function
  $\varepsilon\mapsto a^2c^2+2a^2c\,\varepsilon+a^2\varepsilon^2$ is $\eta$-integrable: the constant
  term is integrable because $\eta$ is a finite measure, the linear term is a constant multiple of
  the integrable identity function, and the quadratic term is a constant multiple of the integrable
  function $\varepsilon\mapsto\varepsilon^2$. Finally, for every $\varepsilon\in\mathbb R$ we have
  the algebraic identity
  $a^2c^2+2a^2c\,\varepsilon+a^2\varepsilon^2=\bigl((c+\varepsilon)a\bigr)^2$, so the two functions
  agree everywhere and the claimed integrability follows. -/)
  (title := /-- Integrability of the square of an affine function of the noise -/)
  (latexEnv := "lemma")]
lemma affine_noise_sq_integrable (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (he2 : Integrable (fun e : ℝ => e ^ 2) eta) (c a : ℝ) :
    Integrable (fun e => ((c + e) * a) ^ 2) eta := by
  have he1 : Integrable (fun e : ℝ => e) eta := by
    have h : MemLp (fun e : ℝ => e) 2 eta := (memLp_two_iff_integrable_sq (by fun_prop)).2 he2
    exact h.integrable one_le_two
  have hi : Integrable (fun e : ℝ => a ^ 2 * c ^ 2 + 2 * a ^ 2 * c * e + a ^ 2 * e ^ 2) eta :=
    ((integrable_const _).add (he1.const_mul _)).add (he2.const_mul _)
  refine hi.congr (Filter.Eventually.of_forall fun e => ?_)
  ring

@[blueprint "lem:affine-noise-sq-lintegral-eq-top"
  (statement := /-- Let $\eta$ be a probability measure on $\mathbb R$ such that
  $\varepsilon\mapsto\varepsilon^2$ is \emph{not} $\eta$-integrable, and let $c,a\in\mathbb R$ with
  $a\ne0$. Then the lower Lebesgue integral of the nonnegative function
  $\varepsilon\mapsto\bigl((c+\varepsilon)a\bigr)^2$ is infinite:
  \[
    \int_{\mathbb R}^{-}\bigl((c+\varepsilon)a\bigr)^2\,d\eta(\varepsilon)=\infty .
  \] -/)
  (proof := /-- The function $\varepsilon\mapsto\bigl((c+\varepsilon)a\bigr)^2$ is nonnegative
  everywhere, being a square, and it is continuous, hence strongly measurable. It is not
  $\eta$-integrable: if it were, then \cref{lem:noise-sq-integrable-of-affine-sq}, applied with the
  hypothesis $a\ne0$, would make $\varepsilon\mapsto\varepsilon^2$ $\eta$-integrable, contrary to
  assumption.

  Integrability is the conjunction of strong measurability and finiteness of the integral of the
  norm. Since strong measurability holds, the finiteness part must fail. For a nonnegative function
  the finiteness of the integral of the norm is equivalent to the strict inequality
  $\int^{-}\bigl((c+\varepsilon)a\bigr)^2\,d\eta<\infty$ in $[0,\infty]$, so this strict inequality
  fails. In $[0,\infty]$ a value is either strictly smaller than $\infty$ or equal to $\infty$;
  hence the lower Lebesgue integral equals $\infty$. -/)
  (title := /-- Infinite lower integral of an affine noise square -/)
  (latexEnv := "lemma")]
lemma affine_noise_sq_lintegral_eq_top (eta : Measure ℝ) [IsProbabilityMeasure eta] (c a : ℝ)
    (ha : a ≠ 0) (he2 : ¬ Integrable (fun e : ℝ => e ^ 2) eta) :
    ∫⁻ e, ENNReal.ofReal (((c + e) * a) ^ 2) ∂eta = ∞ := by
  have hmeas : AEStronglyMeasurable (fun e : ℝ => ((c + e) * a) ^ 2) eta := by fun_prop
  have hnf : ¬ HasFiniteIntegral (fun e : ℝ => ((c + e) * a) ^ 2) eta := fun h =>
    he2 (noise_sq_integrable_of_affine_sq eta c a ha ⟨hmeas, h⟩)
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun e => sq_nonneg _)] at hnf
  by_contra hcon
  exact hnf (lt_top_iff_ne_top.mpr hcon)

@[blueprint "lem:orthonormal-family-ne-zero-measure"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space and let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family}. Then for every $\ell\in[r]$ the set
  $\{x\in\mathcal X:\varphi_\ell(x)\ne0\}$ has nonzero $\mu$-measure. -/)
  (proof := /-- Fix $\ell\in[r]$ and suppose, for contradiction, that
  $\mu\bigl(\{x:\varphi_\ell(x)\ne0\}\bigr)=0$. By the characterisation of almost-everywhere
  statements as null complements, this says exactly that $\varphi_\ell(x)=0$ for $\mu$-almost every
  $x\in\mathcal X$. Then $\varphi_\ell(x)\varphi_\ell(x)=0$ for $\mu$-almost every $x$, so the
  integral of an almost-everywhere vanishing function gives
  \[
    \int_{\mathcal X}\varphi_\ell(x)\varphi_\ell(x)\,d\mu(x)=0 .
  \]
  On the other hand, the orthonormality hypothesis of \cref{def:l2-orthonormal-family} evaluated at
  the pair $(\ell,\ell)$ states that this same integral equals $1$, since the Kronecker symbol
  $\delta_{\ell\ell}$ equals $1$. Hence $1=0$, a contradiction. -/)
  (title := /-- An orthonormal basis function does not vanish almost everywhere -/)
  (latexEnv := "lemma")]
lemma orthonormal_family_ne_zero_measure {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (hphi : l2_orthonormal_family mu phi) (l : Fin r) :
    mu {x | phi l x ≠ 0} ≠ 0 := by
  intro h0
  have hae : ∀ᵐ x ∂mu, phi l x = 0 := MeasureTheory.ae_iff.mpr h0
  have hz : ∫ x, phi l x * phi l x ∂mu = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    simp [hx]
  rw [hphi l l] at hz
  simp at hz

@[blueprint "lem:affine-noise-sq-integral"
  (statement := /-- Let $\eta$ be a centered noise law on $\mathbb R$ with variance $\sigma^2$ in the
  sense of \cref{def:centered-noise}, assume that the function $\varepsilon\mapsto\varepsilon^2$ is
  $\eta$-integrable, and let $c,a\in\mathbb R$. Then
  \[
    \int_{\mathbb R}\bigl((c+\varepsilon)a\bigr)^2\,d\eta(\varepsilon)=(c^2+\sigma^2)\,a^2 .
  \] -/)
  (proof := /-- By \cref{def:centered-noise} the measure $\eta$ is a probability measure, the
  function $\varepsilon\mapsto\varepsilon$ is $\eta$-integrable, and
  $\int_{\mathbb R}\varepsilon\,d\eta=0$ and
  $\int_{\mathbb R}\varepsilon^2\,d\eta=\sigma^2$.

  Expanding the square gives, for every $\varepsilon\in\mathbb R$,
  \[
    \bigl((c+\varepsilon)a\bigr)^2
    =\bigl(a^2c^2+2a^2c\,\varepsilon\bigr)+a^2\varepsilon^2 .
  \]
  The function $\varepsilon\mapsto a^2c^2+2a^2c\,\varepsilon$ is $\eta$-integrable, being the sum of
  a constant function, integrable because $\eta$ is finite, and a constant multiple of the
  integrable identity function; the function $\varepsilon\mapsto a^2\varepsilon^2$ is
  $\eta$-integrable as a constant multiple of $\varepsilon\mapsto\varepsilon^2$. Additivity of the
  integral over this decomposition, applied twice, therefore gives
  \[
    \int_{\mathbb R}\bigl((c+\varepsilon)a\bigr)^2\,d\eta
    =a^2c^2\,\eta(\mathbb R)+2a^2c\int_{\mathbb R}\varepsilon\,d\eta
      +a^2\int_{\mathbb R}\varepsilon^2\,d\eta .
  \]
  Substituting $\eta(\mathbb R)=1$, $\int_{\mathbb R}\varepsilon\,d\eta=0$ and
  $\int_{\mathbb R}\varepsilon^2\,d\eta=\sigma^2$, the right-hand side equals
  $a^2c^2+a^2\sigma^2=(c^2+\sigma^2)a^2$, which is the claimed identity. -/)
  (title := /-- Second moment of an affine function of the noise -/)
  (latexEnv := "lemma")]
lemma affine_noise_sq_integral (eta : Measure ℝ) (sigma : ℝ) (heta : centered_noise eta sigma)
    (he2 : Integrable (fun e : ℝ => e ^ 2) eta) (c a : ℝ) :
    ∫ e, ((c + e) * a) ^ 2 ∂eta = (c ^ 2 + sigma ^ 2) * a ^ 2 := by
  haveI : IsProbabilityMeasure eta := heta.1
  have h0 : Integrable (fun _ : ℝ => a ^ 2 * c ^ 2) eta := integrable_const _
  have h1 : Integrable (fun e : ℝ => 2 * a ^ 2 * c * e) eta :=
    heta.2.2.2.1.const_mul _
  have h2 : Integrable (fun e : ℝ => a ^ 2 * e ^ 2) eta := he2.const_mul _
  calc
    (∫ e, ((c + e) * a) ^ 2 ∂eta) =
        ∫ e, (a ^ 2 * c ^ 2 + 2 * a ^ 2 * c * e) + a ^ 2 * e ^ 2 ∂eta := by
      apply integral_congr_ae
      filter_upwards with e
      ring
    _ = _ := integral_add (h0.add h1) h2
    _ = _ :=
      congrArg (fun x => x + ∫ e, a ^ 2 * e ^ 2 ∂eta) (integral_add h0 h1)
    _ = (c ^ 2 + sigma ^ 2) * a ^ 2 := by
      rw [integral_const, integral_const_mul, integral_const_mul, heta.2.1, heta.2.2.1]
      simp
      ring

@[blueprint "lem:regression-second-moment-bound"
  (statement := /-- Let $(\mathcal X,\mu)$ be a probability space, let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family} with $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every
  $\ell\in[r]$, let $f^\star\in L^2(\mathcal X,\mu)$ with
  $\|f^\star\|_\infty<\infty$, and let $\eta$ be a centered noise law on $\mathbb R$ with variance
  $\sigma^2$ in the sense of \cref{def:centered-noise}. Then for every $\ell\in[r]$,
  \[
    \int_{\mathcal X\times\mathbb R}
      \bigl((f^\star(x)+\varepsilon)\varphi_\ell(x)\bigr)^2\,d(\mu\otimes\eta)(x,\varepsilon)
    \;\le\;\|f^\star\|_\infty^2+\sigma^2 .
  \]
  -/)
  (proof := /-- Fix $\ell\in[r]$ and write $M:=\|f^\star\|_{L^\infty(\mathcal X,\mu)}$, so that
  $M\ge0$; by \cref{def:centered-noise} the measure $\eta$ is a probability measure. Two facts are
  used throughout. First, the orthonormality hypothesis of \cref{def:l2-orthonormal-family} at the
  pair $(\ell,\ell)$ gives $\int_{\mathcal X}\varphi_\ell^2\,d\mu=1$. Second,
  $\varphi_\ell\in L^2(\mathcal X,\mu)$ implies that $\varphi_\ell^2$ is $\mu$-integrable. Moreover,
  by \cref{lem:abs-le-ess-sup-ae} applied to $f^\star$, whose essential supremum is finite by
  hypothesis, we have $|f^\star(x)|\le M$ for $\mu$-almost every $x$.

  Write $F(x,\varepsilon):=\bigl((f^\star(x)+\varepsilon)\varphi_\ell(x)\bigr)^2$. The function $F$
  is $(\mu\otimes\eta)$-almost everywhere strongly measurable: the maps $(x,\varepsilon)\mapsto
  f^\star(x)$ and $(x,\varepsilon)\mapsto\varphi_\ell(x)$ are compositions of the almost everywhere
  strongly measurable functions $f^\star$ and $\varphi_\ell$ with the first projection, which is
  quasi measure preserving from $\mu\otimes\eta$ to $\mu$, the map
  $(x,\varepsilon)\mapsto\varepsilon$ is measurable, and sums, products and squares of almost
  everywhere strongly measurable functions are again almost everywhere strongly measurable. In
  particular $(x,\varepsilon)\mapsto\bigl[F(x,\varepsilon)\bigr]_{+}$, the image of $F$ under the
  canonical embedding $\mathbb R\to[0,\infty]$, is almost everywhere measurable, so Tonelli's
  theorem applies and yields
  \[
    \int^{-}_{\mathcal X\times\mathbb R}F\,d(\mu\otimes\eta)
    =\int^{-}_{\mathcal X}\Bigl(\int^{-}_{\mathbb R}F(x,\varepsilon)\,d\eta(\varepsilon)\Bigr)d\mu(x)
    \tag{$\ast$}
  \]
  for the lower Lebesgue integrals of the corresponding $[0,\infty]$-valued functions.

  We distinguish two cases.

  \emph{Case 1: $F$ is not $(\mu\otimes\eta)$-integrable.} Then the Bochner integral of $F$ is $0$
  by convention, while the right-hand side $M^2+\sigma^2$ is nonnegative because $M\ge0$; the
  inequality holds.

  \emph{Case 2: $F$ is $(\mu\otimes\eta)$-integrable.} We first claim that
  $\varepsilon\mapsto\varepsilon^2$ is $\eta$-integrable. Suppose it is not. For every
  $x\in\mathcal X$ with $\varphi_\ell(x)\ne0$, \cref{lem:affine-noise-sq-lintegral-eq-top} applied
  with $c=f^\star(x)$ and $a=\varphi_\ell(x)$ shows that the inner lower integral
  $\int^{-}_{\mathbb R}F(x,\varepsilon)\,d\eta(\varepsilon)$ equals $\infty$. Hence the set where
  that inner integral is infinite contains $\{x:\varphi_\ell(x)\ne0\}$, and by
  \cref{lem:orthonormal-family-ne-zero-measure} the latter set has nonzero $\mu$-measure; by
  monotonicity of null sets, the former set has nonzero $\mu$-measure too. The function
  $x\mapsto\int^{-}_{\mathbb R}F(x,\varepsilon)\,d\eta(\varepsilon)$ is $\mu$-almost everywhere
  measurable, being the partial lower integral of an almost everywhere measurable function on the
  product; therefore a function which is infinite on a set of positive measure has infinite lower
  integral, so the right-hand side of $(\ast)$ equals $\infty$. Consequently the left-hand side of
  $(\ast)$ is $\infty$ as well. But integrability of $F$ means, for the nonnegative function $F$,
  precisely that this lower integral is finite, a contradiction. This proves the claim.

  With $\varepsilon\mapsto\varepsilon^2$ $\eta$-integrable, \cref{lem:affine-noise-sq-integrable}
  shows that for every fixed $x\in\mathcal X$ the function
  $\varepsilon\mapsto F(x,\varepsilon)$ is $\eta$-integrable, and
  \cref{lem:affine-noise-sq-integral} evaluates its integral:
  \[
    \int_{\mathbb R}\bigl((f^\star(x)+\varepsilon)\varphi_\ell(x)\bigr)^2\,d\eta(\varepsilon)
    =\bigl(f^\star(x)^2+\sigma^2\bigr)\varphi_\ell(x)^2 .
  \]
  Since both sides are nonnegative and the inner integrand is $\eta$-integrable, the inner lower
  integral in $(\ast)$ is the image of this real number under the embedding
  $[0,\infty)\hookrightarrow[0,\infty]$.

  Next we bound the resulting $\mu$-integral. For every $x$ with $|f^\star(x)|\le M$ we have
  $f^\star(x)^2=|f^\star(x)|^2\le M^2$, hence, multiplying by $\varphi_\ell(x)^2\ge0$,
  \[
    f^\star(x)^2\varphi_\ell(x)^2\le M^2\varphi_\ell(x)^2 .
  \]
  This inequality holds for $\mu$-almost every $x$. It shows first that
  $x\mapsto f^\star(x)^2\varphi_\ell(x)^2$ is $\mu$-integrable, since it is almost everywhere
  strongly measurable and dominated in absolute value by the $\mu$-integrable function
  $M^2\varphi_\ell^2$; adding the $\mu$-integrable function $\sigma^2\varphi_\ell^2$ and rearranging
  algebraically shows that $x\mapsto\bigl(f^\star(x)^2+\sigma^2\bigr)\varphi_\ell(x)^2$ is
  $\mu$-integrable. It shows second, by monotonicity of the integral for nonnegative integrands,
  that
  \[
    \int_{\mathcal X}\bigl(f^\star(x)^2+\sigma^2\bigr)\varphi_\ell(x)^2\,d\mu(x)
    \le\int_{\mathcal X}\bigl(M^2+\sigma^2\bigr)\varphi_\ell(x)^2\,d\mu(x)
    =\bigl(M^2+\sigma^2\bigr)\int_{\mathcal X}\varphi_\ell^2\,d\mu
    =M^2+\sigma^2 ,
  \]
  where the last equality uses $\int_{\mathcal X}\varphi_\ell^2\,d\mu=1$.

  Finally we assemble the pieces. Since $F\ge0$ pointwise and $F$ is almost everywhere strongly
  measurable, its Bochner integral is the projection to $\mathbb R$ of the lower integral
  $\int^{-}F\,d(\mu\otimes\eta)$. As $M^2+\sigma^2\ge0$, it therefore suffices to prove that this
  lower integral is at most the image of $M^2+\sigma^2$ in $[0,\infty]$. Rewriting by $(\ast)$, then
  substituting the value of the inner integral computed above, and finally using that the
  $\mu$-integrand is nonnegative and $\mu$-integrable to pull the embedding
  $[0,\infty)\hookrightarrow[0,\infty]$ outside the $\mu$-integral, this reduces to the displayed
  real inequality
  $\int_{\mathcal X}\bigl(f^\star(x)^2+\sigma^2\bigr)\varphi_\ell(x)^2\,d\mu(x)\le M^2+\sigma^2$,
  which was just established. This completes the proof. -/)
  (title := /-- Second moment of a response times a basis function -/)
  (latexEnv := "lemma")]
lemma regression_second_moment_bound {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsProbabilityMeasure mu] {r : ℕ} (phi : Fin r → X → ℝ)
    (hphi : l2_orthonormal_family mu phi) (hmem : ∀ l, MemLp (phi l) 2 mu) (fstar : X → ℝ)
    (hfmem : MemLp fstar 2 mu) (hfinf : eLpNormEssSup fstar mu ≠ ∞) (eta : Measure ℝ) (sigma : ℝ)
    (heta : centered_noise eta sigma) (l : Fin r) :
    ∫ z, ((fstar z.1 + z.2) * phi l z.1) ^ 2 ∂(mu.prod eta)
      ≤ (eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2 := by
  haveI hprob : IsProbabilityMeasure eta := heta.1
  set M : ℝ := (eLpNormEssSup fstar mu).toReal
  have hMnn : (0:ℝ) ≤ M := ENNReal.toReal_nonneg
  have hphi2 : ∫ x, phi l x ^ 2 ∂mu = 1 := by simpa [sq] using hphi l l
  have hphiint : Integrable (fun x => phi l x ^ 2) mu := (hmem l).integrable_sq
  have habs := abs_le_ess_sup_ae mu fstar hfinf
  have hFm : AEStronglyMeasurable (fun z : X × ℝ => ((fstar z.1 + z.2) * phi l z.1) ^ 2)
      (mu.prod eta) := by
    have hf : AEStronglyMeasurable (fun z : X × ℝ => fstar z.1) (mu.prod eta) :=
      hfmem.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have hp : AEStronglyMeasurable (fun z : X × ℝ => phi l z.1) (mu.prod eta) :=
      (hmem l).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have hs : AEStronglyMeasurable (fun z : X × ℝ => z.2) (mu.prod eta) :=
      measurable_snd.aestronglyMeasurable
    exact ((hf.add hs).mul hp).pow 2
  have hFae : AEMeasurable
      (fun z : X × ℝ => ENNReal.ofReal (((fstar z.1 + z.2) * phi l z.1) ^ 2)) (mu.prod eta) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hFm.aemeasurable
  have hprodeq : ∫⁻ z, ENNReal.ofReal (((fstar z.1 + z.2) * phi l z.1) ^ 2) ∂(mu.prod eta)
      = ∫⁻ x, ∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta ∂mu :=
    lintegral_prod _ hFae
  by_cases hint : Integrable (fun z : X × ℝ => ((fstar z.1 + z.2) * phi l z.1) ^ 2) (mu.prod eta)
  · have he2 : Integrable (fun e : ℝ => e ^ 2) eta := by
      by_contra he2
      have hsub : {x | phi l x ≠ 0} ⊆
          {x | (∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta) = ∞} := fun x hx =>
        affine_noise_sq_lintegral_eq_top eta (fstar x) (phi l x) hx he2
      have hpos : mu {x | (∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta) = ∞} ≠ 0 :=
        fun h0 =>
          orthonormal_family_ne_zero_measure mu phi hphi l (measure_mono_null hsub h0)
      have hinnerm : AEMeasurable
          (fun x : X => ∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta) mu :=
        hFae.lintegral_prod_right'
      have htop : ∫⁻ x, ∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta ∂mu = ∞ :=
        lintegral_eq_top_of_measure_eq_top_ne_zero hinnerm hpos
      have hfin := hint.2
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => sq_nonneg _),
        hprodeq, htop] at hfin
      simp at hfin
    have hslice : ∀ x : X, Integrable (fun e => ((fstar x + e) * phi l x) ^ 2) eta := fun x =>
      affine_noise_sq_integrable eta he2 (fstar x) (phi l x)
    have hinner : ∀ x : X, ∫ e, ((fstar x + e) * phi l x) ^ 2 ∂eta
        = (fstar x ^ 2 + sigma ^ 2) * phi l x ^ 2 := fun x =>
      affine_noise_sq_integral eta sigma heta he2 (fstar x) (phi l x)
    have hsqle : ∀ x : X, |fstar x| ≤ M → fstar x ^ 2 * phi l x ^ 2 ≤ M ^ 2 * phi l x ^ 2 := by
      intro x hx
      have hsq : fstar x ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs (fstar x)]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hcomp : Integrable (fun x => (fstar x ^ 2 + sigma ^ 2) * phi l x ^ 2) mu := by
      have h1 : Integrable (fun x => fstar x ^ 2 * phi l x ^ 2) mu := by
        have hb : ∀ᵐ x ∂mu, ‖fstar x ^ 2 * phi l x ^ 2‖ ≤ M ^ 2 * phi l x ^ 2 := by
          filter_upwards [habs] with x hx
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact hsqle x hx
        exact Integrable.mono' (hphiint.const_mul _)
          ((hfmem.1.pow 2).mul ((hmem l).1.pow 2)) hb
      have h2 : Integrable (fun x => sigma ^ 2 * phi l x ^ 2) mu := hphiint.const_mul _
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]
      ring
    have hmono : ∫ x, (fstar x ^ 2 + sigma ^ 2) * phi l x ^ 2 ∂mu
        ≤ ∫ x, (M ^ 2 + sigma ^ 2) * phi l x ^ 2 ∂mu := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        (hphiint.const_mul _) ?_
      filter_upwards [habs] with x hx
      have := hsqle x hx
      nlinarith [this, sq_nonneg (phi l x)]
    have hgoal : ∫ x, (M ^ 2 + sigma ^ 2) * phi l x ^ 2 ∂mu = M ^ 2 + sigma ^ 2 := by
      rw [integral_const_mul, hphi2, mul_one]
    have hrw : ∀ x : X, ∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta
        = ENNReal.ofReal ((fstar x ^ 2 + sigma ^ 2) * phi l x ^ 2) := by
      intro x
      rw [← ofReal_integral_eq_lintegral_ofReal (hslice x)
        (Filter.Eventually.of_forall fun e => sq_nonneg _), hinner x]
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => sq_nonneg _) hFm]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    rw [hprodeq, lintegral_congr hrw, ← ofReal_integral_eq_lintegral_ofReal hcomp
      (Filter.Eventually.of_forall fun x => by positivity)]
    exact ENNReal.ofReal_le_ofReal (hmono.trans_eq hgoal)
  · rw [integral_undef hint]
    positivity

@[blueprint "lem:density-measure-le-smul"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space and let $f^\star:\mathcal X\to\mathbb R$
  satisfy $\|f^\star\|_\infty\neq\infty$, where $\|f^\star\|_\infty\in[0,\infty]$ denotes the
  essential supremum of $|f^\star|$ with respect to $\mu$, and write $M:=\|f^\star\|_\infty$ for its
  value read as a real number. Let $\nu$ be the measure with density
  $x\mapsto\max(f^\star(x),0)$, viewed in $[0,\infty]$, with respect to $\mu$. Then
  \[
    \nu\;\le\;M\,\mu ,
  \]
  an inequality of measures, that is $\nu(A)\le M\,\mu(A)$ for every measurable
  $A\subset\mathcal X$. -/)
  (proof := /-- By \cref{lem:density-ess-sup-ae-bound} we have $f^\star(x)\le M$ for
  $\mu$-almost every $x\in\mathcal X$. The canonical map $\mathbb R\to[0,\infty]$,
  $t\mapsto\max(t,0)$, is monotone, so for $\mu$-almost every $x$ the densities satisfy
  $\max(f^\star(x),0)\le\max(M,0)$ in $[0,\infty]$.

  The operation $h\mapsto\mu.\mathrm{withDensity}\,h$ is monotone in the density with respect to
  $\mu$-almost everywhere domination, hence the measure with density $x\mapsto\max(f^\star(x),0)$ is
  at most the measure with the constant density $\max(M,0)$. The measure with constant density
  $\max(M,0)$ is exactly $\max(M,0)\cdot\mu$, which is the asserted bound. -/)
  (title := /-- A bounded density is dominated by a multiple of the base measure -/)
  (latexEnv := "lemma")]
lemma density_measure_le_smul {X : Type*} [MeasurableSpace X] (mu : Measure X) (fstar : X → ℝ)
    (hfinf : eLpNormEssSup fstar mu ≠ ∞) :
    (mu.withDensity fun x => ENNReal.ofReal (fstar x))
      ≤ ENNReal.ofReal (eLpNormEssSup fstar mu).toReal • mu := by
  have hle : (fun x => ENNReal.ofReal (fstar x))
      ≤ᵐ[mu] fun _ => ENNReal.ofReal (eLpNormEssSup fstar mu).toReal := by
    filter_upwards [density_ess_sup_ae_bound mu fstar hfinf] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  have h := withDensity_mono hle
  rwa [withDensity_const] at h

@[blueprint "lem:memlp-of-density-bounded"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space, let $f^\star:\mathcal X\to\mathbb R$
  satisfy $\|f^\star\|_\infty\neq\infty$, and let $\nu$ be the measure with density
  $x\mapsto\max(f^\star(x),0)$, viewed in $[0,\infty]$, with respect to $\mu$. Then for every
  $p\in[0,\infty]$ and every $g:\mathcal X\to\mathbb R$ with $g\in L^p(\mathcal X,\mu)$ we have
  $g\in L^p(\mathcal X,\nu)$. -/)
  (proof := /-- Write $M:=\|f^\star\|_\infty$, read as a real number. By
  \cref{lem:density-measure-le-smul} the measures satisfy $\nu\le M\mu$, and the factor
  $\max(M,0)\in[0,\infty]$ is finite. If a measure is dominated by a finite multiple of another
  measure, then $L^p$ membership transfers from the larger measure to the smaller one: the
  domination forces absolute continuity, so almost everywhere strong measurability is inherited, and
  the $L^p$ seminorm with respect to $\nu$ is bounded by a finite multiple of the one with respect to
  $\mu$, which is finite because $g\in L^p(\mathcal X,\mu)$. Applying this to $g$ gives
  $g\in L^p(\mathcal X,\nu)$. -/)
  (title := /-- $L^p$ membership transfers to a measure with bounded density -/)
  (latexEnv := "lemma")]
lemma memlp_of_density_bounded {X : Type*} [MeasurableSpace X] (mu : Measure X) (fstar : X → ℝ)
    (hfinf : eLpNormEssSup fstar mu ≠ ∞) {p : ℝ≥0∞} (g : X → ℝ) (hg : MemLp g p mu) :
    MemLp g p (mu.withDensity fun x => ENNReal.ofReal (fstar x)) :=
  hg.of_measure_le_smul ENNReal.ofReal_ne_top (density_measure_le_smul mu fstar hfinf)

@[blueprint "lem:iid-expectation-norm-sq-sum"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal X$, let
  $r,n\in\mathbb N$, let $\psi=(\psi_\ell)_{\ell\in[r]}$ be real-valued functions on $\mathcal X$
  with $\psi_\ell\in L^2(\mathcal X,\nu)$ for every $\ell\in[r]$, and let $c\in\mathbb R^r$. For
  $x_{1:n}\in\mathcal X^n$ let $\widehat\psi(x_{1:n})\in\mathbb R^r$ be the vector with coordinates
  $\widehat\psi(x_{1:n})_\ell:=\frac1n\sum_{i=1}^n\psi_\ell(x_i)$. Then, with expectations taken
  under $n$ i.i.d. samples from $\nu$ as in \cref{def:iid-expectation},
  \[
    \mathbb E\bigl[\|\widehat\psi(x_{1:n})-c\|^2\bigr]
    =\sum_{\ell=1}^r\mathbb E\Bigl[\Bigl(\frac1n\sum_{i=1}^n\psi_\ell(x_i)-c_\ell\Bigr)^2\Bigr],
  \]
  where $\|\cdot\|$ is the Euclidean norm on $\mathbb R^r$. -/)
  (proof := /-- Fix $\ell\in[r]$ and put
  $F_\ell(x_{1:n}):=\frac1n\sum_{i=1}^n\psi_\ell(x_i)-c_\ell$.

  \emph{Step 1: each $F_\ell$ lies in $L^2(\mathcal X^n,\nu^{\otimes n})$.} For every $i\in[n]$ the
  coordinate projection $x_{1:n}\mapsto x_i$ is measure preserving from $\nu^{\otimes n}$ to $\nu$,
  so $x_{1:n}\mapsto\psi_\ell(x_i)$ lies in $L^2(\mathcal X^n,\nu^{\otimes n})$ because
  $\psi_\ell\in L^2(\mathcal X,\nu)$. A finite sum of $L^2$ functions is again in $L^2$, hence
  $x_{1:n}\mapsto\sum_{i=1}^n\psi_\ell(x_i)$ lies in $L^2(\mathcal X^n,\nu^{\otimes n})$;
  multiplying by the constant $1/n$ preserves this, and subtracting the constant function $c_\ell$,
  which is in $L^2$ because $\nu^{\otimes n}$ is a probability measure and hence finite, gives
  $F_\ell\in L^2(\mathcal X^n,\nu^{\otimes n})$. Consequently $F_\ell^2$ is
  $\nu^{\otimes n}$-integrable.

  \emph{Step 2: pointwise expansion of the squared norm.} For every $x_{1:n}\in\mathcal X^n$ the
  squared Euclidean norm on $\mathbb R^r$ is the sum of the squares of the coordinates, and the
  $\ell$-th coordinate of $\widehat\psi(x_{1:n})-c$ is $F_\ell(x_{1:n})$, so
  \[
    \|\widehat\psi(x_{1:n})-c\|^2=\sum_{\ell=1}^rF_\ell(x_{1:n})^2 .
  \]

  \emph{Step 3: exchanging the finite sum with the integral.} Integrating the identity of Step 2
  against $\nu^{\otimes n}$ and using that each of the $r$ summands $F_\ell^2$ is integrable by
  Step 1, the integral of the finite sum equals the sum of the integrals, which is the asserted
  identity. -/)
  (title := /-- Coordinatewise decomposition of the expected squared Euclidean error -/)
  (latexEnv := "lemma")]
lemma iid_expectation_norm_sq_sum {X : Type*} [MeasurableSpace X] (nu : Measure X)
    [IsProbabilityMeasure nu] {r : ℕ} (psi : Fin r → X → ℝ) (hpsi : ∀ l, MemLp (psi l) 2 nu)
    (n : ℕ) (c : EuclideanSpace ℝ (Fin r)) :
    iid_expectation nu n
        (fun xs => ‖(WithLp.toLp 2 fun l => (n : ℝ)⁻¹ * ∑ i, psi l (xs i)) - c‖ ^ 2)
      = ∑ l, iid_expectation nu n
          (fun xs => ((n : ℝ)⁻¹ * ∑ i, psi l (xs i) - c l) ^ 2) := by
  have hmem : ∀ l : Fin r,
      MemLp (fun xs : Fin n → X => (n : ℝ)⁻¹ * ∑ i, psi l (xs i) - c l) 2
        (Measure.pi fun _ : Fin n => nu) := by
    intro l
    have hcoord : ∀ i : Fin n, MemLp (fun xs : Fin n → X => psi l (xs i)) 2
        (Measure.pi fun _ : Fin n => nu) :=
      fun i => (hpsi l).comp_measurePreserving (measurePreserving_eval _ i)
    have hsum : MemLp (fun xs : Fin n → X => ∑ i, psi l (xs i)) 2
        (Measure.pi fun _ : Fin n => nu) :=
      memLp_finsetSum _ fun i _ => hcoord i
    exact (hsum.const_mul _).sub (memLp_const _)
  have hpt : ∀ xs : Fin n → X,
      ‖(WithLp.toLp 2 fun l => (n : ℝ)⁻¹ * ∑ i, psi l (xs i)) - c‖ ^ 2
        = ∑ l, ((n : ℝ)⁻¹ * ∑ i, psi l (xs i) - c l) ^ 2 := by
    intro xs
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  unfold iid_expectation
  simp only [hpt]
  exact integral_finsetSum _ fun l _ => (hmem l).integrable_sq

@[blueprint "lem:baseline-density-excess"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space and let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family} with $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every
  $\ell\in[r]$; write $\mathcal F:=\operatorname{span}\varphi$, an $r$-dimensional subspace. Let
  $f^\star:\mathcal X\to\mathbb R$ satisfy $f^\star\ge0$ $\mu$-almost everywhere,
  $f^\star\in L^2(\mathcal X,\mu)$ and $\|f^\star\|_\infty<\infty$, and assume that
  $\nu:=f^\star\,d\mu$ is a probability measure, so that $f^\star$ is a density with respect to
  $\mu$. Let $n\in\mathbb N$ with $n>0$ and let $x_1,\dots,x_n$ be i.i.d. samples from $\nu$. Then,
  with $\widehat\theta$ the projection density estimator of \cref{def:density-coeff-estimator} and
  $\theta(f^\star)$ the projected target of \cref{def:target-coeff},
  \[
    \mathbb E\bigl[\|\widehat\theta-\theta(f^\star)\|^2\bigr]\;\le\;\frac{\|f^\star\|_\infty}{n}\,r .
  \]
  Equivalently, by \cref{lem:parseval-coeff-norm}, the expected excess $L^2(\mathcal X)$ error of
  $\widehat f$ over $\mathcal F$ satisfies
  $\mathbb E[\|\widehat f-\Pi_{\mathcal F}f^\star\|_{L^2(\mathcal X)}^2]\le\|f^\star\|_\infty r/n$. -/)
  (proof := /-- Write $\nu$ for the measure with density $x\mapsto\max(f^\star(x),0)$, viewed in
  $[0,\infty]$, with respect to $\mu$; by hypothesis $\nu$ is a probability measure. For each
  $\ell\in[r]$ put $\theta_\ell:=\theta(f^\star)_\ell=\int_{\mathcal X}f^\star\varphi_\ell\,d\mu$ as
  in \cref{def:target-coeff}, and recall from \cref{def:density-coeff-estimator} that the
  coordinates of the estimator are the empirical means
  $\widehat\theta_\ell=\frac1n\sum_{i=1}^n\varphi_\ell(x_i)$.

  \emph{Step 1: each $\varphi_\ell$ lies in $L^2(\mathcal X,\nu)$.} Since
  $\|f^\star\|_\infty\neq\infty$ and $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every $\ell\in[r]$,
  \cref{lem:memlp-of-density-bounded} applied with $p=2$ and $g=\varphi_\ell$ gives
  $\varphi_\ell\in L^2(\mathcal X,\nu)$ for every $\ell\in[r]$.

  \emph{Step 2: the target coordinates are means under $\nu$.} Fix $\ell\in[r]$. Since $f^\star$ is
  $\mu$-almost everywhere measurable, being in $L^2(\mathcal X,\mu)$, and $f^\star\ge0$
  $\mu$-almost everywhere, \cref{lem:density-integral-eq-integral-mul} applied to the function
  $g=\varphi_\ell$ gives
  \[
    \int_{\mathcal X}\varphi_\ell\,d\nu=\int_{\mathcal X}f^\star\varphi_\ell\,d\mu=\theta_\ell ,
  \]
  so $\theta_\ell$ is exactly the mean of $\varphi_\ell$ under $\nu$.

  \emph{Step 3: coordinatewise decomposition.} By Step 1 the family $\varphi$ satisfies the
  hypotheses of \cref{lem:iid-expectation-norm-sq-sum} for the probability measure $\nu$, so with
  $c:=\theta(f^\star)$,
  \[
    \mathbb E\bigl[\|\widehat\theta-\theta(f^\star)\|^2\bigr]
    =\sum_{\ell=1}^r\mathbb E\Bigl[\Bigl(\frac1n\sum_{i=1}^n\varphi_\ell(x_i)-\theta_\ell\Bigr)^2\Bigr].
  \]

  \emph{Step 4: bounding each coordinate.} Fix $\ell\in[r]$. Rewriting $\theta_\ell$ as
  $\int_{\mathcal X}\varphi_\ell\,d\nu$ by Step 2 and applying
  \cref{lem:iid-mean-squared-error} to the probability measure $\nu$, the sample size $n>0$ and the
  function $\psi=\varphi_\ell$, which lies in $L^2(\mathcal X,\nu)$ by Step 1, yields
  \[
    \mathbb E\Bigl[\Bigl(\frac1n\sum_{i=1}^n\varphi_\ell(x_i)-\theta_\ell\Bigr)^2\Bigr]
    \le\frac1n\int_{\mathcal X}\varphi_\ell^2\,d\nu .
  \]
  By \cref{lem:density-second-moment-bound} we have
  $\int_{\mathcal X}\varphi_\ell^2\,d\nu\le\|f^\star\|_\infty$, and multiplying this inequality by
  the nonnegative factor $1/n$ gives
  $\mathbb E[(\frac1n\sum_{i=1}^n\varphi_\ell(x_i)-\theta_\ell)^2]\le\|f^\star\|_\infty/n$.

  \emph{Step 5: summation.} Summing the $r$ inequalities of Step 4 and substituting into the
  identity of Step 3 gives
  $\mathbb E[\|\widehat\theta-\theta(f^\star)\|^2]\le r\cdot\|f^\star\|_\infty/n
  =\|f^\star\|_\infty r/n$, as claimed. -/)
  (title := /-- Baseline excess risk: density estimation -/)
  (latexEnv := "lemma")]
lemma baseline_density_excess {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (hphi : l2_orthonormal_family mu phi) (hmem : ∀ l, MemLp (phi l) 2 mu)
    (fstar : X → ℝ) (hf0 : ∀ᵐ x ∂mu, 0 ≤ fstar x) (hfmem : MemLp fstar 2 mu)
    (hfinf : eLpNormEssSup fstar mu ≠ ∞)
    (hprob : IsProbabilityMeasure (mu.withDensity fun x => ENNReal.ofReal (fstar x)))
    (n : ℕ) (hn : 0 < n) :
    iid_expectation (mu.withDensity fun x => ENNReal.ofReal (fstar x)) n
        (fun xs => ‖density_coeff_estimator phi xs - target_coeff mu phi fstar‖ ^ 2)
      ≤ (eLpNormEssSup fstar mu).toReal * r / n := by
  set nu : Measure X := mu.withDensity fun x => ENNReal.ofReal (fstar x) with hnu
  have hphinu : ∀ l, MemLp (phi l) 2 nu := fun l =>
    memlp_of_density_bounded mu fstar hfinf (phi l) (hmem l)
  have hcoeff : ∀ l : Fin r, target_coeff mu phi fstar l = ∫ x, phi l x ∂nu := by
    intro l
    rw [hnu, density_integral_eq_integral_mul mu fstar hf0 hfmem.aemeasurable (phi l)]
    simp [target_coeff]
  have hsplit : iid_expectation nu n
      (fun xs => ‖density_coeff_estimator phi xs - target_coeff mu phi fstar‖ ^ 2)
      = ∑ l, iid_expectation nu n
          (fun xs => ((n : ℝ)⁻¹ * ∑ i, phi l (xs i) - target_coeff mu phi fstar l) ^ 2) :=
    iid_expectation_norm_sq_sum nu phi hphinu n (target_coeff mu phi fstar)
  have hterm : ∀ l : Fin r, iid_expectation nu n
      (fun xs => ((n : ℝ)⁻¹ * ∑ i, phi l (xs i) - target_coeff mu phi fstar l) ^ 2)
      ≤ (n : ℝ)⁻¹ * (eLpNormEssSup fstar mu).toReal := by
    intro l
    rw [hcoeff l]
    refine (iid_mean_squared_error nu n hn (phi l) (hphinu l)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (density_second_moment_bound mu phi hphi fstar hf0 hfmem hfinf hmem l)
      (by positivity)
  rw [hsplit]
  refine (Finset.sum_le_sum fun l _ => hterm l).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

@[blueprint "lem:memLp-of-integrable-affine-sq"
  (statement := /-- Let $(\mathcal Y,\nu)$ be a finite measure space, let
  $\psi:\mathcal Y\to\mathbb R$ be $\nu$-almost everywhere strongly measurable, and let
  $a,b\in\mathbb R$ with $a\neq0$. If the function $y\mapsto(a\psi(y)+b)^2$ is $\nu$-integrable,
  then $\psi\in L^2(\mathcal Y,\nu)$. -/)
  (proof := /-- The function $y\mapsto a\psi(y)+b$ is $\nu$-almost everywhere strongly measurable,
  being the sum of a constant multiple of $\psi$ and a constant function. For a real-valued almost
  everywhere strongly measurable function, membership in $L^2(\mathcal Y,\nu)$ is equivalent to
  $\nu$-integrability of its square; hence the hypothesis gives $a\psi+b\in L^2(\mathcal Y,\nu)$.
  Since $\nu$ is a finite measure, every constant function belongs to $L^2(\mathcal Y,\nu)$, and
  $L^2(\mathcal Y,\nu)$ is a vector space; therefore the function
  $y\mapsto a^{-1}\bigl(a\psi(y)+b\bigr)+\bigl(-a^{-1}b\bigr)$ belongs to $L^2(\mathcal Y,\nu)$.
  Because $a\neq0$, for every $y\in\mathcal Y$ we have
  $a^{-1}\bigl(a\psi(y)+b\bigr)+\bigl(-a^{-1}b\bigr)=\psi(y)$, so these two functions coincide
  pointwise, and membership in $L^2(\mathcal Y,\nu)$ depends only on the almost everywhere
  equivalence class of a function. Hence $\psi\in L^2(\mathcal Y,\nu)$. -/)
  (title := /-- $L^2$ membership from an integrable affine square -/)
  (latexEnv := "lemma")]
lemma memLp_of_integrable_affine_sq {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsFiniteMeasure nu] (psi : Y → ℝ) (hpsi : AEStronglyMeasurable psi nu) (a b : ℝ) (ha : a ≠ 0)
    (hint : Integrable (fun y => (a * psi y + b) ^ 2) nu) :
    MemLp psi 2 nu := by
  have h1 : MemLp (fun y => a * psi y + b) 2 nu :=
    (memLp_two_iff_integrable_sq ((hpsi.const_mul a).add aestronglyMeasurable_const)).2 hint
  have h2 : MemLp (fun y => a⁻¹ * (a * psi y + b) + -(a⁻¹ * b)) 2 nu :=
    (h1.const_mul a⁻¹).add (memLp_const _)
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun y => ?_)).mp h2
  field_simp
  ring

@[blueprint "lem:integrable-of-integrable-sum-nonneg"
  (statement := /-- Let $(\Omega,P)$ be a measure space, let $\iota$ be a finite index type, and for
  every $i\in\iota$ let $f_i:\Omega\to\mathbb R$ be $P$-almost everywhere strongly measurable with
  $f_i(\omega)\ge0$ for every $\omega\in\Omega$. If the function
  $\omega\mapsto\sum_{i\in\iota}f_i(\omega)$ is $P$-integrable, then $f_i$ is $P$-integrable for
  every $i\in\iota$. -/)
  (proof := /-- Fix $i\in\iota$. For every $\omega\in\Omega$ we have
  $\|f_i(\omega)\|=|f_i(\omega)|=f_i(\omega)$, because $f_i(\omega)\ge0$, and
  $f_i(\omega)\le\sum_{j\in\iota}f_j(\omega)$, because the finite sum has nonnegative terms and one
  of them is $f_i(\omega)$. Thus $f_i$ is $P$-almost everywhere strongly measurable and its norm is
  dominated pointwise by the $P$-integrable function $\omega\mapsto\sum_{j\in\iota}f_j(\omega)$;
  the domination criterion for integrability therefore gives that $f_i$ is $P$-integrable. -/)
  (title := /-- Integrability of a summand of a nonnegative integrable finite sum -/)
  (latexEnv := "lemma")]
lemma integrable_of_integrable_sum_nonneg {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) {iota : Type*} [Fintype iota] (f : iota → Omega → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (f i) P) (hnn : ∀ i w, 0 ≤ f i w)
    (hsum : Integrable (fun w => ∑ i, f i w) P) (i : iota) :
    Integrable (f i) P := by
  refine hsum.mono' (hmeas i) (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn i w)]
  exact Finset.single_le_sum (f := fun j => f j w) (fun j _ => hnn j w) (Finset.mem_univ i)

@[blueprint "lem:memLp-of-integrable-empirical-mean-sq"
  (statement := /-- Let $(\mathcal Y,\nu)$ be a probability space, let $\psi:\mathcal Y\to\mathbb R$
  be $\nu$-almost everywhere strongly measurable, let $c\in\mathbb R$, and let $n\in\mathbb N$ with
  $n>0$. If the function $y_{1:n}\mapsto\bigl(\tfrac1n\sum_{i=1}^n\psi(y_i)-c\bigr)^2$ is
  $\nu^{\otimes n}$-integrable, then $\psi\in L^2(\mathcal Y,\nu)$. -/)
  (proof := /-- Write $n=m+1$ with $m\in\mathbb N$. The measurable equivalence
  $e:\mathcal Y^n\to\mathcal Y\times\mathcal Y^m$ sending $y_{1:n}$ to
  $(y_0,(y_{j+1})_{j\in[m]})$ pushes $\nu^{\otimes n}$ forward to $\nu\otimes\nu^{\otimes m}$, by the
  measure-preserving property of the finite product decomposition. Splitting the sum over the first
  coordinate gives, for every $y_{1:n}$,
  \[
    \tfrac1n\sum_{i=1}^n\psi(y_i)-c
    =\tfrac1n\psi(y_0)+\Bigl(\tfrac1n\sum_{j=1}^m\psi(y_{j+1})-c\Bigr),
  \]
  so the integrand equals $G\circ e$, where
  $G(w,z):=\bigl(\tfrac1n\psi(w)+b(z)\bigr)^2$ with $b(z):=\tfrac1n\sum_{j=1}^m\psi(z_j)-c$. Since
  $e$ is a measure-preserving measurable embedding, $G$ is $\nu\otimes\nu^{\otimes m}$-integrable. By
  integrability of sections of an integrable function on a product measure, for
  $\nu^{\otimes m}$-almost every $z$ the function $w\mapsto\bigl(\tfrac1n\psi(w)+b(z)\bigr)^2$ is
  $\nu$-integrable; because $\nu^{\otimes m}$ is a probability measure its almost-everywhere sets are
  nonempty, so such a $z$ exists. Applying \cref{lem:memLp-of-integrable-affine-sq} with
  $a=\tfrac1n\neq0$ and $b=b(z)$, using that $\nu$ is a finite measure, yields
  $\psi\in L^2(\mathcal Y,\nu)$. -/)
  (title := /-- $L^2$ membership from an integrable empirical-mean square -/)
  (latexEnv := "lemma")]
lemma memLp_of_integrable_empirical_mean_sq {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] (psi : Y → ℝ) (hpsi : AEStronglyMeasurable psi nu) (c : ℝ) (n : ℕ)
    (hn : 0 < n)
    (hint : Integrable (fun ys : Fin n → Y => ((n : ℝ)⁻¹ * ∑ i, psi (ys i) - c) ^ 2)
      (Measure.pi fun _ : Fin n => nu)) :
    MemLp psi 2 nu := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Y) 0 with he
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (m + 1) => nu)
      (nu.prod (Measure.pi fun _ : Fin m => nu)) := by
    exact measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => nu) 0
  set G : Y × (Fin m → Y) → ℝ :=
    fun p => ((m + 1 : ℝ)⁻¹ * psi p.1 + ((m + 1 : ℝ)⁻¹ * ∑ j, psi (p.2 j) - c)) ^ 2 with hG
  have hcomp : (fun ys : Fin (m + 1) → Y =>
      (((m + 1 : ℕ) : ℝ)⁻¹ * ∑ i, psi (ys i) - c) ^ 2) = G ∘ e := by
    funext ys
    simp only [hG, Function.comp_apply, he, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv_symm_apply, Fin.removeNth, Fin.zero_succAbove]
    rw [Fin.sum_univ_succ]
    push_cast
    ring
  have hGint : Integrable G (nu.prod (Measure.pi fun _ : Fin m => nu)) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]; exact hcomp ▸ hint
  have hGmeas : AEMeasurable (fun p => ENNReal.ofReal (G p))
      (nu.prod (Measure.pi fun _ : Fin m => nu)) :=
    hGint.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfin : ∫⁻ p, ENNReal.ofReal (G p) ∂(nu.prod (Measure.pi fun _ : Fin m => nu)) ≠ ∞ := by
    have := hGint.2
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => by positivity)] at this
    exact this.ne
  rw [lintegral_prod_symm _ hGmeas] at hfin
  have hinnermeas : AEMeasurable (fun z => ∫⁻ w, ENNReal.ofReal (G (w, z)) ∂nu)
      (Measure.pi fun _ : Fin m => nu) := hGmeas.lintegral_prod_left'
  obtain ⟨z, hz⟩ := (ae_lt_top' hinnermeas hfin).exists
  have hsliceint : Integrable (fun w => G (w, z)) nu := by
    refine ⟨by simp only [hG]; fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w => by
      simp only [hG]; positivity)]
    exact hz
  refine memLp_of_integrable_affine_sq nu psi hpsi ((m : ℝ) + 1)⁻¹
    ((m + 1 : ℝ)⁻¹ * ∑ j, psi (z j) - c) (by positivity) ?_
  refine hsliceint.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [hG]

@[blueprint "lem:integrable-prod-mul-two"
  (statement := /-- Let $(\mathcal Y,\nu)$ and $(\mathcal Z,\tau)$ be probability spaces and let
  $f:\mathcal Y\to\mathbb R$ be $\nu$-integrable and $g:\mathcal Z\to\mathbb R$ be
  $\tau$-integrable. Then the separated product $(y,z)\mapsto f(y)g(z)$ is
  $\nu\otimes\tau$-integrable on $\mathcal Y\times\mathcal Z$. -/)
  (proof := /-- The two coordinate projections are quasi measure preserving, from $\nu\otimes\tau$
  to $\nu$ and to $\tau$ respectively, so $(y,z)\mapsto f(y)$ and $(y,z)\mapsto g(z)$ are
  $\nu\otimes\tau$-almost everywhere strongly measurable, and hence so is their product. It remains
  to verify that the product has finite integral, that is, that the lower Lebesgue integral of the
  extended norm $\|f(y)g(z)\|$ over $\nu\otimes\tau$ is finite. Multiplicativity of the extended
  norm gives $\|f(y)g(z)\|=\|f(y)\|\,\|g(z)\|$ pointwise, and for a separated product of two
  nonnegative measurable functions the lower Lebesgue integral over $\nu\otimes\tau$ factors as
  \[
    \int^{-}\|f(y)\|\,\|g(z)\|\,d(\nu\otimes\tau)
    =\Bigl(\int^{-}\|f\|\,d\nu\Bigr)\Bigl(\int^{-}\|g\|\,d\tau\Bigr).
  \]
  Both factors are finite, because $f$ is $\nu$-integrable and $g$ is $\tau$-integrable, and a
  product of two finite elements of $[0,\infty]$ is finite. -/)
  (title := /-- Integrability of a separated product over two distinct measures -/)
  (latexEnv := "lemma")]
lemma integrable_prod_mul_two {Y : Type*} {Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (nu : Measure Y) (tau : Measure Z) [IsProbabilityMeasure nu] [IsProbabilityMeasure tau]
    {f : Y → ℝ} {g : Z → ℝ} (hf : Integrable f nu) (hg : Integrable g tau) :
    Integrable (fun z : Y × Z => f z.1 * g z.2) (nu.prod tau) := by
  refine ⟨(hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
    (hg.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [enorm_mul]
  rw [lintegral_prod_mul hf.1.aemeasurable.enorm hg.1.aemeasurable.enorm]
  exact ENNReal.mul_lt_top (by rw [← hasFiniteIntegral_iff_enorm]; exact hf.2)
    (by rw [← hasFiniteIntegral_iff_enorm]; exact hg.2)

@[blueprint "lem:integral-prod-mul-two-of-nonneg"
  (statement := /-- Let $(\mathcal Y,\nu)$ and $(\mathcal Z,\tau)$ be probability spaces, let
  $f:\mathcal Y\to\mathbb R$ be $\nu$-almost everywhere strongly measurable and $\nu$-almost
  everywhere nonnegative, and let $g:\mathcal Z\to\mathbb R$ be $\tau$-almost everywhere strongly
  measurable and $\tau$-almost everywhere nonnegative. Then
  \[
    \int_{\mathcal Y\times\mathcal Z}f(y)g(z)\,d(\nu\otimes\tau)(y,z)
    =\Bigl(\int_{\mathcal Y}f\,d\nu\Bigr)\Bigl(\int_{\mathcal Z}g\,d\tau\Bigr).
  \]
  -/)
  (proof := /-- Since the coordinate projections are quasi measure preserving from $\nu\otimes\tau$
  to $\nu$ and to $\tau$, the functions $(y,z)\mapsto f(y)$ and $(y,z)\mapsto g(z)$ are
  $\nu\otimes\tau$-almost everywhere strongly measurable and $\nu\otimes\tau$-almost everywhere
  nonnegative; consequently their product is $\nu\otimes\tau$-almost everywhere nonnegative, being
  an almost everywhere product of two nonnegative quantities. For a nonnegative almost everywhere
  strongly measurable function the Bochner integral equals the real part of the lower Lebesgue
  integral of its nonnegative extension, so all three integrals in the claim may be rewritten in
  that form. Because $f(y)\ge0$ almost everywhere, the nonnegative extension of the product factors
  pointwise almost everywhere as the product of the nonnegative extensions, and for a separated
  product of two nonnegative measurable functions the lower Lebesgue integral over $\nu\otimes\tau$
  equals the product of the two lower Lebesgue integrals. Finally the passage to real values is
  multiplicative on $[0,\infty]$, which turns that product of lower Lebesgue integrals into the
  product of the two Bochner integrals. -/)
  (title := /-- Factorization of a nonnegative separated product over two distinct measures -/)
  (latexEnv := "lemma")]
lemma integral_prod_mul_two_of_nonneg {Y : Type*} {Z : Type*} [MeasurableSpace Y]
    [MeasurableSpace Z] (nu : Measure Y) (tau : Measure Z) [IsProbabilityMeasure nu]
    [IsProbabilityMeasure tau] {f : Y → ℝ} {g : Z → ℝ} (hf : AEStronglyMeasurable f nu)
    (hg : AEStronglyMeasurable g tau) (hf0 : 0 ≤ᵐ[nu] f) (hg0 : 0 ≤ᵐ[tau] g) :
    ∫ z : Y × Z, f z.1 * g z.2 ∂(nu.prod tau) = (∫ y, f y ∂nu) * ∫ w, g w ∂tau := by
  have hf1 : AEStronglyMeasurable (fun z : Y × Z => f z.1) (nu.prod tau) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hg1 : AEStronglyMeasurable (fun z : Y × Z => g z.2) (nu.prod tau) :=
    hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hf0' : ∀ᵐ z : Y × Z ∂(nu.prod tau), 0 ≤ f z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hf0
  have hg0' : ∀ᵐ z : Y × Z ∂(nu.prod tau), 0 ≤ g z.2 :=
    Measure.quasiMeasurePreserving_snd.ae hg0
  have hprod0 : 0 ≤ᵐ[nu.prod tau] fun z : Y × Z => f z.1 * g z.2 := by
    filter_upwards [hf0', hg0'] with z h1 h2 using mul_nonneg h1 h2
  rw [integral_eq_lintegral_of_nonneg_ae hprod0 (hf1.mul hg1),
    integral_eq_lintegral_of_nonneg_ae hf0 hf, integral_eq_lintegral_of_nonneg_ae hg0 hg,
    ← ENNReal.toReal_mul,
    ← lintegral_prod_mul hf.aemeasurable.ennreal_ofReal hg.aemeasurable.ennreal_ofReal]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hf0'] with z h1
  rw [ENNReal.ofReal_mul h1]

@[blueprint "lem:integral-prod-mul-two"
  (statement := /-- Let $(\mathcal Y,\nu)$ and $(\mathcal Z,\tau)$ be probability spaces and let
  $f:\mathcal Y\to\mathbb R$ be $\nu$-integrable and $g:\mathcal Z\to\mathbb R$ be
  $\tau$-integrable. Then
  \[
    \int_{\mathcal Y\times\mathcal Z}f(y)g(z)\,d(\nu\otimes\tau)(y,z)
    =\Bigl(\int_{\mathcal Y}f\,d\nu\Bigr)\Bigl(\int_{\mathcal Z}g\,d\tau\Bigr).
  \]
  -/)
  (proof := /-- Write $f^+:=\max(f,0)$ and $f^-:=\max(-f,0)$, and likewise $g^\pm$ for $g$. All four
  functions are nonnegative everywhere, and each is integrable, with respect to $\nu$ or to $\tau$,
  as the positive or negative part of an integrable function. Moreover $f=f^+-f^-$ and $g=g^+-g^-$
  pointwise: if $f(y)\ge0$ then $f^+(y)=f(y)$ and $f^-(y)=0$, while if $f(y)\le0$ then $f^+(y)=0$ and
  $f^-(y)=-f(y)$. Integrating the identity $f=f^+-f^-$ and using additivity of the integral on
  integrable functions gives $\int f\,d\nu=\int f^+\,d\nu-\int f^-\,d\nu$, and similarly for $g$.

  Expanding the product pointwise on $\mathcal Y\times\mathcal Z$,
  \[
    f(y)g(z)=\bigl(f^+(y)g^+(z)-f^+(y)g^-(z)\bigr)-\bigl(f^-(y)g^+(z)-f^-(y)g^-(z)\bigr).
  \]
  Each of the four separated products is $\nu\otimes\tau$-integrable by
  \cref{lem:integrable-prod-mul-two}, so the integral of the right-hand side splits into the four
  corresponding integrals by additivity, and each of them factors by
  \cref{lem:integral-prod-mul-two-of-nonneg} because the factors are nonnegative and almost
  everywhere strongly measurable. Therefore
  \[
    \int f(y)g(z)\,d(\nu\otimes\tau)
    =\Bigl(\int f^+\Bigr)\Bigl(\int g^+\Bigr)-\Bigl(\int f^+\Bigr)\Bigl(\int g^-\Bigr)
     -\Bigl(\int f^-\Bigr)\Bigl(\int g^+\Bigr)+\Bigl(\int f^-\Bigr)\Bigl(\int g^-\Bigr),
  \]
  which is exactly the expansion of
  $\bigl(\int f^+-\int f^-\bigr)\bigl(\int g^+-\int g^-\bigr)=\bigl(\int f\bigr)\bigl(\int g\bigr)$. -/)
  (title := /-- Factorization of a separated product integral over two distinct measures -/)
  (latexEnv := "lemma")]
lemma integral_prod_mul_two {Y : Type*} {Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (nu : Measure Y) (tau : Measure Z) [IsProbabilityMeasure nu] [IsProbabilityMeasure tau]
    {f : Y → ℝ} {g : Z → ℝ} (hf : Integrable f nu) (hg : Integrable g tau) :
    ∫ z : Y × Z, f z.1 * g z.2 ∂(nu.prod tau) = (∫ y, f y ∂nu) * ∫ w, g w ∂tau := by
  have hfp : Integrable (fun y => max (f y) 0) nu := hf.pos_part
  have hfn : Integrable (fun y => max (-f y) 0) nu := hf.neg_part
  have hgp : Integrable (fun w => max (g w) 0) tau := hg.pos_part
  have hgn : Integrable (fun w => max (-g w) 0) tau := hg.neg_part
  have hnnY : ∀ h : Y → ℝ, 0 ≤ᵐ[nu] fun y => max (h y) 0 :=
    fun h => Filter.Eventually.of_forall fun y => le_max_right _ _
  have hnnZ : ∀ h : Z → ℝ, 0 ≤ᵐ[tau] fun w => max (h w) 0 :=
    fun h => Filter.Eventually.of_forall fun w => le_max_right _ _
  have hsplitY : ∀ y : Y, f y = max (f y) 0 - max (-f y) 0 := by
    intro y
    rcases le_total 0 (f y) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  have hsplitZ : ∀ w : Z, g w = max (g w) 0 - max (-g w) 0 := by
    intro w
    rcases le_total 0 (g w) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  have hIpp := integrable_prod_mul_two nu tau hfp hgp
  have hIpn := integrable_prod_mul_two nu tau hfp hgn
  have hInp := integrable_prod_mul_two nu tau hfn hgp
  have hInn := integrable_prod_mul_two nu tau hfn hgn
  have hA : ∫ z : Y × Z, max (f z.1) 0 * max (g z.2) 0 ∂(nu.prod tau)
      = (∫ y, max (f y) 0 ∂nu) * ∫ w, max (g w) 0 ∂tau :=
    integral_prod_mul_two_of_nonneg nu tau hfp.1 hgp.1 (hnnY f) (hnnZ g)
  have hB : ∫ z : Y × Z, max (f z.1) 0 * max (-g z.2) 0 ∂(nu.prod tau)
      = (∫ y, max (f y) 0 ∂nu) * ∫ w, max (-g w) 0 ∂tau :=
    integral_prod_mul_two_of_nonneg nu tau hfp.1 hgn.1 (hnnY f) (hnnZ fun w => -g w)
  have hC : ∫ z : Y × Z, max (-f z.1) 0 * max (g z.2) 0 ∂(nu.prod tau)
      = (∫ y, max (-f y) 0 ∂nu) * ∫ w, max (g w) 0 ∂tau :=
    integral_prod_mul_two_of_nonneg nu tau hfn.1 hgp.1 (hnnY fun y => -f y) (hnnZ g)
  have hD : ∫ z : Y × Z, max (-f z.1) 0 * max (-g z.2) 0 ∂(nu.prod tau)
      = (∫ y, max (-f y) 0 ∂nu) * ∫ w, max (-g w) 0 ∂tau :=
    integral_prod_mul_two_of_nonneg nu tau hfn.1 hgn.1 (hnnY fun y => -f y)
      (hnnZ fun w => -g w)
  have hexp : ∀ z : Y × Z, f z.1 * g z.2
      = (max (f z.1) 0 * max (g z.2) 0 - max (f z.1) 0 * max (-g z.2) 0)
        - (max (-f z.1) 0 * max (g z.2) 0 - max (-f z.1) 0 * max (-g z.2) 0) := by
    intro z
    linear_combination (g z.2) * hsplitY z.1
      + (max (f z.1) 0 - max (-f z.1) 0) * hsplitZ z.2
  have hstep : ∫ z : Y × Z, f z.1 * g z.2 ∂(nu.prod tau)
      = (∫ z : Y × Z,
            (max (f z.1) 0 * max (g z.2) 0 - max (f z.1) 0 * max (-g z.2) 0) ∂(nu.prod tau))
        - ∫ z : Y × Z,
            (max (-f z.1) 0 * max (g z.2) 0 - max (-f z.1) 0 * max (-g z.2) 0) ∂(nu.prod tau) :=
    (integral_congr_ae (Filter.Eventually.of_forall hexp)).trans
      (integral_sub (hIpp.sub hIpn) (hInp.sub hInn))
  have hposSplit : ∫ z : Y × Z,
        (max (f z.1) 0 * max (g z.2) 0 - max (f z.1) 0 * max (-g z.2) 0) ∂(nu.prod tau)
      = (∫ z : Y × Z, max (f z.1) 0 * max (g z.2) 0 ∂(nu.prod tau))
        - ∫ z : Y × Z, max (f z.1) 0 * max (-g z.2) 0 ∂(nu.prod tau) :=
    integral_sub hIpp hIpn
  have hnegSplit : ∫ z : Y × Z,
        (max (-f z.1) 0 * max (g z.2) 0 - max (-f z.1) 0 * max (-g z.2) 0) ∂(nu.prod tau)
      = (∫ z : Y × Z, max (-f z.1) 0 * max (g z.2) 0 ∂(nu.prod tau))
        - ∫ z : Y × Z, max (-f z.1) 0 * max (-g z.2) 0 ∂(nu.prod tau) :=
    integral_sub hInp hInn
  have hfInt : ∫ y, f y ∂nu = (∫ y, max (f y) 0 ∂nu) - ∫ y, max (-f y) 0 ∂nu :=
    (integral_congr_ae (Filter.Eventually.of_forall hsplitY)).trans (integral_sub hfp hfn)
  have hgInt : ∫ w, g w ∂tau = (∫ w, max (g w) 0 ∂tau) - ∫ w, max (-g w) 0 ∂tau :=
    (integral_congr_ae (Filter.Eventually.of_forall hsplitZ)).trans (integral_sub hgp hgn)
  rw [hstep, hposSplit, hnegSplit, hA, hB, hC, hD, hfInt, hgInt]
  ring

@[blueprint "lem:baseline-regression-excess"
  (statement := /-- Let $(\mathcal X,\mu)$ be a probability space and let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family} with $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every
  $\ell\in[r]$; write $\mathcal F:=\operatorname{span}\varphi$. Let $f^\star\in L^2(\mathcal X,\mu)$
  with $\|f^\star\|_\infty<\infty$, let $\eta$ be a centered noise law on $\mathbb R$ with variance
  $\sigma^2$ in the sense of \cref{def:centered-noise}, let $n\in\mathbb N$ with $n>0$, and let the
  pairs $(x_i,\varepsilon_i)$, $i\in[n]$, be i.i.d. samples from $\mu\otimes\eta$, so that
  $y_i=f^\star(x_i)+\varepsilon_i$ with noise independent of the design. Then, with $\widehat\beta$
  the projection regression estimator of \cref{def:regression-coeff-estimator} and
  $\theta(f^\star)$ the projected target of \cref{def:target-coeff},
  \[
    \mathbb E\bigl[\|\widehat\beta-\theta(f^\star)\|^2\bigr]
    \;\le\;\frac{\|f^\star\|_\infty^2+\sigma^2}{n}\,r .
  \]
  -/)
  (proof := /-- For each $\ell\in[r]$ put
  $\beta_\ell:=\theta(f^\star)_\ell=\int_{\mathcal X}f^\star\varphi_\ell\,d\mu$. We first check that
  $\beta_\ell$ is the mean of the random variable $z=(x,\varepsilon)\mapsto(f^\star(x)+\varepsilon)\varphi_\ell(x)$
  under $\mu\otimes\eta$. Write $\Psi_\ell(x,\varepsilon)=(f^\star(x)+\varepsilon)\varphi_\ell(x)$ and
  assume first that $\Psi_\ell\in L^2(\mu\otimes\eta)$. Then $\varepsilon\mapsto\varepsilon^2$ is
  $\eta$-integrable: otherwise \cref{lem:affine-noise-sq-lintegral-eq-top} would force
  $\int^{-}\Psi_\ell(x,\varepsilon)^2\,d\eta(\varepsilon)=\infty$ at every $x$ with
  $\varphi_\ell(x)\neq0$, and by \cref{lem:orthonormal-family-ne-zero-measure} the set of such $x$
  has positive $\mu$-measure, so the iterated lower integral of $\Psi_\ell^2$ would be infinite,
  contradicting square integrability. Consequently $\varepsilon\mapsto\varepsilon$ is
  $\eta$-integrable as well. Splitting
  $\Psi_\ell(x,\varepsilon)=\bigl(f^\star(x)\varphi_\ell(x)\bigr)\cdot1+\varphi_\ell(x)\cdot\varepsilon$
  exhibits $\Psi_\ell$ as a sum of two separated products, each $\mu\otimes\eta$-integrable by
  \cref{lem:integrable-prod-mul-two}; factoring both integrals with
  \cref{lem:integral-prod-mul-two} and using the vanishing first moment of $\eta$ from
  \cref{def:centered-noise} gives
  \[
    \int(f^\star(x)+\varepsilon)\varphi_\ell(x)\,d(\mu\otimes\eta)
    =\int_{\mathcal X}f^\star\varphi_\ell\,d\mu+\Bigl(\int_{\mathbb R}\varepsilon\,d\eta\Bigr)\int_{\mathcal X}\varphi_\ell\,d\mu
    =\beta_\ell .
  \]
  By \cref{def:regression-coeff-estimator} the coordinates of the estimator are the empirical means
  $\widehat\beta_\ell=\frac1n\sum_{i=1}^n(f^\star(x_i)+\varepsilon_i)\varphi_\ell(x_i)$ of this
  random variable.

  Since the Euclidean norm is given by the sum of squared coordinates and the sum is finite,
  \[
    \mathbb E\bigl[\|\widehat\beta-\theta(f^\star)\|^2\bigr]
    =\sum_{\ell=1}^r\mathbb E\bigl[(\widehat\beta_\ell-\beta_\ell)^2\bigr].
  \]
  For each fixed $\ell$, \cref{lem:iid-mean-squared-error} applied to the probability measure
  $\mu\otimes\eta$ and to the function
  $\psi(x,\varepsilon)=(f^\star(x)+\varepsilon)\varphi_\ell(x)$, which is square integrable by
  \cref{lem:regression-second-moment-bound}, gives
  \[
    \mathbb E\bigl[(\widehat\beta_\ell-\beta_\ell)^2\bigr]
    \le\frac1n\int\bigl((f^\star(x)+\varepsilon)\varphi_\ell(x)\bigr)^2\,d(\mu\otimes\eta).
  \]
  By \cref{lem:regression-second-moment-bound} the integral on the right is at most
  $\|f^\star\|_\infty^2+\sigma^2$, so each summand is at most
  $(\|f^\star\|_\infty^2+\sigma^2)/n$.

  It remains to treat the degenerate branches, where the relevant Bochner integrals are undefined
  and therefore vanish by convention, while the asserted bounds are nonnegative because
  $\|f^\star\|_\infty^2+\sigma^2\ge0$ and $1/n\ge0$. If $\Psi_\ell\notin L^2(\mu\otimes\eta)$ for
  some $\ell$, then by \cref{lem:memLp-of-integrable-empirical-mean-sq} the coordinate square
  $z_{1:n}\mapsto(\widehat\beta_\ell-\beta_\ell)^2$ is not $(\mu\otimes\eta)^{\otimes n}$-integrable,
  so its expectation is $0$ and the per-coordinate bound holds trivially. Likewise, if some
  coordinate square fails to be integrable, then the total squared error cannot be integrable
  either: were it integrable, the coordinatewise identity above would make the finite sum of the
  nonnegative coordinate squares integrable, and \cref{lem:integrable-of-integrable-sum-nonneg}
  would return integrability of each individual summand. Hence the left-hand expectation is $0$ in
  that case and the bound again holds.

  Summing the $r$ per-coordinate estimates gives
  $r(\|f^\star\|_\infty^2+\sigma^2)/n$, which is the claimed bound. -/)
  (title := /-- Baseline excess risk: regression -/)
  (latexEnv := "lemma")]
lemma baseline_regression_excess {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsProbabilityMeasure mu] {r : ℕ} (phi : Fin r → X → ℝ)
    (hphi : l2_orthonormal_family mu phi) (hmem : ∀ l, MemLp (phi l) 2 mu) (fstar : X → ℝ)
    (hfmem : MemLp fstar 2 mu) (hfinf : eLpNormEssSup fstar mu ≠ ∞) (eta : Measure ℝ) (sigma : ℝ)
    (heta : centered_noise eta sigma) (n : ℕ) (hn : 0 < n) :
    iid_expectation (mu.prod eta) n
        (fun zs => ‖regression_coeff_estimator phi fstar zs - target_coeff mu phi fstar‖ ^ 2)
      ≤ ((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * r / n := by
  haveI hprob : IsProbabilityMeasure eta := heta.1
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set M : ℝ := (eLpNormEssSup fstar mu).toReal with hMdef
  set beta : Fin r → ℝ := fun l => ∫ x, fstar x * phi l x ∂mu with hbeta
  set Psi : Fin r → (X × ℝ) → ℝ := fun l z => (fstar z.1 + z.2) * phi l z.1 with hPsi
  have hPsimeas : ∀ l, AEStronglyMeasurable (Psi l) (mu.prod eta) := fun l =>
    ((hfmem.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).add
        measurable_snd.aestronglyMeasurable).mul
      ((hmem l).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have hcoord : ∀ zs : Fin n → X × ℝ,
      ‖regression_coeff_estimator phi fstar zs - target_coeff mu phi fstar‖ ^ 2
        = ∑ l, ((n : ℝ)⁻¹ * ∑ i, Psi l (zs i) - beta l) ^ 2 := by
    intro zs
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [regression_coeff_estimator, target_coeff, hPsi, hbeta]
  have hterm : ∀ l : Fin r, iid_expectation (mu.prod eta) n
      (fun ys => ((n : ℝ)⁻¹ * ∑ i, Psi l (ys i) - beta l) ^ 2) ≤ (n : ℝ)⁻¹ * (M ^ 2 + sigma ^ 2) := by
    intro l
    by_cases hml : MemLp (Psi l) 2 (mu.prod eta)
    · have hmean : ∫ z, Psi l z ∂(mu.prod eta) = beta l := by
        have he2 : Integrable (fun e : ℝ => e ^ 2) eta := by
          by_contra hcon
          have hint : Integrable (fun z : X × ℝ => ((fstar z.1 + z.2) * phi l z.1) ^ 2)
              (mu.prod eta) := by
            have hsq := hml.integrable_sq
            refine hsq.congr (Filter.Eventually.of_forall fun z => ?_)
            simp [hPsi]
          have hFm : AEStronglyMeasurable
              (fun z : X × ℝ => ((fstar z.1 + z.2) * phi l z.1) ^ 2) (mu.prod eta) := by
            have hf : AEStronglyMeasurable (fun z : X × ℝ => fstar z.1) (mu.prod eta) :=
              hfmem.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
            have hp : AEStronglyMeasurable (fun z : X × ℝ => phi l z.1) (mu.prod eta) :=
              (hmem l).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
            have hs : AEStronglyMeasurable (fun z : X × ℝ => z.2) (mu.prod eta) :=
              measurable_snd.aestronglyMeasurable
            exact ((hf.add hs).mul hp).pow 2
          have hFae : AEMeasurable
              (fun z : X × ℝ => ENNReal.ofReal (((fstar z.1 + z.2) * phi l z.1) ^ 2))
              (mu.prod eta) :=
            ENNReal.measurable_ofReal.comp_aemeasurable hFm.aemeasurable
          have hprodeq :
              ∫⁻ z, ENNReal.ofReal (((fstar z.1 + z.2) * phi l z.1) ^ 2) ∂(mu.prod eta)
                = ∫⁻ x, ∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta ∂mu :=
            lintegral_prod _ hFae
          have hsub : {x | phi l x ≠ 0} ⊆
              {x | (∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta) = ∞} := fun x hx =>
            affine_noise_sq_lintegral_eq_top eta (fstar x) (phi l x) hx hcon
          have hpos :
              mu {x | (∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta) = ∞} ≠ 0 :=
            fun h0 =>
              orthonormal_family_ne_zero_measure mu phi hphi l (measure_mono_null hsub h0)
          have hinnerm : AEMeasurable
              (fun x : X => ∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta) mu :=
            hFae.lintegral_prod_right'
          have htop : ∫⁻ x, ∫⁻ e, ENNReal.ofReal (((fstar x + e) * phi l x) ^ 2) ∂eta ∂mu = ∞ :=
            lintegral_eq_top_of_measure_eq_top_ne_zero hinnerm hpos
          have hfin := hint.2
          rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => sq_nonneg _),
            hprodeq, htop] at hfin
          simp at hfin
        have he1 : Integrable (fun e : ℝ => e) eta :=
          ((memLp_two_iff_integrable_sq (by fun_prop)).2 he2).integrable one_le_two
        have hfphi : Integrable (fun x : X => fstar x * phi l x) mu :=
          hfmem.integrable_mul (hmem l)
        have hphil : Integrable (fun x : X => phi l x) mu :=
          (hmem l).integrable one_le_two
        have hone : Integrable (fun _ : ℝ => (1 : ℝ)) eta := integrable_const 1
        have hI1 : Integrable (fun z : X × ℝ => (fstar z.1 * phi l z.1) * (1 : ℝ))
            (mu.prod eta) :=
          integrable_prod_mul_two mu eta hfphi hone
        have hI2 : Integrable (fun z : X × ℝ => phi l z.1 * z.2) (mu.prod eta) :=
          integrable_prod_mul_two mu eta hphil he1
        have hint1 : ∫ z : X × ℝ, (fun x => fstar x * phi l x) z.1 * (fun _ : ℝ => (1 : ℝ)) z.2
            ∂(mu.prod eta) = (∫ x, fstar x * phi l x ∂mu) * ∫ _e, (1 : ℝ) ∂eta :=
          integral_prod_mul_two mu eta hfphi hone
        have hint2 : ∫ z : X × ℝ, (fun x => phi l x) z.1 * (fun e : ℝ => e) z.2 ∂(mu.prod eta)
            = (∫ x, phi l x ∂mu) * ∫ e, e ∂eta :=
          integral_prod_mul_two mu eta hphil he1
        rw [hPsi]
        rw [integral_congr_ae (Filter.Eventually.of_forall fun z : X × ℝ =>
            show (fstar z.1 + z.2) * phi l z.1 = fstar z.1 * phi l z.1 + phi l z.1 * z.2
              from by ring),
          integral_add (by simpa using hI1) hI2, show
            (∫ z : X × ℝ, fstar z.1 * phi l z.1 ∂(mu.prod eta))
              = ∫ z : X × ℝ, (fun x => fstar x * phi l x) z.1 * (fun _ : ℝ => (1 : ℝ)) z.2
                ∂(mu.prod eta) from by simp,
          hint1, hint2, heta.2.1]
        simp [hbeta]
      have hmse := iid_mean_squared_error (mu.prod eta) n hn (Psi l) hml
      rw [hmean] at hmse
      refine hmse.trans ?_
      have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left
        (regression_second_moment_bound mu phi hphi hmem fstar hfmem hfinf eta sigma heta l) hinv
    · have hnotint : ¬ Integrable
          (fun ys : Fin n → X × ℝ => ((n : ℝ)⁻¹ * ∑ i, Psi l (ys i) - beta l) ^ 2)
          (Measure.pi fun _ : Fin n => mu.prod eta) := by
        intro hcon
        exact hml (memLp_of_integrable_empirical_mean_sq (mu.prod eta) (Psi l) (hPsimeas l)
          (beta l) n hn hcon)
      rw [iid_expectation, integral_undef hnotint]
      have hMnn : (0 : ℝ) ≤ M := ENNReal.toReal_nonneg
      positivity
  have hsum : iid_expectation (mu.prod eta) n
      (fun zs => ‖regression_coeff_estimator phi fstar zs - target_coeff mu phi fstar‖ ^ 2)
      ≤ ∑ _l : Fin r, (n : ℝ)⁻¹ * (M ^ 2 + sigma ^ 2) := by
    by_cases hallint : ∀ l : Fin r, Integrable
        (fun ys : Fin n → X × ℝ => ((n : ℝ)⁻¹ * ∑ i, Psi l (ys i) - beta l) ^ 2)
        (Measure.pi fun _ : Fin n => mu.prod eta)
    · have hsplit : iid_expectation (mu.prod eta) n
          (fun zs => ‖regression_coeff_estimator phi fstar zs - target_coeff mu phi fstar‖ ^ 2)
          = ∑ l, iid_expectation (mu.prod eta) n
              (fun ys => ((n : ℝ)⁻¹ * ∑ i, Psi l (ys i) - beta l) ^ 2) := by
        rw [iid_expectation, integral_congr_ae (Filter.Eventually.of_forall hcoord),
          integral_finsetSum _ fun l _ => hallint l]
        rfl
      rw [hsplit]
      exact Finset.sum_le_sum fun l _ => hterm l
    · obtain ⟨l0, hl0⟩ := not_forall.mp hallint
      have hnotint : ¬ Integrable
          (fun zs : Fin n → X × ℝ =>
            ‖regression_coeff_estimator phi fstar zs - target_coeff mu phi fstar‖ ^ 2)
          (Measure.pi fun _ : Fin n => mu.prod eta) := by
        intro hcon
        refine hl0 ?_
        have hcon' : Integrable
            (fun zs : Fin n → X × ℝ => ∑ l, ((n : ℝ)⁻¹ * ∑ i, Psi l (zs i) - beta l) ^ 2)
            (Measure.pi fun _ : Fin n => mu.prod eta) :=
          hcon.congr (Filter.Eventually.of_forall hcoord)
        have hmeasfam : ∀ l : Fin r, AEStronglyMeasurable
            (fun zs : Fin n → X × ℝ => ((n : ℝ)⁻¹ * ∑ i, Psi l (zs i) - beta l) ^ 2)
            (Measure.pi fun _ : Fin n => mu.prod eta) := by
          intro l
          have hev : ∀ i : Fin n, AEStronglyMeasurable
              (fun zs : Fin n → X × ℝ => Psi l (zs i))
              (Measure.pi fun _ : Fin n => mu.prod eta) := fun i =>
            (hPsimeas l).comp_measurePreserving
              (measurePreserving_eval (fun _ : Fin n => mu.prod eta) i)
          have hsummeas : AEStronglyMeasurable
              (fun zs : Fin n → X × ℝ => ∑ i, Psi l (zs i))
              (Measure.pi fun _ : Fin n => mu.prod eta) :=
            Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ => hev i
          have hscaled : AEStronglyMeasurable
              (fun zs : Fin n → X × ℝ => (n : ℝ)⁻¹ * ∑ i, Psi l (zs i))
              (Measure.pi fun _ : Fin n => mu.prod eta) :=
            hsummeas.const_mul ((n : ℝ)⁻¹)
          have hshift : AEStronglyMeasurable
              (fun zs : Fin n → X × ℝ => (n : ℝ)⁻¹ * ∑ i, Psi l (zs i) - beta l)
              (Measure.pi fun _ : Fin n => mu.prod eta) :=
            hscaled.sub aestronglyMeasurable_const
          exact hshift.pow 2
        exact integrable_of_integrable_sum_nonneg (Measure.pi fun _ : Fin n => mu.prod eta)
          (fun l zs => ((n : ℝ)⁻¹ * ∑ i, Psi l (zs i) - beta l) ^ 2) hmeasfam
          (fun l zs => sq_nonneg _) hcon' l0
      rw [iid_expectation, integral_undef hnotint]
      have hMnn : (0 : ℝ) ≤ M := ENNReal.toReal_nonneg
      have : (0 : ℝ) ≤ ∑ _l : Fin r, (n : ℝ)⁻¹ * (M ^ 2 + sigma ^ 2) := by
        refine Finset.sum_nonneg fun l _ => ?_
        positivity
      exact this
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

@[blueprint "lem:uniform-group-expectation-sum-eq"
  (statement := /-- Let $G$ be a finite nonempty type, let $m\in\mathbb N$, let $I$ be a type, let
  $s$ be a finite subset of $I$ and let $\Psi_i:G^m\to\mathbb R$ be a function for every $i\in I$.
  Then the expectation of \cref{def:uniform-group-expectation} commutes with the finite sum over
  $s$, that is
  \[
    \mathbb E_S\Bigl[\sum_{i\in s}\Psi_i(S)\Bigr]=\sum_{i\in s}\mathbb E_S\bigl[\Psi_i(S)\bigr].
  \]
  -/)
  (proof := /-- By \cref{def:uniform-group-expectation}, the left-hand side is
  \[
    |G|^{-m}\sum_{S\in G^m}\sum_{i\in s}\Psi_i(S),
  \]
  and the right-hand side is $\sum_{i\in s}|G|^{-m}\sum_{S\in G^m}\Psi_i(S)$. Distributing the
  constant $|G|^{-m}$ over the finite sum turns the right-hand side into
  $\sum_{i\in s}\sum_{S\in G^m}|G|^{-m}\Psi_i(S)$, and the same distribution applied to the
  left-hand side turns it into $\sum_{S\in G^m}\sum_{i\in s}|G|^{-m}\Psi_i(S)$. Both index sets
  $G^m$ and $s$ are finite, so the two iterated finite sums may be interchanged, which identifies
  the two expressions. -/)
  (title := /-- Additivity of the uniform augmentation expectation -/)
  (latexEnv := "lemma")]
lemma uniform_group_expectation_sum_eq {G : Type*} [Fintype G] {m : ℕ} {I : Type*} (s : Finset I)
    (Psi : I → (Fin m → G) → ℝ) :
    uniform_group_expectation m (fun S => ∑ i ∈ s, Psi i S)
      = ∑ i ∈ s, uniform_group_expectation m (Psi i) := by
  simp only [uniform_group_expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

@[blueprint "lem:uniform-group-expectation-const-mul-eq"
  (statement := /-- Let $G$ be a finite nonempty type, let $m\in\mathbb N$, let $a\in\mathbb R$ and
  let $\Psi:G^m\to\mathbb R$. Then the expectation of \cref{def:uniform-group-expectation} is
  homogeneous, that is
  \[
    \mathbb E_S\bigl[a\,\Psi(S)\bigr]=a\,\mathbb E_S\bigl[\Psi(S)\bigr].
  \]
  -/)
  (proof := /-- By \cref{def:uniform-group-expectation} the left-hand side equals
  $|G|^{-m}\sum_{S\in G^m}a\,\Psi(S)$ and the right-hand side equals
  $a\,|G|^{-m}\sum_{S\in G^m}\Psi(S)$. Distributing the constants $|G|^{-m}$ and $a$ over the
  finite sum $\sum_{S\in G^m}$ writes both sides as $\sum_{S\in G^m}a\,|G|^{-m}\Psi(S)$, up to the
  commutativity and associativity of multiplication in $\mathbb R$ inside each summand. -/)
  (title := /-- Homogeneity of the uniform augmentation expectation -/)
  (latexEnv := "lemma")]
lemma uniform_group_expectation_const_mul_eq {G : Type*} [Fintype G] {m : ℕ} (a : ℝ)
    (Psi : (Fin m → G) → ℝ) :
    uniform_group_expectation m (fun S => a * Psi S) = a * uniform_group_expectation m Psi := by
  simp only [uniform_group_expectation, Finset.mul_sum]
  ring_nf

@[blueprint "lem:uniform-group-expectation-prod-eq"
  (statement := /-- Let $G$ be a finite nonempty type, let $m\in\mathbb N$ and let
  $w_k:G\to\mathbb R$ be a function for every $k\in[m]$. Then the expectation of
  \cref{def:uniform-group-expectation} of the product of the coordinatewise factors factorizes,
  \[
    \mathbb E_S\Bigl[\prod_{k=1}^mw_k(S_k)\Bigr]
    =\prod_{k=1}^m\Bigl(|G|^{-1}\sum_{g\in G}w_k(g)\Bigr).
  \]
  -/)
  (proof := /-- Expanding the product over $k\in[m]$ on the right-hand side into the product of the
  constants and the product of the sums gives
  \[
    \prod_{k=1}^m\Bigl(|G|^{-1}\sum_{g\in G}w_k(g)\Bigr)
    =\Bigl(\prod_{k=1}^m|G|^{-1}\Bigr)\prod_{k=1}^m\sum_{g\in G}w_k(g)
    =|G|^{-m}\prod_{k=1}^m\sum_{g\in G}w_k(g),
  \]
  where the last equality evaluates the product of the $m$ equal factors $|G|^{-1}$ as the $m$-th
  power $\bigl(|G|^{-1}\bigr)^m=|G|^{-m}$.

  By the distributivity of a finite product of finite sums, expanding
  $\prod_{k=1}^m\sum_{g\in G}w_k(g)$ produces exactly one term $\prod_{k=1}^mw_k(S_k)$ for each
  choice function $S$ assigning to every $k\in[m]$ an element $S_k\in G$, and the set of such
  choice functions is precisely $G^m$; hence
  \[
    \prod_{k=1}^m\sum_{g\in G}w_k(g)=\sum_{S\in G^m}\prod_{k=1}^mw_k(S_k).
  \]
  Substituting this into the previous display gives
  $|G|^{-m}\sum_{S\in G^m}\prod_{k=1}^mw_k(S_k)$, which is the left-hand side by
  \cref{def:uniform-group-expectation}. -/)
  (title := /-- Product rule for the uniform augmentation expectation -/)
  (latexEnv := "lemma")]
lemma uniform_group_expectation_prod_eq {G : Type*} [Fintype G] {m : ℕ} (w : Fin m → G → ℝ) :
    uniform_group_expectation m (fun S => ∏ k, w k (S k))
      = ∏ k, ((Fintype.card G : ℝ)⁻¹ * ∑ g, w k g) := by
  rw [uniform_group_expectation, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← inv_pow, Finset.prod_univ_sum, Fintype.piFinset_univ]

@[blueprint "lem:uniform-group-expectation-eval-eq"
  (statement := /-- Let $G$ be a finite group, let $m\in\mathbb N$, let $j\in[m]$ and let
  $u:G\to\mathbb R$. Then the expectation of \cref{def:uniform-group-expectation} of the function
  depending on $S$ only through its $j$-th coordinate is the uniform average of $u$ over $G$,
  \[
    \mathbb E_S\bigl[u(S_j)\bigr]=|G|^{-1}\sum_{g\in G}u(g).
  \]
  -/)
  (proof := /-- Define $w_k:G\to\mathbb R$ for $k\in[m]$ by $w_j:=u$ and $w_k:=1$ for $k\neq j$, and
  apply \cref{lem:uniform-group-expectation-prod-eq} to this family.

  On the left-hand side, for every $S\in G^m$ the product $\prod_{k=1}^mw_k(S_k)$ has all factors
  with $k\neq j$ equal to $1$ and its $j$-th factor equal to $u(S_j)$, so the product equals
  $u(S_j)$; hence the two expectations agree.

  On the right-hand side, the $k$-th factor is $|G|^{-1}\sum_{g\in G}w_k(g)$. For $k\neq j$ this is
  $|G|^{-1}\sum_{g\in G}1=|G|^{-1}|G|=1$, using that $G$ is a nonempty finite type, being a finite
  group, so that $|G|\neq0$. Since all factors with index $k\neq j$ equal $1$, the product over
  $k\in[m]$ reduces to its $j$-th factor $|G|^{-1}\sum_{g\in G}u(g)$, which is the asserted
  value. -/)
  (title := /-- One-coordinate marginal of the uniform augmentation expectation -/)
  (latexEnv := "lemma")]
lemma uniform_group_expectation_eval_eq {G : Type*} [Group G] [Fintype G] {m : ℕ} (j : Fin m)
    (u : G → ℝ) :
    uniform_group_expectation m (fun S => u (S j)) = (Fintype.card G : ℝ)⁻¹ * ∑ g, u g := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_ne_zero (α := G))
  have h := uniform_group_expectation_prod_eq (G := G) (m := m)
    (fun k g => if k = j then u g else (1 : ℝ))
  rw [show (fun S : Fin m → G => ∏ k, (if k = j then u (S k) else (1 : ℝ)))
      = (fun S : Fin m → G => u (S j)) from funext fun S => by simp] at h
  rw [h, Finset.prod_eq_single_of_mem j (Finset.mem_univ j)
    (fun k _ hk => by simp [hk, Finset.card_univ, hcard])]
  simp

@[blueprint "lem:uniform-group-expectation-pair-eq"
  (statement := /-- Let $G$ be a finite group, let $m\in\mathbb N$, let $j,j'\in[m]$ with
  $j\neq j'$ and let $u,v:G\to\mathbb R$. Then the expectation of
  \cref{def:uniform-group-expectation} of the product of a function of the $j$-th coordinate with a
  function of the $j'$-th coordinate factorizes,
  \[
    \mathbb E_S\bigl[u(S_j)\,v(S_{j'})\bigr]
    =\Bigl(|G|^{-1}\sum_{g\in G}u(g)\Bigr)\Bigl(|G|^{-1}\sum_{g\in G}v(g)\Bigr).
  \]
  -/)
  (proof := /-- Define $w_k:G\to\mathbb R$ for $k\in[m]$ by $w_j:=u$, $w_{j'}:=v$, and $w_k:=1$ for
  $k\notin\{j,j'\}$; this is well defined because $j\neq j'$. Apply
  \cref{lem:uniform-group-expectation-prod-eq} to this family.

  On the left-hand side, for every $S\in G^m$ all factors of $\prod_{k=1}^mw_k(S_k)$ with
  $k\notin\{j,j'\}$ equal $1$, so the product reduces to the product of its two factors at the two
  distinct indices $j$ and $j'$, namely $u(S_j)\,v(S_{j'})$; hence the two expectations agree.

  On the right-hand side, the $k$-th factor $|G|^{-1}\sum_{g\in G}w_k(g)$ equals
  $|G|^{-1}\sum_{g\in G}1=|G|^{-1}|G|=1$ for every $k\notin\{j,j'\}$, using that $G$ is a nonempty
  finite type, being a finite group, so that $|G|\neq0$. Therefore the product over $k\in[m]$
  reduces to the product of its factors at the two distinct indices $j$ and $j'$, that is to
  $\bigl(|G|^{-1}\sum_{g\in G}u(g)\bigr)\bigl(|G|^{-1}\sum_{g\in G}v(g)\bigr)$, which is the
  asserted value. -/)
  (title := /-- Independence of two distinct coordinates of the augmentation set -/)
  (latexEnv := "lemma")]
lemma uniform_group_expectation_pair_eq {G : Type*} [Group G] [Fintype G] {m : ℕ} {j j' : Fin m}
    (hjj : j ≠ j') (u v : G → ℝ) :
    uniform_group_expectation m (fun S => u (S j) * v (S j'))
      = ((Fintype.card G : ℝ)⁻¹ * ∑ g, u g) * ((Fintype.card G : ℝ)⁻¹ * ∑ g, v g) := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_ne_zero (α := G))
  have h := uniform_group_expectation_prod_eq (G := G) (m := m)
    (fun k g => if k = j then u g else if k = j' then v g else (1 : ℝ))
  rw [show (fun S : Fin m → G =>
        ∏ k, (if k = j then u (S k) else if k = j' then v (S k) else (1 : ℝ)))
      = (fun S : Fin m → G => u (S j) * v (S j')) from funext fun S => by
        rw [Finset.prod_eq_mul_of_mem j j' (Finset.mem_univ j) (Finset.mem_univ j') hjj
          (fun k _ hk => by simp [hk.1, hk.2])]
        simp [hjj, hjj.symm]] at h
  rw [h, Finset.prod_eq_mul_of_mem j j' (Finset.mem_univ j) (Finset.mem_univ j') hjj
    (fun k _ hk => by simp [hk.1, hk.2, Finset.card_univ, hcard])]
  simp [hjj, hjj.symm]

@[blueprint "lem:uniform-group-average-centered-variance"
  (statement := /-- Let $G$ be a finite group, let $r\in\mathbb N$, let $Z:G\to\mathbb R^r$ be a
  centered family in the sense that $\sum_{g\in G}Z(g)=0$, and let $m\in\mathbb N$ with $m>0$. Then,
  with the expectation of \cref{def:uniform-group-expectation},
  \[
    \mathbb E_S\Bigl[\Bigl\|\frac1m\sum_{j=1}^mZ(S_j)\Bigr\|^2\Bigr]
    =\frac1m\Bigl(|G|^{-1}\sum_{g\in G}\|Z(g)\|^2\Bigr),
  \]
  where $\|\cdot\|$ is the Euclidean norm on $\mathbb R^r$. -/)
  (proof := /-- Write $e_1,\dots,e_r$ for the standard basis of $\mathbb R^r$ and $Z(g)_\ell$ for the
  $\ell$-th coordinate of $Z(g)$.

  \emph{Step 1: every coordinate of $Z$ has vanishing sum.} Evaluating the hypothesis
  $\sum_{g\in G}Z(g)=0$ at the coordinate $\ell\in[r]$, and using that taking the $\ell$-th
  coordinate is additive, gives $\sum_{g\in G}Z(g)_\ell=0$ for every $\ell\in[r]$.

  \emph{Step 2: pointwise expansion of the integrand.} Fix $S\in G^m$. Since $m>0$ we have
  $m^{-1}\ge0$, so $\|m^{-1}v\|^2=(m^{-1})^2\|v\|^2$ for every $v\in\mathbb R^r$. Expanding the
  squared norm of the sum $v:=\sum_{j=1}^mZ(S_j)$ bilinearly, and then writing each Euclidean inner
  product as the sum of the products of coordinates, gives
  \[
    \Bigl\|\frac1m\sum_{j=1}^mZ(S_j)\Bigr\|^2
    =\frac{1}{m}\cdot\frac{1}{m}\sum_{j=1}^m\sum_{j'=1}^m\sum_{\ell=1}^r
      Z(S_j)_\ell\,Z(S_{j'})_\ell .
  \]

  \emph{Step 3: expectation of a single pair of indices.} Fix $j,j'\in[m]$. By
  \cref{lem:uniform-group-expectation-sum-eq} the expectation commutes with the finite sum over
  $\ell\in[r]$, so
  \[
    \mathbb E_S\Bigl[\sum_{\ell=1}^rZ(S_j)_\ell Z(S_{j'})_\ell\Bigr]
    =\sum_{\ell=1}^r\mathbb E_S\bigl[Z(S_j)_\ell Z(S_{j'})_\ell\bigr].
  \]
  If $j\neq j'$, then \cref{lem:uniform-group-expectation-pair-eq} applied with
  $u(g):=Z(g)_\ell$ and $v(g):=Z(g)_\ell$ evaluates each summand as the product
  $\bigl(|G|^{-1}\sum_{g\in G}Z(g)_\ell\bigr)^2$, which vanishes by Step 1; hence the whole
  expectation is $0$. If $j=j'$, then for each $\ell\in[r]$ the summand depends on $S$ only through
  its $j$-th coordinate, so \cref{lem:uniform-group-expectation-eval-eq} applied with
  $u(g):=Z(g)_\ell Z(g)_\ell$ gives
  \[
    \mathbb E_S\bigl[Z(S_j)_\ell Z(S_j)_\ell\bigr]=|G|^{-1}\sum_{g\in G}Z(g)_\ell^2 .
  \]
  Summing over $\ell\in[r]$, interchanging the two finite sums, and using
  $\sum_{\ell=1}^rZ(g)_\ell^2=\|Z(g)\|^2$ shows that the expectation equals
  $|G|^{-1}\sum_{g\in G}\|Z(g)\|^2$ in this case.

  \emph{Step 4: assembling.} By Step 2, \cref{lem:uniform-group-expectation-const-mul-eq} and two
  applications of \cref{lem:uniform-group-expectation-sum-eq}, the expectation of the left-hand side
  equals
  \[
    \frac1{m^2}\sum_{j=1}^m\sum_{j'=1}^m
      \mathbb E_S\Bigl[\sum_{\ell=1}^rZ(S_j)_\ell Z(S_{j'})_\ell\Bigr].
  \]
  By Step 3 the inner expectation vanishes unless $j=j'$, in which case it equals
  $|G|^{-1}\sum_{g\in G}\|Z(g)\|^2$; hence for each fixed $j$ the sum over $j'$ collapses to that
  single value, and summing the $m$ equal terms over $j\in[m]$ gives
  \[
    \frac1{m^2}\cdot m\cdot|G|^{-1}\sum_{g\in G}\|Z(g)\|^2
    =\frac1m\Bigl(|G|^{-1}\sum_{g\in G}\|Z(g)\|^2\Bigr),
  \]
  where the last simplification uses $m\neq0$. -/)
  (title := /-- Variance of the average of a centered i.i.d. sample from $G$ -/)
  (latexEnv := "lemma")]
lemma uniform_group_average_centered_variance {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (Z : G → EuclideanSpace ℝ (Fin r)) (hZ : ∑ g, Z g = 0) (m : ℕ) (hm : 0 < m) :
    uniform_group_expectation m (fun S => ‖(m : ℝ)⁻¹ • ∑ j, Z (S j)‖ ^ 2)
      = (m : ℝ)⁻¹ * ((Fintype.card G : ℝ)⁻¹ * ∑ g, ‖Z g‖ ^ 2) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hcoord : ∀ l : Fin r, ∑ g, (Z g) l = 0 := by
    intro l
    have h : (∑ g, Z g) l = 0 := by rw [hZ]; simp
    simpa using h
  have hexp : ∀ S : Fin m → G, ‖(m : ℝ)⁻¹ • ∑ j, Z (S j)‖ ^ 2
      = (m : ℝ)⁻¹ * (m : ℝ)⁻¹ * ∑ j, ∑ j', ∑ l, (Z (S j)) l * (Z (S j')) l := by
    intro S
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (m : ℝ)⁻¹),
      ← real_inner_self_eq_norm_sq, sum_inner]
    rw [Finset.sum_congr rfl fun j _ => inner_sum (𝕜 := ℝ) Finset.univ (fun j' => Z (S j')) (Z (S j))]
    rw [show (∑ j, ∑ i, (inner ℝ (Z (S j)) (Z (S i)) : ℝ))
        = ∑ j, ∑ j', ∑ l, (Z (S j)) l * (Z (S j')) l from
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
        simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]]
    ring
  have hpair : ∀ j j' : Fin m,
      uniform_group_expectation m (fun S => ∑ l, (Z (S j)) l * (Z (S j')) l)
        = if j = j' then (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖Z g‖ ^ 2 else 0 := by
    intro j j'
    rw [uniform_group_expectation_sum_eq]
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl]
      rw [Finset.sum_congr rfl fun l _ =>
        uniform_group_expectation_eval_eq j (fun g => (Z g) l * (Z g) l)]
      rw [← Finset.mul_sum, Finset.sum_comm]
      refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun l _ => (sq ((Z g) l)).symm
    · rw [if_neg hjj]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [uniform_group_expectation_pair_eq hjj (fun g => (Z g) l) (fun g => (Z g) l), hcoord l]
      simp
  rw [show (fun S : Fin m → G => ‖(m : ℝ)⁻¹ • ∑ j, Z (S j)‖ ^ 2)
      = (fun S : Fin m → G =>
        (m : ℝ)⁻¹ * (m : ℝ)⁻¹ * ∑ j, ∑ j', ∑ l, (Z (S j)) l * (Z (S j')) l)
      from funext hexp, uniform_group_expectation_const_mul_eq,
    uniform_group_expectation_sum_eq]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => uniform_group_expectation_sum_eq
    (G := G) (m := m) Finset.univ (fun j' S => ∑ l, (Z (S j)) l * (Z (S j')) l)]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j' (_ : j' ∈ Finset.univ) => hpair j j']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

@[blueprint "lem:group-average-centered-sum-eq-zero"
  (statement := /-- Let $G$ be a finite group, let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be a
  representation of $G$ on the Euclidean space $\mathbb R^r$ and let $c\in\mathbb R^r$. Then the
  family $g\mapsto\rho(g)c-\Pi_Gc$ is centered,
  \[
    \sum_{g\in G}\bigl(\rho(g)c-\Pi_Gc\bigr)=0,
  \]
  where $\Pi_G$ is the full averaging operator of \cref{def:group-average-operator}. -/)
  (proof := /-- Splitting the sum of the difference into the difference of the sums gives
  \[
    \sum_{g\in G}\bigl(\rho(g)c-\Pi_Gc\bigr)=\sum_{g\in G}\rho(g)c-|G|\,\Pi_Gc ,
  \]
  because the second summand does not depend on $g$ and $G$ has exactly $|G|$ elements. By
  \cref{def:group-average-operator} we have $\Pi_Gc=|G|^{-1}\sum_{g\in G}\rho(g)c$, so
  \[
    |G|\,\Pi_Gc=|G|\cdot|G|^{-1}\sum_{g\in G}\rho(g)c=\sum_{g\in G}\rho(g)c ,
  \]
  where $|G|\cdot|G|^{-1}=1$ because $G$ is a nonempty finite type, being a finite group, so that
  $|G|\neq0$. Substituting this identity into the previous display leaves the difference of a vector
  with itself, which is $0$. -/)
  (title := /-- The orbit family is centered at the group average -/)
  (latexEnv := "lemma")]
lemma group_average_centered_sum_eq_zero {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (c : EuclideanSpace ℝ (Fin r)) :
    ∑ g : G, (rho g c - group_average_operator rho c) = 0 := by
  rw [Finset.sum_sub_distrib, group_average_operator, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fintype.card_ne_zero (α := G))), one_smul, sub_self]

@[blueprint "lem:group-average-inner-self-eq"
  (statement := /-- Let $G$ be a finite group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be an
  orthogonal representation of $G$ on the Euclidean space $\mathbb R^r$ in the sense of
  \cref{def:orthogonal-representation}. Then for every $c\in\mathbb R^r$,
  \[
    \langle c,\Pi_Gc\rangle=\|\Pi_Gc\|^2 ,
  \]
  where $\Pi_G$ is the full averaging operator of \cref{def:group-average-operator} and
  $\langle\cdot,\cdot\rangle$ is the Euclidean inner product on $\mathbb R^r$. -/)
  (proof := /-- By \cref{lem:group-average-eq-invariant-projection} the operator $\Pi_G$ agrees with
  the orthogonal projection $\Pi_{\mathcal F^G}$ onto the invariant subspace of
  \cref{def:invariant-projection}, so it suffices to prove
  $\langle c,\Pi_{\mathcal F^G}c\rangle=\langle\Pi_{\mathcal F^G}c,\Pi_{\mathcal F^G}c\rangle$,
  the right-hand side being $\|\Pi_{\mathcal F^G}c\|^2$ because the inner product of a vector with
  itself is the square of its norm.

  The defining property of the orthogonal projection onto the invariant subspace $V$ states that
  $c-\Pi_{\mathcal F^G}c$ is orthogonal to every element of $V$. Applying this with the element
  $\Pi_{\mathcal F^G}c$, which lies in $V$ because it is in the range of the projection onto $V$,
  gives $\langle c-\Pi_{\mathcal F^G}c,\Pi_{\mathcal F^G}c\rangle=0$. Expanding the first argument
  by additivity of the inner product yields
  \[
    \langle c,\Pi_{\mathcal F^G}c\rangle
      -\langle\Pi_{\mathcal F^G}c,\Pi_{\mathcal F^G}c\rangle=0,
  \]
  which is the desired identity. -/)
  (title := /-- The group average is self-adjointly idempotent against $c$ -/)
  (latexEnv := "lemma")]
lemma group_average_inner_self_eq {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (hrho : orthogonal_representation rho)
    (c : EuclideanSpace ℝ (Fin r)) :
    (inner ℝ c (group_average_operator rho c) : ℝ) = ‖group_average_operator rho c‖ ^ 2 := by
  rw [group_average_eq_invariant_projection rho hrho c, invariant_projection,
    ← real_inner_self_eq_norm_sq]
  have h2 := Submodule.starProjection_inner_eq_zero (K := rho.invariants) c
    (rho.invariants.starProjection c) (Submodule.starProjection_apply_mem _ c)
  rw [inner_sub_left] at h2
  linarith [h2]

@[blueprint "lem:group-orbit-variance-eq"
  (statement := /-- Let $G$ be a finite group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be an
  orthogonal representation of $G$ on the Euclidean space $\mathbb R^r$ in the sense of
  \cref{def:orthogonal-representation}. Then for every $c\in\mathbb R^r$,
  \[
    |G|^{-1}\sum_{g\in G}\bigl\|\rho(g)c-\Pi_Gc\bigr\|^2=\bigl\|c-\Pi_Gc\bigr\|^2 ,
  \]
  where $\Pi_G$ is the full averaging operator of \cref{def:group-average-operator}. -/)
  (proof := /-- Write $b:=\Pi_Gc$ throughout.

  \emph{Step 1: the sum of the orbit against $b$.} By \cref{def:group-average-operator} we have
  $b=|G|^{-1}\sum_{g\in G}\rho(g)c$, hence $\sum_{g\in G}\rho(g)c=|G|\,b$, using
  $|G|\cdot|G|^{-1}=1$, valid because $G$ is a nonempty finite type, being a finite group, so that
  $|G|\neq0$. Taking the inner product with $b$ and using homogeneity of the inner product in its
  first argument gives
  \[
    \Bigl\langle\sum_{g\in G}\rho(g)c,\;b\Bigr\rangle=|G|\,\langle b,b\rangle=|G|\,\|b\|^2 .
  \]

  \emph{Step 2: expanding each orbit term.} Fix $g\in G$. Expanding the squared norm of a difference
  gives $\|\rho(g)c-b\|^2=\|\rho(g)c\|^2-2\langle\rho(g)c,b\rangle+\|b\|^2$. Since $\rho$ is
  orthogonal by \cref{def:orthogonal-representation}, $\|\rho(g)c\|=\|c\|$, so
  \[
    \|\rho(g)c-b\|^2=\|c\|^2+\|b\|^2-2\langle\rho(g)c,b\rangle .
  \]

  \emph{Step 3: summing over the group.} Summing the display of Step 2 over $g\in G$, the constant
  term contributes $|G|\bigl(\|c\|^2+\|b\|^2\bigr)$ because $G$ has exactly $|G|$ elements, and by
  additivity of the inner product in its first argument together with Step 1 the remaining terms
  contribute $-2\sum_{g\in G}\langle\rho(g)c,b\rangle=-2|G|\,\|b\|^2$. Hence
  \[
    \sum_{g\in G}\|\rho(g)c-b\|^2=|G|\bigl(\|c\|^2-\|b\|^2\bigr),
  \]
  and multiplying by $|G|^{-1}$ gives $|G|^{-1}\sum_{g\in G}\|\rho(g)c-b\|^2=\|c\|^2-\|b\|^2$.

  \emph{Step 4: the right-hand side.} Expanding the squared norm of a difference again gives
  $\|c-b\|^2=\|c\|^2-2\langle c,b\rangle+\|b\|^2$, and
  \cref{lem:group-average-inner-self-eq} evaluates $\langle c,b\rangle=\|b\|^2$, so
  $\|c-b\|^2=\|c\|^2-\|b\|^2$. Comparing with Step 3 proves the claim. -/)
  (title := /-- Orbit variance about the group average -/)
  (latexEnv := "lemma")]
lemma group_orbit_variance_eq {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (hrho : orthogonal_representation rho)
    (c : EuclideanSpace ℝ (Fin r)) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖rho g c - group_average_operator rho c‖ ^ 2
      = ‖c - group_average_operator rho c‖ ^ 2 := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_ne_zero (α := G))
  have hb : ∑ g : G, rho g c = (Fintype.card G : ℝ) • group_average_operator rho c := by
    rw [group_average_operator, smul_smul, mul_inv_cancel₀ hcard, one_smul]
  have hsum : (inner ℝ (∑ g : G, rho g c) (group_average_operator rho c) : ℝ)
      = (Fintype.card G : ℝ) * ‖group_average_operator rho c‖ ^ 2 := by
    rw [hb, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hexp : ∑ g : G, ‖rho g c - group_average_operator rho c‖ ^ 2
      = (Fintype.card G : ℝ) * (‖c‖ ^ 2 - ‖group_average_operator rho c‖ ^ 2) := by
    rw [Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => show
      ‖rho g c - group_average_operator rho c‖ ^ 2
        = ‖c‖ ^ 2 + ‖group_average_operator rho c‖ ^ 2
          - 2 * (inner ℝ (rho g c) (group_average_operator rho c) : ℝ) from by
      rw [norm_sub_sq_real, hrho g c]; ring]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum, ← sum_inner,
      hsum, ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul]
    ring
  rw [hexp, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul, norm_sub_sq_real,
    group_average_inner_self_eq rho hrho c]
  ring

@[blueprint "lem:random-averaging-variance"
  (statement := /-- Let $G$ be a finite group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be an
  orthogonal representation of $G$ on the Euclidean space $\mathbb R^r$, in the sense of
  \cref{def:orthogonal-representation}. Let $m\in\mathbb N$ with $m>0$ and let
  $S=(g_1,\dots,g_m)$ be an i.i.d. uniform sample from $G$, with the associated expectation of
  \cref{def:uniform-group-expectation}. Then for every $c\in\mathbb R^r$,
  \[
    \mathbb E_S\bigl[\|\Pi_Sc-\Pi_Gc\|^2\bigr]=\frac1m\,\|c-\Pi_Gc\|^2 ,
  \]
  where $\Pi_S$ is the empirical averaging operator of \cref{def:empirical-average-operator} and
  $\Pi_G$ the full averaging operator of \cref{def:group-average-operator}. -/)
  (proof := /-- Fix $c\in\mathbb R^r$ and set $Z(g):=\rho(g)c-\Pi_Gc$ for $g\in G$.

  \emph{Step 1: rewriting the deviation as a scaled sum of the centered family.} Fix
  $S=(g_1,\dots,g_m)\in G^m$. By \cref{def:empirical-average-operator} we have
  $\Pi_Sc=m^{-1}\sum_{j=1}^m\rho(g_j)c$, and splitting the sum
  $\sum_{j=1}^m\bigl(\rho(g_j)c-\Pi_Gc\bigr)$ into the difference of the sums evaluates the
  contribution of the constant second summand as $m\,\Pi_Gc$, because $[m]$ has exactly $m$
  elements. Hence
  \[
    \frac1m\sum_{j=1}^mZ(g_j)
    =\frac1m\sum_{j=1}^m\rho(g_j)c-\frac1m\,m\,\Pi_Gc
    =\Pi_Sc-\Pi_Gc ,
  \]
  where $m^{-1}m=1$ because $m>0$. Consequently the two functions of $S$ whose expectations we
  compare are equal pointwise on $G^m$, so their expectations coincide.

  \emph{Step 2: the family $Z$ is centered.} By
  \cref{lem:group-average-centered-sum-eq-zero} we have $\sum_{g\in G}Z(g)=0$.

  \emph{Step 3: the variance of the average of the centered family.} By Step 2 the hypothesis of
  \cref{lem:uniform-group-average-centered-variance} is satisfied, and $m>0$, so that lemma
  applied to $Z$ gives
  \[
    \mathbb E_S\Bigl[\Bigl\|\frac1m\sum_{j=1}^mZ(g_j)\Bigr\|^2\Bigr]
    =\frac1m\Bigl(|G|^{-1}\sum_{g\in G}\|Z(g)\|^2\Bigr).
  \]

  \emph{Step 4: identifying the orbit variance.} Since $\rho$ is orthogonal in the sense of
  \cref{def:orthogonal-representation}, \cref{lem:group-orbit-variance-eq} gives
  \[
    |G|^{-1}\sum_{g\in G}\bigl\|\rho(g)c-\Pi_Gc\bigr\|^2=\bigl\|c-\Pi_Gc\bigr\|^2 .
  \]
  Substituting this into the display of Step 3 and using Step 1 to replace the integrand yields
  $\mathbb E_S\bigl[\|\Pi_Sc-\Pi_Gc\|^2\bigr]=\frac1m\|c-\Pi_Gc\|^2$, which is the claimed
  identity. -/)
  (title := /-- Variance of averaging over a random augmentation set -/)
  (latexEnv := "lemma")]
lemma random_averaging_variance {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (hrho : orthogonal_representation rho)
    (m : ℕ) (hm : 0 < m) (c : EuclideanSpace ℝ (Fin r)) :
    uniform_group_expectation m
        (fun S => ‖empirical_average_operator rho S c - group_average_operator rho c‖ ^ 2)
      = (m : ℝ)⁻¹ * ‖c - group_average_operator rho c‖ ^ 2 := by
  rw [show (fun S : Fin m → G =>
        ‖empirical_average_operator rho S c - group_average_operator rho c‖ ^ 2)
      = (fun S : Fin m → G =>
        ‖(m : ℝ)⁻¹ • ∑ j, (rho (S j) c - group_average_operator rho c)‖ ^ 2) from
    funext fun S => by
      rw [empirical_average_operator, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm.ne'), one_smul],
    uniform_group_average_centered_variance _ (group_average_centered_sum_eq_zero rho c) m hm,
    group_orbit_variance_eq rho hrho c]

@[blueprint "lem:augmented-density-estimator-eq-empirical-average"
  (statement := /-- Let $G$ be a group acting on $\mathcal X$ so that every $g\in G$ acts by a
  $\mu$-preserving map, let $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an
  $L^2(\mathcal X,\mu)$-orthonormal family in the sense of \cref{def:l2-orthonormal-family}, and let
  $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every $\ell\in[r]$, and let
  $\rho:G\to\mathrm{GL}(\mathbb R^r)$ implement the lifted action in the sense of
  \cref{def:implements-lifted-action}. Then for every $m,n\in\mathbb N$, every
  $S=(g_1,\dots,g_m)\in G^m$ and every $x_1,\dots,x_n\in\mathcal X$,
  \[
    \widehat\theta^{\,S}=\Pi_S\widehat\theta ,
  \]
  where $\widehat\theta^{\,S}$ is the partially augmented estimator of
  \cref{def:augmented-density-coeff-estimator}, $\widehat\theta$ is the non-augmented projection
  density estimator of \cref{def:density-coeff-estimator}, and $\Pi_S$ is the empirical averaging
  operator of \cref{def:empirical-average-operator}. -/)
  (proof := /-- This is the identity $\widehat f_S=\Pi_S\widehat f$ asserted in Step 3 of the source
  proof, where it is justified only by the phrase ``by the construction of the augmented projection
  estimator and linearity''; we verify it in coordinates, keeping track of the adjoint that the
  transfer of the transform from the basis functions to the coefficient vectors produces.

  Throughout, write $e_1,\dots,e_r$ for the standard basis of $\mathbb R^r$, write
  $\varphi(x):=(\varphi_1(x),\dots,\varphi_r(x))\in\mathbb R^r$ for $x\in\mathcal X$, and write
  $\langle\cdot,\cdot\rangle$ for the Euclidean inner product on $\mathbb R^r$, so that
  $\iota_\varphi(c)(x)=\langle c,\varphi(x)\rangle$ for every $c\in\mathbb R^r$ by
  \cref{def:coeff-to-fun}, and $c_\ell=\langle e_\ell,c\rangle$.

  \emph{Step 1: $\rho$ is orthogonal, and $\rho(g^{-1})$ is the adjoint of $\rho(g)$.} Each $g\in G$
  acts by a $\mu$-preserving map, $\varphi$ is $L^2(\mathcal X,\mu)$-orthonormal with
  $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every $\ell\in[r]$, and $\rho$ implements the lifted
  action, so \cref{lem:representation-orthogonal-of-measure-preserving} applies and shows that
  $\|\rho(g)c\|=\|c\|$ for every $g\in G$ and every $c\in\mathbb R^r$. A norm-preserving linear
  endomorphism of the finite-dimensional real inner-product space $\mathbb R^r$ preserves the inner
  product, by the polarization identity
  $\langle a,b\rangle=\tfrac12(\|a+b\|^2-\|a\|^2-\|b\|^2)$, hence is invertible with
  $\rho(g)^{-1}=\rho(g)^{*}$. Since $\rho$ is a group homomorphism,
  $\rho(g^{-1})=\rho(g)^{-1}=\rho(g)^{*}$, and therefore
  \[
    \bigl\langle\rho(g^{-1})a,\,b\bigr\rangle=\bigl\langle a,\,\rho(g)b\bigr\rangle
    \qquad\text{for all }g\in G\text{ and all }a,b\in\mathbb R^r. \tag{1}
  \]

  \emph{Step 2: transferring the transform to coefficient vectors.} Fix $g\in G$, $\ell\in[r]$ and
  $x\in\mathcal X$. Applying \cref{def:implements-lifted-action} to the group element $g^{-1}$, the
  coefficient vector $c=e_\ell$ and the point $x$ gives
  \[
    \bigl\langle\rho(g^{-1})e_\ell,\varphi(x)\bigr\rangle
    =\iota_\varphi\bigl(\rho(g^{-1})e_\ell\bigr)(x)
    =\iota_\varphi(e_\ell)\bigl((g^{-1})^{-1}x\bigr)
    =\iota_\varphi(e_\ell)(gx)
    =\varphi_\ell(gx). \tag{2}
  \]
  Identity (2) is used below at the prescribed sample points $x_1,\dots,x_n$, which is legitimate
  precisely because \cref{def:implements-lifted-action} asserts the intertwining relation at every
  point of $\mathcal X$ and not merely $\mu$-almost everywhere.

  \emph{Step 3: the coordinatewise computation.} Fix $\ell\in[r]$. By
  \cref{def:augmented-density-coeff-estimator}, then (2), then bilinearity of
  $\langle\cdot,\cdot\rangle$ together with \cref{def:density-coeff-estimator}, which gives
  $\widehat\theta=\frac1n\sum_{i=1}^n\varphi(x_i)$ coordinatewise,
  \[
    \widehat\theta^{\,S}_\ell
    =\frac{1}{nm}\sum_{i=1}^n\sum_{j=1}^m\varphi_\ell(g_jx_i)
    =\frac1m\sum_{j=1}^m\Bigl\langle\rho(g_j^{-1})e_\ell,\ \frac1n\sum_{i=1}^n\varphi(x_i)\Bigr\rangle
    =\frac1m\sum_{j=1}^m\bigl\langle\rho(g_j^{-1})e_\ell,\ \widehat\theta\bigr\rangle .
  \]
  Applying (1) with $a=e_\ell$ and $b=\widehat\theta$ to each summand and using bilinearity once
  more,
  \[
    \widehat\theta^{\,S}_\ell
    =\frac1m\sum_{j=1}^m\bigl\langle e_\ell,\ \rho(g_j)\widehat\theta\bigr\rangle
    =\Bigl\langle e_\ell,\ \frac1m\sum_{j=1}^m\rho(g_j)\widehat\theta\Bigr\rangle
    =\bigl(\Pi_S\widehat\theta\bigr)_\ell ,
  \]
  the last equality by \cref{def:empirical-average-operator}. Since $\ell\in[r]$ was arbitrary, the
  two vectors $\widehat\theta^{\,S}$ and $\Pi_S\widehat\theta$ have the same coordinates and hence
  coincide. -/)
  (title := /-- Augmented estimator as empirical averaging of the base estimator -/)
  (latexEnv := "lemma")]
lemma augmented_density_estimator_eq_empirical_average {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {G : Type*} [Group G] [MulAction G X] {r : ℕ} (phi : Fin r → X → ℝ)
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r)))
    (hact : ∀ g : G, MeasurePreserving (fun x : X => g • x) mu mu)
    (hphi : l2_orthonormal_family mu phi) (hmem : ∀ l, MemLp (phi l) 2 mu)
    (himpl : implements_lifted_action phi rho)
    {m n : ℕ} (S : Fin m → G) (xs : Fin n → X) :
    augmented_density_coeff_estimator phi S xs
      = empirical_average_operator rho S (density_coeff_estimator phi xs) := by
  have hrho :=
    representation_orthogonal_of_measure_preserving mu phi rho hact hphi hmem himpl
  have hfeature : ∀ (g : G) (x : X),
      WithLp.toLp 2 (fun l => phi l (g • x)) =
        rho g (WithLp.toLp 2 fun l => phi l x) := by
    intro g x
    apply ext_inner_left ℝ
    intro c
    calc
      inner ℝ c (WithLp.toLp 2 fun l => phi l (g • x)) =
          coeff_to_fun phi c (g • x) := by
            simp [coeff_to_fun, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      _ = coeff_to_fun phi (rho g⁻¹ c) x := by
            simpa using (himpl g⁻¹ c x).symm
      _ = inner ℝ (rho g⁻¹ c) (WithLp.toLp 2 fun l => phi l x) := by
            simp [coeff_to_fun, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      _ = inner ℝ (rho g (rho g⁻¹ c))
            (rho g (WithLp.toLp 2 fun l => phi l x)) := by
              symm
              exact (LinearMap.norm_map_iff_inner_map_map (rho g)).1 (hrho g) _ _
      _ = inner ℝ c (rho g (WithLp.toLp 2 fun l => phi l x)) := by
            simp
  have hfeature_apply (g : G) (x : X) (l : Fin r) :
      phi l (g • x) = (rho g (WithLp.toLp 2 fun k => phi k x)) l := by
    have h := congrArg (fun c : EuclideanSpace ℝ (Fin r) => c l) (hfeature g x)
    simpa using h
  have hdensity :
      density_coeff_estimator phi xs =
        (n : ℝ)⁻¹ • ∑ i, WithLp.toLp 2 (fun l => phi l (xs i)) := by
    ext l
    simp [density_coeff_estimator]
  ext l
  rw [hdensity]
  simp [augmented_density_coeff_estimator, empirical_average_operator, map_sum, hfeature_apply]
  rw [Finset.sum_comm]
  rw [← Finset.mul_sum]
  ring

@[blueprint "lem:augmented-regression-estimator-eq-empirical-average"
  (statement := /-- Let $(\mathcal X,\mu)$ be a measure space, let $G$ be a group acting on
  $\mathcal X$ so that every $g\in G$ acts by a $\mu$-preserving map, and let $r\in\mathbb N$.
  Let $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the
  sense of \cref{def:l2-orthonormal-family}, and assume that
  $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every $\ell\in[r]$. Let
  $\rho:G\to\mathrm{GL}(\mathbb R^r)$ implement the lifted action in the sense of
  \cref{def:implements-lifted-action}, and let $f^\star:\mathcal X\to\mathbb R$. Then for every
  $m,n\in\mathbb N$, every $S=(g_1,\dots,g_m)\in G^m$, and all
  $(x_1,\varepsilon_1),\dots,(x_n,\varepsilon_n)\in\mathcal X\times\mathbb R$,
  \[
    \widehat\beta^{\,S}=\Pi_S\widehat\beta ,
  \]
  where $\widehat\beta^{\,S}$ is the partially augmented regression estimator of
  \cref{def:augmented-regression-coeff-estimator}, $\widehat\beta$ is the non-augmented projection
  regression estimator of \cref{def:regression-coeff-estimator}, and $\Pi_S$ is the empirical
  averaging operator of \cref{def:empirical-average-operator}. -/)
  (proof := /-- Put $y_i=f^\star(x_i)+\varepsilon_i$; this weight is unchanged when the design
  point $x_i$ is transformed. We prove the identity in coordinates. Write $e_1,\dots,e_r$ for the
  standard basis of $\mathbb R^r$, write
  $\varphi(x):=(\varphi_1(x),\dots,\varphi_r(x))$, and use
  $\langle\cdot,\cdot\rangle$ for the Euclidean inner product, so that
  $\iota_\varphi(c)(x)=\langle c,\varphi(x)\rangle$ by \cref{def:coeff-to-fun}.

  \emph{Step 1: the adjoint relation.} Since every $g\in G$ acts by a $\mu$-preserving map,
  $\varphi$ is $L^2(\mathcal X,\mu)$-orthonormal with $\varphi_\ell\in L^2(\mathcal X,\mu)$ for all
  $\ell\in[r]$, and $\rho$ implements the lifted action,
  \cref{lem:representation-orthogonal-of-measure-preserving} shows that $\rho$ is orthogonal, so by
  the polarization identity each $\rho(g)$ preserves the Euclidean inner product and satisfies
  $\rho(g^{-1})=\rho(g)^{-1}=\rho(g)^{*}$. Consequently
  \[
    \bigl\langle\rho(g^{-1})a,\,b\bigr\rangle=\bigl\langle a,\,\rho(g)b\bigr\rangle
    \qquad\text{for all }g\in G,\ a,b\in\mathbb R^r. \tag{1}
  \]

  \emph{Step 2: the pointwise intertwining identity.} For every $g\in G$, every $\ell\in[r]$ and
  every $x\in\mathcal X$, applying \cref{def:implements-lifted-action} to the element $g^{-1}$ and
  the coefficient vector $e_\ell$ at the point $x$ gives
  \[
    \bigl\langle\rho(g^{-1})e_\ell,\varphi(x)\bigr\rangle
    =\iota_\varphi(e_\ell)(gx)=\varphi_\ell(gx). \tag{2}
  \]
  Because \cref{def:implements-lifted-action} holds at every point of $\mathcal X$, identity (2) may
  be used at the prescribed design points $x_1,\dots,x_n$.

  \emph{Step 3: the coordinatewise computation.} All scalar inverses below are field inverses in
  $\mathbb R$; thus the same calculation covers $n=0$ or $m=0$, when the relevant sums vanish.
  Fix $\ell\in[r]$ and write
  $y_i:=f^\star(x_i)+\varepsilon_i$. By \cref{def:augmented-regression-coeff-estimator}, then (2),
  then bilinearity of $\langle\cdot,\cdot\rangle$ together with
  \cref{def:regression-coeff-estimator}, which gives
  $\widehat\beta=\frac1n\sum_{i=1}^n y_i\varphi(x_i)$ coordinatewise,
  \[
    \widehat\beta^{\,S}_\ell
    =\frac{1}{nm}\sum_{i=1}^n\sum_{j=1}^m y_i\,\varphi_\ell(g_jx_i)
    =\frac1m\sum_{j=1}^m\Bigl\langle\rho(g_j^{-1})e_\ell,\ \frac1n\sum_{i=1}^n y_i\varphi(x_i)\Bigr\rangle
    =\frac1m\sum_{j=1}^m\bigl\langle\rho(g_j^{-1})e_\ell,\ \widehat\beta\bigr\rangle .
  \]
  Applying (1) with $a=e_\ell$ and $b=\widehat\beta$ to each summand and using bilinearity again,
  \[
    \widehat\beta^{\,S}_\ell
    =\Bigl\langle e_\ell,\ \frac1m\sum_{j=1}^m\rho(g_j)\widehat\beta\Bigr\rangle
    =\bigl(\Pi_S\widehat\beta\bigr)_\ell
  \]
  by \cref{def:empirical-average-operator}. As $\ell\in[r]$ was arbitrary, the two vectors agree. -/)
  (title := /-- Augmented regression estimator as empirical averaging -/)
  (latexEnv := "lemma")]
lemma augmented_regression_estimator_eq_empirical_average {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {G : Type*} [Group G] [MulAction G X] {r : ℕ} (phi : Fin r → X → ℝ)
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (fstar : X → ℝ)
    (hact : ∀ g : G, MeasurePreserving (fun x : X => g • x) mu mu)
    (hphi : l2_orthonormal_family mu phi) (hmem : ∀ l, MemLp (phi l) 2 mu)
    (himpl : implements_lifted_action phi rho)
    {m n : ℕ} (S : Fin m → G) (zs : Fin n → X × ℝ) :
    augmented_regression_coeff_estimator phi fstar S zs
      = empirical_average_operator rho S (regression_coeff_estimator phi fstar zs) := by
  have hrho :=
    representation_orthogonal_of_measure_preserving mu phi rho hact hphi hmem himpl
  have hfeature : ∀ (g : G) (x : X),
      WithLp.toLp 2 (fun l => phi l (g • x)) =
        rho g (WithLp.toLp 2 fun l => phi l x) := by
    intro g x
    apply ext_inner_left ℝ
    intro c
    calc
      inner ℝ c (WithLp.toLp 2 fun l => phi l (g • x)) =
          coeff_to_fun phi c (g • x) := by
            simp [coeff_to_fun, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      _ = coeff_to_fun phi (rho g⁻¹ c) x := by
            simpa using (himpl g⁻¹ c x).symm
      _ = inner ℝ (rho g⁻¹ c) (WithLp.toLp 2 fun l => phi l x) := by
            simp [coeff_to_fun, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      _ = inner ℝ (rho g (rho g⁻¹ c))
            (rho g (WithLp.toLp 2 fun l => phi l x)) := by
              symm
              exact (LinearMap.norm_map_iff_inner_map_map (rho g)).1 (hrho g) _ _
      _ = inner ℝ c (rho g (WithLp.toLp 2 fun l => phi l x)) := by
            simp
  have hfeature_apply (g : G) (x : X) (l : Fin r) :
      phi l (g • x) = (rho g (WithLp.toLp 2 fun k => phi k x)) l := by
    have h := congrArg (fun c : EuclideanSpace ℝ (Fin r) => c l) (hfeature g x)
    simpa using h
  have hregression :
      regression_coeff_estimator phi fstar zs =
        (n : ℝ)⁻¹ • ∑ i, (fstar (zs i).1 + (zs i).2) •
          WithLp.toLp 2 (fun l => phi l (zs i).1) := by
    ext l
    simp [regression_coeff_estimator]
  ext l
  rw [hregression]
  simp [augmented_regression_coeff_estimator, empirical_average_operator, map_sum,
    hfeature_apply]
  rw [Finset.sum_comm]
  rw [← Finset.mul_sum]
  ring

@[blueprint "lem:augmentation-error-bound"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$, let
  $n,m\in\mathbb N$ with $m>0$, let $G$ be a finite group and let
  $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be an orthogonal representation of $G$ on $\mathbb R^r$ in the
  sense of \cref{def:orthogonal-representation}. Let
  $\widehat c:\mathcal Y^n\to\mathbb R^r$ be any estimator depending on the base sample, and let
  $b\in(\mathbb R^r)^G$ be an invariant vector. Assume that the map
  $y_{1:n}\mapsto\|\widehat c(y_{1:n})-b\|^2$ is $\nu^{\otimes n}$-integrable and that the map
  $y_{1:n}\mapsto\mathbb E_S[\|\Pi_S\widehat c(y_{1:n})-\Pi_G\widehat c(y_{1:n})\|^2]$ is
  $\nu^{\otimes n}$-integrable. Then
  \[
    \mathbb E_{y_{1:n}}\Bigl[\mathbb E_S\bigl[\|\Pi_S\widehat c-\Pi_G\widehat c\|^2\bigr]\Bigr]
    \;\le\;\frac1m\,\mathbb E_{y_{1:n}}\bigl[\|\widehat c-b\|^2\bigr],
  \]
  with $\Pi_S$ and $\Pi_G$ as in \cref{def:empirical-average-operator} and
  \cref{def:group-average-operator}, and with the expectations of \cref{def:iid-expectation} and
  \cref{def:uniform-group-expectation}. -/)
  (proof := /-- Fix a base sample $y_{1:n}\in\mathcal Y^n$ and write $c:=\widehat c(y_{1:n})$.
  Conditionally on the base sample, \cref{lem:random-averaging-variance} applied to $c$ gives
  \[
    \mathbb E_S\bigl[\|\Pi_Sc-\Pi_Gc\|^2\bigr]=\frac1m\|c-\Pi_Gc\|^2 .
  \]
  By \cref{lem:group-average-eq-invariant-projection} the operator $\Pi_G$ coincides with the
  orthogonal projection $\Pi_{\mathcal F^G}$ onto the invariant subspace, so
  $\|c-\Pi_Gc\|=\|c-\Pi_{\mathcal F^G}c\|$. Since $b$ is invariant,
  \cref{lem:norm-sub-invariant-projection-le} applies and gives
  $\|c-\Pi_{\mathcal F^G}c\|\le\|c-b\|$. Squaring this inequality between nonnegative reals yields
  \[
    \mathbb E_S\bigl[\|\Pi_Sc-\Pi_Gc\|^2\bigr]\le\frac1m\|c-b\|^2 .
  \]
  This inequality holds for every base sample $y_{1:n}$. Both sides are
  $\nu^{\otimes n}$-integrable by hypothesis, so integrating over $y_{1:n}$ with respect to
  $\nu^{\otimes n}$ and using monotonicity of the integral gives the claimed bound. -/)
  (title := /-- Error from replacing full averaging by averaging over $S$ -/)
  (latexEnv := "lemma")]
lemma augmentation_error_bound {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (hrho : orthogonal_representation rho)
    (n m : ℕ) (hm : 0 < m) (chat : (Fin n → Y) → EuclideanSpace ℝ (Fin r))
    (b : EuclideanSpace ℝ (Fin r)) (hb : b ∈ rho.invariants)
    (hint1 : Integrable (fun ys => ‖chat ys - b‖ ^ 2) (Measure.pi fun _ : Fin n => nu))
    (hint2 : Integrable (fun ys => uniform_group_expectation m
      (fun S => ‖empirical_average_operator rho S (chat ys)
        - group_average_operator rho (chat ys)‖ ^ 2)) (Measure.pi fun _ : Fin n => nu)) :
    iid_expectation nu n (fun ys => uniform_group_expectation m
        (fun S => ‖empirical_average_operator rho S (chat ys)
          - group_average_operator rho (chat ys)‖ ^ 2))
      ≤ (m : ℝ)⁻¹ * iid_expectation nu n (fun ys => ‖chat ys - b‖ ^ 2) := by
  rw [iid_expectation, iid_expectation, ← integral_const_mul]
  apply integral_mono hint2 (hint1.const_mul _)
  intro ys
  dsimp only
  rw [random_averaging_variance rho hrho m hm,
    group_average_eq_invariant_projection rho hrho]
  gcongr
  exact norm_sub_invariant_projection_le rho (chat ys) b hb

@[blueprint "lem:invariant-baseline-density-excess"
  (statement := /-- Assume the setting of \cref{lem:baseline-density-excess}: $(\mathcal X,\mu)$ is a
  measure space, $\varphi=(\varphi_\ell)_{\ell\in[r]}$ is an $L^2(\mathcal X,\mu)$-orthonormal family
  as in \cref{def:l2-orthonormal-family} with each $\varphi_\ell\in L^2(\mathcal X,\mu)$,
  $f^\star\ge0$ $\mu$-almost everywhere with $f^\star\in L^2(\mathcal X,\mu)$,
  $\|f^\star\|_\infty<\infty$, and $\nu:=f^\star d\mu$ a probability measure, and $n>0$. Let $G$ be
  a finite group and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be an orthogonal representation as in
  \cref{def:orthogonal-representation}, and set $r_{\mathrm{inv}}:=\dim(\mathbb R^r)^G$. Then the
  fully averaged estimator $\Pi_G\widehat\theta$ satisfies
  \[
    \mathbb E\bigl[\|\Pi_G\widehat\theta-\Pi_G\theta(f^\star)\|^2\bigr]
    \;\le\;\frac{\|f^\star\|_\infty}{n}\,r_{\mathrm{inv}} ,
  \]
  with $\Pi_G$ as in \cref{def:group-average-operator}, $\widehat\theta$ the projection density
  estimator of \cref{def:density-coeff-estimator} and $\theta(f^\star)$ as in
  \cref{def:target-coeff}. -/)
  (proof := /-- Put $K:=(\mathbb R^r)^G$ and $k:=\dim K$, and choose an orthonormal basis
  $(b_j)_{j\in[k]}$ of $K$. For each $j\in[k]$ define
  $\psi_j:=\iota_\varphi(b_j)$ using the synthesis map of \cref{def:coeff-to-fun}. Each
  $\psi_j$ belongs to $L^2(\mathcal X,\mu)$ because it is a finite linear combination of the
  functions $\varphi_\ell$. Moreover, expanding the finite sums and using the orthonormality
  hypothesis from \cref{def:l2-orthonormal-family} gives, for $j,j'\in[k]$,
  \[
    \int_{\mathcal X}\psi_j(x)\psi_{j'}(x)\,d\mu(x)
    =\sum_{\ell,\ell'=1}^r (b_j)_\ell(b_{j'})_{\ell'}
      \int_{\mathcal X}\varphi_\ell(x)\varphi_{\ell'}(x)\,d\mu(x)
    =\langle b_j,b_{j'}\rangle
    =\delta_{jj'}.
  \]
  Thus $(\psi_j)_{j\in[k]}$ satisfies all basis hypotheses of
  \cref{lem:baseline-density-excess}.

  Let $\widehat\theta$ and $\theta(f^\star)$ be the coefficient vectors from
  \cref{def:density-coeff-estimator, def:target-coeff}, and let
  $\widehat\gamma$ and $\gamma(f^\star)$ denote the analogous vectors formed with the family
  $\psi$. Expanding the finite empirical sums in \cref{def:density-coeff-estimator} and commuting
  the finite sum with the integral in \cref{def:target-coeff} yields
  \[
    \widehat\gamma_j=\langle b_j,\widehat\theta\rangle,
    \qquad
    \gamma(f^\star)_j=\langle b_j,\theta(f^\star)\rangle .
  \]
  Since $\Pi_K$ is the orthogonal projection onto $K$, the difference
  $z-\Pi_Kz$ is orthogonal to every $b_j$. Parseval's identity in the orthonormal basis
  $(b_j)_{j\in[k]}$ therefore gives, for every $z\in\mathbb R^r$,
  \[
    \|\Pi_Kz\|^2=\sum_{j=1}^k\langle b_j,z\rangle^2.
  \]
  Taking $z=\widehat\theta-\theta(f^\star)$ and using the two coordinate identities shows
  pointwise that
  \[
    \|\Pi_K\widehat\theta-\Pi_K\theta(f^\star)\|^2
    =\|\widehat\gamma-\gamma(f^\star)\|^2.
  \]
  By \cref{lem:group-average-eq-invariant-projection}, $\Pi_G=\Pi_K$. Integrating the preceding
  pointwise equality according to \cref{def:iid-expectation} and applying
  \cref{lem:baseline-density-excess} to the $k$-element family $\psi$ gives
  \[
    \mathbb E\bigl[\|\Pi_G\widehat\theta-\Pi_G\theta(f^\star)\|^2\bigr]
    \le \frac{\|f^\star\|_\infty}{n}\,k,
  \]
  and $k=\dim(\mathbb R^r)^G$ is the claimed invariant dimension. -/)
  (title := /-- Estimation error inside the invariant subspace: density case -/)
  (latexEnv := "lemma")]
lemma invariant_baseline_density_excess {X : Type*} [MeasurableSpace X] (mu : Measure X)
    {G : Type*} [Group G] [Fintype G] {r : ℕ} (phi : Fin r → X → ℝ)
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (hrho : orthogonal_representation rho)
    (hphi : l2_orthonormal_family mu phi) (hmem : ∀ l, MemLp (phi l) 2 mu) (fstar : X → ℝ)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ fstar x) (hfmem : MemLp fstar 2 mu)
    (hfinf : eLpNormEssSup fstar mu ≠ ∞)
    (hprob : IsProbabilityMeasure (mu.withDensity fun x => ENNReal.ofReal (fstar x)))
    (n : ℕ) (hn : 0 < n) :
    iid_expectation (mu.withDensity fun x => ENNReal.ofReal (fstar x)) n
        (fun xs => ‖group_average_operator rho (density_coeff_estimator phi xs)
          - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
      ≤ (eLpNormEssSup fstar mu).toReal * (Module.finrank ℝ rho.invariants) / n := by
  classical
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin r)) := rho.invariants
  obtain ⟨w, b, _⟩ := exists_orthonormalBasis (𝕜 := ℝ) (E := K)
  have hcard : Fintype.card w = Module.finrank ℝ K := by
    rw [← Module.finrank_eq_card_basis b.toBasis]
  let e : w ≃ Fin (Module.finrank ℝ K) := Fintype.equivFinOfCardEq hcard
  let bfin : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K := b.reindex e
  let psi : Fin (Module.finrank ℝ K) → X → ℝ :=
    fun j x => coeff_to_fun phi (bfin j : EuclideanSpace ℝ (Fin r)) x
  have hpsimem : ∀ j, MemLp (psi j) 2 mu := by
    intro j
    exact memLp_finsetSum _ fun l _ => (hmem l).const_mul _
  have hpsi : l2_orthonormal_family mu psi := by
    simp only [l2_orthonormal_family] at hphi ⊢
    intro j j'
    have hint : ∀ l l' : Fin r, Integrable (fun x => phi l x * phi l' x) mu :=
      fun l l' => (hmem l).integrable_mul (hmem l')
    have hpt : ∀ x, psi j x * psi j' x =
        ∑ l, ∑ l', ((bfin j : EuclideanSpace ℝ (Fin r)) l
          * (bfin j' : EuclideanSpace ℝ (Fin r)) l') * (phi l x * phi l' x) := by
      intro x
      simp only [psi, coeff_to_fun]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun l' _ => ?_
      ring
    simp only [hpt]
    rw [integral_finsetSum _ fun l _ =>
      integrable_finsetSum _ fun l' _ => (hint l l').const_mul _]
    rw [show (∑ l, ∫ x, ∑ l',
        ((bfin j : EuclideanSpace ℝ (Fin r)) l
          * (bfin j' : EuclideanSpace ℝ (Fin r)) l') * (phi l x * phi l' x) ∂mu)
        = ∑ l, ∑ l', ((bfin j : EuclideanSpace ℝ (Fin r)) l
          * (bfin j' : EuclideanSpace ℝ (Fin r)) l')
            * ∫ x, phi l x * phi l' x ∂mu by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_finsetSum _ fun l' _ => (hint l l').const_mul _]
      exact Finset.sum_congr rfl fun l' _ => integral_const_mul _ _]
    simp [hphi]
    have hb := bfin.inner_eq_ite j j'
    change inner ℝ (bfin j : EuclideanSpace ℝ (Fin r))
      (bfin j' : EuclideanSpace ℝ (Fin r)) = (if j = j' then 1 else 0) at hb
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hb
    simpa [dotProduct, mul_comm] using hb
  let coords (z : EuclideanSpace ℝ (Fin r)) :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) :=
    WithLp.toLp 2 fun j => inner ℝ (bfin j : EuclideanSpace ℝ (Fin r)) z
  have hest (xs : Fin n → X) :
      density_coeff_estimator psi xs = coords (density_coeff_estimator phi xs) := by
    ext j
    change (n : ℝ)⁻¹ * ∑ i, ∑ l,
        (bfin j : EuclideanSpace ℝ (Fin r)) l * phi l (xs i)
      = ∑ l, ((n : ℝ)⁻¹ * ∑ i, phi l (xs i))
          * (bfin j : EuclideanSpace ℝ (Fin r)) l
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum]
    ring
  have htarget :
      target_coeff mu psi fstar = coords (target_coeff mu phi fstar) := by
    ext j
    change (∫ x, fstar x * ∑ l,
        (bfin j : EuclideanSpace ℝ (Fin r)) l * phi l x ∂mu)
      = ∑ l, (∫ x, fstar x * phi l x ∂mu)
          * (bfin j : EuclideanSpace ℝ (Fin r)) l
    have hint : ∀ l : Fin r, Integrable (fun x => fstar x * phi l x) mu :=
      fun l => hfmem.integrable_mul (hmem l)
    rw [show (fun x => fstar x * ∑ l, (bfin j : EuclideanSpace ℝ (Fin r)) l * phi l x)
        = fun x => ∑ l, (bfin j : EuclideanSpace ℝ (Fin r)) l * (fstar x * phi l x) by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring]
    rw [integral_finsetSum _ fun l _ => (hint l).const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]
    ring
  have hcoords_sub (z z' : EuclideanSpace ℝ (Fin r)) :
      coords (z - z') = coords z - coords z' := by
    ext j
    simp [coords, inner_sub_right]
  have hproj_norm (z : EuclideanSpace ℝ (Fin r)) :
      ‖invariant_projection rho z‖ ^ 2 = ‖coords z‖ ^ 2 := by
    let pz : K := ⟨invariant_projection rho z,
      Submodule.starProjection_apply_mem K z⟩
    calc
      ‖invariant_projection rho z‖ ^ 2 = ‖pz‖ ^ 2 := rfl
      _ = ∑ j, (inner ℝ (bfin j) pz) ^ 2 := (bfin.sum_sq_inner_right pz).symm
      _ = ∑ j, (inner ℝ (bfin j : EuclideanSpace ℝ (Fin r)) z) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        calc
          inner ℝ (bfin j : EuclideanSpace ℝ (Fin r)) (invariant_projection rho z)
              = inner ℝ (invariant_projection rho z)
                  (bfin j : EuclideanSpace ℝ (Fin r)) := real_inner_comm _ _
          _ = inner ℝ z (bfin j : EuclideanSpace ℝ (Fin r)) := by
            have hz := Submodule.starProjection_inner_eq_zero (K := K) z
              (bfin j : EuclideanSpace ℝ (Fin r)) (bfin j).property
            change inner ℝ (z - invariant_projection rho z)
              (bfin j : EuclideanSpace ℝ (Fin r)) = 0 at hz
            rw [inner_sub_left] at hz
            linarith
          _ = inner ℝ (bfin j : EuclideanSpace ℝ (Fin r)) z := real_inner_comm _ _
      _ = ‖coords z‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
  have herr (xs : Fin n → X) :
      ‖group_average_operator rho (density_coeff_estimator phi xs)
          - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2
        = ‖density_coeff_estimator psi xs - target_coeff mu psi fstar‖ ^ 2 := by
    rw [group_average_eq_invariant_projection rho hrho,
      group_average_eq_invariant_projection rho hrho, ← map_sub, hproj_norm,
      hcoords_sub, ← hest, ← htarget]
  have heq :
      iid_expectation (mu.withDensity fun x => ENNReal.ofReal (fstar x)) n
          (fun xs => ‖group_average_operator rho (density_coeff_estimator phi xs)
            - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
        = iid_expectation (mu.withDensity fun x => ENNReal.ofReal (fstar x)) n
          (fun xs => ‖density_coeff_estimator psi xs - target_coeff mu psi fstar‖ ^ 2) := by
    unfold iid_expectation
    exact integral_congr_ae (Filter.Eventually.of_forall herr)
  rw [heq]
  simpa [K] using
    baseline_density_excess mu psi hpsi hpsimem fstar hf0 hfmem hfinf hprob n hn

@[blueprint "lem:invariant-baseline-regression-excess"
  (statement := /-- Let $(\mathcal X,\mu)$ be a probability space, let $r\in\mathbb N$, and let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family in the sense
  of \cref{def:l2-orthonormal-family}, with $\varphi_\ell\in L^2(\mathcal X,\mu)$ for every
  $\ell\in[r]$. Let $f^\star\in L^2(\mathcal X,\mu)$ satisfy
  $\|f^\star\|_\infty<\infty$, and let $\eta$ be a centered noise law on $\mathbb R$ with variance
  $\sigma^2$ in the sense of \cref{def:centered-noise}. Fix $n\in\mathbb N$ with $n>0$, and let
  $(x_i,\varepsilon_i)_{i\in[n]}$ be i.i.d. with law $\mu\otimes\eta$. Let $G$ be a finite group,
  let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be an orthogonal representation in the sense of
  \cref{def:orthogonal-representation}, and set
  $r_{\mathrm{inv}}:=\dim_{\mathbb R}(\mathbb R^r)^G$. If $\widehat\beta$ is the regression
  coefficient estimator of \cref{def:regression-coeff-estimator}, formed from the responses
  $f^\star(x_i)+\varepsilon_i$, and $\theta(f^\star)$ is the target coefficient vector of
  \cref{def:target-coeff}, then
  \[
    \mathbb E\bigl[\|\Pi_G\widehat\beta-\Pi_G\theta(f^\star)\|^2\bigr]
    \;\le\;\frac{\|f^\star\|_\infty^2+\sigma^2}{n}\,r_{\mathrm{inv}} ,
  \]
  where $\Pi_G$ is the group-average operator of \cref{def:group-average-operator} and the
  expectation is over the $n$ product-law samples. -/)
  (proof := /-- Put $V:=(\mathbb R^r)^G$ and choose an orthonormal basis
  $(b_j)_{j\in[k]}$ of $V$, where $k=\dim_{\mathbb R}V$. For each $j\in[k]$ define
  $\psi_j:=\iota_\varphi(b_j)$ using \cref{def:coeff-to-fun}. Each $\psi_j$ lies in
  $L^2(\mathcal X,\mu)$ because it is a finite linear combination of the functions
  $\varphi_\ell$. Expanding both finite sums and using the orthonormality of $\varphi$ gives
  \[
    \int_{\mathcal X}\psi_j(x)\psi_{j'}(x)\,d\mu(x)
    =\langle b_j,b_{j'}\rangle
    =\delta_{jj'}.
  \]
  Thus $(\psi_j)_{j\in[k]}$ is an $L^2$-orthonormal family.

  By \cref{lem:group-average-eq-invariant-projection}, $\Pi_G$ is the orthogonal projection $P_V$
  onto $V$. If $c\in\mathbb R^r$, the $j$th coordinate of $P_Vc$ in the basis $(b_j)$ is
  $\langle b_j,P_Vc\rangle=\langle b_j,c\rangle$, since $c-P_Vc$ is orthogonal to $V$.
  Expanding the definitions in \cref{def:regression-coeff-estimator} and
  \cref{def:target-coeff}, and interchanging only finite sums with the relevant integrals, therefore
  yields
  \[
    \operatorname{repr}_b(P_V\widehat\beta)
      =\widehat\beta_\psi,
    \qquad
    \operatorname{repr}_b(P_V\theta_\varphi(f^\star))
      =\theta_\psi(f^\star).
  \]
  The coordinate map $\operatorname{repr}_b$ is an isometry, so the squared norm of the difference
  on the left of the asserted inequality equals
  $\|\widehat\beta_\psi-\theta_\psi(f^\star)\|^2$ pointwise for every sample.

  Applying \cref{lem:baseline-regression-excess} to the $k$-element orthonormal family $\psi$
  gives
  \[
    \mathbb E\bigl[\|\widehat\beta_\psi-\theta_\psi(f^\star)\|^2\bigr]
    \le \frac{\|f^\star\|_\infty^2+\sigma^2}{n}\,k.
  \]
  Since the chosen orthonormal basis is a basis of $V$, its cardinality is
  $k=\dim_{\mathbb R}V=r_{\mathrm{inv}}$, which proves the result. -/)
  (title := /-- Estimation error inside the invariant subspace: regression case -/)
  (latexEnv := "lemma")]
lemma invariant_baseline_regression_excess {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsProbabilityMeasure mu] {G : Type*} [Group G] [Fintype G] {r : ℕ} (phi : Fin r → X → ℝ)
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (hrho : orthogonal_representation rho)
    (hphi : l2_orthonormal_family mu phi) (hmem : ∀ l, MemLp (phi l) 2 mu) (fstar : X → ℝ)
    (hfmem : MemLp fstar 2 mu) (hfinf : eLpNormEssSup fstar mu ≠ ∞) (eta : Measure ℝ) (sigma : ℝ)
    (heta : centered_noise eta sigma) (n : ℕ) (hn : 0 < n) :
    iid_expectation (mu.prod eta) n
        (fun zs => ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
          - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
      ≤ ((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2)
          * (Module.finrank ℝ rho.invariants) / n := by
  classical
  obtain ⟨w, b, _⟩ := exists_orthonormalBasis (𝕜 := ℝ) (E := rho.invariants)
  let b' : OrthonormalBasis (Fin w.card) ℝ rho.invariants :=
    b.reindex (Finset.equivFin w)
  let psi : Fin w.card → X → ℝ := fun j => coeff_to_fun phi (b' j)
  have hpsimem : ∀ j, MemLp (psi j) 2 mu := by
    intro j
    exact memLp_finsetSum _ fun l _ =>
      (hmem l).const_mul ((b' j : EuclideanSpace ℝ (Fin r)) l)
  have hinner (c d : EuclideanSpace ℝ (Fin r)) :
      ∫ x, coeff_to_fun phi c x * coeff_to_fun phi d x ∂mu = inner ℝ c d := by
    have hint : ∀ l l' : Fin r, Integrable (fun x => phi l x * phi l' x) mu :=
      fun l l' => (hmem l).integrable_mul (hmem l')
    have hpt : ∀ x, coeff_to_fun phi c x * coeff_to_fun phi d x =
        ∑ l, ∑ l', c l * d l' * (phi l x * phi l' x) := by
      intro x
      unfold coeff_to_fun
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun l' _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun l _ =>
      integrable_finsetSum _ fun l' _ => (hint l l').const_mul _]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro l hl
    rw [integral_finsetSum _ fun l' _ => (hint l l').const_mul _]
    have hterm (l' : Fin r) :
        (∫ x, c l * d l' * (phi l x * phi l' x) ∂mu) =
          c l * d l' * (if l = l' then 1 else 0) := by
      rw [integral_const_mul, hphi]
    rw [Finset.sum_congr rfl fun l' _ => hterm l']
    simp [mul_comm]
  have hpsi : l2_orthonormal_family mu psi := by
    intro j j'
    change (∫ x, coeff_to_fun phi (b' j) x * coeff_to_fun phi (b' j') x ∂mu) =
      if j = j' then 1 else 0
    rw [hinner]
    exact b'.inner_eq_ite j j'
  let P := invariant_projection rho
  let proj (c : EuclideanSpace ℝ (Fin r)) : rho.invariants :=
    ⟨P c, by exact Submodule.starProjection_apply_mem rho.invariants c⟩
  have hrepr (c : EuclideanSpace ℝ (Fin r)) (j : Fin w.card) :
      b'.repr (proj c) j = inner ℝ (b' j : EuclideanSpace ℝ (Fin r)) c := by
    rw [b'.repr_apply_apply]
    change inner ℝ (b' j : EuclideanSpace ℝ (Fin r)) (P c) =
      inner ℝ (b' j : EuclideanSpace ℝ (Fin r)) c
    have hz := Submodule.starProjection_inner_eq_zero (K := rho.invariants) c
      (b' j : EuclideanSpace ℝ (Fin r)) (b' j).property
    change inner ℝ (c - P c) (b' j : EuclideanSpace ℝ (Fin r)) = 0 at hz
    rw [inner_sub_left] at hz
    have heq : inner ℝ c (b' j : EuclideanSpace ℝ (Fin r)) =
        inner ℝ (P c) (b' j : EuclideanSpace ℝ (Fin r)) := sub_eq_zero.mp hz
    simpa only [real_inner_comm] using heq.symm
  have hest (zs : Fin n → X × ℝ) :
      regression_coeff_estimator psi fstar zs =
        b'.repr (proj (regression_coeff_estimator phi fstar zs)) := by
    ext j
    rw [hrepr]
    simp [regression_coeff_estimator, psi, coeff_to_fun,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm]
    rw [Finset.sum_comm]
  have htarget :
      target_coeff mu psi fstar = b'.repr (proj (target_coeff mu phi fstar)) := by
    ext j
    rw [hrepr]
    change (∫ x, fstar x * (∑ l, (b' j : EuclideanSpace ℝ (Fin r)) l * phi l x) ∂mu) =
      inner ℝ (b' j : EuclideanSpace ℝ (Fin r))
        (WithLp.toLp 2 fun l => ∫ x, fstar x * phi l x ∂mu)
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, RCLike.star_def, conj_trivial, WithLp.ofLp_toLp]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun l _ => by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hfmem.integrable_mul (hmem l)).const_mul
          ((b' j : EuclideanSpace ℝ (Fin r)) l)]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show (fun x => fstar x * ((b' j : EuclideanSpace ℝ (Fin r)) l * phi l x)) =
        fun x => (b' j : EuclideanSpace ℝ (Fin r)) l * (fstar x * phi l x) by
          funext x
          ring]
    rw [integral_const_mul]
    simp [mul_comm]
  have hnorm (c d : EuclideanSpace ℝ (Fin r)) :
      ‖P c - P d‖ = ‖b'.repr (proj c) - b'.repr (proj d)‖ := by
    have h := b'.repr.norm_map (proj c - proj d)
    rw [map_sub] at h
    exact h.symm
  have herr (zs : Fin n → X × ℝ) :
      ‖group_average_operator rho (regression_coeff_estimator phi fstar zs) -
          group_average_operator rho (target_coeff mu phi fstar)‖ =
        ‖regression_coeff_estimator psi fstar zs - target_coeff mu psi fstar‖ := by
    rw [group_average_eq_invariant_projection rho hrho,
      group_average_eq_invariant_projection rho hrho]
    change ‖P (regression_coeff_estimator phi fstar zs) -
        P (target_coeff mu phi fstar)‖ =
      ‖regression_coeff_estimator psi fstar zs - target_coeff mu psi fstar‖
    rw [hnorm, hest, htarget]
  have hbase := baseline_regression_excess mu psi hpsi hpsimem fstar hfmem hfinf
    eta sigma heta n hn
  have hwcard : w.card = Module.finrank ℝ rho.invariants :=
    (Module.finrank_eq_card_finset_basis b.toBasis).symm
  simpa only [herr, hwcard] using hbase

@[blueprint "lem:norm-add-sq-doubling"
  (statement := /-- For every $r\in\mathbb N$ and all vectors $a,b$ in the Euclidean space
  $\mathbb R^r$,
  \[
    \|a+b\|^2\le2\|a\|^2+2\|b\|^2 .
  \]
  -/)
  (proof := /-- Expanding the squared norm of the sum by bilinearity of the inner product gives
  \[
    \|a+b\|^2=\|a\|^2+2\langle a,b\rangle+\|b\|^2 .
  \]
  The elementary inequality $2uv\le u^2+v^2$, valid for all real $u,v$ because
  $(u-v)^2\ge0$, applied with $u=\|a\|$ and $v=\|b\|$ gives
  $2\|a\|\,\|b\|\le\|a\|^2+\|b\|^2$. Combining this with the Cauchy-Schwarz inequality
  $\langle a,b\rangle\le\|a\|\,\|b\|$ yields $2\langle a,b\rangle\le\|a\|^2+\|b\|^2$. Substituting
  this bound into the expansion above gives
  \[
    \|a+b\|^2\le\|a\|^2+\bigl(\|a\|^2+\|b\|^2\bigr)+\|b\|^2=2\|a\|^2+2\|b\|^2 . \qedhere
  \]
  -/)
  (title := /-- Doubling inequality for the squared norm of a sum -/)
  (latexEnv := "lemma")]
lemma norm_add_sq_doubling {r : ℕ} (a b : EuclideanSpace ℝ (Fin r)) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hexp : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := norm_add_sq_real a b
  have hcs : inner ℝ a b ≤ ‖a‖ * ‖b‖ := real_inner_le_norm a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

@[blueprint "lem:general-augmentation-error-bound"
  (statement := /-- Let $\nu$ be a probability measure on a measurable space $\mathcal Y$, let
  $n,m\in\mathbb N$ with $m>0$, and let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ be an orthogonal
  representation of a finite group $G$. Let
  $\widehat c:\mathcal Y^n\to\mathbb R^r$ be an estimator and let $\theta\in\mathbb R^r$ be
  arbitrary. Assume that the squared distances from $\widehat c$ to both $\theta$ and
  $\Pi_{\mathcal F^G}\theta$ are integrable, and that the conditional augmentation error is
  integrable. Then
  \[
    \mathbb E_{y_{1:n}}\!\left[
      \mathbb E_S\|\Pi_S\widehat c-\Pi_G\widehat c\|^2\right]
    \le \frac{2}{m}\left(
      \mathbb E_{y_{1:n}}\|\widehat c-\theta\|^2
      +\|\theta-\Pi_{\mathcal F^G}\theta\|^2\right).
  \]
  Here $\Pi_{\mathcal F^G}$ is the invariant projection of
  \cref{def:invariant-projection}. -/)
  (proof := /-- Put $b:=\Pi_{\mathcal F^G}\theta$. By the defining property of an orthogonal
  projection, $b$ belongs to the invariant subspace. Hence
  \cref{lem:augmentation-error-bound}, applied with this $b$, bounds the left-hand side by
  $m^{-1}\mathbb E\|\widehat c-b\|^2$.

  For every base sample,
  \[
    \widehat c-b=(\widehat c-\theta)+(\theta-b).
  \]
  Applying \cref{lem:norm-add-sq-doubling} to these two summands gives
  \[
    \|\widehat c-b\|^2
    \le 2\|\widehat c-\theta\|^2+2\|\theta-b\|^2.
  \]
  The assumed integrability permits integration of this pointwise inequality. Since $\nu$ is a
  probability measure, the expectation of the constant second term is
  $2\|\theta-b\|^2$. Multiplication by $m^{-1}>0$ yields the asserted estimate. -/)
  (title := /-- Augmentation error for a general projected target -/)
  (latexEnv := "lemma")]
lemma general_augmentation_error_bound {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    [IsProbabilityMeasure nu] {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (hrho : orthogonal_representation rho)
    (n m : ℕ) (hm : 0 < m) (chat : (Fin n → Y) → EuclideanSpace ℝ (Fin r))
    (theta : EuclideanSpace ℝ (Fin r))
    (hint1 : Integrable (fun ys => ‖chat ys - theta‖ ^ 2) (Measure.pi fun _ : Fin n => nu))
    (hint2 : Integrable (fun ys =>
      ‖chat ys - invariant_projection rho theta‖ ^ 2) (Measure.pi fun _ : Fin n => nu))
    (hint3 : Integrable (fun ys => uniform_group_expectation m
      (fun S => ‖empirical_average_operator rho S (chat ys)
        - group_average_operator rho (chat ys)‖ ^ 2)) (Measure.pi fun _ : Fin n => nu)) :
    iid_expectation nu n (fun ys => uniform_group_expectation m
        (fun S => ‖empirical_average_operator rho S (chat ys)
          - group_average_operator rho (chat ys)‖ ^ 2))
      ≤ 2 * (m : ℝ)⁻¹ * (iid_expectation nu n (fun ys => ‖chat ys - theta‖ ^ 2)
          + ‖theta - invariant_projection rho theta‖ ^ 2) := by
  have hb : invariant_projection rho theta ∈ rho.invariants :=
    rho.invariants.starProjection_apply_mem theta
  have hpoint : ∀ ys,
      ‖chat ys - invariant_projection rho theta‖ ^ 2
        ≤ 2 * ‖chat ys - theta‖ ^ 2
          + 2 * ‖theta - invariant_projection rho theta‖ ^ 2 := by
    intro ys
    rw [show chat ys - invariant_projection rho theta =
      (chat ys - theta) + (theta - invariant_projection rho theta) by abel]
    exact norm_add_sq_doubling _ _
  have hupper : Integrable (fun ys : Fin n → Y =>
      2 * ‖chat ys - theta‖ ^ 2
        + 2 * ‖theta - invariant_projection rho theta‖ ^ 2)
      (Measure.pi fun _ : Fin n => nu) :=
    (hint1.const_mul 2).add (integrable_const _)
  have hi : iid_expectation nu n
        (fun ys => ‖chat ys - invariant_projection rho theta‖ ^ 2)
      ≤ 2 * (iid_expectation nu n (fun ys => ‖chat ys - theta‖ ^ 2)
        + ‖theta - invariant_projection rho theta‖ ^ 2) := by
    rw [iid_expectation, iid_expectation]
    calc
      _ ≤ ∫ ys, (2 * ‖chat ys - theta‖ ^ 2
          + 2 * ‖theta - invariant_projection rho theta‖ ^ 2)
          ∂(Measure.pi fun _ : Fin n => nu) :=
        integral_mono hint2 hupper hpoint
      _ = _ := by
        rw [integral_add (hint1.const_mul 2) (integrable_const _),
          integral_const_mul, integral_const]
        simp; ring
  calc
    _ ≤ (m : ℝ)⁻¹ * iid_expectation nu n
        (fun ys => ‖chat ys - invariant_projection rho theta‖ ^ 2) :=
      augmentation_error_bound nu rho hrho n m hm chat
        (invariant_projection rho theta) hb hint2 hint3
    _ ≤ (m : ℝ)⁻¹ * (2 * (iid_expectation nu n
        (fun ys => ‖chat ys - theta‖ ^ 2)
          + ‖theta - invariant_projection rho theta‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (Nat.cast_nonneg m))
    _ = _ := by ring

@[blueprint "def:partial-augmentation-density-bound"
  (statement := /-- Let $C\in\mathbb R$. We say that $C$ is an \emph{admissible density-estimation
  constant} if the following holds for every choice of data. Let $(\mathcal X,\mu)$ be a
  probability space; let $G$ be a finite group acting on $\mathcal X$ such that every map
  $x\mapsto g\cdot x$ preserves $\mu$; let $r\in\mathbb N$ and let
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an $L^2(\mathcal X,\mu)$-orthonormal family as in
  \cref{def:l2-orthonormal-family} with each $\varphi_\ell\in L^2(\mathcal X,\mu)$, spanning the
  $r$-dimensional subspace $\mathcal F$; let $\rho:G\to\mathrm{GL}(\mathbb R^r)$ implement the
  lifted action as in \cref{def:implements-lifted-action}, so that $\mathcal F$ is closed under the
  action of $G$, and set $r_{\mathrm{inv}}:=\dim(\mathbb R^r)^G$; let
  $f^\star:\mathcal X\to[0,\infty)$ be a density belonging to
  $L^2(\mathcal X,\mu)\cap L^\infty(\mathcal X,\mu)$ and normalized by
  $\int_{\mathcal X}f^\star\,d\mu=1$. Assume in addition that
  $\|f^\star\|_\infty\le 1$ and that the orthogonal projection
  $\Pi_{\mathcal F}f^\star$ is $G$-invariant. Write
  $d\nu=f^\star\,d\mu$ for the resulting probability law, and let $\theta(f^\star)$ be the
  coefficient vector of $\Pi_{\mathcal F}f^\star$ from \cref{def:target-coeff}. Finally, let
  $n,m\in\mathbb N$ with $n,m>0$, let
  $x_1,\dots,x_n$ be i.i.d. samples from $\nu$, and let $S=(g_1,\dots,g_m)$ be an independent
  i.i.d. uniform sample from $G$. Then the partially augmented projection density estimator
  $\widehat f_S$ of \cref{def:augmented-density-coeff-estimator} satisfies
  \[
    \mathbb E\bigl[\|\widehat f_S-\Pi_{\mathcal F^G}f^\star\|_{L^2(\mathcal X)}^2\bigr]
    \;\le\;C\left(
      \frac{\|f^\star\|_\infty}{n}\,r_{\mathrm{inv}}
      +\frac{r}{nm}
    \right),
  \]
  where the expectation is over both the base sample and the augmentation set, the squared
  $L^2(\mathcal X)$ error is that of \cref{def:l2-sq-dist}, and $\Pi_{\mathcal F^G}f^\star$ is
  represented by $\Pi_{\mathcal F^G}\theta(f^\star)$ with $\Pi_{\mathcal F^G}$ as in
  \cref{def:invariant-projection}. -/)
  (title := /-- Admissible constant for the density-estimation bound -/)
  (latexEnv := "definition")]
def partial_augmentation_density_bound (C : ℝ) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (mu : Measure X), IsProbabilityMeasure mu →
    ∀ (G : Type) [Group G] [Fintype G] [MulAction G X],
      (∀ g : G, MeasurePreserving (fun x : X => g • x) mu mu) →
    ∀ (r : ℕ) (phi : Fin r → X → ℝ), l2_orthonormal_family mu phi →
      (∀ l, MemLp (phi l) 2 mu) →
    ∀ (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))),
      implements_lifted_action phi rho →
    ∀ (fstar : X → ℝ), (∀ᵐ x ∂mu, 0 ≤ fstar x) → MemLp fstar 2 mu →
      eLpNormEssSup fstar mu ≠ ∞ →
      IsProbabilityMeasure (mu.withDensity fun x => ENNReal.ofReal (fstar x)) →
      invariant_projection rho (target_coeff mu phi fstar) = target_coeff mu phi fstar →
      (eLpNormEssSup fstar mu).toReal ≤ 1 →
    ∀ (n m : ℕ), 0 < n → 0 < m →
      iid_expectation (mu.withDensity fun x => ENNReal.ofReal (fstar x)) n
          (fun xs => uniform_group_expectation m (fun S : Fin m → G =>
            l2_sq_dist mu phi (augmented_density_coeff_estimator phi S xs)
              (invariant_projection rho (target_coeff mu phi fstar))))
        ≤ C * ((eLpNormEssSup fstar mu).toReal * (Module.finrank ℝ rho.invariants) / n
              + r / ((n : ℝ) * (m : ℝ)))

@[blueprint "def:partial-augmentation-regression-bound"
  (statement := /-- Let $C\in\mathbb R$. We say that $C$ is an \emph{admissible regression constant}
  if the following holds for every choice of data. Let $(\mathcal X,\mu)$ be a probability space;
  let $G$ be a finite group acting on $\mathcal X$ such that each $g\in G$ acts by a
  $\mu$-preserving map; let $r\in\mathbb N$ and let $\varphi=(\varphi_\ell)_{\ell\in[r]}$ be an
  $L^2(\mathcal X,\mu)$-orthonormal family as in \cref{def:l2-orthonormal-family} with each
  $\varphi_\ell\in L^2(\mathcal X,\mu)$, spanning $\mathcal F$; let
  $\rho:G\to\mathrm{GL}(\mathbb R^r)$ implement the lifted action as in
  \cref{def:implements-lifted-action} and set $r_{\mathrm{inv}}:=\dim(\mathbb R^r)^G$; let
  $f^\star\in L^2(\mathcal X,\mu)$ with $\|f^\star\|_\infty<\infty$, and let the coefficient
  vector $\theta(f^\star)$ be as in \cref{def:target-coeff}. Write $P_G$ for the invariant
  projection of \cref{def:invariant-projection}, so that $P_G\theta(f^\star)$ represents
  $\Pi_{\mathcal F^G}f^\star$. Let $\eta$ be a centered noise law with variance
  $\sigma^2$ as in \cref{def:centered-noise}. Let
  $n,m\in\mathbb N$ with $n,m>0$. If
  $(x_i,\varepsilon_i)_{i\in[n]}$ are i.i.d. from $\mu\otimes\eta$ and
  $S=(g_1,\dots,g_m)$ consists of i.i.d. uniform samples from $G$, then the partially augmented
  projection regression estimator of \cref{def:augmented-regression-coeff-estimator} satisfies
  \[
    \mathbb E\bigl[\|\widehat f_S-\Pi_{\mathcal F^G}f^\star\|_{L^2(\mathcal X)}^2\bigr]
    \;\le\;C\left(
      \frac{\|f^\star\|_\infty^2+\sigma^2}{n}\,r_{\mathrm{inv}}
      +\frac{(\|f^\star\|_\infty^2+\sigma^2)r}{nm}
      +\frac{\|\theta(f^\star)-P_G\theta(f^\star)\|^2}{m}
    \right),
  \]
  Here the last term records the component of the target coefficient vector orthogonal to the
  invariant subspace; in particular, it vanishes when $\theta(f^\star)$ is $G$-invariant. The
  squared $L^2(\mathcal X)$ error is that of \cref{def:l2-sq-dist}, and
  $\Pi_{\mathcal F^G}$ as in \cref{def:invariant-projection}. -/)
  (title := /-- Admissible constant for the regression bound -/)
  (latexEnv := "definition")]
def partial_augmentation_regression_bound (C : ℝ) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (mu : Measure X), IsProbabilityMeasure mu →
    ∀ (G : Type) [Group G] [Fintype G] [MulAction G X],
      (∀ g : G, MeasurePreserving (fun x : X => g • x) mu mu) →
    ∀ (r : ℕ) (phi : Fin r → X → ℝ), l2_orthonormal_family mu phi →
      (∀ l, MemLp (phi l) 2 mu) →
    ∀ (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))),
      implements_lifted_action phi rho →
    ∀ (fstar : X → ℝ), MemLp fstar 2 mu → eLpNormEssSup fstar mu ≠ ∞ →
    ∀ (eta : Measure ℝ) (sigma : ℝ), centered_noise eta sigma →
    ∀ (n m : ℕ), 0 < n → 0 < m →
      iid_expectation (mu.prod eta) n
          (fun zs => uniform_group_expectation m (fun S : Fin m → G =>
            l2_sq_dist mu phi (augmented_regression_coeff_estimator phi fstar S zs)
              (invariant_projection rho (target_coeff mu phi fstar))))
        ≤ C * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2)
                * (Module.finrank ℝ rho.invariants) / n
              + ((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * (r : ℝ)
                  / ((n : ℝ) * (m : ℝ))
              + ‖target_coeff mu phi fstar
                    - invariant_projection rho (target_coeff mu phi fstar)‖ ^ 2 / m)

@[blueprint "thm:partial-augmentation-excess-density"
  (statement := /-- There exists an absolute constant $C>0$ which is an admissible
  density-estimation constant in the sense of
  \cref{def:partial-augmentation-density-bound}. Explicitly, for every probability space
  $(\mathcal X,\mu)$, every finite group $G$ acting on $\mathcal X$ by $\mu$-preserving maps, every
  $r$-dimensional subspace $\mathcal F\subset L^2(\mathcal X,\mu)$ presented by an
  $L^2$-orthonormal family and closed under the action of $G$, with invariant subspace
  $\mathcal F^G$ of dimension $r_{\mathrm{inv}}$, and every
  nonnegative $f^\star\in L^2(\mathcal X,\mu)\cap L^\infty(\mathcal X,\mu)$ satisfying
  $\int_{\mathcal X}f^\star\,d\mu=1$ and $\|f^\star\|_\infty\le 1$, assume that
  $\Pi_{\mathcal F}f^\star\in\mathcal F^G$, and let $\nu$ be the probability measure
  $d\nu=f^\star\,d\mu$. For every $n,m\in\mathbb N$ with $n,m>0$, the partially augmented
  projection density estimator $\widehat f_S$ built from $n$ i.i.d. samples
  $x_1,\dots,x_n\sim\nu$ and an independent tuple
  $S=(g_1,\dots,g_m)$ of $m$ i.i.d. uniform samples from $G$ satisfies
  \[
    \mathbb E\bigl[\|\widehat f_S-\Pi_{\mathcal F^G}f^\star\|_{L^2(\mathcal X)}^2\bigr]
    \le C\left(
      \frac{\|f^\star\|_\infty}{n}\,r_{\mathrm{inv}}
      +\frac{r}{nm}
    \right).
  \]
  -/)
  (proof := /-- Fix data satisfying the hypotheses in
  \cref{def:partial-augmentation-density-bound}. Let
  $\nu:=f^\star\mu$, let $\theta:=\theta(f^\star)$ be the coefficient vector of
  $\Pi_{\mathcal F}f^\star$, and let $\widehat\theta$ be the non-augmented projection density
  estimator based on the $n$ observations with law $\nu$. By \cref{lem:baseline-density-excess},
  \[
    \mathbb E\|\widehat\theta-\theta\|^2
    \le\frac{\|f^\star\|_\infty r}{n}.
  \]
  Since the action preserves $\mu$ and the family $\varphi$ is orthonormal,
  \cref{lem:representation-orthogonal-of-measure-preserving} shows that $\rho$ is orthogonal.
  The invariant-space estimate \cref{lem:invariant-baseline-density-excess}, together with
  \cref{lem:group-average-eq-invariant-projection}, yields
  \[
    \mathbb E\|\Pi_G\widehat\theta-\Pi_G\theta\|^2
    \le \frac{\|f^\star\|_\infty r_{\mathrm{inv}}}{n}.
  \]
  Because $f^\star$ is essentially bounded and every $\varphi_\ell$ belongs to
  $L^2(\mathcal X,\mu)$, \cref{lem:memlp-of-density-bounded} gives
  $\varphi_\ell\in L^2(\mathcal X,\nu)$ for every $\ell$. Expanding squared Euclidean norms
  coordinatewise and using closure of $L^2$ under finite linear combinations shows that the
  squared distances from $\widehat\theta$ to $\theta$ and to
  $\Pi_{\mathcal F^G}\theta$ are integrable. Moreover,
  \cref{lem:random-averaging-variance} identifies the conditional augmentation error with
  $m^{-1}\|\widehat\theta-\Pi_G\widehat\theta\|^2$, whose integrability follows by the same
  coordinatewise argument. We may therefore apply
  \cref{lem:general-augmentation-error-bound} and then the preceding full-space estimate to obtain
  \[
    \mathbb E\|\Pi_S\widehat\theta-\Pi_G\widehat\theta\|^2
    \le\frac{2}{m}\left(
      \frac{\|f^\star\|_\infty r}{n}
      +\|\theta-\Pi_{\mathcal F^G}\theta\|^2\right)
    \le \frac{2r}{nm}.
  \]
  Indeed, the invariance hypothesis makes the squared residual zero, and
  $\|f^\star\|_\infty\le 1$ bounds the remaining summand.
  By \cref{lem:augmented-density-estimator-eq-empirical-average}, the coefficient vector of the
  partially augmented estimator is $\Pi_S\widehat\theta$. The decomposition
  \[
    \Pi_S\widehat\theta-\Pi_G\theta
    =(\Pi_S\widehat\theta-\Pi_G\widehat\theta)
      +(\Pi_G\widehat\theta-\Pi_G\theta)
  \]
  and \cref{lem:norm-add-sq-doubling} show that
  \[
    \mathbb E\|\Pi_S\widehat\theta-\Pi_G\theta\|^2
    \le
      2\frac{\|f^\star\|_\infty r_{\mathrm{inv}}}{n}
      +4\frac{r}{nm}.
  \]
  Finally, \cref{lem:parseval-coeff-norm} identifies this coefficient norm with the squared
  $L^2(\mathcal X)$ error, while \cref{lem:group-average-eq-invariant-projection} identifies
  $\Pi_G\theta$ with the coefficient vector of $\Pi_{\mathcal F^G}f^\star$. Thus $C=4$ is
  admissible. -/)
  (title := /-- Partial data augmentation for projection density estimators -/)
  (latexEnv := "theorem")]
theorem partial_augmentation_excess_density :
    ∃ C : ℝ, 0 < C ∧ partial_augmentation_density_bound C := by
  classical
  refine ⟨4, by norm_num, ?_⟩
  dsimp only [partial_augmentation_density_bound]
  intro X _ mu hmu G _ _ _ hact r phi hphi hmem rho himpl
    fstar hf0 hfmem hfinf hprob hinv hess n m hn hm
  let nu : Measure X := mu.withDensity fun x => ENNReal.ofReal (fstar x)
  let theta : EuclideanSpace ℝ (Fin r) := target_coeff mu phi fstar
  let chat : (Fin n → X) → EuclideanSpace ℝ (Fin r) := density_coeff_estimator phi
  letI : IsProbabilityMeasure nu := by simpa only [nu] using hprob
  have hrho : orthogonal_representation rho :=
    representation_orthogonal_of_measure_preserving mu phi rho hact hphi hmem himpl
  have hphinu : ∀ l, MemLp (phi l) 2 nu := fun l =>
    memlp_of_density_bounded mu fstar hfinf (phi l) (hmem l)
  have hchatmem (l : Fin r) : MemLp (fun xs => chat xs l) 2
      (Measure.pi fun _ : Fin n => nu) := by
    have hcoords : ∀ i : Fin n, MemLp (fun xs : Fin n → X => phi l (xs i)) 2
        (Measure.pi fun _ : Fin n => nu) := fun i =>
      (hphinu l).comp_measurePreserving (measurePreserving_eval _ i)
    simpa [chat, density_coeff_estimator] using
      (memLp_finsetSum Finset.univ fun i _ => hcoords i).const_mul (n : ℝ)⁻¹
  have hdist (b : EuclideanSpace ℝ (Fin r)) :
      Integrable (fun xs => ‖chat xs - b‖ ^ 2) (Measure.pi fun _ : Fin n => nu) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    exact integrable_finset_sum _ fun l _ =>
      ((hchatmem l).sub (memLp_const (b l))).integrable_sq
  have hmapcoord (A : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r))
      (l : Fin r) : MemLp (fun xs => A (chat xs) l) 2
        (Measure.pi fun _ : Fin n => nu) := by
    have heq : (fun xs => A (chat xs) l) =
        (fun xs => ∑ k, chat xs k * (A (EuclideanSpace.basisFun (Fin r) ℝ k)) l) := by
      funext xs
      have hsum : (∑ k, chat xs k • EuclideanSpace.basisFun (Fin r) ℝ k) = chat xs := by
        simpa using (EuclideanSpace.basisFun (Fin r) ℝ).sum_repr (chat xs)
      calc
        (A (chat xs)) l =
            (A (∑ k, chat xs k • EuclideanSpace.basisFun (Fin r) ℝ k)) l := by
          rw [hsum]
        _ = ∑ k, chat xs k * (A (EuclideanSpace.basisFun (Fin r) ℝ k)) l := by
          simp
    rw [heq]
    exact memLp_finsetSum Finset.univ fun k _ => by
      simpa [mul_comm] using
        (hchatmem k).const_mul ((A (EuclideanSpace.basisFun (Fin r) ℝ k)) l)
  have hrhocoord (g : G) (l : Fin r) : MemLp (fun xs => rho g (chat xs) l) 2
      (Measure.pi fun _ : Fin n => nu) :=
    hmapcoord (rho g) l
  have hgroupcoord (l : Fin r) :
      MemLp (fun xs => group_average_operator rho (chat xs) l) 2
        (Measure.pi fun _ : Fin n => nu) := by
    simpa [group_average_operator] using
      (memLp_finsetSum Finset.univ fun g _ => hrhocoord g l).const_mul
        (Fintype.card G : ℝ)⁻¹
  have hgroupdiff :
      Integrable (fun xs => ‖chat xs - group_average_operator rho (chat xs)‖ ^ 2)
        (Measure.pi fun _ : Fin n => nu) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    exact integrable_finset_sum _ fun l _ => ((hchatmem l).sub (hgroupcoord l)).integrable_sq
  have hconditional : Integrable (fun xs => uniform_group_expectation m
      (fun S => ‖empirical_average_operator rho S (chat xs)
        - group_average_operator rho (chat xs)‖ ^ 2))
      (Measure.pi fun _ : Fin n => nu) := by
    refine (hgroupdiff.const_mul (m : ℝ)⁻¹).congr
      (Filter.Eventually.of_forall fun xs => ?_)
    exact (random_averaging_variance rho hrho m hm (chat xs)).symm
  have hinv' : invariant_projection rho theta = theta := by
    simpa only [theta] using hinv
  have hbase : iid_expectation nu n (fun xs => ‖chat xs - theta‖ ^ 2)
      ≤ (eLpNormEssSup fstar mu).toReal * r / n := by
    simpa only [nu, chat, theta] using
      baseline_density_excess mu phi hphi hmem fstar hf0 hfmem hfinf hprob n hn
  have hinvbase : iid_expectation nu n (fun xs =>
      ‖group_average_operator rho (chat xs) - group_average_operator rho theta‖ ^ 2)
      ≤ (eLpNormEssSup fstar mu).toReal * Module.finrank ℝ rho.invariants / n := by
    simpa only [nu, chat, theta] using
      invariant_baseline_density_excess mu phi rho hrho hphi hmem fstar hf0 hfmem hfinf
        hprob n hn
  have haugmentation := general_augmentation_error_bound nu rho hrho n m hm chat theta
    (hdist theta) (hdist (invariant_projection rho theta)) hconditional
  have haugmentation' : iid_expectation nu n (fun xs => uniform_group_expectation m
      (fun S => ‖empirical_average_operator rho S (chat xs)
        - group_average_operator rho (chat xs)‖ ^ 2))
      ≤ 2 * (m : ℝ)⁻¹ * iid_expectation nu n (fun xs => ‖chat xs - theta‖ ^ 2) := by
    simpa [hinv'] using haugmentation
  have hess0 : 0 ≤ (eLpNormEssSup fstar mu).toReal := ENNReal.toReal_nonneg
  have hbaseunit : iid_expectation nu n (fun xs => ‖chat xs - theta‖ ^ 2)
      ≤ (r : ℝ) / n := by
    refine hbase.trans ?_
    calc
      (eLpNormEssSup fstar mu).toReal * r / n ≤ 1 * r / n := by gcongr
      _ = (r : ℝ) / n := by ring
  have haugmentation_rate : iid_expectation nu n (fun xs => uniform_group_expectation m
      (fun S => ‖empirical_average_operator rho S (chat xs)
        - group_average_operator rho (chat xs)‖ ^ 2))
      ≤ 2 * (r : ℝ) / ((n : ℝ) * (m : ℝ)) := by
    calc
      _ ≤ 2 * (m : ℝ)⁻¹ * iid_expectation nu n
          (fun xs => ‖chat xs - theta‖ ^ 2) := haugmentation'
      _ ≤ 2 * (m : ℝ)⁻¹ * ((r : ℝ) / n) := by gcongr
      _ = 2 * (r : ℝ) / ((n : ℝ) * (m : ℝ)) := by
        field_simp [Nat.cast_ne_zero.mpr hn.ne', Nat.cast_ne_zero.mpr hm.ne']
  have hempcoord (S : Fin m → G) (l : Fin r) :
      MemLp (fun xs => empirical_average_operator rho S (chat xs) l) 2
        (Measure.pi fun _ : Fin n => nu) := by
    simpa [empirical_average_operator] using
      (memLp_finsetSum Finset.univ fun j _ => hrhocoord (S j) l).const_mul (m : ℝ)⁻¹
  have hriskint : Integrable (fun xs => uniform_group_expectation m
      (fun S => ‖empirical_average_operator rho S (chat xs)
        - group_average_operator rho theta‖ ^ 2))
      (Measure.pi fun _ : Fin n => nu) := by
    unfold uniform_group_expectation
    exact (integrable_finset_sum _ fun S _ =>
      (by
        simp_rw [EuclideanSpace.real_norm_sq_eq]
        exact integrable_finset_sum _ fun l _ =>
          ((hempcoord S l).sub (memLp_const _)).integrable_sq)).const_mul _
  have hinvint : Integrable (fun xs =>
      ‖group_average_operator rho (chat xs) - group_average_operator rho theta‖ ^ 2)
      (Measure.pi fun _ : Fin n => nu) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    exact integrable_finset_sum _ fun l _ =>
      ((hgroupcoord l).sub (memLp_const _)).integrable_sq
  have hupperint : Integrable (fun xs =>
      2 * uniform_group_expectation m (fun S =>
        ‖empirical_average_operator rho S (chat xs)
          - group_average_operator rho (chat xs)‖ ^ 2)
      + 2 * ‖group_average_operator rho (chat xs) - group_average_operator rho theta‖ ^ 2)
      (Measure.pi fun _ : Fin n => nu) :=
    (hconditional.const_mul 2).add (hinvint.const_mul 2)
  have hue_mono (F H : (Fin m → G) → ℝ) (hFH : ∀ S, F S ≤ H S) :
      uniform_group_expectation m F ≤ uniform_group_expectation m H := by
    unfold uniform_group_expectation
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S _ => hFH S) (by positivity)
  have hue_add (F H : (Fin m → G) → ℝ) :
      uniform_group_expectation m (fun S => F S + H S) =
        uniform_group_expectation m F + uniform_group_expectation m H := by
    simp [uniform_group_expectation, Finset.sum_add_distrib]
    ring
  have hue_mul (a : ℝ) (F : (Fin m → G) → ℝ) :
      uniform_group_expectation m (fun S => a * F S) =
        a * uniform_group_expectation m F := by
    simp [uniform_group_expectation, Finset.mul_sum]
    ring_nf
  have hue_const (a : ℝ) :
      uniform_group_expectation m (fun _ : Fin m → G => a) = a := by
    simp [uniform_group_expectation]
  have hue_doubling (F : (Fin m → G) → ℝ) (a : ℝ) :
      uniform_group_expectation m (fun S => 2 * F S + 2 * a)
        = 2 * uniform_group_expectation m F + 2 * a := by
    rw [hue_add, hue_mul, hue_const]
  have hpoint (xs : Fin n → X) :
      uniform_group_expectation m (fun S =>
        ‖empirical_average_operator rho S (chat xs) - group_average_operator rho theta‖ ^ 2)
      ≤ 2 * uniform_group_expectation m (fun S =>
          ‖empirical_average_operator rho S (chat xs)
            - group_average_operator rho (chat xs)‖ ^ 2)
        + 2 * ‖group_average_operator rho (chat xs) - group_average_operator rho theta‖ ^ 2 := by
    calc
      _ ≤ uniform_group_expectation m (fun S =>
          2 * ‖empirical_average_operator rho S (chat xs)
            - group_average_operator rho (chat xs)‖ ^ 2
          + 2 * ‖group_average_operator rho (chat xs)
            - group_average_operator rho theta‖ ^ 2) := by
        apply hue_mono
        intro S
        rw [show empirical_average_operator rho S (chat xs) - group_average_operator rho theta =
          (empirical_average_operator rho S (chat xs)
            - group_average_operator rho (chat xs))
          + (group_average_operator rho (chat xs)
            - group_average_operator rho theta) by abel]
        exact norm_add_sq_doubling _ _
      _ = _ := hue_doubling _ _
  have htotal0 : iid_expectation nu n (fun xs => uniform_group_expectation m
      (fun S => ‖empirical_average_operator rho S (chat xs)
        - group_average_operator rho theta‖ ^ 2))
      ≤ 2 * iid_expectation nu n (fun xs => uniform_group_expectation m
          (fun S => ‖empirical_average_operator rho S (chat xs)
            - group_average_operator rho (chat xs)‖ ^ 2))
        + 2 * iid_expectation nu n (fun xs =>
          ‖group_average_operator rho (chat xs) - group_average_operator rho theta‖ ^ 2) := by
    unfold iid_expectation
    calc
      _ ≤ ∫ xs, (2 * uniform_group_expectation m (fun S =>
            ‖empirical_average_operator rho S (chat xs)
              - group_average_operator rho (chat xs)‖ ^ 2)
          + 2 * ‖group_average_operator rho (chat xs)
              - group_average_operator rho theta‖ ^ 2)
          ∂(Measure.pi fun _ : Fin n => nu) :=
        integral_mono hriskint hupperint hpoint
      _ = _ := by
        rw [integral_add (hconditional.const_mul 2) (hinvint.const_mul 2),
          integral_const_mul, integral_const_mul]
  have hinvterm0 : 0 ≤ (eLpNormEssSup fstar mu).toReal
      * Module.finrank ℝ rho.invariants / (n : ℝ) := by positivity
  have htotal : iid_expectation nu n (fun xs => uniform_group_expectation m
      (fun S => ‖empirical_average_operator rho S (chat xs)
        - group_average_operator rho theta‖ ^ 2))
      ≤ 4 * ((eLpNormEssSup fstar mu).toReal * Module.finrank ℝ rho.invariants / n
        + r / ((n : ℝ) * (m : ℝ))) := by
    calc
      _ ≤ 2 * iid_expectation nu n (fun xs => uniform_group_expectation m
            (fun S => ‖empirical_average_operator rho S (chat xs)
              - group_average_operator rho (chat xs)‖ ^ 2))
          + 2 * iid_expectation nu n (fun xs =>
            ‖group_average_operator rho (chat xs) - group_average_operator rho theta‖ ^ 2) :=
        htotal0
      _ ≤ 2 * (2 * (r : ℝ) / ((n : ℝ) * (m : ℝ)))
          + 2 * ((eLpNormEssSup fstar mu).toReal
            * Module.finrank ℝ rho.invariants / n) := by gcongr
      _ ≤ 4 * ((eLpNormEssSup fstar mu).toReal * Module.finrank ℝ rho.invariants / n
          + r / ((n : ℝ) * (m : ℝ))) := by
        let A : ℝ := (eLpNormEssSup fstar mu).toReal
          * Module.finrank ℝ rho.invariants / n
        let B : ℝ := (r : ℝ) / ((n : ℝ) * (m : ℝ))
        have hA : 0 ≤ A := hinvterm0
        have hAB : 2 * (2 * B) + 2 * A ≤ 4 * (A + B) := by linarith
        convert hAB using 1 <;> simp only [A, B] <;> ring
  rw [show (fun xs => uniform_group_expectation m (fun S : Fin m → G =>
      l2_sq_dist mu phi (augmented_density_coeff_estimator phi S xs)
        (invariant_projection rho (target_coeff mu phi fstar)))) =
      (fun xs => uniform_group_expectation m (fun S : Fin m → G =>
        ‖empirical_average_operator rho S (chat xs) - group_average_operator rho theta‖ ^ 2))
      from funext fun xs => by
        congr 1
        funext S
        rw [parseval_coeff_norm mu phi hphi hmem,
          augmented_density_estimator_eq_empirical_average mu phi rho hact hphi hmem himpl,
          group_average_eq_invariant_projection rho hrho]]
  exact htotal

@[blueprint "thm:partial-augmentation-excess-regression"
  (statement := /-- There exists an absolute constant $C>0$ which is an admissible regression
  constant in the sense of \cref{def:partial-augmentation-regression-bound}. Explicitly, let
  $(\mathcal X,\mu)$ be a probability space, let a finite group $G$ act on $\mathcal X$ by
  $\mu$-preserving maps, and let the $r$-dimensional space $\mathcal F$ be spanned by an
  $L^2(\mathcal X,\mu)$-orthonormal family and be stable under the induced action. Write
  $r_{\mathrm{inv}}:=\dim\mathcal F^G$. For every
  $f^\star\in L^2(\mathcal X,\mu)\cap L^\infty(\mathcal X,\mu)$, let
  $\theta(f^\star)$ be its coefficient vector from \cref{def:target-coeff}, and let $P_G$ be the
  invariant projection of \cref{def:invariant-projection}. For every centered noise law
  $\eta$ of variance $\sigma^2$ in the sense of \cref{def:centered-noise}, and every
  $n,m\in\mathbb N$ with $n,m>0$, let
  $y_i=f^\star(x_i)+\varepsilon_i$, where the pairs
  $(x_i,\varepsilon_i)_{i\in[n]}$ are independent samples from $\mu\otimes\eta$. If
  $S=(g_1,\dots,g_m)$ is an independent tuple of uniform samples from $G$, then the partially augmented
  projection regression estimator $\widehat f_S$ satisfies
  \[
    \mathbb E\bigl[\|\widehat f_S-\Pi_{\mathcal F^G}f^\star\|_{L^2(\mathcal X)}^2\bigr]
    \le C\left(
      \frac{\|f^\star\|_\infty^2+\sigma^2}{n}\,r_{\mathrm{inv}}
      +\frac{(\|f^\star\|_\infty^2+\sigma^2)r}{nm}
      +\frac{\|\theta(f^\star)-P_G\theta(f^\star)\|^2}{m}
    \right).
  \]
  The last summand is zero whenever the target coefficient vector is $G$-invariant.
  -/)
  (proof := /-- Fix data satisfying \cref{def:partial-augmentation-regression-bound}. Let
  $\theta:=\theta(f^\star)$ be the coefficient vector of
  $\Pi_{\mathcal F}f^\star$, let $\widehat\beta$ be the non-augmented regression estimator,
  and put $q:=\|f^\star\|_\infty^2+\sigma^2$. Let $P$ be the orthogonal projection onto the
  invariant coefficient subspace. By
  \cref{lem:representation-orthogonal-of-measure-preserving}, the coefficient representation is
  orthogonal. Hence \cref{lem:group-average-eq-invariant-projection} identifies its group
  average with $P$.

  By \cref{lem:augmented-regression-estimator-eq-empirical-average}, the augmented coefficient
  estimator is $\Pi_S\widehat\beta$. Apply \cref{lem:general-augmentation-error-bound} with the
  arbitrary target $\theta$. Its integrability hypotheses hold because every coordinate of the
  empirical regression estimator is square-integrable under the hypotheses of
  \cref{lem:baseline-regression-excess}; the invariant projection is linear on the
  finite-dimensional coefficient space, and the conditional augmentation error is a finite
  average of squared norms of linear images of that estimator. We obtain
  \[
    \mathbb E\!\left[\mathbb E_S
      \|\Pi_S\widehat\beta-P\widehat\beta\|^2\right]
    \le \frac{2}{m}\left(
      \mathbb E\|\widehat\beta-\theta\|^2+\|\theta-P\theta\|^2
    \right).
  \]
  The full-space estimate \cref{lem:baseline-regression-excess} bounds the first term in
  parentheses by $qr/n$. Consequently, the augmentation contribution is at most
  $2qr/(nm)+2\|\theta-P\theta\|^2/m$.

  Independently, \cref{lem:invariant-baseline-regression-excess} gives
  \[
    \mathbb E\|P\widehat\beta-P\theta\|^2
    \le \frac{q}{n}r_{\mathrm{inv}}.
  \]

  Decompose
  \[
    \Pi_S\widehat\beta-P\theta
    =(\Pi_S\widehat\beta-P\widehat\beta)
      +(P\widehat\beta-P\theta).
  \]
  By \cref{lem:norm-add-sq-doubling}, the expected squared norm of the left-hand side is at most
  twice the sum of the preceding two bounds. Thus
  \[
    \mathbb E\|\Pi_S\widehat\beta-P\theta\|^2
    \le 2\frac{q}{n}r_{\mathrm{inv}}+4\frac{qr}{nm}
      +4\frac{\|\theta-P\theta\|^2}{m}
    \le 4\left(\frac{q}{n}r_{\mathrm{inv}}+\frac{qr}{nm}
      +\frac{\|\theta-P\theta\|^2}{m}\right).
  \]
  The last inequality follows because all three summands are nonnegative.
  Finally, \cref{lem:parseval-coeff-norm} transfers this coefficient estimate to
  $L^2(\mathcal X)$, while \cref{lem:group-average-eq-invariant-projection} identifies
  $P\theta$ with the coefficient vector of $\Pi_{\mathcal F^G}f^\star$. Thus $C=4$ is
  admissible. -/)
  (title := /-- Partial data augmentation for projection regression estimators -/)
  (latexEnv := "theorem")]
theorem partial_augmentation_excess_regression :
    ∃ C : ℝ, 0 < C ∧ partial_augmentation_regression_bound C := by
  classical
  refine ⟨4, by norm_num, ?_⟩
  dsimp only [partial_augmentation_regression_bound]
  intro X _ mu hmu G _ _ _ hact r phi hphi hmem rho himpl fstar hfmem hfinf eta sigma heta
    n m hn hm
  haveI hetaprob : IsProbabilityMeasure eta := heta.1
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hrho : orthogonal_representation rho :=
    representation_orthogonal_of_measure_preserving mu phi rho hact hphi hmem himpl
  have hinvterm0 : (0 : ℝ) ≤ ((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2)
      * (Module.finrank ℝ rho.invariants) / n := by positivity
  rw [show (fun zs => uniform_group_expectation m (fun S : Fin m → G =>
      l2_sq_dist mu phi (augmented_regression_coeff_estimator phi fstar S zs)
        (invariant_projection rho (target_coeff mu phi fstar)))) =
      (fun zs => uniform_group_expectation m (fun S : Fin m → G =>
        ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
          - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2))
      from funext fun zs => by
        congr 1
        funext S
        rw [parseval_coeff_norm mu phi hphi hmem,
          augmented_regression_estimator_eq_empirical_average mu phi rho fstar hact hphi hmem
            himpl,
          group_average_eq_invariant_projection rho hrho]]
  have hPsimeas : ∀ l : Fin r, AEStronglyMeasurable
      (fun z : X × ℝ => (fstar z.1 + z.2) * phi l z.1) (mu.prod eta) := fun l =>
    ((hfmem.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).add
        measurable_snd.aestronglyMeasurable).mul
      ((hmem l).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have hnormcoord : ∀ (b : EuclideanSpace ℝ (Fin r)) (zs : Fin n → X × ℝ),
      ‖regression_coeff_estimator phi fstar zs - b‖ ^ 2
        = ∑ l, ((n : ℝ)⁻¹ * ∑ i, (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1) - b l) ^ 2 := by
    intro b zs
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [regression_coeff_estimator]
  have hcoordmeas : ∀ (b : EuclideanSpace ℝ (Fin r)) (l : Fin r), AEStronglyMeasurable
      (fun zs : Fin n → X × ℝ =>
        ((n : ℝ)⁻¹ * ∑ i, (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1) - b l) ^ 2)
      (Measure.pi fun _ : Fin n => mu.prod eta) := by
    intro b l
    have hev : ∀ i : Fin n, AEStronglyMeasurable
        (fun zs : Fin n → X × ℝ => (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1))
        (Measure.pi fun _ : Fin n => mu.prod eta) := fun i =>
      (hPsimeas l).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => mu.prod eta) i)
    exact ((((Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ =>
      hev i).const_mul ((n : ℝ)⁻¹)).sub aestronglyMeasurable_const).pow 2)
  by_cases hriskint : Integrable (fun zs : Fin n → X × ℝ => uniform_group_expectation m
      (fun S : Fin m → G =>
        ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
          - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2))
      (Measure.pi fun _ : Fin n => mu.prod eta)
  ·
    have hcardpos : (0 : ℝ) < (Fintype.card G : ℝ) ^ m := by
      have : 0 < Fintype.card G := Fintype.card_pos
      positivity
    have hugenn : ∀ zs : Fin n → X × ℝ, 0 ≤ uniform_group_expectation m
        (fun S : Fin m → G =>
          ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
            - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2) := by
      intro zs
      rw [uniform_group_expectation]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun S _ => sq_nonneg _)
    have hdom : ∀ zs : Fin n → X × ℝ,
        ((Fintype.card G : ℝ) ^ m)⁻¹
            * ‖regression_coeff_estimator phi fstar zs
                - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2
          ≤ uniform_group_expectation m (fun S : Fin m → G =>
              ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
                - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2) := by
      intro zs
      have hone : empirical_average_operator rho (fun _ : Fin m => (1 : G))
          (regression_coeff_estimator phi fstar zs)
            = regression_coeff_estimator phi fstar zs := by
        have h1 : ∀ c : EuclideanSpace ℝ (Fin r), rho (1 : G) c = c := by
          intro c; simp
        rw [empirical_average_operator]
        simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
      have hterm := Finset.single_le_sum
        (f := fun S : Fin m → G =>
          ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
            - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
        (fun S _ => sq_nonneg _) (Finset.mem_univ (fun _ : Fin m => (1 : G)))
      rw [hone] at hterm
      rw [uniform_group_expectation]
      exact mul_le_mul_of_nonneg_left hterm (by positivity)
    have hnormint : Integrable (fun zs : Fin n → X × ℝ =>
        ‖regression_coeff_estimator phi fstar zs
          - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
        (Measure.pi fun _ : Fin n => mu.prod eta) := by
      have hmeas : AEStronglyMeasurable (fun zs : Fin n → X × ℝ =>
          ((Fintype.card G : ℝ) ^ m)⁻¹ * ‖regression_coeff_estimator phi fstar zs
            - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
          (Measure.pi fun _ : Fin n => mu.prod eta) := by
        have hsum : AEStronglyMeasurable (fun zs : Fin n → X × ℝ =>
            ∑ l, ((n : ℝ)⁻¹ * ∑ i, (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1)
              - group_average_operator rho (target_coeff mu phi fstar) l) ^ 2)
            (Measure.pi fun _ : Fin n => mu.prod eta) :=
          Finset.aestronglyMeasurable_fun_sum Finset.univ fun l _ =>
            hcoordmeas (group_average_operator rho (target_coeff mu phi fstar)) l
        refine (hsum.const_mul (((Fintype.card G : ℝ) ^ m)⁻¹)).congr
          (Filter.Eventually.of_forall fun zs => ?_)
        simp only [hnormcoord]
      have h1 : Integrable (fun zs : Fin n → X × ℝ =>
          ((Fintype.card G : ℝ) ^ m)⁻¹ * ‖regression_coeff_estimator phi fstar zs
            - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
          (Measure.pi fun _ : Fin n => mu.prod eta) := by
        refine hriskint.mono hmeas (Filter.Eventually.of_forall fun zs => ?_)
        have h0 : (0 : ℝ) ≤ ((Fintype.card G : ℝ) ^ m)⁻¹
            * ‖regression_coeff_estimator phi fstar zs
              - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2 := by positivity
        rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (hugenn zs)]
        exact hdom zs
      refine (h1.const_mul ((Fintype.card G : ℝ) ^ m)).congr
        (Filter.Eventually.of_forall fun zs => ?_)
      simp only [← mul_assoc, mul_inv_cancel₀ hcardpos.ne', one_mul]
    have hcoordint : ∀ l : Fin r, Integrable (fun zs : Fin n → X × ℝ =>
        ((n : ℝ)⁻¹ * ∑ i, (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1)
          - group_average_operator rho (target_coeff mu phi fstar) l) ^ 2)
        (Measure.pi fun _ : Fin n => mu.prod eta) := by
      have hsplit : Integrable (fun zs : Fin n → X × ℝ =>
          ∑ l, ((n : ℝ)⁻¹ * ∑ i, (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1)
            - group_average_operator rho (target_coeff mu phi fstar) l) ^ 2)
          (Measure.pi fun _ : Fin n => mu.prod eta) :=
        hnormint.congr (Filter.Eventually.of_forall fun zs => hnormcoord _ zs)
      exact fun l => integrable_of_integrable_sum_nonneg
        (Measure.pi fun _ : Fin n => mu.prod eta)
        (fun l zs => ((n : ℝ)⁻¹ * ∑ i, (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1)
          - group_average_operator rho (target_coeff mu phi fstar) l) ^ 2)
        (fun l => hcoordmeas (group_average_operator rho (target_coeff mu phi fstar)) l)
        (fun l zs => sq_nonneg _) hsplit l
    have hmemPsi : ∀ l : Fin r,
        MemLp (fun z : X × ℝ => (fstar z.1 + z.2) * phi l z.1) 2 (mu.prod eta) := fun l =>
      memLp_of_integrable_empirical_mean_sq (mu.prod eta) _ (hPsimeas l)
        (group_average_operator rho (target_coeff mu phi fstar) l) n hn (hcoordint l)
    have hchatmem : ∀ l : Fin r, MemLp (fun zs : Fin n → X × ℝ =>
        regression_coeff_estimator phi fstar zs l) 2
        (Measure.pi fun _ : Fin n => mu.prod eta) := by
      intro l
      have hcoords : ∀ i : Fin n, MemLp (fun zs : Fin n → X × ℝ =>
          (fstar (zs i).1 + (zs i).2) * phi l ((zs i).1)) 2
          (Measure.pi fun _ : Fin n => mu.prod eta) := fun i =>
        (hmemPsi l).comp_measurePreserving
          (measurePreserving_eval (fun _ : Fin n => mu.prod eta) i)
      simpa [regression_coeff_estimator] using
        (memLp_finsetSum Finset.univ fun i _ => hcoords i).const_mul (n : ℝ)⁻¹
    have hdist : ∀ b : EuclideanSpace ℝ (Fin r), Integrable (fun zs : Fin n → X × ℝ =>
        ‖regression_coeff_estimator phi fstar zs - b‖ ^ 2)
        (Measure.pi fun _ : Fin n => mu.prod eta) := by
      intro b
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      exact integrable_finset_sum _ fun l _ =>
        ((hchatmem l).sub (memLp_const (b l))).integrable_sq
    have hmapcoord : ∀ (A : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r))
        (l : Fin r), MemLp (fun zs : Fin n → X × ℝ =>
          A (regression_coeff_estimator phi fstar zs) l) 2
          (Measure.pi fun _ : Fin n => mu.prod eta) := by
      intro A l
      have heq : (fun zs : Fin n → X × ℝ => A (regression_coeff_estimator phi fstar zs) l) =
          (fun zs => ∑ k, regression_coeff_estimator phi fstar zs k
            * (A (EuclideanSpace.basisFun (Fin r) ℝ k)) l) := by
        funext zs
        have hsum : (∑ k, regression_coeff_estimator phi fstar zs k
            • EuclideanSpace.basisFun (Fin r) ℝ k) = regression_coeff_estimator phi fstar zs := by
          simpa using
            (EuclideanSpace.basisFun (Fin r) ℝ).sum_repr (regression_coeff_estimator phi fstar zs)
        calc
          (A (regression_coeff_estimator phi fstar zs)) l =
              (A (∑ k, regression_coeff_estimator phi fstar zs k
                • EuclideanSpace.basisFun (Fin r) ℝ k)) l := by
            rw [hsum]
          _ = ∑ k, regression_coeff_estimator phi fstar zs k
              * (A (EuclideanSpace.basisFun (Fin r) ℝ k)) l := by
            simp
      rw [heq]
      exact memLp_finsetSum Finset.univ fun k _ => by
        simpa [mul_comm] using
          (hchatmem k).const_mul ((A (EuclideanSpace.basisFun (Fin r) ℝ k)) l)
    have hrhocoord : ∀ (g : G) (l : Fin r), MemLp (fun zs : Fin n → X × ℝ =>
        rho g (regression_coeff_estimator phi fstar zs) l) 2
        (Measure.pi fun _ : Fin n => mu.prod eta) := fun g l => hmapcoord (rho g) l
    have hgroupcoord : ∀ l : Fin r, MemLp (fun zs : Fin n → X × ℝ =>
        group_average_operator rho (regression_coeff_estimator phi fstar zs) l) 2
        (Measure.pi fun _ : Fin n => mu.prod eta) := by
      intro l
      simpa [group_average_operator] using
        (memLp_finsetSum Finset.univ fun g _ => hrhocoord g l).const_mul
          (Fintype.card G : ℝ)⁻¹
    have hgroupdiff : Integrable (fun zs : Fin n → X × ℝ =>
        ‖regression_coeff_estimator phi fstar zs
          - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2)
        (Measure.pi fun _ : Fin n => mu.prod eta) := by
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      exact integrable_finset_sum _ fun l _ =>
        ((hchatmem l).sub (hgroupcoord l)).integrable_sq
    have hconditional : Integrable (fun zs : Fin n → X × ℝ => uniform_group_expectation m
        (fun S : Fin m → G =>
          ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
            - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2))
        (Measure.pi fun _ : Fin n => mu.prod eta) := by
      refine (hgroupdiff.const_mul (m : ℝ)⁻¹).congr
        (Filter.Eventually.of_forall fun zs => ?_)
      exact (random_averaging_variance rho hrho m hm
        (regression_coeff_estimator phi fstar zs)).symm
    have hinvint : Integrable (fun zs : Fin n → X × ℝ =>
        ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
          - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
        (Measure.pi fun _ : Fin n => mu.prod eta) := by
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      exact integrable_finset_sum _ fun l _ =>
        ((hgroupcoord l).sub (memLp_const _)).integrable_sq
    have hupperint : Integrable (fun zs : Fin n → X × ℝ =>
        2 * uniform_group_expectation m (fun S : Fin m → G =>
          ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
            - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2)
        + 2 * ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
            - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
        (Measure.pi fun _ : Fin n => mu.prod eta) :=
      (hconditional.const_mul 2).add (hinvint.const_mul 2)
    have hue_mono : ∀ F H : (Fin m → G) → ℝ, (∀ S, F S ≤ H S) →
        uniform_group_expectation m F ≤ uniform_group_expectation m H := by
      intro F H hFH
      unfold uniform_group_expectation
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S _ => hFH S) (by positivity)
    have hue_add : ∀ F H : (Fin m → G) → ℝ,
        uniform_group_expectation m (fun S => F S + H S) =
          uniform_group_expectation m F + uniform_group_expectation m H := by
      intro F H
      simp [uniform_group_expectation, Finset.sum_add_distrib]
      ring
    have hue_mul : ∀ (a : ℝ) (F : (Fin m → G) → ℝ),
        uniform_group_expectation m (fun S => a * F S) =
          a * uniform_group_expectation m F := by
      intro a F
      simp [uniform_group_expectation, Finset.mul_sum]
      ring_nf
    have hue_const : ∀ a : ℝ,
        uniform_group_expectation m (fun _ : Fin m → G => a) = a := by
      intro a
      simp [uniform_group_expectation]
    have hue_doubling : ∀ (F : (Fin m → G) → ℝ) (a : ℝ),
        uniform_group_expectation m (fun S => 2 * F S + 2 * a)
          = 2 * uniform_group_expectation m F + 2 * a := by
      intro F a
      rw [hue_add, hue_mul, hue_const]
    have hpoint : ∀ zs : Fin n → X × ℝ,
        uniform_group_expectation m (fun S : Fin m → G =>
          ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
            - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
        ≤ 2 * uniform_group_expectation m (fun S : Fin m → G =>
            ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2)
          + 2 * ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2 := by
      intro zs
      calc
        _ ≤ uniform_group_expectation m (fun S : Fin m → G =>
            2 * ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2
            + 2 * ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2) := by
          refine hue_mono _ _ fun S => ?_
          rw [show empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (target_coeff mu phi fstar) =
            (empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (regression_coeff_estimator phi fstar zs))
            + (group_average_operator rho (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (target_coeff mu phi fstar)) by abel]
          exact norm_add_sq_doubling _ _
        _ = _ := hue_doubling _ _
    have htotal0 : iid_expectation (mu.prod eta) n (fun zs => uniform_group_expectation m
        (fun S : Fin m → G =>
          ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
            - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2))
        ≤ 2 * iid_expectation (mu.prod eta) n (fun zs => uniform_group_expectation m
            (fun S : Fin m → G =>
              ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
                - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2))
          + 2 * iid_expectation (mu.prod eta) n (fun zs =>
            ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2) := by
      unfold iid_expectation
      calc
        _ ≤ ∫ zs, (2 * uniform_group_expectation m (fun S : Fin m → G =>
              ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
                - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2)
            + 2 * ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
                - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
            ∂(Measure.pi fun _ : Fin n => mu.prod eta) :=
          integral_mono hriskint hupperint hpoint
        _ = _ := by
          rw [integral_add (hconditional.const_mul 2) (hinvint.const_mul 2),
            integral_const_mul, integral_const_mul]
    have hbase : iid_expectation (mu.prod eta) n (fun zs =>
        ‖regression_coeff_estimator phi fstar zs - target_coeff mu phi fstar‖ ^ 2)
        ≤ ((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * r / n :=
      baseline_regression_excess mu phi hphi hmem fstar hfmem hfinf eta sigma heta n hn
    have hinvbase : iid_expectation (mu.prod eta) n (fun zs =>
        ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
          - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2)
        ≤ ((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2)
            * (Module.finrank ℝ rho.invariants) / n :=
      invariant_baseline_regression_excess mu phi rho hrho hphi hmem fstar hfmem hfinf eta sigma
        heta n hn
    have haugmentation := general_augmentation_error_bound (mu.prod eta) rho hrho n m hm
      (regression_coeff_estimator phi fstar) (target_coeff mu phi fstar)
      (hdist (target_coeff mu phi fstar))
      (hdist (invariant_projection rho (target_coeff mu phi fstar))) hconditional
    have hA : iid_expectation (mu.prod eta) n (fun zs => uniform_group_expectation m
        (fun S : Fin m → G =>
          ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
            - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2))
        ≤ 2 * (m : ℝ)⁻¹ * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * r / n
          + ‖target_coeff mu phi fstar
              - invariant_projection rho (target_coeff mu phi fstar)‖ ^ 2) := by
      refine haugmentation.trans ?_
      have hmnn : (0 : ℝ) ≤ 2 * (m : ℝ)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) hmnn
    have hcombine : 2 * (2 * (m : ℝ)⁻¹ * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * r / n
          + ‖target_coeff mu phi fstar
              - invariant_projection rho (target_coeff mu phi fstar)‖ ^ 2))
        + 2 * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2)
            * (Module.finrank ℝ rho.invariants) / n)
        ≤ 4 * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2)
              * (Module.finrank ℝ rho.invariants) / n
            + ((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * (r : ℝ)
                / ((n : ℝ) * (m : ℝ))
            + ‖target_coeff mu phi fstar
                  - invariant_projection rho (target_coeff mu phi fstar)‖ ^ 2 / m) := by
      have hrw : 2 * (2 * (m : ℝ)⁻¹ * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * r / n
            + ‖target_coeff mu phi fstar
                - invariant_projection rho (target_coeff mu phi fstar)‖ ^ 2))
          = 4 * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * (r : ℝ)
                / ((n : ℝ) * (m : ℝ)))
            + 4 * (‖target_coeff mu phi fstar
                - invariant_projection rho (target_coeff mu phi fstar)‖ ^ 2 / m) := by
        field_simp
        ring
      rw [hrw]
      linarith
    calc
      _ ≤ 2 * iid_expectation (mu.prod eta) n (fun zs => uniform_group_expectation m
            (fun S : Fin m → G =>
              ‖empirical_average_operator rho S (regression_coeff_estimator phi fstar zs)
                - group_average_operator rho (regression_coeff_estimator phi fstar zs)‖ ^ 2))
          + 2 * iid_expectation (mu.prod eta) n (fun zs =>
            ‖group_average_operator rho (regression_coeff_estimator phi fstar zs)
              - group_average_operator rho (target_coeff mu phi fstar)‖ ^ 2) := htotal0
      _ ≤ 2 * (2 * (m : ℝ)⁻¹ * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2) * r / n
            + ‖target_coeff mu phi fstar
                - invariant_projection rho (target_coeff mu phi fstar)‖ ^ 2))
          + 2 * (((eLpNormEssSup fstar mu).toReal ^ 2 + sigma ^ 2)
              * (Module.finrank ℝ rho.invariants) / n) := by
        linarith
      _ ≤ _ := hcombine
  ·
    rw [iid_expectation, integral_undef hriskint]
    positivity

@[blueprint "def:partial-augmentation-density-lower-bound"
  (statement := /-- Let $c\in\mathbb R$. We say that $c$ is an \emph{attainable density-estimation
  lower-bound constant} if the following holds for every choice of the rate parameters
  $r,r_{\mathrm{inv}},n,m\in\mathbb N$ subject to $0<r_{\mathrm{inv}}$, $r_{\mathrm{inv}}\le r$,
  $0<n$ and $0<m$. There exist a probability space $(\mathcal X,\mu)$; a finite group $G$ acting on
  $\mathcal X$ such that for each $g\in G$ the map $x\mapsto g\cdot x$ preserves $\mu$; a family
  $\varphi=(\varphi_\ell)_{\ell\in[r]}$ which is $L^2(\mathcal X,\mu)$-orthonormal in the sense of
  \cref{def:l2-orthonormal-family} with each $\varphi_\ell\in L^2(\mathcal X,\mu)$, so that the
  space $\mathcal F=\operatorname{span}\varphi$ has dimension exactly $r$; a representation
  $\rho:G\to\mathrm{GL}(\mathbb R^r)$ implementing the lifted action in the sense of
  \cref{def:implements-lifted-action} and whose invariant subspace has dimension exactly
  $\dim(\mathbb R^r)^G=r_{\mathrm{inv}}$; and a function $f^\star:\mathcal X\to\mathbb R$ with
  $f^\star\ge0$ $\mu$-almost everywhere, $f^\star\in L^2(\mathcal X,\mu)$,
  $\|f^\star\|_\infty<\infty$, with $f^\star\,d\mu$ a probability measure and with the coefficient
  vector $\theta(f^\star)$ of \cref{def:target-coeff} $G$-invariant, such that the partially
  augmented projection density estimator $\widehat f_S$ of
  \cref{def:augmented-density-coeff-estimator}, built from $n$ i.i.d. samples from $f^\star d\mu$
  and an i.i.d. uniform augmentation set $S=(g_1,\dots,g_m)$ of size $m$, satisfies the lower bound
  \[
    \mathbb E\bigl[\|\widehat f_S-\Pi_{\mathcal F^G}f^\star\|_{L^2(\mathcal X)}^2\bigr]
    \;\ge\;c\left(\frac{\|f^\star\|_\infty}{n}\,r_{\mathrm{inv}}+\frac{r}{nm}\right).
  \]
  Here the expectation is over both the base sample and the augmentation set, the squared
  $L^2(\mathcal X)$ error is that of \cref{def:l2-sq-dist}, and $\Pi_{\mathcal F^G}f^\star$ is
  represented by $\Pi_{\mathcal F^G}\theta(f^\star)$ with $\Pi_{\mathcal F^G}$ as in
  \cref{def:invariant-projection}. Thus the constant $c$ is chosen once and for all, before the
  rate parameters, and the configuration realizing the lower bound is allowed to depend on
  $(r,r_{\mathrm{inv}},n,m)$. -/)
  (title := /-- Attainable constant for the density-estimation lower bound -/)
  (latexEnv := "definition")]
def partial_augmentation_density_lower_bound (c : ℝ) : Prop :=
  ∀ r rinv n m : ℕ, 0 < rinv → rinv ≤ r → 0 < n → 0 < m →
    ∃ (X : Type) (_ : MeasurableSpace X) (G : Type) (_ : Group G) (_ : Fintype G)
      (_ : MulAction G X) (mu : Measure X) (phi : Fin r → X → ℝ)
      (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) (fstar : X → ℝ),
      IsProbabilityMeasure mu ∧
      (∀ g : G, MeasurePreserving (fun x : X => g • x) mu mu) ∧
      l2_orthonormal_family mu phi ∧
      (∀ l, MemLp (phi l) 2 mu) ∧
      implements_lifted_action phi rho ∧
      Module.finrank ℝ rho.invariants = rinv ∧
      (∀ᵐ x ∂mu, 0 ≤ fstar x) ∧
      MemLp fstar 2 mu ∧
      eLpNormEssSup fstar mu ≠ ∞ ∧
      IsProbabilityMeasure (mu.withDensity fun x => ENNReal.ofReal (fstar x)) ∧
      target_coeff mu phi fstar ∈ rho.invariants ∧
      c * ((eLpNormEssSup fstar mu).toReal * (rinv : ℝ) / n + (r : ℝ) / ((n : ℝ) * (m : ℝ)))
        ≤ iid_expectation (mu.withDensity fun x => ENNReal.ofReal (fstar x)) n
            (fun xs => uniform_group_expectation m (fun S : Fin m → G =>
              l2_sq_dist mu phi (augmented_density_coeff_estimator phi S xs)
                (invariant_projection rho (target_coeff mu phi fstar))))

@[blueprint "def:partial-augmentation-tightness-sample"
  (statement := /-- For $r\in\mathbb N$, a sample point consists of an index in $[r]$ and a
  Rademacher sign encoded by a Boolean value. -/)
  (title := /-- Finite Rademacher sample space for the tightness construction -/)
  (latexEnv := "definition")]
structure partial_augmentation_tightness_sample (r : ℕ) where
  index : Fin r
  sign : Bool
  deriving Fintype, DecidableEq

@[blueprint "def:partial-augmentation-tightness-action"
  (statement := /-- The two-element group $\mathbb Z^\times=\{1,-1\}$ acts on the finite
  Rademacher sample space by fixing coordinates below $r_{\mathrm{inv}}$ and flipping the Boolean
  sign at all remaining coordinates when the acting element is $-1$. -/)
  (title := /-- Sign-flip action for the tightness construction -/)
  (latexEnv := "definition")]
abbrev partial_augmentation_tightness_action (r rinv : ℕ) :
    MulAction ℤˣ (partial_augmentation_tightness_sample r) :=
  MulAction.ofEndHom {
    toFun := fun g x => if x.index.val < rinv ∨ g = 1 then x else ⟨x.index, !x.sign⟩
    map_one' := by
      funext x
      simp [Function.End.one_def]
    map_mul' := by
      intro g h
      funext x
      rcases Int.units_eq_one_or g with rfl | rfl <;>
        rcases Int.units_eq_one_or h with rfl | rfl <;>
        by_cases hx : x.index.val < rinv <;>
        simp [hx, Bool.not_not, Function.End.mul_def, Function.comp_apply] }

@[blueprint "def:partial-augmentation-tightness-representation"
  (statement := /-- On $\mathbb R^r$, the element $-1\in\mathbb Z^\times$ fixes coordinates below
  $r_{\mathrm{inv}}$ and negates all remaining coordinates, while $1$ acts identically. This
  defines the diagonal representation used in the finite tightness construction. -/)
  (title := /-- Diagonal sign representation for the tightness construction -/)
  (latexEnv := "definition")]
noncomputable def partial_augmentation_tightness_representation (r rinv : ℕ) :
    Representation ℝ ℤˣ (EuclideanSpace ℝ (Fin r)) where
  toFun g := {
    toFun := fun c => WithLp.toLp 2 fun l =>
      if l.val < rinv then c l else ((g : ℤ) : ℝ) * c l
    map_add' := by
      intro c d
      ext l
      by_cases hl : l.val < rinv <;> simp [hl, mul_add]
    map_smul' := by
      intro a c
      ext l
      by_cases hl : l.val < rinv
      · simp [hl]
      · simp [hl]
        ring }
  map_one' := by
    ext c l
    by_cases hl : l.val < rinv <;> simp [hl]
  map_mul' g h := by
    ext c l
    by_cases hl : l.val < rinv <;> simp [hl, mul_assoc]

@[blueprint "lem:partial-augmentation-tightness-invariants-finrank"
  (statement := /-- If $r_{\mathrm{inv}}\le r$, then the invariant subspace of the diagonal sign
  representation of \cref{def:partial-augmentation-tightness-representation} has dimension exactly
  $r_{\mathrm{inv}}$. -/)
  (proof := /-- Restriction to the first $r_{\mathrm{inv}}$ coordinates defines a linear
  equivalence from the invariant subspace to $\mathbb R^{r_{\mathrm{inv}}}$. Its inverse extends a
  vector by zero on all remaining coordinates. The extension is invariant because the
  representation fixes the first block and only changes signs in the zero block. Conversely, an
  invariant vector has every coordinate in the second block equal to its own negative under the
  element $-1$, and therefore those coordinates vanish. The equivalence preserves dimension, and
  $\mathbb R^{r_{\mathrm{inv}}}$ has dimension $r_{\mathrm{inv}}$. -/)
  (title := /-- Dimension of the invariant block in the sign representation -/)
  (latexEnv := "lemma")]
lemma partial_augmentation_tightness_invariants_finrank (r rinv : ℕ) (hle : rinv ≤ r) :
    Module.finrank ℝ
      (partial_augmentation_tightness_representation r rinv).invariants = rinv := by
  let rho := partial_augmentation_tightness_representation r rinv
  let e : rho.invariants ≃ₗ[ℝ] EuclideanSpace ℝ (Fin rinv) := {
    toFun := fun v => WithLp.toLp 2 fun j => v.1 ⟨j.val, lt_of_lt_of_le j.isLt hle⟩
    invFun := fun w => ⟨WithLp.toLp 2 fun l =>
      if hl : l.val < rinv then w ⟨l.val, hl⟩ else 0, by
        rw [Representation.mem_invariants]
        intro g
        ext l
        by_cases hl : l.val < rinv <;>
          simp [rho, partial_augmentation_tightness_representation, hl]⟩
    left_inv := by
      intro v
      apply Subtype.ext
      ext l
      by_cases hl : l.val < rinv
      · simp [hl]
      · have hv := (Representation.mem_invariants (ρ := rho) v.1).1 v.2 (-1)
        have hv' := congrArg (fun c => c l) hv
        simp [rho, partial_augmentation_tightness_representation, hl] at hv'
        have hz : v.1 l = 0 := by linarith [hv']
        simp [hl, hz]
    right_inv := by
      intro w
      ext j
      simp [j.isLt]
    map_add' := by
      intro v w
      ext j
      simp
    map_smul' := by
      intro a v
      ext j
      simp }
  calc
    Module.finrank ℝ rho.invariants = Module.finrank ℝ (EuclideanSpace ℝ (Fin rinv)) :=
      LinearEquiv.finrank_eq e
    _ = rinv := by simp

@[blueprint "lem:iid-mean-square-centered-exact-for-tightness"
  (statement := /-- Let $\nu$ be a probability measure, let $n>0$, and let
  $\psi\in L^2(\nu)$ have mean zero. Then the empirical mean of $n$ independent samples has exact
  second moment equal to the second moment of $\psi$ divided by $n$. -/)
  (proof := /-- Expand the square of the empirical sum into its double sum. For distinct sample
  indices the integral vanishes by \cref{lem:integral-pi-cross-term}, since the mean of $\psi$ is
  zero. For equal indices, \cref{lem:integral-pi-eval} identifies the product-space integral with
  the second moment of $\psi$. Thus precisely the $n$ diagonal terms remain, and division by
  $n^2$ gives the claimed factor $1/n$. -/)
  (title := /-- Exact second moment of a centered empirical mean -/)
  (latexEnv := "lemma")]
lemma iid_mean_square_centered_exact_for_tightness {Y : Type*} [MeasurableSpace Y]
    (nu : Measure Y) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n) (psi : Y → ℝ)
    (hpsi : MemLp psi 2 nu) (hmean : ∫ y, psi y ∂nu = 0) :
    iid_expectation nu n (fun ys => ((n : ℝ)⁻¹ * ∑ i, psi (ys i)) ^ 2) =
      (n : ℝ)⁻¹ * ∫ y, psi y ^ 2 ∂nu := by
  have hM : ∀ i : Fin n, MemLp (fun ys : Fin n → Y => psi (ys i)) 2
      (Measure.pi fun _ : Fin n => nu) := fun i =>
    hpsi.comp_measurePreserving (measurePreserving_eval _ i)
  have hInt : ∀ i j : Fin n, Integrable
      (fun ys : Fin n → Y => psi (ys i) * psi (ys j))
      (Measure.pi fun _ : Fin n => nu) := fun i j => (hM i).integrable_mul (hM j)
  have hpoint : ∀ ys : Fin n → Y, ((n : ℝ)⁻¹ * ∑ i, psi (ys i)) ^ 2 =
      (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i, ∑ j, psi (ys i) * psi (ys j) := by
    intro ys
    rw [← Finset.sum_mul_sum]
    ring
  have hexpand : iid_expectation nu n (fun ys => ((n : ℝ)⁻¹ * ∑ i, psi (ys i)) ^ 2) =
      (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i, ∑ j,
        ∫ ys, psi (ys i) * psi (ys j) ∂(Measure.pi fun _ : Fin n => nu) := by
    rw [iid_expectation, integral_congr_ae (Filter.Eventually.of_forall hpoint),
      integral_const_mul, integral_finset_sum _ fun i _ =>
        integrable_finset_sum _ fun j _ => hInt i j]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    exact integral_finset_sum _ fun j _ => hInt i j
  have hrow : ∀ i : Fin n, ∑ j,
      ∫ ys, psi (ys i) * psi (ys j) ∂(Measure.pi fun _ : Fin n => nu) =
        ∫ y, psi y ^ 2 ∂nu := by
    intro i
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hij => by
      simpa [hmean] using integral_pi_cross_term nu (Ne.symm hij) psi
        (hpsi.integrable one_le_two)]
    simpa [sq] using integral_pi_eval nu i (fun y => psi y ^ 2) hpsi.integrable_sq.1
  rw [hexpand, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hrow i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

@[blueprint "thm:partial-augmentation-excess-tight"
  (statement := /-- There exists an absolute constant $c>0$ which is an attainable
  density-estimation lower-bound constant in the sense of
  \cref{def:partial-augmentation-density-lower-bound}. Explicitly, $c$ is fixed once and for all,
  and for every choice of the rate parameters $r,r_{\mathrm{inv}},n,|S|\in\mathbb N$ with
  $0<r_{\mathrm{inv}}\le r$, $n>0$ and $|S|>0$ there is a configuration
  $(\mathcal X,\mu,G,\varphi,\rho,f^\star)$ satisfying every hypothesis of
  \cref{def:partial-augmentation-density-bound}, whose subspace
  $\mathcal F=\operatorname{span}\varphi$ has dimension $r$ and whose invariant subspace
  $\mathcal F^G$ has dimension $r_{\mathrm{inv}}$, for which
  \[
    \mathbb E\bigl[\|\widehat f_S-\Pi_{\mathcal F^G}f^\star\|_{L^2(\mathcal X)}^2\bigr]
    \;\ge\;c\left(\frac{\|f^\star\|_\infty}{n}\,r_{\mathrm{inv}}+\frac{r}{n|S|}\right).
  \]
  Thus the same positive constant $c$ works for every admissible choice of the four rate
  parameters, although the realizing configuration may depend on those parameters. -/)
  (proof := /-- Take $c=1/2$. Fix integers $0<r_{\mathrm{inv}}\le r$ and $n,m>0$. Let
  $\mathcal X$ be the finite Rademacher space of
  \cref{def:partial-augmentation-tightness-sample}, equipped with the uniform probability measure,
  and let $G=\mathbb Z^\times=\{1,-1\}$. For $\ell\in[r]$, define $\varphi_\ell$ to be
  $\sqrt r$ times the signed indicator of the two points having index $\ell$. Each
  $\varphi_\ell$ has mean zero and second moment one, and distinct coordinates have disjoint
  support. Hence the family is orthonormal and belongs to $L^2(\mu)$.

  Use the action of \cref{def:partial-augmentation-tightness-action}: the element $-1$ fixes the
  signs at indices below $r_{\mathrm{inv}}$ and flips all other signs. This action permutes the
  finite sample space and therefore preserves the uniform measure. The diagonal representation
  of \cref{def:partial-augmentation-tightness-representation} implements the lifted action on the
  span of the functions $\varphi_\ell$. Its invariant subspace has dimension
  $r_{\mathrm{inv}}$ by
  \cref{lem:partial-augmentation-tightness-invariants-finrank}. Take $f^\star\equiv1$. Then
  $f^\star d\mu=\mu$, $\|f^\star\|_\infty=1$, and all the required positivity, $L^2$, and
  finiteness conditions hold. Since every $\varphi_\ell$ is centered, the target coefficient
  vector is zero, and is consequently invariant.

  Write $\widehat\theta$ for the unaugmented empirical coefficient vector. By
  \cref{lem:representation-orthogonal-of-measure-preserving} the diagonal representation is
  orthogonal, and by
  \cref{lem:augmented-density-estimator-eq-empirical-average} the augmented coefficient vector is
  $\Pi_S\widehat\theta$. The full group average $\Pi_G$ retains precisely the first
  $r_{\mathrm{inv}}$ coordinates and annihilates the remaining coordinates. These two coordinate
  blocks are orthogonal. Thus \cref{lem:random-averaging-variance}, together with the Pythagorean
  identity for the two blocks, gives conditionally on the data
  \[
    \mathbb E_S\|\Pi_S\widehat\theta\|^2
      =\frac1m\|\widehat\theta-\Pi_G\widehat\theta\|^2
       +\|\Pi_G\widehat\theta\|^2.
  \]

  For every coordinate, \cref{lem:iid-mean-square-centered-exact-for-tightness} gives
  $\mathbb E[\widehat\theta_\ell^2]=1/n$. Summing these identities by
  \cref{lem:iid-expectation-norm-sq-sum} yields
  $\mathbb E\|\widehat\theta\|^2=r/n$; summing only over the invariant block yields
  $\mathbb E\|\Pi_G\widehat\theta\|^2=r_{\mathrm{inv}}/n$. Consequently the preceding conditional
  identity gives the exact risk
  \[
    \mathbb E_{x,S}\|\Pi_S\widehat\theta\|^2
      =\frac{r_{\mathrm{inv}}}{n}+\frac{r-r_{\mathrm{inv}}}{nm}.
  \]
  By \cref{lem:parseval-coeff-norm}, this is exactly the squared $L^2(\mu)$ risk appearing in the
  assertion. Finally, $r\ge r_{\mathrm{inv}}$ and $m\ge1$ imply
  \[
    \frac{r_{\mathrm{inv}}}{n}+\frac{r-r_{\mathrm{inv}}}{nm}
      \ge \frac12\left(\frac{r_{\mathrm{inv}}}{n}+\frac r{nm}\right),
  \]
  which proves the claim with the same constant $c=1/2$ for every admissible choice of the four
  parameters. -/)
  (title := /-- Tightness of the partial-augmentation bound -/)
  (latexEnv := "theorem")]
theorem partial_augmentation_excess_tight :
    ∃ c : ℝ, 0 < c ∧ partial_augmentation_density_lower_bound c := by
  classical
  refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
  intro r rinv n m hrinv hle hn hm
  have hr : 0 < r := lt_of_lt_of_le hrinv hle
  let X := partial_augmentation_tightness_sample r
  letI : Nonempty X := ⟨⟨⟨0, hr⟩, false⟩⟩
  letI : MeasurableSpace X := ⊤
  letI : MulAction ℤˣ X := partial_augmentation_tightness_action r rinv
  let mu : Measure X := (Fintype.card X : ℝ≥0∞)⁻¹ • Measure.count
  let phi : Fin r → X → ℝ := fun l x =>
    if l = x.index then Real.sqrt r * (if x.sign then -1 else 1) else 0
  let rho := partial_augmentation_tightness_representation r rinv
  let fstar : X → ℝ := fun _ => 1
  let e : X ≃ Fin r × Bool := {
    toFun := fun x => (x.index, x.sign)
    invFun := fun p => ⟨p.1, p.2⟩
    left_inv := by intro x; cases x; rfl
    right_inv := by intro p; cases p; rfl }
  have hmean : ∀ l, ∫ x, phi l x ∂mu = 0 := by
    intro l
    simp only [mu, MeasureTheory.integral_smul_measure, MeasureTheory.integral_count]
    rw [Fintype.sum_equiv e (phi l)
      (fun p : Fin r × Bool =>
        if l = p.1 then Real.sqrt r * (if p.2 then -1 else 1) else 0)
      (by intro x; rfl)]
    simp only [Fintype.sum_prod_type]
    simp
  have hcard : Fintype.card X = 2 * r := by
    rw [Fintype.card_congr e]
    simp [mul_comm]
  have hsq : ∀ l, ∫ x, (phi l x) ^ 2 ∂mu = 1 := by
    intro l
    simp only [mu, MeasureTheory.integral_smul_measure, MeasureTheory.integral_count]
    rw [Fintype.sum_equiv e (fun x => (phi l x) ^ 2)
      (fun p : Fin r × Bool =>
        (if l = p.1 then Real.sqrt r * (if p.2 then -1 else 1) else 0) ^ 2)
      (by intro x; rfl)]
    simp only [Fintype.sum_prod_type]
    simp [hcard, Real.sq_sqrt (Nat.cast_nonneg r)]
    field_simp [Nat.cast_ne_zero.mpr hr.ne']
  have hprob : IsProbabilityMeasure mu := by
    rw [isProbabilityMeasure_iff]
    simp [mu, hcard, Nat.cast_ne_zero.mpr hr.ne']
    apply ENNReal.inv_mul_cancel
    · positivity
    · exact ENNReal.mul_ne_top (by simp) (by simp)
  have hmp : ∀ g : ℤˣ, MeasurePreserving (fun x : X => g • x) mu mu := by
    intro g
    refine ⟨by fun_prop, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (by fun_prop) hs]
    simp [mu, Measure.count_apply,
      Set.encard_preimage_of_bijective (MulAction.bijective g)]
  have horth : l2_orthonormal_family mu phi := by
    intro l l'
    by_cases hll : l = l'
    · subst l'
      simpa [pow_two] using hsq l
    · rw [if_neg hll]
      have hz : (fun x => phi l x * phi l' x) = fun _ => 0 := by
        funext x
        by_cases hl : l = x.index
        · have hl' : l' ≠ x.index := fun heq => hll (hl.trans heq.symm)
          simp [phi, hl, hl']
        · simp [phi, hl]
      rw [hz]
      simp
  letI : IsProbabilityMeasure mu := hprob
  have hmem : ∀ l, MemLp (phi l) 2 mu := by
    intro l
    apply memLp_of_bounded (a := -Real.sqrt r) (b := Real.sqrt r)
    · filter_upwards with x
      rcases x with ⟨i, b⟩
      by_cases hi : l = i <;> cases b <;> simp [phi, hi, Real.sqrt_nonneg]
    · fun_prop
  have hsmul (g : ℤˣ) (x : X) :
      g • x = if x.index.val < rinv ∨ g = 1 then x else ⟨x.index, !x.sign⟩ := by
    change (partial_augmentation_tightness_action r rinv).smul g x = _
    rfl
  have himpl : implements_lifted_action phi rho := by
    intro g c x
    rcases Int.units_eq_one_or g with rfl | rfl
    · simp [coeff_to_fun, phi, rho, partial_augmentation_tightness_representation,
        partial_augmentation_tightness_action, hsmul]
    · rcases x with ⟨i, b⟩
      by_cases hi : i.val < rinv <;> cases b <;>
        simp [coeff_to_fun, phi, rho, partial_augmentation_tightness_representation,
          partial_augmentation_tightness_action, hsmul, hi]
  have hfinrank : Module.finrank ℝ rho.invariants = rinv := by
    simpa [rho] using partial_augmentation_tightness_invariants_finrank r rinv hle
  have hf0 : ∀ᵐ x ∂mu, 0 ≤ fstar x := Filter.Eventually.of_forall fun _ => by simp [fstar]
  have hfmem : MemLp fstar 2 mu := by simp [fstar]
  have hfinf : eLpNormEssSup fstar mu ≠ ∞ := by
    rw [show fstar = (fun _ : X => (1 : ℝ)) from rfl,
      eLpNormEssSup_const (1 : ℝ) hprob.ne_zero]
    simp
  have hdensity : mu.withDensity (fun x => ENNReal.ofReal (fstar x)) = mu := by
    simp [fstar]
  have hdprob : IsProbabilityMeasure
      (mu.withDensity fun x => ENNReal.ofReal (fstar x)) := by
    rw [hdensity]
    exact hprob
  have hess : (eLpNormEssSup fstar mu).toReal = 1 := by
    rw [show fstar = (fun _ : X => (1 : ℝ)) from rfl,
      eLpNormEssSup_const (1 : ℝ) hprob.ne_zero]
    simp
  have hcoeff : target_coeff mu phi fstar = 0 := by
    ext l
    simp [target_coeff, fstar, hmean l]
  have hinv : target_coeff mu phi fstar ∈ rho.invariants := by
    rw [hcoeff]
    exact rho.invariants.zero_mem
  have hproj : invariant_projection rho (target_coeff mu phi fstar) = 0 := by
    rw [hcoeff]
    exact map_zero _
  have hrho : orthogonal_representation rho :=
    representation_orthogonal_of_measure_preserving mu phi rho hmp horth hmem himpl
  have hgroup (c : EuclideanSpace ℝ (Fin r)) (l : Fin r) :
      group_average_operator rho c l = if l.val < rinv then c l else 0 := by
    by_cases hl : l.val < rinv <;>
      simp [group_average_operator, rho, partial_augmentation_tightness_representation, hl] <;>
      ring
  have hpyth (S : Fin m → ℤˣ) (c : EuclideanSpace ℝ (Fin r)) :
      ‖empirical_average_operator rho S c‖ ^ 2 =
        ‖empirical_average_operator rho S c - group_average_operator rho c‖ ^ 2 +
          ‖group_average_operator rho c‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [PiLp.sub_apply, hgroup c l]
    by_cases hl : l.val < rinv <;>
      simp [empirical_average_operator, rho, partial_augmentation_tightness_representation, hl,
        Nat.cast_ne_zero.mpr hm.ne'] <;>
      ring
  have hconst (F : (Fin m → ℤˣ) → ℝ) (a : ℝ) :
      uniform_group_expectation m (fun S => F S + a) =
        uniform_group_expectation m F + a := by
    simp [uniform_group_expectation, Finset.sum_add_distrib]
    field_simp
  have hconditional (c : EuclideanSpace ℝ (Fin r)) :
      uniform_group_expectation m (fun S => ‖empirical_average_operator rho S c‖ ^ 2) =
        (m : ℝ)⁻¹ * ‖c - group_average_operator rho c‖ ^ 2 +
          ‖group_average_operator rho c‖ ^ 2 := by
    rw [show (fun S : Fin m → ℤˣ => ‖empirical_average_operator rho S c‖ ^ 2) =
        (fun S => ‖empirical_average_operator rho S c - group_average_operator rho c‖ ^ 2 +
          ‖group_average_operator rho c‖ ^ 2) from funext fun S => hpyth S c,
      hconst, random_averaging_variance rho hrho m hm c]
  have hchatmem (l : Fin r) : MemLp
      (fun xs : Fin n → X => density_coeff_estimator phi xs l) 2
      (Measure.pi fun _ : Fin n => mu) := by
    have hcoords : ∀ i : Fin n, MemLp (fun xs : Fin n → X => phi l (xs i)) 2
        (Measure.pi fun _ : Fin n => mu) := fun i =>
      (hmem l).comp_measurePreserving (measurePreserving_eval _ i)
    simpa [density_coeff_estimator] using
      (memLp_finsetSum Finset.univ fun i _ => hcoords i).const_mul (n : ℝ)⁻¹
  have hcoord (l : Fin r) :
      iid_expectation mu n (fun xs => (density_coeff_estimator phi xs l) ^ 2) =
        (n : ℝ)⁻¹ := by
    simpa [density_coeff_estimator, hsq l] using
      iid_mean_square_centered_exact_for_tightness mu n hn (phi l) (hmem l) (hmean l)
  have hbase : iid_expectation mu n
      (fun xs => ‖density_coeff_estimator phi xs‖ ^ 2) = (r : ℝ) / n := by
    calc
      iid_expectation mu n (fun xs => ‖density_coeff_estimator phi xs‖ ^ 2) =
          ∑ l, iid_expectation mu n
            (fun xs => (density_coeff_estimator phi xs l) ^ 2) := by
        simpa [density_coeff_estimator] using
          iid_expectation_norm_sq_sum mu phi hmem n (0 : EuclideanSpace ℝ (Fin r))
      _ = ∑ _l : Fin r, (n : ℝ)⁻¹ := Finset.sum_congr rfl fun l _ => hcoord l
      _ = (r : ℝ) / n := by simp [div_eq_mul_inv]
  have hgroupnorm (c : EuclideanSpace ℝ (Fin r)) :
      ‖group_average_operator rho c‖ ^ 2 =
        ∑ l, if l.val < rinv then (c l) ^ 2 else 0 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hgroup]
    by_cases hl : l.val < rinv <;> simp [hl]
  have hdiffnorm (c : EuclideanSpace ℝ (Fin r)) :
      ‖c - group_average_operator rho c‖ ^ 2 =
        ∑ l, if l.val < rinv then 0 else (c l) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [PiLp.sub_apply, hgroup c l]
    by_cases hl : l.val < rinv <;> simp [hl]
  have hprojected : iid_expectation mu n (fun xs =>
      ‖group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2) =
        (rinv : ℝ) / n := by
    rw [show (fun xs => ‖group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2) =
        (fun xs => ∑ l, if l.val < rinv then (density_coeff_estimator phi xs l) ^ 2 else 0)
      from funext fun xs => hgroupnorm (density_coeff_estimator phi xs)]
    unfold iid_expectation
    rw [integral_finset_sum _ fun l _ => by
      by_cases hl : l.val < rinv
      · simpa [hl] using (hchatmem l).integrable_sq
      · simp [hl]]
    calc
      (∑ l : Fin r, ∫ xs, (if l.val < rinv then
          (density_coeff_estimator phi xs l) ^ 2 else 0) ∂(Measure.pi fun _ : Fin n => mu)) =
          ∑ l : Fin r, if l.val < rinv then (n : ℝ)⁻¹ else 0 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases hl : l.val < rinv
        · simp only [hl, if_true]
          exact hcoord l
        · simp [hl]
      _ = (rinv : ℝ) / n := by
        rw [← Finset.sum_filter]
        simp [Fin.card_filter_val_lt, Nat.min_eq_right hle, div_eq_mul_inv]
  have hdecomp (c : EuclideanSpace ℝ (Fin r)) :
      ‖c‖ ^ 2 = ‖c - group_average_operator rho c‖ ^ 2 +
        ‖group_average_operator rho c‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, hdiffnorm, hgroupnorm,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l.val < rinv <;> simp [hl]
  have hbaseint : Integrable (fun xs : Fin n → X =>
      ‖density_coeff_estimator phi xs‖ ^ 2) (Measure.pi fun _ : Fin n => mu) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    exact integrable_finset_sum _ fun l _ => (hchatmem l).integrable_sq
  have hprojectedint : Integrable (fun xs : Fin n → X =>
      ‖group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2)
      (Measure.pi fun _ : Fin n => mu) := by
    simp_rw [hgroupnorm]
    exact integrable_finset_sum _ fun l _ => by
      by_cases hl : l.val < rinv
      · simpa [hl] using (hchatmem l).integrable_sq
      · simp [hl]
  have hdifference : iid_expectation mu n (fun xs =>
      ‖density_coeff_estimator phi xs -
        group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2) =
          ((r : ℝ) - rinv) / n := by
    rw [show (fun xs => ‖density_coeff_estimator phi xs -
          group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2) =
        (fun xs => ‖density_coeff_estimator phi xs‖ ^ 2 -
          ‖group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2)
      from funext fun xs => by linarith [hdecomp (density_coeff_estimator phi xs)]]
    unfold iid_expectation
    rw [integral_sub hbaseint hprojectedint]
    change iid_expectation mu n (fun xs => ‖density_coeff_estimator phi xs‖ ^ 2) -
      iid_expectation mu n
        (fun xs => ‖group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2) = _
    rw [hbase, hprojected]
    ring
  have hdifferenceint : Integrable (fun xs : Fin n → X =>
      ‖density_coeff_estimator phi xs -
        group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2)
      (Measure.pi fun _ : Fin n => mu) := by
    simp_rw [hdiffnorm]
    exact integrable_finset_sum _ fun l _ => by
      by_cases hl : l.val < rinv
      · simp [hl]
      · simpa [hl] using (hchatmem l).integrable_sq
  have hrisk : iid_expectation mu n (fun xs => uniform_group_expectation m
      (fun S : Fin m → ℤˣ => l2_sq_dist mu phi
        (augmented_density_coeff_estimator phi S xs)
        (invariant_projection rho (target_coeff mu phi fstar)))) =
      (m : ℝ)⁻¹ * (((r : ℝ) - rinv) / n) + (rinv : ℝ) / n := by
    rw [show (fun xs => uniform_group_expectation m
          (fun S : Fin m → ℤˣ => l2_sq_dist mu phi
            (augmented_density_coeff_estimator phi S xs)
            (invariant_projection rho (target_coeff mu phi fstar)))) =
        (fun xs => (m : ℝ)⁻¹ * ‖density_coeff_estimator phi xs -
            group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2 +
          ‖group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2)
      from funext fun xs => by
        rw [← hconditional (density_coeff_estimator phi xs)]
        congr 1
        funext S
        rw [augmented_density_estimator_eq_empirical_average mu phi rho hmp horth hmem himpl,
          parseval_coeff_norm mu phi horth hmem, hproj, sub_zero]]
    unfold iid_expectation
    rw [integral_add (hdifferenceint.const_mul _) hprojectedint, integral_const_mul]
    change (m : ℝ)⁻¹ * iid_expectation mu n (fun xs => ‖density_coeff_estimator phi xs -
      group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2) +
      iid_expectation mu n
        (fun xs => ‖group_average_operator rho (density_coeff_estimator phi xs)‖ ^ 2) = _
    rw [hdifference, hprojected]
  refine ⟨X, inferInstance, ℤˣ, inferInstance, inferInstance, inferInstance,
    mu, phi, rho, fstar, hprob, hmp, horth, hmem, himpl, hfinrank,
    hf0, hfmem, hfinf, hdprob, hinv, ?_⟩
  rw [hdensity, hrisk, hess]
  have hleR : (rinv : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmul : 0 ≤ (rinv : ℝ) * ((m : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg rinv) (sub_nonneg.mpr hmR)
  field_simp [Nat.cast_ne_zero.mpr hn.ne', Nat.cast_ne_zero.mpr hm.ne']
  nlinarith [hleR, hmul]
