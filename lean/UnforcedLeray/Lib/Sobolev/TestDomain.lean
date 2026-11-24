import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Test domains and iterated directional derivatives (INF11 target S0)


§5.0 and §5.1 (S0); decisions D1 and D3 of the scoping README §3.

The manuscript uses integer-order Sobolev spaces defined by weak derivatives with an
*unweighted* distribution pairing (tex 13876–13886: `X_m = L²(ρ_ℓ^m dq dη)`,
`H^k_m = {f : D^α f ∈ X_m, |α| ≤ k}`, "The distribution pairing is unweighted"), on the whole
space and on the periodic cylinder with *periodic* weak derivatives (tex 4573–4577,
13850–13852: "Derivatives are periodic weak derivatives, never derivatives of zero
extensions"). A `TestDomain E n` packages the test class and the pairing measure of one such
setting.

## Deviation from the note's signature

The note writes `TestDomain (n : ℕ)` over `Eucl n`. Decision D1 (binding) puts the cylinder on
the carrier `Plane = ℝ × ℝ`. To make `Sob.W (cylinder c) …` typecheck on that carrier (D3:
`Cyl.H c m k = W (cylinder c) (ρw c ^ m) ℂ F k 2`), the carrier is a parameter `E` and the
`n` coordinate directions are a field `dir : Fin n → E`. For `wholeSpace n` the carrier is
`Eucl n` and `dir = e`, so every statement of the note specializes verbatim.

## Main declarations
* `Sob.Eucl n`, `Sob.e i` (the coordinate vectors of `EuclideanSpace ℝ (Fin n)`);
* `Sob.iterDirDeriv vs φ = ∂_{v₁} ⋯ ∂_{vₘ} φ` (NonUniqueEuler convention), with
  `iterDirDeriv_append`, `contDiff_iterDirDeriv`, `iterDirDeriv_perm`;
* `Sob.TestDomain E n`: measure, coordinate directions, admissible tests (smooth, closed under
  directional derivatives, a.e. compactly supported) and the fundamental lemma of the calculus
  of variations for the test class (`ae_zero`), which is what makes weak derivatives unique;
* `Sob.wholeSpaceOf E μ dir` and `Sob.wholeSpace n` (`C_c^∞` tests, Lebesgue measure).

The cylinder instance is in `Lib/Sobolev/Cylinder.lean`.

The commutation proof `dirDeriv_comm` is adapted from NonUniqueEuler
`P/Infra/Sobolev/WeakDeriv.lean` (`dirDeriv_dirDeriv_eq`, `dirDeriv_comm`, `iterDirDeriv_perm`;
vendored at `lean/NonUniqueEuler/P/Infra/Sobolev/WeakDeriv.lean`, reference copy

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

/-- Euclidean `ℝⁿ`. -/
abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The `i`-th coordinate vector of `ℝⁿ`. -/
def e {n : ℕ} (i : Fin n) : Eucl n := EuclideanSpace.single i 1

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `∂_{v₁} ∂_{v₂} ⋯ ∂_{vₘ} φ` for `vs = [v₁, …, vₘ]`, with `∂_v φ (x) = Dφ(x) v`
(NonUniqueEuler convention). -/
def iterDirDeriv (vs : List E) (φ : E → ℝ) : E → ℝ :=
  vs.foldr (fun v ψ x => fderiv ℝ ψ x v) φ

@[simp] theorem iterDirDeriv_nil (φ : E → ℝ) : iterDirDeriv [] φ = φ := rfl

@[simp] theorem iterDirDeriv_cons (v : E) (vs : List E) (φ : E → ℝ) :
    iterDirDeriv (v :: vs) φ = fun x => fderiv ℝ (iterDirDeriv vs φ) x v := rfl

theorem iterDirDeriv_singleton (v : E) (φ : E → ℝ) :
    iterDirDeriv [v] φ = fun x => fderiv ℝ φ x v := rfl

theorem iterDirDeriv_append (vs ws : List E) (φ : E → ℝ) :
    iterDirDeriv (vs ++ ws) φ = iterDirDeriv vs (iterDirDeriv ws φ) := by
  simp [iterDirDeriv, List.foldr_append]

theorem contDiff_dirDeriv {φ : E → ℝ} (h : ContDiff ℝ ∞ φ) (v : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ φ x v) :=
  (ContDiff.fderiv_right (m := ∞) h (by simp)).clm_apply contDiff_const

theorem contDiff_iterDirDeriv {φ : E → ℝ} (h : ContDiff ℝ ∞ φ) (vs : List E) :
    ContDiff ℝ ∞ (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih => exact contDiff_dirDeriv ih v

theorem dirDeriv_dirDeriv_eq {φ : E → ℝ} (h : ContDiff ℝ ∞ φ) (v w x : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y w) x v = fderiv ℝ (fderiv ℝ φ) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (ContDiff.fderiv_right (m := ∞) h (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) x).flip w) x := by
    have := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa using this
  rw [hx.fderiv]
  rfl

/-- Directional derivatives of a smooth function commute. -/
theorem dirDeriv_comm {φ : E → ℝ} (h : ContDiff ℝ ∞ φ) (v w : E) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ φ y w) x v) =
      fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x w := by
  funext x
  rw [dirDeriv_dirDeriv_eq h, dirDeriv_dirDeriv_eq h]
  exact (h.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- For smooth `φ`, `iterDirDeriv vs φ` depends on `vs` only up to permutation (S0). -/
theorem iterDirDeriv_perm {vs ws : List E} (hp : vs.Perm ws) {φ : E → ℝ}
    (h : ContDiff ℝ ∞ φ) : iterDirDeriv vs φ = iterDirDeriv ws φ := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp only [iterDirDeriv_cons, ih]
  | swap x y l =>
    simp only [iterDirDeriv_cons]
    exact dirDeriv_comm (contDiff_iterDirDeriv h l) y x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A directional derivative is linear in the direction. -/
theorem dirDeriv_add_dir (φ : E → ℝ) (v w : E) :
    (fun x => fderiv ℝ φ x (v + w)) = fun x => fderiv ℝ φ x v + fderiv ℝ φ x w := by
  funext x
  simp

end Calculus

/-! ### Test domains -/

/-- **Test domain** (S0). A carrier `E` with a pairing measure `μ`, `n` coordinate directions
`dir`, and a class `Adm` of real test functions which are smooth, closed under directional
derivatives, and vanish `μ`-a.e. outside a compact set. The field `ae_zero` is the
fundamental lemma for this test class: a locally integrable function with zero pairing
against every admissible test vanishes `μ`-a.e. It is what makes weak derivatives unique, and
is proved for each instance (`wholeSpaceOf`, `cylinder`). -/
structure TestDomain (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (n : ℕ) where
  /-- The (unweighted) pairing measure. -/
  μ : Measure E
  /-- The coordinate directions `∂₁, …, ∂ₙ`. -/
  dir : Fin n → E
  /-- Admissible test functions. -/
  Adm : (E → ℝ) → Prop
  smooth : ∀ {φ : E → ℝ}, Adm φ → ContDiff ℝ ∞ φ
  deriv_mem : ∀ {φ : E → ℝ}, Adm φ → ∀ v : E, Adm (fun x => fderiv ℝ φ x v)
  supp : ∀ {φ : E → ℝ}, Adm φ → ∃ K : Set E, IsCompact K ∧ ∀ᵐ x ∂μ, x ∉ K → φ x = 0
  finite : IsFiniteMeasureOnCompacts μ
  ae_zero : ∀ g : E → ℝ, LocallyIntegrable g μ →
    (∀ φ, Adm φ → ∫ x, φ x * g x ∂μ = 0) → g =ᵐ[μ] 0

namespace TestDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {n : ℕ}
  (D : TestDomain E n)

instance isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts D.μ := D.finite

theorem adm_iterDirDeriv {φ : E → ℝ} (hφ : D.Adm φ) (vs : List E) :
    D.Adm (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using hφ
  | cons v vs ih => exact D.deriv_mem ih v

theorem continuous {φ : E → ℝ} (hφ : D.Adm φ) : Continuous φ := (D.smooth hφ).continuous

end TestDomain

/-! ### The whole space -/

section WholeSpace

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The whole space `E` with a measure finite on compacts, the coordinate directions `dir`,
and the tests `C_c^∞(E)`. -/
def wholeSpaceOf (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {n : ℕ} (dir : Fin n → E) :
    TestDomain E n where
  μ := μ
  dir := dir
  Adm φ := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ
  smooth h := h.1
  deriv_mem h v := ⟨contDiff_dirDeriv h.1 v, h.2.fderiv_apply ℝ v⟩
  supp {φ} h := ⟨tsupport φ, h.2, Eventually.of_forall fun x hx =>
    image_eq_zero_of_notMem_tsupport hx⟩
  finite := inferInstance
  ae_zero g hg hφ := by
    have := ae_eq_zero_of_integral_contDiff_smul_eq_zero hg (fun φ h1 h2 => by
      simpa [smul_eq_mul] using hφ φ ⟨h1, h2⟩)
    filter_upwards [this] with x hx
    simpa using hx

variable {E}

@[simp] theorem wholeSpaceOf_adm (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {n : ℕ}
    (dir : Fin n → E) (φ : E → ℝ) :
    (wholeSpaceOf E μ dir).Adm φ ↔ ContDiff ℝ ∞ φ ∧ HasCompactSupport φ := Iff.rfl

@[simp] theorem wholeSpaceOf_μ (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {n : ℕ}
    (dir : Fin n → E) : (wholeSpaceOf E μ dir).μ = μ := rfl

@[simp] theorem wholeSpaceOf_dir (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {n : ℕ}
    (dir : Fin n → E) : (wholeSpaceOf E μ dir).dir = dir := rfl

end WholeSpace

/-- `ℝⁿ` with Lebesgue measure, coordinate directions `e i`, and tests `C_c^∞(ℝⁿ)`. -/
def wholeSpace (n : ℕ) : TestDomain (Eucl n) n :=
  wholeSpaceOf (Eucl n) volume e

@[simp] theorem wholeSpace_adm (n : ℕ) (φ : Eucl n → ℝ) :
    (wholeSpace n).Adm φ ↔ ContDiff ℝ ∞ φ ∧ HasCompactSupport φ := Iff.rfl

@[simp] theorem wholeSpace_μ (n : ℕ) : (wholeSpace n).μ = volume := rfl

@[simp] theorem wholeSpace_dir (n : ℕ) : (wholeSpace n).dir = e := rfl

end UnforcedLeray.Sob
