import UnforcedLeray.Units.B0146
import UnforcedLeray.Units.B0151.Linf

/-!
# B0147 helper: the unit-width profile class

Blueprint unit **B0147** (`eq:st18-t00145`, `paper/main.tex` lines 2217–2234), helper file.

After the rescaling `y = x/√a` (tex line 2229: "absorb the polynomial Gaussian factors from
differentiation into a smaller Gaussian exponent") every derivative of the isolated heat
vortex is a polynomial times the unit Gaussian `G₀(y) = e^{-|y|²/4}`. The predicate `GP`
records exactly this class: it contains `G₀` and is closed under multiplication by the
coordinates, sums and scalar multiples. We prove

* closure under the classical partial derivatives (`GP.derivX`, `GP.derivY`), with genuine
  one-variable derivatives;
* a Gaussian bound `|f y| ≤ K e^{-β|y|²}` with `β > 0` (`GP.bound`), which is the absorption
  of the polynomial factors into a smaller exponent;
* continuity, and closure under the transverse weight `(1 + y₂²)^m`.

The velocity components at width `a` are `a^{-3/2}` times the unit-width components at
`x/√a` (`uc_scale`).
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace UnforcedLeray.B0147

open UnforcedLeray.GaussianVortex
open UnforcedLeray.B0146 (GF XDecay latticeSum shift radiusSq_nonneg uc vcomp)

/-- The unit Gaussian `G₀(y) = e^{-|y|²/4}` (the width-one factor of tex line 2203). -/
def G0 (y : Plane) : ℝ := Real.exp (-(radiusSq y / 4))

/-- Polynomials in `(y₁, y₂)` times the unit Gaussian `G₀`: the class of all derivatives of the
unit-width heat vortex (tex line 2229). -/
inductive GP : (Plane → ℝ) → Prop
  | gauss : GP G0
  | mulX {f : Plane → ℝ} : GP f → GP (fun y => y.1 * f y)
  | mulY {f : Plane → ℝ} : GP f → GP (fun y => y.2 * f y)
  | add {f g : Plane → ℝ} : GP f → GP g → GP (fun y => f y + g y)
  | smul (k : ℝ) {f : Plane → ℝ} : GP f → GP (fun y => k * f y)

theorem GP.congr {f g : Plane → ℝ} (hf : GP f) (h : ∀ y, f y = g y) : GP g := by
  have : f = g := funext h
  subst this
  exact hf

theorem hasDerivAt_G0_x (y : Plane) :
    HasDerivAt (fun t => G0 (t, y.2)) (-(1 / 2) * (y.1 * G0 y)) y.1 := by
  have h2 := (((hasDerivAt_pow 2 y.1).add_const (y.2 ^ 2)).const_mul (-(1 / 4 : ℝ))).exp
  have e : ∀ t : ℝ, G0 (t, y.2) = Real.exp (-(1 / 4) * (t ^ 2 + y.2 ^ 2)) := fun t => by
    unfold G0 radiusSq; congr 1; ring
  have e0 : G0 y = Real.exp (-(1 / 4) * (y.1 ^ 2 + y.2 ^ 2)) := e y.1
  rw [show (fun t => G0 (t, y.2)) = fun t => Real.exp (-(1 / 4) * (t ^ 2 + y.2 ^ 2)) from
    funext e, e0]
  convert h2 using 1
  push_cast
  ring

theorem hasDerivAt_G0_y (y : Plane) :
    HasDerivAt (fun t => G0 (y.1, t)) (-(1 / 2) * (y.2 * G0 y)) y.2 := by
  have h2 := (((hasDerivAt_pow 2 y.2).const_add (y.1 ^ 2)).const_mul (-(1 / 4 : ℝ))).exp
  have e : ∀ t : ℝ, G0 (y.1, t) = Real.exp (-(1 / 4) * (y.1 ^ 2 + t ^ 2)) := fun t => by
    unfold G0 radiusSq; congr 1; ring
  have e0 : G0 y = Real.exp (-(1 / 4) * (y.1 ^ 2 + y.2 ^ 2)) := e y.2
  rw [show (fun t => G0 (y.1, t)) = fun t => Real.exp (-(1 / 4) * (y.1 ^ 2 + t ^ 2)) from
    funext e, e0]
  convert h2 using 1
  push_cast
  ring

/-- Closure of `GP` under the classical `∂_q`, with a genuine derivative. -/
theorem GP.derivX {f : Plane → ℝ} (hf : GP f) :
    ∃ g : Plane → ℝ, GP g ∧ ∀ y : Plane, HasDerivAt (fun t => f (t, y.2)) (g y) y.1 := by
  induction hf with
  | gauss => exact ⟨_, .smul _ (.mulX .gauss), hasDerivAt_G0_x⟩
  | @mulX f _ ih =>
    obtain ⟨g, hg, hd⟩ := ih
    refine ⟨fun y => f y + y.1 * g y, .add (by assumption) hg.mulX, fun y => ?_⟩
    exact ((hasDerivAt_id' y.1).mul (hd y)).congr_deriv (by simp)
  | @mulY f _ ih =>
    obtain ⟨g, hg, hd⟩ := ih
    exact ⟨fun y => y.2 * g y, hg.mulY, fun y => (hd y).const_mul y.2⟩
  | @add f₁ f₂ _ _ ih₁ ih₂ =>
    obtain ⟨g₁, hg₁, hd₁⟩ := ih₁
    obtain ⟨g₂, hg₂, hd₂⟩ := ih₂
    exact ⟨fun y => g₁ y + g₂ y, hg₁.add hg₂, fun y => (hd₁ y).add (hd₂ y)⟩
  | @smul k f _ ih =>
    obtain ⟨g, hg, hd⟩ := ih
    exact ⟨fun y => k * g y, hg.smul k, fun y => (hd y).const_mul k⟩

/-- Closure of `GP` under the classical `∂_η`, with a genuine derivative. -/
theorem GP.derivY {f : Plane → ℝ} (hf : GP f) :
    ∃ g : Plane → ℝ, GP g ∧ ∀ y : Plane, HasDerivAt (fun t => f (y.1, t)) (g y) y.2 := by
  induction hf with
  | gauss => exact ⟨_, .smul _ (.mulY .gauss), hasDerivAt_G0_y⟩
  | @mulX f _ ih =>
    obtain ⟨g, hg, hd⟩ := ih
    exact ⟨fun y => y.1 * g y, hg.mulX, fun y => (hd y).const_mul y.1⟩
  | @mulY f _ ih =>
    obtain ⟨g, hg, hd⟩ := ih
    refine ⟨fun y => f y + y.2 * g y, .add (by assumption) hg.mulY, fun y => ?_⟩
    exact ((hasDerivAt_id' y.2).mul (hd y)).congr_deriv (by simp)
  | @add f₁ f₂ _ _ ih₁ ih₂ =>
    obtain ⟨g₁, hg₁, hd₁⟩ := ih₁
    obtain ⟨g₂, hg₂, hd₂⟩ := ih₂
    exact ⟨fun y => g₁ y + g₂ y, hg₁.add hg₂, fun y => (hd₁ y).add (hd₂ y)⟩
  | @smul k f _ ih =>
    obtain ⟨g, hg, hd⟩ := ih
    exact ⟨fun y => k * g y, hg.smul k, fun y => (hd y).const_mul k⟩

theorem GF_G0 : GF 1 1 (fun _ => G0) := by
  refine ⟨1, 1 / 4, zero_le_one, by norm_num, fun a _ w => ?_⟩
  simp only [G0]
  rw [abs_of_pos (Real.exp_pos _), one_mul]
  apply le_of_eq
  congr 1
  ring

/-- `GP` functions decay like a Gaussian (uniform-width predicate of unit B0146 at width one). -/
theorem GP.gf {f : Plane → ℝ} (hf : GP f) : GF 1 1 (fun _ => f) := by
  induction hf with
  | gauss => exact GF_G0
  | mulX _ ih => exact B0146.GF.mul_left B0146.PG.fst ih
  | mulY _ ih => exact B0146.GF.mul_left B0146.PG.snd ih
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | smul k _ ih => exact B0146.GF.mul_left (B0146.PG.const k) ih

/-- A Gaussian bound with an explicit rate. -/
def GBound (K β : ℝ) (f : Plane → ℝ) : Prop :=
  ∀ y : Plane, |f y| ≤ K * Real.exp (-(β * radiusSq y))

theorem GBound.mono {K β K' β' : ℝ} {f : Plane → ℝ} (h : GBound K β f) (hK0 : 0 ≤ K)
    (hK : K ≤ K') (hβ : β' ≤ β) : GBound K' β' f := by
  intro y
  have hR := radiusSq_nonneg y
  have h1 : Real.exp (-(β * radiusSq y)) ≤ Real.exp (-(β' * radiusSq y)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc |f y| ≤ K * Real.exp (-(β * radiusSq y)) := h y
    _ ≤ K' * Real.exp (-(β' * radiusSq y)) :=
        mul_le_mul hK h1 (Real.exp_pos _).le (hK0.trans hK)

/-- **Absorption of polynomial factors** (tex line 2229): every `GP` function is bounded by a
Gaussian `K e^{-β|y|²}` with `β > 0`. -/
theorem GP.bound {f : Plane → ℝ} (hf : GP f) :
    ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ GBound K β f := by
  obtain ⟨K, β, hK, hβ, h⟩ := hf.gf
  exact ⟨K, β, hK, hβ, fun y => h 1 ⟨le_rfl, le_rfl⟩ y⟩

theorem GBound.xdecay {K β : ℝ} {f : Plane → ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (h : GBound K β f) : XDecay f := by
  refine ⟨K, β, hK, hβ, fun y => (h y).trans ?_⟩
  have := B0146.fst_sq_le_radiusSq y
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK

theorem GP.xdecay {f : Plane → ℝ} (hf : GP f) : XDecay f :=
  B0146.xd (a := 1) hf.gf

theorem continuous_G0 : Continuous G0 := by
  unfold G0 radiusSq
  fun_prop

theorem GP.continuous {f : Plane → ℝ} (hf : GP f) : Continuous f := by
  induction hf with
  | gauss => exact continuous_G0
  | mulX _ ih => exact continuous_fst.mul ih
  | mulY _ ih => exact continuous_snd.mul ih
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | smul k _ ih => exact continuous_const.mul ih

/-- Closure under the transverse weight `(1 + y₂²)^m` (tex line 2234). -/
theorem GP.weight {f : Plane → ℝ} (hf : GP f) (m : ℕ) :
    GP (fun y => (1 + y.2 ^ 2) ^ m * f y) := by
  induction m with
  | zero => exact hf.congr fun y => by simp
  | succ m ih =>
    exact (ih.add ih.mulY.mulY).congr fun y => by ring

/-! ### The unit-width velocity profile and the rescaling -/

/-- The unit-width velocity components `U_k = uc k 1`: `U₀ = -y₂ G₀`, `U₁ = y₁ G₀`. -/
def U (k : Fin 2) : Plane → ℝ := uc k 1

theorem gw_one (y : Plane) : B0113.gw 1 y = G0 y := by
  simp [B0113.gw, G0]

theorem GP_U (k : Fin 2) : GP (U k) := by
  fin_cases k
  · exact (GP.gauss.mulY.smul (-1)).congr fun y => by
      simp [U, uc, vcomp, B0113.vExp, gw_one]
  · exact GP.gauss.mulX.congr fun y => by
      simp [U, uc, vcomp, B0113.vExp, gw_one]

/-- The inverse width scale `λ = a^{-1/2}`. -/
def lam (a : ℝ) : ℝ := (Real.sqrt a)⁻¹

theorem lam_pos {a : ℝ} (ha : 0 < a) : 0 < lam a := inv_pos.mpr (Real.sqrt_pos.mpr ha)

theorem lam_sq {a : ℝ} (ha : 0 < a) : lam a ^ 2 = a⁻¹ := by
  rw [lam, inv_pow, Real.sq_sqrt ha.le]

/-- Rescaling of the isolated velocity: `V_a(w) = a^{-3/2} U(w/√a)` componentwise. -/
theorem uc_scale {a : ℝ} (ha : 0 < a) (k : Fin 2) (w : Plane) :
    uc k a w = lam a ^ 3 * U k (lam a * w.1, lam a * w.2) := by
  have h2 := lam_sq ha
  have he : B0113.gw 1 (lam a * w.1, lam a * w.2) = B0113.gw a w := by
    simp only [B0113.gw, radiusSq]
    congr 1
    rw [mul_pow, mul_pow, h2]
    ring
  have h4 : lam a ^ 3 * lam a = a⁻¹ ^ 2 := by rw [← h2]; ring
  fin_cases k
  · simp only [U, uc, vcomp, B0113.vExp, he]
    simp
    linear_combination (-(w.2 * B0113.gw a w)) * h4
  · simp only [U, uc, vcomp, B0113.vExp, he]
    simp
    linear_combination (-(w.1 * B0113.gw a w)) * h4

end UnforcedLeray.B0147
