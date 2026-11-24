import UnforcedLeray.Infra.RieszProjection

/-!
# Periodic dichotomy, I: the monodromy splitting and the phase projections

Abstract setting of `paper/main.tex`, lines 359-385. Let `X` be a complex Banach space and
`E : ℝ → ℝ → (X →L[ℂ] X)` an evolution family:

* `E s s = 1`;
* `E τ r ∘ E r s = E τ s` for `s ≤ r ≤ τ`;
* `E (τ + P) (s + P) = E τ s` (period `P > 0`).

Let `ℳ = E P 0` be the monodromy and `r > 0` a radius with the circle `|z| = r` in the resolvent
set of `ℳ` (in the manuscript `r = e^{β𝒯}`). With `P₋ = rieszProj ℳ r` (the interior Riesz
projection), `P₊ = 1 - P₋`, `S = rieszOuterInv ℳ r` (the inverse of `ℳ` on `P₊X`, extended by `0`
on `P₋X`) and `ℳ₊ = ℳ|_{P₊X}` we put, for a phase `θ`,

* `F θ = E(θ,0)|_{P₊X} : P₊X → X`,
* `G θ = ℳ₊⁻¹ P₊ E(P,θ) : X → P₊X`,
* `piPlusPhase θ = F θ ∘ G θ = E(θ,0) S E(P,θ)` (the projection `Π₊(θ)` before periodic
  extension).

Main results:

* `G_comp_F`: `G θ F θ = 1` on `P₊X` for `0 ≤ θ ≤ P`;
* `isIdempotentElem_piPlusPhase`: `Π₊(θ)` is idempotent for `0 ≤ θ ≤ P`;
* `piPlusPhase_zero`, `piPlusPhase_period`: `Π₊(0) = Π₊(P) = P₊`;
* `E_natCast_mul_add`, `E_natCast_mul_add_period`: `E(nP + θ, 0) = E(θ,0) ℳⁿ` and
  `E(nP + P, φ) = ℳⁿ E(P,φ)`, the factorization through whole periods.

The Riesz operators come from `UnforcedLeray.Infra.RieszProjection`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Metric Complex Set
open UnforcedLeray.Infra.RieszProjection

namespace UnforcedLeray.Infra.PeriodicDichotomy

/-- A `P`-periodic evolution family on a complex Banach space together with a circle `|z| = r`
in the resolvent set of its monodromy `E P 0`. This is the data of `paper/main.tex`,
lines 359-370, with `r = e^{β𝒯}`. -/
structure PeriodicSplitting (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  /-- The evolution family `E(τ, s)`. -/
  E : ℝ → ℝ → X →L[ℂ] X
  /-- The period. -/
  P : ℝ
  P_pos : 0 < P
  E_self : ∀ s, E s s = 1
  E_comp : ∀ s r τ, s ≤ r → r ≤ τ → E τ r * E r s = E τ s
  E_periodic : ∀ τ s, E (τ + P) (s + P) = E τ s
  /-- The radius of the splitting circle. -/
  r : ℝ
  r_pos : 0 < r
  sphere_subset : sphere (0 : ℂ) r ⊆ resolventSet ℂ (E P 0)

namespace PeriodicSplitting

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (D : PeriodicSplitting X)

/-! ### Whole periods -/

/-- Periodicity by any integer number of periods. -/
theorem E_add_intCast_mul (τ s : ℝ) (n : ℤ) :
    D.E (τ + n * D.P) (s + n * D.P) = D.E τ s := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have h1 : τ + ((i + 1 : ℤ) : ℝ) * D.P = (τ + ((i : ℤ) : ℝ) * D.P) + D.P := by
      push_cast; ring
    have h2 : s + ((i + 1 : ℤ) : ℝ) * D.P = (s + ((i : ℤ) : ℝ) * D.P) + D.P := by
      push_cast; ring
    rw [h1, h2, D.E_periodic, ih]
  | pred i ih =>
    have h1 : τ + ((-(i : ℤ) : ℤ) : ℝ) * D.P = (τ + ((-(i : ℤ) - 1 : ℤ) : ℝ) * D.P) + D.P := by
      push_cast; ring
    have h2 : s + ((-(i : ℤ) : ℤ) : ℝ) * D.P = (s + ((-(i : ℤ) - 1 : ℤ) : ℝ) * D.P) + D.P := by
      push_cast; ring
    rw [← ih, h1, h2, D.E_periodic]

theorem E_add_natCast_mul (τ s : ℝ) (n : ℕ) :
    D.E (τ + n * D.P) (s + n * D.P) = D.E τ s := by
  have h := D.E_add_intCast_mul τ s n
  simpa only [Int.cast_natCast] using h

/-- The monodromy operator `ℳ = E(P, 0)`. -/
def monodromy : X →L[ℂ] X := D.E D.P 0

theorem sphere_subset_monodromy : sphere (0 : ℂ) D.r ⊆ resolventSet ℂ D.monodromy :=
  D.sphere_subset

/-- `E(nP, 0) = ℳⁿ`. -/
theorem E_natCast_mul_zero (n : ℕ) : D.E (n * D.P) 0 = D.monodromy ^ n := by
  have hP := D.P_pos
  induction n with
  | zero => simp [D.E_self]
  | succ n ih =>
    have h0 : (0 : ℝ) ≤ n * D.P := by positivity
    have h1 : (n : ℝ) * D.P ≤ ((n + 1 : ℕ) : ℝ) * D.P := by
      push_cast; nlinarith
    rw [← D.E_comp 0 (n * D.P) _ h0 h1, ih, pow_succ']
    congr 1
    have h := D.E_add_natCast_mul D.P 0 n
    rw [zero_add] at h
    rw [monodromy, ← h]
    congr 1
    push_cast; ring

/-- `E(nP + θ, 0) = E(θ, 0) ℳⁿ` for `θ ≥ 0`. -/
theorem E_natCast_mul_add (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    D.E (n * D.P + θ) 0 = D.E θ 0 * D.monodromy ^ n := by
  have hP := D.P_pos
  have h0 : (0 : ℝ) ≤ n * D.P := by positivity
  rw [← D.E_comp 0 (n * D.P) _ h0 (by linarith), D.E_natCast_mul_zero]
  congr 1
  have h := D.E_add_natCast_mul θ 0 n
  rw [zero_add] at h
  rw [← h, add_comm]

/-- `E(nP + P, φ) = ℳⁿ E(P, φ)` for `0 ≤ φ ≤ P`. -/
theorem E_natCast_mul_add_period (n : ℕ) {φ : ℝ} (hφ : φ ≤ D.P) :
    D.E (n * D.P + D.P) φ = D.monodromy ^ n * D.E D.P φ := by
  have hP := D.P_pos
  have h0 : (0 : ℝ) ≤ n * D.P := by positivity
  rw [← D.E_comp φ D.P _ hφ (by linarith), ← D.E_natCast_mul_zero]
  congr 1
  have h := D.E_periodic (n * D.P) 0
  rwa [zero_add] at h

/-! ### The Riesz splitting of the monodromy -/

/-- The interior Riesz projection `P₋ = (2πi)⁻¹ ∮_{|z|=r} (z - ℳ)⁻¹ dz`. -/
def projMinus : X →L[ℂ] X := rieszProj D.monodromy D.r

/-- The exterior projection `P₊ = 1 - P₋`. -/
def projPlus : X →L[ℂ] X := 1 - D.projMinus

/-- The outer inverse `S = -(2πi)⁻¹ ∮_{|z|=r} z⁻¹ (z - ℳ)⁻¹ dz`, the inverse of `ℳ` on `P₊X`,
vanishing on `P₋X`. -/
def outerInv : X →L[ℂ] X := rieszOuterInv D.monodromy D.r

/-- The exterior subspace `P₊X = ker P₋`. -/
abbrev exterior : Submodule ℂ X := outerSubspace D.monodromy D.r

/-- The exterior monodromy `ℳ₊ = ℳ|_{P₊X}`. -/
def monodromyPlus : D.exterior →L[ℂ] D.exterior := outerPart D.monodromy D.r

/-- `ℳ₊⁻¹ = S|_{P₊X}`. -/
def monodromyPlusInv : D.exterior →L[ℂ] D.exterior := outerPartInv D.monodromy D.r

theorem monodromyPlus_mul_inv : D.monodromyPlus * D.monodromyPlusInv = 1 :=
  outerPart_mul_outerPartInv D.r_pos D.sphere_subset_monodromy

theorem monodromyPlusInv_mul : D.monodromyPlusInv * D.monodromyPlus = 1 :=
  outerPartInv_mul_outerPart D.r_pos D.sphere_subset_monodromy

/-- `ℳ₊` as a unit of the operator algebra of `P₊X`. -/
def unitPlus : (D.exterior →L[ℂ] D.exterior)ˣ :=
  ⟨D.monodromyPlus, D.monodromyPlusInv, D.monodromyPlus_mul_inv, D.monodromyPlusInv_mul⟩

@[simp] theorem val_unitPlus : (D.unitPlus : D.exterior →L[ℂ] D.exterior) = D.monodromyPlus :=
  rfl

@[simp] theorem val_unitPlus_inv :
    ((D.unitPlus⁻¹ : (D.exterior →L[ℂ] D.exterior)ˣ) : D.exterior →L[ℂ] D.exterior) =
      D.monodromyPlusInv :=
  rfl

/-- `P₊` as a map onto `P₊X`. -/
def toExterior : X →L[ℂ] D.exterior :=
  D.projPlus.codRestrict D.exterior
    (one_sub_rieszProj_apply_mem D.r_pos D.sphere_subset_monodromy)

@[simp] theorem coe_toExterior (x : X) : (D.toExterior x : X) = D.projPlus x := rfl

/-! ### Algebra of the splitting -/

theorem projMinus_mul_self : D.projMinus * D.projMinus = D.projMinus :=
  rieszProj_mul_self D.r_pos D.sphere_subset_monodromy

theorem projPlus_mul_self : D.projPlus * D.projPlus = D.projPlus :=
  isIdempotentElem_one_sub_rieszProj D.r_pos D.sphere_subset_monodromy

theorem monodromy_mul_outerInv : D.monodromy * D.outerInv = D.projPlus :=
  mul_rieszOuterInv D.r_pos D.sphere_subset_monodromy

theorem outerInv_mul_monodromy : D.outerInv * D.monodromy = D.projPlus :=
  rieszOuterInv_mul D.r_pos D.sphere_subset_monodromy

theorem outerInv_mul_projPlus : D.outerInv * D.projPlus = D.outerInv :=
  rieszOuterInv_mul_one_sub D.r_pos D.sphere_subset_monodromy

theorem projPlus_mul_outerInv : D.projPlus * D.outerInv = D.outerInv :=
  one_sub_mul_rieszOuterInv D.r_pos D.sphere_subset_monodromy

theorem commute_monodromy_outerInv : Commute D.monodromy D.outerInv :=
  commute_rieszOuterInv_of_commute (Commute.refl _) D.r

theorem commute_monodromy_projPlus : Commute D.monodromy D.projPlus :=
  (Commute.one_right _).sub_right (commute_self_rieszProj D.r_pos.le D.sphere_subset_monodromy)

theorem commute_monodromy_pow_outerInv (n : ℕ) : Commute (D.monodromy ^ n) D.outerInv :=
  D.commute_monodromy_outerInv.pow_left n

/-- `ℳ^{n+1} S = ℳⁿ P₊`. -/
theorem monodromy_pow_succ_mul_outerInv (n : ℕ) :
    D.monodromy ^ (n + 1) * D.outerInv = D.monodromy ^ n * D.projPlus := by
  rw [pow_succ, mul_assoc, D.monodromy_mul_outerInv]

theorem projMinus_apply_of_mem {v : X} (hv : v ∈ D.exterior) : D.projMinus v = 0 :=
  mem_outerSubspace.1 hv

theorem projPlus_apply_of_mem {v : X} (hv : v ∈ D.exterior) : D.projPlus v = v := by
  rw [projPlus, sub_apply, one_apply_eq_self, D.projMinus_apply_of_mem hv, sub_zero]

theorem outerInv_apply_mem (x : X) : D.outerInv x ∈ D.exterior := by
  rw [mem_outerSubspace]
  show (D.projMinus * D.outerInv) x = 0
  rw [projMinus, outerInv, rieszProj_mul_rieszOuterInv D.r_pos D.sphere_subset_monodromy,
    zero_apply]

@[simp] theorem coe_monodromyPlus_apply (v : D.exterior) :
    (D.monodromyPlus v : X) = D.monodromy v := rfl

@[simp] theorem coe_monodromyPlusInv_apply (v : D.exterior) :
    (D.monodromyPlusInv v : X) = D.outerInv v := rfl

theorem coe_monodromyPlus_pow_apply (n : ℕ) (v : D.exterior) :
    ((D.monodromyPlus ^ n) v : X) = (D.monodromy ^ n) v :=
  restrict_pow_apply _ (mapsTo_outerSubspace (Commute.refl _)) n v

theorem coe_monodromyPlusInv_pow_apply (n : ℕ) (v : D.exterior) :
    ((D.monodromyPlusInv ^ n) v : X) = (D.outerInv ^ n) v :=
  restrict_pow_apply _
    (mapsTo_outerSubspace (commute_rieszOuterInv_of_commute (Commute.refl _) _).symm) n v

/-! ### The phase operators `F θ`, `G θ` and `Π₊(θ)` -/

/-- `F θ = E(θ, 0)|_{P₊X}`. -/
def F (θ : ℝ) : D.exterior →L[ℂ] X := (D.E θ 0).comp D.exterior.subtypeL

/-- `G θ = ℳ₊⁻¹ P₊ E(P, θ)`. -/
def G (θ : ℝ) : X →L[ℂ] D.exterior := D.monodromyPlusInv.comp (D.toExterior.comp (D.E D.P θ))

/-- The phase projection `Π₊(θ) = F θ G θ`, for `0 ≤ θ ≤ P` (before periodic extension). -/
def piPlusPhase (θ : ℝ) : X →L[ℂ] X := (D.F θ).comp (D.G θ)

@[simp] theorem F_apply (θ : ℝ) (v : D.exterior) : D.F θ v = D.E θ 0 v := rfl

theorem coe_G_apply (θ : ℝ) (x : X) : (D.G θ x : X) = D.outerInv (D.E D.P θ x) := by
  show D.outerInv (D.projPlus (D.E D.P θ x)) = _
  rw [← mul_apply_eq_comp, D.outerInv_mul_projPlus]

/-- `ι ∘ G θ = S E(P, θ)`. -/
theorem subtypeL_comp_G (θ : ℝ) :
    D.exterior.subtypeL.comp (D.G θ) = D.outerInv * D.E D.P θ := by
  ext x
  rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, coe_G_apply, mul_apply_eq_comp]

/-- `Π₊(θ) = E(θ, 0) S E(P, θ)`. -/
theorem piPlusPhase_eq (θ : ℝ) :
    D.piPlusPhase θ = D.E θ 0 * D.outerInv * D.E D.P θ := by
  ext x
  rw [piPlusPhase, ContinuousLinearMap.comp_apply, F_apply, coe_G_apply, mul_apply_eq_comp,
    mul_apply_eq_comp]

/-- `E(P, θ) E(θ, 0) = ℳ` for `0 ≤ θ ≤ P`. -/
theorem E_period_mul_E (θ : ℝ) (h0 : 0 ≤ θ) (hP : θ ≤ D.P) :
    D.E D.P θ * D.E θ 0 = D.monodromy :=
  D.E_comp 0 θ D.P h0 hP

/-- **`G θ F θ = 1` on `P₊X`** for `0 ≤ θ ≤ P`. -/
theorem G_comp_F {θ : ℝ} (h0 : 0 ≤ θ) (hP : θ ≤ D.P) :
    (D.G θ).comp (D.F θ) = ContinuousLinearMap.id ℂ D.exterior := by
  ext v
  rw [ContinuousLinearMap.comp_apply, coe_G_apply, F_apply, ContinuousLinearMap.id_apply,
    ← mul_apply_eq_comp (D.E D.P θ), D.E_period_mul_E θ h0 hP, ← mul_apply_eq_comp,
    D.outerInv_mul_monodromy, D.projPlus_apply_of_mem v.2]

theorem G_F_apply {θ : ℝ} (h0 : 0 ≤ θ) (hP : θ ≤ D.P) (v : D.exterior) :
    D.G θ (D.F θ v) = v := by
  rw [← ContinuousLinearMap.comp_apply, D.G_comp_F h0 hP, ContinuousLinearMap.id_apply]

/-- `S E(P,θ) E(θ,0) S = S` for `0 ≤ θ ≤ P`. -/
theorem outerInv_mul_E_mul_E_mul_outerInv {θ : ℝ} (h0 : 0 ≤ θ) (hP : θ ≤ D.P) :
    D.outerInv * D.E D.P θ * (D.E θ 0 * D.outerInv) = D.outerInv := by
  rw [mul_assoc, ← mul_assoc (D.E D.P θ), D.E_period_mul_E θ h0 hP, ← mul_assoc,
    D.outerInv_mul_monodromy, D.projPlus_mul_outerInv]

/-- **`Π₊(θ)` is a projection** for `0 ≤ θ ≤ P`. -/
theorem isIdempotentElem_piPlusPhase {θ : ℝ} (h0 : 0 ≤ θ) (hP : θ ≤ D.P) :
    IsIdempotentElem (D.piPlusPhase θ) := by
  unfold IsIdempotentElem
  rw [D.piPlusPhase_eq]
  calc D.E θ 0 * D.outerInv * D.E D.P θ * (D.E θ 0 * D.outerInv * D.E D.P θ)
      = D.E θ 0 * (D.outerInv * D.E D.P θ * (D.E θ 0 * D.outerInv)) * D.E D.P θ := by
        simp only [mul_assoc]
    _ = D.E θ 0 * D.outerInv * D.E D.P θ := by
        rw [D.outerInv_mul_E_mul_E_mul_outerInv h0 hP]

/-- **`Π₋(θ) = 1 - Π₊(θ)` is a projection** for `0 ≤ θ ≤ P`. -/
theorem isIdempotentElem_one_sub_piPlusPhase {θ : ℝ} (h0 : 0 ≤ θ) (hP : θ ≤ D.P) :
    IsIdempotentElem (1 - D.piPlusPhase θ) :=
  (D.isIdempotentElem_piPlusPhase h0 hP).one_sub

/-- **`Π₊(0) = P₊`.** -/
theorem piPlusPhase_zero : D.piPlusPhase 0 = D.projPlus := by
  rw [piPlusPhase_eq, D.E_self, one_mul]
  exact D.outerInv_mul_monodromy

/-- **`Π₊(P) = P₊`** (equal endpoint values). -/
theorem piPlusPhase_period : D.piPlusPhase D.P = D.projPlus := by
  rw [piPlusPhase_eq, D.E_self, mul_one]
  exact D.monodromy_mul_outerInv

/-- `Π₊(θ) F θ = F θ`: the range of `F θ` lies in the range of `Π₊(θ)`. -/
theorem piPlusPhase_comp_F {θ : ℝ} (h0 : 0 ≤ θ) (hP : θ ≤ D.P) :
    (D.piPlusPhase θ).comp (D.F θ) = D.F θ := by
  rw [piPlusPhase, ContinuousLinearMap.comp_assoc, D.G_comp_F h0 hP,
    ContinuousLinearMap.comp_id]

/-- `G θ Π₊(θ) = G θ`. -/
theorem G_comp_piPlusPhase {θ : ℝ} (h0 : 0 ≤ θ) (hP : θ ≤ D.P) :
    (D.G θ).comp (D.piPlusPhase θ) = D.G θ := by
  rw [piPlusPhase, ← ContinuousLinearMap.comp_assoc, D.G_comp_F h0 hP,
    ContinuousLinearMap.id_comp]

end PeriodicSplitting

end UnforcedLeray.Infra.PeriodicDichotomy
