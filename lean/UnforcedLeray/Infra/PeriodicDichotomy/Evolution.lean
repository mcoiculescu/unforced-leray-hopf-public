import UnforcedLeray.Infra.PeriodicDichotomy.Basic

/-!
# Periodic dichotomy, II: periodic projections, intertwining and the exterior evolution

Continuation of `PeriodicDichotomy/Basic.lean` (`paper/main.tex`, lines 371-385). Every time
`t` is written `t = k P + θ` with `k = index t ∈ ℤ` and phase `θ = phase t ∈ [0, P)`
(`toIcoDiv`, `toIcoMod`). We define

* `piPlus t = Π₊(phase t)`, `piMinus t = 1 - piPlus t`, the `P`-periodic extensions of the
  phase projections;
* `extEvol τ s = F_θ ℳ₊^{k-l} G_φ` for `τ = kP + θ`, `s = lP + φ` (`k - l ∈ ℤ`; only `ℳ₊` is
  inverted), the two-sided exterior evolution `E₊(τ, s) Π₊(s)`.

Main results:

* `isIdempotentElem_piPlus`, `isIdempotentElem_piMinus`, `piPlus_zero`, `piPlus_period`,
  `piPlus_add_period`;
* `E_mul_piPlus`, `E_mul_piMinus`: intertwining `E(τ,s) Π_±(s) = Π_±(τ) E(τ,s)` for `τ ≥ s`;
* `extEvol_mul_piPlus`, `piPlus_mul_extEvol`: `E₊(τ,s) Π₊(s) = E₊(τ,s) = Π₊(τ) E₊(τ,s)`;
* `extEvol_mul_extEvol`: `E₊(τ,r) E₊(r,s) = E₊(τ,s)` for all `τ, r, s`;
* `E_mul_piPlus_eq_extEvol`: `E(τ,s) Π₊(s) = E₊(τ,s) Π₊(s)` for `τ ≥ s`;
* `E_mul_extEvol`: `E(τ,r) E₊(r,s) Π₊(s) = E₊(τ,s) Π₊(s)` for `τ ≥ r`;
* `extEvol_intCast_mul_add`: `E₊(kP + θ, lP + φ) Π₊(φ) = F_θ ℳ₊^{k-l} G_φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Metric Complex Set
open UnforcedLeray.Infra.RieszProjection

namespace UnforcedLeray.Infra.PeriodicDichotomy

namespace PeriodicSplitting

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (D : PeriodicSplitting X)

/-! ### Phases -/

/-- The phase `θ ∈ [0, P)` of `t = kP + θ`. -/
def phase (t : ℝ) : ℝ := toIcoMod D.P_pos 0 t

/-- The period index `k ∈ ℤ` of `t = kP + θ`. -/
def index (t : ℝ) : ℤ := toIcoDiv D.P_pos 0 t

theorem phase_mem (t : ℝ) : D.phase t ∈ Ico 0 D.P := by
  have h := toIcoMod_mem_Ico D.P_pos 0 t
  rwa [zero_add] at h

theorem phase_nonneg (t : ℝ) : 0 ≤ D.phase t := (D.phase_mem t).1

theorem phase_lt (t : ℝ) : D.phase t < D.P := (D.phase_mem t).2

theorem phase_le (t : ℝ) : D.phase t ≤ D.P := (D.phase_lt t).le

theorem index_mul_add_phase (t : ℝ) : (D.index t : ℝ) * D.P + D.phase t = t := by
  have h := toIcoDiv_zsmul_sub_toIcoMod D.P_pos 0 t
  rwa [zsmul_eq_mul] at h

theorem index_intCast_mul_add (k : ℤ) {θ : ℝ} (hθ : θ ∈ Ico 0 D.P) :
    D.index (k * D.P + θ) = k := by
  rw [index, toIcoDiv_eq_iff, zsmul_eq_mul, add_sub_cancel_left, zero_add]
  exact hθ

theorem phase_intCast_mul_add (k : ℤ) {θ : ℝ} (hθ : θ ∈ Ico 0 D.P) :
    D.phase (k * D.P + θ) = θ := by
  have h := D.index_mul_add_phase (k * D.P + θ)
  rw [D.index_intCast_mul_add k hθ] at h
  linarith

theorem phase_of_mem {θ : ℝ} (hθ : θ ∈ Ico 0 D.P) : D.phase θ = θ := by
  have h := D.phase_intCast_mul_add 0 hθ
  rwa [Int.cast_zero, zero_mul, zero_add] at h

theorem index_of_mem {θ : ℝ} (hθ : θ ∈ Ico 0 D.P) : D.index θ = 0 := by
  have h := D.index_intCast_mul_add 0 hθ
  rwa [Int.cast_zero, zero_mul, zero_add] at h

theorem phase_add_period (t : ℝ) : D.phase (t + D.P) = D.phase t :=
  toIcoMod_add_right D.P_pos 0 t

theorem index_add_period (t : ℝ) : D.index (t + D.P) = D.index t + 1 :=
  toIcoDiv_add_right D.P_pos 0 t

theorem phase_zero : D.phase 0 = 0 := D.phase_of_mem ⟨le_rfl, D.P_pos⟩

theorem phase_period : D.phase D.P = 0 := by
  have h := D.phase_add_period 0
  rwa [zero_add, D.phase_zero] at h

/-- The index is monotone. -/
theorem index_le_index {s τ : ℝ} (hsτ : s ≤ τ) : D.index s ≤ D.index τ := by
  by_contra h
  rw [not_le] at h
  have h1 : (D.index τ : ℝ) + 1 ≤ D.index s := by exact_mod_cast h
  have hτ := D.index_mul_add_phase τ
  have hs := D.index_mul_add_phase s
  have hθ := D.phase_lt τ
  have hφ := D.phase_nonneg s
  have hP := D.P_pos
  have : ((D.index τ : ℝ) + 1) * D.P ≤ (D.index s : ℝ) * D.P :=
    mul_le_mul_of_nonneg_right h1 hP.le
  nlinarith

/-- `E(τ, s) = E(nP + θ, φ)` for `τ ≥ s`, with `θ, φ` the phases and `n = index τ - index s`. -/
theorem E_eq_phase {s τ : ℝ} (hsτ : s ≤ τ) :
    D.E τ s = D.E ((D.index τ - D.index s).toNat * D.P + D.phase τ) (D.phase s) := by
  have hn : (((D.index τ - D.index s).toNat : ℤ) : ℝ) = (D.index τ : ℝ) - D.index s := by
    rw [Int.toNat_of_nonneg (sub_nonneg.2 (D.index_le_index hsτ))]
    push_cast; ring
  have hτ := D.index_mul_add_phase τ
  have hs := D.index_mul_add_phase s
  have h := D.E_add_intCast_mul ((D.index τ - D.index s).toNat * D.P + D.phase τ) (D.phase s)
    (D.index s)
  rw [← h]
  rw [Int.cast_natCast] at hn
  congr 1
  · rw [hn]; linarith
  · linarith

/-! ### Factorization through whole periods -/

/-- `E(nP + θ, φ) E(φ, 0) = E(θ, 0) ℳⁿ` for `0 ≤ φ ≤ nP + θ`, `θ ≥ 0`. -/
theorem E_mul_E_phase (n : ℕ) {θ φ : ℝ} (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hφθ : φ ≤ n * D.P + θ) :
    D.E (n * D.P + θ) φ * D.E φ 0 = D.E θ 0 * D.monodromy ^ n := by
  rw [D.E_comp 0 φ _ hφ hφθ, D.E_natCast_mul_add n hθ]

/-- `E(P, θ) E(nP + θ, φ) = ℳⁿ E(P, φ)` for `φ ≤ nP + θ`, `θ ≤ P`, `φ ≤ P`. -/
theorem E_period_mul_E_phase (n : ℕ) {θ φ : ℝ} (hθ : θ ≤ D.P) (hφ : φ ≤ D.P)
    (hφθ : φ ≤ n * D.P + θ) :
    D.E D.P θ * D.E (n * D.P + θ) φ = D.monodromy ^ n * D.E D.P φ := by
  have h := D.E_add_natCast_mul D.P θ n
  rw [← h, add_comm D.P, add_comm θ, D.E_comp φ _ _ hφθ (by linarith),
    D.E_natCast_mul_add_period n hφ]

/-- Intertwining on the phases: `E(nP + θ, φ) Π₊(φ) = Π₊(θ) E(nP + θ, φ)`. -/
theorem E_mul_piPlusPhase (n : ℕ) {θ φ : ℝ} (hθ : θ ∈ Ico 0 D.P) (hφ : φ ∈ Ico 0 D.P)
    (hφθ : φ ≤ n * D.P + θ) :
    D.E (n * D.P + θ) φ * D.piPlusPhase φ = D.piPlusPhase θ * D.E (n * D.P + θ) φ := by
  rw [D.piPlusPhase_eq, D.piPlusPhase_eq]
  calc D.E (n * D.P + θ) φ * (D.E φ 0 * D.outerInv * D.E D.P φ)
      = (D.E (n * D.P + θ) φ * D.E φ 0) * D.outerInv * D.E D.P φ := by simp only [mul_assoc]
    _ = D.E θ 0 * (D.monodromy ^ n * D.outerInv) * D.E D.P φ := by
        rw [D.E_mul_E_phase n hθ.1 hφ.1 hφθ]; simp only [mul_assoc]
    _ = D.E θ 0 * D.outerInv * (D.monodromy ^ n * D.E D.P φ) := by
        rw [(D.commute_monodromy_pow_outerInv n).eq]; simp only [mul_assoc]
    _ = D.E θ 0 * D.outerInv * D.E D.P θ * D.E (n * D.P + θ) φ := by
        rw [← D.E_period_mul_E_phase n hθ.2.le hφ.2.le hφθ]; simp only [mul_assoc]

/-! ### The periodic projections -/

/-- `Π₊(t)`, the `P`-periodic extension of the phase projection. -/
def piPlus (t : ℝ) : X →L[ℂ] X := D.piPlusPhase (D.phase t)

/-- `Π₋(t) = 1 - Π₊(t)`. -/
def piMinus (t : ℝ) : X →L[ℂ] X := 1 - D.piPlus t

theorem piPlus_of_mem {θ : ℝ} (hθ : θ ∈ Ico 0 D.P) : D.piPlus θ = D.piPlusPhase θ := by
  rw [piPlus, D.phase_of_mem hθ]

theorem piPlus_add_period (t : ℝ) : D.piPlus (t + D.P) = D.piPlus t := by
  rw [piPlus, piPlus, D.phase_add_period]

theorem piMinus_add_period (t : ℝ) : D.piMinus (t + D.P) = D.piMinus t := by
  rw [piMinus, piMinus, D.piPlus_add_period]

theorem piPlus_intCast_mul_add (k : ℤ) {θ : ℝ} (hθ : θ ∈ Ico 0 D.P) :
    D.piPlus (k * D.P + θ) = D.piPlusPhase θ := by
  rw [piPlus, D.phase_intCast_mul_add k hθ]

theorem piPlus_eq (t : ℝ) :
    D.piPlus t = D.E (D.phase t) 0 * D.outerInv * D.E D.P (D.phase t) :=
  D.piPlusPhase_eq _

/-- `Π₊(0) = P₊`. -/
theorem piPlus_zero : D.piPlus 0 = D.projPlus := by
  rw [piPlus, D.phase_zero, D.piPlusPhase_zero]

/-- `Π₊(P) = P₊`. -/
theorem piPlus_period : D.piPlus D.P = D.projPlus := by
  rw [piPlus, D.phase_period, D.piPlusPhase_zero]

theorem piMinus_zero : D.piMinus 0 = D.projMinus := by
  rw [piMinus, D.piPlus_zero, projPlus, sub_sub_cancel]

theorem piMinus_period : D.piMinus D.P = D.projMinus := by
  rw [piMinus, D.piPlus_period, projPlus, sub_sub_cancel]

/-- **`Π₊(t)` is a projection.** -/
theorem isIdempotentElem_piPlus (t : ℝ) : IsIdempotentElem (D.piPlus t) :=
  D.isIdempotentElem_piPlusPhase (D.phase_nonneg t) (D.phase_le t)

/-- **`Π₋(t)` is a projection.** -/
theorem isIdempotentElem_piMinus (t : ℝ) : IsIdempotentElem (D.piMinus t) :=
  (D.isIdempotentElem_piPlus t).one_sub

theorem piPlus_mul_piMinus (t : ℝ) : D.piPlus t * D.piMinus t = 0 := by
  rw [piMinus, mul_sub, mul_one, (D.isIdempotentElem_piPlus t).eq, sub_self]

theorem piMinus_mul_piPlus (t : ℝ) : D.piMinus t * D.piPlus t = 0 := by
  rw [piMinus, sub_mul, one_mul, (D.isIdempotentElem_piPlus t).eq, sub_self]

theorem piPlus_add_piMinus (t : ℝ) : D.piPlus t + D.piMinus t = 1 := by
  rw [piMinus, add_sub_cancel]

/-- **Intertwining** `E(τ,s) Π₊(s) = Π₊(τ) E(τ,s)` for `τ ≥ s`. -/
theorem E_mul_piPlus {s τ : ℝ} (hsτ : s ≤ τ) :
    D.E τ s * D.piPlus s = D.piPlus τ * D.E τ s := by
  have hτ := D.index_mul_add_phase τ
  have hs := D.index_mul_add_phase s
  have hn : (((D.index τ - D.index s).toNat : ℤ) : ℝ) = (D.index τ : ℝ) - D.index s := by
    rw [Int.toNat_of_nonneg (sub_nonneg.2 (D.index_le_index hsτ))]
    push_cast; ring
  rw [Int.cast_natCast] at hn
  have hφθ : D.phase s ≤ ((D.index τ - D.index s).toNat : ℝ) * D.P + D.phase τ := by
    rw [hn]; nlinarith
  rw [D.E_eq_phase hsτ, piPlus, piPlus,
    D.E_mul_piPlusPhase _ (D.phase_mem τ) (D.phase_mem s) hφθ]

/-- **Intertwining** `E(τ,s) Π₋(s) = Π₋(τ) E(τ,s)` for `τ ≥ s`. -/
theorem E_mul_piMinus {s τ : ℝ} (hsτ : s ≤ τ) :
    D.E τ s * D.piMinus s = D.piMinus τ * D.E τ s := by
  rw [piMinus, piMinus, mul_sub, sub_mul, mul_one, one_mul, D.E_mul_piPlus hsτ]

/-! ### Integer powers of `ℳ₊` -/

/-- `ℳ₊ⁿ` for `n ∈ ℤ`. -/
def zpowPlus (n : ℤ) : D.exterior →L[ℂ] D.exterior :=
  ((D.unitPlus ^ n : (D.exterior →L[ℂ] D.exterior)ˣ) : D.exterior →L[ℂ] D.exterior)

theorem zpowPlus_add (a b : ℤ) : D.zpowPlus (a + b) = D.zpowPlus a * D.zpowPlus b := by
  rw [zpowPlus, zpowPlus, zpowPlus, zpow_add, Units.val_mul]

theorem zpowPlus_zero : D.zpowPlus 0 = 1 := by
  rw [zpowPlus, zpow_zero, Units.val_one]

theorem zpowPlus_natCast (n : ℕ) : D.zpowPlus n = D.monodromyPlus ^ n := by
  rw [zpowPlus, zpow_natCast, Units.val_pow_eq_pow_val, val_unitPlus]

theorem zpowPlus_neg_natCast (n : ℕ) : D.zpowPlus (-(n : ℤ)) = D.monodromyPlusInv ^ n := by
  rw [zpowPlus, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, val_unitPlus_inv]

/-! ### The exterior evolution -/

/-- The two-sided exterior evolution `E₊(τ, s) Π₊(s) = F_θ ℳ₊^{k-l} G_φ`, for `τ = kP + θ`,
`s = lP + φ` with phases `θ, φ ∈ [0, P)`. -/
def extEvol (τ s : ℝ) : X →L[ℂ] X :=
  (D.F (D.phase τ)).comp ((D.zpowPlus (D.index τ - D.index s)).comp (D.G (D.phase s)))

/-- **The phase formula** `E₊(kP + θ, lP + φ) Π₊(φ) = F_θ ℳ₊^{k-l} G_φ`. -/
theorem extEvol_intCast_mul_add (k l : ℤ) {θ φ : ℝ} (hθ : θ ∈ Ico 0 D.P)
    (hφ : φ ∈ Ico 0 D.P) :
    D.extEvol (k * D.P + θ) (l * D.P + φ) * D.piPlus φ =
      (D.F θ).comp ((D.zpowPlus (k - l)).comp (D.G φ)) := by
  rw [D.piPlus_of_mem hφ, extEvol, D.phase_intCast_mul_add k hθ, D.phase_intCast_mul_add l hφ,
    D.index_intCast_mul_add k hθ, D.index_intCast_mul_add l hφ, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
    D.G_comp_piPlusPhase hφ.1 hφ.2.le]

/-- `E₊(τ, s) Π₊(s) = E₊(τ, s)`. -/
theorem extEvol_mul_piPlus (τ s : ℝ) : D.extEvol τ s * D.piPlus s = D.extEvol τ s := by
  rw [extEvol, piPlus, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc, D.G_comp_piPlusPhase (D.phase_nonneg s) (D.phase_le s)]

/-- `Π₊(τ) E₊(τ, s) = E₊(τ, s)`. -/
theorem piPlus_mul_extEvol (τ s : ℝ) : D.piPlus τ * D.extEvol τ s = D.extEvol τ s := by
  rw [extEvol, piPlus, ContinuousLinearMap.mul_def, ← ContinuousLinearMap.comp_assoc,
    D.piPlusPhase_comp_F (D.phase_nonneg τ) (D.phase_le τ)]

/-- `E₊(τ, s) Π₋(s) = 0`. -/
theorem extEvol_mul_piMinus (τ s : ℝ) : D.extEvol τ s * D.piMinus s = 0 := by
  rw [piMinus, mul_sub, mul_one, D.extEvol_mul_piPlus, sub_self]

/-- `E₊(τ, τ) = Π₊(τ)`. -/
theorem extEvol_self (τ : ℝ) : D.extEvol τ τ = D.piPlus τ := by
  rw [extEvol, sub_self, zpowPlus_zero, piPlus, piPlusPhase]
  rfl

/-- **Two-sided evolution law** on the exterior fibers: `E₊(τ,r) E₊(r,s) = E₊(τ,s)` for all
`τ, r, s`. -/
theorem extEvol_mul_extEvol (τ r s : ℝ) : D.extEvol τ r * D.extEvol r s = D.extEvol τ s := by
  have h : (D.G (D.phase r)).comp (D.F (D.phase r)) = ContinuousLinearMap.id ℂ D.exterior :=
    D.G_comp_F (D.phase_nonneg r) (D.phase_le r)
  have hz : D.zpowPlus (D.index τ - D.index s) =
      (D.zpowPlus (D.index τ - D.index r)).comp (D.zpowPlus (D.index r - D.index s)) := by
    rw [← ContinuousLinearMap.mul_def, ← zpowPlus_add]
    congr 1
    ring
  rw [extEvol, extEvol, extEvol, ContinuousLinearMap.mul_def, hz]
  simp only [ContinuousLinearMap.comp_assoc]
  congr 2
  rw [← ContinuousLinearMap.comp_assoc (D.G (D.phase r)), h, ContinuousLinearMap.id_comp]

theorem extEvol_add_period (τ s : ℝ) : D.extEvol (τ + D.P) (s + D.P) = D.extEvol τ s := by
  rw [extEvol, extEvol, D.phase_add_period, D.phase_add_period, D.index_add_period,
    D.index_add_period, add_sub_add_right_eq_sub]

/-- `E₊(τ, s)` in `X`-terms for `index τ - index s = n ≥ 0`:
`E₊(τ,s) = E(θ,0) ℳⁿ S E(P,φ)`. -/
theorem extEvol_eq_of_index_sub_eq_natCast {τ s : ℝ} {n : ℕ}
    (h : D.index τ - D.index s = n) :
    D.extEvol τ s = D.E (D.phase τ) 0 * D.monodromy ^ n * D.outerInv * D.E D.P (D.phase s) := by
  ext x
  rw [extEvol, h, zpowPlus_natCast, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, F_apply, coe_monodromyPlus_pow_apply, coe_G_apply]
  simp only [mul_apply_eq_comp]

/-- `E₊(τ, s)` in `X`-terms for `index τ - index s = -m ≤ 0`:
`E₊(τ,s) = E(θ,0) S^{m+1} E(P,φ)`. -/
theorem extEvol_eq_of_index_sub_eq_neg {τ s : ℝ} {m : ℕ}
    (h : D.index τ - D.index s = -(m : ℤ)) :
    D.extEvol τ s = D.E (D.phase τ) 0 * D.outerInv ^ (m + 1) * D.E D.P (D.phase s) := by
  ext x
  rw [extEvol, h, zpowPlus_neg_natCast, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, F_apply, coe_monodromyPlusInv_pow_apply, coe_G_apply,
    pow_succ]
  simp only [mul_apply_eq_comp]

/-- **Forward agreement**: `E(τ, s) Π₊(s) = E₊(τ, s)` for `τ ≥ s`. -/
theorem E_mul_piPlus_eq_extEvol {s τ : ℝ} (hsτ : s ≤ τ) :
    D.E τ s * D.piPlus s = D.extEvol τ s := by
  have hτ := D.index_mul_add_phase τ
  have hs := D.index_mul_add_phase s
  have hnz : (((D.index τ - D.index s).toNat : ℕ) : ℤ) = D.index τ - D.index s :=
    Int.toNat_of_nonneg (sub_nonneg.2 (D.index_le_index hsτ))
  have hn : (((D.index τ - D.index s).toNat : ℕ) : ℝ) = (D.index τ : ℝ) - D.index s := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hnz
    simp only [Int.cast_natCast, Int.cast_sub] at this
    exact this
  have hφθ : D.phase s ≤ ((D.index τ - D.index s).toNat : ℝ) * D.P + D.phase τ := by
    rw [hn]; nlinarith
  rw [D.extEvol_eq_of_index_sub_eq_natCast hnz.symm, D.E_eq_phase hsτ, D.piPlus_eq]
  calc D.E (((D.index τ - D.index s).toNat : ℝ) * D.P + D.phase τ) (D.phase s) *
        (D.E (D.phase s) 0 * D.outerInv * D.E D.P (D.phase s))
      = (D.E (((D.index τ - D.index s).toNat : ℝ) * D.P + D.phase τ) (D.phase s) *
          D.E (D.phase s) 0) * D.outerInv * D.E D.P (D.phase s) := by simp only [mul_assoc]
    _ = _ := by rw [D.E_mul_E_phase _ (D.phase_nonneg τ) (D.phase_nonneg s) hφθ]

/-- `E(τ, s) Π₊(s) = E₊(τ, s) Π₊(s)` for `τ ≥ s`. -/
theorem E_mul_piPlus_eq_extEvol_mul_piPlus {s τ : ℝ} (hsτ : s ≤ τ) :
    D.E τ s * D.piPlus s = D.extEvol τ s * D.piPlus s := by
  rw [D.extEvol_mul_piPlus, D.E_mul_piPlus_eq_extEvol hsτ]

/-- **Compatibility with the forward evolution**: `E(τ, r) E₊(r, s) = E₊(τ, s)` for `τ ≥ r`
(any `s`). -/
theorem E_mul_extEvol {r τ : ℝ} (hrτ : r ≤ τ) (s : ℝ) :
    D.E τ r * D.extEvol r s = D.extEvol τ s := by
  rw [← D.piPlus_mul_extEvol r s, ← mul_assoc, D.E_mul_piPlus_eq_extEvol hrτ,
    D.extEvol_mul_extEvol]

/-- `E(τ, r) E₊(r, s) Π₊(s) = E₊(τ, s) Π₊(s)` for `τ ≥ r`. -/
theorem E_mul_extEvol_mul_piPlus {r τ : ℝ} (hrτ : r ≤ τ) (s : ℝ) :
    D.E τ r * (D.extEvol r s * D.piPlus s) = D.extEvol τ s * D.piPlus s := by
  rw [D.extEvol_mul_piPlus, D.extEvol_mul_piPlus, D.E_mul_extEvol hrτ]

end PeriodicSplitting

end UnforcedLeray.Infra.PeriodicDichotomy
