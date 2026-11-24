import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.EBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs

/-!
# Definitions and `WardELipschitzL` assembly for `PartIII-b:C/cont/WE`

Source of record: `the November 2 reference manuscript` (73 pages), lines
4161-4303 (`subsec:ward`), 5196-5260 (`prop:actual-body`), 5684-5685, 5701-5704, 5918-5920.

This file defines the `μ`-Lipschitz young-support leaves for `wardX` and `wardY` on compact
intervals `[a, b] ⊂ (0, 1/4)` (`WardDXSubYoungL2`, `WardD2XSubYoungL2`, `WardDYSubYoungL2`,
`WardDXSubYoungSup`) and assembles them with `WardBgBoundL` to prove `WardELipschitzL`, the
`μ`-Lipschitz counterpart of `WardEBoundL` (`ReturnInst/Ward/EBound.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. `μ`-Lipschitz young-support leaves for `wardE` -/

/-- **`μ`-Lipschitz `Y₂` bound of `DX_μ - DX_{μ'}` on the young support**
(source 3633-3648 `sep:young`, 3687-3713, 4194-4196, 5212-5235): on any compact window
`[a, b] ⊂ (0, 1/4)`, the spatial partials `∂_j X_μ - ∂_j X_{μ'}` are `μ`-Lipschitz in `Y₂` on
the young support against the old source norm `‖g‖_{L²(s^{-1/2}dς)}`. -/
def WardDXSubYoungL2 : Prop :=
  ∀ (a b ν R c : ℝ) (χy : ℝ → ℝ),
    0 < a → b < 1 / 4 → IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c →
    ∃ C : ℝ, ∀ μ ∈ Icc a b, ∀ μ' ∈ Icc a b, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ j : Fin 3,
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y => physPd (wardX ν μ R c χy g τ) j y - physPd (wardX ν μ' R c χy g τ) j y) g

/-- **`μ`-Lipschitz `Y₂` bound of `D²X_μ - D²X_{μ'}` on the young support**
(source 3633-3648 `sep:young` with `j = 2`, 4194-4196, 5225-5235): on any compact window
`[a, b] ⊂ (0, 1/4)`, the second spatial partials `∂_j ∂_l X_μ - ∂_j ∂_l X_{μ'}` are
`μ`-Lipschitz in `Y₂` on the young support against `‖g‖_{L²(s^{-1/2}dς)}`. -/
def WardD2XSubYoungL2 : Prop :=
  ∀ (a b ν R c : ℝ) (χy : ℝ → ℝ),
    0 < a → b < 1 / 4 → IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c →
    ∃ C : ℝ, ∀ μ ∈ Icc a b, ∀ μ' ∈ Icc a b, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ j l : Fin 3,
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y =>
            physPd2 (wardX ν μ R c χy g τ) j l y - physPd2 (wardX ν μ' R c χy g τ) j l y) g

/-- **`μ`-Lipschitz `Y₂` bound of `DY_μ - DY_{μ'}` on the young support**
(source 3633-3648 `sep:young` with `j = 1`, 4202-4216, 5212-5224): on any compact window
`[a, b] ⊂ (0, 1/4)`, the spatial partials `∂_k Y_μ - ∂_k Y_{μ'}` are `μ`-Lipschitz in `Y₂` on
the young support against `‖g‖_{L²(s^{-1/2}dς)}`. -/
def WardDYSubYoungL2 : Prop :=
  ∀ (a b ν R c : ℝ) (χy : ℝ → ℝ),
    0 < a → b < 1 / 4 → IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c →
    ∃ C : ℝ, ∀ μ ∈ Icc a b, ∀ μ' ∈ Icc a b, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ k : Fin 3,
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y => physPd (wardY ν μ R c χy g τ) k y - physPd (wardY ν μ' R c χy g τ) k y) g

/-- **`μ`-Lipschitz `L^∞` bound of `DX_μ - DX_{μ'}` on the young support**
(source 3603-3629 `sep:kernel`, 4178-4186, 5238-5244): on any compact window `[a, b] ⊂ (0, 1/4)`,
on `R√ν ≤ ϱ y` the old source is at distance `≥ c_0 R√ν > 0`, so `∂_j X_μ - ∂_j X_{μ'}` is
pointwise bounded by `C |μ - μ'| ‖g‖_{L²(s^{-1/2}dς)}`. -/
def WardDXSubYoungSup : Prop :=
  ∀ (a b ν R c : ℝ) (χy : ℝ → ℝ),
    0 < a → b < 1 / 4 → IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c →
    ∃ C : ℝ, ∀ μ ∈ Icc a b, ∀ μ' ∈ Icc a b, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y → ∀ j : Fin 3,
        ‖physPd (wardX ν μ R c χy g τ) j y - physPd (wardX ν μ' R c χy g τ) j y‖ ≤
          C * |μ - μ'| * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal

/-- **`μ`-Lipschitz bound of the chart-read Ward residual `wardE`** in `L²(srcMeasure c)` under
`WardBgBoundL` (source 5196-5260, 5684-5685, 5701-5704). -/
def WardELipschitzL : Prop :=
  ∀ (a b ν R c M : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    0 < a → b < 1 / 4 → IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c →
    WardBgBoundL R ν c U p M →
    ∃ C : ℝ, ∀ μ ∈ Icc a b, ∀ μ' ∈ Icc a b, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      eLpNorm (coefOf R (wardE ν μ R c χy U p g) - coefOf R (wardE ν μ' R c χy U p g)) 2
          (srcMeasure c) ≤
        ENNReal.ofReal (C * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2))

/-! ## 2. Pointwise algebraic difference bounds for `wardE` -/

namespace WardELipAux

theorem wo_coefOf_sub (R : ℝ) (F G : ℝ → Space → Space) :
    coefOf R (fun τ y => F τ y - G τ y) = coefOf R F - coefOf R G := by
  funext p
  ext i
  fin_cases i <;> simp [coefOf] <;> ring

theorem web_fderiv_sub_le {M : ℝ} {u Y₁ Y₂ : Space → Space} {y : Space} (hU : ‖u y‖ ≤ M) :
    ‖fderiv ℝ Y₁ y (u y) - fderiv ℝ Y₂ y (u y)‖ ≤
      M * ∑ k : Fin 3, ‖physPd Y₁ k y - physPd Y₂ k y‖ := by
  rw [wyl_fderiv_apply_eq Y₁, wyl_fderiv_apply_eq Y₂, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((wyl_abs_apply_le _ k).trans hU) (norm_nonneg _)

theorem web_cdiff_sub_le {M : ℝ} {u X₁ X₂ : Space → Space} {y : Space}
    (hdU : ∀ j : Fin 3, ‖physPd u j y‖ ≤ M) (hd2U : ∀ j l : Fin 3, ‖physPd2 u j l y‖ ≤ M) :
    ‖physCdiff u X₁ y - physCdiff u X₂ y‖ ≤
      M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X₁ j l y - physPd2 X₂ j l y‖ +
        M * ∑ j : Fin 3, ∑ _l : Fin 3, ‖physPd X₁ j y - physPd X₂ j y‖ := by
  unfold physCdiff
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  have heq : (physPd u j y l • physPd2 X₁ j l y - physPd X₁ j y l • physPd2 u j l y) -
      (physPd u j y l • physPd2 X₂ j l y - physPd X₂ j y l • physPd2 u j l y) =
      physPd u j y l • (physPd2 X₁ j l y - physPd2 X₂ j l y) -
        (physPd X₁ j y - physPd X₂ j y) l • physPd2 u j l y := by
    simp only [smul_sub, PiLp.sub_apply, sub_smul]
    abel
  rw [heq]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((wyl_abs_apply_le _ l).trans (hdU j)) (norm_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs, mul_comm M]
    exact mul_le_mul (wyl_abs_apply_le _ l) (hd2U j l) (norm_nonneg _) (norm_nonneg _)

theorem web_uud2_sub_le {M : ℝ} {u X₁ X₂ : Space → Space} {y : Space} (hU : ‖u y‖ ≤ M) :
    ‖physUUD2 u X₁ y - physUUD2 u X₂ y‖ ≤
      M * M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X₁ j l y - physPd2 X₂ j l y‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hU
  unfold physUUD2
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact mul_le_mul ((wyl_abs_apply_le _ j).trans hU) ((wyl_abs_apply_le _ l).trans hU)
    (abs_nonneg _) hM

theorem web_dxp_sub_le {A : ℝ} {X₁ X₂ : Space → Space} {q : Space → ℝ} {y : Space}
    (hA : ∀ j : Fin 3, ‖physPd X₁ j y - physPd X₂ j y‖ ≤ A) :
    ‖physDXp X₁ q y - physDXp X₂ q y‖ ≤ 18 * A * ‖physGrad q y‖ := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine (wyl_norm_le_sum_abs _).trans ?_
  have hi : ∀ i : Fin 3, |(physDXp X₁ q y - physDXp X₂ q y) i| ≤ 6 * A * ‖physGrad q y‖ := by
    intro i
    have hcomp : (physDXp X₁ q y - physDXp X₂ q y) i = ∑ j : Fin 3,
        ((physPd X₁ j y - physPd X₂ j y) i + (physPd X₁ i y - physPd X₂ i y) j) *
          physGrad q y j := by
      simp only [PiLp.sub_apply, physDXp, physGrad, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hcomp]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j : Fin 3,
        |((physPd X₁ j y - physPd X₂ j y) i + (physPd X₁ i y - physPd X₂ i y) j) *
          physGrad q y j| ≤ 2 * A * ‖physGrad q y‖ := by
      intro j
      rw [abs_mul]
      refine mul_le_mul ?_ (wyl_abs_apply_le _ j) (abs_nonneg _) (by positivity)
      refine (abs_add_le _ _).trans ?_
      have h1 := (wyl_abs_apply_le (physPd X₁ j y - physPd X₂ j y) i).trans (hA j)
      have h2 := (wyl_abs_apply_le (physPd X₁ i y - physPd X₂ i y) j).trans (hA i)
      linarith
    calc ∑ j : Fin 3,
          |((physPd X₁ j y - physPd X₂ j y) i + (physPd X₁ i y - physPd X₂ i y) j) *
            physGrad q y j|
        ≤ ∑ _j : Fin 3, 2 * A * ‖physGrad q y‖ := Finset.sum_le_sum fun j _ => hj j
      _ = 6 * A * ‖physGrad q y‖ := by simp [Finset.sum_const]; ring
  calc ∑ i : Fin 3, |(physDXp X₁ q y - physDXp X₂ q y) i|
      ≤ ∑ _i : Fin 3, 6 * A * ‖physGrad q y‖ := Finset.sum_le_sum fun i _ => hi i
    _ = 18 * A * ‖physGrad q y‖ := by simp [Finset.sum_const]; ring

/-- **The four-term residual difference on the young support** (source 4276-4280, 5225-5260). -/
theorem web_sub_pointwise {M A ν : ℝ} (hν : 0 ≤ ν) {u X₁ X₂ Y₁ Y₂ : Space → Space}
    {q : Space → ℝ} {y : Space} (hU : ‖u y‖ ≤ M) (hdU : ∀ j : Fin 3, ‖physPd u j y‖ ≤ M)
    (hd2U : ∀ j l : Fin 3, ‖physPd2 u j l y‖ ≤ M)
    (hA : ∀ j : Fin 3, ‖physPd X₁ j y - physPd X₂ j y‖ ≤ A) :
    ‖((2 : ℝ) • fderiv ℝ Y₁ y (u y) - (2 * ν) • physCdiff u X₁ y + physUUD2 u X₁ y -
        physDXp X₁ q y) -
      ((2 : ℝ) • fderiv ℝ Y₂ y (u y) - (2 * ν) • physCdiff u X₂ y + physUUD2 u X₂ y -
        physDXp X₂ q y)‖ ≤
      2 * M * ∑ k : Fin 3, ‖physPd Y₁ k y - physPd Y₂ k y‖ +
        2 * ν * (M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X₁ j l y - physPd2 X₂ j l y‖ +
          M * ∑ j : Fin 3, ∑ _l : Fin 3, ‖physPd X₁ j y - physPd X₂ j y‖) +
        M * M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X₁ j l y - physPd2 X₂ j l y‖ +
        18 * A * ‖physGrad q y‖ := by
  have h1 : ‖(2 : ℝ) • fderiv ℝ Y₁ y (u y) - (2 : ℝ) • fderiv ℝ Y₂ y (u y)‖ ≤
      2 * M * ∑ k : Fin 3, ‖physPd Y₁ k y - physPd Y₂ k y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
    exact mul_le_mul_of_nonneg_left (web_fderiv_sub_le hU) (by norm_num)
  have h2 : ‖(2 * ν) • physCdiff u X₁ y - (2 * ν) • physCdiff u X₂ y‖ ≤
      2 * ν * (M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X₁ j l y - physPd2 X₂ j l y‖ +
        M * ∑ j : Fin 3, ∑ _l : Fin 3, ‖physPd X₁ j y - physPd X₂ j y‖) := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (web_cdiff_sub_le hdU hd2U) (by positivity)
  have h3 := web_uud2_sub_le (X₁ := X₁) (X₂ := X₂) hU
  have h4 := web_dxp_sub_le (q := q) hA
  have heq : ((2 : ℝ) • fderiv ℝ Y₁ y (u y) - (2 * ν) • physCdiff u X₁ y + physUUD2 u X₁ y -
        physDXp X₁ q y) -
      ((2 : ℝ) • fderiv ℝ Y₂ y (u y) - (2 * ν) • physCdiff u X₂ y + physUUD2 u X₂ y -
        physDXp X₂ q y) =
      ((2 : ℝ) • fderiv ℝ Y₁ y (u y) - (2 : ℝ) • fderiv ℝ Y₂ y (u y)) -
        ((2 * ν) • physCdiff u X₁ y - (2 * ν) • physCdiff u X₂ y) +
        (physUUD2 u X₁ y - physUUD2 u X₂ y) -
        (physDXp X₁ q y - physDXp X₂ q y) := by abel
  rw [heq]
  calc ‖((2 : ℝ) • fderiv ℝ Y₁ y (u y) - (2 : ℝ) • fderiv ℝ Y₂ y (u y)) -
        ((2 * ν) • physCdiff u X₁ y - (2 * ν) • physCdiff u X₂ y) +
        (physUUD2 u X₁ y - physUUD2 u X₂ y) -
        (physDXp X₁ q y - physDXp X₂ q y)‖
      ≤ ‖((2 : ℝ) • fderiv ℝ Y₁ y (u y) - (2 : ℝ) • fderiv ℝ Y₂ y (u y)) -
          ((2 * ν) • physCdiff u X₁ y - (2 * ν) • physCdiff u X₂ y) +
          (physUUD2 u X₁ y - physUUD2 u X₂ y)‖ +
          ‖physDXp X₁ q y - physDXp X₂ q y‖ := norm_sub_le _ _
    _ ≤ ‖((2 : ℝ) • fderiv ℝ Y₁ y (u y) - (2 : ℝ) • fderiv ℝ Y₂ y (u y)) -
          ((2 * ν) • physCdiff u X₁ y - (2 * ν) • physCdiff u X₂ y)‖ +
          ‖physUUD2 u X₁ y - physUUD2 u X₂ y‖ +
          ‖physDXp X₁ q y - physDXp X₂ q y‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖(2 : ℝ) • fderiv ℝ Y₁ y (u y) - (2 : ℝ) • fderiv ℝ Y₂ y (u y)‖ +
          ‖(2 * ν) • physCdiff u X₁ y - (2 * ν) • physCdiff u X₂ y‖ +
          ‖physUUD2 u X₁ y - physUUD2 u X₂ y‖ +
          ‖physDXp X₁ q y - physDXp X₂ q y‖ :=
        add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ _ := by linarith

end WardELipAux

open WardELipAux

/-! ## 3. Assembly of `WardELipschitzL` -/

/-- **`WardELipschitzL` holds** given the four `μ`-Lipschitz young-support leaves
(`WardDXSubYoungL2`, `WardD2XSubYoungL2`, `WardDYSubYoungL2`, `WardDXSubYoungSup`). -/
theorem wardELipschitzL_of (hX : WardDXSubYoungL2) (hX2 : WardD2XSubYoungL2)
    (hDY : WardDYSubYoungL2) (hsup : WardDXSubYoungSup) : WardELipschitzL := by
  intro a b ν R c M χy U p ha hb hχy hν hR hc hbg
  obtain ⟨C1, hC1⟩ := hX a b ν R c χy ha hb hχy hν hR hc
  obtain ⟨C2, hC2⟩ := hX2 a b ν R c χy ha hb hχy hν hR hc
  obtain ⟨C3, hC3⟩ := hDY a b ν R c χy ha hb hχy hν hR hc
  obtain ⟨C4, hC4⟩ := hsup a b ν R c χy ha hb hχy hν hR hc
  have hM : 0 ≤ M := by
    set y₀ : Space := WithLp.toLp 2 ![R * Real.sqrt ν, 0, 0]
    have hy : R * Real.sqrt ν ≤ ϱ y₀ := by
      have h0 : y₀ 0 = R * Real.sqrt ν := by simp [y₀]
      have h1 : y₀ 1 = 0 := by simp [y₀]
      unfold ϱ
      rw [h0, h1, show (R * Real.sqrt ν) ^ 2 + (0 : ℝ) ^ 2 = (R * Real.sqrt ν) ^ 2 by ring,
        Real.sqrt_sq (mul_nonneg hR.le (Real.sqrt_nonneg _))]
    exact (norm_nonneg _).trans (hbg.1 0 y₀ hy).1
  set C1' := max C1 0 with hC1'
  set C2' := max C2 0 with hC2'
  set C3' := max C3 0 with hC3'
  set C4' := max C4 0 with hC4'
  have h1' : 0 ≤ C1' := le_max_right _ _
  have h2' : 0 ≤ C2' := le_max_right _ _
  have h3' : 0 ≤ C3' := le_max_right _ _
  have h4' : 0 ≤ C4' := le_max_right _ _
  set K₁ : ℝ := |2 * M| * ∑ _k : Fin 3, C3' +
    |2 * ν| * (|M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C2' + |M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C1') +
    |M * M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C2' with hK₁
  refine ⟨Real.sqrt Real.pi * K₁ + 18 * C4' * M, fun μ hμ μ' hμ' g hg => ?_⟩
  set d : ℝ := |μ - μ'|
  have hd0 : 0 ≤ d := abs_nonneg _
  set N := eLpNorm g 2 (ageμ c (-1 / 2)) with hN
  have hNt : N ≠ ⊤ := hg.memLp.2.ne
  set m := ageμ c (-3 / 2) with hm
  set X₁ := wardX ν μ R c χy g
  set X₂ := wardX ν μ' R c χy g
  set Y₁ := wardY ν μ R c χy g
  set Y₂ := wardY ν μ' R c χy g
  have b1 : ∀ j : Fin 3,
      WylBd m N (wardYoungRead ν R fun τ y => physPd (X₁ τ) j y - physPd (X₂ τ) j y) (C1' * d) :=
    fun j => (wyl_bd_of_young (hC1 μ hμ μ' hμ' g hg j)).mono_K
      (max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0) (mul_nonneg h1' hd0))
  have b2 : ∀ j l : Fin 3,
      WylBd m N (wardYoungRead ν R fun τ y => physPd2 (X₁ τ) j l y - physPd2 (X₂ τ) j l y)
        (C2' * d) :=
    fun j l => (wyl_bd_of_young (hC2 μ hμ μ' hμ' g hg j l)).mono_K
      (max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0) (mul_nonneg h2' hd0))
  have b3 : ∀ k : Fin 3,
      WylBd m N (wardYoungRead ν R fun τ y => physPd (Y₁ τ) k y - physPd (Y₂ τ) k y) (C3' * d) :=
    fun k => (wyl_bd_of_young (hC3 μ hμ μ' hμ' g hg k)).mono_K
      (max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0) (mul_nonneg h3' hd0))
  have t3 := WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => C3' * d)
    (fun _ => mul_nonneg h3' hd0) (fun k _ => b3 k)
  have t2 := WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => ∑ _l : Fin 3, C2' * d)
    (fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg h2' hd0)
    (fun j _ => WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => C2' * d)
      (fun _ => mul_nonneg h2' hd0) (fun l _ => b2 j l))
  have t1 := WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => ∑ _l : Fin 3, C1' * d)
    (fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg h1' hd0)
    (fun j _ => WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => C1' * d)
      (fun _ => mul_nonneg h1' hd0) (fun _ _ => b1 j))
  have s3 : 0 ≤ ∑ _k : Fin 3, C3' * d := Finset.sum_nonneg fun _ _ => mul_nonneg h3' hd0
  have s2 : 0 ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, C2' * d :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg h2' hd0
  have s1 : 0 ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, C1' * d :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg h1' hd0
  have tB := (((t3.const_mul (2 * M)).add (((t2.const_mul M).add (t1.const_mul M)
    (mul_nonneg (abs_nonneg _) s2) (mul_nonneg (abs_nonneg _) s1)).const_mul (2 * ν))
    (mul_nonneg (abs_nonneg _) s3) (mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (abs_nonneg _) s2) (mul_nonneg (abs_nonneg _) s1)))).add
    (t2.const_mul (M * M)) (add_nonneg (mul_nonneg (abs_nonneg _) s3) (mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (abs_nonneg _) s2) (mul_nonneg (abs_nonneg _) s1))))
    (mul_nonneg (abs_nonneg _) s2))
  set B : Chart → ℝ := fun q =>
    2 * M * ∑ k : Fin 3,
        wardYoungRead ν R (fun τ y => physPd (Y₁ τ) k y - physPd (Y₂ τ) k y) q +
      2 * ν * (M * ∑ j : Fin 3, ∑ l : Fin 3,
          wardYoungRead ν R (fun τ y => physPd2 (X₁ τ) j l y - physPd2 (X₂ τ) j l y) q +
        M * ∑ j : Fin 3, ∑ _l : Fin 3,
          wardYoungRead ν R (fun τ y => physPd (X₁ τ) j y - physPd (X₂ τ) j y) q) +
      M * M * ∑ j : Fin 3, ∑ l : Fin 3,
        wardYoungRead ν R (fun τ y => physPd2 (X₁ τ) j l y - physPd2 (X₂ τ) j l y) q
    with hBdef
  have hK₁d : |2 * M| * ∑ _k : Fin 3, C3' * d +
      |2 * ν| * (|M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C2' * d +
        |M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C1' * d) +
      |M * M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C2' * d = K₁ * d := by
    simp only [hK₁, Finset.sum_const, nsmul_eq_mul]
    ring
  have tB' : WylBd m N B (K₁ * d) := hK₁d ▸ tB
  set A : ℝ := C4' * d * N.toReal with hAdef
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg h4' hd0) ENNReal.toReal_nonneg
  set Pp : Chart → ℝ := wardYoungRead ν R (fun τ y => physGrad (p τ) y) with hPp
  have hB0 : ∀ q, 0 ≤ B q := by
    intro q
    have r1 := fun k =>
      wyl_youngRead_nonneg ν R (fun τ y => physPd (Y₁ τ) k y - physPd (Y₂ τ) k y) q
    have r2 := fun j l =>
      wyl_youngRead_nonneg ν R (fun τ y => physPd2 (X₁ τ) j l y - physPd2 (X₂ τ) j l y) q
    have r3 := fun j =>
      wyl_youngRead_nonneg ν R (fun τ y => physPd (X₁ τ) j y - physPd (X₂ τ) j y) q
    have e1 : 0 ≤ ∑ k : Fin 3,
        wardYoungRead ν R (fun τ y => physPd (Y₁ τ) k y - physPd (Y₂ τ) k y) q :=
      Finset.sum_nonneg fun k _ => r1 k
    have e2 : 0 ≤ ∑ j : Fin 3, ∑ l : Fin 3,
        wardYoungRead ν R (fun τ y => physPd2 (X₁ τ) j l y - physPd2 (X₂ τ) j l y) q :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => r2 j l
    have e3 : 0 ≤ ∑ j : Fin 3, ∑ _l : Fin 3,
        wardYoungRead ν R (fun τ y => physPd (X₁ τ) j y - physPd (X₂ τ) j y) q :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => r3 j
    simp only [hBdef]
    have := mul_nonneg hM e2
    have := mul_nonneg hM e3
    have := mul_nonneg (mul_nonneg hM hM) e2
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM) e1
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hν.le)
      (add_nonneg (mul_nonneg hM e2) (mul_nonneg hM e3))
    linarith
  have hP0 : ∀ q, 0 ≤ 18 * A * Pp q := fun q =>
    mul_nonneg (mul_nonneg (by norm_num) hA0) (wyl_youngRead_nonneg _ _ _ q)
  have hpt : ∀ q,
      ‖(coefOf R (wardE ν μ R c χy U p g) - coefOf R (wardE ν μ' R c χy U p g)) q‖ ≤
        B q + 18 * A * Pp q := by
    intro q
    rw [← wo_coefOf_sub]
    refine wyl_coefOf_le (ν := ν) (fun q => add_nonneg (hB0 q) (hP0 q))
      (fun q hq => by
        rw [web_E_zero U p hν hR hχy g hq _, web_E_zero U p hν hR hχy g hq _, sub_self])
      (fun q hs hq => ?_) q
    set τ := NearInst.chartTau R q
    set y := NearInst.chartY R q
    have hy := wyl_young_ϱ hν hR hs hq
    obtain ⟨hU, hdU, hd2U⟩ := hbg.1 τ y hy
    have hAj : ∀ j : Fin 3, ‖physPd (X₁ τ) j y - physPd (X₂ τ) j y‖ ≤ A := fun j =>
      (hC4 μ hμ μ' hμ' g hg τ y hy j).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0) ENNReal.toReal_nonneg)
    have key := web_sub_pointwise (Y₁ := Y₁ τ) (Y₂ := Y₂ τ) (q := p τ) hν.le hU hdU hd2U hAj
    have hi : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    simp only [hBdef, hPp, wyl_youngRead_of_young _ hq]
    calc (Real.sqrt q.1)⁻¹ * ‖wardE ν μ R c χy U p g τ y - wardE ν μ' R c χy U p g τ y‖
        ≤ (Real.sqrt q.1)⁻¹ * (2 * M * ∑ k : Fin 3, ‖physPd (Y₁ τ) k y - physPd (Y₂ τ) k y‖ +
            2 * ν * (M * ∑ j : Fin 3, ∑ l : Fin 3,
                ‖physPd2 (X₁ τ) j l y - physPd2 (X₂ τ) j l y‖ +
              M * ∑ j : Fin 3, ∑ _l : Fin 3, ‖physPd (X₁ τ) j y - physPd (X₂ τ) j y‖) +
            M * M * ∑ j : Fin 3, ∑ l : Fin 3,
              ‖physPd2 (X₁ τ) j l y - physPd2 (X₂ τ) j l y‖ +
            18 * A * ‖physGrad (p τ) y‖) := mul_le_mul_of_nonneg_left key hi
      _ = _ := by
          simp only [← Finset.mul_sum]
          ring
  have hBm : AEStronglyMeasurable B (srcMeasure c) := by
    unfold srcMeasure
    exact tB'.1.smul_measure _
  have hmink := web_eLpNorm_le_add (μ := srcMeasure c) hBm hB0 hP0 hpt
  have hPpe : eLpNorm Pp 2 (srcMeasure c) ≤ ENNReal.ofReal M := by
    have heq : Pp = fun q => ‖({q : Chart | ν * q.1 ≤ 1}.indicator fun q : Chart =>
        (Real.sqrt q.1)⁻¹ • physGrad (p (NearInst.chartTau R q)) (NearInst.chartY R q)) q‖ := by
      funext q
      simp only [hPp, wardYoungRead, wardYoungSet]
      by_cases hq : q ∈ {q : Chart | ν * q.1 ≤ 1}
      · rw [indicator_of_mem hq, indicator_of_mem hq, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      · rw [indicator_of_notMem hq, indicator_of_notMem hq, norm_zero]
    rw [heq, eLpNorm_norm]
    exact hbg.2
  have hAP : eLpNorm (fun q => 18 * A * Pp q) 2 (srcMeasure c) ≤
      ENNReal.ofReal (18 * C4' * M * d) * N := by
    calc eLpNorm (fun q => 18 * A * Pp q) 2 (srcMeasure c)
        = eLpNorm ((18 * A) • Pp) 2 (srcMeasure c) := rfl
      _ = ‖18 * A‖ₑ * eLpNorm Pp 2 (srcMeasure c) := eLpNorm_const_smul _ _ _ _
      _ ≤ ‖18 * A‖ₑ * ENNReal.ofReal M := mul_le_mul' le_rfl hPpe
      _ = ENNReal.ofReal (18 * C4' * M * d) * N := by
          rw [Real.enorm_of_nonneg (by positivity), hAdef, ← ENNReal.ofReal_mul (by positivity)]
          rw [show 18 * (C4' * d * N.toReal) * M = 18 * C4' * M * d * N.toReal by ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hNt]
  have hBs : eLpNorm B 2 (srcMeasure c) ≤ ENNReal.ofReal (Real.sqrt Real.pi * K₁ * d) * N := by
    rw [wyl_eLpNorm_src]
    calc ENNReal.ofReal (Real.sqrt Real.pi) * eLpNorm B 2 (ageμ c (-3 / 2))
        ≤ ENNReal.ofReal (Real.sqrt Real.pi) * (ENNReal.ofReal (K₁ * d) * N) :=
          mul_le_mul' le_rfl tB'.2
      _ = ENNReal.ofReal (Real.sqrt Real.pi * K₁ * d) * N := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc]
  have hK₁0 : 0 ≤ K₁ := by
    simp only [hK₁, Finset.sum_const, nsmul_eq_mul]
    positivity
  calc eLpNorm (coefOf R (wardE ν μ R c χy U p g) - coefOf R (wardE ν μ' R c χy U p g)) 2
        (srcMeasure c)
      ≤ eLpNorm B 2 (srcMeasure c) + eLpNorm (fun q => 18 * A * Pp q) 2 (srcMeasure c) := hmink
    _ ≤ ENNReal.ofReal (Real.sqrt Real.pi * K₁ * d) * N +
          ENNReal.ofReal (18 * C4' * M * d) * N := add_le_add hBs hAP
    _ = ENNReal.ofReal ((Real.sqrt Real.pi * K₁ + 18 * C4' * M) * d) * N := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
end
