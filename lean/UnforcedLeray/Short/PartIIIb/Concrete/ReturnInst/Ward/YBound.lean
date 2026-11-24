import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9.L2

/-!
# `L²` bound of `Y = D_{μ+1}X` on the young support (`PartIII-b:C/ward/9`; source 4187-4216,
3631-3713, 4306-4311, 2683-2689)

Source of record: `the November 2 reference manuscript` (73 pages).

* `wardYBound_of : WardYYoungL2 → WardYBound` (the change of measure and the young support).
* `wardYYoungL2_proved : WardYYoungL2`, from the four leaves `wardYShiftedRes_proved`,
  `wardYWYoungL2_proved`, `wardYTransYoungL2_proved`, `wardYYoungMeas_proved`, via `wardY_split`
  (source 4203-4214) pointwise on the young chart region.
* `wardYBound_proved : WardYBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **(C)** The chart coefficient of `Y` is dominated by its young chart reading (source
4306-4311). -/
theorem wyb_coefOf_le {ν μ R c : ℝ} {χy : ℝ → ℝ} (hν : 0 < ν) (hR : 0 < R)
    (hχy : IsYoungCutoff χy) (g : Chart → Ten3) (q : Chart) :
    ‖coefOf R (wardY ν μ R c χy g) q‖ ≤ wardYoungRead ν R (wardY ν μ R c χy g) q := by
  refine wyl_coefOf_le (ν := ν) (wyl_youngRead_nonneg ν R _) (fun q hq => ?_)
    (fun q _ hq => le_of_eq (wyl_youngRead_of_young _ hq).symm) q
  exact (wyl_Y_zero_nhds (μ := μ) (c := c) hν hR hχy g hq _).self_of_nhds

/-- **`WardYBound` from the young `Y₂` bound of `Y`** (source 4194-4196, 4202-4216, 4306-4311,
2683-2689). -/
theorem wardYBound_of (hY : WardYYoungL2) : WardYBound := by
  intro ν μ R c γ χy hχy hν hR hc hμ
  obtain ⟨C, hC⟩ := hY ν μ R c χy hχy hν hR hc hμ
  set KA : ℝ := Real.sqrt (Real.pi * Real.exp (2 * |γ| / ν)) with hKA
  refine ⟨KA * max C 0, fun g hg => ?_⟩
  have b := wyl_bd_of_young (hC g hg)
  have hzero : ∀ q : Chart, 1 < ν * q.1 → coefOf R (wardY ν μ R c χy g) q = 0 :=
    fun q hq => (wardYoungPointwise (μ := μ) (c := c) (fun _ _ => 0) hν hR hχy g q hq).1
  calc eLpNorm (coefOf R (wardY ν μ R c χy g)) 2 (bodyMeasure c γ ν)
      ≤ ENNReal.ofReal KA * eLpNorm (coefOf R (wardY ν μ R c χy g)) 2 (ageμ c (-3 / 2)) :=
        wyl_eLpNorm_body_le c γ hν hzero
    _ ≤ ENNReal.ofReal KA * eLpNorm (wardYoungRead ν R (wardY ν μ R c χy g)) 2
          (ageμ c (-3 / 2)) :=
        mul_le_mul' le_rfl (eLpNorm_mono_real (wyb_coefOf_le hν hR hχy g))
    _ ≤ ENNReal.ofReal KA * (ENNReal.ofReal (max C 0) * eLpNorm g 2 (ageμ c (-1 / 2))) :=
        mul_le_mul' le_rfl b.2
    _ = ENNReal.ofReal (KA * max C 0) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-- The young chart reading is subadditive in the field. -/
theorem wyY_youngRead_add_le (ν R : ℝ) (F G : ℝ → Space → Space) (q : Chart) :
    wardYoungRead ν R (fun τ y => F τ y + G τ y) q ≤
      wardYoungRead ν R F q + wardYoungRead ν R G q := by
  unfold wardYoungRead
  by_cases hq : q ∈ wardYoungSet ν
  · rw [indicator_of_mem hq, indicator_of_mem hq, indicator_of_mem hq]
    simp only
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.2 (Real.sqrt_nonneg _))
  · rw [indicator_of_notMem hq, indicator_of_notMem hq, indicator_of_notMem hq]
    simp

/-- Pointwise split of the young chart reading of `wardY` (source 4203-4214, valid on the
young region by `ShiftedResolventYoung`). -/
theorem wyY_youngRead_split {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) (hν : 0 < ν)
    (hR : 0 < R) (g : Chart → Ten3) (hres : ShiftedResolventYoung ν μ R c g) :
    wardYoungRead ν R (wardY ν μ R c χy g) =
      wardYoungRead ν R (fun τ y => wardYoungW ν μ R c χy g τ y + transField ν μ R c χy g τ y) := by
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  funext q
  unfold wardYoungRead
  by_cases hq : q ∈ wardYoungSet ν
  · rw [indicator_of_mem hq, indicator_of_mem hq]
    by_cases hs : 0 < q.1
    · have hϱ : 0 < ϱ (NearInst.chartY R q) := by
        rw [wyl_ϱ_chartY hR hs]
        exact div_pos hR (Real.sqrt_pos.mpr hs)
      simp only
      rw [wardY_split hχ hν.le hres _ hϱ]
    · have h0 : Real.sqrt q.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hs)
      simp [h0]
  · rw [indicator_of_notMem hq, indicator_of_notMem hq]

/-- **`WardYYoungL2`**: the young `Y₂` bound of `Y`, from the four leaves (source 4194-4216). -/
theorem wardYYoungL2_diag (hW : WardYWYoungL2) : WardYYoungL2 := by
  intro ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C1, hC1⟩ := hW ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C2, hC2⟩ := wardYTransYoungL2_proved ν μ R c χy hχy hν hR hc hμ
  refine ⟨max C1 0 + max C2 0, fun g hg => ?_⟩
  obtain ⟨hW1, hW2⟩ := hC1 g hg
  obtain ⟨hT1, hT2⟩ := hC2 g hg
  have hres : ShiftedResolventYoung ν μ R c g :=
    wardYShiftedRes_proved ν μ R c g hν hR hc hμ hg
  have hM := wardYYoungMeas_proved ν μ R c χy hχy hν hR hc hμ g hg
  refine ⟨hM, ?_⟩
  rw [wyY_youngRead_split hχy hν hR g hres]
  have hle : eLpNorm (wardYoungRead ν R (fun τ y => wardYoungW ν μ R c χy g τ y +
        transField ν μ R c χy g τ y)) 2 (ageμ c (-3 / 2)) ≤
      eLpNorm (fun q => wardYoungRead ν R (wardYoungW ν μ R c χy g) q +
        wardYoungRead ν R (transField ν μ R c χy g) q) 2 (ageμ c (-3 / 2)) := by
    refine eLpNorm_mono_real (fun q => ?_)
    rw [Real.norm_of_nonneg (wyl_youngRead_nonneg ν R _ q)]
    exact wyY_youngRead_add_le ν R _ _ q
  refine le_trans hle ?_
  have hadd := eLpNorm_add_le hW1 hT1 (by norm_num : (1 : ENNReal) ≤ 2)
  refine le_trans hadd ?_
  have hW : eLpNorm (wardYoungRead ν R (wardYoungW ν μ R c χy g)) 2 (ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (max C1 0) * eLpNorm g 2 (ageμ c (-1 / 2)) :=
    le_trans hW2 (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)
  have hT : eLpNorm (wardYoungRead ν R (transField ν μ R c χy g)) 2 (ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (max C2 0) * eLpNorm g 2 (ageμ c (-1 / 2)) :=
    le_trans hT2 (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)
  calc _ ≤ ENNReal.ofReal (max C1 0) * eLpNorm g 2 (ageμ c (-1 / 2)) +
        ENNReal.ofReal (max C2 0) * eLpNorm g 2 (ageμ c (-1 / 2)) := add_le_add hW hT
    _ = ENNReal.ofReal (max C1 0 + max C2 0) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
        rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), add_mul]

/-- **`WardYYoungL2`** (source 4203-4214): the young-chart `L²` bound of `Y`, from the leaf
`wardYWYoungL2_proved` (`Sub/PartIII-b_C_ward_9/L2.lean`) by `wardYYoungL2_diag`. -/
theorem wardYYoungL2_proved : WardYYoungL2 := wardYYoungL2_diag wardYWYoungL2_proved

/-- **`PartIII-b:C/ward/9`**: the `L²` bound of `Y = D_{μ+1}X` on the young support. -/
theorem wardYBound_proved : WardYBound := wardYBound_of wardYYoungL2_proved

end UnforcedLeray.Short.PartIIIb.Concrete
