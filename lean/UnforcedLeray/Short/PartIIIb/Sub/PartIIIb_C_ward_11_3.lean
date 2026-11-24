import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_3.H4

/-!
# `PartIII-b:C/ward/11/3`: `∂_jY ∈ Y₂` on the young support

Source of record `the November 2 reference manuscript` (73 pages).
`Y = χ_yW_μ + transField` holds at every point with `ϱ > 0` (`wardY_split`, 4203-4214), hence in a
neighbourhood of each young chart point, so `∂_jY = ∂_j(χ_yW_μ) + ∂_j transField` there.  The
analytic leaves (`sep:young` 3633-3648 with `j = 1`, stream majorant 3687-3713, regularity and
measurability) are proved in `Sub/PartIII-b_C_ward_11_3/H1..H4.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Regularity**: `χ_yW_μ` and `transField` are differentiable in `y` where `ϱ > 0` (the
separated-kernel responses are smooth off the source, source 3603-3611, 4203-4214). -/
def WardDYRegular : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
      DifferentiableAt ℝ (wardYoungW ν μ R c χy g τ) y ∧
        DifferentiableAt ℝ (transField ν μ R c χy g τ) y

/-- **`∂_j(χ_yW_μ)` on the young support** (`sep:young` 3633-3648, `p = q = 2`, `b = 1`, `j = 1`,
lift identity 2683-2689; `∂_jχ_y` lives on the annulus, bounded by `D⁻¹` times `W_μ`). -/
def WardDYWYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
      YoungL2Le c ν R C (fun τ => physPd (wardYoungW ν μ R c χy g τ) j) g

/-- **`∂_j transField` on the young support** (stream majorant derivative, 3687-3713, 4202-4216). -/
def WardDYTransYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
      YoungL2Le c ν R C (fun τ => physPd (transField ν μ R c χy g τ) j) g

/-- **Measurability** of the young reading of `∂_jY` for `ageμ c (-3/2)`. -/
def WardDYYoungMeas : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
      AEStronglyMeasurable
        (wardYoungRead ν R (fun τ => physPd (wardY ν μ R c χy g τ) j)) (ageμ c (-3 / 2))

theorem wdy_read_le {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) (hν : 0 < ν)
    (hR : 0 < R) (g : Chart → Ten3) (hg : IsOldL2 c ν g) (hres : ShiftedResolventYoung ν μ R c g)
    (hreg : WardDYRegular) (hc : 0 < c) (hμ : -(1 / 4) < μ) (j : Fin 3) (q : Chart) :
    wardYoungRead ν R (fun τ => physPd (wardY ν μ R c χy g τ) j) q ≤
      wardYoungRead ν R (fun τ => physPd (wardYoungW ν μ R c χy g τ) j) q +
        wardYoungRead ν R (fun τ => physPd (transField ν μ R c χy g τ) j) q := by
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  unfold wardYoungRead
  by_cases hq : q ∈ wardYoungSet ν
  · rw [indicator_of_mem hq, indicator_of_mem hq, indicator_of_mem hq]
    simp only
    by_cases hs : 0 < q.1
    · have hϱ : 0 < ϱ (NearInst.chartY R q) := by
        rw [wyl_ϱ_chartY hR hs]
        exact div_pos hR (Real.sqrt_pos.mpr hs)
      set τ := NearInst.chartTau R q
      set y := NearInst.chartY R q
      have hev : wardY ν μ R c χy g τ =ᶠ[𝓝 y]
          (wardYoungW ν μ R c χy g τ + transField ν μ R c χy g τ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_ϱ).mem_nhds hϱ] with z hz
        exact wardY_split hχ hν.le hres τ hz
      obtain ⟨h1, h2⟩ := hreg ν μ R c χy hχy hν hR hc hμ g hg τ y hϱ
      have : physPd (wardY ν μ R c χy g τ) j y =
          physPd (wardYoungW ν μ R c χy g τ) j y + physPd (transField ν μ R c χy g τ) j y := by
        unfold physPd
        rw [hev.fderiv_eq]
        have e := fderiv_add h1 h2
        rw [e]
        rfl
      rw [this, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.2 (Real.sqrt_nonneg _))
    · have h0 : Real.sqrt q.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hs)
      simp [h0]
  · rw [indicator_of_notMem hq, indicator_of_notMem hq, indicator_of_notMem hq]
    simp

theorem wardDYYoungL2_of (hreg : WardDYRegular) (hW : WardDYWYoungL2) (hT : WardDYTransYoungL2)
    (hM : WardDYYoungMeas) : WardDYYoungL2 := by
  intro ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C1, hC1⟩ := hW ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C2, hC2⟩ := hT ν μ R c χy hχy hν hR hc hμ
  refine ⟨max C1 0 + max C2 0, fun g hg j => ?_⟩
  obtain ⟨hW1, hW2⟩ := hC1 g hg j
  obtain ⟨hT1, hT2⟩ := hC2 g hg j
  have hres : ShiftedResolventYoung ν μ R c g :=
    wardYShiftedRes_proved ν μ R c g hν hR hc hμ hg
  refine ⟨hM ν μ R c χy hχy hν hR hc hμ g hg j, ?_⟩
  have hle : eLpNorm (wardYoungRead ν R (fun τ => physPd (wardY ν μ R c χy g τ) j)) 2
        (ageμ c (-3 / 2)) ≤
      eLpNorm (fun q => wardYoungRead ν R (fun τ => physPd (wardYoungW ν μ R c χy g τ) j) q +
        wardYoungRead ν R (fun τ => physPd (transField ν μ R c χy g τ) j) q) 2
        (ageμ c (-3 / 2)) := by
    refine eLpNorm_mono_real (fun q => ?_)
    rw [Real.norm_of_nonneg (wyl_youngRead_nonneg ν R _ q)]
    exact wdy_read_le hχy hν hR g hg hres hreg hc hμ j q
  refine le_trans hle (le_trans (eLpNorm_add_le hW1 hT1 (by norm_num : (1 : ENNReal) ≤ 2)) ?_)
  have hW' := le_trans hW2
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left C1 0)) (eLpNorm g 2 (ageμ c (-1 / 2))))
  have hT' := le_trans hT2
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left C2 0)) (eLpNorm g 2 (ageμ c (-1 / 2))))
  calc _ ≤ ENNReal.ofReal (max C1 0) * eLpNorm g 2 (ageμ c (-1 / 2)) +
        ENNReal.ofReal (max C2 0) * eLpNorm g 2 (ageμ c (-1 / 2)) := add_le_add hW' hT'
    _ = ENNReal.ofReal (max C1 0 + max C2 0) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
        rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), add_mul]

theorem wardDYRegular_proved : WardDYRegular :=
  fun _ν _μ _R _c _χy hχy hν hR hc hμ _g hg τ _y hy =>
    ⟨w113_wardYoungW_diffAt hχy hν hR hc hμ hg τ hy,
     w113_transField_diffAt hχy hν hR hc hμ hg τ hy⟩

theorem wardDYWYoungL2_proved : WardDYWYoungL2 := w113_wardDYWYoungL2

theorem wardDYTransYoungL2_proved : WardDYTransYoungL2 := w113_wardDYTransYoungL2

theorem wardDYYoungMeas_proved : WardDYYoungMeas := w113_wardDYYoungMeas

/-- **`∂_jY ∈ Y₂` on the young support** (`PartIII-b:C/ward/11/3`, source 4203-4214, 5225-5235). -/
theorem wardDYYoungL2_proved : WardDYYoungL2 :=
  wardDYYoungL2_of wardDYRegular_proved wardDYWYoungL2_proved
    wardDYTransYoungL2_proved wardDYYoungMeas_proved

end UnforcedLeray.Short.PartIIIb.Concrete
end
