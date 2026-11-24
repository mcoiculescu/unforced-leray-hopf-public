import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_4

/-!
# `SFCZero` (zero entrance) for the classical representative of `R₀ g`

Source of record `the November 2 reference manuscript` 3426-3430, 1650-1656:
the representative `b` equals `R₀ g` almost everywhere, and `R₀ g ∈ Hsp c`, so the local
`L²(ageμ c (-3/2))` integral over the strip `Ioo 0 1 × univ` is finite (it is bounded by the
whole-space integral, which equals `‖R₀ g‖²` by `HspNormLintegral`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- The pointwise norm of the complexified field is the norm of the real field. -/
theorem vnorm2_velC_norm (f : Chart → Merid) (p : Chart) :
    vnorm2 (NearInst.velC f p) = ‖f p‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold vnorm2 NearInst.velC
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  show ‖((f p).ofLp i : ℂ)‖ ^ 2 = ‖(f p).ofLp i‖ ^ 2
  rw [Complex.norm_real]

/-- The `L²` norm of `u : Hsp c` is the lintegral of the squared pointwise norm of its complexified
field (from `HspNormLintegral` against the zero element). -/
theorem lintegral_velC_hsp (c : ℝ) (u : Hsp c) :
    ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC u p) ^ 2) ∂(ageμ c (-3 / 2)) =
      ENNReal.ofReal (‖u‖ ^ 2) := by
  have h := hspNormLintegral c u 0
  rw [sub_zero] at h
  rw [← h]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 2)) (p := 2)
    (μ := ageμ c (-3 / 2))] with p hp
  rw [Pi.zero_apply] at hp
  have hv : NearInst.velC (⇑(0 : Hsp c)) p = 0 := by
    funext i
    have h1 : (⇑(0 : Hsp c) : Chart → Merid) p = 0 := hp
    unfold NearInst.velC
    rw [h1]
    simp
  rw [hv, sub_zero]

/-- **Z** Zero entrance: the classical representative is square integrable on a strip
`(0, δ) × cell` (source 3426-3430). -/
theorem sfcZero : SFCZero := by
  intro c ν μ hc R0 g _hctx b _hb hbe
  refine ⟨1, one_pos, ?_⟩
  calc ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 1 ×ˢ univ))
      ≤ ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2)) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC (R0 g) p) ^ 2) ∂(ageμ c (-3 / 2)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hbe] with p hp
        rw [hp]
    _ = ENNReal.ofReal (‖R0 g‖ ^ 2) := lintegral_velC_hsp c (R0 g)
    _ < ⊤ := ENNReal.ofReal_lt_top

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
