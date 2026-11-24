import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5

/-!
# Linearity of `convY` in the kernel

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480.  `convY (κ₁ - κ₂) Θ = convY κ₁ Θ - convY κ₂ Θ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem convY_integrable_of_kerOK (κ : Space → ℝ) (hκ : KerOK κ) (Θ : ℝ × Space → CVec3)
    (hΘ : Continuous Θ) (x : ℝ × Space) :
    Integrable (fun z : Space => (κ z : ℂ) • Θ (x.1, x.2 - z)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp hκ.1.continuous).smul
      (hΘ.comp (continuous_const.prodMk (continuous_const.sub continuous_id)))
  · exact (hκ.2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).smul_right

theorem convSub : UnforcedLeray.Short.PartIIIb.Concrete.ConvSub := by
  intro P κ₁ κ₂ Θ h1 h2 hΘ
  funext x
  unfold convY
  rw [← integral_sub (convY_integrable_of_kerOK κ₁ h1 Θ hΘ.smooth.continuous x)
    (convY_integrable_of_kerOK κ₂ h2 Θ hΘ.smooth.continuous x)]
  congr 1
  funext z
  simp only [Complex.ofReal_sub, sub_smul]

end UnforcedLeray.Short.PartIIIb.Concrete
