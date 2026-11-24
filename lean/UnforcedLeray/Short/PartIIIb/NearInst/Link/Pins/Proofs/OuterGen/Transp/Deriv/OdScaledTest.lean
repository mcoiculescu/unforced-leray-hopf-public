import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem odScaledTest : OD_ScaledTest := by
  intro p Φ hΦ
  have hε : 0 < p.ε := p.ε_pos
  refine ⟨?_, ?_, ?_⟩
  · exact hΦ.smooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul p.ε⁻¹))
  · intro τ y
    exact hΦ.periodic _ _
  · obtain ⟨R, hR⟩ := hΦ.bounded_support
    refine ⟨p.ε * R, fun τ y hy => ?_⟩
    have h1 : R < p.ε⁻¹ * ‖y‖ := by
      have h2 := mul_lt_mul_of_pos_left hy (inv_pos.2 hε)
      rwa [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at h2
    show Φ (τ, p.ε⁻¹ • y) = 0
    exact hR τ _ (by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]; exact h1)

end UnforcedLeray.Short.PartIIIb.NearInst
