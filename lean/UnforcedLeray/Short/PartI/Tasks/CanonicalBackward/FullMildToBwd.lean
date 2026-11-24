import UnforcedLeray.Short.PartI.Sub.PartI_C08_1_3

/-!
# `PartI:C08/1/3/1`: proof of `FullMildToBwd`

Converse of `fullMildEq_of_bwdMild` (source lines 1094-1125).  The change of variables
`u = -σ` (`intervalIntegral.integral_comp_neg`) is run in reverse.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

theorem fullMildToBwd_proof : UnforcedLeray.Short.PartI.FullMildToBwd := by
  intro b V hb hVc hFM θ s₀ hθ hθs
  have hθ0 : 0 < θ := hb.trans_le hθ
  have hVθ : ContinuousOn V (Icc θ s₀) := hVc.mono (fun x hx => le_trans hθ hx.1)
  have hLc : ContinuousOn (fun σ => Planar.L0 (V σ)) (Icc θ s₀) :=
    Planar.L0.continuous.comp_continuousOn hVθ
  have hi := Short.Spine.CanonicalMild.intervalIntegrable_expD_log hθ0 hθs hLc
  have h := hFM θ s₀ hθ hθs
  have hc := intervalIntegral.integral_comp_neg (a := θ) (b := s₀)
    (f := fun u : ℝ => Cons.G3b.freeU (-θ) u (B0012.L0 (V (-u))))
  simp only [neg_neg] at hc
  refine ⟨?_, ?_⟩
  · simpa [Pi.zero_apply, add_zero] using hi
  · simp only [Pi.zero_apply, add_zero]
    rw [h, ← hc]
    congr 1
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [Cons.G3b.freeU, neg_neg]
    rfl

end UnforcedLeray.Short.PartI
