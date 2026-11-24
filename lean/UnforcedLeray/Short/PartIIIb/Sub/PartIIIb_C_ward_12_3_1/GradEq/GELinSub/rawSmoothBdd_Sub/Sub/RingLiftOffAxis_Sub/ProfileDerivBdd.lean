import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub
import UnforcedLeray.Lib.HeatR3.Line
import UnforcedLeray.Units.B0191

/-!
# Organizer task `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/6`: `profileDerivBdd`

Source of record: `the November 2 reference manuscript`, SP 1311-1313 (Gaussian in `z`).
The unit-age profile `B0191.profile ν = heatKernel ν 1` equals the line Gaussian
`Heat.lineGauss ν` (`(4πν)^{-1/2} e^{-z²/(4ν)}`), so its derivatives are the derivatives of the
line Gaussian, which are bounded (`Heat.iteratedDeriv_lineGauss_bounded`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem profileDerivBdd : UnforcedLeray.Short.PartIIIb.Concrete.ProfileDerivBdd := by
  intro ν hν n
  obtain ⟨M, hM⟩ := UnforcedLeray.Heat.iteratedDeriv_lineGauss_bounded n hν
  refine ⟨M, fun z => ?_⟩
  have hfun : UnforcedLeray.B0191.profile ν = UnforcedLeray.Heat.lineGauss ν := by
    funext x
    simp only [UnforcedLeray.B0191.profile, UnforcedLeray.B0191.heatKernel,
      UnforcedLeray.Heat.lineGauss, mul_one]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      hν.le)]
    ring_nf
  have hpd : UnforcedLeray.B0191.profileDeriv ν n =
      iteratedDeriv n (UnforcedLeray.Heat.lineGauss ν) := by
    unfold UnforcedLeray.B0191.profileDeriv
    rw [hfun]
  rw [hpd, ← Real.norm_eq_abs]
  exact hM z

end UnforcedLeray.Short.PartIIIb.Concrete
