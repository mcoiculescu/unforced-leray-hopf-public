import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1.L1.Common

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Gaussian (shiftVec)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **PartIII-b:C/rep/8/3/2/1/1.** `ContDiff 2` of the summed velocity and differentiability of
the summed pressure (source 4963-4978: Gaussian decay, termwise differentiation). -/
theorem gaussSumSmooth : GaussSumSmooth := by
  intro ν s hν hs
  have hc := cOf_ne_zero hν
  refine ⟨?_, ?_⟩
  · rw [gaussV_periodize]
    refine UnforcedLeray.Gaussian.contDiff_periodize (N := 2) (s := 2) (by norm_num) hc
      (vj0_contDiff ν s) ?_
    intro k hk
    have hk' : k ≤ 2 := by exact_mod_cast hk
    refine ⟨C16 ν s, fun z => ?_⟩
    interval_cases k
    · rw [norm_iteratedFDeriv_zero]; exact prof_v0 hν hs z
    · rw [norm_iteratedFDeriv_one]; exact prof_v1 hν hs z
    · have e : ‖iteratedFDeriv ℝ 2 (Vj ν s 0) z‖ = ‖fderiv ℝ (fderiv ℝ (Vj ν s 0)) z‖ := by
        rw [← norm_iteratedFDeriv_one, ← norm_iteratedFDeriv_fderiv]
      rw [e]; exact prof_v2 hν hs z
  · rw [gaussP_fun]
    intro x
    have H := UnforcedLeray.Gaussian.hasFDerivAt_tsum_translates (g := pj ν s 0)
      ((pj0_contDiff ν s).differentiable (by norm_num)) (by norm_num : (1 : ℝ) < 2) hc (C₀ := C16 ν s) (C₁ := C16 ν s)
      (fun z => prof_p0 hν hs z) (fun z => prof_p1 hν hs z) x
    exact H.differentiableAt

end UnforcedLeray.Short.PartIIIb.Concrete
