import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1.L1.Common

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Gaussian (shiftVec)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **PartIII-b:C/rep/8/3/2/1/4.** Termwise gradient of the summed pressure (source 4978). -/
theorem gaussSumGrad : GaussSumGrad := by
  intro ν s hν hs x
  have hc := cOf_ne_zero hν
  refine ⟨summable_mgrad_pj_translate hν hs x, ?_⟩
  have H := UnforcedLeray.Gaussian.hasFDerivAt_tsum_translates (g := pj ν s 0)
    ((pj0_contDiff ν s).differentiable (by norm_num)) (by norm_num : (1 : ℝ) < 2) hc (C₀ := C16 ν s) (C₁ := C16 ν s)
    (fun z => prof_p0 hν hs z) (fun z => prof_p1 hν hs z) x
  have hfd : fderiv ℝ (gaussP ν s) x =
      ∑' n : ℤ, fderiv ℝ (fun y => pj ν s 0 (y - shiftVec (cOf ν) n)) x := by
    rw [gaussP_fun]; exact H.fderiv
  have hsumD : Summable (fun n : ℤ => fderiv ℝ (fun y => pj ν s 0 (y - shiftVec (cOf ν) n)) x) := by
    refine Summable.of_norm_bounded
      ((UnforcedLeray.Gaussian.summable_translate (by norm_num : (1 : ℝ) < 2) hc x.1).mul_left
        (C16 ν s)) (fun n => ?_)
    rw [fderiv_comp_sub]
    have h := prof_p1 hν hs (x - shiftVec (cOf ν) n)
    have e : (x - shiftVec (cOf ν) n).1 = x.1 - n * cOf ν := by simp [shiftVec]
    rw [e] at h
    exact h
  have hev : ∀ b : Fin 2, fderiv ℝ (gaussP ν s) x (ei b) =
      ∑' n : ℤ, fderiv ℝ (fun y => pj ν s 0 (y - shiftVec (cOf ν) n)) x (ei b) := by
    intro b
    rw [hfd]
    have := (ContinuousLinearMap.apply ℝ ℝ (ei b)).map_tsum hsumD
    simpa using this
  have hpn : ∀ n : ℤ, (fun y => pj ν s 0 (y - shiftVec (cOf ν) n)) = pj ν s n :=
    fun n => funext fun y => (pj_shift ν s n y).symm
  have hS := summable_mgrad_pj_translate hν hs x
  have f0 : (∑' j : ℤ, mgrad (pj ν s j) x).1 = ∑' j : ℤ, (mgrad (pj ν s j) x).1 := by
    have := (ContinuousLinearMap.fst ℝ ℝ ℝ).map_tsum hS
    simpa using this
  have f1 : (∑' j : ℤ, mgrad (pj ν s j) x).2 = ∑' j : ℤ, (mgrad (pj ν s j) x).2 := by
    have := (ContinuousLinearMap.snd ℝ ℝ ℝ).map_tsum hS
    simpa using this
  refine Prod.ext ?_ ?_
  · show fderiv ℝ (gaussP ν s) x (ei 0) = (∑' j : ℤ, mgrad (pj ν s j) x).1
    rw [f0, hev 0]
    refine tsum_congr fun n => ?_
    rw [hpn n]; rfl
  · show fderiv ℝ (gaussP ν s) x (ei 1) = (∑' j : ℤ, mgrad (pj ν s j) x).2
    rw [f1, hev 1]
    refine tsum_congr fun n => ?_
    rw [hpn n]; rfl

end UnforcedLeray.Short.PartIIIb.Concrete
