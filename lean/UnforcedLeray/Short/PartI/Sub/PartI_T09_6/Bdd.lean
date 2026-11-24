import UnforcedLeray.Short.PartI.Sub.PartI_T09_6
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.Regular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.VcDeriv
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

theorem trainErrGradBdd_proof : TrainErrGradBdd := by
  intro ν c hν hc tr htr s hs
  have hT : 0 ≤ s + 1 := by linarith
  obtain ⟨hC1, -, -⟩ := UnforcedLeray.Short.IIb.CylPDE.tcRegular ν c tr s hs
  have hv : Differentiable ℝ (tr.v s) := (hC1 s ⟨hs, le_rfl⟩).differentiable one_ne_zero
  obtain ⟨hVd, K, hK⟩ := UnforcedLeray.Short.IIb.CylPDE.tcVcDeriv (ν * s + 1) (by positivity) ν c hν hc
  have hsmem : s ∈ Icc 0 ((ν * s + 1) / ν) := by
    refine ⟨hs, ?_⟩
    rw [le_div_iff₀ hν]; nlinarith
  obtain ⟨M, hM⟩ := htr.deriv_bound hs 1
  have hM1 := hM s ⟨hs, le_rfl⟩
  refine ⟨M + K, ?_⟩
  rintro x ⟨β, k, z, rfl⟩
  have hVdiff := hVd s hsmem
  have hdiff : Differentiable ℝ (trainErr tr s) := hv.sub hVdiff
  have hcomp : Differentiable ℝ (fun x => trainErr tr s x k) :=
    differentiable_euclidean.1 hdiff k
  unfold wordComp
  show |UnforcedLeray.B0151.derivWord [β] (fun x => trainErr tr s x k) z| ≤ M + K
  have h1 : UnforcedLeray.B0151.derivWord [β] (fun x => trainErr tr s x k) z =
      fderiv ℝ (fun x => trainErr tr s x k) z (cjwE β) := by
    cases β
    · exact UnforcedLeray.B0151.partialY_eq_fderiv hcomp z
    · exact UnforcedLeray.B0151.partialX_eq_fderiv hcomp z
  rw [h1]
  have h2 : fderiv ℝ (fun x => trainErr tr s x k) z (cjwE β) =
      (fderiv ℝ (trainErr tr s) z (cjwE β)) k := by
    have := ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).hasFDerivAt.comp z (hdiff z).hasFDerivAt).fderiv
    rw [show (fun x => trainErr tr s x k) = (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) ∘ trainErr tr s from rfl, this]
    rfl
  rw [h2]
  have h3 : fderiv ℝ (trainErr tr s) z = fderiv ℝ (tr.v s) z - fderiv ℝ (Vc ν c s) z :=
    fderiv_sub (hv z) (hVdiff z)
  have h4 : ‖fderiv ℝ (tr.v s) z‖ ≤ M := by
    have := hM1 z
    rwa [norm_iteratedFDeriv_one] at this
  have h5 := hK s hsmem z
  calc |(fderiv ℝ (trainErr tr s) z (cjwE β)) k|
      ≤ ‖fderiv ℝ (trainErr tr s) z (cjwE β)‖ := by
        simpa using PiLp.norm_apply_le (fderiv ℝ (trainErr tr s) z (cjwE β)) k
    _ ≤ ‖fderiv ℝ (trainErr tr s) z‖ * ‖cjwE β‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M + K := by
        rw [cjwE_norm, mul_one, h3]
        exact (norm_sub_le _ _).trans (add_le_add h4 h5)

end UnforcedLeray.Short.PartI
