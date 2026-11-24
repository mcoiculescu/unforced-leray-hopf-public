import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Units.B0238
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Part III-a, `PartIII-a:T21/2/6/17`: the mean velocity formula

Source of record: `the November 2 reference manuscript` (SP), lines 397-404
(`sct:mean`: `\bar v₁ = -S_η`, `\bar v₂ = 0`, `S = \bar ψ`, `S` smooth for `s > 0`).
Target: `meanVecFormula_of`, proving the Prop `MeanVecFormula` from `TrainMeanEquations`.

Route. The slice `η ↦ S(s, η)` is `C^∞` for `s > 0` because `S` is jointly `C^∞` on
`Ioi 0 ×ˢ univ` (composition with `η ↦ (s, η)`). The vector identity follows componentwise: the
horizontal average commutes with the coordinate projection (the integrand is continuous on the
finite-measure interval `Ioc (-c/2) (c/2)`, so `ContinuousLinearMap.integral_comp_comm` applies),
and the components are the two identities of `sct:mean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Componentwise horizontal average: for a continuous-in-`q` vector field, the `k`-th component
of the average is the average of the `k`-th component. -/
theorem meanVec_hmean_proj (c : ℝ) (f : ℝ × ℝ → UnforcedLeray.Train.Vec) (η : ℝ) (k : Fin 2)
    (hf : Continuous (fun q : ℝ => f (q, η))) :
    UnforcedLeray.Short.PartI.hmean c f η k =
      UnforcedLeray.Short.PartI.hmean c (fun z => f z k) η := by
  have hint : Integrable (fun q : ℝ => f (q, η))
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    hf.integrableOn_Ioc
  have key : (∫ q in Ioc (-c / 2) (c / 2), f (q, η)) k =
      ∫ q in Ioc (-c / 2) (c / 2), f (q, η) k := by
    have hL := (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).integral_comp_comm hint
    exact hL.symm
  unfold UnforcedLeray.Short.PartI.hmean
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [key]

/-- The velocity identity `\bar v = (-S_η, 0)` in vector form and the smoothness of the mean
stream slice (`sct:mean`). -/
theorem meanVecFormula_of (hmeq : UnforcedLeray.Short.PartI.TrainMeanEquations) :
    MeanVecFormula := by
  intro ν c hν hc tr hbuc s hs
  obtain ⟨hCD, hpt⟩ := hmeq ν c hν hc tr hbuc
  have hslice : ContDiff ℝ ∞ (fun η => UnforcedLeray.Short.PartI.meanStream tr s η) :=
    hCD.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun η => ⟨hs, mem_univ η⟩)
  refine ⟨hslice, fun η => ?_⟩
  obtain ⟨_, hB, hC⟩ := hpt s hs η
  have hcont : Continuous (fun q : ℝ => tr.v s (q, η)) :=
    (UnforcedLeray.B0238.contDiff_Vc tr hs.le).continuous.comp
      (continuous_id.prodMk continuous_const)
  have h0 := meanVec_hmean_proj c (tr.v s) η 0 hcont
  have h1 := meanVec_hmean_proj c (tr.v s) η 1 hcont
  have hvec : UnforcedLeray.Short.PartI.hmean c (tr.v s) η =
      UnforcedLeray.Train.toVec
        (UnforcedLeray.Short.PartI.hmean c (fun z => tr.v s z 0) η,
          UnforcedLeray.Short.PartI.hmean c (fun z => tr.v s z 1) η) := by
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  rw [hvec, hB, hC]

end UnforcedLeray.Short.IIIa
