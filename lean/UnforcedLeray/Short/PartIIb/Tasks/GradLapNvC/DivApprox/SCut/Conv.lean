import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_2_1

/-!
# Part II-b, task `PartII-b:T09/2/1/3` (`DivSCutConv`): the `s`-cut errors tend to `0`

Source of record: `the November 2 reference manuscript`, lines 1912-1918.
`DriftSCutHelp.tendsto_sCut_sub` for `b`, `√s Qb`, `√s Eb` (the cut commutes with `√s`) and
`DriftSCutHelp.tendsto_dterm` for the commutator `-2ε (s χ_n') b`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open DriftSCutHelp in
/-- **`PartII-b:T09/2/1/3`.** -/
theorem divSCutConv_proof : UnforcedLeray.Short.IIb.DivSCutConv := by
  intro c r ε b Qb Eb hc hr hd
  obtain ⟨M, hM0, hMb⟩ := sBump_deriv_bound_exists
  have e1 : ∀ (k : ℝ) (f : CProf), (sqrtS fun x => sCutB k f x - f x) =
      fun x => (sBump k x.1 : ℂ) • sqrtS f x - sqrtS f x := by
    intro k f
    funext x
    simp only [sqrtS, sCutB, smul_sub, smul_smul, mul_comm]
  refine ⟨tendsto_sCut_sub hc hr hd.inHr, ?_, ?_, ?_⟩
  · simp only [e1]
    exact tendsto_sCut_sub hc hr hd.inQ
  · have t := tendsto_dterm hd.inHr hM0 hMb
    have t' := ENNReal.Tendsto.const_mul t (Or.inr (enorm_ne_top (x := ((-2 * ε : ℝ) : ℂ))))
    rw [mul_zero] at t'
    refine t'.congr (fun n => ?_)
    unfold hNorm
    rw [← eLpNorm_const_smul]
    congr 1
    funext x
    simp only [sCutD, Pi.smul_apply, smul_smul]
    congr 1
    push_cast
    ring
  · simp only [e1]
    exact tendsto_sCut_sub hc hr hd.inE

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divSCutConv_proof
