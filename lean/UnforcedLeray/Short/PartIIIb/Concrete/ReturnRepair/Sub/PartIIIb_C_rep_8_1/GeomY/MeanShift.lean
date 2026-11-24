import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Shift
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Lap
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Pieces
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org

/-!
# `PartIII-b:C/rep/8/1/1/2/2a`: the shifted dilation identity of the phase-mean Newton fields

Source of record: `the November 2 reference manuscript`, lines 5383-5387 and
4776-4782.  The uncut zero-width fields `V_{p}` (`newtonV`) are harmonic off the old disc
(`newtonV_trace`, `MeanShift/Harmonic.lean`) and satisfy the shifted dilation identity
`(-½ x·∇ + μ + ½)(V_μ - V_{μ+1}) = V_μ` there (`newtonV_shift_component`, `MeanShift/Shift.lean`,
from the degree `-4` homogeneity of the kernel and an integration by parts in `t`,
`MeanShift/Ibp.lean`).  At a young receiver `εy` lies off the old disc, and
`W_p(y) = ε² V_p(εy)`, so the Laplacian term drops and the identity transfers.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem meanShiftIdentity : MeanShiftIdentity := by
  intro c ν ε μ χo χy hL M hM y hy
  have hc : 0 < c := hL.c_pos
  have hν : 0 < ν := hL.nu_pos
  have hε : 0 < ε := hL.eps_pos
  have hμ : 0 < μ := hL.mu_pos
  have hχ : IsOutwardCutoff χo := hL.chiO
  -- the receiver `x = εy` lies off the old disc
  have hx : 5 * ν / 6 < (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 := by
    have h1 : Real.sqrt ν ≤ ε * cylR y := by
      have := (div_le_iff₀ hε).1 hy
      linarith
    have h2 : ν ≤ (ε * cylR y) ^ 2 := by
      calc ν = Real.sqrt ν ^ 2 := (Real.sq_sqrt hν.le).symm
        _ ≤ (ε * cylR y) ^ 2 := by gcongr
    have h3 : (ε * cylR y) ^ 2 = (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 := by
      unfold cylR
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      simp [mul_pow]
      ring
    linarith
  set U : Set Vec3 := {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} with hUdef
  have hU : IsOpen U := isOpen_newtonRegion ν
  have hxU : ε • y ∈ U := hx
  have hVS : ∀ p : ℝ, 0 < p → ContDiffOn ℝ ∞ (newtonV c ν p χo M) U := fun p hp =>
    newtonVSmooth_of newtonFamSmooth newtonFamMeas newtonFamDom c ν p χo M hc hν hp hχ hM
  have hVd : ∀ p : ℝ, 0 < p → DifferentiableAt ℝ (newtonV c ν p χo M) (ε • y) := fun p hp =>
    ((hVS p hp).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hZ : youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M =
      fun z => ε ^ 2 • (newtonV c ν μ χo M (ε • z) - newtonV c ν (μ + 1) χo M (ε • z)) := by
    funext z
    simp [youngW, smul_sub]
  have hshift := fun i => newtonV_shift_component hc hν hμ hχ hM i hx
  funext i
  -- (B) the radial derivative
  have hB : fderiv ℝ (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) y y i =
      ε ^ 2 * (fderiv ℝ (newtonV c ν μ χo M) (ε • y) (ε • y) i -
        fderiv ℝ (newtonV c ν (μ + 1) χo M) (ε • y) (ε • y) i) := by
    rw [hZ]
    have hVdiff : HasFDerivAt (fun w => newtonV c ν μ χo M w - newtonV c ν (μ + 1) χo M w)
        (fderiv ℝ (newtonV c ν μ χo M) (ε • y) - fderiv ℝ (newtonV c ν (μ + 1) χo M) (ε • y))
        (ε • y) := (hVd μ hμ).hasFDerivAt.sub (hVd (μ + 1) (by linarith)).hasFDerivAt
    have hZ' : HasFDerivAt
        (fun z => ε ^ 2 • (newtonV c ν μ χo M (ε • z) - newtonV c ν (μ + 1) χo M (ε • z)))
        (ε ^ 2 • ((fderiv ℝ (newtonV c ν μ χo M) (ε • y) -
          fderiv ℝ (newtonV c ν (μ + 1) χo M) (ε • y)).comp (ε • ContinuousLinearMap.id ℝ Vec3)))
        y :=
      (hVdiff.comp y ((hasFDerivAt_id y).const_smul ε)).const_smul (ε ^ 2)
    rw [hZ'.fderiv]
    simp [mul_sub]
  -- (C) the Laplacian vanishes
  have hC : vecLap (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) y i = 0 := by
    rw [hZ]
    set U' : Set Vec3 := {z : Vec3 | ε • z ∈ U} with hU'def
    have hU' : IsOpen U' := hU.preimage (continuous_const_smul ε)
    have hyU' : y ∈ U' := hxU
    have hsm : ContDiffOn ℝ ∞
        (fun w => newtonV c ν μ χo M w - newtonV c ν (μ + 1) χo M w) U :=
      (hVS μ hμ).sub (hVS (μ + 1) (by linarith))
    have hX : ContDiffOn ℝ ∞
        (fun z => ε ^ 2 • (newtonV c ν μ χo M (ε • z) - newtonV c ν (μ + 1) χo M (ε • z))) U' := by
      refine ContDiffOn.const_smul (ε ^ 2) ?_
      exact hsm.comp (contDiff_const_smul ε).contDiffOn (fun z hz => hz)
    rw [vecLap_apply hU' hX hyU' i]
    -- the scalar component `hs = V_μ,i - V_{μ+1},i`
    set hs : Vec3 → ℝ := fun w => newtonV c ν μ χo M w i - newtonV c ν (μ + 1) χo M w i with hhs
    have hs_sm : ContDiffOn ℝ ∞ hs U := by
      have h1 : ∀ p : ℝ, 0 < p → ContDiffOn ℝ ∞ (fun w => newtonV c ν p χo M w i) U :=
        fun p hp => (contDiffOn_pi.1 (hVS p hp)) i
      exact (h1 μ hμ).sub (h1 (μ + 1) (by linarith))
    have hfun : (fun z : Vec3 => (ε ^ 2 • (newtonV c ν μ χo M (ε • z) -
        newtonV c ν (μ + 1) χo M (ε • z))) i) = (ε ^ 2) • (fun z => hs (ε • z)) := by
      funext z
      simp [hhs]
    have hcomp : ContDiffAt ℝ 2 (fun z => hs (ε • z)) y :=
      ((hs_sm.contDiffAt (hU.mem_nhds hxU)).of_le (by norm_cast)).comp y
        (contDiff_const_smul ε).contDiffAt
    rw [hfun]
    simp only [iteratedFDeriv_const_smul_apply hcomp, smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [trace_scale hU hs_sm hxU]
    have hc1 : ∀ p : ℝ, 0 < p → ContDiffAt ℝ 2 (fun w => newtonV c ν p χo M w i) (ε • y) :=
      fun p hp => (((contDiffOn_pi.1 (hVS p hp)) i).contDiffAt (hU.mem_nhds hxU)).of_le
        (by norm_cast)
    have hsub : ∀ l : Fin 3, iteratedFDeriv ℝ 2 hs (ε • y) ![Pi.single l 1, Pi.single l 1] =
        iteratedFDeriv ℝ 2 (fun w => newtonV c ν μ χo M w i) (ε • y)
          ![Pi.single l 1, Pi.single l 1] -
        iteratedFDeriv ℝ 2 (fun w => newtonV c ν (μ + 1) χo M w i) (ε • y)
          ![Pi.single l 1, Pi.single l 1] := by
      intro l
      rw [show hs = (fun w => newtonV c ν μ χo M w i) - (fun w => newtonV c ν (μ + 1) χo M w i)
        from rfl, iteratedFDeriv_sub_apply (hc1 μ hμ) (hc1 (μ + 1) (by linarith))]
      rfl
    simp only [hsub, Finset.sum_sub_distrib]
    rw [newtonV_trace hc hν hμ hχ hM i hx, newtonV_trace hc hν (by linarith) hχ hM i hx]
    ring
  have hW : ∀ p : ℝ, youngW c ν ε p χo M y i = ε ^ 2 * newtonV c ν p χo M (ε • y) i := by
    intro p
    simp [youngW]
  unfold dmuFree
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hB, hC, hW μ, hW (μ + 1)]
  have := hshift i
  linear_combination ε ^ 2 * this

end UnforcedLeray.Short.PartIIIb.Concrete
