import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_1
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

/-!
# `TrainDiffSmooth` (`PartIII-b:C/asrc/ra/8/3/1/2`)

Source: `the November 2 reference manuscript` 2040-2051.

For `s > 0`, `z ↦ tr.v s z` is `C^∞` (`IsTrain.smooth_v`, restricted to the slice `{s} × Plane`
which lies in `Ici 0 ×ˢ univ`).  The periodized vortex `Vc ν c s` is `C^∞` for `c ≠ 0`, `s > 0`
(the rescaling `vcReg_Vc_scale` and `Train.datum_contDiff`), and is identically `0` for `c = 0`
(a constant series over `ℤ` is summable only when the constant vanishes).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- At period `c = 0` the periodized vortex vanishes: the series over `ℤ` has constant terms. -/
theorem vcZero_B2 (ν s : ℝ) : UnforcedLeray.Train.Vc ν 0 s = fun _ => 0 := by
  funext z
  unfold UnforcedLeray.Train.Vc UnforcedLeray.Gaussian.periodize
  simp only [mul_zero, sub_zero]
  by_cases hsum : Summable (fun _ : ℤ => UnforcedLeray.Train.isoV ν s (z.1, z.2))
  · have h0 := hsum.tendsto_cofinite_zero
    have h1 : Tendsto (fun _ : ℤ => UnforcedLeray.Train.isoV ν s (z.1, z.2)) cofinite
        (𝓝 (UnforcedLeray.Train.isoV ν s (z.1, z.2))) := tendsto_const_nhds
    have h2 : UnforcedLeray.Train.isoV ν s (z.1, z.2) = 0 := tendsto_nhds_unique h1 h0
    rw [h2, tsum_zero]
  · exact tsum_eq_zero_of_not_summable hsum

/-- `C^∞`-smoothness of the periodized vortex for `c ≠ 0`, `s > 0`. -/
theorem vcSmooth_B2 {ν c s : ℝ} (hν : 0 < ν) (hs : 0 < s) (hc : c ≠ 0) :
    ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν c s) := by
  have ha : 0 < UnforcedLeray.Train.width ν s := by
    unfold UnforcedLeray.Train.width
    have := mul_pos hν hs
    linarith
  have hr : 0 < Real.sqrt (UnforcedLeray.Train.width ν s) := Real.sqrt_pos.2 ha
  have hr2 : Real.sqrt (UnforcedLeray.Train.width ν s) ^ 2 = UnforcedLeray.Train.width ν s :=
    Real.sq_sqrt ha.le
  have hfun : UnforcedLeray.Train.Vc ν c s = fun z : ℝ × ℝ =>
      (Real.sqrt (UnforcedLeray.Train.width ν s))⁻¹ ^ 3 •
        UnforcedLeray.Train.datum (c / Real.sqrt (UnforcedLeray.Train.width ν s))
          ((Real.sqrt (UnforcedLeray.Train.width ν s))⁻¹ • z) :=
    funext fun z => UnforcedLeray.Short.Spine.vcReg_Vc_scale ν c s _ hr2 z
  rw [hfun]
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (Real.sqrt (UnforcedLeray.Train.width ν s))⁻¹ • z) :=
    contDiff_const_smul _
  have h2 : ContDiff ℝ ∞
      (UnforcedLeray.Train.datum (c / Real.sqrt (UnforcedLeray.Train.width ν s))) :=
    UnforcedLeray.Train.datum_contDiff (div_ne_zero hc hr.ne')
  exact (h2.comp h1).const_smul _

theorem trainDiffSmooth_proof : TrainDiffSmooth := by
  unfold TrainDiffSmooth
  intro ν c tr hν s hs
  have hs0 : 0 ≤ s := hs.le
  have hv : ContDiff ℝ ∞ (fun z : ℝ × ℝ => tr.v s z) := by
    have h := tr.isTrain.smooth_v
    have hm : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ))) :=
      contDiff_const.prodMk contDiff_id
    have hmaps : MapsTo (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ))) univ (Ici 0 ×ˢ univ) :=
      fun z _ => ⟨hs0, mem_univ _⟩
    exact contDiffOn_univ.mp (h.comp hm.contDiffOn hmaps)
  have hVc : ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν c s) := by
    by_cases hc : c = 0
    · subst hc
      rw [vcZero_B2]
      exact contDiff_const
    · exact vcSmooth_B2 hν hs hc
  exact (hv.sub hVc).of_le (WithTop.coe_le_coe.2 le_top)

end UnforcedLeray.Short.PartIIIb.Concrete
