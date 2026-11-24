import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

/-- The mollifier kernel has the properties of `MollKerProps` (one `n`). -/
theorem molKer_props (n : ℕ) :
    ContDiff ℝ ∞ (molKer n) ∧ HasCompactSupport (molKer n) ∧
      ∀ y : ℝ × ℝ, 1 < ‖y‖ → molKer n y = 0 := by
  refine ⟨(molBump n).contDiff_normed, (molBump n).hasCompactSupport_normed, ?_⟩
  intro y hy
  have hr : (molBump n).rOut ≤ 1 := by
    show 1 / ((n : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hd : (molBump n).rOut ≤ dist y (0 : ℝ × ℝ) := by
    rw [dist_zero_right]; linarith
  show (molBump n).normed volume y = 0
  rw [ContDiffBump.normed_def, (molBump n).zero_of_le_dist hd, zero_div]

/-- The mollifier kernel reflected: `mollR n h = ρ̌_n ⋆ h` as a real convolution. -/
theorem mollR_eq_conv (n : ℕ) (h : ℝ × ℝ → ℝ) :
    mollR n h = (fun y => molKer n (-y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h := by
  funext x
  rw [convolution_def]
  have := integral_neg_eq_self (fun y => molKer n (-y) * h (x - y)) (volume : Measure (ℝ × ℝ))
  simp only [neg_neg, sub_neg_eq_add] at this
  simp only [mollR, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact this

/-- The mollifier convolution is smooth. -/
theorem mollR_contDiff (n : ℕ) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (mollR n h) := by
  rw [mollR_eq_conv]
  have hK := molKer_props n
  have hcs : HasCompactSupport (fun y : ℝ × ℝ => molKer n (-y)) :=
    hK.2.1.comp_homeomorph (Homeomorph.neg (ℝ × ℝ))
  have hsm : ContDiff ℝ ∞ (fun y : ℝ × ℝ => molKer n (-y)) :=
    hK.1.comp contDiff_neg
  exact hcs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hsm
    (hh.continuous.locallyIntegrable (μ := (volume : Measure (ℝ × ℝ))))

/-- Differentiation under the integral: the derivative of `mollR n h` at `x₀`. -/
theorem mollR_hasFDerivAt (n : ℕ) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x0 : ℝ × ℝ) :
    HasFDerivAt (mollR n h) (∫ a, molKer n a • fderiv ℝ h (x0 + a)) x0 := by
  obtain ⟨hKs, hKc, hKz⟩ := molKer_props n
  have hfd : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x0 2).exists_bound_of_continuousOn hfd.continuousOn
  have hcont : ∀ x : ℝ × ℝ, Continuous (fun a : ℝ × ℝ => molKer n a • fderiv ℝ h (x + a)) :=
    fun x => hKs.continuous.smul (hfd.comp (continuous_const.add continuous_id))
  have hH := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x a => molKer n a * h (x + a))
    (F' := fun x a => molKer n a • fderiv ℝ h (x + a))
    (x₀ := x0) (s := Metric.ball x0 1) (bound := fun a => ‖molKer n a‖ * M)
    (Metric.ball_mem_nhds x0 one_pos)
    (Eventually.of_forall fun x => ((hKs.continuous.mul
      (hh.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable))
    ((hKs.continuous.mul (hh.continuous.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
      (hKc.mul_right))
    (hcont x0).aestronglyMeasurable
    (Eventually.of_forall fun a x hx => by
      have hx' : ‖x - x0‖ < 1 := by simpa [dist_eq_norm, Metric.mem_ball] using hx
      by_cases ha : ‖a‖ ≤ 1
      · have hmem : x + a ∈ Metric.closedBall x0 2 := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have e : x + a - x0 = (x - x0) + a := by abel
          rw [e]
          have := norm_add_le (x - x0) a
          linarith
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hM _ hmem) (norm_nonneg _)
      · have h0 : molKer n a = 0 := hKz a (not_le.1 ha)
        simp [h0])
    ((hKs.continuous.integrable_of_hasCompactSupport hKc).norm.mul_const M)
    (Eventually.of_forall fun a x hx => by
      have hd : HasFDerivAt (fun t => h (t + a)) (fderiv ℝ h (x + a)) x :=
        (hasFDerivAt_comp_add_right (f := h) a).2 ((hh.differentiable (by simp) (x + a)).hasFDerivAt)
      exact hd.const_mul (molKer n a))
  exact hH

/-- `∂_l (ρ̌_n ⋆ h) = ρ̌_n ⋆ ∂_l h`. -/
theorem mollR_pd (n : ℕ) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (l : Fin 2) :
    B0579.pd l (mollR n h) = mollR n (B0579.pd l h) := by
  obtain ⟨hKs, hKc, _⟩ := molKer_props n
  have hfd : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by simp)
  funext x
  have hH := mollR_hasFDerivAt n hh x
  have hint : Integrable (fun a : ℝ × ℝ => molKer n a • fderiv ℝ h (x + a)) volume :=
    (hKs.continuous.smul (hfd.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
      hKc.smul_right
  show fderiv ℝ (mollR n h) x (B0579.dir l) = mollR n (B0579.pd l h) x
  rw [hH.fderiv, ContinuousLinearMap.integral_apply hint]
  simp only [mollR, ContinuousLinearMap.smul_apply, smul_eq_mul, B0579.pd]

theorem mollR_periodic (n : ℕ) {c : ℝ} {h : ℝ × ℝ → ℝ}
    (hper : ∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x) (x : ℝ × ℝ) :
    mollR n h (x.1 + c, x.2) = mollR n h x := by
  unfold mollR
  congr 1
  funext y
  have e : ((x.1 + c, x.2) + y) = ((x + y).1 + c, (x + y).2) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add])
  rw [e, hper]

theorem mollR_band (n : ℕ) {h : ℝ × ℝ → ℝ} {R : ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → h x = 0) (x : ℝ × ℝ) (hx : R + 1 < |x.2|) :
    mollR n h x = 0 := by
  unfold mollR
  have hz : ∀ y : ℝ × ℝ, molKer n y * h (x + y) = 0 := by
    intro y
    by_cases hy : 1 < ‖y‖
    · simp [(molKer_props n).2.2 y hy]
    · push_neg at hy
      have hy2 : |y.2| ≤ 1 := by
        have := norm_snd_le y
        rw [Real.norm_eq_abs] at this
        linarith
      have e : x.2 = (x.2 + y.2) + (-y.2) := by ring
      have h1 : |x.2| ≤ |x.2 + y.2| + |y.2| := by
        calc |x.2| = |(x.2 + y.2) + (-y.2)| := by rw [← e]
          _ ≤ |x.2 + y.2| + |-y.2| := abs_add_le _ _
          _ = |x.2 + y.2| + |y.2| := by rw [abs_neg]
      have hz' : R < |(x + y).2| := by
        rw [Prod.snd_add]
        linarith
      rw [hR (x + y) hz', mul_zero]
  simp [hz]

theorem mollR_isCylTest (n : ℕ) {c : ℝ} {h : ℝ × ℝ → ℝ} (hh : B0579.IsCylTest c h) :
    B0579.IsCylTest c (mollR n h) := by
  obtain ⟨R, hR⟩ := hh.band
  exact ⟨mollR_contDiff n hh.smooth, fun x => mollR_periodic n hh.periodic x,
    ⟨R + 1, fun x hx => mollR_band n hR x hx⟩⟩

/-- The box of the mollifier estimates. -/
def mollBox (c R : ℝ) : Set (ℝ × ℝ) := Icc (-(c / 2) - 1) (c / 2 + 1) ×ˢ Icc (-R - 1) (R + 1)

theorem mollBox_compact (c R : ℝ) : IsCompact (mollBox c R) := isCompact_Icc.prod isCompact_Icc

/-- Band radius and a uniform bound of a cylinder test on the strip `-c/2 - 1 ≤ z₁ ≤ c/2 + 1`. -/
theorem cyl_test_bound {c : ℝ} {h : ℝ × ℝ → ℝ} (hh : B0579.IsCylTest c h) :
    ∃ R M : ℝ, 0 ≤ M ∧ (∀ x : ℝ × ℝ, R < |x.2| → h x = 0) ∧
      ∀ z : ℝ × ℝ, -(c / 2) - 1 ≤ z.1 → z.1 ≤ c / 2 + 1 → ‖h z‖ ≤ M := by
  obtain ⟨R, hR⟩ := hh.band
  obtain ⟨C, hC⟩ := (mollBox_compact c R).exists_bound_of_continuousOn hh.continuous.continuousOn
  refine ⟨R, max C 0, le_max_right _ _, hR, fun z h1 h2 => ?_⟩
  by_cases hz : |z.2| ≤ R + 1
  · have hmem : z ∈ mollBox c R := by
      refine ⟨⟨h1, h2⟩, ?_⟩
      exact ⟨by linarith [(abs_le.1 hz).1], by linarith [(abs_le.1 hz).2]⟩
    exact le_trans (hC z hmem) (le_max_left _ _)
  · push_neg at hz
    rw [hR z (by linarith), norm_zero]
    exact le_max_right _ _

/-- The cell times the plane is the restriction of the product measure. -/
theorem cell_prod_eq (c : ℝ) :
    (volume.restrict (B0579.cell c)).prod (volume : Measure (ℝ × ℝ)) =
      ((volume : Measure (ℝ × ℝ)).prod volume).restrict (B0579.cell c ×ˢ univ) := by
  have := Measure.prod_restrict (μ := (volume : Measure (ℝ × ℝ)))
    (ν := (volume : Measure (ℝ × ℝ))) (B0579.cell c) (univ : Set (ℝ × ℝ))
  rw [Measure.restrict_univ] at this
  exact this

/-- The two cell definitions agree. -/
theorem cell_eq_cyl (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

/-- Translation invariance of the cell integral (periodicity of `f` and `h`). -/
theorem cell_shift {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℝ} (hh : B0579.IsCylTest c h)
    {f : ℝ × ℝ → ℂ} (hfp : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) (y : ℝ × ℝ) :
    ∫ x in B0579.cell c, f (x - y) * (h x : ℂ) = ∫ x in B0579.cell c, f x * (h (x + y) : ℂ) := by
  have hper : UnforcedLeray.Cyl.IsPeriodic c (fun z => f z * (h (z + y) : ℂ)) := by
    intro z
    have e : ((z.1 + c, z.2) + y) = ((z + y).1 + c, (z + y).2) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add])
    simp only [e, hfp z, hh.periodic (z + y)]
  have key := UnforcedLeray.Cyl.integral_cell_comp_add hc hper (-y)
  rw [← cell_eq_cyl] at key
  calc ∫ x in B0579.cell c, f (x - y) * (h x : ℂ)
      = ∫ x in B0579.cell c, f (x + -y) * (h (x + -y + y) : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [sub_eq_add_neg, neg_add_cancel_right]
    _ = ∫ x in B0579.cell c, f x * (h (x + y) : ℂ) := key

/-- The first Fubini integrand is integrable on the cell times the plane. -/
theorem mollDual_integrable1 (n : ℕ) {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℝ}
    (hh : B0579.IsCylTest c h) {f : ℝ × ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hfL : LocallyIntegrable f volume) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((molKer n p.2 : ℝ) : ℂ) *
        (f (p.1 - p.2) * (h p.1 : ℂ)))
      ((volume.restrict (B0579.cell c)).prod volume) := by
  obtain ⟨R, M, hM0, hRz, hMb⟩ := cyl_test_bound hh
  obtain ⟨hKs, hKc, hKz⟩ := molKer_props n
  have hKcont : Continuous (molKer n) := hKs.continuous
  have hIK : Integrable (fun y : ℝ × ℝ => ‖molKer n y‖) volume :=
    (hKcont.integrable_of_hasCompactSupport hKc).norm
  have hIind : Integrable ((mollBox c R).indicator (fun z : ℝ × ℝ => ‖f z‖)) volume := by
    refine (integrable_indicator_iff (mollBox_compact c R).measurableSet).2 ?_
    exact (hfL.integrableOn_isCompact (mollBox_compact c R)).norm
  have hG : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      M * (‖molKer n p.2‖ * (mollBox c R).indicator (fun z : ℝ × ℝ => ‖f z‖) (p.1 - p.2)))
      (volume.prod volume) :=
    ((hIK.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hIind)).const_mul M
  have hF1 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => f (p.1 - p.2))
      ((volume : Measure (ℝ × ℝ)).prod volume) :=
    hfm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume)
  have hmeas : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((molKer n p.2 : ℝ) : ℂ) *
      (f (p.1 - p.2) * (h p.1 : ℂ))) ((volume : Measure (ℝ × ℝ)).prod volume) := by
    have c1 : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((molKer n p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hKcont.comp continuous_snd)
    have c2 : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((h p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hh.continuous.comp continuous_fst)
    exact c1.aestronglyMeasurable.mul (hF1.mul c2.aestronglyMeasurable)
  rw [cell_prod_eq]
  refine Integrable.mono' hG.restrict hmeas.restrict ?_
  refine ae_restrict_of_forall_mem ((B0579.measurableSet_cell c).prod MeasurableSet.univ) ?_
  intro p hp
  have hA : -(c / 2) ≤ p.1.1 := hp.1.1.1
  have hB : p.1.1 < c / 2 := hp.1.1.2
  by_cases hK : molKer n p.2 = 0
  · simp [hK]
  have hp2 : ‖p.2‖ ≤ 1 := by
    by_contra hcon
    exact hK ((molKer_props n).2.2 p.2 (not_le.1 hcon))
  have hp21 : |p.2.1| ≤ 1 := by
    have := norm_fst_le p.2
    rw [Real.norm_eq_abs] at this
    linarith
  have hp22 : |p.2.2| ≤ 1 := by
    have := norm_snd_le p.2
    rw [Real.norm_eq_abs] at this
    linarith
  by_cases hh0 : h p.1 = 0
  · simp only [hh0, Complex.ofReal_zero, mul_zero, norm_zero]
    exact mul_nonneg hM0 (mul_nonneg (norm_nonneg _)
      (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _))
  have hx2 : |p.1.2| ≤ R := by
    by_contra hcon
    push_neg at hcon
    exact hh0 (hRz _ hcon)
  have hmem : p.1 - p.2 ∈ mollBox c R := by
    obtain ⟨a1, a2⟩ := abs_le.1 hp21
    obtain ⟨b1, b2⟩ := abs_le.1 hp22
    obtain ⟨c1, c2⟩ := abs_le.1 hx2
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> linarith
  have hb : ‖h p.1‖ ≤ M := hMb p.1 (by linarith) (by linarith)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Set.indicator_of_mem hmem]
  calc ‖molKer n p.2‖ * (‖f (p.1 - p.2)‖ * ‖h p.1‖)
      ≤ ‖molKer n p.2‖ * (‖f (p.1 - p.2)‖ * M) := by gcongr
    _ = M * (‖molKer n p.2‖ * ‖f (p.1 - p.2)‖) := by ring

/-- The second Fubini integrand is integrable on the cell times the plane. -/
theorem mollDual_integrable2 (n : ℕ) {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℝ}
    (hh : B0579.IsCylTest c h) {f : ℝ × ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hfL : LocallyIntegrable f volume) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((molKer n p.2 : ℝ) : ℂ) *
        (f p.1 * (h (p.1 + p.2) : ℂ)))
      ((volume.restrict (B0579.cell c)).prod volume) := by
  obtain ⟨R, M, hM0, hRz, hMb⟩ := cyl_test_bound hh
  obtain ⟨hKs, hKc, hKz⟩ := molKer_props n
  have hKcont : Continuous (molKer n) := hKs.continuous
  have hIK : Integrable (fun y : ℝ × ℝ => ‖molKer n y‖) volume :=
    (hKcont.integrable_of_hasCompactSupport hKc).norm
  have hIind : Integrable ((mollBox c R).indicator (fun z : ℝ × ℝ => ‖f z‖)) volume := by
    refine (integrable_indicator_iff (mollBox_compact c R).measurableSet).2 ?_
    exact (hfL.integrableOn_isCompact (mollBox_compact c R)).norm
  have hG : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (mollBox c R).indicator (fun z : ℝ × ℝ => ‖f z‖) p.1 * (M * ‖molKer n p.2‖))
      (volume.prod volume) :=
    Integrable.mul_prod hIind (hIK.const_mul M)
  have hF1 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => f p.1)
      ((volume : Measure (ℝ × ℝ)).prod volume) :=
    hfm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hmeas : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((molKer n p.2 : ℝ) : ℂ) *
      (f p.1 * (h (p.1 + p.2) : ℂ))) ((volume : Measure (ℝ × ℝ)).prod volume) := by
    have c1 : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((molKer n p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hKcont.comp continuous_snd)
    have c2 : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((h (p.1 + p.2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hh.continuous.comp (continuous_fst.add continuous_snd))
    exact c1.aestronglyMeasurable.mul (hF1.mul c2.aestronglyMeasurable)
  rw [cell_prod_eq]
  refine Integrable.mono' hG.restrict hmeas.restrict ?_
  refine ae_restrict_of_forall_mem ((B0579.measurableSet_cell c).prod MeasurableSet.univ) ?_
  intro p hp
  have hA : -(c / 2) ≤ p.1.1 := hp.1.1.1
  have hB : p.1.1 < c / 2 := hp.1.1.2
  by_cases hK : molKer n p.2 = 0
  · simp [hK]
  have hp2 : ‖p.2‖ ≤ 1 := by
    by_contra hcon
    exact hK ((molKer_props n).2.2 p.2 (not_le.1 hcon))
  have hp21 : |p.2.1| ≤ 1 := by
    have := norm_fst_le p.2
    rw [Real.norm_eq_abs] at this
    linarith
  have hp22 : |p.2.2| ≤ 1 := by
    have := norm_snd_le p.2
    rw [Real.norm_eq_abs] at this
    linarith
  by_cases hbig : R + 1 < |p.1.2|
  · have hz : R < |(p.1 + p.2).2| := by
      rw [Prod.snd_add]
      have e : p.1.2 = (p.1.2 + p.2.2) + (-p.2.2) := by ring
      have hT := abs_add_le (p.1.2 + p.2.2) (-p.2.2)
      rw [abs_neg, ← e] at hT
      linarith [abs_le.1 hp22]
    rw [hRz _ hz]
    simp only [Complex.ofReal_zero, mul_zero, norm_zero]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
      (mul_nonneg hM0 (norm_nonneg _))
  have hmem : p.1 ∈ mollBox c R := by
    have hx2 : |p.1.2| ≤ R + 1 := not_lt.1 hbig
    obtain ⟨c1, c2⟩ := abs_le.1 hx2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hb : ‖h (p.1 + p.2)‖ ≤ M := by
    obtain ⟨a1, a2⟩ := abs_le.1 hp21
    exact hMb (p.1 + p.2) (by simp only [Prod.fst_add]; linarith)
      (by simp only [Prod.fst_add]; linarith)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Set.indicator_of_mem hmem]
  calc ‖molKer n p.2‖ * (‖f p.1‖ * ‖h (p.1 + p.2)‖)
      ≤ ‖molKer n p.2‖ * (‖f p.1‖ * M) := by gcongr
    _ = ‖f p.1‖ * (M * ‖molKer n p.2‖) := by ring

/-- The mollification of a periodic field as a plane integral. -/
theorem cellMoll_mul (n : ℕ) (f : ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    cellMoll n f x * (h x : ℂ) = ∫ y, ((molKer n y : ℝ) : ℂ) * (f (x - y) * (h x : ℂ)) := by
  unfold cellMoll cellConv
  rw [← integral_mul_const]
  congr 1
  funext y
  rw [Complex.real_smul]
  ring

/-- The core of the duality: Fubini and the translation invariance of the cell. -/
theorem mollDual_core (n : ℕ) {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℝ} (hh : B0579.IsCylTest c h)
    {f : ℝ × ℝ → ℂ} (hfp : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (hfm : AEStronglyMeasurable f volume) (hfL : LocallyIntegrable f volume) :
    IntegrableOn (fun x => cellMoll n f x * (h x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, cellMoll n f x * (h x : ℂ) =
        ∫ x in B0579.cell c, f x * (mollR n h x : ℂ) := by
  have hI1 := mollDual_integrable1 n hc hh hfm hfL
  have hI2 := mollDual_integrable2 n hc hh hfm hfL
  refine ⟨?_, ?_⟩
  · exact (hI1.integral_prod_left).congr (ae_of_all _ fun x => (cellMoll_mul n f h x).symm)
  · calc ∫ x in B0579.cell c, cellMoll n f x * (h x : ℂ)
        = ∫ x in B0579.cell c, ∫ y, ((molKer n y : ℝ) : ℂ) * (f (x - y) * (h x : ℂ)) := by
          simp only [cellMoll_mul]
      _ = ∫ y, ∫ x in B0579.cell c, ((molKer n y : ℝ) : ℂ) * (f (x - y) * (h x : ℂ)) :=
          integral_integral_swap (f := fun x y => ((molKer n y : ℝ) : ℂ) * (f (x - y) * (h x : ℂ)))
            hI1
      _ = ∫ y, ((molKer n y : ℝ) : ℂ) * ∫ x in B0579.cell c, f (x - y) * (h x : ℂ) := by
          simp only [integral_const_mul]
      _ = ∫ y, ((molKer n y : ℝ) : ℂ) * ∫ x in B0579.cell c, f x * (h (x + y) : ℂ) := by
          simp only [cell_shift hc hh hfp]
      _ = ∫ y, ∫ x in B0579.cell c, ((molKer n y : ℝ) : ℂ) * (f x * (h (x + y) : ℂ)) := by
          simp only [integral_const_mul]
      _ = ∫ x in B0579.cell c, ∫ y, ((molKer n y : ℝ) : ℂ) * (f x * (h (x + y) : ℂ)) :=
          (integral_integral_swap (f := fun x y => ((molKer n y : ℝ) : ℂ) *
            (f x * (h (x + y) : ℂ))) hI2).symm
      _ = ∫ x in B0579.cell c, f x * ∫ y, ((molKer n y : ℝ) : ℂ) * (h (x + y) : ℂ) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          dsimp only
          rw [← integral_const_mul]
          congr 1
          funext y
          ring
      _ = ∫ x in B0579.cell c, f x * (mollR n h x : ℂ) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          dsimp only
          congr 1
          unfold mollR
          rw [← integral_complex_ofReal]
          congr 1
          funext y
          simp [Complex.ofReal_mul]

/-- **(A4) Duality for the mollification.** -/
theorem mollDual (hL : UnforcedLeray.Short.IIIa.CellPeriodicLocInt)
    (hD : UnforcedLeray.Short.IIIa.CellConvDeriv) : UnforcedLeray.Short.IIIa.MollDual := by
  unfold MollDual
  intro c m n hc h hh
  refine ⟨mollR_isCylTest n hh, fun l => mollR_pd n hh.smooth l, ?_⟩
  intro f hfp hfM
  obtain ⟨hfm, hfL⟩ := hL c m f hc hfp hfM
  exact mollDual_core n hc hh hfp hfm hfL

end UnforcedLeray.Short.IIIa
