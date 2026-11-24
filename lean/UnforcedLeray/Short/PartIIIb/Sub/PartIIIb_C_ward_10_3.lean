import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H15

/-!
# `PartIII-b:C/ward/10/3`: `WardXYoungL2` from `WardX0YoungL2` and `WardStreamCorrYoungL2`

Source of record: `the November 2 reference manuscript` (73 pages), 4171-4196.

By `wardX_eq_cut_add_corr`, `X = χ_y(ν·age) • X₀ + wardStreamCorr`. On the young support
`ϱ ≥ R√ν`, `|χ_y| ≤ 1` and `|∂_j(χ_y(ν·age))| ≤ K_cut` by the chain rule via `hasFDerivAt_age`
and the derivative bound of `χ_y` on `[0, 1]`. Combining the young readings via `WylBd` closure
under sums and scalar multiples yields `WardXYoungL2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- HasFDerivAt for the young cutoff `y ↦ χy (ν * age R y)` off the axis. -/
theorem w3_cut_hasFDerivAt {R ν : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    {y : Space} (hy : y ∉ axis) :
    HasFDerivAt (fun x : Space => χy (ν * age R x))
      (deriv χy (ν * age R y) • (ν • ageD R y)) y := by
  have hage : HasFDerivAt (fun x : Space => ν * age R x) (ν • ageD R y) y :=
    (hasFDerivAt_age R hy).const_mul ν
  have hχ1 : ContDiff ℝ 1 χy :=
    hχy.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hχd : HasDerivAt χy (deriv χy (ν * age R y)) (ν * age R y) :=
    (hχ1.contDiffAt.differentiableAt one_ne_zero).hasDerivAt
  exact hχd.comp_hasFDerivAt y hage

/-- Uniform bound on `|∂_j (y ↦ χy (ν * age R y))|` on the young receiver region `R√ν ≤ ϱ y`. -/
theorem w3_cut_deriv_bound (R ν : ℝ) {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hR : 0 < R) (hν : 0 < ν) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : Space) (j : Fin 3), R * Real.sqrt ν ≤ ϱ y →
      |(deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector j)| ≤ K := by
  have hdχ1 : ContDiff ℝ 1 (deriv χy) :=
    ((show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχy.smooth).deriv').of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hdχ : Continuous (deriv χy) := hdχ1.continuous
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hdχ.continuousOn : ContinuousOn (deriv χy) (Icc 0 1))
  set r1 : ℝ := R * Real.sqrt ν with hr1
  have hr1pos : 0 < r1 := by positivity
  set K : ℝ := max M 0 * (ν * (2 * R ^ 2 / r1 ^ 3)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun y j hy => ?_⟩
  have hρ : 0 < ϱ y := lt_of_lt_of_le hr1pos hy
  have hyax : y ∉ axis := fun h => by
    have := (mem_axis_iff y).1 h
    linarith
  have hage_mem : ν * age R y ∈ Icc (0 : ℝ) 1 := by
    unfold age
    refine ⟨by positivity, ?_⟩
    rw [← mul_div_assoc, div_le_one (pow_pos hρ 2)]
    have hsq : r1 ^ 2 ≤ ϱ y ^ 2 := pow_le_pow_left₀ hr1pos.le hy 2
    have hr1sq : r1 ^ 2 = ν * R ^ 2 := by
      rw [hr1, mul_pow, Real.sq_sqrt hν.le]
      ring
    linarith
  have hM' : |deriv χy (ν * age R y)| ≤ max M 0 := by
    have := (hM (ν * age R y) hage_mem).trans (le_max_left M 0)
    rwa [Real.norm_eq_abs] at this
  have hD : |ϱD y (coordinateVector j)| ≤ 1 := w2_abs_ϱD y hyax j
  have hpow : r1 ^ 3 ≤ ϱ y ^ 3 := pow_le_pow_left₀ hr1pos.le hy 3
  have hdiv : 2 * R ^ 2 / ϱ y ^ 3 ≤ 2 * R ^ 2 / r1 ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hr1pos 3) hpow
  simp only [ageD, smul_apply, smul_eq_mul]
  rw [abs_mul, abs_mul, abs_of_pos hν, abs_mul, abs_neg,
    abs_of_nonneg (show 0 ≤ 2 * R ^ 2 / ϱ y ^ 3 by positivity)]
  have h1 : 2 * R ^ 2 / ϱ y ^ 3 * |ϱD y (coordinateVector j)| ≤ 2 * R ^ 2 / r1 ^ 3 := by
    calc 2 * R ^ 2 / ϱ y ^ 3 * |ϱD y (coordinateVector j)|
        ≤ 2 * R ^ 2 / ϱ y ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 2 * R ^ 2 / ϱ y ^ 3 := mul_one _
      _ ≤ 2 * R ^ 2 / r1 ^ 3 := hdiv
  have h2 : ν * (2 * R ^ 2 / ϱ y ^ 3 * |ϱD y (coordinateVector j)|) ≤
      ν * (2 * R ^ 2 / r1 ^ 3) :=
    mul_le_mul_of_nonneg_left h1 hν.le
  exact mul_le_mul hM' h2 (by positivity) (le_max_right M 0)

/-- Joint measurability of `wardX`. -/
theorem w3_wardX_measurable (ν μ R c : ℝ) {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) :
    Measurable (fun x : ℝ × Space => wardX ν μ R c χy g x.1 x.2) := by
  have hZ := wardX0_measurable_of_measurable ν μ R c g hg.measurable
  have hC := w2_corr_measurable (ν := ν) (μ := μ) (R := R) (c := c) (χy := χy) hg
  have hage : Measurable (fun x : ℝ × Space => χy (ν * age R x.2)) := by
    unfold age
    exact hχy.smooth.continuous.measurable.comp
      (measurable_const.mul (measurable_const.div
        ((continuous_ϱ.measurable.comp measurable_snd).pow_const 2)))
  have heq : (fun x : ℝ × Space => wardX ν μ R c χy g x.1 x.2) =
      fun x : ℝ × Space =>
        χy (ν * age R x.2) • wardX0 ν μ R c g x.1 x.2 +
          wardStreamCorr ν R χy (wardX0 ν μ R c g) x.1 x.2 := by
    funext x
    exact wardX_eq_cut_add_corr ν μ R c χy g x.1 x.2
  rw [heq]
  exact (hage.smul hZ).add hC

/-- Differentiability of `wardX` and product/sum expansion of `physPd (wardX ...)` on `youngOpen`. -/
theorem w3_wardX_diff_and_pd {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : y ∈ youngOpen ν R) :
    DifferentiableAt ℝ (wardX ν μ R c χy g τ) y ∧
      ∀ j : Fin 3, physPd (wardX ν μ R c χy g τ) j y =
        χy (ν * age R y) • physPd (wardX0 ν μ R c g τ) j y +
          ((deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector j)) •
            wardX0 ν μ R c g τ y +
          physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y := by
  have hyax : y ∉ axis := t9_not_axis hν hR hy
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hX0 : DifferentiableAt ℝ (wardX0 ν μ R c g τ) y :=
    ((w2_smooth hν hR hc hμ hg τ).contDiffAt (hUo.mem_nhds hy)).differentiableAt (by simp)
  have hcut := w3_cut_hasFDerivAt (R := R) (ν := ν) hχy hyax
  have hsmul := hcut.smul hX0.hasFDerivAt
  have hcorr : DifferentiableAt ℝ (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) y :=
    w2_corr_diff hχy hν hR hc hμ hg τ hy
  have hsum := hsmul.add hcorr.hasFDerivAt
  have heq : wardX ν μ R c χy g τ =
      (fun x : Space => χy (ν * age R x)) • wardX0 ν μ R c g τ +
        wardStreamCorr ν R χy (wardX0 ν μ R c g) τ := by
    funext x
    exact wardX_eq_cut_add_corr ν μ R c χy g τ x
  refine ⟨?_, fun j => ?_⟩
  · rw [heq]
    exact hsum.differentiableAt
  · unfold physPd
    rw [heq, hsum.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]

/-- **`WardXYoungL2` from `WardX0YoungL2` and `WardStreamCorrYoungL2`** (source 4171-4196). -/
theorem wardXYoungL2_of_parts (hA : WardX0YoungL2) (hB : WardStreamCorrYoungL2) :
    WardXYoungL2 := by
  classical
  intro ν μ R c χy hχy hν hR hc hμ
  obtain ⟨CA, hCA⟩ := hA ν μ R c hν hR hc hμ
  obtain ⟨CB, hCB⟩ := hB ν μ R c χy hχy hν hR hc hμ
  obtain ⟨Kcut, hKcut0, hKcut⟩ := w3_cut_deriv_bound R ν hχy hR hν
  set CA' : ℝ := max CA 0
  set CB' : ℝ := max CB 0
  have hCA' : 0 ≤ CA' := le_max_right _ _
  have hCB' : 0 ≤ CB' := le_max_right _ _
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  refine ⟨(1 + Kcut) * CA' + CB', fun g hg => ?_⟩
  obtain ⟨hX0, hX0'⟩ := hCA g hg
  obtain ⟨hCorr, hCorr'⟩ := hCB g hg
  have bX0 := wyl_bd_of_young hX0
  have bCorr := wyl_bd_of_young hCorr
  have hXm := w3_wardX_measurable ν μ R c hχy hg
  refine ⟨?_, fun j => ?_⟩
  · refine w10_young_of_sum
      (w10_read_meas hXm).aestronglyMeasurable bX0 bCorr hCA' hCB'
      (by nlinarith) ?_
    refine w10_read_dom hν hR fun τ y _ => ?_
    rw [wardX_eq_cut_add_corr]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hχy.range (ν * age R y)).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχy.range (ν * age R y)).2
  · have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
    have hdX : ∀ τ y, y ∈ youngOpen ν R → DifferentiableAt ℝ (wardX ν μ R c χy g τ) y :=
      fun τ y hy => (w3_wardX_diff_and_pd hχy hν hR hc hμ hg τ hy).1
    have hPd := w10_meas_pd hXm hUo.measurableSet hdX j
    have hread : wardYoungRead ν R (fun τ => physPd (wardX ν μ R c χy g τ) j) =
        wardYoungRead ν R (fun τ y =>
          if y ∈ youngOpen ν R then physPd (wardX ν μ R c χy g τ) j y else 0) := by
      refine w10_read_congr hν hR fun τ y hy => ?_
      have : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
      simp [this]
    have hFm : AEStronglyMeasurable
        (wardYoungRead ν R (fun τ => physPd (wardX ν μ R c χy g τ) j))
        (ageμ c (-3 / 2)) := by
      rw [hread]
      exact (w10_read_meas hPd).aestronglyMeasurable
    have bX0j := wyl_bd_of_young (hX0' j)
    have bCorrj := wyl_bd_of_young (hCorr' j)
    have bCutX0 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (fun q => Kcut * wardYoungRead ν R (wardX0 ν μ R c g) q) (Kcut * CA') := by
      simpa [abs_of_nonneg hKcut0] using bX0.const_mul Kcut
    have bSum1 := bX0j.add bCutX0 hCA' (mul_nonneg hKcut0 hCA')
    have bSum2 := bSum1.add bCorrj (add_nonneg hCA' (mul_nonneg hKcut0 hCA')) hCB'
    refine ⟨hFm, ?_⟩
    have hdom : ∀ q : Chart,
        wardYoungRead ν R (fun τ => physPd (wardX ν μ R c χy g τ) j) q ≤
          (wardYoungRead ν R (fun τ => physPd (wardX0 ν μ R c g τ) j) q +
            Kcut * wardYoungRead ν R (wardX0 ν μ R c g) q) +
          wardYoungRead ν R
            (fun τ => physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j) q := by
      intro q
      by_cases hq : ν * q.1 ≤ 1
      · rcases le_or_gt q.1 0 with hs | hs
        · rw [wyl_youngRead_zero_of_nonpos _ hs]
          exact add_nonneg (add_nonneg (wyl_youngRead_nonneg _ _ _ q)
            (mul_nonneg hKcut0 (wyl_youngRead_nonneg _ _ _ q)))
            (wyl_youngRead_nonneg _ _ _ q)
        · rw [wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
            wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq]
          set τ := NearInst.chartTau R q
          set y := NearInst.chartY R q
          have hy : R * Real.sqrt ν ≤ ϱ y := wyl_young_ϱ hν hR hs hq
          have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
          have hpd := (w3_wardX_diff_and_pd hχy hν hR hc hμ hg τ hyU).2 j
          have hnorm : ‖physPd (wardX ν μ R c χy g τ) j y‖ ≤
              (‖physPd (wardX0 ν μ R c g τ) j y‖ + Kcut * ‖wardX0 ν μ R c g τ y‖) +
                ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y‖ := by
            rw [hpd]
            refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχy.range (ν * age R y)).1]
              exact mul_le_of_le_one_left (norm_nonneg _) (hχy.range (ν * age R y)).2
            · rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right (hKcut y j hy) (norm_nonneg _)
          have hinv : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
          calc (Real.sqrt q.1)⁻¹ * ‖physPd (wardX ν μ R c χy g τ) j y‖
              ≤ (Real.sqrt q.1)⁻¹ *
                  ((‖physPd (wardX0 ν μ R c g τ) j y‖ + Kcut * ‖wardX0 ν μ R c g τ y‖) +
                    ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y‖) :=
                mul_le_mul_of_nonneg_left hnorm hinv
            _ = ((Real.sqrt q.1)⁻¹ * ‖physPd (wardX0 ν μ R c g τ) j y‖ +
                  Kcut * ((Real.sqrt q.1)⁻¹ * ‖wardX0 ν μ R c g τ y‖)) +
                  (Real.sqrt q.1)⁻¹ *
                    ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y‖ := by ring
      · have hqS : q ∉ wardYoungSet ν := hq
        have h0 : wardYoungRead ν R (fun τ => physPd (wardX ν μ R c χy g τ) j) q = 0 := by
          unfold wardYoungRead
          rw [indicator_of_notMem hqS]
        rw [h0]
        exact add_nonneg (add_nonneg (wyl_youngRead_nonneg _ _ _ q)
          (mul_nonneg hKcut0 (wyl_youngRead_nonneg _ _ _ q)))
          (wyl_youngRead_nonneg _ _ _ q)
    refine (eLpNorm_mono_real (fun q => ?_)).trans
      (bSum2.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl))
    rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ q)]
    exact hdom q

end UnforcedLeray.Short.PartIIIb.Concrete
end
