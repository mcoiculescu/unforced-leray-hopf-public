import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonOrg

/-!
# First radial moment bound for `sigmaM` (`PartIII-b:IIIb-D3/2/G5/2/3`)

Source of record: `the November 2 reference manuscript`, lines 4879-4884.
Proves `sigmaMFirstMoment`: `x' ↦ |x'| frob (sigmaM c ν chio M x')` is integrable on `ℝ × ℝ`
with integral at most `π * oldN1w c ν chio M`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

/-- Integrability of the cut first old moment integrand `u^{-2} chio(νu) ∫|M(u,·)|` on
`Ioi (6 / 5 / ν)`. -/
theorem w1_int {c ν : ℝ} {chio : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff chio)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    Integrable (fun u : ℝ =>
      u ^ (-(2 : ℝ)) * (chio (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)))
      (volume.restrict (Ioi (6 / 5 / ν))) := by
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hcont : Continuous (fun u : ℝ => chio (ν * u)) :=
    hχ.smooth.continuous.comp (continuous_const.mul continuous_id)
  have hp : Measurable (fun u : ℝ => u ^ (-(2 : ℝ))) := measurable_id.pow_const _
  have hG : AEStronglyMeasurable (fun u : ℝ => ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))
      (volume.restrict (Ioi (6 / 5 / ν))) := gAESM_bint hM
  refine Integrable.mono' ((w_int_base M hM).const_mul ((6 / 5 / ν) ^ (-(1 / 2 : ℝ))))
    (hp.aestronglyMeasurable.mul (hcont.aestronglyMeasurable.mul hG)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu_gt : 6 / 5 / ν < u := Set.mem_Ioi.1 hu
  have hu0 : (0 : ℝ) < u := ha.trans hu_gt
  have hGnn : 0 ≤ ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := integral_nonneg fun x => frob_nonneg' _
  have hr2 : 0 ≤ u ^ (-(2 : ℝ)) := Real.rpow_nonneg hu0.le _
  have hr32 : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
  have hr_split : u ^ (-(2 : ℝ)) = u ^ (-(1 / 2 : ℝ)) * u ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hu0]
    norm_num
  have hr_le : u ^ (-(1 / 2 : ℝ)) ≤ (6 / 5 / ν) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hu_gt.le (by norm_num)
  have hr2_le : u ^ (-(2 : ℝ)) ≤ (6 / 5 / ν) ^ (-(1 / 2 : ℝ)) * u ^ (-(3 / 2 : ℝ)) := by
    rw [hr_split]
    exact mul_le_mul_of_nonneg_right hr_le hr32
  have hχ_le : chio (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) ≤
      ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) :=
    mul_le_of_le_one_left hGnn (hχ.range _).2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr2 (mul_nonneg (hχ.range _).1 hGnn))]
  calc u ^ (-(2 : ℝ)) * (chio (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))
      ≤ ((6 / 5 / ν) ^ (-(1 / 2 : ℝ)) * u ^ (-(3 / 2 : ℝ))) *
          ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) :=
        mul_le_mul hr2_le hχ_le (mul_nonneg (hχ.range _).1 hGnn)
          (mul_nonneg (Real.rpow_nonneg ha.le _) hr32)
    _ = (6 / 5 / ν) ^ (-(1 / 2 : ℝ)) *
          (u ^ (-(3 / 2 : ℝ)) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) := by ring

/-- The weighted phase bound `H1 u = u^{-1/2} phaseB c ν chio M u` for the first radial moment. -/
def phaseB1 (c ν : ℝ) (chio : ℝ → ℝ) (M : Chart → Mat3) (u : ℝ) : ℝ :=
  u ^ (-(1 / 2 : ℝ)) * phaseB c ν chio M u

theorem phaseB1_nonneg {c ν : ℝ} {chio : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff chio)
    (M : Chart → Mat3) (u : ℝ) :
    0 ≤ phaseB1 c ν chio M u := by
  unfold phaseB1
  by_cases hu : 0 ≤ u
  · exact mul_nonneg (Real.rpow_nonneg hu _) (phaseB_nonneg c ν hχ M u)
  · have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
    have hnot : u ∉ Ioi (6 / 5 / ν) := by
      intro hmem
      have : 0 < u := ha.trans hmem
      linarith
    have h0 : phaseB c ν chio M u = 0 := by
      rw [phaseB_eq_ind_bint c ν hν hχ M, Set.indicator_of_notMem hnot]
    rw [h0, mul_zero]

theorem phaseB1_aesm {c ν : ℝ} {chio : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff chio)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    AEStronglyMeasurable (phaseB1 c ν chio M) (volume.restrict (Ioi (0 : ℝ))) :=
  (measurable_id.pow_const (-(1 / 2 : ℝ))).aestronglyMeasurable.mul
    (phaseB_aesm_bint hν hχ M hM)

/-- The cut first moment `oldN1w` controls the `ENNReal` polar integral of `phaseB1`. -/
theorem phaseB1_lintegral_W {c ν : ℝ} {chio : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff chio)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB1 c ν chio M u) ≤
      ENNReal.ofReal (oldN1w c ν chio M) := by
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hpt : ∀ u : ℝ, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB1 c ν chio M u) ≤
      (Ioi (6 / 5 / ν)).indicator
        (fun u => ENNReal.ofReal (u ^ (-(2 : ℝ)) *
          (chio (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)))) u := by
    intro u
    by_cases hu : u ∈ Ioi (6 / 5 / ν)
    · rw [Set.indicator_of_mem hu]
      apply ENNReal.ofReal_le_ofReal
      have hu0 : 0 < u := ha.trans (Set.mem_Ioi.1 hu)
      have hr : u ^ (-(3 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ)) = u ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add hu0]
        norm_num
      unfold phaseB1 phaseB
      rw [← mul_assoc, hr]
    · have h0 : phaseB c ν chio M u = 0 := by
        rw [phaseB_eq_ind_bint c ν hν hχ M, Set.indicator_of_notMem hu]
      unfold phaseB1
      rw [Set.indicator_of_notMem hu, h0, mul_zero, mul_zero, ENNReal.ofReal_zero]
  have hint := w1_int hν hχ M hM
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (6 / 5 / ν))] fun u : ℝ =>
      u ^ (-(2 : ℝ)) * (chio (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg (ha.trans (Set.mem_Ioi.1 hu)).le _)
      (mul_nonneg (hχ.range _).1 (integral_nonneg fun x => frob_nonneg' _))
  calc ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB1 c ν chio M u)
      ≤ ∫⁻ u in Ioi (0 : ℝ), (Ioi (6 / 5 / ν)).indicator
          (fun u => ENNReal.ofReal (u ^ (-(2 : ℝ)) *
            (chio (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)))) u :=
        lintegral_mono fun u => hpt u
    _ = ∫⁻ u in Ioi (6 / 5 / ν), ENNReal.ofReal (u ^ (-(2 : ℝ)) *
          (chio (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) := by
        rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Set.Ioi_inter_Ioi, sup_eq_left.2 ha.le]
    _ = ENNReal.ofReal (oldN1w c ν chio M) := by
        unfold oldN1w
        rw [ofReal_integral_eq_lintegral_ofReal hint hnn]

/-- `ENNReal` radial first moment bound on the plane:
`∫⁻ |x'| frob(Σ_M(x')) ≤ ENNReal.ofReal (π * oldN1w)`. -/
theorem sigmaM_firstMoment_lintegral_le {c ν : ℝ} {chio : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff chio) {M : Chart → Mat3} (hM : OldThinFinite c ν M) :
    ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x')) ≤
      ENNReal.ofReal (Real.pi * oldN1w c ν chio M) := by
  have hmeas : AEMeasurable (phaseB1 c ν chio M) (volume.restrict (Ioi (0 : ℝ))) :=
    (phaseB1_aesm hν hχ M hM).aemeasurable
  have hae : ∀ᵐ x' : ℝ × ℝ,
      Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x') ≤
        (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * phaseB1 c ν chio M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by
    filter_upwards [sigmaPointwise c ν chio hc hν hχ M hM] with x' hx'
    have hs : 0 ≤ x'.1 ^ 2 + x'.2 ^ 2 := by positivity
    have hsqrt_nn : 0 ≤ Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) := Real.sqrt_nonneg _
    have hrpow : (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ^ (-(1 / 2 : ℝ)) =
        Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) := by
      rw [Real.rpow_neg (inv_nonneg.2 hs), ← Real.sqrt_eq_rpow, Real.sqrt_inv, inv_inv]
    calc Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x')
        ≤ Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) *
            ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * phaseB c ν chio M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left hx' hsqrt_nn
      _ = (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
            phaseB1 c ν chio M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by
          unfold phaseB1
          rw [hrpow]
          ring
  calc ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal
        (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x'))
      ≤ ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
          phaseB1 c ν chio M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) :=
        lintegral_mono_ae (hae.mono fun x' h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB1 c ν chio M u) :=
        planePolar _ (phaseB1_nonneg hν hχ M) hmeas
    _ ≤ ENNReal.ofReal Real.pi * ENNReal.ofReal (oldN1w c ν chio M) := by
        gcongr
        exact phaseB1_lintegral_W hν hχ M hM
    _ = ENNReal.ofReal (Real.pi * oldN1w c ν chio M) :=
        (ENNReal.ofReal_mul Real.pi_pos.le).symm

/-- First radial moment bound for `sigmaM`: `∫ |x'| |Σ_M(x')|_F dx' ≤ π N₁^χ(M)`
(source 4879-4884). -/
theorem sigmaMFirstMoment (chio : ℝ → ℝ) : FlatUnif.G5.SigmaMFirstMoment chio := by
  intro c ν hc hν hχ M hM
  have hmeas_sig := sigmaMeas c ν chio hc hν hχ M hM
  have hsqrt : Measurable (fun x' : ℝ × ℝ => Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) :=
    Real.continuous_sqrt.measurable.comp
      ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
  have hf_meas : AEStronglyMeasurable
      (fun x' : ℝ × ℝ => Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x')) volume :=
    hsqrt.aestronglyMeasurable.mul (continuous_frob.comp_aestronglyMeasurable hmeas_sig)
  have hf_nn : ∀ x' : ℝ × ℝ,
      0 ≤ Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x') :=
    fun x' => mul_nonneg (Real.sqrt_nonneg _) (frob_nonneg' _)
  have hL := sigmaM_firstMoment_lintegral_le hc hν hχ hM
  have hN1 := oldN1w_nonneg (c := c) hν hχ M
  have hfin : (∫⁻ x' : ℝ × ℝ, ENNReal.ofReal
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x'))) < ∞ :=
    lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  have hg : Integrable
      (fun x' : ℝ × ℝ => Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x')) :=
    ⟨hf_meas, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf_nn)).2 hfin⟩
  refine ⟨hg, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf_nn) hf_meas]
  calc (∫⁻ x' : ℝ × ℝ, ENNReal.ofReal
        (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν chio M x'))).toReal
      ≤ (ENNReal.ofReal (Real.pi * oldN1w c ν chio M)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hL
    _ = Real.pi * oldN1w c ν chio M :=
        ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le hN1)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
