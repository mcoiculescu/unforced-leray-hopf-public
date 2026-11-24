import UnforcedLeray.Short.PartI.Sub.PartI_T14
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanEnergy
import UnforcedLeray.Short.PartI.Tasks.TrainL2DecayProof

/-!
# `PartI:T14/2` (`MeanStressPreOverlapL1Integral.lean`): pre-overlap `L¹` time integral of `meanStress`

Source of record: `the November 2 reference manuscript`, lines 406-414.

Proves `MeanStressPreOverlapL1Integral`: for `1 / 2 < ρ`, there exist `C, ν₀ > 0` such that for
`0 < ν ≤ ν₀` and `tr : B0140.TrainSol ν (trainPeriod ρ ν)` with `IsBUCTrain tr`
(`c = trainPeriod ρ ν`),
`∫⁻ r in Ioc 0 (B0146.overlapAge ν c), eLpNorm (meanStress tr r) 1 volume ≤
  ENNReal.ofReal (C * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) + ν ^ (-3 : ℝ) * c ^ (-7 : ℝ)))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc width)

/-! ### 1. Cell `L²` square integral and `L¹_η` bound on `meanStress` -/

private theorem integrable_slice_sq_and_integral_le {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    {f : Plane → Vec} (hf : Continuous f) (hl2 : cellL2 c f ≤ ENNReal.ofReal B) :
    Integrable (fun η : ℝ => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ ^ 2) volume ∧
      (∫ η : ℝ, (c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ ^ 2)) ≤ c⁻¹ * B ^ 2 := by
  have hmem : MemLp (fun z : Plane => ‖f z‖) 2 (Cyl.cellμ c) := by
    refine ⟨hf.norm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_norm]
    exact hl2.trans_lt ENNReal.ofReal_lt_top
  have hprod : Integrable (fun z : Plane => ‖f z‖ ^ 2)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) := by
    rw [← Cyl.cellμ_eq_prod]
    exact hmem.integrable_sq
  have hint : Integrable (fun η : ℝ => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ ^ 2) volume :=
    hprod.integral_prod_right.const_mul c⁻¹
  refine ⟨hint, ?_⟩
  have heq_f : cellL2 c f =
      ENNReal.ofReal (Real.sqrt (∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c))) := by
    unfold cellL2
    rw [← eLpNorm_norm]
    have h := jl2_abs_eLpNorm (Cyl.cellμ c) (fun z : Plane => ‖f z‖) hmem
    simpa [abs_of_nonneg (norm_nonneg _)] using h
  have hsqrt_le : Real.sqrt (∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c)) ≤ B := by
    rw [heq_f] at hl2
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 hl2
  have hcell_le : ∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c) ≤ B ^ 2 := by
    have hnn : 0 ≤ ∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c) :=
      integral_nonneg (fun _ => sq_nonneg _)
    calc ∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c)
        = (Real.sqrt (∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c))) ^ 2 := (Real.sq_sqrt hnn).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
  have hfub : ∫ η : ℝ, (c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ ^ 2) =
      c⁻¹ * ∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c) := by
    rw [integral_const_mul, Cyl.cellμ_eq_prod, ← MeasureTheory.integral_prod_symm _ hprod]
  rw [hfub]
  exact mul_le_mul_of_nonneg_left hcell_le (inv_nonneg.2 hc.le)

private theorem norm_error_prod_le {w V : Vec} {Bw BV : ℝ} (hBw : 0 < Bw) (hBV : 0 < BV) :
    ‖(w 0 + V 0) * (w 1 + V 1) - V 0 * V 1‖ ≤
      (1 + BV / Bw) * ‖w‖ ^ 2 + (Bw / BV) * ‖V‖ ^ 2 := by
  have hw0 : |w 0| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w 0
  have hw1 : |w 1| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w 1
  have hV0 : |V 0| ≤ ‖V‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le V 0
  have hV1 : |V 1| ≤ ‖V‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le V 1
  have halg : (w 0 + V 0) * (w 1 + V 1) - V 0 * V 1 =
      w 0 * V 1 + V 0 * w 1 + w 0 * w 1 := by ring
  rw [halg, Real.norm_eq_abs]
  have htri1 : |w 0 * V 1 + V 0 * w 1 + w 0 * w 1| ≤
      |w 0| * |V 1| + |V 0| * |w 1| + |w 0| * |w 1| := by
    calc |w 0 * V 1 + V 0 * w 1 + w 0 * w 1|
        ≤ |w 0 * V 1 + V 0 * w 1| + |w 0 * w 1| := abs_add_le _ _
      _ ≤ |w 0 * V 1| + |V 0 * w 1| + |w 0 * w 1| := by
          gcongr
          exact abs_add_le _ _
      _ = |w 0| * |V 1| + |V 0| * |w 1| + |w 0| * |w 1| := by
          simp only [abs_mul]
  have htri2 : |w 0| * |V 1| + |V 0| * |w 1| + |w 0| * |w 1| ≤
      2 * ‖w‖ * ‖V‖ + ‖w‖ ^ 2 := by
    have h1 : |w 0| * |V 1| ≤ ‖w‖ * ‖V‖ :=
      mul_le_mul hw0 hV1 (abs_nonneg _) (norm_nonneg _)
    have h2 : |V 0| * |w 1| ≤ ‖V‖ * ‖w‖ :=
      mul_le_mul hV0 hw1 (abs_nonneg _) (norm_nonneg _)
    have h3 : |w 0| * |w 1| ≤ ‖w‖ * ‖w‖ :=
      mul_le_mul hw0 hw1 (abs_nonneg _) (norm_nonneg _)
    nlinarith
  have hyoung : 2 * ‖w‖ * ‖V‖ ≤ (BV / Bw) * ‖w‖ ^ 2 + (Bw / BV) * ‖V‖ ^ 2 := by
    have hsq : 0 ≤ (Bw * BV)⁻¹ * (BV * ‖w‖ - Bw * ‖V‖) ^ 2 := by positivity
    have heq : (BV / Bw) * ‖w‖ ^ 2 + (Bw / BV) * ‖V‖ ^ 2 - 2 * ‖w‖ * ‖V‖ =
        (Bw * BV)⁻¹ * (BV * ‖w‖ - Bw * ‖V‖) ^ 2 := by
      field_simp [hBw.ne', hBV.ne']
      ring
    linarith
  linarith

/-- Pointwise-in-age `L¹_η` bound on `meanStress tr s` from `cellL2` bounds on
`w = tr.v s - Vc ν c s` and `V = Vc ν c s`. -/
theorem eLpNorm_meanStress_one_le {ν c s Bw BV : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s)
    (hBw : 0 < Bw) (hBV : 0 < BV) (tr : B0140.TrainSol ν c)
    (hw_l2 : cellL2 c (fun z : Plane => tr.v s z - Vc ν c s z) ≤ ENNReal.ofReal Bw)
    (hV_l2 : cellL2 c (Vc ν c s) ≤ ENNReal.ofReal BV) :
    eLpNorm (meanStress tr s) 1 volume ≤
      ENNReal.ofReal (c⁻¹ * (2 * Bw * BV + Bw ^ 2)) := by
  set w : Plane → Vec := fun z => tr.v s z - Vc ν c s z
  set V : Plane → Vec := Vc ν c s
  have hvc : Continuous (tr.v s) := by
    have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    exact hcont.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hs, mem_univ z⟩)
  have ha_pos : 0 < width ν s := by
    change 0 < 1 + ν * s
    nlinarith
  have hVc : Continuous V :=
    (UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc ha_pos).continuous
  have hwc : Continuous w := hvc.sub hVc
  obtain ⟨hw_int, hw_le⟩ := integrable_slice_sq_and_integral_le hc hBw.le hwc hw_l2
  obtain ⟨hV_int, hV_le⟩ := integrable_slice_sq_and_integral_le hc hBV.le hVc hV_l2
  set F : Plane → ℝ := fun z => tr.v s z 0 * tr.v s z 1 - V z 0 * V z 1
  set G : Plane → ℝ := fun z => (1 + BV / Bw) * ‖w z‖ ^ 2 + (Bw / BV) * ‖V z‖ ^ 2
  have hG_cont : Continuous G := by
    refine Continuous.add ?_ ?_
    · exact continuous_const.mul (hwc.norm.pow 2)
    · exact continuous_const.mul (hVc.norm.pow 2)
  have hFG : ∀ z : Plane, ‖F z‖ ≤ G z := by
    intro z
    have h0 : tr.v s z 0 = w z 0 + V z 0 := by simp [w, V, sub_add_cancel]
    have h1 : tr.v s z 1 = w z 1 + V z 1 := by simp [w, V, sub_add_cancel]
    dsimp only [F, G]
    rw [h0, h1]
    exact norm_error_prod_le hBw hBV
  have hpt : ∀ η : ℝ, ‖meanStress tr s η‖ ≤ c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), G (q, η) := by
    intro η
    rw [meanStress_eq_hmean_error hν hc hs tr η]
    exact meanEnergy_norm_hmean_le hc hG_cont hFG η
  have hG_slice_eq : (fun η : ℝ => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), G (q, η)) =
      fun η : ℝ => (1 + BV / Bw) * (c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖w (q, η)‖ ^ 2) +
        (Bw / BV) * (c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖V (q, η)‖ ^ 2) := by
    funext η
    have hline : Continuous (fun q : ℝ => ((q, η) : Plane)) :=
      continuous_id.prodMk continuous_const
    have h1 : Integrable (fun q : ℝ => (1 + BV / Bw) * ‖w (q, η)‖ ^ 2)
        (volume.restrict (Ico (-c / 2) (c / 2))) :=
      (((continuous_const.mul (hwc.norm.pow 2)).comp hline).integrableOn_Icc).mono_set
        Ico_subset_Icc_self
    have h2 : Integrable (fun q : ℝ => (Bw / BV) * ‖V (q, η)‖ ^ 2)
        (volume.restrict (Ico (-c / 2) (c / 2))) :=
      (((continuous_const.mul (hVc.norm.pow 2)).comp hline).integrableOn_Icc).mono_set
        Ico_subset_Icc_self
    dsimp only [G]
    rw [integral_add h1 h2, integral_const_mul, integral_const_mul]
    ring
  have hG_slice_int : Integrable (fun η : ℝ => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), G (q, η)) volume := by
    rw [hG_slice_eq]
    exact (hw_int.const_mul (1 + BV / Bw)).add (hV_int.const_mul (Bw / BV))
  have hstress_cont : Continuous (meanStress tr s) := by
    have hv0 : Continuous (fun z : Plane => tr.v s z 0) :=
      (PiLp.continuous_apply _ _ 0).comp hvc
    have hv1 : Continuous (fun z : Plane => tr.v s z 1) :=
      (PiLp.continuous_apply _ _ 1).comp hvc
    exact meanEnergy_hmean_continuous (hv0.mul hv1)
  have hstress_int : Integrable (meanStress tr s) volume :=
    Integrable.mono' hG_slice_int hstress_cont.aestronglyMeasurable (Eventually.of_forall hpt)
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hstress_int]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ η : ℝ, ‖meanStress tr s η‖
      ≤ ∫ η : ℝ, (c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), G (q, η)) :=
        integral_mono hstress_int.norm hG_slice_int hpt
    _ = (1 + BV / Bw) * (∫ η : ℝ, (c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖w (q, η)‖ ^ 2)) +
          (Bw / BV) * (∫ η : ℝ, (c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖V (q, η)‖ ^ 2)) := by
        rw [hG_slice_eq, integral_add (hw_int.const_mul _) (hV_int.const_mul _),
          integral_const_mul (1 + BV / Bw), integral_const_mul (Bw / BV)]
    _ ≤ (1 + BV / Bw) * (c⁻¹ * Bw ^ 2) + (Bw / BV) * (c⁻¹ * BV ^ 2) := by
        gcongr
    _ = c⁻¹ * (2 * Bw * BV + Bw ^ 2) := by
        field_simp [hBw.ne', hBV.ne']
        ring

/-! ### 2. Elementary exponential bounds for `a⁻³ e^{-b c² / a}` and `a⁻⁴ e^{-2b c² / a}` -/

private theorem cube_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 3 * Real.exp (-u) ≤ 27 := by
  have h1 : u / 3 ≤ Real.exp (u / 3) := by
    linarith [Real.add_one_le_exp (u / 3)]
  have h2 : (u / 3) ^ 3 ≤ (Real.exp (u / 3)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h1 3
  have h3 : (Real.exp (u / 3)) ^ 3 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : u ^ 3 ≤ 27 * Real.exp u := by
    have : (u / 3) ^ 3 = u ^ 3 / 27 := by ring
    rw [this, h3, div_le_iff₀ (by norm_num)] at h2
    linarith
  calc u ^ 3 * Real.exp (-u)
      ≤ (27 * Real.exp u) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 27 * (Real.exp u * Real.exp (-u)) := by ring
    _ = 27 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

private theorem fourth_mul_exp_neg_sq_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 4 * (Real.exp (-u)) ^ 2 ≤ 16 := by
  have h1 : u / 2 ≤ Real.exp (u / 2) := by
    linarith [Real.add_one_le_exp (u / 2)]
  have h2 : (u / 2) ^ 4 ≤ (Real.exp (u / 2)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (Real.exp (u / 2)) ^ 4 = Real.exp (2 * u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : u ^ 4 ≤ 16 * Real.exp (2 * u) := by
    have : (u / 2) ^ 4 = u ^ 4 / 16 := by ring
    rw [this, h3, div_le_iff₀ (by norm_num)] at h2
    linarith
  have hexp_sq : (Real.exp (-u)) ^ 2 = Real.exp (-(2 * u)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc u ^ 4 * (Real.exp (-u)) ^ 2
      = u ^ 4 * Real.exp (-(2 * u)) := by rw [hexp_sq]
    _ ≤ (16 * Real.exp (2 * u)) * Real.exp (-(2 * u)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 16 * (Real.exp (2 * u) * Real.exp (-(2 * u))) := by ring
    _ = 16 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

private theorem rpow_neg_two_zero_eq {a : ℝ} (ha : 0 < a) :
    a ^ (-(2 + (0 : ℝ) / 2)) = (a⁻¹) ^ 2 := by
  have h2 : -(2 + (0 : ℝ) / 2) = (-2 : ℝ) := by norm_num
  rw [h2, Real.rpow_neg ha.le, Real.rpow_two, inv_pow]

private theorem inv_cube_exp_le {b c a : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : 0 < a) :
    (a⁻¹) ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a)) ≤ 27 * b⁻¹ ^ 3 * (c⁻¹) ^ 6 := by
  set u := b * c ^ 2 / a
  have hu : 0 ≤ u := by positivity
  have h1 := cube_mul_exp_neg_le hu
  have heq : (a⁻¹) ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a)) =
      b⁻¹ ^ 3 * (c⁻¹) ^ 6 * (u ^ 3 * Real.exp (-u)) := by
    dsimp only [u]
    field_simp [hb.ne', hc.ne', ha.ne']
  rw [heq]
  calc b⁻¹ ^ 3 * (c⁻¹) ^ 6 * (u ^ 3 * Real.exp (-u))
      ≤ b⁻¹ ^ 3 * (c⁻¹) ^ 6 * 27 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 27 * b⁻¹ ^ 3 * (c⁻¹) ^ 6 := by ring

private theorem inv_fourth_exp_sq_le {b c a : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : 0 < a) :
    ((a⁻¹) ^ 2) ^ 2 * (Real.exp (-(b * c ^ 2 / a))) ^ 2 ≤ 16 * b⁻¹ ^ 4 * (c⁻¹) ^ 8 := by
  set u := b * c ^ 2 / a
  have hu : 0 ≤ u := by positivity
  have h1 := fourth_mul_exp_neg_sq_le hu
  have heq : ((a⁻¹) ^ 2) ^ 2 * (Real.exp (-(b * c ^ 2 / a))) ^ 2 =
      b⁻¹ ^ 4 * (c⁻¹) ^ 8 * (u ^ 4 * (Real.exp (-u)) ^ 2) := by
    dsimp only [u]
    field_simp [hb.ne', hc.ne', ha.ne']
  rw [heq]
  calc b⁻¹ ^ 4 * (c⁻¹) ^ 8 * (u ^ 4 * (Real.exp (-u)) ^ 2)
      ≤ b⁻¹ ^ 4 * (c⁻¹) ^ 8 * 16 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 16 * b⁻¹ ^ 4 * (c⁻¹) ^ 8 := by ring

/-! ### 3. Main theorem: `meanStressPreOverlapL1Integral_proof` (`PartI:T14/2`) -/

/-- **`PartI:T14/2` (`meanStressPreOverlapL1Integral_proof`)** (source lines 406-414):
proves `MeanStressPreOverlapL1Integral`. -/
theorem meanStressPreOverlapL1Integral_proof :
    UnforcedLeray.Short.PartI.MeanStressPreOverlapL1Integral := by
  intro ρ hρ
  obtain ⟨Ce, be, νe, hCe, hbe, hνe, hcomp⟩ := trainComparison_proof ρ hρ 0
  obtain ⟨CV, hCV, hVc⟩ := preOverlap_Vc_cellL2_bound
  obtain ⟨νp, hνp, _, hp⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
  let C1 : ℝ := 54 * Ce * CV * be⁻¹ ^ 3
  let C2 : ℝ := 16 * Ce ^ 2 * be⁻¹ ^ 4
  let C : ℝ := C1 + C2
  have hC1 : 0 < C1 := by positivity
  have hC2 : 0 < C2 := by positivity
  have hC : 0 < C := by positivity
  refine ⟨C, min νe νp, hC, lt_min hνe hνp, ?_⟩
  intro ν hν hν_le tr htr
  dsimp only
  let c := trainPeriod ρ ν
  have hν_e : ν ≤ νe := hν_le.trans (min_le_left _ _)
  have hν_p : ν ≤ νp := hν_le.trans (min_le_right _ _)
  obtain ⟨hc1, _⟩ := hp ν hν hν_p
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  let s_c := B0146.overlapAge ν c
  have hs_c_nn : 0 ≤ s_c := overlapAge_nonneg hν hc1
  let K : ℝ := C1 * ν⁻¹ * (c⁻¹) ^ 7 + C2 * (ν⁻¹) ^ 2 * (c⁻¹) ^ 9
  have hK_nn : 0 ≤ K := by positivity
  have hpt : ∀ r ∈ Ioc 0 s_c, eLpNorm (meanStress tr r) 1 volume ≤ ENNReal.ofReal K := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1.le
    have hr_le : r ≤ s_c := hr.2
    have hw_ge1 : 1 ≤ width ν r := by
      unfold width
      nlinarith
    have ha0 : 0 < width ν r := zero_lt_one.trans_le hw_ge1
    have hw_le_c2 : width ν r ≤ c ^ 2 := by
      have hw_sc : width ν s_c = c ^ 2 := width_overlapAge hν.ne'
      have hmono : width ν r ≤ width ν s_c := by
        unfold width
        nlinarith
      exact hmono.trans_eq hw_sc
    have hw_l2 : cellL2 c (fun z : Plane => tr.v r z - Vc ν c r z) ≤
        ENNReal.ofReal (Ce * ν⁻¹ * width ν r ^ (-(2 + (0 : ℝ) / 2)) *
          Real.exp (-(be * c ^ 2 / width ν r))) := by
      rw [← cellL2_jet_zero]
      simpa [c] using (hcomp ν hν hν_e tr htr r hr0 hw_le_c2).1
    have hV_l2 : cellL2 c (Vc ν c r) ≤ ENNReal.ofReal (CV * (width ν r)⁻¹) :=
      hVc ν c r hc0 hw_ge1 hw_le_c2
    set Bw := Ce * ν⁻¹ * width ν r ^ (-(2 + (0 : ℝ) / 2)) *
      Real.exp (-(be * c ^ 2 / width ν r))
    set BV := CV * (width ν r)⁻¹
    have hBw_pos : 0 < Bw := by positivity
    have hBV_pos : 0 < BV := by positivity
    have hstress := eLpNorm_meanStress_one_le hν hc0 hr0 hBw_pos hBV_pos tr hw_l2 hV_l2
    refine hstress.trans (ENNReal.ofReal_le_ofReal ?_)
    have hterm1 : c⁻¹ * (2 * Bw * BV) ≤ C1 * ν⁻¹ * (c⁻¹) ^ 7 := by
      have heq : c⁻¹ * (2 * Bw * BV) =
          (2 * Ce * CV * ν⁻¹ * c⁻¹) *
            ((width ν r)⁻¹ ^ 2 * (width ν r)⁻¹ * Real.exp (-(be * c ^ 2 / width ν r))) := by
        dsimp only [Bw, BV]
        rw [rpow_neg_two_zero_eq ha0]
        ring
      rw [heq]
      calc (2 * Ce * CV * ν⁻¹ * c⁻¹) *
              ((width ν r)⁻¹ ^ 2 * (width ν r)⁻¹ * Real.exp (-(be * c ^ 2 / width ν r)))
          ≤ (2 * Ce * CV * ν⁻¹ * c⁻¹) * (27 * be⁻¹ ^ 3 * (c⁻¹) ^ 6) :=
            mul_le_mul_of_nonneg_left (inv_cube_exp_le hbe hc0 ha0) (by positivity)
        _ = C1 * ν⁻¹ * (c⁻¹) ^ 7 := by
            dsimp only [C1]
            ring
    have hterm2 : c⁻¹ * Bw ^ 2 ≤ C2 * (ν⁻¹) ^ 2 * (c⁻¹) ^ 9 := by
      have heq : c⁻¹ * Bw ^ 2 =
          (Ce ^ 2 * (ν⁻¹) ^ 2 * c⁻¹) *
            (((width ν r)⁻¹ ^ 2) ^ 2 * (Real.exp (-(be * c ^ 2 / width ν r))) ^ 2) := by
        dsimp only [Bw]
        rw [rpow_neg_two_zero_eq ha0]
        ring
      rw [heq]
      calc (Ce ^ 2 * (ν⁻¹) ^ 2 * c⁻¹) *
              (((width ν r)⁻¹ ^ 2) ^ 2 * (Real.exp (-(be * c ^ 2 / width ν r))) ^ 2)
          ≤ (Ce ^ 2 * (ν⁻¹) ^ 2 * c⁻¹) * (16 * be⁻¹ ^ 4 * (c⁻¹) ^ 8) :=
            mul_le_mul_of_nonneg_left (inv_fourth_exp_sq_le hbe hc0 ha0) (by positivity)
        _ = C2 * (ν⁻¹) ^ 2 * (c⁻¹) ^ 9 := by
            dsimp only [C2]
            ring
    calc c⁻¹ * (2 * Bw * BV + Bw ^ 2)
        = c⁻¹ * (2 * Bw * BV) + c⁻¹ * Bw ^ 2 := by ring
      _ ≤ C1 * ν⁻¹ * (c⁻¹) ^ 7 + C2 * (ν⁻¹) ^ 2 * (c⁻¹) ^ 9 := add_le_add hterm1 hterm2
      _ = K := rfl
  have hlint : ∫⁻ r in Ioc 0 s_c, eLpNorm (meanStress tr r) 1 volume ≤
      ENNReal.ofReal K * ENNReal.ofReal s_c := by
    calc ∫⁻ r in Ioc 0 s_c, eLpNorm (meanStress tr r) 1 volume
        ≤ ∫⁻ _r in Ioc 0 s_c, ENNReal.ofReal K :=
          setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal K * volume (Ioc 0 s_c) := setLIntegral_const (Ioc 0 s_c) (ENNReal.ofReal K)
      _ = ENNReal.ofReal K * ENNReal.ofReal s_c := by rw [Real.volume_Ioc, sub_zero]
  have hsc_le : s_c ≤ ν⁻¹ * c ^ 2 := by
    dsimp only [s_c, B0146.overlapAge]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hν.le)
  have hpow_ν2 : ν ^ (-2 : ℝ) = (ν⁻¹) ^ 2 := by
    rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]
  have hpow_ν3 : ν ^ (-3 : ℝ) = (ν⁻¹) ^ 3 := by
    rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν.le, Real.rpow_natCast, inv_pow]
  have hpow_c5 : c ^ (-5 : ℝ) = (c⁻¹) ^ 5 := by
    rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc0.le, Real.rpow_natCast, inv_pow]
  have hpow_c7 : c ^ (-7 : ℝ) = (c⁻¹) ^ 7 := by
    rw [show (-7 : ℝ) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc0.le, Real.rpow_natCast, inv_pow]
  have hK_sc : K * s_c ≤ C * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) + ν ^ (-3 : ℝ) * c ^ (-7 : ℝ)) := by
    calc K * s_c
        ≤ K * (ν⁻¹ * c ^ 2) := mul_le_mul_of_nonneg_left hsc_le hK_nn
      _ = C1 * (ν⁻¹) ^ 2 * (c⁻¹) ^ 5 + C2 * (ν⁻¹) ^ 3 * (c⁻¹) ^ 7 := by
          dsimp only [K]
          field_simp [hν.ne', hc0.ne']
      _ = C1 * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ)) + C2 * (ν ^ (-3 : ℝ) * c ^ (-7 : ℝ)) := by
          rw [hpow_ν2, hpow_ν3, hpow_c5, hpow_c7]
          ring
      _ ≤ C * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) + ν ^ (-3 : ℝ) * c ^ (-7 : ℝ)) := by
          have ht1 : 0 ≤ ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) := by positivity
          have ht2 : 0 ≤ ν ^ (-3 : ℝ) * c ^ (-7 : ℝ) := by positivity
          dsimp only [C]
          nlinarith
  calc ∫⁻ r in Ioc 0 s_c, eLpNorm (meanStress tr r) 1 volume
      ≤ ENNReal.ofReal K * ENNReal.ofReal s_c := hlint
    _ = ENNReal.ofReal (K * s_c) := (ENNReal.ofReal_mul hK_nn).symm
    _ ≤ ENNReal.ofReal (C * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) + ν ^ (-3 : ℝ) * c ^ (-7 : ℝ))) :=
        ENNReal.ofReal_le_ofReal hK_sc

end UnforcedLeray.Short.PartI
