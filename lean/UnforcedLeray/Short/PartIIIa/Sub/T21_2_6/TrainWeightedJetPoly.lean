import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Units.B0238
import UnforcedLeray.Units.B0169
import UnforcedLeray.Lib.Train.Datum

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem trainWeightedJetPoly_of (hF : FluctJetWeighted) (hM : MeanJetWeighted)
    (hVc : VcWeightedJet) : TrainWeightedJetPoly := by
  intro k j
  obtain ⟨CF, NF, νF, hνF, hF'⟩ := hF k j
  obtain ⟨CM, NM, νM, hνM, hM'⟩ := hM k j
  obtain ⟨CV, hV'⟩ := hVc k j
  refine ⟨|CF| + |CM| + |CV|, max NF NM, min 1 (min νF νM), lt_min one_pos (lt_min hνF hνM), ?_⟩
  intro ν hν tr htr s hs x
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := le_trans hν.2 (min_le_left _ _)
  have hνF' : ν ∈ Ioc 0 νF :=
    ⟨hν0, le_trans hν.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hνM' : ν ∈ Ioc 0 νM :=
    ⟨hν0, le_trans hν.2 (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hinv : 1 ≤ ν⁻¹ := by
    have h := mul_inv_cancel₀ hν0.ne'
    nlinarith [inv_pos.2 hν0]
  have hinvnn : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
  have hc : ν ^ (-2 : ℝ) = ν⁻¹ ^ 2 := by
    rw [Real.rpow_neg hν0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      inv_pow]
  have hcpos : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have htr0 : tr.v 0 = UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) 0 := by
      calc tr.v 0 = UnforcedLeray.B0140.trainDatum (ν ^ (-2 : ℝ)) := tr.isTrain.initial
        _ = UnforcedLeray.Train.datum (ν ^ (-2 : ℝ)) :=
          UnforcedLeray.B0169.trainDatum_eq_datum _
        _ = UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) 0 :=
          (UnforcedLeray.Train.Vc_zero ν _).symm
    have hc1 : 1 ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
      rw [hc]
      exact one_le_pow₀ (one_le_pow₀ hinv)
    have hcl : UnforcedLeray.Short.IIIa.clockA ν 0 = 1 := by simp [UnforcedLeray.Short.IIIa.clockA]
    have hV0 := hV' ν (ν ^ (-2 : ℝ)) 0 hν0 hcpos le_rfl (by rw [hcl]; exact hc1) x
    rw [hcl] at hV0
    simp only [div_one, Real.one_rpow, Real.sqrt_one, one_pow, mul_one, inv_one] at hV0
    rw [htr0]
    have h1 : 1 ≤ ν⁻¹ ^ (max NF NM) := one_le_pow₀ hinv
    have hnn : 0 ≤ |CF| + |CM| + |CV| := by positivity
    have hCV : CV ≤ |CF| + |CM| + |CV| := by
      linarith [abs_nonneg CF, abs_nonneg CM, le_abs_self CV]
    calc (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) 0) x‖
        ≤ CV := hV0
      _ ≤ (|CF| + |CM| + |CV|) * ν⁻¹ ^ (max NF NM) * (1 + 0) ^ (max NF NM) := by
        rw [add_zero, one_pow, mul_one]
        linarith [mul_le_mul_of_nonneg_left h1 hnn]
  · have hVsm : ContDiff ℝ ∞ (tr.v s) := UnforcedLeray.B0238.contDiff_Vc tr hpos.le
    obtain ⟨hMsm, hMb⟩ := hM' ν hνM' tr htr s hpos
    have hA : ContDiff ℝ ∞ (fun z : UnforcedLeray.Cyl.Plane =>
        UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s) z) :=
      hVsm.sub hMsm
    have e1 : tr.v s = (fun z : UnforcedLeray.Cyl.Plane =>
        UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s) z) +
        (fun y : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) y.2) :=
      funext fun z => by simp [UnforcedLeray.Short.PartI.hfluct]
    have h2 : iteratedFDeriv ℝ j (tr.v s) x =
        iteratedFDeriv ℝ j (fun z : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s) z) x +
        iteratedFDeriv ℝ j (fun y : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) y.2) x := by
      conv_lhs => rw [e1]
      exact iteratedFDeriv_add_apply (hA.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))
        (hMsm.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))
    have hnorm : ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤
        ‖iteratedFDeriv ℝ j (fun z : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s) z) x‖ +
        ‖iteratedFDeriv ℝ j (fun y : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) y.2) x‖ := by
      rw [h2]
      exact norm_add_le _ _
    have hAb := hF' ν hνF' tr htr s hpos x
    have hBb := hMb x
    have ha0 : 0 ≤ ν⁻¹ ^ (max NF NM) := pow_nonneg hinvnn _
    have hb1 : 1 ≤ (1 + s) ^ (max NF NM) := one_le_pow₀ (by linarith)
    have hb0 : 0 ≤ (1 + s) ^ (max NF NM) := by linarith
    have hT1 : ν⁻¹ ^ NF ≤ ν⁻¹ ^ (max NF NM) := pow_le_pow_right₀ hinv (le_max_left _ _)
    have hT3 : ν⁻¹ ^ NM ≤ ν⁻¹ ^ (max NF NM) := pow_le_pow_right₀ hinv (le_max_right _ _)
    have hT4 : (1 + s) ^ NM ≤ (1 + s) ^ (max NF NM) :=
      pow_le_pow_right₀ (by linarith) (le_max_right _ _)
    have hA1 : (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (fun z : UnforcedLeray.Cyl.Plane =>
        UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s) z) x‖ ≤
        |CF| * (ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM)) := by
      refine le_trans hAb ?_
      calc CF * ν⁻¹ ^ NF ≤ |CF| * ν⁻¹ ^ NF :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hinvnn _)
        _ ≤ |CF| * ν⁻¹ ^ (max NF NM) := mul_le_mul_of_nonneg_left hT1 (abs_nonneg _)
        _ ≤ |CF| * (ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM)) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right ha0 hb1) (abs_nonneg _)
    have hB1 : (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (fun y : UnforcedLeray.Cyl.Plane =>
        UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) y.2) x‖ ≤
        |CM| * (ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM)) := by
      refine le_trans hBb ?_
      calc CM * ν⁻¹ ^ NM * (1 + s) ^ NM ≤ |CM| * ν⁻¹ ^ NM * (1 + s) ^ NM :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hinvnn _))
              (pow_nonneg (by linarith) _)
        _ = |CM| * (ν⁻¹ ^ NM * (1 + s) ^ NM) := by ring
        _ ≤ |CM| * (ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hT3 hT4 (by positivity) ha0) (abs_nonneg _)
    have hK : (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤
        (1 + x.2 ^ 2) ^ k * (‖iteratedFDeriv ℝ j (fun z : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s) z) x‖ +
        ‖iteratedFDeriv ℝ j (fun y : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) y.2) x‖) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    have hab0 : 0 ≤ ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM) := mul_nonneg ha0 hb0
    have habs := mul_nonneg (abs_nonneg CV) hab0
    calc (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (tr.v s) x‖
        ≤ (1 + x.2 ^ 2) ^ k * (‖iteratedFDeriv ℝ j (fun z : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s) z) x‖ +
        ‖iteratedFDeriv ℝ j (fun y : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) y.2) x‖) := hK
      _ = (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (fun z : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s) z) x‖ +
        (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (fun y : UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) y.2) x‖ := by ring
      _ ≤ |CF| * (ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM)) +
          |CM| * (ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM)) := add_le_add hA1 hB1
      _ ≤ (|CF| + |CM| + |CV|) * (ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM)) := by
          linarith
      _ = (|CF| + |CM| + |CV|) * ν⁻¹ ^ (max NF NM) * (1 + s) ^ (max NF NM) := by ring

end UnforcedLeray.Short.IIIa
