import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Convert
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Real
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Deriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Cont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.Int
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.Chi
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.IBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.GradYoung
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.Transport

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace AdjFieldIntH1Aux

lemma cutE0_le_of_eLpNorm {c m R M₀ ρ : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}
    (hmem : MemLp (ψ ρ) 2 (B0579.cellMeasure c (-m)))
    (he : eLpNorm (ψ ρ) 2 (B0579.cellMeasure c (-m)) ≤ ENNReal.ofReal M₀) :
    cutE0 c m R ψ ρ ≤ (max M₀ 0) ^ 2 := by
  have hint : Integrable (fun x => ‖ψ ρ x‖ ^ 2) (B0579.cellMeasure c (-m)) := by
    have h2 : MemLp (ψ ρ) ((2 : ℕ) : ℝ≥0∞) (B0579.cellMeasure c (-m)) := by
      exact_mod_cast hmem
    exact h2.integrable_norm_pow (by norm_num)
  have hbound : ∫ x, ‖ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) ≤ (max M₀ 0) ^ 2 :=
    CutLowerChiAux.integral_sq_le_of_eLpNorm hmem he
  have heq : cutE0 c m R ψ ρ = ∫ x, ladCut R x ^ 2 * ‖ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) := by
    unfold cutE0
    rw [integral_cellMeasure_eq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring
  rw [heq]
  calc ∫ x, ladCut R x ^ 2 * ‖ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure c (-m))
      ≤ ∫ x, ‖ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hint
          (ae_of_all _ fun x => mul_le_of_le_one_left (sq_nonneg _)
            (pow_le_one₀ (CutLowerTransportAux.ladCut_nonneg' R x)
              (CutLowerTransportAux.ladCut_le_one' R x)))
    _ ≤ (max M₀ 0) ^ 2 := hbound

lemma low_int {m ν t b R ρ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (ht : 0 ≤ t) {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hR : 0 < R) (hρ : ρ ∈ Ioo t b) :
    IntegrableOn (lowF1 tr m R ψ ρ) (B0579.cell (ν ^ (-2 : ℝ))) ∧
    IntegrableOn (lowF2 m R ψ ρ) (B0579.cell (ν ^ (-2 : ℝ))) ∧
    IntegrableOn (lowF3 tr m R ψ ρ) (B0579.cell (ν ^ (-2 : ℝ))) := by
  have hslice : ContDiff ℝ ∞ (ψ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hLc : Continuous (ladCut R) := (CutLowerIntAux.ladCut_contDiff' R).continuous
  have hJ : Continuous (fun x : ℝ × ℝ => B0579.jb x ^ (-m)) := B0579.continuous_jb_rpow (-m)
  have hPhi : Continuous (ψ ρ) := hslice.continuous
  have hChi : Continuous (ladChi tr ψ ρ) := continuous_ladChi tr ht hj hρ
  have hLL : Continuous (ladLapCx (ψ ρ)) := CutLowerIntAux.ladLapCx_continuous' hslice
  have hDt : Continuous (ladDt ψ ρ) := continuous_ladDt hj hρ
  have hC2 : Continuous (fun x : ℝ × ℝ => (ν : ℂ) * ladLapCx (ψ ρ) x) :=
    continuous_const.mul hLL
  have hTr : Continuous (fun x : ℝ × ℝ => ladTransport tr ρ (ψ ρ) x) := by
    have h0 : Continuous (fun x : ℝ × ℝ =>
        ladChi tr ψ ρ x - ladDt ψ ρ x - (ν : ℂ) * ladLapCx (ψ ρ) x) :=
      (hChi.sub hDt).sub hC2
    refine h0.congr (fun x => ?_)
    unfold ladChi
    ring
  have hF1 : Continuous (lowF1 tr m R ψ ρ) := by
    unfold lowF1
    exact (hLc.pow 2).mul (hJ.mul
      (Complex.continuous_re.comp ((Complex.continuous_conj.comp hPhi).mul hChi)))
  have hF2 : Continuous (lowF2 m R ψ ρ) := by
    unfold lowF2
    exact (hLc.pow 2).mul (hJ.mul
      (Complex.continuous_re.comp ((Complex.continuous_conj.comp hPhi).mul hLL)))
  have hF3 : Continuous (lowF3 tr m R ψ ρ) := by
    unfold lowF3
    exact (hLc.pow 2).mul (hJ.mul
      (Complex.continuous_re.comp ((Complex.continuous_conj.comp hPhi).mul hTr)))
  refine ⟨?_, ?_, ?_⟩
  · refine CutLowerIntAux.integrableOn_cell_box' (c := ν ^ (-2 : ℝ)) (R := R) hF1 ?_
    intro x hx hK
    simp [lowF1, CutLowerIntAux.ladCut_zero_of_not_box' hR hx hK]
  · refine CutLowerIntAux.integrableOn_cell_box' (c := ν ^ (-2 : ℝ)) (R := R) hF2 ?_
    intro x hx hK
    simp [lowF2, CutLowerIntAux.ladCut_zero_of_not_box' hR hx hK]
  · refine CutLowerIntAux.integrableOn_cell_box' (c := ν ^ (-2 : ℝ)) (R := R) hF3 ?_
    intro x hx hK
    simp [lowF3, CutLowerIntAux.ladCut_zero_of_not_box' hR hx hK]

lemma low_chi {m ν M₀ M R ρ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {ψ : ℝ → ℝ × ℝ → ℂ}
    (hfM : MemLp (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hM₀ : eLpNorm (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M₀)
    (hχM : MemLp (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hχb : eLpNorm (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M) :
    |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R ψ ρ x| ≤
      ((max M₀ 0) ^ 2 + (max M 0) ^ 2) / 2 := by
  have hφb : ∫ x, ‖ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ (max M₀ 0) ^ 2 :=
    CutLowerChiAux.integral_sq_le_of_eLpNorm hfM hM₀
  have hχb' : ∫ x, ‖ladChi tr ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
      (max M 0) ^ 2 :=
    CutLowerChiAux.integral_sq_le_of_eLpNorm hχM hχb
  have hfI : Integrable (fun x => ‖ψ ρ x‖ ^ 2) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    have h2 : MemLp (ψ ρ) ((2 : ℕ) : ℝ≥0∞) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
      exact_mod_cast hfM
    exact h2.integrable_norm_pow (by norm_num)
  have hχI : Integrable (fun x => ‖ladChi tr ψ ρ x‖ ^ 2)
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    have h2 : MemLp (ladChi tr ψ ρ) ((2 : ℕ) : ℝ≥0∞) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
      exact_mod_cast hχM
    exact h2.integrable_norm_pow (by norm_num)
  have hu : Integrable (fun x => (1 / 2 : ℝ) * (‖ψ ρ x‖ ^ 2 + ‖ladChi tr ψ ρ x‖ ^ 2))
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    (hfI.add hχI).const_mul (1 / 2 : ℝ)
  have hcell : IntegrableOn (fun x => B0579.jb x ^ (-m) *
      ((1 / 2 : ℝ) * (‖ψ ρ x‖ ^ 2 + ‖ladChi tr ψ ρ x‖ ^ 2))) (B0579.cell (ν ^ (-2 : ℝ))) := by
    have := (B0579.integrable_cellMeasure_iff (ν ^ (-2 : ℝ)) (-m)).1 hu
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell _)
    simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]
  have hpt : ∀ x : ℝ × ℝ, ‖lowF1 tr m R ψ ρ x‖ ≤
      B0579.jb x ^ (-m) * ((1 / 2 : ℝ) * (‖ψ ρ x‖ ^ 2 + ‖ladChi tr ψ ρ x‖ ^ 2)) := by
    intro x
    unfold lowF1
    have hJ0 : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have hre : |((starRingEnd ℂ) (ψ ρ x) * ladChi tr ψ ρ x).re| ≤
        ‖ψ ρ x‖ * ‖ladChi tr ψ ρ x‖ := by
      calc |((starRingEnd ℂ) (ψ ρ x) * ladChi tr ψ ρ x).re|
          ≤ ‖(starRingEnd ℂ) (ψ ρ x) * ladChi tr ψ ρ x‖ := Complex.abs_re_le_norm _
        _ = ‖ψ ρ x‖ * ‖ladChi tr ψ ρ x‖ := by rw [norm_mul, Complex.norm_conj]
    have hab : ‖ψ ρ x‖ * ‖ladChi tr ψ ρ x‖ ≤
        (1 / 2 : ℝ) * (‖ψ ρ x‖ ^ 2 + ‖ladChi tr ψ ρ x‖ ^ 2) := by
      nlinarith [sq_nonneg (‖ψ ρ x‖ - ‖ladChi tr ψ ρ x‖)]
    have ha0 := CutLowerChiAux.ladCut_nonneg' R x
    have ha1 := CutLowerChiAux.ladCut_le_one' R x
    have ha2 : ladCut R x ^ 2 ≤ 1 := by nlinarith
    have hJre : 0 ≤ B0579.jb x ^ (-m) *
        |((starRingEnd ℂ) (ψ ρ x) * ladChi tr ψ ρ x).re| :=
      mul_nonneg hJ0 (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul,
      abs_of_nonneg hJ0]
    nlinarith [mul_le_mul_of_nonneg_right ha2 hJre,
      mul_le_mul_of_nonneg_left (hre.trans hab) hJ0]
  have hbound1 : |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R ψ ρ x| ≤
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.jb x ^ (-m) *
        ((1 / 2 : ℝ) * (‖ψ ρ x‖ ^ 2 + ‖ladChi tr ψ ρ x‖ ^ 2)) := by
    calc |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R ψ ρ x|
        = ‖∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R ψ ρ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ‖lowF1 tr m R ψ ρ x‖ := norm_integral_le_integral_norm _
      _ ≤ _ := integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hcell
          (ae_of_all _ hpt)
  have hval := integral_cellMeasure_eq (ν ^ (-2 : ℝ)) m
    (fun x => (1 / 2 : ℝ) * (‖ψ ρ x‖ ^ 2 + ‖ladChi tr ψ ρ x‖ ^ 2))
  rw [← hval] at hbound1
  rw [integral_const_mul, integral_add hfI hχI] at hbound1
  nlinarith [hbound1, hφb, hχb']

lemma low_ibp {m ν t b R ρ : ℝ} (hν : 0 < ν) {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hper : ∀ r ∈ Ico t b, ∀ x : ℝ × ℝ, ψ r (x.1 + ν ^ (-2 : ℝ), x.2) = ψ r x)
    (hmem : ∀ r ∈ Ico t b, MemLp (ψ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hR : 0 < R) (hρ : ρ ∈ Ioo t b) :
    ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF2 m R ψ ρ x =
      -∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ -
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowFJ m R ψ ρ x := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hΦs : ContDiff ℝ ∞ (ψ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hΦc : Continuous (ψ ρ) := hΦs.continuous
  have hperρ : ∀ x : ℝ × ℝ, ψ ρ (x.1 + ν ^ (-2 : ℝ), x.2) = ψ ρ x :=
    hper ρ (Ioo_subset_Ico_self hρ)
  have hfM : MemLp (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    hmem ρ (Ioo_subset_Ico_self hρ)
  have hIBP := cutIBP (ν ^ (-2 : ℝ)) m R (ψ ρ) (ψ ρ) hc hR hΦs hΦs hperρ hperρ
  have hI := (cutRateIntegrable m (ν ^ (-2 : ℝ)) R (ψ ρ) (ψ ρ) (ψ ρ) hc hR hΦs hΦc hΦc
    hfM).2.1
  have eG : ∀ k : Fin 2, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * (2 * ((starRingEnd ℂ) (pdCx k (ψ ρ) x) *
        pdCx k (ψ ρ) x).re)) = 2 * cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ := by
    intro k
    unfold cutGReal
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [CutLowerIBPAux.re_conj_self]
    ring
  simp only [Fin.sum_univ_two] at hIBP
  unfold cutRate at hIBP
  simp only [Fin.sum_univ_two] at hIBP
  rw [eG 0, eG 1] at hIBP
  have hL2 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF2 m R ψ ρ x =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        ((starRingEnd ℂ) (ladLapCx (ψ ρ) x) * ψ ρ x).re) := by
    congr 1
    funext x
    unfold lowF2
    rw [CutLowerIBPAux.re_conj_comm]
  have hJ : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowFJ m R ψ ρ x =
      (∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.pd 0 (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
          ((starRingEnd ℂ) (pdCx 0 (ψ ρ) x) * ψ ρ x).re) +
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.pd 1 (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
          ((starRingEnd ℂ) (pdCx 1 (ψ ρ) x) * ψ ρ x).re := by
    rw [← integral_add (hI 0) (hI 1)]
    congr 1
    funext x
    exact CutLowerIBPAux.re_conj_mul_ofReal_add (ψ ρ x) (pdCx 0 (ψ ρ) x) (pdCx 1 (ψ ρ) x) _ _
  rw [Fin.sum_univ_two]
  linarith [hIBP, hL2, hJ]

lemma low_grad {m ν t b M₀ : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hmem : ∀ r ∈ Ico t b, MemLp (ψ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hM₀ : ∀ ρ ∈ Ioo t b, eLpNorm (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M₀) :
    ∃ K₂ : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t b,
      |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowFJ m R ψ ρ x| ≤
        (1 / 4 : ℝ) * ∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ + K₂ := by
  obtain ⟨Kc, hK0, hKP⟩ := ladCutProps
  refine ⟨2 * (2 * Kc + 2 * |m|) ^ 2 * (max M₀ 0) ^ 2, fun R hR ρ hρ => ?_⟩
  have hR1 : (1 : ℝ) ≤ R := hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  obtain ⟨-, -, -, -, hpd, -⟩ := hKP R hR0
  have hΦs : ContDiff ℝ ∞ (ψ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hfM : MemLp (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    hmem ρ (Ioo_subset_Ico_self hρ)
  have hφb : ∫ x, ‖ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ (max M₀ 0) ^ 2 :=
    CutLowerChiAux.integral_sq_le_of_eLpNorm hfM (hM₀ ρ hρ)
  have hfI : Integrable (fun x => ‖ψ ρ x‖ ^ 2) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    have h2 : MemLp (ψ ρ) ((2 : ℕ) : ℝ≥0∞) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
      exact_mod_cast hfM
    exact h2.integrable_norm_pow (by norm_num)
  have hcellU : IntegrableOn (fun x => B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)
      (B0579.cell (ν ^ (-2 : ℝ))) := by
    have := (B0579.integrable_cellMeasure_iff (ν ^ (-2 : ℝ)) (-m)).1 hfI
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell _)
    simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]
  have hG0 := CutLowerGradAux.integrable_G (c := ν ^ (-2 : ℝ)) (m := m) hR0 hΦs 0
  have hG1 := CutLowerGradAux.integrable_G (c := ν ^ (-2 : ℝ)) (m := m) hR0 hΦs 1
  set K2 := 2 * Kc + 2 * |m|
  have hgI : IntegrableOn (fun x => 2 * K2 ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2) +
      (1 / 4 : ℝ) * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    (hcellU.const_mul (2 * K2 ^ 2)).add ((hG0.add hG1).const_mul (1 / 4 : ℝ))
  have hpt : ∀ x : ℝ × ℝ, |lowFJ m R ψ ρ x| ≤ 2 * K2 ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2) +
      (1 / 4 : ℝ) * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)) := by
    intro x
    unfold lowFJ
    refine le_trans (CutLowerGradAux.re_bound _ _ _ _ _) ?_
    have ha0 : |B0579.pd 0 (lowW m R) x| ≤ K2 * (ladCut R x * B0579.jb x ^ (-m)) :=
      CutLowerGradAux.pd_weight_bound hK0 hR1 hpd x 0
    have ha1 : |B0579.pd 1 (lowW m R) x| ≤ K2 * (ladCut R x * B0579.jb x ^ (-m)) :=
      CutLowerGradAux.pd_weight_bound hK0 hR1 hpd x 1
    have hp0 : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have hu : 0 ≤ ‖ψ ρ x‖ := norm_nonneg _
    have hv0 : 0 ≤ ‖pdCx 0 (ψ ρ) x‖ := norm_nonneg _
    have hv1 : 0 ≤ ‖pdCx 1 (ψ ρ) x‖ := norm_nonneg _
    have hs : |B0579.pd 0 (lowW m R) x| * (‖pdCx 0 (ψ ρ) x‖ * ‖ψ ρ x‖) +
        |B0579.pd 1 (lowW m R) x| * (‖pdCx 1 (ψ ρ) x‖ * ‖ψ ρ x‖) ≤
        K2 * (ladCut R x * B0579.jb x ^ (-m)) * ‖ψ ρ x‖ *
          (‖pdCx 0 (ψ ρ) x‖ + ‖pdCx 1 (ψ ρ) x‖) := by
      nlinarith [mul_le_mul_of_nonneg_right ha0 (mul_nonneg hv0 hu),
        mul_le_mul_of_nonneg_right ha1 (mul_nonneg hv1 hu)]
    have hy := CutLowerGradAux.young_grad K2 (ladCut R x) (B0579.jb x ^ (-m)) ‖ψ ρ x‖
      ‖pdCx 0 (ψ ρ) x‖ ‖pdCx 1 (ψ ρ) x‖ hp0
    have e : K2 * (ladCut R x * B0579.jb x ^ (-m)) * ‖ψ ρ x‖ *
        (‖pdCx 0 (ψ ρ) x‖ + ‖pdCx 1 (ψ ρ) x‖) =
        K2 * ladCut R x * B0579.jb x ^ (-m) * ‖ψ ρ x‖ *
          (‖pdCx 0 (ψ ρ) x‖ + ‖pdCx 1 (ψ ρ) x‖) := by ring
    nlinarith [hs, hy, e]
  have hpu : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2 =
      ∫ x, ‖ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    (integral_cellMeasure_eq (ν ^ (-2 : ℝ)) m (fun x => ‖ψ ρ x‖ ^ 2)).symm
  have hmono := integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) hgI
    (ae_of_all _ hpt)
  have habs := abs_integral_le_integral_abs (μ := volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))
    (f := fun x => lowFJ m R ψ ρ x)
  have hsplit : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (2 * K2 ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2) +
        (1 / 4 : ℝ) * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2) +
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2))) =
      2 * K2 ^ 2 * (∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2) +
        (1 / 4 : ℝ) * ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2)) +
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)) := by
    have hI1 : IntegrableOn (fun x => 2 * K2 ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2))
        (B0579.cell (ν ^ (-2 : ℝ))) := hcellU.const_mul (2 * K2 ^ 2)
    have hI2 : IntegrableOn (fun x => (1 / 4 : ℝ) * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        ‖pdCx 0 (ψ ρ) x‖ ^ 2) + ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)))
        (B0579.cell (ν ^ (-2 : ℝ))) := (hG0.add hG1).const_mul (1 / 4 : ℝ)
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_add hG0 hG1]
  have hbnd : 2 * K2 ^ 2 * (∫ x, ‖ψ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) ≤
      2 * K2 ^ 2 * (max M₀ 0) ^ 2 :=
    mul_le_mul_of_nonneg_left hφb (by positivity)
  rw [Fin.sum_univ_two]
  unfold cutGReal
  have final : |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowFJ m R ψ ρ x| ≤
      2 * K2 ^ 2 * (∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2) +
        (1 / 4 : ℝ) * ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2)) +
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)) := by
    rw [← hsplit]
    exact le_trans habs hmono
  rw [hpu] at final
  linarith [final, hbnd]

lemma low_tr {m ν t b M₀ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (htb : t < b)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hb : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hmem : ∀ r ∈ Ico t b, MemLp (ψ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hM₀ : ∀ ρ ∈ Ioo t b, eLpNorm (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M₀) :
    ∃ K₃ : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t b,
      |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF3 tr m R ψ ρ x| ≤
        (ν / 4) * ∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ + K₃ := by
  have hb0 : 0 ≤ b := by linarith
  obtain ⟨C, hC⟩ := hb b hb0
  refine ⟨4 * C ^ 2 / ν * (max M₀ 0) ^ 2, fun R hR ρ hρ => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hρC : ρ ∈ Icc (0 : ℝ) b := ⟨le_trans ht hρ.1.le, hρ.2.le⟩
  have hρD : ρ ∈ Ico t b := ⟨hρ.1.le, hρ.2⟩
  have hΦ : ContDiff ℝ ∞ (ψ ρ) := CutLowerTransportAux.slice_contDiff hj hρD
  have hmemρ : MemLp (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hmem ρ hρD
  have hE : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2) ≤ (max M₀ 0) ^ 2 :=
    cutE0_le_of_eLpNorm (R := R) hmemρ (hM₀ ρ hρ)
  have hpt : ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)), ‖lowF3 tr m R ψ ρ x‖ ≤
      ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)) +
      4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)) := by
    intro x hx
    have hv := (hC ρ hρC x hx).1
    have hT : ‖ladTransport tr ρ (ψ ρ) x‖ ≤
        C * ‖pdCx 0 (ψ ρ) x‖ + C * ‖pdCx 1 (ψ ρ) x‖ := by
      unfold ladTransport
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_right (hv 0) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hv 1) (norm_nonneg _))
    have hRe : |((starRingEnd ℂ) (ψ ρ x) * ladTransport tr ρ (ψ ρ) x).re| ≤
        ‖ψ ρ x‖ * (C * ‖pdCx 0 (ψ ρ) x‖ + C * ‖pdCx 1 (ψ ρ) x‖) := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left hT (norm_nonneg _)
    have hkey : ‖ψ ρ x‖ * (C * ‖pdCx 0 (ψ ρ) x‖ + C * ‖pdCx 1 (ψ ρ) x‖) ≤
        ν / 8 * (‖pdCx 0 (ψ ρ) x‖ ^ 2 + ‖pdCx 1 (ψ ρ) x‖ ^ 2) + 4 * C ^ 2 / ν * ‖ψ ρ x‖ ^ 2 := by
      have h0 := CutLowerTransportAux.amgm_aux (C := C) (p := ‖ψ ρ x‖) (a := ‖pdCx 0 (ψ ρ) x‖) hν
      have h1 := CutLowerTransportAux.amgm_aux (C := C) (p := ‖ψ ρ x‖) (a := ‖pdCx 1 (ψ ρ) x‖) hν
      calc ‖ψ ρ x‖ * (C * ‖pdCx 0 (ψ ρ) x‖ + C * ‖pdCx 1 (ψ ρ) x‖)
          = C * ‖ψ ρ x‖ * ‖pdCx 0 (ψ ρ) x‖ + C * ‖ψ ρ x‖ * ‖pdCx 1 (ψ ρ) x‖ := by ring
        _ ≤ (ν / 8 * ‖pdCx 0 (ψ ρ) x‖ ^ 2 + 2 * C ^ 2 / ν * ‖ψ ρ x‖ ^ 2) +
            (ν / 8 * ‖pdCx 1 (ψ ρ) x‖ ^ 2 + 2 * C ^ 2 / ν * ‖ψ ρ x‖ ^ 2) := add_le_add h0 h1
        _ = ν / 8 * (‖pdCx 0 (ψ ρ) x‖ ^ 2 + ‖pdCx 1 (ψ ρ) x‖ ^ 2) +
            4 * C ^ 2 / ν * ‖ψ ρ x‖ ^ 2 := by ring
    have hmain := hRe.trans hkey
    have hW : 0 ≤ ladCut R x ^ 2 * B0579.jb x ^ (-m) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (B0579.jb_pos x).le _)
    have hf : ‖lowF3 tr m R ψ ρ x‖ = ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        |((starRingEnd ℂ) (ψ ρ x) * ladTransport tr ρ (ψ ρ) x).re|) := by
      unfold lowF3
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)]
    rw [hf]
    calc ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
          |((starRingEnd ℂ) (ψ ρ x) * ladTransport tr ρ (ψ ρ) x).re|)
        = (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
            |((starRingEnd ℂ) (ψ ρ x) * ladTransport tr ρ (ψ ρ) x).re| := by ring
      _ ≤ (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
            (ν / 8 * (‖pdCx 0 (ψ ρ) x‖ ^ 2 + ‖pdCx 1 (ψ ρ) x‖ ^ 2) +
              4 * C ^ 2 / ν * ‖ψ ρ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hmain hW
      _ = ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2) +
            ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)) +
          4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)) := by ring
  have hcont : ∀ k : Fin 2, Continuous (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k (ψ ρ) x‖ ^ 2)) := fun k =>
    ((CutLowerTransportAux.ladCut_continuous' R).pow 2).mul
      ((B0579.continuous_jb_rpow (-m)).mul ((CutLowerTransportAux.pdCx_continuous' hΦ k).norm.pow 2))
  have hcontE : Continuous (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)) :=
    ((CutLowerTransportAux.ladCut_continuous' R).pow 2).mul
      ((B0579.continuous_jb_rpow (-m)).mul (hΦ.continuous.norm.pow 2))
  have hband : ∀ k : Fin 2, ∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 →
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k (ψ ρ) x‖ ^ 2) = 0 := by
    intro k x hx
    rw [CutLowerTransportAux.ladCut_zero_of_band hR0 hx]
    simp
  have hbandE : ∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 →
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2) = 0 := by
    intro x hx
    rw [CutLowerTransportAux.ladCut_zero_of_band hR0 hx]
    simp
  have hI0 : IntegrableOn (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    CutLowerTransportAux.integrableOn_band hR0 (hcont 0) (hband 0)
  have hI1 : IntegrableOn (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    CutLowerTransportAux.integrableOn_band hR0 (hcont 1) (hband 1)
  have hIE : IntegrableOn (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    CutLowerTransportAux.integrableOn_band hR0 hcontE hbandE
  have hA : Integrable (fun x : ℝ × ℝ =>
      ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)))
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) :=
    (Integrable.add hI0 hI1).const_mul _
  have hB : Integrable (fun x : ℝ × ℝ =>
      4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)))
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) :=
    hIE.const_mul _
  have hgI : Integrable (fun x : ℝ × ℝ =>
      ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)) +
      4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)))
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) :=
    hA.add hB
  have hsplit : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (ψ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (ψ ρ) x‖ ^ 2)) +
      4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)))
      = ν / 8 * (cutGReal (ν ^ (-2 : ℝ)) m R ψ 0 ρ + cutGReal (ν ^ (-2 : ℝ)) m R ψ 1 ρ) +
        4 * C ^ 2 / ν * (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)) := by
    unfold cutGReal
    rw [integral_add hA hB, integral_const_mul, integral_const_mul, integral_add hI0 hI1]
  have hG0 : 0 ≤ cutGReal (ν ^ (-2 : ℝ)) m R ψ 0 ρ := by
    unfold cutGReal
    refine setIntegral_nonneg (B0579.measurableSet_cell _) (fun x _ => ?_)
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))
  have hG1 : 0 ≤ cutGReal (ν ^ (-2 : ℝ)) m R ψ 1 ρ := by
    unfold cutGReal
    refine setIntegral_nonneg (B0579.measurableSet_cell _) (fun x _ => ?_)
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))
  have hnorm := norm_integral_le_of_norm_le hgI
    ((ae_restrict_mem (B0579.measurableSet_cell _)).mono fun x hx => hpt x hx)
  have hpos : 0 ≤ ν * (cutGReal (ν ^ (-2 : ℝ)) m R ψ 0 ρ + cutGReal (ν ^ (-2 : ℝ)) m R ψ 1 ρ) :=
    mul_nonneg hν.le (add_nonneg hG0 hG1)
  have hK : 4 * C ^ 2 / ν * (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ ρ x‖ ^ 2)) ≤ 4 * C ^ 2 / ν * (max M₀ 0) ^ 2 :=
    mul_le_mul_of_nonneg_left hE (div_nonneg (by positivity) hν.le)
  rw [← Real.norm_eq_abs, Fin.sum_univ_two]
  rw [hsplit] at hnorm
  nlinarith [hnorm, hpos, hK]

lemma rate_lower {m ν t b M₀ M : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (htb : t < b)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hb : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hper : ∀ r ∈ Ico t b, ∀ x : ℝ × ℝ, ψ r (x.1 + ν ^ (-2 : ℝ), x.2) = ψ r x)
    (hmem : ∀ r ∈ Ico t b, MemLp (ψ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hM₀ : ∀ ρ ∈ Ioo t b, eLpNorm (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M₀)
    (hM : ∀ ρ ∈ Ioo t b,
      MemLp (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
      eLpNorm (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M) :
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t b,
      ν * ∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ - K ≤
        cutE0Rate (ν ^ (-2 : ℝ)) m R ψ ρ := by
  obtain ⟨K4, hK4⟩ := low_grad hj hmem hM₀
  obtain ⟨K5, hK5⟩ := low_tr hν ht htb tr hb hj hmem hM₀
  set K1 : ℝ := ((max M₀ 0) ^ 2 + (max M 0) ^ 2) / 2
  refine ⟨2 * K1 + 2 * ν * K4 + 2 * K5, fun R hR ρ hρ => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  obtain ⟨i1, i2, i3⟩ := low_int tr ht hj hR0 hρ
  have hI := low_ibp hν hj hper hmem hR0 hρ
  have hpt : ∀ x : ℝ × ℝ,
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (ψ ρ x) * ladDt ψ ρ x).re) =
        lowF1 tr m R ψ ρ x - ν * lowF2 m R ψ ρ x - lowF3 tr m R ψ ρ x := by
    intro x
    have hd : ladDt ψ ρ x = ladChi tr ψ ρ x - (ν : ℂ) * ladLapCx (ψ ρ) x -
        ladTransport tr ρ (ψ ρ) x := by
      unfold ladChi; ring
    simp only [lowF1, lowF2, lowF3, hd, mul_sub, Complex.sub_re]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hrate : cutE0Rate (ν ^ (-2 : ℝ)) m R ψ ρ =
      2 * ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R ψ ρ x) -
        ν * (∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF2 m R ψ ρ x) -
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF3 tr m R ψ ρ x) := by
    unfold cutE0Rate
    simp_rw [hpt]
    have j2 : IntegrableOn (fun x => ν * lowF2 m R ψ ρ x) (B0579.cell (ν ^ (-2 : ℝ))) :=
      i2.const_mul ν
    have j12 : IntegrableOn (fun x => lowF1 tr m R ψ ρ x - ν * lowF2 m R ψ ρ x)
        (B0579.cell (ν ^ (-2 : ℝ))) := i1.sub j2
    rw [integral_sub j12 i3, integral_sub i1 j2, integral_const_mul]
  have b1 : |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R ψ ρ x| ≤ K1 :=
    low_chi tr (hmem ρ (Ioo_subset_Ico_self hρ)) (hM₀ ρ hρ) (hM ρ hρ).1 (hM ρ hρ).2
  have a1 := abs_le.1 b1
  have a4 := abs_le.1 (hK4 R hR ρ hρ)
  have a5 := abs_le.1 (hK5 R hR ρ hρ)
  rw [hrate, hI]
  nlinarith [mul_le_mul_of_nonneg_left a4.1 hν.le, a1.1, a5.2, a4.2,
    mul_le_mul_of_nonneg_left a4.2 hν.le]

lemma cutE0_cont {m ν t b R : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hR : 0 < R) :
    ContinuousOn (cutE0 (ν ^ (-2 : ℝ)) m R ψ) (Ico t b) ∧
    ContinuousOn (cutE0Rate (ν ^ (-2 : ℝ)) m R ψ) (Ico t b) ∧
    ∀ k : Fin 2, ContinuousOn (cutGReal (ν ^ (-2 : ℝ)) m R ψ k) (Ico t b) := by
  have hF : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ) :=
    hj.continuousOn
  have hJ : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m)) (Ico t b ×ˢ univ) :=
    ((B0579.continuous_jb_rpow (-m)).comp continuous_snd).continuousOn
  have hLD := AdjCutE0ContAux.continuousOn_ladDt_strip hj
  have hE0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m) * ‖ψ p.1 p.2‖ ^ 2)
      (Ico t b ×ˢ univ) :=
    hJ.mul (hF.norm.pow 2)
  have hRate : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m) *
      ((starRingEnd ℂ) (ψ p.1 p.2) * ladDt ψ p.1 p.2).re) (Ico t b ×ˢ univ) :=
    hJ.mul (Complex.continuous_re.comp_continuousOn
      ((Complex.continuous_conj.comp_continuousOn hF).mul hLD))
  have hGk : ∀ k : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      B0579.jb p.2 ^ (-m) * ‖pdCx k (ψ p.1) p.2‖ ^ 2) (Ico t b ×ˢ univ) := fun k =>
    hJ.mul ((jointSmooth_pdCx hj k).continuousOn.norm.pow 2)
  refine ⟨?_, ?_, ?_⟩
  · intro r₀ hr₀
    unfold cutE0
    exact AdjCutE0ContAux.cutInt_cws (ν ^ (-2 : ℝ)) hR
      (fun r x => B0579.jb x ^ (-m) * ‖ψ r x‖ ^ 2) hE0 hr₀
  · intro r₀ hr₀
    unfold cutE0Rate
    exact continuousWithinAt_const.mul
      (AdjCutE0ContAux.cutInt_cws (ν ^ (-2 : ℝ)) hR
        (fun r x => B0579.jb x ^ (-m) * ((starRingEnd ℂ) (ψ r x) * ladDt ψ r x).re) hRate hr₀)
  · intro k r₀ hr₀
    unfold cutGReal
    exact AdjCutE0ContAux.cutInt_cws (ν ^ (-2 : ℝ)) hR
      (fun r x => B0579.jb x ^ (-m) * ‖pdCx k (ψ r) x‖ ^ 2) (hGk k) hr₀

lemma rate_convert {m ν t b M₀ KL R s' : ℝ} (hν : 0 < ν) {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hmem : ∀ r ∈ Ico t b, MemLp (ψ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hM₀ : ∀ ρ ∈ Ioo t b, eLpNorm (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M₀)
    (hKL : ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t b,
      ν * ∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ - KL ≤
        cutE0Rate (ν ^ (-2 : ℝ)) m R ψ ρ)
    (hR : 1 ≤ R) (hs' : s' ∈ Ioo t b) :
    ENNReal.ofReal ν * ∑ k : Fin 2,
      ∫⁻ ρ in Ioc t s', cutGradEnergy (ν ^ (-2 : ℝ)) m R ψ k ρ ≤
        ENNReal.ofReal ((max M₀ 0) ^ 2 + max KL 0 * (b - t)) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  obtain ⟨hE, hD, hGk⟩ := cutE0_cont (ν := ν) (m := m) hj hR0
  have hrs' : t ≤ s' := hs'.1.le
  have hs'lt : s' < b := hs'.2
  have hsub : Icc t s' ⊆ Ico t b := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hs'lt⟩
  have hsubO : Ioo t s' ⊆ Ioo t b := fun x hx => ⟨hx.1, lt_trans hx.2 hs'lt⟩
  have hIoc : Ioc t s' ⊆ Ico t b := fun x hx => ⟨hx.1.le, lt_of_le_of_lt hx.2 hs'lt⟩
  have hderiv : ∀ x ∈ Ioo t s', HasDerivAt (cutE0 (ν ^ (-2 : ℝ)) m R ψ)
      (cutE0Rate (ν ^ (-2 : ℝ)) m R ψ x) x := by
    intro x hx
    have hd := Cut0DU.hasDerivAt_cut0 hj (c := ν ^ (-2 : ℝ)) (m := m) hR0 (hsubO hx)
    refine hd.congr_deriv ?_
    unfold cutE0Rate
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hDint : IntervalIntegrable (cutE0Rate (ν ^ (-2 : ℝ)) m R ψ) volume t s' :=
    ContinuousOn.intervalIntegrable_of_Icc hrs' (hD.mono hsub)
  have hFTC : ∫ x in t..s', cutE0Rate (ν ^ (-2 : ℝ)) m R ψ x =
      cutE0 (ν ^ (-2 : ℝ)) m R ψ s' - cutE0 (ν ^ (-2 : ℝ)) m R ψ t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrs' (hE.mono hsub) hderiv hDint
  have hEr : 0 ≤ cutE0 (ν ^ (-2 : ℝ)) m R ψ t := by
    unfold cutE0
    refine setIntegral_nonneg (B0579.measurableSet_cell _) (fun x _ => ?_)
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (CutRealDU.jb_nonneg' x) _) (sq_nonneg _))
  have hEs : cutE0 (ν ^ (-2 : ℝ)) m R ψ s' ≤ (max M₀ 0) ^ 2 :=
    cutE0_le_of_eLpNorm (hmem s' (Ioo_subset_Ico_self hs')) (hM₀ s' hs')
  have hGI : ∀ k : Fin 2, IntervalIntegrable (cutGReal (ν ^ (-2 : ℝ)) m R ψ k) volume t s' :=
    fun k => ContinuousOn.intervalIntegrable_of_Icc hrs' ((hGk k).mono hsub)
  have hSI : IntervalIntegrable (fun x => ∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k x)
      volume t s' :=
    ContinuousOn.intervalIntegrable_of_Icc hrs'
      (continuousOn_finsetSum _ fun k _ => (hGk k).mono hsub)
  have hsplit : ∫ x in t..s', (ν * (∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k x) - KL) =
      ν * (∑ k : Fin 2, ∫ x in t..s', cutGReal (ν ^ (-2 : ℝ)) m R ψ k x) - KL * (s' - t) := by
    rw [intervalIntegral.integral_sub (hSI.const_mul ν) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun k _ => hGI k)]
    simp [smul_eq_mul]
    ring
  have hcont_f : ContinuousOn
      (fun x => ν * (∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k x) - KL) (Icc t s') :=
    ((continuousOn_const.mul (continuousOn_finsetSum _ fun k _ => (hGk k).mono hsub)).sub
      continuousOn_const)
  have hmono : ∫ x in t..s', (ν * (∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R ψ k x) - KL) ≤
      ∫ x in t..s', cutE0Rate (ν ^ (-2 : ℝ)) m R ψ x := by
    refine intervalIntegral.integral_mono_ae_restrict hrs'
      (ContinuousOn.intervalIntegrable_of_Icc hrs' hcont_f) hDint ?_
    have hae : ∀ᵐ x ∂(volume.restrict (Icc t s')), x ∈ Ioo t s' := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    refine hae.mono fun x hx => hKL R hR x (hsubO hx)
  have hfin := hmono.trans_eq hFTC
  rw [hsplit] at hfin
  have hk1 : KL * (s' - t) ≤ max KL 0 * (s' - t) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.2 hrs')
  have hk2 : max KL 0 * (s' - t) ≤ max KL 0 * (b - t) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
  have hreal : ν * ∑ k : Fin 2, ∫ ρ in t..s', cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ ≤
      (max M₀ 0) ^ 2 + max KL 0 * (b - t) := by
    linarith
  have hpt : ∀ k : Fin 2, ∀ ρ ∈ Ico t b,
      cutGradEnergy (ν ^ (-2 : ℝ)) m R ψ k ρ =
        ENNReal.ofReal (cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ) := fun k ρ hρ =>
    AdjCutConvertAux.cutLint_eq _ m R hR0 (ψ ρ) (AdjCutConvertAux.slice_contDiff hj hρ) k
  have hI0 : ∀ k : Fin 2, 0 ≤ ∫ ρ in t..s', cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ := fun k =>
    intervalIntegral.integral_nonneg hrs' (fun ρ _ => AdjCutConvertAux.cutGReal_nonneg _ m R ψ k ρ)
  have hstep : ∀ k : Fin 2,
      ∫⁻ ρ in Ioc t s', cutGradEnergy (ν ^ (-2 : ℝ)) m R ψ k ρ =
        ENNReal.ofReal (∫ ρ in t..s', cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ) := by
    intro k
    have hintIoc : IntegrableOn (cutGReal (ν ^ (-2 : ℝ)) m R ψ k) (Ioc t s') :=
      (((hGk k).mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have e1 : ∫⁻ ρ in Ioc t s', cutGradEnergy (ν ^ (-2 : ℝ)) m R ψ k ρ =
        ∫⁻ ρ in Ioc t s', ENNReal.ofReal (cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ) :=
      setLIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => hpt k ρ (hIoc hρ))
    have e2 : ENNReal.ofReal (∫ ρ in Ioc t s', cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ) =
        ∫⁻ ρ in Ioc t s', ENNReal.ofReal (cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ) :=
      ofReal_integral_eq_lintegral_ofReal hintIoc
        (Eventually.of_forall fun ρ => AdjCutConvertAux.cutGReal_nonneg _ m R ψ k ρ)
    have e3 : ∫ ρ in t..s', cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ =
        ∫ ρ in Ioc t s', cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ :=
      intervalIntegral.integral_of_le hrs'
    rw [e1, e3, ← e2]
  rw [Finset.sum_congr rfl (fun k _ => hstep k),
    ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun k : Fin 2 => ∫ ρ in t..s', cutGReal (ν ^ (-2 : ℝ)) m R ψ k ρ)
      (fun k _ => hI0 k),
    ← ENNReal.ofReal_mul hν.le]
  exact ENNReal.ofReal_le_ofReal hreal

end AdjFieldIntH1Aux

open AdjFieldIntH1Aux in
/-- **Higher-derivative integrated `H¹` bound** (`PartIII-a:T21/2/7/2/4/3`). -/
theorem adjFieldIntegratedH1 (m : ℝ) (_hm : 8 < m) :
    UnforcedLeray.Short.IIIa.AdjFieldIntegratedH1 m := by
  classical
  intro ν hν _hν1 tr hb t b ht htb ψ hj hper hmem ⟨M₀, hM₀⟩ ⟨M, hM⟩ k
  obtain ⟨KL, hKL⟩ := rate_lower hν ht htb tr hb hj hper hmem hM₀ hM
  set K : ℝ := (max M₀ 0) ^ 2 + max KL 0 * (b - t)
  have hνne : ENNReal.ofReal ν ≠ 0 := (ENNReal.ofReal_pos.2 hν).ne'
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ × (ℝ × ℝ) → ℂ, Q = (Ico t b ×ˢ (univ : Set (ℝ × ℝ))).piecewise
      (fun p : ℝ × (ℝ × ℝ) => pdCx k (ψ p.1) p.2) (fun _ => 0) := ⟨_, rfl⟩
  have hP : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx k (ψ p.1) p.2)
      (Ico t b ×ˢ (univ : Set (ℝ × ℝ))) :=
    (jointSmooth_pdCx hj k).continuousOn
  have hQm : Measurable Q := by
    rw [hQdef]
    exact ContinuousOn.measurable_piecewise hP continuousOn_const
      (measurableSet_Ico.prod MeasurableSet.univ)
  have hQeq : ∀ ρ ∈ Ico t b, ∀ x : ℝ × ℝ, Q (ρ, x) = pdCx k (ψ ρ) x := by
    intro ρ hρ x
    rw [hQdef]
    exact Set.piecewise_eq_of_mem _ _ _ (⟨hρ, mem_univ x⟩ : (ρ, x) ∈ Ico t b ×ˢ (univ : Set (ℝ × ℝ)))
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ × (ℝ × ℝ) → ℝ≥0∞, ∀ n p, g n p =
      ENNReal.ofReal (ladCut ((n : ℝ) + 1) p.2 ^ 2) * ‖Q p‖ₑ ^ (2 : ℝ) :=
    ⟨fun n p => ENNReal.ofReal (ladCut ((n : ℝ) + 1) p.2 ^ 2) * ‖Q p‖ₑ ^ (2 : ℝ), fun _ _ => rfl⟩
  have hcut : ∀ R : ℝ, Measurable (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (ladCut R p.2 ^ 2)) := by
    intro R
    have hc : Continuous (fun p : ℝ × (ℝ × ℝ) => ladCut R p.2 ^ 2) :=
      ((CutLimitAux.continuous_cut R).comp continuous_snd).pow 2
    exact ENNReal.measurable_ofReal.comp hc.measurable
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    have e : g n = fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (ladCut ((n : ℝ) + 1) p.2 ^ 2) * ‖Q p‖ₑ ^ (2 : ℝ) := funext (hg n)
    rw [e]
    exact (hcut _).mul (hQm.enorm.pow_const _)
  have hgeq : ∀ n ρ, ρ ∈ Ico t b → ∀ x : ℝ × ℝ, g n (ρ, x) =
      ENNReal.ofReal (ladCut ((n : ℝ) + 1) x ^ 2) * ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ) := by
    intro n ρ hρ x
    rw [hg, hQeq ρ hρ x]
  have hlim : ∀ ρ x, Tendsto (fun n => g n (ρ, x)) atTop (𝓝 (‖Q (ρ, x)‖ₑ ^ (2 : ℝ))) := by
    intro ρ x
    have hev : ∀ᶠ n : ℕ in atTop, |x.2| + 1 ≤ (n : ℝ) + 1 := by
      filter_upwards [eventually_ge_atTop ⌈|x.2|⌉₊] with n hn
      have h1 := Nat.le_ceil |x.2|
      have h2 : ((⌈|x.2|⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with n hn
    rw [hg]
    simp [CutLimitAux.eq_one hn]
  have hSF : SFinite (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    unfold B0579.cellMeasure
    infer_instance
  have hJm : ∀ n, Measurable (fun ρ => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) :=
    fun n => Measurable.lintegral_prod_right' (hgm n)
  have hFx : ∀ ρ, ∫⁻ x, ‖Q (ρ, x)‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
      liminf (fun n => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop := by
    intro ρ
    have h := lintegral_liminf_le' (μ := B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
      (u := atTop) (f := fun n x => g n (ρ, x))
      (fun n => ((hgm n).comp measurable_prodMk_left).aemeasurable)
    calc ∫⁻ x, ‖Q (ρ, x)‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
        = ∫⁻ x, liminf (fun n => g n (ρ, x)) atTop ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
          lintegral_congr fun x => ((hlim ρ x).liminf_eq).symm
      _ ≤ _ := h
  have hFp : ∀ ρ ∈ Ioo t b, ∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
      liminf (fun n => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop := by
    intro ρ hρ
    have hρ' : ρ ∈ Ico t b := ⟨hρ.1.le, hρ.2⟩
    have e : ∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) =
        ∫⁻ x, ‖Q (ρ, x)‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      lintegral_congr fun x => by rw [hQeq ρ hρ' x]
    rw [e]
    exact hFx ρ
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ≥0∞, D = ENNReal.ofReal K / ENNReal.ofReal ν := ⟨_, rfl⟩
  have hpos : 0 < b - t := sub_pos.2 htb
  obtain ⟨sm, hsm⟩ : ∃ sm : ℕ → ℝ, ∀ m' : ℕ, sm m' = b - (b - t) / ((m' : ℝ) + 2) :=
    ⟨fun m' => b - (b - t) / ((m' : ℝ) + 2), fun _ => rfl⟩
  have hsm_lt : ∀ m', sm m' < b := by
    intro m'
    rw [hsm]
    have : 0 < (b - t) / ((m' : ℝ) + 2) := div_pos hpos (by positivity)
    linarith
  have hsm_gt : ∀ m', t < sm m' := by
    intro m'
    rw [hsm]
    have h0 : (0 : ℝ) ≤ (m' : ℝ) := Nat.cast_nonneg m'
    have : (b - t) / ((m' : ℝ) + 2) < b - t := div_lt_self hpos (by linarith)
    linarith
  have hsm_mono : Monotone sm := by
    intro a b' hab
    rw [hsm, hsm]
    have hab' : (a : ℝ) ≤ (b' : ℝ) := by exact_mod_cast hab
    have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have : (b - t) / ((b' : ℝ) + 2) ≤ (b - t) / ((a : ℝ) + 2) :=
      div_le_div_of_nonneg_left hpos.le (by positivity) (by linarith)
    linarith
  have hU : (⋃ m', Ioc t (sm m')) = Ioo t b := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨m', h1, h2⟩
      exact ⟨h1, lt_of_le_of_lt h2 (hsm_lt m')⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨m', hm'⟩ := exists_nat_gt ((b - t) / (b - x))
      refine ⟨m', h1, ?_⟩
      rw [hsm]
      have hsx : 0 < b - x := sub_pos.2 h2
      have h3 : b - t < (m' : ℝ) * (b - x) := (div_lt_iff₀ hsx).1 hm'
      have h4 : (b - t) / ((m' : ℝ) + 2) ≤ b - x := by
        rw [div_le_iff₀ (by positivity)]
        have h0 : (0 : ℝ) ≤ (m' : ℝ) := Nat.cast_nonneg m'
        nlinarith
      linarith
  have hmonoS : Monotone (fun m' => Ioc t (sm m')) := fun a b' hab => Ioc_subset_Ioc_right (hsm_mono hab)
  have hJbd : ∀ n : ℕ, ∫⁻ ρ in Ioo t b, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
      ≤ D := by
    intro n
    have hterm : ∀ m', ∫⁻ ρ in Ioc t (sm m'), ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
        ≤ D := by
      intro m'
      have hI : ∫⁻ ρ in Ioc t (sm m'), ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
          = ∫⁻ ρ in Ioc t (sm m'), cutGradEnergy (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) ψ k ρ := by
        refine setLIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => ?_)
        have hρ' : ρ ∈ Ico t b := ⟨hρ.1.le, hρ.2.trans_lt (hsm_lt m')⟩
        exact lintegral_congr fun x => hgeq n ρ hρ' x
      rw [hI, hDdef]
      have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hsub : sm m' ∈ Ioo t b := ⟨hsm_gt m', hsm_lt m'⟩
      have h1 := rate_convert hν hj hmem hM₀ hKL hR hsub
      have h2 : ∫⁻ ρ in Ioc t (sm m'), cutGradEnergy (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) ψ k ρ ≤
          ∑ k' : Fin 2, ∫⁻ ρ in Ioc t (sm m'), cutGradEnergy (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) ψ k' ρ :=
        Finset.single_le_sum (f := fun k' : Fin 2 =>
          ∫⁻ ρ in Ioc t (sm m'), cutGradEnergy (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) ψ k' ρ)
          (fun _ _ => zero_le) (Finset.mem_univ k)
      refine (ENNReal.le_div_iff_mul_le (Or.inl hνne) (Or.inl ENNReal.ofReal_ne_top)).2 ?_
      refine (mul_comm _ _).trans_le ?_
      exact le_trans (mul_le_mul_of_nonneg_left h2 zero_le) h1
    have hset : ∫⁻ ρ in Ioo t b, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
        = ⨆ m', ∫⁻ ρ in Ioc t (sm m'), ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
      rw [← hU]
      exact setLIntegral_iUnion_of_directed _ hmonoS.directed_le
    rw [hset]
    exact iSup_le hterm
  have hIoo : ∫⁻ ρ in Ioc t b, (∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) = ∫⁻ ρ in Ioo t b, (∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) :=
    (setLIntegral_congr Ioo_ae_eq_Ioc).symm
  have h1 : ∫⁻ ρ in Ioo t b, (∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) ≤
      ∫⁻ ρ in Ioo t b, liminf (fun n => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop :=
    setLIntegral_mono' measurableSet_Ioo (fun ρ hρ => hFp ρ hρ)
  have h2 : ∫⁻ ρ in Ioo t b, liminf (fun n => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop
      ≤ liminf (fun n => ∫⁻ ρ in Ioo t b, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop :=
    lintegral_liminf_le' (fun n => (hJm n).aemeasurable)
  have h3 : liminf (fun n => ∫⁻ ρ in Ioo t b, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
      atTop ≤ D := by
    calc liminf (fun n => ∫⁻ ρ in Ioo t b, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
          atTop ≤ liminf (fun _ : ℕ => D) atTop := liminf_le_liminf (Eventually.of_forall hJbd)
      _ = D := liminf_const D
  rw [hIoo]
  have hfin : D < ⊤ := by
    rw [hDdef]
    exact ENNReal.div_lt_top ENNReal.ofReal_ne_top hνne
  exact lt_of_le_of_lt (h1.trans (h2.trans h3)) hfin

end UnforcedLeray.Short.IIIa
