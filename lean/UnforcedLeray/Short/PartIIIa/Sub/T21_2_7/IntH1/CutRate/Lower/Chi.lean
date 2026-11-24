import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutLowerChiAux

lemma ladCut_nonneg' (R : ℝ) (x : ℝ × ℝ) : 0 ≤ ladCut R x :=
  Real.smoothTransition.nonneg _

lemma ladCut_le_one' (R : ℝ) (x : ℝ × ℝ) : ladCut R x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma enorm_sq_eq' (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm_eq_enorm, ENNReal.rpow_two]

/-- A uniform lintegral bound of `‖f‖²` gives a uniform integral bound. -/
lemma integral_sq_le_of_lintegral {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} {M : ℝ}
    (hf : MemLp f 2 μ) (hl : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal M) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ max M 0 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (‖f x‖))
    (hf.aestronglyMeasurable.norm.pow 2)]
  apply ENNReal.toReal_le_of_le_ofReal (le_max_right M 0)
  calc ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ
      = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := lintegral_congr fun x => enorm_sq_eq' _
    _ ≤ ENNReal.ofReal M := hl
    _ ≤ ENNReal.ofReal (max M 0) := ENNReal.ofReal_le_ofReal (le_max_left M 0)

/-- A uniform `L²` bound (`eLpNorm`) gives a uniform bound on `∫ ‖f‖²`. -/
lemma integral_sq_le_of_eLpNorm {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} {M : ℝ}
    (hf : MemLp f 2 μ) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal M) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ (max M 0) ^ 2 := by
  have hY : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : eLpNorm f 2 μ = ENNReal.ofReal ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)) := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num [Real.rpow_two]
  rw [e] at h
  have h' : ENNReal.ofReal ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)) ≤ ENNReal.ofReal (max M 0) :=
    h.trans (ENNReal.ofReal_le_ofReal (le_max_left M 0))
  have h1 : (∫ x, ‖f x‖ ^ 2 ∂μ) ^ (2⁻¹ : ℝ) ≤ max M 0 := by
    have := ENNReal.toReal_le_of_le_ofReal (le_max_right M 0) h'
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg hY _)] at this
  set Y := ∫ x, ‖f x‖ ^ 2 ∂μ with hYdef
  have h2 : Y = (Y ^ (2⁻¹ : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY]
    norm_num
  calc Y = (Y ^ (2⁻¹ : ℝ)) ^ 2 := h2
    _ ≤ (max M 0) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hY _) h1 2

end CutLowerChiAux

open CutLowerChiAux in
/-- **(ii) The `χ`-term** (SP 3052-3058): pointwise `|w Re(Φ̄χ)| ≤ jb^{-m}(|Φ|²+|χ|²)/2` (`0 ≤ χ_R² ≤ 1`),
then `∫_cell jb^{-m} u = ∫ u dμ` for `μ = X_{-m,c}`, with `∫|Φ|² ≤ M` and `∫|χ|² ≤ M_χ²` from
`adjWeakChiBound`. Young in place of Cauchy-Schwarz gives a bound independent of `R ≥ 1` and `ρ`. -/
theorem cutLowerChi (m : ℝ) : CutLowerChi m := by
  intro ν tr t s G φ M hL
  obtain ⟨hctx, hm8, hM⟩ := hL
  obtain ⟨hν, hν1, hb, ht, hts, hG, hφ, hj⟩ := id hctx
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hc0 : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hW : AdjWCtx m ν (ν ^ (-2 : ℝ)) tr t s (physAdj (clockA ν s) G) φ :=
    ⟨hν, hc0, ht, hts, hb, hφ, hj⟩
  obtain ⟨Mχ, hMχ⟩ := adjWeakChiBound m hm8 ν (ν ^ (-2 : ℝ)) tr t s (physAdj (clockA ν s) G) φ
    hc1 hW
  refine ⟨(max M 0 + (max Mχ 0) ^ 2) / 2, fun R hR ρ hρ => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hρI : ρ ∈ Icc t s := Ioo_subset_Icc_self hρ
  have hfM : MemLp (φ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hφ.memX ρ hρI
  obtain ⟨hχM, hχb⟩ := hMχ ρ hρ
  have hφb : ∫ x, ‖φ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ max M 0 :=
    integral_sq_le_of_lintegral hfM (hM ρ hρI)
  have hχb' : ∫ x, ‖ladChi tr φ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
      (max Mχ 0) ^ 2 :=
    integral_sq_le_of_eLpNorm hχM hχb
  -- integrability of the squared norms with respect to the weighted measure
  have hfI : Integrable (fun x => ‖φ ρ x‖ ^ 2) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    have h2 : MemLp (φ ρ) ((2 : ℕ) : ℝ≥0∞) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
      exact_mod_cast hfM
    exact h2.integrable_norm_pow (by norm_num)
  have hχI : Integrable (fun x => ‖ladChi tr φ ρ x‖ ^ 2)
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    have h2 : MemLp (ladChi tr φ ρ) ((2 : ℕ) : ℝ≥0∞) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
      exact_mod_cast hχM
    exact h2.integrable_norm_pow (by norm_num)
  have hu : Integrable (fun x => (1 / 2 : ℝ) * (‖φ ρ x‖ ^ 2 + ‖ladChi tr φ ρ x‖ ^ 2))
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    (hfI.add hχI).const_mul (1 / 2 : ℝ)
  have hcell : IntegrableOn (fun x => B0579.jb x ^ (-m) *
      ((1 / 2 : ℝ) * (‖φ ρ x‖ ^ 2 + ‖ladChi tr φ ρ x‖ ^ 2))) (B0579.cell (ν ^ (-2 : ℝ))) := by
    have := (B0579.integrable_cellMeasure_iff (ν ^ (-2 : ℝ)) (-m)).1 hu
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell _)
    simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]
  -- pointwise bound
  have hpt : ∀ x : ℝ × ℝ, ‖lowF1 tr m R φ ρ x‖ ≤
      B0579.jb x ^ (-m) * ((1 / 2 : ℝ) * (‖φ ρ x‖ ^ 2 + ‖ladChi tr φ ρ x‖ ^ 2)) := by
    intro x
    unfold lowF1
    have hJ0 : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have hre : |((starRingEnd ℂ) (φ ρ x) * ladChi tr φ ρ x).re| ≤
        ‖φ ρ x‖ * ‖ladChi tr φ ρ x‖ := by
      calc |((starRingEnd ℂ) (φ ρ x) * ladChi tr φ ρ x).re|
          ≤ ‖(starRingEnd ℂ) (φ ρ x) * ladChi tr φ ρ x‖ := Complex.abs_re_le_norm _
        _ = ‖φ ρ x‖ * ‖ladChi tr φ ρ x‖ := by rw [norm_mul, Complex.norm_conj]
    have hab : ‖φ ρ x‖ * ‖ladChi tr φ ρ x‖ ≤
        (1 / 2 : ℝ) * (‖φ ρ x‖ ^ 2 + ‖ladChi tr φ ρ x‖ ^ 2) := by
      nlinarith [sq_nonneg (‖φ ρ x‖ - ‖ladChi tr φ ρ x‖)]
    have ha0 := ladCut_nonneg' R x
    have ha1 := ladCut_le_one' R x
    have ha2 : ladCut R x ^ 2 ≤ 1 := by nlinarith
    have hJre : 0 ≤ B0579.jb x ^ (-m) *
        |((starRingEnd ℂ) (φ ρ x) * ladChi tr φ ρ x).re| :=
      mul_nonneg hJ0 (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul,
      abs_of_nonneg hJ0]
    nlinarith [mul_le_mul_of_nonneg_right ha2 hJre,
      mul_le_mul_of_nonneg_left (hre.trans hab) hJ0]
  have hbound1 : |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R φ ρ x| ≤
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.jb x ^ (-m) *
        ((1 / 2 : ℝ) * (‖φ ρ x‖ ^ 2 + ‖ladChi tr φ ρ x‖ ^ 2)) := by
    calc |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R φ ρ x|
        = ‖∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R φ ρ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ‖lowF1 tr m R φ ρ x‖ := norm_integral_le_integral_norm _
      _ ≤ _ := integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hcell
          (ae_of_all _ hpt)
  have hval := integral_cellMeasure_eq (ν ^ (-2 : ℝ)) m
    (fun x => (1 / 2 : ℝ) * (‖φ ρ x‖ ^ 2 + ‖ladChi tr φ ρ x‖ ^ 2))
  rw [← hval] at hbound1
  rw [integral_const_mul, integral_add hfI hχI] at hbound1
  nlinarith [hbound1, hφb, hχb']

end UnforcedLeray.Short.IIIa
