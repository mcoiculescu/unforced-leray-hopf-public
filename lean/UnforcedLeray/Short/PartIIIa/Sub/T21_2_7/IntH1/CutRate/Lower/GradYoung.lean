import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.WeightGrad

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutLowerGradAux

lemma ladCut_contDiff' (R : ℝ) : ContDiff ℝ ∞ (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma pdCx_contDiff' (k : Fin 2) {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.fderiv_right (by simp)).clm_apply contDiff_const

lemma ladCut_nonneg' (R : ℝ) (x : ℝ × ℝ) : 0 ≤ ladCut R x :=
  Real.smoothTransition.nonneg _

lemma ladCut_le_one' (R : ℝ) (x : ℝ × ℝ) : ladCut R x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma sq_ge_of_not_box {c R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (hK : x ∉ B0579.box c (3 * R)) : 8 * R ^ 2 ≤ x.2 ^ 2 := by
  by_contra h
  push Not at h
  apply hK
  apply B0579.mem_box_of_mem_cell hx
  nlinarith [sq_abs x.2, abs_nonneg x.2]

lemma ladCut_zero_of_not_box' {c R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (hK : x ∉ B0579.box c (3 * R)) : ladCut R x = 0 := by
  obtain ⟨K, _, h⟩ := ladCutProps
  exact (h R hR).2.2.2.1 x (by nlinarith [sq_ge_of_not_box hR hx hK, sq_nonneg R])

lemma integrableOn_cell_box' {c R : ℝ} {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ x ∈ B0579.cell c, x ∉ B0579.box c (3 * R) → g x = 0) :
    IntegrableOn g (B0579.cell c) :=
  B0579.integrableOn_cell_of_continuous hg (B0579.isCompact_box c (3 * R)) h0

/-- Integrability of the cutoff gradient energy density `χ_R² jb^{-m} |∂_kΦ|²`. -/
lemma integrable_G {c m R : ℝ} (hR : 0 < R) {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) :
    IntegrableOn (fun x => ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2))
      (B0579.cell c) := by
  have hLc : Continuous (ladCut R) := (ladCut_contDiff' R).continuous
  have hJ : Continuous (fun x : ℝ × ℝ => B0579.jb x ^ (-m)) := B0579.continuous_jb_rpow (-m)
  have hP : Continuous (pdCx k Φ) := (pdCx_contDiff' k hΦ).continuous
  refine integrableOn_cell_box' (c := c) (R := R) ((hLc.pow 2).mul (hJ.mul (hP.norm.pow 2))) ?_
  intro x hx hK
  simp [ladCut_zero_of_not_box' hR hx hK]

/-- A uniform lintegral bound of `‖f‖²` gives a uniform integral bound. -/
lemma integral_sq_le_of_lintegral {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} {M : ℝ}
    (hf : MemLp f 2 μ) (hl : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal M) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ max M 0 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (‖f x‖))
    (hf.aestronglyMeasurable.norm.pow 2)]
  apply ENNReal.toReal_le_of_le_ofReal (le_max_right M 0)
  calc ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ
      = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := lintegral_congr fun x => by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ENNReal.rpow_two]
    _ ≤ ENNReal.ofReal M := hl
    _ ≤ ENNReal.ofReal (max M 0) := ENNReal.ofReal_le_ofReal (le_max_left M 0)

/-- The weight gradient: `|∂_k(χ_R² jb^{-m})| ≤ (2K + 2|m|) χ_R jb^{-m}` for `R ≥ 1`. -/
lemma pd_weight_bound {Kc m R : ℝ} (hK0 : 0 ≤ Kc) (hR : 1 ≤ R)
    (hkey : ∀ (x : ℝ × ℝ) (j : Fin 2), |B0579.pd j (ladCut R) x| ≤ Kc / R) (x : ℝ × ℝ) (k : Fin 2) :
    |B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x| ≤
      (2 * Kc + 2 * |m|) * (ladCut R x * B0579.jb x ^ (-m)) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hd : Differentiable ℝ (ladCut R) := (ladCut_contDiff' R).differentiable (by simp)
  have hsqd : Differentiable ℝ (fun y => ladCut R y ^ 2) :=
    ((ladCut_contDiff' R).pow 2).differentiable (by simp)
  have hp : Differentiable ℝ (fun y : ℝ × ℝ => B0579.jb y ^ (-m)) :=
    (B0579.contDiff_jb_rpow (-m)).differentiable (by simp)
  have hw : B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x =
      B0579.pd k (fun y => ladCut R y ^ 2) x * B0579.jb x ^ (-m) +
        ladCut R x ^ 2 * B0579.pd k (fun y => B0579.jb y ^ (-m)) x :=
    B0579.pd_mul hsqd hp k x
  have hsq : B0579.pd k (fun y => ladCut R y ^ 2) x = 2 * ladCut R x * B0579.pd k (ladCut R) x := by
    have e : (fun y => ladCut R y ^ 2) = fun y => ladCut R y * ladCut R y :=
      funext fun y => sq _
    rw [e, B0579.pd_mul hd hd k x]
    ring
  have hb := adjWeightGrad m x k
  have haK : |B0579.pd k (ladCut R) x| ≤ Kc :=
    le_trans (hkey x k) (div_le_self hK0 hR)
  have hc0 := ladCut_nonneg' R x
  have hc1 := ladCut_le_one' R x
  have hp0 : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have hm0 : 0 ≤ |m| := abs_nonneg m
  have ha' := abs_le.1 haK
  have hb' := abs_le.1 hb
  rw [hw, hsq, abs_le]
  have h1 : 0 ≤ ladCut R x * B0579.jb x ^ (-m) * (Kc - B0579.pd k (ladCut R) x) :=
    mul_nonneg (mul_nonneg hc0 hp0) (sub_nonneg.2 ha'.2)
  have h2 : 0 ≤ ladCut R x * B0579.jb x ^ (-m) * (Kc + B0579.pd k (ladCut R) x) :=
    mul_nonneg (mul_nonneg hc0 hp0) (by linarith [ha'.1])
  have h3 : 0 ≤ ladCut R x ^ 2 * (2 * |m| * B0579.jb x ^ (-m) -
      B0579.pd k (fun y => B0579.jb y ^ (-m)) x) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.2 hb'.2)
  have h4 : 0 ≤ ladCut R x ^ 2 * (2 * |m| * B0579.jb x ^ (-m) +
      B0579.pd k (fun y => B0579.jb y ^ (-m)) x) :=
    mul_nonneg (sq_nonneg _) (by linarith [hb'.1])
  have h5 : 0 ≤ ladCut R x * (1 - ladCut R x) * (|m| * B0579.jb x ^ (-m)) :=
    mul_nonneg (mul_nonneg hc0 (sub_nonneg.2 hc1)) (mul_nonneg hm0 hp0)
  constructor <;> nlinarith [h1, h2, h3, h4, h5]

/-- Pointwise: `|Re(Φ̄ (a₀ z₀ + a₁ z₁))| ≤ |a₀| |z₀||Φ| + |a₁| |z₁||Φ|` for real `a_k`. -/
lemma re_bound (Φv z0 z1 : ℂ) (a0 a1 : ℝ) :
    |((starRingEnd ℂ) Φv * ((a0 : ℂ) * z0 + (a1 : ℂ) * z1)).re| ≤
      |a0| * (‖z0‖ * ‖Φv‖) + |a1| * (‖z1‖ * ‖Φv‖) := by
  have hX : |((starRingEnd ℂ) z0 * Φv).re| ≤ ‖z0‖ * ‖Φv‖ := by
    calc |((starRingEnd ℂ) z0 * Φv).re| ≤ ‖(starRingEnd ℂ) z0 * Φv‖ := Complex.abs_re_le_norm _
      _ = ‖z0‖ * ‖Φv‖ := by rw [norm_mul, Complex.norm_conj]
  have hY : |((starRingEnd ℂ) z1 * Φv).re| ≤ ‖z1‖ * ‖Φv‖ := by
    calc |((starRingEnd ℂ) z1 * Φv).re| ≤ ‖(starRingEnd ℂ) z1 * Φv‖ := Complex.abs_re_le_norm _
      _ = ‖z1‖ * ‖Φv‖ := by rw [norm_mul, Complex.norm_conj]
  have e : ((starRingEnd ℂ) Φv * ((a0 : ℂ) * z0 + (a1 : ℂ) * z1)).re =
      a0 * ((starRingEnd ℂ) z0 * Φv).re + a1 * ((starRingEnd ℂ) z1 * Φv).re := by
    have hc : ∀ (a : ℝ) (z : ℂ), ((starRingEnd ℂ) Φv * ((a : ℂ) * z)).re =
        a * ((starRingEnd ℂ) Φv * z).re := by
      intro a z
      rw [show (starRingEnd ℂ) Φv * ((a : ℂ) * z) = (a : ℂ) * ((starRingEnd ℂ) Φv * z) by ring,
        Complex.re_ofReal_mul]
    rw [mul_add, Complex.add_re, hc, hc]
    have comm : ∀ z : ℂ, ((starRingEnd ℂ) Φv * z).re = ((starRingEnd ℂ) z * Φv).re := by
      intro z
      rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
    rw [comm z0, comm z1]
  rw [e]
  calc |a0 * ((starRingEnd ℂ) z0 * Φv).re + a1 * ((starRingEnd ℂ) z1 * Φv).re|
      ≤ |a0 * ((starRingEnd ℂ) z0 * Φv).re| + |a1 * ((starRingEnd ℂ) z1 * Φv).re| :=
        abs_add_le _ _
    _ = |a0| * |((starRingEnd ℂ) z0 * Φv).re| + |a1| * |((starRingEnd ℂ) z1 * Φv).re| := by
        rw [abs_mul, abs_mul]
    _ ≤ |a0| * (‖z0‖ * ‖Φv‖) + |a1| * (‖z1‖ * ‖Φv‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hX (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hY (abs_nonneg _))

/-- Young's inequality for the weight-gradient term: `K₂ c p u (v₀+v₁) ≤ 2K₂² p u² + ¼ c² (p v₀² + p v₁²)`
(`p ≥ 0`). -/
lemma young_grad (K2 c p u v0 v1 : ℝ) (hp : 0 ≤ p) :
    K2 * c * p * u * (v0 + v1) ≤
      2 * K2 ^ 2 * (p * u ^ 2) + (1 / 4 : ℝ) * (c ^ 2 * (p * v0 ^ 2) + c ^ 2 * (p * v1 ^ 2)) := by
  nlinarith [mul_nonneg hp (sq_nonneg (2 * K2 * u - c * (v0 + v1) / 2)),
    mul_nonneg (mul_nonneg hp (sq_nonneg c)) (sq_nonneg (v0 - v1))]

end CutLowerGradAux

open CutLowerGradAux in
/-- **(iv) The weight-gradient term** (SP 3044-3049, `ladCutProps`, `adjWeightGrad`): for `R ≥ 1`,
`|∂_k w| ≤ K₂ χ_R jb^{-m}` with `w = χ_R² jb^{-m}`, so `|J| ≤ ∫ 2K₂²jb^{-m}|Φ|² +
¼∑_k G_k^R`, and `∫ jb^{-m}|Φ|² ≤ M`. -/
theorem cutLowerGradYoung (m : ℝ) : CutLowerGradYoung m := by
  intro ν tr t s G φ M hL
  obtain ⟨hctx, _, hM⟩ := hL
  obtain ⟨hν, hν1, hb, ht, hts, hG, hφ, hj⟩ := id hctx
  obtain ⟨Kc, hK0, hKP⟩ := ladCutProps
  refine ⟨2 * (2 * Kc + 2 * |m|) ^ 2 * max M 0, fun R hR ρ hρ => ?_⟩
  have hR1 : (1 : ℝ) ≤ R := hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  obtain ⟨-, -, -, -, hpd, -⟩ := hKP R hR0
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hΦs : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hρI : ρ ∈ Icc t s := Ioo_subset_Icc_self hρ
  have hfM : MemLp (φ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hφ.memX ρ hρI
  have hφb : ∫ x, ‖φ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ max M 0 :=
    integral_sq_le_of_lintegral hfM (hM ρ hρI)
  have hfI : Integrable (fun x => ‖φ ρ x‖ ^ 2) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    have h2 : MemLp (φ ρ) ((2 : ℕ) : ℝ≥0∞) (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
      exact_mod_cast hfM
    exact h2.integrable_norm_pow (by norm_num)
  have hcellU : IntegrableOn (fun x => B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)
      (B0579.cell (ν ^ (-2 : ℝ))) := by
    have := (B0579.integrable_cellMeasure_iff (ν ^ (-2 : ℝ)) (-m)).1 hfI
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell _)
    simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]
  have hG0 := integrable_G (c := ν ^ (-2 : ℝ)) (m := m) hR0 hΦs 0
  have hG1 := integrable_G (c := ν ^ (-2 : ℝ)) (m := m) hR0 hΦs 1
  set K2 := 2 * Kc + 2 * |m| with hK2
  have hgI : IntegrableOn (fun x => 2 * K2 ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2) +
      (1 / 4 : ℝ) * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    (hcellU.const_mul (2 * K2 ^ 2)).add ((hG0.add hG1).const_mul (1 / 4 : ℝ))
  -- pointwise domination of the integrand
  have hpt : ∀ x : ℝ × ℝ, |lowFJ m R φ ρ x| ≤ 2 * K2 ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2) +
      (1 / 4 : ℝ) * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)) := by
    intro x
    unfold lowFJ
    refine le_trans (re_bound _ _ _ _ _) ?_
    have ha0 : |B0579.pd 0 (lowW m R) x| ≤ K2 * (ladCut R x * B0579.jb x ^ (-m)) :=
      pd_weight_bound hK0 hR1 hpd x 0
    have ha1 : |B0579.pd 1 (lowW m R) x| ≤ K2 * (ladCut R x * B0579.jb x ^ (-m)) :=
      pd_weight_bound hK0 hR1 hpd x 1
    have hp0 : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have hcp : 0 ≤ ladCut R x * B0579.jb x ^ (-m) := mul_nonneg (ladCut_nonneg' R x) hp0
    have hu : 0 ≤ ‖φ ρ x‖ := norm_nonneg _
    have hv0 : 0 ≤ ‖pdCx 0 (φ ρ) x‖ := norm_nonneg _
    have hv1 : 0 ≤ ‖pdCx 1 (φ ρ) x‖ := norm_nonneg _
    have hs : |B0579.pd 0 (lowW m R) x| * (‖pdCx 0 (φ ρ) x‖ * ‖φ ρ x‖) +
        |B0579.pd 1 (lowW m R) x| * (‖pdCx 1 (φ ρ) x‖ * ‖φ ρ x‖) ≤
        K2 * (ladCut R x * B0579.jb x ^ (-m)) * ‖φ ρ x‖ *
          (‖pdCx 0 (φ ρ) x‖ + ‖pdCx 1 (φ ρ) x‖) := by
      nlinarith [mul_le_mul_of_nonneg_right ha0 (mul_nonneg hv0 hu),
        mul_le_mul_of_nonneg_right ha1 (mul_nonneg hv1 hu)]
    have hy := young_grad K2 (ladCut R x) (B0579.jb x ^ (-m)) ‖φ ρ x‖ ‖pdCx 0 (φ ρ) x‖
      ‖pdCx 1 (φ ρ) x‖ hp0
    have e : K2 * (ladCut R x * B0579.jb x ^ (-m)) * ‖φ ρ x‖ *
        (‖pdCx 0 (φ ρ) x‖ + ‖pdCx 1 (φ ρ) x‖) =
        K2 * ladCut R x * B0579.jb x ^ (-m) * ‖φ ρ x‖ *
          (‖pdCx 0 (φ ρ) x‖ + ‖pdCx 1 (φ ρ) x‖) := by ring
    nlinarith [hs, hy, e]
  -- integrate
  have hpu : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2 =
      ∫ x, ‖φ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    (integral_cellMeasure_eq (ν ^ (-2 : ℝ)) m (fun x => ‖φ ρ x‖ ^ 2)).symm
  have hmono := integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) hgI
    (ae_of_all _ hpt)
  have habs := abs_integral_le_integral_abs (μ := volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))
    (f := fun x => lowFJ m R φ ρ x)
  have hsplit : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (2 * K2 ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2) +
        (1 / 4 : ℝ) * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2) +
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2))) =
      2 * K2 ^ 2 * (∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2) +
        (1 / 4 : ℝ) * ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2)) +
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)) := by
    have hI1 : IntegrableOn (fun x => 2 * K2 ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2))
        (B0579.cell (ν ^ (-2 : ℝ))) := hcellU.const_mul (2 * K2 ^ 2)
    have hI2 : IntegrableOn (fun x => (1 / 4 : ℝ) * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        ‖pdCx 0 (φ ρ) x‖ ^ 2) + ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)))
        (B0579.cell (ν ^ (-2 : ℝ))) := (hG0.add hG1).const_mul (1 / 4 : ℝ)
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_add hG0 hG1]
  have hbnd : 2 * K2 ^ 2 * (∫ x, ‖φ ρ x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) ≤
      2 * K2 ^ 2 * max M 0 :=
    mul_le_mul_of_nonneg_left hφb (by positivity)
  rw [Fin.sum_univ_two]
  unfold cutGReal
  have final : |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowFJ m R φ ρ x| ≤
      2 * K2 ^ 2 * (∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2) +
        (1 / 4 : ℝ) * ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2)) +
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)) := by
    rw [← hsplit]
    exact le_trans habs hmono
  rw [hpu] at final
  linarith [final, hbnd]

end UnforcedLeray.Short.IIIa
