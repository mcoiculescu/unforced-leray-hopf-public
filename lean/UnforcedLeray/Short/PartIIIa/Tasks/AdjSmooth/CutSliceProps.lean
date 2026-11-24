import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutSliceAux

lemma ladCut_continuous (R : ℝ) : Continuous (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.continuous.comp (by fun_prop)

lemma ladCut_nonneg (R : ℝ) (x : ℝ × ℝ) : 0 ≤ ladCut R x :=
  Real.smoothTransition.nonneg _

lemma ladCut_le_one (R : ℝ) (x : ℝ × ℝ) : ladCut R x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma ladCut_eq_one_of {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ^ 2 ≤ R ^ 2) :
    ladCut R x = 1 := by
  obtain ⟨K, _, h⟩ := ladCutProps
  exact (h R hR).2.2.1 x hx

lemma ladCut_eq_zero_of {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R ^ 2 ≤ x.2 ^ 2) :
    ladCut R x = 0 := by
  obtain ⟨K, _, h⟩ := ladCutProps
  exact (h R hR).2.2.2.1 x hx

lemma ladCut_le_ladCut {R R' : ℝ} (hR : 0 < R) (hRR : R ≤ R') (x : ℝ × ℝ) :
    ladCut R x ≤ ladCut R' x := by
  unfold ladCut
  apply Real.smoothTransition.monotone
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have : x.2 ^ 2 / R' ^ 2 ≤ x.2 ^ 2 / R ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) hR2 (pow_le_pow_left₀ hR.le hRR 2)
  linarith

lemma integrableOn_cell_of_vanish {c R : ℝ} (hR : 0 < R) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 → g x = 0) :
    IntegrableOn g (B0579.cell c) := by
  refine B0579.integrableOn_cell_of_continuous hg (B0579.isCompact_box c (2 * R)) ?_
  intro x hx hxK
  apply h0
  by_contra hcon
  push Not at hcon
  apply hxK
  apply B0579.mem_box_of_mem_cell hx
  nlinarith [sq_abs x.2, abs_nonneg x.2]

lemma contDiff_pdCx {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma continuous_ladLapCx {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (ladLapCx Φ) := by
  unfold ladLapCx
  exact ((contDiff_pdCx (contDiff_pdCx hΦ 0) 0).continuous).add
    ((contDiff_pdCx (contDiff_pdCx hΦ 1) 1).continuous)

lemma cutE1_nonneg (c m R : ℝ) (Φ : ℝ × ℝ → ℂ) : 0 ≤ cutE1 c m R Φ := by
  unfold cutE1
  refine Finset.sum_nonneg fun k _ => setIntegral_nonneg (B0579.measurableSet_cell c) fun x _ => ?_
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))

lemma cutLap_nonneg (c m R : ℝ) (Φ : ℝ × ℝ → ℂ) : 0 ≤ cutLap c m R Φ := by
  unfold cutLap
  refine setIntegral_nonneg (B0579.measurableSet_cell c) fun x _ => ?_
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))

lemma integrableOn_cutLap {c m R : ℝ} (hR : 0 < R) {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    IntegrableOn (fun x => ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ladLapCx Φ x‖ ^ 2))
      (B0579.cell c) := by
  apply integrableOn_cell_of_vanish hR
  · exact ((ladCut_continuous R).pow 2).mul
      ((B0579.continuous_jb_rpow (-m)).mul ((continuous_ladLapCx hΦ).norm.pow 2))
  · intro x hx
    simp [ladCut_eq_zero_of hR hx]

lemma integrableOn_cutE1 {c m R : ℝ} (hR : 0 < R) {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) :
    IntegrableOn (fun x => ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2))
      (B0579.cell c) := by
  apply integrableOn_cell_of_vanish hR
  · exact ((ladCut_continuous R).pow 2).mul
      ((B0579.continuous_jb_rpow (-m)).mul ((contDiff_pdCx hΦ k).continuous.norm.pow 2))
  · intro x hx
    simp [ladCut_eq_zero_of hR hx]

lemma integrableOn_gradTerm {c m : ℝ} {g : ℝ × ℝ → ℂ}
    (hmem : MemLp g 2 (B0579.cellMeasure c (-m))) :
    IntegrableOn (fun x => B0579.jb x ^ (-m) * ‖g x‖ ^ 2) (B0579.cell c) := by
  have h1 : Integrable (fun x => ‖g x‖ ^ 2) (B0579.cellMeasure c (-m)) :=
    (memLp_two_iff_integrable_sq_norm hmem.1).1 hmem
  have h2 := (B0579.integrable_cellMeasure_iff c (-m)).1 h1
  refine h2.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
  simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]

lemma gradE_eq {c m : ℝ} (Φ : ℝ × ℝ → ℂ) :
    gradE c m Φ = ∑ k : Fin 2, ∫ x in B0579.cell c,
      B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2 :=
  Finset.sum_congr rfl fun k _ => integral_cellMeasure_eq c m (fun x => ‖pdCx k Φ x‖ ^ 2)

lemma cutLap_mono {c m : ℝ} {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) {R R' : ℝ}
    (hR : 0 < R) (hRR : R ≤ R') : cutLap c m R Φ ≤ cutLap c m R' Φ := by
  have hR' : 0 < R' := lt_of_lt_of_le hR hRR
  unfold cutLap
  refine setIntegral_mono_on (integrableOn_cutLap hR hΦ) (integrableOn_cutLap hR' hΦ)
    (B0579.measurableSet_cell c) fun x _ => ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (ladCut_nonneg _ _)
    (ladCut_le_ladCut hR hRR x) 2)
    (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))

lemma cutE1_le_gradE {c m : ℝ} {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hmem : ∀ k : Fin 2, MemLp (pdCx k Φ) 2 (B0579.cellMeasure c (-m))) {R : ℝ} (hR : 0 < R) :
    cutE1 c m R Φ ≤ gradE c m Φ := by
  rw [gradE_eq Φ]
  unfold cutE1
  refine Finset.sum_le_sum fun k _ => setIntegral_mono_on (integrableOn_cutE1 hR hΦ k)
    (integrableOn_gradTerm (hmem k)) (B0579.measurableSet_cell c) fun x _ => ?_
  have hnn : 0 ≤ B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)
  exact mul_le_of_le_one_left hnn (pow_le_one₀ (ladCut_nonneg _ _) (ladCut_le_one _ _))

lemma tendsto_cutE1 {c m : ℝ} {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hmem : ∀ k : Fin 2, MemLp (pdCx k Φ) 2 (B0579.cellMeasure c (-m))) :
    Tendsto (fun n : ℕ => cutE1 c m ((n : ℝ) + 1) Φ) atTop (𝓝 (gradE c m Φ)) := by
  rw [gradE_eq Φ]
  unfold cutE1
  refine tendsto_finsetSum _ fun k _ => ?_
  refine tendsto_integral_of_dominated_convergence
    (fun x => B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2) (fun n => ?_)
    (integrableOn_gradTerm (hmem k)) (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · exact (Continuous.mul ((ladCut_continuous _).pow 2)
      (Continuous.mul (B0579.continuous_jb_rpow (-m))
        ((contDiff_pdCx hΦ k).continuous.norm.pow 2))).aestronglyMeasurable
  · skip
    have hnn : 0 ≤ B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
    exact mul_le_of_le_one_left hnn (pow_le_one₀ (ladCut_nonneg _ _) (ladCut_le_one _ _))
  · skip
    obtain ⟨N, hN⟩ := exists_nat_ge |x.2|
    refine tendsto_const_nhds.congr' ?_
    apply Filter.eventually_atTop.2
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    have hle : |x.2| ≤ (n : ℝ) + 1 := by linarith
    have hsq : x.2 ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    simp [ladCut_eq_one_of (R := (n : ℝ) + 1) (by positivity) hsq]

end CutSliceAux

open CutSliceAux in
theorem cutSliceProps : UnforcedLeray.Short.IIIa.CutSliceProps := by
  intro c m Φ hc hΦ
  refine ⟨fun R hR => ⟨cutE1_nonneg c m R Φ, cutLap_nonneg c m R Φ⟩,
    fun R R' hR hRR => cutLap_mono hΦ hR hRR, fun hmem => ⟨fun R hR => cutE1_le_gradE hΦ hmem hR, ?_⟩⟩
  exact tendsto_cutE1 hΦ hmem
