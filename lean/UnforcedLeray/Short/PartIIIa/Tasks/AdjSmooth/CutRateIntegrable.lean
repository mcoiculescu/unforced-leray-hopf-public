import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutIntegrableAux

lemma ladCut_contDiff' (R : ℝ) : ContDiff ℝ ∞ (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma pdCx_contDiff' (k : Fin 2) {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.fderiv_right (by simp)).clm_apply contDiff_const

lemma ladLapCx_continuous' {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (ladLapCx Φ) := by
  unfold ladLapCx
  exact (pdCx_contDiff' 0 (pdCx_contDiff' 0 hΦ)).continuous.add
    (pdCx_contDiff' 1 (pdCx_contDiff' 1 hΦ)).continuous

lemma sq_ge_of_not_box {c R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (hK : x ∉ B0579.box c (3 * R)) : 8 * R ^ 2 ≤ x.2 ^ 2 := by
  by_contra h
  push Not at h
  apply hK
  apply B0579.mem_box_of_mem_cell hx
  nlinarith [sq_abs x.2, abs_nonneg x.2]

lemma ladCut_eq_zero_of' {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R ^ 2 ≤ x.2 ^ 2) :
    ladCut R x = 0 := by
  obtain ⟨K, _, h⟩ := ladCutProps
  exact (h R hR).2.2.2.1 x hx

lemma ladCut_zero_of_not_box {c R R' : ℝ} (hR : 0 < R) (hR' : 0 < R')
    (hR8 : 2 * R' ^ 2 ≤ 8 * R ^ 2) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (hK : x ∉ B0579.box c (3 * R)) : ladCut R' x = 0 :=
  ladCut_eq_zero_of' hR' (le_trans hR8 (sq_ge_of_not_box hR hx hK))

lemma integrableOn_cell_box {c R : ℝ} {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ x ∈ B0579.cell c, x ∉ B0579.box c (3 * R) → g x = 0) :
    IntegrableOn g (B0579.cell c) :=
  B0579.integrableOn_cell_of_continuous hg (B0579.isCompact_box c (3 * R)) h0

end CutIntegrableAux

open CutIntegrableAux in
theorem cutRateIntegrable : UnforcedLeray.Short.IIIa.CutRateIntegrable := by
  intro m c R Φ χ F hc hR hΦ hχ hF hmem
  have hLc1 : Continuous (ladCut R) := (ladCut_contDiff' R).continuous
  have hLc2 : Continuous (ladCut (2 * R)) := (ladCut_contDiff' (2 * R)).continuous
  have hJ : Continuous (fun x => B0579.jb x ^ (-m)) := B0579.continuous_jb_rpow (-m)
  have hLL : Continuous (ladLapCx Φ) := ladLapCx_continuous' hΦ
  have hPk : ∀ k : Fin 2, Continuous (pdCx k Φ) := fun k => (pdCx_contDiff' k hΦ).continuous
  have hR8a : 2 * R ^ 2 ≤ 8 * R ^ 2 := by nlinarith [sq_nonneg R]
  have hR8b : 2 * (2 * R) ^ 2 ≤ 8 * R ^ 2 := by nlinarith [sq_nonneg R]
  have hG : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ladCut R y ^ 2 * B0579.jb y ^ (-m)) :=
    ((ladCut_contDiff' R).pow 2).mul (B0579.contDiff_jb_rpow (-m))
  -- the derivative `pd k` of the weight vanishes outside the box
  have hGv : ∀ k : Fin 2, ∀ x ∈ B0579.cell c, x ∉ B0579.box c (3 * R) →
      B0579.pd k (fun y : ℝ × ℝ => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x = 0 := by
    intro k x hx hK
    have hx8 := sq_ge_of_not_box hR hx hK
    have hlt : ∀ᶠ y in 𝓝 x, 2 * R ^ 2 < y.2 ^ 2 :=
      ContinuousAt.eventually_lt continuousAt_const
        (continuous_snd.pow 2).continuousAt (by nlinarith [sq_nonneg R])
    have hev : (fun y : ℝ × ℝ => ladCut R y ^ 2 * B0579.jb y ^ (-m)) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hlt] with y hy
      have h0 := ladCut_eq_zero_of' hR (le_of_lt hy)
      simp [h0]
    unfold B0579.pd
    rw [hev.fderiv_eq]
    simp
  have hGc : ∀ k : Fin 2, Continuous
      (B0579.pd k (fun y : ℝ × ℝ => ladCut R y ^ 2 * B0579.jb y ^ (-m))) :=
    fun k => (B0579.contDiff_pd hG k).continuous
  have hFre : ∀ k : Fin 2, Continuous (fun x => ((starRingEnd ℂ) (pdCx k Φ x) * F x).re) :=
    fun k => Complex.continuous_re.comp ((Complex.continuous_conj.comp (hPk k)).mul hF)
  have hLre : Continuous (fun x => ((starRingEnd ℂ) (ladLapCx Φ x) * F x).re) :=
    Complex.continuous_re.comp ((Complex.continuous_conj.comp hLL).mul hF)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine integrableOn_cell_box (c := c) (R := R) ?_ ?_
    · exact (hLc1.pow 2).mul (hJ.mul hLre)
    · intro x hx hK
      simp [ladCut_zero_of_not_box hR hR hR8a hx hK]
  · intro k
    refine integrableOn_cell_box (c := c) (R := R) ?_ ?_
    · exact (hGc k).mul (hFre k)
    · intro x hx hK
      simp [hGv k x hx hK]
  · refine integrableOn_cell_box (c := c) (R := R) ?_ ?_
    · exact (hLc1.pow 2).mul (hJ.mul (hLL.norm.pow 2))
    · intro x hx hK
      simp [ladCut_zero_of_not_box hR hR hR8a hx hK]
  · intro k
    refine integrableOn_cell_box (c := c) (R := R) ?_ ?_
    · exact (hLc2.pow 2).mul (hJ.mul ((hPk k).norm.pow 2))
    · intro x hx hK
      simp [ladCut_zero_of_not_box hR (by linarith) hR8b hx hK]
  · -- the weighted `L²` piece: integrable by `MemLp χ 2` through the density
    have hint : Integrable (fun x => ‖χ x‖ ^ 2) (B0579.cellMeasure c (-m)) := by
      have h2 : MemLp χ ((2 : ℕ) : ℝ≥0∞) (B0579.cellMeasure c (-m)) := by
        exact_mod_cast hmem
      exact h2.integrable_norm_pow (by norm_num)
    have := (B0579.integrable_cellMeasure_iff c (-m)).1 hint
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]

end UnforcedLeray.Short.IIIa
