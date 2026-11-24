import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Conv

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1`: `L²(cell)` bounds and self-adjointness of the mollifier

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. Jensen's inequality for the probability density `K_k(x - ·)` on the cell, Fubini and the
evenness of `K_k` give the contraction `‖J_k g‖ ≤ ‖g‖` and the self-adjointness of `J_k` on `L²(cell)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

theorem lmK_swap {c : ℝ} (hc : 0 < c) (k : ℕ) (x y : ℝ × ℝ) : lmK c k (x - y) = lmK c k (y - x) := by
  rw [← neg_sub, lmK_neg hc]

theorem lmK_integrable_cell {c : ℝ} (hc : 0 < c) (k : ℕ) (x : ℝ × ℝ) :
    Integrable (fun y => lmK c k (x - y)) (volume.restrict (B0579.cell c)) := by
  obtain ⟨M, hM⟩ := lmK_bdd c k
  exact memLp_one_iff_integrable.1 (lm_memLp_band (c := c) (measurable_lmK c k) hM
    (fun z hz => lmK_eq_zero_of_snd hc k (by linarith)) x 1)

theorem lm_integrable_sq {c : ℝ} {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    Integrable (fun y => ‖g y‖ ^ 2) (volume.restrict (B0579.cell c)) :=
  (memLp_two_iff_integrable_sq_norm hg.1).1 hg

/-- Jensen: `|J_k g(x)|² ≤ ∫_cell K_k(x - y) |g(y)|² dy`. -/
theorem lmJs_sq_le {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (x : ℝ × ℝ) :
    ‖lmJs c k g x‖ ^ 2 ≤ ∫ y in B0579.cell c, lmK c k (x - y) * ‖g y‖ ^ 2 := by
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c) with hμ
  have hK0 : ∀ y : ℝ × ℝ, 0 ≤ lmK c k (x - y) := fun y => lmK_nonneg c k _
  have hK1 : ∫ y, lmK c k (x - y) ∂μ = 1 := lmK_integral_cell hc k x
  have hKint : Integrable (fun y => lmK c k (x - y)) μ := lmK_integrable_cell hc k x
  have hKu : Integrable (fun y => lmK c k (x - y) * ‖g y‖) μ := by
    refine (lmJs_integrable hc k hg x).norm.congr (ae_of_all _ fun y => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 y)]
  obtain ⟨M, hM⟩ := lmK_bdd c k
  have hKu2 : Integrable (fun y => lmK c k (x - y) * ‖g y‖ ^ 2) μ := by
    refine ((lm_integrable_sq hg).const_mul M).mono'
      (hKint.1.mul (lm_integrable_sq hg).1) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g y‖)]
    exact mul_le_mul_of_nonneg_right (hM _) (sq_nonneg _)
  set A : ℝ := ∫ y, lmK c k (x - y) * ‖g y‖ ∂μ with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun y => mul_nonneg (hK0 y) (norm_nonneg _)
  have hA : ‖lmJs c k g x‖ ≤ A := by
    have h1 := norm_integral_le_integral_norm (μ := μ) (fun y => (lmK c k (x - y) : ℂ) * g y)
    have h2 : ∀ y, ‖(lmK c k (x - y) : ℂ) * g y‖ = lmK c k (x - y) * ‖g y‖ := fun y => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 y)]
    simp only [h2] at h1
    exact h1
  have hnn : 0 ≤ ∫ y, lmK c k (x - y) * (‖g y‖ - A) ^ 2 ∂μ :=
    integral_nonneg fun y => mul_nonneg (hK0 y) (sq_nonneg _)
  have hexp : ∫ y, lmK c k (x - y) * (‖g y‖ - A) ^ 2 ∂μ =
      ∫ y, lmK c k (x - y) * ‖g y‖ ^ 2 ∂μ - 2 * A * A + A ^ 2 := by
    have hpt : ∀ y : ℝ × ℝ, lmK c k (x - y) * (‖g y‖ - A) ^ 2 =
        lmK c k (x - y) * ‖g y‖ ^ 2 - 2 * A * (lmK c k (x - y) * ‖g y‖) +
          A ^ 2 * lmK c k (x - y) := fun y => by ring
    simp only [hpt]
    have hsub : Integrable
        (fun y => lmK c k (x - y) * ‖g y‖ ^ 2 - 2 * A * (lmK c k (x - y) * ‖g y‖)) μ :=
      hKu2.sub (hKu.const_mul _)
    rw [integral_add hsub (hKint.const_mul _), integral_sub hKu2 (hKu.const_mul _),
      integral_const_mul, integral_const_mul, hK1, mul_one]
  have hsq : ‖lmJs c k g x‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  nlinarith

theorem lmK_integral_cell_left {c : ℝ} (hc : 0 < c) (k : ℕ) (y : ℝ × ℝ) :
    ∫ x in B0579.cell c, lmK c k (x - y) = 1 := by
  simp only [lmK_swap hc k _ y]
  exact lmK_integral_cell hc k y

theorem lmK_integrable_cell_left {c : ℝ} (hc : 0 < c) (k : ℕ) (y : ℝ × ℝ) :
    Integrable (fun x => lmK c k (x - y)) (volume.restrict (B0579.cell c)) := by
  simp only [lmK_swap hc k _ y]
  exact lmK_integrable_cell hc k y

theorem lmK_integrable_prod {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => lmK c k (p.1 - p.2) * ‖g p.2‖ ^ 2)
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) := by
  have hg2 := lm_integrable_sq hg
  have hmeas : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => lmK c k (p.1 - p.2) * ‖g p.2‖ ^ 2)
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) :=
    ((measurable_lmK c k).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
      hg2.1.comp_snd
  rw [integrable_prod_iff' hmeas]
  constructor
  · exact ae_of_all _ fun y => (lmK_integrable_cell_left hc k y).mul_const (‖g y‖ ^ 2)
  · refine hg2.congr (ae_of_all _ fun y => ?_)
    have h1 : ∀ x : ℝ × ℝ, ‖lmK c k (x - y) * ‖g y‖ ^ 2‖ = lmK c k (x - y) * ‖g y‖ ^ 2 := fun x =>
      Real.norm_of_nonneg (mul_nonneg (lmK_nonneg c k _) (sq_nonneg _))
    simp only [h1]
    rw [integral_mul_const, lmK_integral_cell_left hc k y, one_mul]

theorem lmK_fubini {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    ∫ x in B0579.cell c, ∫ y in B0579.cell c, lmK c k (x - y) * ‖g y‖ ^ 2 =
      ∫ y in B0579.cell c, ‖g y‖ ^ 2 := by
  rw [integral_integral_swap (f := fun x y => lmK c k (x - y) * ‖g y‖ ^ 2)
    (lmK_integrable_prod hc k hg)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show ∫ x in B0579.cell c, lmK c k (x - y) * ‖g y‖ ^ 2 = ‖g y‖ ^ 2
  rw [integral_mul_const, lmK_integral_cell_left hc k y, one_mul]

theorem lmJs_contr {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    ∫ x in B0579.cell c, ‖lmJs c k g x‖ ^ 2 ≤ ∫ x in B0579.cell c, ‖g x‖ ^ 2 := by
  rw [← lmK_fubini hc k hg]
  exact integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
    (lmK_integrable_prod hc k hg).integral_prod_left (ae_of_all _ fun x => lmJs_sq_le hc k hg x)

theorem lmJs_memLp {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    MemLp (lmJs c k g) 2 (volume.restrict (B0579.cell c)) := by
  have hcont : Continuous (lmJs c k g) := (lmJs_contDiff hc k hg).continuous
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  refine (lmK_integrable_prod hc k hg).integral_prod_left.mono'
    (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact lmJs_sq_le hc k hg x

theorem lmK_integrable_pair {c : ℝ} (hc : 0 < c) (k : ℕ) {f g : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        (lmK c k (p.1 - p.2) : ℂ) * (starRingEnd ℂ (f p.2) * g p.1))
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) := by
  have h1 := lmK_integrable_prod hc k hf
  have h2 := (lmK_integrable_prod hc k hg).swap
  have hmeasK : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (lmK c k (p.1 - p.2) : ℂ))
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) :=
    (Complex.measurable_ofReal.comp
      ((measurable_lmK c k).comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  have hmeasF : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => starRingEnd ℂ (f p.2))
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hf.1.comp_snd
  have hmeasG : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1)
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) :=
    hg.1.comp_fst
  refine (h1.add h2).mono' (hmeasK.mul (hmeasF.mul hmeasG)) (ae_of_all _ fun p => ?_)
  have hK0 : 0 ≤ lmK c k (p.1 - p.2) := lmK_nonneg c k _
  have hsw : lmK c k (p.2 - p.1) = lmK c k (p.1 - p.2) := lmK_swap hc k _ _
  simp only [Pi.add_apply, Function.comp_apply, Prod.fst_swap, Prod.snd_swap, hsw, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0, RCLike.norm_conj]
  have hab : ‖f p.2‖ * ‖g p.1‖ ≤ ‖f p.2‖ ^ 2 + ‖g p.1‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f p.2‖ - ‖g p.1‖), sq_nonneg ‖f p.2‖, sq_nonneg ‖g p.1‖]
  calc lmK c k (p.1 - p.2) * (‖f p.2‖ * ‖g p.1‖)
      ≤ lmK c k (p.1 - p.2) * (‖f p.2‖ ^ 2 + ‖g p.1‖ ^ 2) := mul_le_mul_of_nonneg_left hab hK0
    _ = _ := by ring

theorem lmJs_selfAdj {c : ℝ} (hc : 0 < c) (k : ℕ) {f g : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    ∫ x in B0579.cell c, starRingEnd ℂ (lmJs c k f x) * g x =
      ∫ x in B0579.cell c, starRingEnd ℂ (f x) * lmJs c k g x := by
  have hL : ∀ x : ℝ × ℝ, starRingEnd ℂ (lmJs c k f x) * g x =
      ∫ y in B0579.cell c, (lmK c k (x - y) : ℂ) * (starRingEnd ℂ (f y) * g x) := fun x => by
    unfold lmJs
    rw [← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hR : ∀ y : ℝ × ℝ, starRingEnd ℂ (f y) * lmJs c k g y =
      ∫ x in B0579.cell c, (lmK c k (x - y) : ℂ) * (starRingEnd ℂ (f y) * g x) := fun y => by
    unfold lmJs
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [lmK_swap hc k y x]
    ring
  simp only [hL, hR]
  exact integral_integral_swap (f := fun x y => (lmK c k (x - y) : ℂ) * (starRingEnd ℂ (f y) * g x))
    (lmK_integrable_pair hc k hf hg)

end UnforcedLeray.Short.IIIa
