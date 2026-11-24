import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Defs
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.L2

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: the mollifier `lmJ` has the properties `LMMollH1`

Source of record: `the November 2 reference manuscript` lines 3427-3440, 3541-3552.
For the periodic convolution `lmJ c k` of `Mollifier/Defs.lean`:

* `lmJ_gradL2`: `∂ⱼ lmJ` is bounded on `L²(cell)`: the derivative falls on the kernel, which is
  bounded and vanishes for `|η| ≥ c/3`, and the Schur test applies (`lm_schur_L2`);
* `lmJ_divFreeWeak`: `y ↦ K_k(x - y)` is a test function, so the divergence of `lmJ f` at `x` is the
  weak divergence of `f` tested with it.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

/-- A bounded nonnegative function vanishing off a band of width `2c/3` has cell integral at most
`M c (2c/3)`. -/
theorem lm_band_integral_le {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℝ} (hfm : Measurable f) {M : ℝ}
    (hfM : ∀ y, f y ≤ M) (hf0 : ∀ y, 0 ≤ f y) {a : ℝ}
    (hb : ∀ y : ℝ × ℝ, c / 3 ≤ |a - y.2| → f y = 0) :
    ∫ y in B0579.cell c, f y ≤ M * (c * (2 * c / 3)) := by
  set S : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ Icc (a - c / 3) (a + c / 3) with hSdef
  have hS : MeasurableSet S := measurableSet_Ico.prod measurableSet_Icc
  have hSsub : S ⊆ B0579.cell c := fun z hz => ⟨hz.1, mem_univ _⟩
  have hvol : volume S = ENNReal.ofReal c * ENNReal.ofReal (2 * c / 3) := by
    rw [hSdef, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    congr 2 <;> ring
  have hfin : volume S < ⊤ := by
    rw [hvol]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hvolR : volume.real S = c * (2 * c / 3) := by
    rw [Measure.real, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
      ENNReal.toReal_ofReal (by positivity)]
  have e : ∫ y in B0579.cell c, f y = ∫ y in S, f y := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (B0579.measurableSet_cell c) hSsub ?_
    rintro y ⟨hy1, hy2⟩
    refine hb y ?_
    by_contra hcon
    push Not at hcon
    rw [abs_lt] at hcon
    exact hy2 ⟨hy1.1, ⟨by linarith [hcon.2], by linarith [hcon.1]⟩⟩
  have hint : IntegrableOn f S := by
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne hfm.aestronglyMeasurable ?_
    exact ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (hf0 y)]
      exact hfM y
  have hMint : IntegrableOn (fun _ : ℝ × ℝ => M) S := integrableOn_const hfin.ne
  calc ∫ y in B0579.cell c, f y = ∫ y in S, f y := e
    _ ≤ ∫ _y in S, M := setIntegral_mono_on hint hMint hS fun y _ => hfM y
    _ = M * (c * (2 * c / 3)) := by
        rw [setIntegral_const, hvolR, smul_eq_mul, mul_comm]

/-- The constant of the Schur test. -/
def lmSchurA (c M : ℝ) : ℝ := M * (c * (2 * c / 3)) + 1

section Schur

variable {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℝ} (hm : Measurable h) {M : ℝ}
  (hM : ∀ z : ℝ × ℝ, |h z| ≤ M) (hb : ∀ z : ℝ × ℝ, c / 3 ≤ |z.2| → h z = 0)

include hc hm hM hb

theorem lmSchurA_pos : 0 < lmSchurA c M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  unfold lmSchurA
  positivity

theorem lm_schur_left_le (x : ℝ × ℝ) : ∫ y in B0579.cell c, |h (x - y)| ≤ lmSchurA c M - 1 := by
  have := lm_band_integral_le hc (f := fun y => |h (x - y)|) (M := M)
    (continuous_abs.measurable.comp (hm.comp (measurable_const.sub measurable_id))) (fun y => hM _) (fun y => abs_nonneg _)
    (a := x.2) (fun y hy => by
      have : h (x - y) = 0 := hb _ (by simpa using hy)
      simp [this])
  unfold lmSchurA
  linarith

theorem lm_schur_right_le (y : ℝ × ℝ) : ∫ x in B0579.cell c, |h (x - y)| ≤ lmSchurA c M - 1 := by
  have := lm_band_integral_le hc (f := fun x => |h (x - y)|) (M := M)
    (continuous_abs.measurable.comp (hm.comp (measurable_id.sub measurable_const))) (fun x => hM _) (fun x => abs_nonneg _)
    (a := y.2) (fun x hx => by
      have h1 : c / 3 ≤ |(x - y).2| := by
        rw [Prod.snd_sub, abs_sub_comm]
        exact hx
      simp [hb _ h1])
  unfold lmSchurA
  linarith

theorem lm_schur_memLp_left (x : ℝ × ℝ) (p : ℝ≥0∞) :
    MemLp (fun y => |h (x - y)|) p (volume.restrict (B0579.cell c)) :=
  lm_memLp_band (h := fun z => |h z|) (continuous_abs.measurable.comp hm) (fun z => by simpa using hM z)
    (fun z hz => by simp [hb z hz]) x p

theorem lm_schur_memLp_right (y : ℝ × ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => |h (x - y)|) p (volume.restrict (B0579.cell c)) := by
  have := lm_memLp_band (c := c) (h := fun z => |h (-z)|)
    (continuous_abs.measurable.comp (hm.comp measurable_neg)) (fun z => by simpa using hM (-z))
    (fun z hz => by
      have : h (-z) = 0 := hb _ (by simpa using hz)
      simp [this]) y p
  simpa [neg_sub] using this

/-- Cauchy-Schwarz with the weight `|h(x - ·)|`. -/
theorem lm_schur_sq {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (B0579.cell c)))
    (x : ℝ × ℝ) :
    ‖∫ y in B0579.cell c, (h (x - y) : ℂ) * g y‖ ^ 2 ≤
      lmSchurA c M * ∫ y in B0579.cell c, |h (x - y)| * ‖g y‖ ^ 2 := by
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c) with hμ
  have hA0 := lmSchurA_pos hc hm hM hb
  have hK0 : ∀ y : ℝ × ℝ, 0 ≤ |h (x - y)| := fun y => abs_nonneg _
  have hKint : Integrable (fun y => |h (x - y)|) μ :=
    memLp_one_iff_integrable.1 (lm_schur_memLp_left hc hm hM hb x 1)
  have hKu : Integrable (fun y => |h (x - y)| * ‖g y‖) μ :=
    (lm_schur_memLp_left hc hm hM hb x 2).integrable_mul hg.norm
  have hKu2 : Integrable (fun y => |h (x - y)| * ‖g y‖ ^ 2) μ := by
    refine ((lm_integrable_sq hg).const_mul M).mono'
      (hKint.1.mul (lm_integrable_sq hg).1) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g y‖), abs_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (sq_nonneg _)
  set A : ℝ := ∫ y, |h (x - y)| ∂μ with hAdef
  set B : ℝ := ∫ y, |h (x - y)| * ‖g y‖ ∂μ with hBdef
  set C : ℝ := ∫ y, |h (x - y)| * ‖g y‖ ^ 2 ∂μ with hCdef
  have hAle : A ≤ lmSchurA c M - 1 := lm_schur_left_le hc hm hM hb x
  have hB0 : 0 ≤ B := integral_nonneg fun y => mul_nonneg (hK0 y) (norm_nonneg _)
  have hnorm : ‖∫ y in B0579.cell c, (h (x - y) : ℂ) * g y‖ ≤ B := by
    have h1 := norm_integral_le_integral_norm (μ := μ) (fun y => (h (x - y) : ℂ) * g y)
    have h2 : ∀ y, ‖(h (x - y) : ℂ) * g y‖ = |h (x - y)| * ‖g y‖ := fun y => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simp only [h2] at h1
    exact h1
  set t : ℝ := B / lmSchurA c M with htdef
  have hBt : B = t * lmSchurA c M := by rw [htdef]; field_simp
  have hnn : 0 ≤ ∫ y, |h (x - y)| * (‖g y‖ - t) ^ 2 ∂μ :=
    integral_nonneg fun y => mul_nonneg (hK0 y) (sq_nonneg _)
  have hexp : ∫ y, |h (x - y)| * (‖g y‖ - t) ^ 2 ∂μ = C - 2 * t * B + t ^ 2 * A := by
    have hpt : ∀ y : ℝ × ℝ, |h (x - y)| * (‖g y‖ - t) ^ 2 =
        |h (x - y)| * ‖g y‖ ^ 2 - 2 * t * (|h (x - y)| * ‖g y‖) + t ^ 2 * |h (x - y)| := fun y => by
      ring
    simp only [hpt]
    have hsub : Integrable
        (fun y => |h (x - y)| * ‖g y‖ ^ 2 - 2 * t * (|h (x - y)| * ‖g y‖)) μ :=
      hKu2.sub (hKu.const_mul _)
    rw [integral_add hsub (hKint.const_mul _), integral_sub hKu2 (hKu.const_mul _),
      integral_const_mul, integral_const_mul]
  have hA1 : t ^ 2 * A ≤ t ^ 2 * lmSchurA c M :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg t)
  have hkey : t ^ 2 * lmSchurA c M ≤ C := by
    rw [hexp] at hnn
    have : 2 * t * B = 2 * (t ^ 2 * lmSchurA c M) := by rw [hBt]; ring
    linarith
  have hsq : ‖∫ y in B0579.cell c, (h (x - y) : ℂ) * g y‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hBsq : B ^ 2 = lmSchurA c M * (t ^ 2 * lmSchurA c M) := by rw [hBt]; ring
  calc ‖∫ y in B0579.cell c, (h (x - y) : ℂ) * g y‖ ^ 2 ≤ B ^ 2 := hsq
    _ = lmSchurA c M * (t ^ 2 * lmSchurA c M) := hBsq
    _ ≤ lmSchurA c M * C := mul_le_mul_of_nonneg_left hkey hA0.le

/-- The kernel `|h(x - y)| |g(y)|²` is integrable on `cell × cell`. -/
theorem lm_schur_prod {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => |h (p.1 - p.2)| * ‖g p.2‖ ^ 2)
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) := by
  have hg2 := lm_integrable_sq hg
  have hA0 := lmSchurA_pos hc hm hM hb
  have hmeas : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => |h (p.1 - p.2)| * ‖g p.2‖ ^ 2)
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) :=
    (continuous_abs.measurable.comp (hm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable.mul hg2.1.comp_snd
  rw [integrable_prod_iff' hmeas]
  constructor
  · exact ae_of_all _ fun y =>
      (memLp_one_iff_integrable.1 (lm_schur_memLp_right hc hm hM hb y 1)).mul_const (‖g y‖ ^ 2)
  · refine (hg2.const_mul (lmSchurA c M)).mono' hmeas.norm.prod_swap.integral_prod_right'
      (ae_of_all _ fun y => ?_)
    have h1 : ∀ x : ℝ × ℝ, ‖|h (x - y)| * ‖g y‖ ^ 2‖ = |h (x - y)| * ‖g y‖ ^ 2 := fun x =>
      Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))
    simp only [h1]
    rw [integral_mul_const, Real.norm_of_nonneg
      (mul_nonneg (integral_nonneg fun x => abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (by linarith [lm_schur_right_le hc hm hM hb y]) (sq_nonneg _)

/-- **The Schur test on the cell.** -/
theorem lm_schur_L2 {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (B0579.cell c)))
    (hcont : Continuous fun x => ∫ y in B0579.cell c, (h (x - y) : ℂ) * g y) :
    MemLp (fun x => ∫ y in B0579.cell c, (h (x - y) : ℂ) * g y) 2
        (volume.restrict (B0579.cell c)) ∧
      ∫ x in B0579.cell c, ‖∫ y in B0579.cell c, (h (x - y) : ℂ) * g y‖ ^ 2 ≤
        lmSchurA c M ^ 2 * ∫ x in B0579.cell c, ‖g x‖ ^ 2 := by
  have hP := lm_schur_prod hc hm hM hb hg
  have hL := hP.integral_prod_left
  have hA0 := lmSchurA_pos hc hm hM hb
  refine ⟨(memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_, ?_⟩
  · refine (hL.const_mul (lmSchurA c M)).mono' (hcont.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact lm_schur_sq hc hm hM hb hg x
  · have h1 : ∫ x in B0579.cell c, ‖∫ y in B0579.cell c, (h (x - y) : ℂ) * g y‖ ^ 2 ≤
        ∫ x in B0579.cell c, lmSchurA c M * ∫ y in B0579.cell c, |h (x - y)| * ‖g y‖ ^ 2 :=
      integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (hL.const_mul _)
        (ae_of_all _ fun x => lm_schur_sq hc hm hM hb hg x)
    have h2 : ∫ x in B0579.cell c, ∫ y in B0579.cell c, |h (x - y)| * ‖g y‖ ^ 2 =
        ∫ y in B0579.cell c, ∫ x in B0579.cell c, |h (x - y)| * ‖g y‖ ^ 2 :=
      integral_integral_swap (f := fun x y => |h (x - y)| * ‖g y‖ ^ 2) hP
    have h3 : ∫ y in B0579.cell c, ∫ x in B0579.cell c, |h (x - y)| * ‖g y‖ ^ 2 ≤
        ∫ y in B0579.cell c, lmSchurA c M * ‖g y‖ ^ 2 := by
      refine integral_mono_of_nonneg
        (ae_of_all _ fun y => integral_nonneg fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        ((lm_integrable_sq hg).const_mul _) (ae_of_all _ fun y => ?_)
      show ∫ x in B0579.cell c, |h (x - y)| * ‖g y‖ ^ 2 ≤ lmSchurA c M * ‖g y‖ ^ 2
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (by linarith [lm_schur_right_le hc hm hM hb y])
        (sq_nonneg _)
    rw [integral_const_mul] at h1 h3
    calc _ ≤ lmSchurA c M * ∫ x in B0579.cell c, ∫ y in B0579.cell c, |h (x - y)| * ‖g y‖ ^ 2 := h1
      _ ≤ lmSchurA c M * (lmSchurA c M * ∫ y in B0579.cell c, ‖g y‖ ^ 2) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left h3 hA0.le
      _ = _ := by ring

end Schur

/-! ### The kernel `∂ⱼ K_k` -/

theorem lmK_pd_band {c : ℝ} (hc : 0 < c) (k : ℕ) (j : Fin 2) {z : ℝ × ℝ} (hz : c / 3 ≤ |z.2|) :
    B0579.pd j (lmK c k) z = 0 := by
  rw [lmK_pd hc k j z]
  have hz' : c / 3 ≤ |(lmPer c z).2| := hz
  have hopen : IsOpen {w : ℝ × ℝ | c / 4 < |w.2|} := isOpen_lt continuous_const continuous_snd.abs
  have hev : lmRho c k =ᶠ[𝓝 (lmPer c z)] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds (show lmPer c z ∈ {w : ℝ × ℝ | c / 4 < |w.2|} by
      show c / 4 < |(lmPer c z).2|
      linarith)] with w hw
    exact lmRho_eq_zero hc k (Or.inr (le_of_lt hw))
  unfold B0579.pd
  rw [hev.fderiv_eq]
  simp

theorem lmK_pd_bdd {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ M : ℝ, ∀ (j : Fin 2) (z : ℝ × ℝ), |B0579.pd j (lmK c k) z| ≤ M := by
  obtain ⟨M, hM⟩ := ((lmRho_hasCompactSupport c k).fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((lmRho_contDiff c k).continuous_fderiv (by simp))
  refine ⟨M, fun j z => ?_⟩
  rw [lmK_pd hc k j z]
  have hd : ‖B0579.dir j‖ ≤ 1 := by
    fin_cases j <;> simp [B0579.dir, Prod.norm_def]
  have h1 := (fderiv ℝ (lmRho c k) (lmPer c z)).le_opNorm (B0579.dir j)
  have h2 := hM (lmPer c z)
  have hnn : 0 ≤ ‖fderiv ℝ (lmRho c k) (lmPer c z)‖ := norm_nonneg _
  calc |B0579.pd j (lmRho c k) (lmPer c z)| = ‖fderiv ℝ (lmRho c k) (lmPer c z) (B0579.dir j)‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ‖fderiv ℝ (lmRho c k) (lmPer c z)‖ * ‖B0579.dir j‖ := h1
    _ ≤ ‖fderiv ℝ (lmRho c k) (lmPer c z)‖ * 1 := mul_le_mul_of_nonneg_left hd hnn
    _ ≤ M := by linarith

theorem lmK_pd_continuous {c : ℝ} (hc : 0 < c) (k : ℕ) (j : Fin 2) :
    Continuous (B0579.pd j (lmK c k)) :=
  ((lmK_contDiff hc k).continuous_fderiv (by simp)).clm_apply continuous_const

theorem lmJs_pd_kernel {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (j : Fin 2) (x : ℝ × ℝ) :
    LMPd j (lmJs c k g) x = ∫ y in B0579.cell c, (B0579.pd j (lmK c k) (x - y) : ℂ) * g y := by
  rw [lmJs_pd_plane hc k hg j x, lmJs_pd_cell hc k g j x]

theorem lmJs_pd_continuous {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (j : Fin 2) :
    Continuous (LMPd j (lmJs c k g)) := by
  have hsm := lmJs_contDiff hc k hg
  have heq : LMPd j (lmJs c k g) = fun y => fderiv ℝ (lmJs c k g) y (B0579.dir j) :=
    funext fun y => lmPd_eq_fderiv ((hsm.differentiable (by simp)) y) j
  rw [heq]
  exact (hsm.continuous_fderiv (by simp)).clm_apply continuous_const

/-- **`∂ⱼ lmJ` is bounded on `L²(cell)`** (clause `gradL2` of `LMMollH1`). -/
theorem lmJ_gradL2 {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, ∀ f : LMSpField, LMCellL2 c f → ∀ i j : Fin 2,
      MemLp (LMPd j (fun y => lmJ c k f y i)) 2 (volume.restrict (B0579.cell c)) ∧
        ∫ x in B0579.cell c, ‖LMPd j (fun y => lmJ c k f y i) x‖ ^ 2 ≤
          C * ∫ x in B0579.cell c, ∑ l : Fin 2, ‖f x l‖ ^ 2 := by
  obtain ⟨M, hM⟩ := lmK_pd_bdd hc k
  refine ⟨lmSchurA c M ^ 2, fun f hf i j => ?_⟩
  have hm : Measurable (B0579.pd j (lmK c k)) := (lmK_pd_continuous hc k j).measurable
  have hb : ∀ z : ℝ × ℝ, c / 3 ≤ |z.2| → B0579.pd j (lmK c k) z = 0 := fun z hz =>
    lmK_pd_band hc k j hz
  have e1 : LMPd j (fun y => lmJ c k f y i) =
      fun x => ∫ y in B0579.cell c, (B0579.pd j (lmK c k) (x - y) : ℂ) * f y i :=
    funext fun x => lmJs_pd_kernel hc k (hf i) j x
  have hcont : Continuous fun x => ∫ y in B0579.cell c, (B0579.pd j (lmK c k) (x - y) : ℂ) * f y i := by
    rw [← e1]
    exact lmJs_pd_continuous hc k (hf i) j
  obtain ⟨h1, h2⟩ := lm_schur_L2 hc hm (hM j) hb (hf i) hcont
  rw [e1]
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))⟩
  refine integral_mono (lm_integrable_sq (hf i))
    (integrable_finsetSum _ fun l _ => lm_integrable_sq (hf l)) fun x => ?_
  exact Finset.single_le_sum (f := fun l => ‖f x l‖ ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i)

/-- **`lmJ` maps weakly divergence-free fields to divergence-free fields** (clause `divFreeWeak` of
`LMMollH1`). -/
theorem lmJ_divFreeWeak {c : ℝ} (hc : 0 < c) (k : ℕ) (f : LMSpField) (hf : LMCellL2 c f)
    (hd : LMWeakDivFree c f) (x : ℝ × ℝ) :
    LMPd 0 (fun y => lmJ c k f y 0) x + LMPd 1 (fun y => lmJ c k f y 1) x = 0 := by
  have htest := (lmK_test hc k x).1
  have e : ∀ j : Fin 2, LMPd j (fun y => lmJ c k f y j) x =
      -∫ y in B0579.cell c, f y j * (B0579.pd j (fun y => lmK c k (x - y)) y : ℂ) := fun j =>
    lmJs_pd hc k (hf j) j x
  have hint : ∀ j : Fin 2, Integrable
      (fun y => f y j * (B0579.pd j (fun y => lmK c k (x - y)) y : ℂ))
      (volume.restrict (B0579.cell c)) := fun j => by
    have hpd := htest.pd j
    have h2 : MemLp (fun y => (B0579.pd j (fun y => lmK c k (x - y)) y : ℂ)) 2
        (volume.restrict (B0579.cell c)) := by
      obtain ⟨M, hM⟩ := lmK_pd_bdd hc k
      have h3 := lm_memLp_band (c := c) (h := fun z => -B0579.pd j (lmK c k) z)
        (lmK_pd_continuous hc k j).measurable.neg (fun z => by simpa using hM j z)
        (fun z hz => by simp [lmK_pd_band hc k j hz]) x 2
      have e2 : (fun y => (B0579.pd j (fun y => lmK c k (x - y)) y : ℂ)) =
          fun y => ((-B0579.pd j (lmK c k) (x - y) : ℝ) : ℂ) := funext fun y => by
        rw [(lmK_test hc k x).2 j y]
      rw [e2]
      exact h3.ofReal
    exact (hf j).integrable_mul h2
  have hz := hd _ htest
  rw [integral_add (hint 0) (hint 1)] at hz
  rw [e 0, e 1]
  linear_combination -hz

/-- **`lmJ` has the two properties of `LMMollH1`.** -/
theorem lmJ_H1 {c : ℝ} (hc : 0 < c) : LMMollH1 c (lmJ c) :=
  ⟨fun k => lmJ_gradL2 hc k, fun k f hf hd x => lmJ_divFreeWeak hc k f hf hd x⟩

end UnforcedLeray.Short.IIIa
