import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

/-!
# `PartIII-a:T21/2/2/3/7`: the diffusion integration by parts for `E_1`

Source: `the November 2 reference manuscript`, lines 3060-3069 (no seam terms since
`w` and `Φ` are `d`-periodic). With `g = ∂_kΦ`, `F_l = w Re(conj g ∂_l g)`:
`∂_l F_l = ∂_l w Re(conj g ∂_l g) + w |∂_l g|² + w Re(conj g ∂_l∂_l g)`, all three integrable
(`int1`, `int2`, `int3`, `|∂_l w| ≤ C w`), and `∫_cell (∂_0F_0 + ∂_1F_1) = 0` by
`E0.cellDivZero`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

theorem pd_reconj {g h : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (l : Fin 2) (y : ℝ × ℝ) :
    B0579.pd l (fun x => ((starRingEnd ℂ) (g x) * h x).re) y =
      ((starRingEnd ℂ) (pdCx l g y) * h y).re + ((starRingEnd ℂ) (g y) * pdCx l h y).re := by
  have h1 : HasFDerivAt (fun x => (starRingEnd ℂ) (g x))
      ((Complex.conjCLE.toContinuousLinearMap).comp (fderiv ℝ g y)) y :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp y (hg y).hasFDerivAt
  have h2 := h1.mul (hh y).hasFDerivAt
  have h3 := Complex.reCLM.hasFDerivAt.comp y h2
  unfold B0579.pd pdCx
  have := h3.fderiv
  have e : (fun x => ((starRingEnd ℂ) (g x) * h x).re) =
    (⇑Complex.reCLM ∘ ((fun x => (starRingEnd ℂ) (g x)) * h)) := rfl
  rw [e, this]
  simp [mul_comm]
  ring


theorem re_conj_self (z : ℂ) : ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem int_re_prod {d : ℝ} {w W : ℝ × ℝ → ℝ} {C : ℝ} (hW : Continuous W)
    (hw0 : ∀ y, 0 ≤ w y) (hb : ∀ y, |W y| ≤ C * w y) {u v : ℝ × ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v)
    (hiu : IntegrableOn (fun y => w y * ‖u y‖ ^ 2) (B0579.cell d))
    (hiv : IntegrableOn (fun y => w y * ‖v y‖ ^ 2) (B0579.cell d)) :
    IntegrableOn (fun y => W y * ((starRingEnd ℂ) (u y) * v y).re) (B0579.cell d) := by
  have hcont : Continuous (fun y => W y * ((starRingEnd ℂ) (u y) * v y).re) :=
    hW.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hu).mul hv))
  refine Integrable.mono' ((hiu.add hiv).const_mul (|C| / 2)) hcont.aestronglyMeasurable
    (ae_restrict_of_forall_mem (B0579.measurableSet_cell d) fun y _ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have r : |((starRingEnd ℂ) (u y) * v y).re| ≤ ‖u y‖ * ‖v y‖ := by
    calc _ ≤ ‖(starRingEnd ℂ) (u y) * v y‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, Complex.norm_conj]
  have hbw : |W y| ≤ |C| * w y := (hb y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hw0 y))
  have hwy := hw0 y
  calc |W y| * |((starRingEnd ℂ) (u y) * v y).re|
      ≤ (|C| * w y) * (‖u y‖ * ‖v y‖) :=
        mul_le_mul hbw r (abs_nonneg _) (by positivity)
    _ ≤ |C| / 2 * (w y * ‖u y‖ ^ 2 + w y * ‖v y‖ ^ 2) := by
        have : 0 ≤ |C| * w y := by positivity
        nlinarith [mul_nonneg this (sq_nonneg (‖u y‖ - ‖v y‖))]

theorem diffusion_gen (d : ℝ) (hd : 0 < d) (w : ℝ × ℝ → ℝ) (CW : ℝ) (hw : ContDiff ℝ ∞ w)
    (hwp : ∀ y : ℝ × ℝ, w (y.1 + d, y.2) = w y) (hw0 : ∀ y, 0 ≤ w y)
    (hgrad : ∀ (y : ℝ × ℝ) (l : Fin 2), |B0579.pd l w y| ≤ CW * w y)
    (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgp : ∀ y : ℝ × ℝ, g (y.1 + d, y.2) = g y)
    (hi1 : IntegrableOn (fun y => w y * ‖g y‖ ^ 2) (B0579.cell d))
    (hi2 : ∀ l, IntegrableOn (fun y => w y * ‖pdCx l g y‖ ^ 2) (B0579.cell d))
    (hi3 : ∀ l, IntegrableOn (fun y => w y * ‖pdCx l (pdCx l g) y‖ ^ 2) (B0579.cell d)) :
    IntegrableOn (fun y => w y * ((starRingEnd ℂ) (g y) * lapC g y).re) (B0579.cell d) ∧
      (∀ l : Fin 2, IntegrableOn (fun y => B0579.pd l w y *
        ((starRingEnd ℂ) (g y) * pdCx l g y).re) (B0579.cell d)) ∧
      ∫ y in B0579.cell d, w y * ((starRingEnd ℂ) (g y) * lapC g y).re =
        -(∑ l : Fin 2, ∫ y in B0579.cell d, w y * ‖pdCx l g y‖ ^ 2) -
          ∑ l : Fin 2, ∫ y in B0579.cell d, B0579.pd l w y *
            ((starRingEnd ℂ) (g y) * pdCx l g y).re := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast le_top)
  have hgl : ∀ l, ContDiff ℝ ∞ (pdCx l g) := fun l => pdCx_contDiff hg l
  have hgll : ∀ l, ContDiff ℝ ∞ (pdCx l (pdCx l g)) := fun l => pdCx_contDiff (hgl l) l
  have hcw : Continuous w := hw.continuous
  have hcg : Continuous g := hg.continuous
  have hcgl : ∀ l, Continuous (pdCx l g) := fun l => (hgl l).continuous
  have hcgll : ∀ l, Continuous (pdCx l (pdCx l g)) := fun l => (hgll l).continuous
  have hpw : ∀ l, Continuous (B0579.pd l w) := fun l => pdContinuous hw1 l
  -- the three pieces
  have iA : ∀ l, IntegrableOn (fun y => B0579.pd l w y *
      ((starRingEnd ℂ) (g y) * pdCx l g y).re) (B0579.cell d) := fun l =>
    int_re_prod (hpw l) hw0 (fun y => hgrad y l) hcg (hcgl l) hi1 (hi2 l)
  have iB := hi2
  have iC : ∀ l, IntegrableOn (fun y => w y *
      ((starRingEnd ℂ) (g y) * pdCx l (pdCx l g) y).re) (B0579.cell d) := fun l =>
    int_re_prod (C := 1) hcw hw0 (fun y => by rw [abs_of_nonneg (hw0 y), one_mul]) hcg (hcgll l)
      hi1 (hi3 l)
  have hF1 : ∀ l, ContDiff ℝ 1 (fun z => w z * ((starRingEnd ℂ) (g z) * pdCx l g z).re) := by
    intro l
    have h1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
    have h2 : ContDiff ℝ 1 (pdCx l g) := (hgl l).of_le (by exact_mod_cast le_top)
    exact hw1.mul (Complex.reCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp h1).mul h2))
  have prod : ∀ (l : Fin 2) (y : ℝ × ℝ),
      B0579.pd l (fun z => w z * ((starRingEnd ℂ) (g z) * pdCx l g z).re) y =
        B0579.pd l w y * ((starRingEnd ℂ) (g y) * pdCx l g y).re + w y * ‖pdCx l g y‖ ^ 2 +
          w y * ((starRingEnd ℂ) (g y) * pdCx l (pdCx l g) y).re := by
    intro l y
    have hgd : Differentiable ℝ g := hg.differentiable (by simp)
    have hgld : Differentiable ℝ (pdCx l g) := (hgl l).differentiable (by simp)
    have hRd : DifferentiableAt ℝ (fun z => ((starRingEnd ℂ) (g z) * pdCx l g z).re) y := by
      have h1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
      have h2 : ContDiff ℝ 1 (pdCx l g) := (hgl l).of_le (by exact_mod_cast le_top)
      exact ((Complex.reCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp h1).mul h2)).differentiable
        one_ne_zero) y
    rw [pd_mul ((hw1.differentiable one_ne_zero) y) hRd, pd_reconj hgd hgld l y, re_conj_self]
    ring
  have hzero := UnforcedLeray.Short.IIIa.E0.cellDivZero d hd _ _ (hF1 0) (hF1 1)
    (fun y => by simp only [hwp, hgp, pdCx_periodic d hgp 0 y])
    (int_re_prod (C := 1) hcw hw0 (fun y => by rw [abs_of_nonneg (hw0 y), one_mul]) hcg (hcgl 1)
      hi1 (hi2 1))
    (by
      have := (((iA 0).add (iB 0)).add (iC 0)).add (((iA 1).add (iB 1)).add (iC 1))
      refine this.congr_fun (fun y _ => ?_) (B0579.measurableSet_cell d)
      simp only [Pi.add_apply, prod]; try ring)
  have hlap : ∫ y in B0579.cell d, w y * ((starRingEnd ℂ) (g y) * lapC g y).re =
      ∑ l : Fin 2, ∫ y in B0579.cell d, w y *
        ((starRingEnd ℂ) (g y) * pdCx l (pdCx l g) y).re := by
    rw [Fin.sum_univ_two, ← integral_add (iC 0) (iC 1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [lapC, mul_add, Complex.add_re, mul_add]
  refine ⟨?_, iA, ?_⟩
  · have := (iC 0).add (iC 1)
    refine this.congr_fun (fun y _ => ?_) (B0579.measurableSet_cell d)
    simp only [Pi.add_apply, lapC, mul_add, Complex.add_re]
  · rw [hlap]
    have hint : ∀ l : Fin 2, IntegrableOn
        (fun y => B0579.pd l (fun z => w z * ((starRingEnd ℂ) (g z) * pdCx l g z).re) y)
        (B0579.cell d) := by
      intro l
      refine (((iA l).add (iB l)).add (iC l)).congr_fun (fun y _ => ?_)
        (B0579.measurableSet_cell d)
      simp only [Pi.add_apply, prod]
    have hz2 := hzero
    rw [integral_add (hint 0) (hint 1)] at hz2
    have hI : ∀ l : Fin 2, ∫ y in B0579.cell d,
        B0579.pd l (fun z => w z * ((starRingEnd ℂ) (g z) * pdCx l g z).re) y =
        (∫ y in B0579.cell d, B0579.pd l w y * ((starRingEnd ℂ) (g y) * pdCx l g y).re) +
        (∫ y in B0579.cell d, w y * ‖pdCx l g y‖ ^ 2) +
        ∫ y in B0579.cell d, w y * ((starRingEnd ℂ) (g y) * pdCx l (pdCx l g) y).re := by
      intro l
      have e1 := integral_add (iA l) (iB l)
      have e2 := integral_add ((iA l).add (iB l)) (iC l)
      simp only [Pi.add_apply] at e1 e2
      rw [← e1, ← e2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only [prod])
    simp only [Fin.sum_univ_two]
    rw [hI 0, hI 1] at hz2
    linarith

theorem e1DiffusionIBP (m : ℝ) (hm : 8 < m)
    (hW : UnforcedLeray.Short.IIIa.PeriodicWeightLogBounds) :
    UnforcedLeray.Short.IIIa.AdjE1.E1DiffusionIBP m := by
  intro d Φ hd hlo hhi k
  obtain ⟨CW, hCW⟩ := hW (-m)
  have hb := (hCW d hd).1
  exact diffusion_gen d hd (periodicWeight (-m) d) CW (pw_contDiff _ _) (pw_periodic _ _ hd.ne')
    (fun y => (pw_pos _ _ y).le) (fun y l => pw_pd_abs_le (-m) d CW hb l y)
    (pdCx k Φ) (pdCx_contDiff hlo.smooth k) (pdCx_periodic d hlo.periodic k) (hlo.int1 k)
    (fun l => hhi.int2 l k) (fun l => hhi.int3 l l k)

end UnforcedLeray.Short.IIIa.AdjE1
