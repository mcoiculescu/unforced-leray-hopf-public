import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.WPeriodic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod

/-!
# `PartIII-a:T21/2/7/2/1/1/2/12`: spatial derivatives pass under `K_c`

Proof of `TjKcDerivSpace` (`Sub/AdjInterior/Train/Defs.lean`, SP 3052-3058).

For `p = (ρ, x)` with `ρ ≥ 0` and a spatial direction `a`, the derivative of `h` along the line
`s ↦ p + s stDir a` is `tjW [a] h p` (`tj_line_hasDerivAt`). Since `h = K_c g` on `tjU` and the
line stays in `tjU`, the centred form `Cyl.K_eq_reflect` writes `K_c g` on the line as the cell
integral of `g(ρ, (x + s e) - y) • bsKernel c y`. Differentiation under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on `|s| < 1` is dominated by
`C 3^σ (1 + (x₂ - y₂)²)^{-σ} ‖bsKernel c y‖`, `σ = (m+1)/2`, which is integrable on the cell
(`bsKernel_split`, and `m > 0` makes `(1 + u²)^{-σ}` integrable on `ℝ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

theorem tj_stDir_fst {a : Fin 3} (ha : a ≠ 0) : (stDir a).1 = 0 := by
  revert ha; fin_cases a <;> simp [stDir]

theorem tj_stDir_snd_abs {a : Fin 3} (ha : a ≠ 0) : |(stDir a).2.2| ≤ 1 := by
  revert ha; fin_cases a <;> simp [stDir]

/-- The derivative of `h` along a spatial line through `p ∈ tjU` (vector valued). -/
theorem tj_line_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ × (ℝ × ℝ) → F} (hh : ContDiffOn ℝ ∞ h tjU) {a : Fin 3} (ha : (stDir a).1 = 0)
    {p : ℝ × (ℝ × ℝ)} (hp : p ∈ tjU) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (p + s • stDir a)) (tjW [a] h (p + t • stDir a)) t := by
  have h1 : ∀ s : ℝ, (p + s • stDir a).1 = p.1 := fun s => by simp [ha]
  have hpt : ∀ s : ℝ, p + s • stDir a ∈ tjU := fun s => by
    refine mem_prod.2 ⟨?_, mem_univ _⟩
    rw [h1]
    exact (mem_prod.1 hp).1
  have hγ : HasDerivAt (fun s : ℝ => p + s • stDir a) (stDir a) t := by
    have := ((hasDerivAt_id t).smul_const (stDir a)).const_add p
    simpa using this
  have hd : HasFDerivWithinAt h (fderivWithin ℝ h tjU (p + t • stDir a)) tjU
      (p + t • stDir a) :=
    ((hh.differentiableOn (by simp)) _ (hpt t)).hasFDerivWithinAt
  have hmaps : MapsTo (fun s : ℝ => p + s • stDir a) univ tjU := fun s _ => hpt s
  have := hd.comp_hasDerivWithinAt t hγ.hasDerivWithinAt hmaps
  exact hasDerivWithinAt_univ.1 this

/-- `1 + u²` against `1 + (u + w)²` for `|w| ≤ 1`. -/
theorem tj_wt_compare {σ : ℝ} (hσ : 0 ≤ σ) (u w : ℝ) (hw : |w| ≤ 1) :
    (1 + (u + w) ^ 2) ^ (-σ) ≤ (3 : ℝ) ^ σ * (1 + u ^ 2) ^ (-σ) := by
  have hw2 : w ^ 2 ≤ 1 := by nlinarith [sq_abs w, abs_nonneg w]
  have hB : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have hA : (1 + u ^ 2) / 3 ≤ 1 + (u + w) ^ 2 := by
    nlinarith [sq_nonneg (u + 2 * w), sq_nonneg (u + w)]
  calc (1 + (u + w) ^ 2) ^ (-σ) ≤ ((1 + u ^ 2) / 3) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hA (by linarith)
    _ = (1 + u ^ 2) ^ (-σ) / (3 : ℝ) ^ (-σ) := Real.div_rpow hB.le (by norm_num) _
    _ = (3 : ℝ) ^ σ * (1 + u ^ 2) ^ (-σ) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), div_inv_eq_mul, mul_comm]

/-- Passing from the weighted bound to the unweighted one. -/
theorem tj_abs_le_of_wt {m C v D : ℝ} (hC0 : 0 ≤ C)
    (hD : (1 + v ^ 2) ^ ((m + 1) / 2) * |D| ≤ C) :
    |D| ≤ C * (1 + v ^ 2) ^ (-((m + 1) / 2)) := by
  have hP : 0 < (1 + v ^ 2) ^ ((m + 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
  rw [Real.rpow_neg (show (0 : ℝ) ≤ 1 + v ^ 2 by positivity), le_mul_inv_iff₀ hP]
  rw [mul_comm]
  exact hD

/-- Integrability of the weighted kernel on the cell. -/
theorem tj_wt_integrable {m c : ℝ} (hm : 0 < m) (hc : 1 ≤ c) (x2 : ℝ) :
    Integrable (fun y : ℝ × ℝ => (1 + (x2 - y.2) ^ 2) ^ (-((m + 1) / 2)) *
      ‖UnforcedLeray.Cyl.bsKernel c y‖) (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
  obtain ⟨C, -, hsplit⟩ := UnforcedLeray.Cyl.bsKernel_split
  obtain ⟨hnear, hfar, hdec⟩ := hsplit c hc
  have h1 : Integrable (fun u : ℝ => ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(m + 1) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simp only [Module.finrank_self, Nat.cast_one]; linarith)
  have hline : Integrable (fun η : ℝ => (1 + (x2 - η) ^ 2) ^ (-((m + 1) / 2))) volume := by
    have h2 := (MeasureTheory.integrable_comp_sub_left (μ := (volume : Measure ℝ))
      (fun u : ℝ => ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(m + 1) / 2)) x2).2 h1
    refine h2.congr (Filter.Eventually.of_forall fun η => ?_)
    show ((1 : ℝ) + ‖x2 - η‖ ^ 2) ^ (-(m + 1) / 2) = _
    rw [Real.norm_eq_abs, sq_abs, neg_div]
  have hG : Integrable (fun z : ℝ × ℝ => (Set.Ico (-c / 2) (c / 2)).indicator
      (fun _ => (1 : ℝ)) z.1 * (1 + (x2 - z.2) ^ 2) ^ (-((m + 1) / 2))) volume := by
    rw [Measure.volume_eq_prod]
    exact (((integrableOn_const (C := (1 : ℝ)) (s := Set.Ico (-c / 2) (c / 2)) (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Ico)).mul_prod hline
  have hGr := hG.restrict (s := UnforcedLeray.Cyl.cell c)
  have hnearM : Measurable (UnforcedLeray.Cyl.kNear c) :=
    (UnforcedLeray.Cyl.measurable_bsKernel c).indicator
      ((UnforcedLeray.Cyl.measurableSet_cell c).inter measurableSet_ball)
  have hnearI : Integrable (UnforcedLeray.Cyl.kNear c)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    ⟨hnearM.aestronglyMeasurable, lt_of_le_of_lt hnear ENNReal.ofReal_lt_top⟩
  have hB : Integrable (fun y => ‖UnforcedLeray.Cyl.kNear c y‖ +
      2 * ((Set.Ico (-c / 2) (c / 2)).indicator (fun _ => (1 : ℝ)) y.1 *
        (1 + (x2 - y.2) ^ 2) ^ (-((m + 1) / 2))))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    hnearI.norm.add (hGr.const_mul 2)
  refine Integrable.mono' hB ?_ ?_
  · exact ((((measurable_const.add ((measurable_const.sub measurable_snd).pow_const 2)).pow_const
      _).mul (UnforcedLeray.Cyl.measurable_bsKernel c).norm)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem (UnforcedLeray.Cyl.measurableSet_cell c) ?_
    intro y hy
    have hyI : y.1 ∈ Set.Ico (-c / 2) (c / 2) :=
      ⟨(UnforcedLeray.Cyl.mem_cell.1 hy).1, (UnforcedLeray.Cyl.mem_cell.1 hy).2⟩
    have hind : (Set.Ico (-c / 2) (c / 2)).indicator (fun _ => (1 : ℝ)) y.1 = 1 :=
      Set.indicator_of_mem hyI _
    have hwt0 : 0 ≤ (1 + (x2 - y.2) ^ 2) ^ (-((m + 1) / 2)) :=
      Real.rpow_nonneg (by positivity) _
    have hwt1 : (1 + (x2 - y.2) ^ 2) ^ (-((m + 1) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)
    have hK : ‖UnforcedLeray.Cyl.bsKernel c y‖ ≤ ‖UnforcedLeray.Cyl.kNear c y‖ + 2 := by
      rw [hdec y hy]
      exact (norm_add_le _ _).trans (by linarith [hfar y])
    rw [hind, one_mul, Real.norm_of_nonneg (mul_nonneg hwt0 (norm_nonneg _))]
    have e1 := mul_le_mul_of_nonneg_left hK hwt0
    have e2 := mul_le_mul_of_nonneg_right hwt1 (norm_nonneg (UnforcedLeray.Cyl.kNear c y))
    have e3 : (1 + (x2 - y.2) ^ 2) ^ (-((m + 1) / 2)) * (‖UnforcedLeray.Cyl.kNear c y‖ + 2) =
        (1 + (x2 - y.2) ^ 2) ^ (-((m + 1) / 2)) * ‖UnforcedLeray.Cyl.kNear c y‖ +
          2 * (1 + (x2 - y.2) ^ 2) ^ (-((m + 1) / 2)) := by ring
    linarith [e1, e2, e3]

theorem tjKcDerivSpace : TjKcDerivSpace := by
  intro c m hc hm g h hg hh hper hgW a ha hDW hEq
  rintro ⟨ρ, x⟩ hp
  have hρ : 0 ≤ ρ := mem_Ici.1 (mem_prod.1 hp).1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have ha0 : (stDir a).1 = 0 := tj_stDir_fst ha
  have hab : |(stDir a).2.2| ≤ 1 := tj_stDir_snd_abs ha
  have hσ : (0 : ℝ) ≤ (m + 1) / 2 := by linarith
  obtain ⟨C, hC⟩ := hDW ρ hρ
  obtain ⟨Cg, hCg⟩ := hgW ρ hρ
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (tjWt_pos m _).le (abs_nonneg _)) (hC ρ ⟨hρ, le_rfl⟩ (0, 0))
  have hCg0 : 0 ≤ Cg :=
    le_trans (mul_nonneg (tjWt_pos m _).le (abs_nonneg _)) (hCg ρ ⟨hρ, le_rfl⟩ (0, 0))
  -- Step 1: the derivative of `h` along the line through `(ρ, x)`
  have hpoint : ∀ s : ℝ, (ρ, x) + s • stDir a = (ρ, x + s • (stDir a).2) := fun s =>
    Prod.ext (by simp [ha0]) (by simp)
  have H1 : HasDerivAt (fun s : ℝ => h ((ρ, x) + s • stDir a)) (tjW [a] h (ρ, x)) 0 := by
    have := tj_line_hasDerivAt hh ha0 hp 0
    rwa [zero_smul, add_zero] at this
  -- Step 2: `K_c g` on the line
  have H2 : HasDerivAt (fun s : ℝ => tjKc c g (ρ, x + s • (stDir a).2)) (tjW [a] h (ρ, x)) 0 := by
    have hfun : (fun s : ℝ => tjKc c g (ρ, x + s • (stDir a).2)) =
        (fun s : ℝ => h ((ρ, x) + s • stDir a)) := by
      funext s
      rw [hpoint s]
      have hmem : (ρ, x + s • (stDir a).2) ∈ tjU :=
        mem_prod.2 ⟨mem_Ici.2 hρ, mem_univ _⟩
      exact (hEq hmem).symm
    rw [hfun]
    exact H1
  -- Step 3: the derivative of `K_c g` along the line
  have H3 : HasDerivAt (fun s : ℝ => tjKc c g (ρ, x + s • (stDir a).2))
      (tjKc c (tjW [a] g) (ρ, x)) 0 := by
    have hωg : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => g (ρ, w)) :=
      fun z => hper ρ hρ z
    have hωW : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => tjW [a] g (ρ, w)) :=
      fun z => tjWPeriodic c g hg hper [a] ρ hρ z
    have hK_g : ∀ s : ℝ, tjKc c g (ρ, x + s • (stDir a).2) =
        ∫ y in UnforcedLeray.Cyl.cell c, g (ρ, (x + s • (stDir a).2) - y) •
          UnforcedLeray.Cyl.bsKernel c y := fun s =>
      UnforcedLeray.Cyl.K_eq_reflect hc0 hωg (x + s • (stDir a).2)
    have hR : tjKc c (tjW [a] g) (ρ, x) =
        ∫ y in UnforcedLeray.Cyl.cell c, tjW [a] g (ρ, x - y) •
          UnforcedLeray.Cyl.bsKernel c y :=
      UnforcedLeray.Cyl.K_eq_reflect hc0 hωW x
    have hfunK : (fun s : ℝ => tjKc c g (ρ, x + s • (stDir a).2)) =
        (fun s : ℝ => ∫ y in UnforcedLeray.Cyl.cell c, g (ρ, (x + s • (stDir a).2) - y) •
          UnforcedLeray.Cyl.bsKernel c y) := funext hK_g
    rw [hfunK, hR]
    -- measurability
    have hgcont : ContinuousOn g tjU := hg.continuousOn
    have hWcont : ContinuousOn (tjW [a] g) tjU := (tjW_contDiffOn hg [a]).continuousOn
    have hmeasG : ∀ s : ℝ, AEStronglyMeasurable (fun y : ℝ × ℝ =>
        g (ρ, (x + s • (stDir a).2) - y) • UnforcedLeray.Cyl.bsKernel c y)
        (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
      intro s
      have hc1 : Continuous (fun y : ℝ × ℝ => g (ρ, (x + s • (stDir a).2) - y)) :=
        hgcont.comp_continuous (continuous_const.prodMk (continuous_const.sub continuous_id))
          (fun y => mem_prod.2 ⟨mem_Ici.2 hρ, mem_univ _⟩)
      exact hc1.aestronglyMeasurable.smul
        (UnforcedLeray.Cyl.measurable_bsKernel c).aestronglyMeasurable
    have hmeasF' : ∀ s : ℝ, AEStronglyMeasurable (fun y : ℝ × ℝ =>
        tjW [a] g (ρ, (x + s • (stDir a).2) - y) • UnforcedLeray.Cyl.bsKernel c y)
        (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
      intro s
      have hc1 : Continuous (fun y : ℝ × ℝ => tjW [a] g (ρ, (x + s • (stDir a).2) - y)) :=
        hWcont.comp_continuous (continuous_const.prodMk (continuous_const.sub continuous_id))
          (fun y => mem_prod.2 ⟨mem_Ici.2 hρ, mem_univ _⟩)
      exact hc1.aestronglyMeasurable.smul
        (UnforcedLeray.Cyl.measurable_bsKernel c).aestronglyMeasurable
    -- the pointwise bound on `|s| < 1`
    have hFbd : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ y : ℝ × ℝ,
        ‖tjW [a] g (ρ, (x + s • (stDir a).2) - y) • UnforcedLeray.Cyl.bsKernel c y‖ ≤
          (C * (3 : ℝ) ^ ((m + 1) / 2)) * ((1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) *
            ‖UnforcedLeray.Cyl.bsKernel c y‖) := by
      intro s hs y
      have hs1 : |s| < 1 := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
        exact hs
      have hD := tj_abs_le_of_wt (v := ((x + s • (stDir a).2) - y).2) hC0
        (hC ρ ⟨hρ, le_rfl⟩ ((x + s • (stDir a).2) - y))
      have hv : ((x + s • (stDir a).2) - y).2 = (x.2 - y.2) + s * (stDir a).2.2 := by
        simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        ring
      rw [hv] at hD
      have hw : |s * (stDir a).2.2| ≤ 1 := by
        rw [abs_mul]
        nlinarith [abs_nonneg s, abs_nonneg (stDir a).2.2]
      have hcmp := tj_wt_compare hσ (x.2 - y.2) (s * (stDir a).2.2) hw
      rw [norm_smul, Real.norm_eq_abs]
      calc |tjW [a] g (ρ, (x + s • (stDir a).2) - y)| * ‖UnforcedLeray.Cyl.bsKernel c y‖
          ≤ (C * ((3 : ℝ) ^ ((m + 1) / 2) * (1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)))) *
              ‖UnforcedLeray.Cyl.bsKernel c y‖ :=
            mul_le_mul_of_nonneg_right (hD.trans (mul_le_mul_of_nonneg_left hcmp hC0))
              (norm_nonneg _)
        _ = (C * (3 : ℝ) ^ ((m + 1) / 2)) * ((1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) *
            ‖UnforcedLeray.Cyl.bsKernel c y‖) := by ring
    -- integrability at `s = 0`
    have hF0 : Integrable (fun y : ℝ × ℝ =>
        g (ρ, (x + (0 : ℝ) • (stDir a).2) - y) • UnforcedLeray.Cyl.bsKernel c y)
        (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
      refine Integrable.mono' ((tj_wt_integrable hm hc x.2).const_mul Cg)
        (hmeasG 0) (ae_of_all _ fun y => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      have hv0 : ((x + (0 : ℝ) • (stDir a).2) - y).2 = x.2 - y.2 := by simp
      have hD := tj_abs_le_of_wt (v := ((x + (0 : ℝ) • (stDir a).2) - y).2) hCg0
        (hCg ρ ⟨hρ, le_rfl⟩ ((x + (0 : ℝ) • (stDir a).2) - y))
      rw [hv0] at hD
      exact (mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans (le_of_eq (by ring))
    -- the derivative of the integrand
    have hdiff : ∀ᵐ y ∂(volume.restrict (UnforcedLeray.Cyl.cell c)), ∀ s ∈ Metric.ball (0 : ℝ) 1,
        HasDerivAt (fun s' : ℝ => g (ρ, (x + s' • (stDir a).2) - y) •
            UnforcedLeray.Cyl.bsKernel c y)
          (tjW [a] g (ρ, (x + s • (stDir a).2) - y) • UnforcedLeray.Cyl.bsKernel c y) s := by
      refine ae_of_all _ (fun y s _ => ?_)
      have hline := tj_line_hasDerivAt hg ha0 (p := (ρ, x - y))
        (mem_prod.2 ⟨mem_Ici.2 hρ, mem_univ _⟩) s
      have e1 : ∀ s' : ℝ, (ρ, x - y) + s' • stDir a = (ρ, (x + s' • (stDir a).2) - y) :=
        fun s' => Prod.ext (by simp [ha0]) (by simp only [Prod.snd_add, Prod.smul_snd]; abel)
      simp only [e1] at hline
      exact hline.smul_const (UnforcedLeray.Cyl.bsKernel c y)
    have hbI : Integrable (fun y : ℝ × ℝ => (C * (3 : ℝ) ^ ((m + 1) / 2)) *
        ((1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖))
        (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
      (tj_wt_integrable hm hc x.2).const_mul _
    have hbound : ∀ᵐ y ∂(volume.restrict (UnforcedLeray.Cyl.cell c)),
        ∀ s ∈ Metric.ball (0 : ℝ) 1,
          ‖tjW [a] g (ρ, (x + s • (stDir a).2) - y) • UnforcedLeray.Cyl.bsKernel c y‖ ≤
            (C * (3 : ℝ) ^ ((m + 1) / 2)) * ((1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) *
              ‖UnforcedLeray.Cyl.bsKernel c y‖) :=
      ae_of_all _ (fun y s hs => hFbd s hs y)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (UnforcedLeray.Cyl.cell c))
      (F := fun s y => g (ρ, (x + s • (stDir a).2) - y) • UnforcedLeray.Cyl.bsKernel c y)
      (F' := fun s y => tjW [a] g (ρ, (x + s • (stDir a).2) - y) •
        UnforcedLeray.Cyl.bsKernel c y)
      (x₀ := 0) (bound := fun y => (C * (3 : ℝ) ^ ((m + 1) / 2)) *
        ((1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖))
      (Metric.ball_mem_nhds 0 one_pos) (Filter.Eventually.of_forall hmeasG) hF0 (hmeasF' 0)
      hbound hbI hdiff
    simpa only [zero_smul, add_zero] using key.2
  exact H2.unique H3

end UnforcedLeray.Short.IIIa
