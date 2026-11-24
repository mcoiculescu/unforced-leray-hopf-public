import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelDecay.GaussTail
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelDecay.Factor

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/4/3`: value bound of the Duhamel solution

Target: `duhDecValue : DuhDecValue` (`Sub/PartIIIa_T18_2_4_1_4.lean`, leaf 3 of the Duhamel
decay; SP 3427-3440 of `the November 2 reference manuscript`).

For `c, ν > 0`, a `NiceScalar c h`, and `s₂`, put `H = sup ‖h‖` (from `duhSm_bound`, order 0),
`T = |s₂ - a| + 1 > 0` and `κ = 1 / (32 ν T)`. For `s ≤ s₂` the `r`-integral only sees
`0 < r ≤ s - a ≤ T`. Two cases in `η = x.2`:

* `2R ≤ |η|`: the `z`-integrand is nonzero only for `|z.2| ≥ |η|/2`, so
  `‖∫_z G h‖ ≤ H ∫ g(z.1) (1_{|t| ≥ |η|/2} g)(z.2) dz = H ∫_{|t|≥|η|/2} g_{νr}`
  `≤ 2H exp(-η²/(32 ν r)) ≤ 2H e^{-κη²}`; the `r`-integral is over a set of length `≤ T`.
* `|η| < 2R`: `‖∫_z G h‖ ≤ H`, and `H T ≤ 2 H T e^{4R²κ} e^{-κη²}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

theorem duhDecValue : UnforcedLeray.Short.IIIa.DuhDecValue := by
  intro c ν h hc hν hn s₂
  obtain ⟨_hsm, _hper, a, B, R, ha, hvan⟩ := duhSm_unfold hn
  obtain ⟨K0, hK0⟩ := duhSm_bound hc hn 0
  set H : ℝ := max K0 0 with hHdef
  have hH0 : 0 ≤ H := le_max_right _ _
  have hHb : ∀ p : ℝ × (ℝ × ℝ), ‖h p‖ ≤ H := fun p => by
    have h1 := hK0 p
    rw [norm_iteratedFDeriv_zero] at h1
    exact h1.trans (le_max_left _ _)
  set T : ℝ := |s₂ - a| + 1 with hTdef
  have hT : 0 < T := by rw [hTdef]; positivity
  set κ : ℝ := 1 / (32 * ν * T) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hexpLe : ∀ r : ℝ, 0 < r → r ≤ T → ∀ x : ℝ × ℝ,
      -(|x.2| / 2) ^ 2 / (8 * (ν * r)) ≤ -κ * x.2 ^ 2 := by
    intro r hr0 hrT x
    have e1 : -(|x.2| / 2) ^ 2 / (8 * (ν * r)) = -(x.2 ^ 2 / (32 * (ν * r))) := by
      rw [div_pow, sq_abs]; ring
    have e2 : -κ * x.2 ^ 2 = -(x.2 ^ 2 / (32 * ν * T)) := by rw [hκdef]; ring
    rw [e1, e2, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  refine ⟨2 * H * T * Real.exp (4 * R ^ 2 * κ), κ, hκ, ?_⟩
  intro s x hs
  have hsT : s - a ≤ T := by
    have h1 := le_abs_self (s₂ - a)
    have h2 := abs_nonneg (s₂ - a)
    rw [hTdef]; linarith
  unfold duhamelHeat
  set F : ℝ → ℂ := fun r : ℝ => ∫ z : ℝ × ℝ,
    ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) * h (s - r, (x.1 - z.1, x.2 - z.2)) with hF
  -- finishing step: the `r`-integral over `(0, ∞)` reduces to `(0, T]`
  have finish : ∀ M : ℝ, (∀ r : ℝ, 0 < r → r ≤ T → ‖F r‖ ≤ M) →
      M * T ≤ 2 * H * T * Real.exp (4 * R ^ 2 * κ) * Real.exp (-κ * x.2 ^ 2) →
      ‖∫ r in Ioi (0 : ℝ), F r‖ ≤ 2 * H * T * Real.exp (4 * R ^ 2 * κ) * Real.exp (-κ * x.2 ^ 2) := by
    intro M hM hMT
    have hzero : ∀ r : ℝ, T < r → F r = 0 := by
      intro r hr
      have h0 : ∀ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
          h (s - r, (x.1 - z.1, x.2 - z.2)) = 0 := by
        intro z
        rw [hvan (s - r) (x.1 - z.1, x.2 - z.2) (Or.inl (by linarith)), mul_zero]
      simp only [hF]
      simp only [h0, integral_zero]
    have hsplit : ∫ r in Ioi (0 : ℝ), F r = ∫ r in Ioc (0 : ℝ) T, F r := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      intro r hr
      apply hzero r
      by_contra hcon
      exact hr.2 (Set.mem_Ioc.mpr ⟨Set.mem_Ioi.mp hr.1, not_lt.mp hcon⟩)
    have hfin : volume (Ioc (0 : ℝ) T) < ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have hvol : (volume : Measure ℝ).real (Ioc (0 : ℝ) T) = T := by
      simp only [Measure.real, Real.volume_Ioc]
      rw [ENNReal.toReal_ofReal (by linarith)]; ring
    rw [hsplit]
    calc ‖∫ r in Ioc (0 : ℝ) T, F r‖
        ≤ M * (volume : Measure ℝ).real (Ioc (0 : ℝ) T) :=
          norm_setIntegral_le_of_norm_le_const hfin
            (fun r hr => hM r (Set.mem_Ioc.mp hr).1 (Set.mem_Ioc.mp hr).2)
      _ = M * T := by rw [hvol]
      _ ≤ _ := hMT
  by_cases hcase : 2 * R ≤ |x.2|
  · -- Case A: the `z`-integrand is supported where `|z.2| ≥ |η|/2`
    have innerA : ∀ r : ℝ, 0 < r →
        ‖F r‖ ≤ H * (2 * Real.exp (-(|x.2| / 2) ^ 2 / (8 * (ν * r)))) := by
      intro r hr
      have hθ : 0 < ν * r := mul_pos hν hr
      have hA : 0 ≤ |x.2| / 2 := by positivity
      have hSm : MeasurableSet {t : ℝ | |x.2| / 2 ≤ |t|} :=
        measurableSet_le measurable_const continuous_abs.measurable
      have hg1 : Integrable (fun t : ℝ => UnforcedLeray.B0191.heatKernel 1 (ν * r) t) := by
        apply Integrable.of_integral_ne_zero
        have := UnforcedLeray.B0284.integral_heatKernel_one hθ
        simp only [this]
        exact one_ne_zero
      have hψ : Integrable (fun z : ℝ × ℝ => UnforcedLeray.B0191.heatKernel 1 (ν * r) z.1 *
          Set.indicator {t : ℝ | |x.2| / 2 ≤ |t|}
            (fun t => UnforcedLeray.B0191.heatKernel 1 (ν * r) t) z.2) := by
        rw [Measure.volume_eq_prod]
        exact Integrable.mul_prod hg1 (hg1.indicator hSm)
      have hpt : ∀ z : ℝ × ℝ,
          ‖((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
            h (s - r, (x.1 - z.1, x.2 - z.2))‖ ≤
          H * (UnforcedLeray.B0191.heatKernel 1 (ν * r) z.1 *
            Set.indicator {t : ℝ | |x.2| / 2 ≤ |t|}
              (fun t => UnforcedLeray.B0191.heatKernel 1 (ν * r) t) z.2) := by
        intro z
        by_cases hz : |x.2| / 2 ≤ |z.2|
        · have hind : Set.indicator {t : ℝ | |x.2| / 2 ≤ |t|}
              (fun t => UnforcedLeray.B0191.heatKernel 1 (ν * r) t) z.2
              = UnforcedLeray.B0191.heatKernel 1 (ν * r) z.2 :=
            Set.indicator_of_mem (show z.2 ∈ {t : ℝ | |x.2| / 2 ≤ |t|} from hz) _
          have hG := UnforcedLeray.B0284.heatKernel2_nonneg hθ z
          rw [hind, norm_mul, Complex.norm_real, Real.norm_of_nonneg hG]
          calc UnforcedLeray.B0284.heatKernel2 (ν * r) z * ‖h (s - r, (x.1 - z.1, x.2 - z.2))‖
              ≤ UnforcedLeray.B0284.heatKernel2 (ν * r) z * H :=
                mul_le_mul_of_nonneg_left (hHb _) hG
            _ = H * (UnforcedLeray.B0191.heatKernel 1 (ν * r) z.1 *
                  UnforcedLeray.B0191.heatKernel 1 (ν * r) z.2) := by
                unfold UnforcedLeray.B0284.heatKernel2; ring
        · have hind : Set.indicator {t : ℝ | |x.2| / 2 ≤ |t|}
              (fun t => UnforcedLeray.B0191.heatKernel 1 (ν * r) t) z.2 = 0 :=
            Set.indicator_of_notMem (show z.2 ∉ {t : ℝ | |x.2| / 2 ≤ |t|} from hz) _
          have hR : R < |x.2 - z.2| := by
            have h1 := abs_sub_abs_le_abs_sub x.2 z.2
            have h2 := not_le.mp hz
            linarith
          have hh0 : h (s - r, (x.1 - z.1, x.2 - z.2)) = 0 := hvan _ _ (Or.inr (Or.inr hR))
          simp [hind, hh0]
      have hGauss : ∫ t in {t : ℝ | |x.2| / 2 ≤ |t|},
          UnforcedLeray.B0191.heatKernel 1 (ν * r) t
          ≤ 2 * Real.exp (-(|x.2| / 2) ^ 2 / (8 * (ν * r))) :=
        duhDecGaussTail (ν * r) (|x.2| / 2) hθ hA
      have hI : ∫ z : ℝ × ℝ, (UnforcedLeray.B0191.heatKernel 1 (ν * r) z.1 *
          Set.indicator {t : ℝ | |x.2| / 2 ≤ |t|}
            (fun t => UnforcedLeray.B0191.heatKernel 1 (ν * r) t) z.2)
          = 1 * ∫ t in {t : ℝ | |x.2| / 2 ≤ |t|}, UnforcedLeray.B0191.heatKernel 1 (ν * r) t := by
        rw [Measure.volume_eq_prod, integral_prod_mul, UnforcedLeray.B0284.integral_heatKernel_one hθ,
          integral_indicator hSm]
      simp only [hF]
      calc ‖∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
            h (s - r, (x.1 - z.1, x.2 - z.2))‖
          ≤ ∫ z : ℝ × ℝ, H * (UnforcedLeray.B0191.heatKernel 1 (ν * r) z.1 *
              Set.indicator {t : ℝ | |x.2| / 2 ≤ |t|}
                (fun t => UnforcedLeray.B0191.heatKernel 1 (ν * r) t) z.2) :=
            norm_integral_le_of_norm_le (hψ.const_mul H) (Filter.Eventually.of_forall hpt)
        _ = H * ∫ z : ℝ × ℝ, (UnforcedLeray.B0191.heatKernel 1 (ν * r) z.1 *
              Set.indicator {t : ℝ | |x.2| / 2 ≤ |t|}
                (fun t => UnforcedLeray.B0191.heatKernel 1 (ν * r) t) z.2) :=
            integral_const_mul _ _
        _ = H * (1 * ∫ t in {t : ℝ | |x.2| / 2 ≤ |t|},
              UnforcedLeray.B0191.heatKernel 1 (ν * r) t) := by rw [hI]
        _ ≤ H * (2 * Real.exp (-(|x.2| / 2) ^ 2 / (8 * (ν * r)))) :=
            mul_le_mul_of_nonneg_left (by rw [one_mul]; exact hGauss) hH0
    refine finish (H * (2 * Real.exp (-κ * x.2 ^ 2))) (fun r hr0 hrT => ?_) ?_
    · refine (innerA r hr0).trans ?_
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexpLe r hr0 hrT x)) (by norm_num)) hH0
    · have h1 : (1 : ℝ) ≤ Real.exp (4 * R ^ 2 * κ) :=
        Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg R)) hκ.le)
      have h2 : 0 ≤ 2 * H * T * Real.exp (-κ * x.2 ^ 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH0) hT.le) (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  · -- Case B: `|η| < 2R`, use the trivial bound `‖∫_z G h‖ ≤ H`
    have innerB : ∀ r : ℝ, 0 < r → ‖F r‖ ≤ H := by
      intro r hr
      have hθ : 0 < ν * r := mul_pos hν hr
      simp only [hF]
      calc ‖∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
            h (s - r, (x.1 - z.1, x.2 - z.2))‖
          ≤ ∫ z : ℝ × ℝ, H * UnforcedLeray.B0284.heatKernel2 (ν * r) z :=
            norm_integral_le_of_norm_le
              ((UnforcedLeray.B0284.integrable_heatKernel2 hθ).const_mul H)
              (Filter.Eventually.of_forall fun z => by
                have hG := UnforcedLeray.B0284.heatKernel2_nonneg hθ z
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hG]
                calc UnforcedLeray.B0284.heatKernel2 (ν * r) z * ‖h (s - r, (x.1 - z.1, x.2 - z.2))‖
                    ≤ UnforcedLeray.B0284.heatKernel2 (ν * r) z * H :=
                      mul_le_mul_of_nonneg_left (hHb _) hG
                  _ = H * UnforcedLeray.B0284.heatKernel2 (ν * r) z := mul_comm _ _)
        _ = H := by
            rw [integral_const_mul, UnforcedLeray.B0284.integral_heatKernel2 hθ, mul_one]
    have hlt : |x.2| < 2 * R := not_le.mp hcase
    have hx2 : x.2 ^ 2 ≤ 4 * R ^ 2 := by nlinarith [sq_abs x.2, abs_nonneg x.2]
    have h3 : (1 : ℝ) ≤ Real.exp (4 * R ^ 2 * κ) * Real.exp (-κ * x.2 ^ 2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hx2)])
    have hHT : 0 ≤ H * T := mul_nonneg hH0 hT.le
    refine finish H (fun r hr0 _ => innerB r hr0) ?_
    nlinarith [mul_le_mul_of_nonneg_left h3 hHT,
      mul_nonneg hHT (mul_nonneg (Real.exp_pos (4 * R ^ 2 * κ)).le (Real.exp_pos (-κ * x.2 ^ 2)).le)]

end UnforcedLeray.Short.IIIa
