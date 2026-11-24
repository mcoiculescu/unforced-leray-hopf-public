import UnforcedLeray.Short.PartIIa.Sub.F05

/-!


Source of record: `the November 2 reference manuscript`, lines 1445-1450
("uniqueness does not require an a priori graph"; the adjoint resolvent has its derivatives in
`Y_{r'}`). The elementary analysis is the statement `SliceContOfDecay`: a continuous `ℂ³`-valued
`G` with `‖G(τ, y)‖ ≤ C (1 + ‖y‖)^{-s}` and `3 < s q` has every slice in `L^q(ℝ³)` and is slice
continuous in `τ`.

Proof. The weight `H(y) = (1 + ‖y‖)^{-s p}`, `p = q.toReal`, is integrable on `ℝ³` by
`integrable_one_add_norm`, since `finrank ℝ ℝ³ = 3 < s p`. Pointwise, `‖x‖ ≤ a (1+‖y‖)^{-s}`
gives `‖x‖ₑ^p ≤ ofReal (a^p H(y))`. Each slice is then in `L^q` by finiteness of the
lintegral. For continuity at `τ₀`, the `L^q` distance of slices is
`(∫⁻ ‖G(τ,·) - G(τ₀,·)‖ₑ^p)^{1/p}`, and the integrand tends to `0` pointwise and is dominated
by `ofReal ((2|C|)^p H(y))`, so dominated convergence (filter form) gives the limit `0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace

/-- **Leaf `PartII-a:F05/2` (slice continuity from polynomial decay).** -/
theorem sliceContOfDecay : SliceContOfDecay := by
  intro q hfact hqtop s C hs G hG hb
  have hq1 : (1 : ℝ≥0∞) ≤ q := hfact.out
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq1).ne'
  have hp1 : (1 : ℝ) ≤ q.toReal := by
    have h := ENNReal.toReal_mono hqtop hq1
    simpa using h
  have hppos : 0 < q.toReal := by linarith
  set p : ℝ := q.toReal with hpdef
  -- slices of `G` are continuous in `y`, and `τ ↦ G(τ, y)` is continuous
  have hsl : ∀ τ : ℝ, Continuous fun y : Space => G (τ, y) := fun τ =>
    hG.comp (Continuous.prodMk continuous_const continuous_id)
  have hsτ : ∀ y : Space, Continuous fun τ : ℝ => G (τ, y) := fun y =>
    hG.comp (Continuous.prodMk continuous_id continuous_const)
  -- the weight
  have hH : ∀ y : Space, ((1 + ‖y‖) ^ (-s)) ^ p = (1 + ‖y‖) ^ (-(s * p)) := fun y => by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖y‖), neg_mul]
  have hfr : (Module.finrank ℝ Space : ℝ) = 3 := by simp
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(s * p))) volume :=
    integrable_one_add_norm (by rw [hfr]; exact hs)
  have hfin : ∀ c : ℝ, ∫⁻ y, ENNReal.ofReal (c * (1 + ‖y‖) ^ (-(s * p))) ≠ ⊤ :=
    fun c => ((hint.const_mul c).lintegral_lt_top).ne
  -- pointwise bound in `ℝ≥0∞`
  have hpt : ∀ (a : ℝ), 0 ≤ a → ∀ (x : CVec3) (y : Space), ‖x‖ ≤ a * (1 + ‖y‖) ^ (-s) →
      ‖x‖ₑ ^ p ≤ ENNReal.ofReal (a ^ p * (1 + ‖y‖) ^ (-(s * p))) := by
    intro a ha x y hx
    have hb0 : 0 ≤ a * (1 + ‖y‖) ^ (-s) := le_trans (norm_nonneg x) hx
    calc ‖x‖ₑ ^ p = (ENNReal.ofReal ‖x‖) ^ p := by rw [ofReal_norm]
      _ ≤ (ENNReal.ofReal (a * (1 + ‖y‖) ^ (-s))) ^ p :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx) hppos.le
      _ = ENNReal.ofReal ((a * (1 + ‖y‖) ^ (-s)) ^ p) :=
          ENNReal.ofReal_rpow_of_nonneg hb0 hppos.le
      _ = ENNReal.ofReal (a ^ p * (1 + ‖y‖) ^ (-(s * p))) := by
          rw [Real.mul_rpow ha (by positivity), hH y]
  have hb' : ∀ (τ : ℝ) (y : Space), ‖G (τ, y)‖ ≤ |C| * (1 + ‖y‖) ^ (-s) := fun τ y =>
    (hb τ y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  -- every slice is in `L^q`
  have hmem : ∀ τ : ℝ, MemLp (fun y : Space => G (τ, y)) q volume := by
    intro τ
    refine ⟨(hsl τ).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hqtop]
    exact lt_of_le_of_lt
      (lintegral_mono fun y => hpt _ (abs_nonneg C) (G (τ, y)) y (hb' τ y))
      (hfin _).lt_top
  refine ⟨hmem, ?_⟩
  -- continuity of the slice map at `τ₀`
  refine continuous_iff_continuousAt.2 fun τ0 => ?_
  unfold ContinuousAt
  refine (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun τ => MemLp.toLp _ (hmem τ))
    (fun y => G (τ0, y)) (hmem τ0)).2 ?_
  -- the `L^q` distance is a power of a lintegral
  have hrep : ∀ τ : ℝ, eLpNorm (⇑(MemLp.toLp _ (hmem τ)) - fun y => G (τ0, y)) q volume =
      (∫⁻ y, ‖G (τ, y) - G (τ0, y)‖ₑ ^ p) ^ (1 / p) := by
    intro τ
    calc eLpNorm (⇑(MemLp.toLp _ (hmem τ)) - fun y => G (τ0, y)) q volume
        = eLpNorm (fun y => G (τ, y) - G (τ0, y)) q volume :=
          eLpNorm_congr_ae ((MemLp.coeFn_toLp (hmem τ)).sub Filter.EventuallyEq.rfl)
      _ = (∫⁻ y, ‖G (τ, y) - G (τ0, y)‖ₑ ^ p) ^ (1 / p) :=
          eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop
  -- uniform domination of the difference
  have hdom : ∀ (τ : ℝ) (y : Space),
      ‖G (τ, y) - G (τ0, y)‖ₑ ^ p ≤ ENNReal.ofReal ((2 * |C|) ^ p * (1 + ‖y‖) ^ (-(s * p))) := by
    intro τ y
    apply hpt (2 * |C|) (by positivity) _ y
    have e : (2 * |C|) * (1 + ‖y‖) ^ (-s) = |C| * (1 + ‖y‖) ^ (-s) + |C| * (1 + ‖y‖) ^ (-s) := by
      ring
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (hb' τ y) (hb' τ0 y))
  -- pointwise convergence of the integrand as `τ → τ₀`
  have hlim : ∀ y : Space, Tendsto (fun τ : ℝ => ‖G (τ, y) - G (τ0, y)‖ₑ ^ p) (𝓝 τ0) (𝓝 0) := by
    intro y
    have hc : Continuous fun τ : ℝ => ‖G (τ, y) - G (τ0, y)‖ₑ ^ p :=
      (ENNReal.continuous_rpow_const (y := p)).comp (continuous_enorm.comp ((hsτ y).sub continuous_const))
    have h2 : Tendsto (fun τ : ℝ => ‖G (τ, y) - G (τ0, y)‖ₑ ^ p) (𝓝 τ0)
        (𝓝 ((‖G (τ0, y) - G (τ0, y)‖ₑ) ^ p)) := hc.tendsto τ0
    rw [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hppos] at h2
    exact h2
  -- dominated convergence of the integrals, along the filter `𝓝 τ₀`
  have hlint : Tendsto (fun τ : ℝ => ∫⁻ y, ‖G (τ, y) - G (τ0, y)‖ₑ ^ p) (𝓝 τ0) (𝓝 0) := by
    have key := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 τ0)
      (F := fun (τ : ℝ) (y : Space) => ‖G (τ, y) - G (τ0, y)‖ₑ ^ p)
      (f := fun _ : Space => (0 : ℝ≥0∞))
      (fun y => ENNReal.ofReal ((2 * |C|) ^ p * (1 + ‖y‖) ^ (-(s * p))))
      (Filter.Eventually.of_forall fun τ =>
        (ENNReal.continuous_rpow_const (y := p)).comp
          (continuous_enorm.comp (((hsl τ).sub (hsl τ0)))) |>.measurable)
      (Filter.Eventually.of_forall fun τ => ae_of_all _ fun y => hdom τ y)
      (hfin _)
      (ae_of_all _ fun y => hlim y)
    simpa only [lintegral_zero] using key
  -- conclude: the `L^q` distance tends to `0`
  refine Filter.Tendsto.congr (fun τ => (hrep τ).symm) ?_
  have h1 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto (0 : ℝ≥0∞)).comp hlint
  rw [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hppos)] at h1
  exact h1

end UnforcedLeray.Short.PartIIa
