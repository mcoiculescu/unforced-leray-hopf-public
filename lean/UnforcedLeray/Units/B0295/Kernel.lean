import UnforcedLeray.Units.B0284

/-!
# B0295 `mixed-background:C.22`: continuity of the heat kernel in time and a difference bound

Unit B0295 of `paper/main.tex`, label `mixed-background:C.22`, tex lines 5020–5032; blueprint


The continuity of `T̄f` into `L^p_sp` (tex lines 5029–5030, "the same integral formula …
prove continuity into `L^p_sp`") needs one fact about the cylinder heat semigroup of B0284
(`UnforcedLeray.B0284.heat`, the periodic lift convolved with the planar Gaussian
`heatKernel2 θ`): for `θ, θ₀ > 0`,
`‖e^{θΔ}g - e^{θ₀Δ}g‖_{L^p(dq/c dη)} ≤ κ(θ, θ₀) ‖g‖_{L^p(dq/c dη)}`,
`κ(θ, θ₀) = ∫ |G_θ - G_{θ₀}|` (`eLpNorm_heat_sub_le`), and `κ(θ, θ₀) → 0` as `θ → θ₀`
(`tendsto_kernelDist`, dominated convergence with a Gaussian majorant on `[θ₀/2, 2θ₀]`).
Neither the semigroup law nor translation continuity is used.

Main declarations: `kernelDist`, `measurable_kernelDist`, `kernelDist_le_two`,
`tendsto_kernelDist`, `heat_congr_ae`, `eLpNorm_kernelAbs_le`, `ae_kernelAbs_lt_top`,
`eLpNorm_heat_sub_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real Topology
open scoped NNReal ENNReal

namespace UnforcedLeray.B0295

open UnforcedLeray.B0284
open UnforcedLeray.GaussianVortex (Plane)

/-! ## The `L¹` distance of two heat kernels -/

/-- `κ(θ, θ₀) = ∫ |G_θ(w) - G_{θ₀}(w)| dw`, the `L¹(ℝ²)` distance of two planar heat kernels
(`B0284.heatKernel2`). -/
def kernelDist (θ θ₀ : ℝ) : ℝ≥0∞ := ∫⁻ w : Plane, ‖heatKernel2 θ w - heatKernel2 θ₀ w‖ₑ

theorem measurable_kernelDist : Measurable fun q : ℝ × ℝ => kernelDist q.1 q.2 := by
  have h1 : Measurable fun x : (ℝ × ℝ) × Plane => heatKernel2 x.1.1 x.2 :=
    measurable_heatKernel2.comp (f := fun x : (ℝ × ℝ) × Plane => (x.1.1, x.2)) (by fun_prop)
  have h2 : Measurable fun x : (ℝ × ℝ) × Plane => heatKernel2 x.1.2 x.2 :=
    measurable_heatKernel2.comp (f := fun x : (ℝ × ℝ) × Plane => (x.1.2, x.2)) (by fun_prop)
  exact (h1.sub h2).enorm.lintegral_prod_right'

/-- `κ(θ, θ₀) ≤ 2` for `θ, θ₀ > 0` (both kernels have unit mass). -/
theorem kernelDist_le_two {θ θ₀ : ℝ} (hθ : 0 < θ) (hθ₀ : 0 < θ₀) : kernelDist θ θ₀ ≤ 2 := by
  calc kernelDist θ θ₀
      ≤ ∫⁻ w : Plane, (ENNReal.ofReal (heatKernel2 θ w) + ENNReal.ofReal (heatKernel2 θ₀ w)) := by
        refine lintegral_mono fun w => enorm_sub_le.trans (le_of_eq ?_)
        rw [Real.enorm_of_nonneg (heatKernel2_nonneg hθ w),
          Real.enorm_of_nonneg (heatKernel2_nonneg hθ₀ w)]
    _ = 2 := by
        rw [lintegral_add_left (measurable_heatKernel2_right θ).ennreal_ofReal,
          lintegral_heatKernel2 hθ, lintegral_heatKernel2 hθ₀, one_add_one_eq_two]

/-- The one-dimensional kernel `(4πθ)^{-1/2} e^{-x²/(4θ)}` is continuous in `θ > 0`. -/
theorem continuousAt_heatKernel {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (x : ℝ) :
    ContinuousAt (fun θ => B0191.heatKernel 1 θ x) θ₀ := by
  unfold B0191.heatKernel
  have hs : Real.sqrt (4 * Real.pi * 1 * θ₀) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hd : 4 * 1 * θ₀ ≠ 0 := by positivity
  refine ContinuousAt.mul ?_ ?_
  · exact ((Real.continuous_sqrt.continuousAt).comp
      (by fun_prop : ContinuousAt (fun θ : ℝ => 4 * Real.pi * 1 * θ) θ₀)).inv₀ hs
  · exact Real.continuous_exp.continuousAt.comp (continuousAt_const.div (by fun_prop) hd)

/-- A Gaussian majorant of the one-dimensional kernel for `θ ∈ [θ₀/2, 2θ₀]`. -/
theorem heatKernel_le_of_mem_Icc {θ₀ θ : ℝ} (hθ₀ : 0 < θ₀) (hθ : θ ∈ Icc (θ₀ / 2) (2 * θ₀))
    (x : ℝ) :
    B0191.heatKernel 1 θ x ≤
      (Real.sqrt (2 * Real.pi * θ₀))⁻¹ * Real.exp (-(1 / (8 * θ₀)) * x ^ 2) := by
  have hθpos : 0 < θ := by linarith [hθ.1]
  unfold B0191.heatKernel
  refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (inv_nonneg.2 (Real.sqrt_nonneg _))
  · refine inv_anti₀ (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt ?_)
    nlinarith [hθ.1, Real.pi_pos]
  · refine Real.exp_le_exp.2 ?_
    have h : x ^ 2 / (8 * θ₀) ≤ x ^ 2 / (4 * 1 * θ) :=
      div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by linarith [hθ.2])
    rw [neg_div, show -(1 / (8 * θ₀)) * x ^ 2 = -(x ^ 2 / (8 * θ₀)) by ring]
    linarith

/-- **`L¹` continuity of the heat kernel in time**: `κ(θ, θ₀) → 0` as `θ → θ₀ > 0`. -/
theorem tendsto_kernelDist {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    Tendsto (fun θ => kernelDist θ θ₀) (𝓝 θ₀) (𝓝 0) := by
  set gb : ℝ → ℝ := fun x =>
    (Real.sqrt (2 * Real.pi * θ₀))⁻¹ * Real.exp (-(1 / (8 * θ₀)) * x ^ 2) with hgbdef
  have hgb0 : ∀ x, 0 ≤ gb x := fun x => by rw [hgbdef]; positivity
  have hgb : Integrable gb := (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have hbb : Integrable (fun w : Plane => gb w.1 * gb w.2) := hgb.mul_prod hgb
  set bound : Plane → ℝ≥0∞ := fun w => ‖gb w.1 * gb w.2‖ₑ + ‖heatKernel2 θ₀ w‖ₑ with hbound
  have hfin : ∫⁻ w, bound w ≠ ⊤ := by
    rw [hbound, lintegral_add_left' hbb.1.enorm]
    exact ENNReal.add_ne_top.2 ⟨hbb.2.ne, (integrable_heatKernel2 hθ₀).2.ne⟩
  have hmem : Icc (θ₀ / 2) (2 * θ₀) ∈ 𝓝 θ₀ := Icc_mem_nhds (by linarith) (by linarith)
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := (volume : Measure Plane))
    (l := 𝓝 θ₀) (F := fun θ w => ‖heatKernel2 θ w - heatKernel2 θ₀ w‖ₑ) (f := fun _ => 0)
    bound
    (Eventually.of_forall fun θ =>
      ((measurable_heatKernel2_right θ).sub (measurable_heatKernel2_right θ₀)).enorm)
    (by
      filter_upwards [hmem] with θ hθ
      refine ae_of_all _ fun w => enorm_sub_le.trans (add_le_add_left ?_ _)
      have hθpos : 0 < θ := by linarith [hθ.1]
      rw [Real.enorm_of_nonneg (heatKernel2_nonneg hθpos w),
        Real.enorm_of_nonneg (mul_nonneg (hgb0 _) (hgb0 _))]
      refine ENNReal.ofReal_le_ofReal ?_
      exact mul_le_mul (heatKernel_le_of_mem_Icc hθ₀ hθ w.1) (heatKernel_le_of_mem_Icc hθ₀ hθ w.2)
        (B0191.heatKernel_pos one_pos hθpos _).le (hgb0 _))
    hfin
    (ae_of_all _ fun w => by
      have hc : ContinuousAt (fun θ => heatKernel2 θ w) θ₀ :=
        (continuousAt_heatKernel hθ₀ w.1).mul (continuousAt_heatKernel hθ₀ w.2)
      have := (hc.tendsto.sub_const (heatKernel2 θ₀ w)).enorm
      simpa using this)
  simpa [kernelDist] using h

/-! ## The heat difference bound on the cylinder -/

/-- `e^{θΔ}g`, `θ > 0`, only depends on the almost-everywhere class of `g`. -/
theorem heat_congr_ae {θ : ℝ} (hθ : 0 < θ) {g g' : Plane → Plane} (h : g =ᵐ[volume] g') :
    heat θ g = heat θ g' := by
  funext z
  rw [heat_apply_of_pos hθ, heat_apply_of_pos hθ]
  refine integral_congr_ae ?_
  have h' := (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure Plane) z).ae h
  filter_upwards [h'] with w hw
  rw [hw]

/-- Minkowski with a general kernel on the cylinder: for measurable `k ≥ 0` and periodic,
almost everywhere strongly measurable `g`,
`‖∫ k(w) |g(·-w)| dw‖_{L^p(dq/c dη)} ≤ (∫ k) ‖g‖_{L^p(dq/c dη)}`, `1 ≤ p < ∞`
(the proof of `B0284.eLpNorm_heatAbs_le` with `k` in place of the heat kernel). -/
theorem eLpNorm_kernelAbs_le {c : ℝ} (hc : 0 < c) {k : Plane → ℝ≥0∞} (hk : Measurable k)
    (hk' : ∀ w, k w ≠ ⊤) {g : Plane → Plane} (hper : IsQPeriodic c g)
    (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (fun z => ∫⁻ w, k w * ‖g (z - w)‖ₑ) p (cellMeasure c) ≤
      (∫⁻ w, k w) * eLpNorm g p (cellMeasure c) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hsub : AEStronglyMeasurable (fun q : Plane × Plane => g (q.1 - q.2))
      ((volume : Measure Plane).prod volume) :=
    hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure Plane) volume)
  have hF : AEMeasurable (Function.uncurry fun z w => k w * ‖g (z - w)‖ₑ)
      ((cellMeasure c).prod volume) := by
    have h1 : AEMeasurable (fun q : Plane × Plane => ‖g (q.1 - q.2)‖ₑ)
        ((cellMeasure c).prod volume) :=
      (hsub.enorm).mono_ac ((cellMeasure_ac c).prod Measure.AbsolutelyContinuous.rfl)
    exact (hk.comp measurable_snd).aemeasurable.mul h1
  calc eLpNorm (fun z => ∫⁻ w, k w * ‖g (z - w)‖ₑ) p (cellMeasure c)
      ≤ ∫⁻ w, eLpNorm (fun z => k w * ‖g (z - w)‖ₑ) p (cellMeasure c) :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hF hp hp'
    _ = ∫⁻ w, k w * eLpNorm g p (cellMeasure c) := by
        refine lintegral_congr fun w => ?_
        rw [eLpNorm_const_mul_ennreal (hk' w) _ hp0 hp', eLpNorm_enorm,
          eLpNorm_cellMeasure_sub hc hper hg hp0 hp' w]
    _ = (∫⁻ w, k w) * eLpNorm g p (cellMeasure c) := lintegral_mul_const _ hk

/-- A `[0,∞]`-valued function with finite `L^p` norm, `0 < p < ∞`, is finite almost
everywhere. -/
theorem ae_lt_top_of_eLpNorm_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (h : eLpNorm f p μ ≠ ⊤) : ∀ᵐ x ∂μ, f x < ⊤ := by
  have h1 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp h.lt_top
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h2 := ae_lt_top' (hf.enorm.pow_const p.toReal) h1.ne
  filter_upwards [h2] with x hx
  rw [enorm_eq_self] at hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hpr).1 hx

/-- The absolute kernel integral of a periodic `L^p` field against a finite-mass kernel is
finite at almost every point of the cell. -/
theorem ae_kernelAbs_lt_top {c : ℝ} (hc : 0 < c) {k : Plane → ℝ≥0∞} (hk : Measurable k)
    (hk' : ∀ w, k w ≠ ⊤) (hkfin : ∫⁻ w, k w ≠ ⊤) {g : Plane → Plane} (hper : IsQPeriodic c g)
    (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hfin : eLpNorm g p (cellMeasure c) ≠ ⊤) :
    ∀ᵐ z ∂(cellMeasure c), ∫⁻ w, k w * ‖g (z - w)‖ₑ < ⊤ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hsub : AEStronglyMeasurable (fun q : Plane × Plane => g (q.1 - q.2))
      ((volume : Measure Plane).prod volume) :=
    hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure Plane) volume)
  have hF : AEMeasurable (fun q : Plane × Plane => k q.2 * ‖g (q.1 - q.2)‖ₑ)
      ((cellMeasure c).prod volume) := by
    have h1 : AEMeasurable (fun q : Plane × Plane => ‖g (q.1 - q.2)‖ₑ)
        ((cellMeasure c).prod volume) :=
      (hsub.enorm).mono_ac ((cellMeasure_ac c).prod Measure.AbsolutelyContinuous.rfl)
    exact (hk.comp measurable_snd).aemeasurable.mul h1
  refine ae_lt_top_of_eLpNorm_ne_top hF.lintegral_prod_right' hp0 hp' ?_
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hkfin hfin)
    (eLpNorm_kernelAbs_le hc hk hk' hper hg hp hp')

/-- **Heat difference bound**: for `θ, θ₀ > 0`, `1 ≤ p < ∞` and a periodic, almost everywhere
strongly measurable `g ∈ L^p(dq/c dη)`,
`‖e^{θΔ}g - e^{θ₀Δ}g‖_{L^p(dq/c dη)} ≤ κ(θ, θ₀) ‖g‖_{L^p(dq/c dη)}`. -/
theorem eLpNorm_heat_sub_le {c θ θ₀ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθ₀ : 0 < θ₀)
    {g : Plane → Plane} (hper : IsQPeriodic c g) (hg : AEStronglyMeasurable g volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hfin : eLpNorm g p (cellMeasure c) ≠ ⊤) :
    eLpNorm (heat θ g - heat θ₀ g) p (cellMeasure c) ≤
      kernelDist θ θ₀ * eLpNorm g p (cellMeasure c) := by
  have hK : ∀ {θ' : ℝ}, 0 < θ' → ∀ᵐ z ∂(cellMeasure c),
      ∫⁻ w, ENNReal.ofReal (heatKernel2 θ' w) * ‖g (z - w)‖ₑ < ⊤ := by
    intro θ' hθ'
    refine ae_kernelAbs_lt_top hc (measurable_heatKernel2_right θ').ennreal_ofReal
      (fun _ => ENNReal.ofReal_ne_top) ?_ hper hg hp hp' hfin
    rw [lintegral_heatKernel2 hθ']
    exact ENNReal.one_ne_top
  have hint : ∀ {θ' : ℝ}, 0 < θ' → ∀ z,
      ∫⁻ w, ENNReal.ofReal (heatKernel2 θ' w) * ‖g (z - w)‖ₑ < ⊤ →
        Integrable (fun w => heatKernel2 θ' w • g (z - w)) := by
    intro θ' hθ' z h
    have hgz : AEStronglyMeasurable (fun w => g (z - w)) volume :=
      hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure Plane) z)
    refine ⟨(measurable_heatKernel2_right θ').aestronglyMeasurable.smul hgz, ?_⟩
    show ∫⁻ w, ‖heatKernel2 θ' w • g (z - w)‖ₑ < ⊤
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun w => ?_)) h
    rw [enorm_smul, Real.enorm_of_nonneg (heatKernel2_nonneg hθ' w)]
  have hkd : Measurable fun w => ‖heatKernel2 θ w - heatKernel2 θ₀ w‖ₑ :=
    ((measurable_heatKernel2_right θ).sub (measurable_heatKernel2_right θ₀)).enorm
  calc eLpNorm (heat θ g - heat θ₀ g) p (cellMeasure c)
      ≤ eLpNorm (fun z => ∫⁻ w, ‖heatKernel2 θ w - heatKernel2 θ₀ w‖ₑ * ‖g (z - w)‖ₑ) p
          (cellMeasure c) := by
        refine eLpNorm_mono_enorm_ae ?_
        filter_upwards [hK hθ, hK hθ₀] with z h1 h2
        rw [enorm_eq_self, Pi.sub_apply, heat_apply_of_pos hθ, heat_apply_of_pos hθ₀,
          ← integral_sub (hint hθ z h1) (hint hθ₀ z h2)]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr fun w => ?_
        rw [← sub_smul, enorm_smul]
    _ ≤ kernelDist θ θ₀ * eLpNorm g p (cellMeasure c) :=
        eLpNorm_kernelAbs_le hc hkd (fun _ => enorm_ne_top) hper hg hp hp'

end UnforcedLeray.B0295
