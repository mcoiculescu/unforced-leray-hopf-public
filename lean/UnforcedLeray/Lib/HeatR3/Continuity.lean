import UnforcedLeray.Lib.HeatR3.LpOp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Strong continuity of the generic heat semigroup on `L^p`, `p < ∞` (INF04 T3)


`heatLp_continuousOn` (decision D17). Adapted from the R³ draft

`lintegral_kernel_mul_eq`, `tendsto_flow_sub`), with Mathlib's `L^p` translation continuity
(`Continuous.compMeasurePreservingLp`) in place of the R³-specific approximation argument.

Proof: by Minkowski, `‖e^{θΔ}u - u‖_p ≤ ∫ G_θ(y) ‖τ_{ιy}u - u‖_p dy`; the dilation `y = √θ w`
turns this into `∫ G_1(w) ω(√θ w) dw` with `ω(y) = ‖τ_{ιy}u - u‖_p ≤ 2‖u‖_p` continuous and
`ω(0) = 0`, so it tends to `0` by dominated convergence. Continuity at `θ₀ > 0` follows from the
semigroup law and the contraction property.

Hypotheses on `(G, μ)` beyond `ConvOp`: `μ` inner regular for sets of finite measure and locally
finite (true for Haar measures on `ℝⁿ`, `ℝ × ℝ`, `AddCircle c × ℝ`), `G` an `R₁` space (true for
topological groups that are regular).

Main results: `translateLp`, `tendsto_translateLp`, `enorm_heatLp_sub_le`,
`tendsto_heatLp_sub`, `heatLp_continuousOn`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ} {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsAddRightInvariant]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)]

/-- The translation `x ↦ x - ι y` as a continuous map. -/
def shiftMap (ι : Euc d →+ G) (hι : Continuous ι) (y : Euc d) : C(G, G) :=
  ⟨fun x => x - ι y, continuous_id.sub continuous_const⟩

theorem continuous_shiftMap (ι : Euc d →+ G) (hι : Continuous ι) :
    Continuous (shiftMap ι hι) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_snd.sub (hι.comp continuous_fst))

/-- The translation `τ_{ιy}u = u(· - ι y)` on `Lp E p μ`. -/
def translateLp (ι : Euc d →+ G) (hι : Continuous ι) (y : Euc d) (u : Lp E p μ) : Lp E p μ :=
  Lp.compMeasurePreserving (shiftMap ι hι y) (measurePreserving_sub_right μ (ι y)) u

theorem coeFn_translateLp (ι : Euc d →+ G) (hι : Continuous ι) (y : Euc d) (u : Lp E p μ) :
    (translateLp ι hι y u : G → E) =ᵐ[μ] fun x => u (x - ι y) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem translateLp_zero (ι : Euc d →+ G) (hι : Continuous ι) (u : Lp E p μ) :
    translateLp ι hι 0 u = u := by
  refine Lp.ext ((coeFn_translateLp ι hι 0 u).trans ?_)
  filter_upwards with x
  rw [map_zero, sub_zero]

variable [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G]

/-- **`L^p` translation continuity**, `p < ∞`: `τ_{ιy}u → u` as `y → 0`. -/
theorem tendsto_translateLp (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞)
    (u : Lp E p μ) : Tendsto (fun y => translateLp ι hι y u) (𝓝 0) (𝓝 u) := by
  have h := Continuous.compMeasurePreservingLp (μ := μ) (ν := μ) (E := E) (p := p)
    (f := fun _ : Euc d => u) (g := shiftMap ι hι) continuous_const (continuous_shiftMap ι hι)
    (fun y => measurePreserving_sub_right μ (ι y)) hp
  have h0 := h.tendsto 0
  rwa [show Lp.compMeasurePreserving (shiftMap ι hι 0) (measurePreserving_sub_right μ (ι 0)) u
    = u from translateLp_zero ι hι u] at h0

omit [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G] in
/-- The translation modulus as an `eLpNorm`. -/
theorem enorm_translateLp_sub (ι : Euc d →+ G) (hι : Continuous ι) (y : Euc d)
    (u : Lp E p μ) :
    ‖translateLp ι hι y u - u‖ₑ = eLpNorm (fun x => u (x - ι y) - u x) p μ := by
  rw [Lp.enorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (translateLp ι hι y u) u, coeFn_translateLp ι hι y u]
    with x h1 h2
  rw [h1, Pi.sub_apply, h2]

omit [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G] in
theorem enorm_translateLp_sub_le (ι : Euc d →+ G) (hι : Continuous ι) (y : Euc d)
    (u : Lp E p μ) : ‖translateLp ι hι y u - u‖ₑ ≤ 2 * ‖u‖ₑ := by
  calc ‖translateLp ι hι y u - u‖ₑ ≤ ‖translateLp ι hι y u‖ₑ + ‖u‖ₑ := enorm_sub_le
    _ = 2 * ‖u‖ₑ := by
        rw [two_mul]
        congr 1
        rw [Lp.enorm_def, Lp.enorm_def]
        exact (eLpNorm_congr_ae (coeFn_translateLp ι hι y u)).trans
          (eLpNorm_comp_measurePreserving (f := fun x => x - ι y) (Lp.aestronglyMeasurable u)
            (measurePreserving_sub_right μ (ι y)))

omit [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G] in
/-- **Minkowski bound of the heat increment** (adapted from B0418 `eLpNorm_flow_sub_le`):
`‖e^{θΔ}u - u‖_p ≤ ∫ G_θ(y) ‖τ_{ιy}u - u‖_p dy`, `θ > 0`, `p < ∞`. -/
theorem enorm_heatLp_sub_le (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞) {θ : ℝ}
    (hθ : 0 < θ) (u : Lp E p μ) :
    ‖heatLp ι hι θ u - u‖ₑ ≤
      ∫⁻ y : Euc d, ENNReal.ofReal (gaussKernel d θ y) * ‖translateLp ι hι y u - u‖ₑ := by
  have hrep : (heatLp ι hι θ u - u : Lp E p μ) =ᵐ[μ]
      fun x => ∫ y : Euc d, gaussKernel d θ y • (u (x - ι y) - u x) := by
    filter_upwards [Lp.coeFn_sub (heatLp ι hι θ u) u, heatLp_rep ι hι hθ u,
      ae_integrable_heatIntegrand ι hι.measurable hθ hp1.out (Lp.memLp u)] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, heatConv]
    simp only [smul_sub]
    rw [integral_sub h3 ((Gaussian.integrable_gaussKernel hθ).smul_const (u x)),
      integral_smul_const, Gaussian.integral_gaussKernel hθ, one_smul]
  rw [Lp.enorm_def, eLpNorm_congr_ae hrep]
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun x y => gaussKernel d θ y • (u (x - ι y) - u x)) (μ.prod volume) :=
    ((Gaussian.continuous_gaussKernel θ).comp continuous_snd).aestronglyMeasurable.smul
      ((aestronglyMeasurable_heatShift ι hι.measurable (Lp.aestronglyMeasurable u)).sub
        (Lp.aestronglyMeasurable u).comp_fst)
  refine (NonUniqueEuler.Conv.eLpNorm_integral_le hjoint hp1.out hp).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  change eLpNorm (gaussKernel d θ y • fun x => u (x - ι y) - u x) p μ = _
  rw [eLpNorm_const_smul, enorm_translateLp_sub, enorm_gaussKernel hθ]

omit [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G] in
/-- The dilation `y = √θ w` in the Minkowski bound (adapted from B0418
`lintegral_kernel_mul_eq`). -/
theorem lintegral_gaussKernel_mul_eq {θ : ℝ} (hθ : 0 < θ) (ω : Euc d → ℝ≥0∞) :
    ∫⁻ y : Euc d, ENNReal.ofReal (gaussKernel d θ y) * ω y =
      ∫⁻ w : Euc d, ENNReal.ofReal (gaussKernel d 1 w) * ω (Real.sqrt θ • w) := by
  set c := Real.sqrt θ with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr hθ
  have hc2 : c ^ 2 * 1 = θ := by rw [mul_one]; exact Real.sq_sqrt hθ.le
  let F : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (gaussKernel d θ y) * ω y
  have hemb : MeasurableEmbedding (fun w : Euc d => c • w) :=
    (Homeomorph.smulOfNeZero c hc0.ne').measurableEmbedding
  have hmap := hemb.lintegral_map (μ := (volume : Measure (Euc d))) F
  rw [Measure.map_addHaar_smul volume hc0.ne', lintegral_smul_measure,
    Gaussian.finrank_euc] at hmap
  have hF : (fun w : Euc d => F (c • w)) = fun w =>
      ENNReal.ofReal |(c ^ d)⁻¹| * (ENNReal.ofReal (gaussKernel d 1 w) * ω (c • w)) := by
    funext w
    simp only [F]
    rw [← hc2, Gaussian.gaussKernel_scale hc0 one_pos, abs_of_pos (by positivity),
      Real.rpow_neg hc0.le, Real.rpow_natCast, ENNReal.ofReal_mul (by positivity), mul_assoc]
  rw [hF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hmap
  have h0 : ENNReal.ofReal |(c ^ d)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  exact (ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top).mp (by simpa [smul_eq_mul] using hmap)

theorem lintegral_ofReal_gaussKernel_one : ∫⁻ w : Euc d, ENNReal.ofReal (gaussKernel d 1 w) = 1 := by
  simpa only [enorm_gaussKernel one_pos] using lintegral_enorm_gaussKernel (d := d) one_pos

/-- **Strong continuity at `θ = 0`**, `p < ∞`: `‖e^{θΔ}u - u‖_p → 0` as `θ → 0`. -/
theorem tendsto_heatLp_sub (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞)
    (u : Lp E p μ) : Tendsto (fun θ => ‖heatLp ι hι θ u - u‖ₑ) (𝓝 0) (𝓝 0) := by
  set ω : Euc d → ℝ≥0∞ := fun y => ‖translateLp ι hι y u - u‖ₑ with hω
  have hωc : Continuous ω := by
    have hcont : Continuous fun y => translateLp ι hι y u :=
      Continuous.compMeasurePreservingLp (μ := μ) (ν := μ) (E := E) (p := p)
        (f := fun _ : Euc d => u) (g := shiftMap ι hι) continuous_const
        (continuous_shiftMap ι hι) (fun y => measurePreserving_sub_right μ (ι y)) hp
    exact (hcont.sub continuous_const).enorm
  have hω0 : Tendsto ω (𝓝 0) (𝓝 0) := by
    have h := ((tendsto_translateLp ι hι hp u).sub_const u).enorm
    simpa [hω] using h
  let Φ : ℝ → ℝ≥0∞ := fun c => ∫⁻ w, ENNReal.ofReal (gaussKernel d 1 w) * ω (c • w)
  have hΦ : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have hlim := tendsto_lintegral_filter_of_dominated_convergence
      (μ := (volume : Measure (Euc d))) (l := 𝓝 (0 : ℝ))
      (F := fun c w => ENNReal.ofReal (gaussKernel d 1 w) * ω (c • w))
      (f := fun _ => 0)
      (fun w => ENNReal.ofReal (gaussKernel d 1 w) * (2 * ‖u‖ₑ))
      (Eventually.of_forall fun c =>
        (ENNReal.measurable_ofReal.comp (Gaussian.continuous_gaussKernel 1).measurable).mul
          (hωc.measurable.comp (measurable_const_smul c)))
      (Eventually.of_forall fun c => Eventually.of_forall fun w => by
        gcongr; exact enorm_translateLp_sub_le ι hι _ u)
      (by
        rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top),
          lintegral_ofReal_gaussKernel_one, one_mul]
        exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top)
      (Eventually.of_forall fun w => by
        have h1 : Tendsto (fun c : ℝ => c • w) (𝓝 0) (𝓝 0) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const w
        have h3 := ENNReal.Tendsto.const_mul (hω0.comp h1) (Or.inr ENNReal.ofReal_ne_top)
          (a := ENNReal.ofReal (gaussKernel d 1 w))
        rw [mul_zero] at h3
        exact h3)
    simpa [Φ] using hlim
  have hsq : Tendsto (fun θ : ℝ => Real.sqrt θ) (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_sqrt.tendsto (0 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hΦ.comp hsq)
    (fun _ => zero_le) (fun θ => ?_)
  by_cases hθ : 0 < θ
  · exact (enorm_heatLp_sub_le ι hι hp hθ u).trans_eq (lintegral_gaussKernel_mul_eq hθ ω)
  · rw [heatLp_of_nonpos ι hι (not_lt.mp hθ), ContinuousLinearMap.id_apply, sub_self,
      enorm_zero]
    exact zero_le

omit [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G] in
/-- `‖e^{θΔ}u - e^{θ₀Δ}u‖ ≤ ‖e^{|θ-θ₀|Δ}u - u‖` for `θ, θ₀ ≥ 0` (semigroup law + contraction). -/
theorem enorm_heatLp_sub_heatLp_le (ι : Euc d →+ G) (hι : Continuous ι) {θ θ₀ : ℝ}
    (hθ : 0 ≤ θ) (hθ₀ : 0 ≤ θ₀) (u : Lp E p μ) :
    ‖heatLp ι hι θ u - heatLp ι hι θ₀ u‖ₑ ≤ ‖heatLp ι hι |θ - θ₀| u - u‖ₑ := by
  have hc : ∀ (s : ℝ) (v : Lp E p μ), ‖heatLp ι hι s v‖ₑ ≤ ‖v‖ₑ := fun s v => by
    simpa only [enorm_eq_nnnorm, ENNReal.coe_le_coe] using
      (show ‖heatLp ι hι s v‖₊ ≤ ‖v‖₊ from norm_heatLp_apply_le ι hι s v)
  rcases le_total θ₀ θ with h | h
  · have hs : θ = θ₀ + (θ - θ₀) := by ring
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    conv_lhs => rw [hs, heatLp_add ι hι hθ₀ (sub_nonneg.mpr h), ContinuousLinearMap.comp_apply,
      ← map_sub]
    exact hc _ _
  · have hs : θ₀ = θ + (θ₀ - θ) := by ring
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    conv_lhs => rw [hs, heatLp_add ι hι hθ (sub_nonneg.mpr h), ContinuousLinearMap.comp_apply,
      ← map_sub]
    refine (hc _ _).trans (le_of_eq ?_)
    rw [← enorm_neg, neg_sub]

/-- **INF04 T3 `heatLp_continuousOn`** (D17). For `1 ≤ p < ∞`, `θ ↦ e^{θΔ}u` is continuous on
`[0, ∞)` in `L^p(μ)` (tex 7416–7425, B0418: strong continuity). -/
theorem heatLp_continuousOn (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞)
    (u : Lp E p μ) : ContinuousOn (fun θ => heatLp ι hι θ u) (Ici 0) := by
  intro θ₀ hθ₀
  rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
  have h0 := tendsto_heatLp_sub ι hι hp u
  have habs : Tendsto (fun θ : ℝ => |θ - θ₀|) (𝓝[Ici 0] θ₀) (𝓝 0) := by
    have : Tendsto (fun θ : ℝ => |θ - θ₀|) (𝓝 θ₀) (𝓝 |θ₀ - θ₀|) :=
      ((continuous_id.sub continuous_const).abs).tendsto θ₀
    rw [sub_self, abs_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h0.comp habs)
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  rw [edist_eq_enorm_sub]
  exact enorm_heatLp_sub_heatLp_le ι hι hθ hθ₀ u

end UnforcedLeray.Heat
