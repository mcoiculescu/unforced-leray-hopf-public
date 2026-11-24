import UnforcedLeray.Lib.Gaussian.Kernel
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# The generic Gaussian heat operator on a translation-invariant group (INF04 T3, bypass BP1)


built under decision D17 of `scoping/README.md` §3 (`heatConv`/`heatLp` are frozen interfaces).

Bypass BP1: one heat operator for every geometry. `G` is an abelian topological group with a
translation-invariant measure `μ`, and `ι : ℝ^d →+ G` is a measurable homomorphism. Then

`heatConv ι θ u x = ∫_{ℝ^d} G_θ(y) u(x - ι y) dy`,   `G_θ = gaussKernel d θ` (heat time `θ`),

is `e^{θΔ}u` on `ℝ³` (`ι = id`, tex 7411–7427, units B0418–B0420), on `ℝ` (`d = 1`, tex
2394–2404, B0158) and, by decision D1, on periodic functions on the plane (`G = ℝ × ℝ`, tex
4961–4969, B0672). Every statement assumes `0 < θ`: for `θ ≤ 0` the formula is a Lean junk
value (`rpow` of a nonpositive base) and nothing is claimed about it. Where the integral
diverges, `heatConv` is the Bochner junk value `0`; the statements below say where it converges.

Main results (this file):
* `heatAbs` (the `[0,∞]`-valued majorant) and `enorm_heatConv_le`;
* `eLpNorm_heatAbs_le`, `eLpNorm_heatConv_le`: `‖e^{θΔ}u‖_{L^p(μ)} ≤ ‖u‖_{L^p(μ)}` for
  `1 ≤ p ≤ ∞` (Minkowski; no integrability hypothesis);
* `ae_integrable_heatIntegrand`: for `u ∈ L^p`, `1 ≤ p ≤ ∞`, the defining integral converges
  absolutely for a.e. `x`;
* `heatConv_congr_ae`, `heatConv_add_ae`, `heatConv_smul`: linearity;
* `heatConv_add_time_of_lt_top`, `heatConv_add_time`: `e^{(s+t)Δ} = e^{sΔ}e^{tΔ}`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

section Generic

variable {d : ℕ} {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **INF04 T3 `heatConv`** (D17 interface). The Gaussian average of `u` over the translations
`ι y`: `heatConv ι θ u x = ∫ G_θ(y) • u(x - ι y) dy`. It is `e^{θΔ}u` for `θ > 0`
(tex 7411–7427, B0418–B0420). -/
def heatConv (ι : Euc d →+ G) (θ : ℝ) (u : G → E) (x : G) : E :=
  ∫ y : Euc d, gaussKernel d θ y • u (x - ι y)

/-- The `[0,∞]`-valued majorant `∫⁻ |G_θ(y)| ‖u(x - ι y)‖ dy` of `heatConv`. -/
def heatAbs (ι : Euc d →+ G) (θ : ℝ) (u : G → E) (x : G) : ℝ≥0∞ :=
  ∫⁻ y : Euc d, ‖gaussKernel d θ y‖ₑ * ‖u (x - ι y)‖ₑ

theorem enorm_heatConv_le (ι : Euc d →+ G) (θ : ℝ) (u : G → E) (x : G) :
    ‖heatConv ι θ u x‖ₑ ≤ heatAbs ι θ u x := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  simp only [heatAbs, enorm_smul]

theorem enorm_gaussKernel {θ : ℝ} (hθ : 0 < θ) (y : Euc d) :
    ‖gaussKernel d θ y‖ₑ = ENNReal.ofReal (gaussKernel d θ y) :=
  Real.enorm_of_nonneg (Gaussian.gaussKernel_nonneg hθ y)

theorem lintegral_enorm_gaussKernel {θ : ℝ} (hθ : 0 < θ) :
    ∫⁻ y : Euc d, ‖gaussKernel d θ y‖ₑ = 1 := by
  simp_rw [enorm_gaussKernel hθ]
  rw [← ofReal_integral_eq_lintegral_ofReal (Gaussian.integrable_gaussKernel hθ)
    (Eventually.of_forall fun y => Gaussian.gaussKernel_nonneg hθ y),
    Gaussian.integral_gaussKernel hθ, ENNReal.ofReal_one]

theorem heatConv_smul (ι : Euc d →+ G) (θ c : ℝ) (u : G → E) :
    heatConv ι θ (c • u) = c • heatConv ι θ u := by
  funext x
  simp only [heatConv, Pi.smul_apply, smul_comm (gaussKernel d θ _) c]
  exact integral_smul c _

theorem heatConv_neg (ι : Euc d →+ G) (θ : ℝ) (u : G → E) :
    heatConv ι θ (-u) = -heatConv ι θ u := by
  funext x
  simp only [heatConv, Pi.neg_apply, smul_neg]
  exact integral_neg _

/-- Additivity at a point where both defining integrals converge. -/
theorem heatConv_add_of_integrable (ι : Euc d →+ G) (θ : ℝ) {u v : G → E} {x : G}
    (hu : Integrable (fun y : Euc d => gaussKernel d θ y • u (x - ι y)))
    (hv : Integrable (fun y : Euc d => gaussKernel d θ y • v (x - ι y))) :
    heatConv ι θ (u + v) x = heatConv ι θ u x + heatConv ι θ v x := by
  simp only [heatConv, Pi.add_apply, smul_add]
  exact integral_add hu hv

variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]

/-- The skew map `(x, y) ↦ (x - ι y, y)` preserves `μ × volume`. -/
theorem measurePreserving_heatShift (ι : Euc d →+ G) (hι : Measurable ι) :
    MeasurePreserving (fun q : G × Euc d => (q.1 - ι q.2, q.2)) (μ.prod volume)
      (μ.prod volume) := by
  have h1 : MeasurePreserving (fun q : Euc d × G => (id q.1, q.2 - ι q.1))
      ((volume : Measure (Euc d)).prod μ) ((volume : Measure (Euc d)).prod μ) :=
    MeasurePreserving.skew_product (MeasurePreserving.id volume)
      (g := fun y x => x - ι y) (measurable_snd.sub (hι.comp measurable_fst))
      (Eventually.of_forall fun y => (measurePreserving_sub_right μ (ι y)).map_eq)
  exact (Measure.measurePreserving_swap.comp h1).comp Measure.measurePreserving_swap

theorem quasiMeasurePreserving_heatShift (ι : Euc d →+ G) (hι : Measurable ι) :
    Measure.QuasiMeasurePreserving (fun q : G × Euc d => q.1 - ι q.2) (μ.prod volume) μ :=
  Measure.quasiMeasurePreserving_fst.comp
    (measurePreserving_heatShift μ ι hι).quasiMeasurePreserving

variable {μ}

theorem aestronglyMeasurable_heatShift (ι : Euc d →+ G) (hι : Measurable ι) {u : G → E}
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun q : G × Euc d => u (q.1 - ι q.2)) (μ.prod volume) :=
  hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_heatShift μ ι hι)

theorem aestronglyMeasurable_heatIntegrand (ι : Euc d →+ G) (hι : Measurable ι) (θ : ℝ)
    {u : G → E} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun q : G × Euc d => gaussKernel d θ q.2 • u (q.1 - ι q.2))
      (μ.prod volume) :=
  ((Gaussian.continuous_gaussKernel θ).comp continuous_snd).aestronglyMeasurable.smul
    (aestronglyMeasurable_heatShift ι hι hu)

/-- `heatConv ι θ u` is a.e. strongly measurable whenever `u` is. -/
theorem aestronglyMeasurable_heatConv (ι : Euc d →+ G) (hι : Measurable ι) (θ : ℝ)
    {u : G → E} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (heatConv ι θ u) μ :=
  (aestronglyMeasurable_heatIntegrand ι hι θ hu).integral_prod_right'

theorem aemeasurable_heatAbs_integrand (ι : Euc d →+ G) (hι : Measurable ι) (θ : ℝ)
    {u : G → E} (hu : AEStronglyMeasurable u μ) :
    AEMeasurable (Function.uncurry fun x y => ‖gaussKernel d θ y‖ₑ * ‖u (x - ι y)‖ₑ)
      (μ.prod volume) := by
  have h := (aestronglyMeasurable_heatIntegrand ι hι θ hu).enorm
  refine h.congr (Eventually.of_forall fun q => ?_)
  simp only [Function.uncurry, enorm_smul]

theorem aemeasurable_heatAbs (ι : Euc d →+ G) (hι : Measurable ι) (θ : ℝ)
    {u : G → E} (hu : AEStronglyMeasurable u μ) : AEMeasurable (heatAbs ι θ u) μ :=
  (aemeasurable_heatAbs_integrand ι hι θ hu).lintegral_prod_right'

/-- For a.e. `x`, the section `y ↦ u (x - ι y)` is a.e. strongly measurable. -/
theorem ae_aestronglyMeasurable_section (ι : Euc d →+ G) (hι : Measurable ι) {u : G → E}
    (hu : AEStronglyMeasurable u μ) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y : Euc d => u (x - ι y)) volume :=
  (aestronglyMeasurable_heatShift ι hι hu).prodMk_left

/-- Integrability of the defining integrand at `x` from finiteness of the majorant. -/
theorem integrable_heatIntegrand_of_lt_top (ι : Euc d →+ G) (θ : ℝ) {u : G → E} {x : G}
    (hm : AEStronglyMeasurable (fun y : Euc d => u (x - ι y)) volume)
    (hx : heatAbs ι θ u x < ∞) :
    Integrable (fun y : Euc d => gaussKernel d θ y • u (x - ι y)) := by
  refine ⟨(Gaussian.continuous_gaussKernel θ).aestronglyMeasurable.smul hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [enorm_smul, heatAbs] using hx

/-- Changing `u` on a `μ`-null set changes `heatConv ι θ u` only on a `μ`-null set. -/
theorem heatConv_congr_ae (ι : Euc d →+ G) (hι : Measurable ι) (θ : ℝ) {u v : G → E}
    (huv : u =ᵐ[μ] v) : heatConv ι θ u =ᵐ[μ] heatConv ι θ v := by
  have h0 : ∀ᵐ q ∂(μ.prod volume), u (q.1 - ι q.2) = v (q.1 - ι q.2) :=
    (quasiMeasurePreserving_heatShift μ ι hι).ae huv
  filter_upwards [Measure.ae_ae_of_ae_prod h0] with x hx
  exact integral_congr_ae (hx.mono fun y hy => by simp only [hy])

/-- The same for the majorant. -/
theorem heatAbs_congr_ae (ι : Euc d →+ G) (hι : Measurable ι) (θ : ℝ) {u v : G → E}
    (huv : u =ᵐ[μ] v) : heatAbs ι θ u =ᵐ[μ] heatAbs ι θ v := by
  have h0 : ∀ᵐ q ∂(μ.prod volume), u (q.1 - ι q.2) = v (q.1 - ι q.2) :=
    (quasiMeasurePreserving_heatShift μ ι hι).ae huv
  filter_upwards [Measure.ae_ae_of_ae_prod h0] with x hx
  exact lintegral_congr_ae (hx.mono fun y hy => by simp only [hy])

/-- The `L^∞` bound of the majorant: for a.e. `x`, `heatAbs ι θ u x ≤ ‖u‖_∞`. -/
theorem ae_heatAbs_le_essSup (ι : Euc d →+ G) (hι : Measurable ι) {θ : ℝ} (hθ : 0 < θ)
    (u : G → E) : ∀ᵐ x ∂μ, heatAbs ι θ u x ≤ eLpNormEssSup u μ := by
  have h0 : ∀ᵐ q ∂(μ.prod volume), ‖u (q.1 - ι q.2)‖ₑ ≤ eLpNormEssSup u μ :=
    (quasiMeasurePreserving_heatShift μ ι hι).ae (ae_le_eLpNormEssSup (f := u))
  filter_upwards [Measure.ae_ae_of_ae_prod h0] with x hx
  calc heatAbs ι θ u x ≤ ∫⁻ y : Euc d, ‖gaussKernel d θ y‖ₑ * eLpNormEssSup u μ :=
        lintegral_mono_ae (hx.mono fun y hy => by gcongr)
    _ = eLpNormEssSup u μ := by
        rw [lintegral_mul_const'' _
          (Gaussian.continuous_gaussKernel θ).measurable.enorm.aemeasurable,
          lintegral_enorm_gaussKernel hθ, one_mul]

variable [SigmaFinite μ]

/-- **INF04 T3, majorant form.** `‖heatAbs ι θ u‖_{L^p(μ)} ≤ ‖u‖_{L^p(μ)}` for `1 ≤ p ≤ ∞`
(Minkowski for `p < ∞`; tex 7416–7425, B0419). -/
theorem eLpNorm_heatAbs_le (ι : Euc d →+ G) (hι : Measurable ι) {θ : ℝ} (hθ : 0 < θ)
    {u : G → E} (hu : AEStronglyMeasurable u μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (heatAbs ι θ u) p μ ≤ eLpNorm u p μ := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_heatAbs_le_essSup ι hι hθ u] with x hx
    simpa only [enorm_eq_self] using hx
  have hmink := NonUniqueEuler.Conv.eLpNorm_lintegral_le (μ := μ) (ν := volume)
    (F := fun x y => ‖gaussKernel d θ y‖ₑ * ‖u (x - ι y)‖ₑ)
    (aemeasurable_heatAbs_integrand ι hι θ hu) hp hp'
  refine hmink.trans ?_
  calc ∫⁻ y : Euc d, eLpNorm (fun x => ‖gaussKernel d θ y‖ₑ * ‖u (x - ι y)‖ₑ) p μ
      ≤ ∫⁻ y : Euc d, ‖gaussKernel d θ y‖ₑ * eLpNorm u p μ := by
        refine lintegral_mono fun y => ?_
        have h1 : eLpNorm (fun x => ‖gaussKernel d θ y‖ₑ * ‖u (x - ι y)‖ₑ) p μ ≤
            ‖gaussKernel d θ y‖₊ • eLpNorm (fun x => u (x - ι y)) p μ :=
          eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
            (Eventually.of_forall fun x => by rw [enorm_eq_self]; rfl) p
        have h2 : eLpNorm (fun x => u (x - ι y)) p μ = eLpNorm u p μ :=
          eLpNorm_comp_measurePreserving (f := fun x => x - ι y) hu
            (measurePreserving_sub_right μ (ι y))
        rw [h2] at h1
        exact h1
    _ = eLpNorm u p μ := by
        rw [lintegral_mul_const'' _
          (Gaussian.continuous_gaussKernel θ).measurable.enorm.aemeasurable,
          lintegral_enorm_gaussKernel hθ, one_mul]

/-- **INF04 T3 `eLpNorm_heatConv_le`.** `‖e^{θΔ}u‖_{L^p(μ)} ≤ ‖u‖_{L^p(μ)}`, `1 ≤ p ≤ ∞`,
`θ > 0` (tex 7416–7425, B0419; tex 2394–2404, B0158 on the line). -/
theorem eLpNorm_heatConv_le (ι : Euc d →+ G) (hι : Measurable ι) {θ : ℝ} (hθ : 0 < θ)
    {u : G → E} (hu : AEStronglyMeasurable u μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (heatConv ι θ u) p μ ≤ eLpNorm u p μ :=
  (eLpNorm_mono_enorm (g := heatAbs ι θ u) fun x => by
      rw [enorm_eq_self]; exact enorm_heatConv_le ι θ u x).trans
    (eLpNorm_heatAbs_le ι hι hθ hu hp)

/-- `e^{θΔ}` maps `L^p(μ)` into itself, `1 ≤ p ≤ ∞`. -/
theorem memLp_heatConv (ι : Euc d →+ G) (hι : Measurable ι) {θ : ℝ} (hθ : 0 < θ)
    {u : G → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : MemLp u p μ) :
    MemLp (heatConv ι θ u) p μ :=
  ⟨aestronglyMeasurable_heatConv ι hι θ hu.1,
    (eLpNorm_heatConv_le ι hι hθ hu.1 hp).trans_lt hu.2⟩

/-- For `u ∈ L^p(μ)`, `1 ≤ p ≤ ∞`, the majorant is finite almost everywhere. -/
theorem ae_heatAbs_lt_top (ι : Euc d →+ G) (hι : Measurable ι) {θ : ℝ} (hθ : 0 < θ)
    {u : G → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : MemLp u p μ) :
    ∀ᵐ x ∂μ, heatAbs ι θ u x < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · have hfin : eLpNormEssSup u μ < ∞ := by simpa [eLpNorm_exponent_top] using hu.2
    filter_upwards [ae_heatAbs_le_essSup ι hι hθ u] with x hx
    exact hx.trans_lt hfin
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hfinite : eLpNorm (heatAbs ι θ u) p μ < ∞ :=
    (eLpNorm_heatAbs_le ι hι hθ hu.1 hp).trans_lt hu.2
  have hpower : ∫⁻ x, heatAbs ι θ u x ^ p.toReal ∂μ < ∞ := by
    simpa only [enorm_eq_self] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp' hfinite
  filter_upwards [ae_lt_top' ((aemeasurable_heatAbs ι hι θ hu.1).pow_const _) hpower.ne]
    with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos hp0 hp')).mp hx

/-- **INF04 T3.** For `u ∈ L^p(μ)`, `1 ≤ p ≤ ∞`, `θ > 0`, the defining integral of
`heatConv ι θ u x` converges absolutely for a.e. `x`. -/
theorem ae_integrable_heatIntegrand (ι : Euc d →+ G) (hι : Measurable ι) {θ : ℝ} (hθ : 0 < θ)
    {u : G → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : MemLp u p μ) :
    ∀ᵐ x ∂μ, Integrable (fun y : Euc d => gaussKernel d θ y • u (x - ι y)) := by
  filter_upwards [ae_heatAbs_lt_top ι hι hθ hp hu,
    ae_aestronglyMeasurable_section ι hι hu.1] with x hx hm
  exact integrable_heatIntegrand_of_lt_top ι θ hm hx

/-- Additivity almost everywhere for `L^p` inputs. -/
theorem heatConv_add_ae (ι : Euc d →+ G) (hι : Measurable ι) {θ : ℝ} (hθ : 0 < θ)
    {u v : G → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : MemLp u p μ) (hv : MemLp v p μ) :
    heatConv ι θ (u + v) =ᵐ[μ] heatConv ι θ u + heatConv ι θ v := by
  filter_upwards [ae_integrable_heatIntegrand ι hι hθ hp hu,
    ae_integrable_heatIntegrand ι hι hθ hp hv] with x hxu hxv
  exact heatConv_add_of_integrable ι θ hxu hxv

end Generic

/-! ### The semigroup law -/

section Semigroup

variable {d : ℕ} {G : Type*} [AddCommGroup G] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

theorem integrable_gaussKernel_mul_shift {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (w : Euc d) :
    Integrable (fun y : Euc d => gaussKernel d s y * gaussKernel d t (w - y)) := by
  simpa only [mul_comm] using Gaussian.integrable_gaussKernel_product ht hs w

theorem integral_gaussKernel_mul_shift {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (w : Euc d) :
    ∫ y : Euc d, gaussKernel d s y * gaussKernel d t (w - y) = gaussKernel d (s + t) w := by
  simp_rw [mul_comm (gaussKernel d s _)]
  rw [Gaussian.integral_gaussKernel_mul_gaussKernel ht hs w, add_comm]

theorem lintegral_gaussKernel_mul_shift {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (w : Euc d) :
    ∫⁻ y : Euc d, ‖gaussKernel d s y‖ₑ * ‖gaussKernel d t (w - y)‖ₑ =
      ‖gaussKernel d (s + t) w‖ₑ := by
  simp_rw [enorm_gaussKernel hs, enorm_gaussKernel ht, enorm_gaussKernel (add_pos hs ht),
    ← ENNReal.ofReal_mul (Gaussian.gaussKernel_nonneg hs _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussKernel_mul_shift hs ht w)
    (Eventually.of_forall fun y => mul_nonneg (Gaussian.gaussKernel_nonneg hs _)
      (Gaussian.gaussKernel_nonneg ht _)), integral_gaussKernel_mul_shift hs ht w]

/-- **INF04 T3 semigroup law, pointwise form.** At every `x` where the section
`y ↦ u(x - ι y)` is a.e. strongly measurable and the majorant `heatAbs ι (s+t) u x` is finite,
`e^{(s+t)Δ}u(x) = e^{sΔ}(e^{tΔ}u)(x)`. Proof: Fubini for
`(y, w) ↦ G_s(y) G_t(w - y) u(x - ι w)` and `G_s ⋆ G_t = G_{s+t}`. -/
theorem heatConv_add_time_of_lt_top (ι : Euc d →+ G) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {u : G → E} {x : G} (hm : AEStronglyMeasurable (fun y : Euc d => u (x - ι y)) volume)
    (hx : heatAbs ι (s + t) u x < ∞) :
    heatConv ι (s + t) u x = heatConv ι s (heatConv ι t u) x := by
  set F : Euc d × Euc d → E := fun q =>
    (gaussKernel d s q.1 * gaussKernel d t (q.2 - q.1)) • u (x - ι q.2) with hF
  have hker : Continuous fun q : Euc d × Euc d =>
      gaussKernel d s q.1 * gaussKernel d t (q.2 - q.1) :=
    ((Gaussian.continuous_gaussKernel s).comp continuous_fst).mul
      ((Gaussian.continuous_gaussKernel t).comp (continuous_snd.sub continuous_fst))
  have hFm : AEStronglyMeasurable F (volume.prod volume) :=
    hker.aestronglyMeasurable.smul (hm.comp_snd)
  have hFi : Integrable F (volume.prod volume) := by
    refine ⟨hFm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hFm.enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) hx
    refine lintegral_congr fun w => ?_
    simp only [hF, enorm_smul, enorm_mul]
    rw [lintegral_mul_const'' _ ?_, lintegral_gaussKernel_mul_shift hs ht w]
    exact ((Gaussian.continuous_gaussKernel s).measurable.enorm.mul
      ((Gaussian.continuous_gaussKernel t).measurable.comp
        (measurable_const.sub measurable_id)).enorm).aemeasurable
  have h1 : ∫ q, F q ∂(volume.prod volume) = heatConv ι (s + t) u x := by
    rw [integral_prod_symm F hFi]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hF]
    rw [integral_smul_const, integral_gaussKernel_mul_shift hs ht w]
  have h2 : ∫ q, F q ∂(volume.prod volume) = heatConv ι s (heatConv ι t u) x := by
    rw [integral_prod F hFi]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF, heatConv]
    simp_rw [mul_smul]
    rw [integral_smul]
    congr 1
    rw [← integral_add_right_eq_self
      (fun w : Euc d => gaussKernel d t (w - y) • u (x - ι w)) y]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [add_sub_cancel_right, map_add, sub_add_eq_sub_sub, sub_right_comm]
  rw [← h1, h2]

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {μ : Measure G} [SigmaFinite μ] [μ.IsAddRightInvariant]

/-- **INF04 T3 `heatConv_add_time`.** For `u ∈ L^p(μ)`, `1 ≤ p ≤ ∞`, and `s, t > 0`,
`e^{(s+t)Δ}u = e^{sΔ}e^{tΔ}u` almost everywhere (tex 7416–7425, B0418). -/
theorem heatConv_add_time (ι : Euc d →+ G) (hι : Measurable ι) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) {u : G → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : MemLp u p μ) :
    heatConv ι (s + t) u =ᵐ[μ] heatConv ι s (heatConv ι t u) := by
  filter_upwards [ae_heatAbs_lt_top ι hι (add_pos hs ht) hp hu,
    ae_aestronglyMeasurable_section ι hι hu.1] with x hx hm
  exact heatConv_add_time_of_lt_top ι hs ht hm hx

end Semigroup

end UnforcedLeray.Heat
