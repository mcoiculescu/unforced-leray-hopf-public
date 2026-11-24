import UnforcedLeray.Short.PartI.Sub.C02
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Part I, task `PartI:C02`: continuous approximation of a bounded measurable coefficient

Source of record: `the November 2 reference manuscript`, lines 1014-1030.
The statement is `ContinuousApproximation` of `Short/PartI/Sub/C02.lean`: a measurable `β`
with values in `[0, βs]` is the almost everywhere limit of continuous functions with values
in `[0, βs]`.

Proof: `volume` is not finite, so the approximation is done in `L¹(μ)` for the finite measure
`μ = volume.withDensity (exp(-t²))`, which has the same null sets as `volume`.
Bounded continuous approximants are clamped to `[0, βs]` (this does not increase the `L¹(μ)`
distance to `β`), and an almost everywhere convergent subsequence is extracted.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace UnforcedLeray.Short.PartI

/-- **Continuous approximation** (task `PartI:C02`, sub-lemma 4). -/
theorem continuousApproximation : ContinuousApproximation := by
  intro βs β hβm hβ
  have hβs0 : 0 ≤ βs := le_trans (hβ 0).1 (hβ 0).2
  -- A finite measure with the same null sets as `volume`.
  let dens : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-1 * t ^ 2))
  let μ : Measure ℝ := volume.withDensity dens
  have hint : Integrable (fun t : ℝ => Real.exp (-1 * t ^ 2)) :=
    integrable_exp_neg_mul_sq one_pos
  have : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hint.2
  have hdens_meas : Measurable dens := by fun_prop
  have hdens_ne : ∀ᵐ t ∂(volume : Measure ℝ), dens t ≠ 0 :=
    Filter.Eventually.of_forall fun t => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hvol_ac : (volume : Measure ℝ) ≪ μ :=
    withDensity_absolutelyContinuous' hdens_meas.aemeasurable hdens_ne
  -- `β` is bounded and measurable, hence in `L¹(μ)`.
  have hbd : ∀ᵐ t ∂μ, ‖β t‖ ≤ |βs| := Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hβ t).1]
    exact le_trans (hβ t).2 (le_abs_self βs)
  have hβL : MemLp β 1 μ := MemLp.of_bound hβm.aestronglyMeasurable |βs| hbd
  -- Clamping to `[0, βs]` does not increase the distance to `b ∈ [0, βs]`.
  have key : ∀ x b : ℝ, 0 ≤ b → b ≤ βs → |max 0 (min x βs) - b| ≤ |x - b| := by
    intro x b hb0 hbs
    rcases le_total x 0 with hx | hx
    · have h1 : max 0 (min x βs) = 0 := max_eq_left (le_trans (min_le_left _ _) hx)
      rw [h1, abs_of_nonpos (by linarith : (0:ℝ) - b ≤ 0),
        abs_of_nonpos (by linarith : x - b ≤ 0)]
      linarith
    · rcases le_total x βs with hx' | hx'
      · have h1 : max 0 (min x βs) = x := by rw [min_eq_left hx', max_eq_right hx]
        exact le_of_eq (by rw [h1])
      · have h1 : max 0 (min x βs) = βs := by rw [min_eq_right hx', max_eq_right hβs0]
        rw [h1, abs_of_nonneg (by linarith : 0 ≤ βs - b),
          abs_of_nonneg (by linarith : 0 ≤ x - b)]
        linarith
  -- Bounded continuous approximants in `L¹(μ)` with rate `(n+1)⁻¹`.
  have hex : ∀ n : ℕ, ∃ g : ℝ →ᵇ ℝ,
      eLpNorm (β - (g : ℝ → ℝ)) 1 μ ≤ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := fun n => by
    obtain ⟨g, hg, -⟩ := hβL.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top
      (ε := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    exact ⟨g, hg⟩
  choose g hg using hex
  -- Clamped approximants.
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℝ → ℝ, ∀ n t, F n t = max 0 (min (g n t) βs) :=
    ⟨fun n t => max 0 (min (g n t) βs), fun _ _ => rfl⟩
  have hFc : ∀ n, Continuous (F n) := fun n => by
    have h : F n = fun t => max 0 (min (g n t) βs) := funext (hFdef n)
    rw [h]
    exact continuous_const.max ((g n).continuous.min continuous_const)
  have hFb : ∀ n t, 0 ≤ F n t ∧ F n t ≤ βs := fun n t => by
    rw [hFdef]
    exact ⟨le_max_left _ _, max_le hβs0 (min_le_right _ _)⟩
  have hdist : ∀ n, eLpNorm (F n - β) 1 μ ≤ eLpNorm (β - (g n : ℝ → ℝ)) 1 μ := fun n =>
    eLpNorm_mono fun t => by
      simp only [Pi.sub_apply, Real.norm_eq_abs, hFdef]
      rw [abs_sub_comm (β t) (g n t)]
      exact key (g n t) (β t) (hβ t).1 (hβ t).2
  -- Convergence in `L¹(μ)`, hence in measure.
  have hε : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hL1 : Tendsto (fun n => eLpNorm (F n - β) 1 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε (fun n => zero_le)
      (fun n => (hdist n).trans (hg n))
  have hconv : TendstoInMeasure μ F atTop β :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun n => (hFc n).aestronglyMeasurable)
      hβm.aestronglyMeasurable hL1
  -- Almost everywhere convergent subsequence, transferred from `μ` to `volume`.
  obtain ⟨ns, -, hae⟩ := hconv.exists_seq_tendsto_ae
  refine ⟨fun i => F (ns i), fun i => hFc (ns i), fun i t => hFb (ns i) t, ?_⟩
  exact Filter.Eventually.filter_mono hvol_ac.ae_le hae

end UnforcedLeray.Short.PartI
