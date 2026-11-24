import UnforcedLeray.Analysis.Rayleigh.Compactness
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
# Genuine decay of uniformly continuous square-integrable fields

A uniformly continuous function with finite squared mass tends to zero at both
ends of the real line. A nonzero value would force a fixed amount of squared
mass on an adjacent interval; the actual integrable tail tends to zero.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.Rayleigh

/-- A fixed local value and uniform continuity force genuine positive local mass. -/
lemma local_mass_lower_of_uniform_modulus {f : ℝ → ℂ} {ε δ x : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hmod : ∀ ⦃a b : ℝ⦄, dist a b < δ → dist (f a) (f b) < ε / 2)
    (hval : ε ≤ ‖f x‖) (hint : Integrable (fun t => ‖f t‖ ^ 2)) :
    δ / 2 * (ε / 2) ^ 2 ≤ ∫ t in Ioc x (x + δ / 2), ‖f t‖ ^ 2 := by
  have hlower : ∀ t ∈ Ioc x (x + δ / 2), (ε / 2) ^ 2 ≤ ‖f t‖ ^ 2 := by
    intro t ht
    have hdist : dist x t < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
      linarith [ht.2]
    have hm := hmod hdist
    rw [dist_eq_norm] at hm
    have hn := norm_sub_norm_le (f x) (f t)
    have hb : ε / 2 ≤ ‖f t‖ := by linarith
    nlinarith [norm_nonneg (f t)]
  have hconst : IntegrableOn (fun _ : ℝ => (ε / 2) ^ 2) (Ioc x (x + δ / 2)) :=
    continuous_const.integrableOn_Ioc
  have hi := setIntegral_mono_on hconst hint.integrableOn measurableSet_Ioc hlower
  have hvol : (∫ _ in Ioc x (x + δ / 2), (ε / 2) ^ 2) = δ / 2 * (ε / 2) ^ 2 := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith : x ≤ x + δ / 2), smul_eq_mul]
    congr 1
    ring
  rwa [hvol] at hi

/-- Positive-end decay follows from actual finite squared mass and uniform continuity. -/
theorem tendsto_zero_atTop_of_uniformContinuous_integrable_sq {f : ℝ → ℂ}
    (hu : UniformContinuous f) (hi : Integrable (fun t => ‖f t‖ ^ 2)) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (by linarith)
  have hpositive : 0 < δ / 2 * (ε / 2) ^ 2 := by positivity
  have htail : Tendsto (fun x : ℝ => ∫ t in Ioi x, ‖f t‖ ^ 2) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hsmall : ∀ᶠ x : ℝ in atTop, (∫ t in Ioi x, ‖f t‖ ^ 2) < δ / 2 * (ε / 2) ^ 2 :=
    htail.eventually (gt_mem_nhds hpositive)
  filter_upwards [hsmall] with x hx
  rw [dist_zero_right]
  by_contra hbad
  have hval : ε ≤ ‖f x‖ := le_of_not_gt hbad
  have hlower := local_mass_lower_of_uniform_modulus hε hδ hmod hval hi
  have hupper : (∫ t in Ioc x (x + δ / 2), ‖f t‖ ^ 2) ≤
      ∫ t in Ioi x, ‖f t‖ ^ 2 := by
    exact setIntegral_mono_set hi.integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ ht => ht.1)
  linarith

/-- Negative-end decay is the reflected positive-end theorem. -/
theorem tendsto_zero_atBot_of_uniformContinuous_integrable_sq {f : ℝ → ℂ}
    (hu : UniformContinuous f) (hi : Integrable (fun t => ‖f t‖ ^ 2)) :
    Tendsto f atBot (𝓝 0) := by
  have h := tendsto_zero_atTop_of_uniformContinuous_integrable_sq
    (hu.comp uniformContinuous_neg) hi.comp_neg
  simpa only [Function.comp_def, neg_neg] using h.comp tendsto_neg_atBot_atTop

/-- A continuous square-root modulus and genuine L² membership imply decay at both ends. -/
theorem tendsto_zero_of_sqrt_bound_memLp {f : ℝ → ℂ} (K : ℝ)
    (hmod : ∀ s t, ‖f s - f t‖ ≤ K * Real.sqrt |s - t|)
    (hf : MemLp f 2 volume) :
    Tendsto f atTop (𝓝 0) ∧ Tendsto f atBot (𝓝 0) := by
  have hu : UniformContinuous f :=
    (uniformEquicontinuous_of_sqrt_bound (fun _ : Unit => f) K (fun _ => hmod)).uniformContinuous ()
  have hi : Integrable (fun t => ‖f t‖ ^ 2) := hf.integrable_norm_pow (by norm_num)
  exact ⟨tendsto_zero_atTop_of_uniformContinuous_integrable_sq hu hi,
    tendsto_zero_atBot_of_uniformContinuous_integrable_sq hu hi⟩

end UnforcedLeray.Rayleigh
