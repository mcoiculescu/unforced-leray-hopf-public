import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Convergence of the `y`-mollification for continuous compactly supported `g` (proof)

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`).

Route: `g` is uniformly continuous with compact support, so `spatMol (ρ n) g - g → 0`
uniformly; the difference vanishes outside a fixed ball, whose volume is finite, and the
`L^p` norm of a function bounded by `ε` and supported in a set of finite measure is at most
`ε · vol(S)^{1/p}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

/-- The difference `spatMol ρ g - g` vanishes outside the ball of radius `r + 1`, when `g`
vanishes outside the ball of radius `r` and `tsupport ρ ⊆ closedBall 0 1`. -/
theorem spatMolC2_zero (r : ℝ) (g : ℝ × UnforcedLeray.Space → ℂ)
    (hgr : ∀ x, r < ‖x‖ → g x = 0) (ρ : UnforcedLeray.Space → ℝ)
    (hρs : tsupport ρ ⊆ Metric.closedBall 0 1) (x : ℝ × UnforcedLeray.Space)
    (hx : r + 1 < ‖x‖) : spatMol ρ g x - g x = 0 := by
  have hgx : g x = 0 := hgr x (by linarith)
  have hz : ∀ y' : UnforcedLeray.Space, (ρ y' : ℂ) * g (x.1, x.2 - y') = 0 := by
    intro y'
    by_cases h0 : ρ y' = 0
    · simp [h0]
    · have hy' : y' ∈ tsupport ρ := subset_tsupport _ (Function.mem_support.2 h0)
      have hb : ‖y'‖ ≤ 1 := by
        have := hρs hy'
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      have hd : dist x (x.1, x.2 - y') ≤ 1 := by
        rw [Prod.dist_eq]
        refine max_le (by rw [dist_self]; norm_num) ?_
        rw [dist_eq_norm, sub_sub_cancel]
        exact hb
      have hn : r < ‖(x.1, x.2 - y')‖ := by
        have h3 := dist_triangle x (x.1, x.2 - y') 0
        simp only [dist_zero_right] at h3
        linarith
      rw [hgr _ hn, mul_zero]
  show (∫ y', (ρ y' : ℂ) * g (x.1, x.2 - y')) - g x = 0
  simp only [hz, hgx, integral_zero, sub_zero]

/-- Uniform convergence `spatMol (ρ n) g → g` for continuous compactly supported `g`. -/
theorem spatMolC2_unif (g : ℝ × UnforcedLeray.Space → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (ρ : ℕ → UnforcedLeray.Space → ℝ)
    (hρ : ∀ n, ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) ∧ (∀ y, 0 ≤ ρ n y) ∧
      ∫ y, ρ n y = 1 ∧ tsupport (ρ n) ⊆ Metric.closedBall 0 (1 / ((n : ℝ) + 1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ × UnforcedLeray.Space, ‖spatMol (ρ n) g x - g x‖ ≤ ε := by
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.1
    (hgc.uniformContinuous_of_continuous hg) ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn x => ?_⟩
  obtain ⟨_, hρsupp, hρ0, hρ1, hρs⟩ := hρ n
  have hρc : Continuous (ρ n) := by
    obtain ⟨hρC, _, _, _, _⟩ := hρ n
    exact hρC.continuous
  have hy_small : ∀ y' : UnforcedLeray.Space, ρ n y' ≠ 0 → ‖y'‖ < δ := by
    intro y' h0
    have hmem : y' ∈ tsupport (ρ n) := subset_tsupport _ (Function.mem_support.2 h0)
    have h1 := hρs hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
    linarith
  have hρint : Integrable (ρ n) :=
    hρc.integrable_of_hasCompactSupport hρsupp
  have hρCint : Integrable (fun y' : UnforcedLeray.Space => (ρ n y' : ℂ)) :=
    hρint.ofReal
  have hρI : ∫ y', (ρ n y' : ℂ) = 1 := by
    rw [integral_complex_ofReal, hρ1]
    simp
  have hint1 : Integrable (fun y' : UnforcedLeray.Space => (ρ n y' : ℂ) * g (x.1, x.2 - y')) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_ofReal.comp hρc).mul
        (hg.comp (continuous_const.prodMk (continuous_const.sub continuous_id)))
    · have hcs : HasCompactSupport (fun y' : UnforcedLeray.Space => (ρ n y' : ℂ)) :=
        hρsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
      exact hcs.mul_right
  have hint2 : Integrable (fun y' : UnforcedLeray.Space => (ρ n y' : ℂ) * g x) :=
    hρCint.mul_const (g x)
  have hcst : ∫ y', (ρ n y' : ℂ) * g x = g x := by
    rw [integral_mul_const, hρI, one_mul]
  set F : UnforcedLeray.Space → ℂ :=
    fun y' => (ρ n y' : ℂ) * (g (x.1, x.2 - y') - g x) with hF
  have key : spatMol (ρ n) g x - g x = ∫ y', F y' := by
    have e1 : ∫ y', F y' = ∫ y', ((ρ n y' : ℂ) * g (x.1, x.2 - y') - (ρ n y' : ℂ) * g x) := by
      congr 1
      ext y'
      simp only [hF, mul_sub]
    rw [e1, integral_sub hint1 hint2, hcst]
    rfl
  have hbd : ∀ y', ‖F y'‖ ≤ ρ n y' * ε := by
    intro y'
    by_cases h0 : ρ n y' = 0
    · simp [hF, h0]
    · have hdist : dist (x.1, x.2 - y') x ≤ ‖y'‖ := by
        rw [Prod.dist_eq, dist_self]
        refine max_le (by positivity) ?_
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
      have hgd : dist (g (x.1, x.2 - y')) (g x) < ε :=
        hgδ (lt_of_le_of_lt hdist (hy_small y' h0))
      rw [dist_eq_norm] at hgd
      simp only [hF]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ0 y')]
      exact mul_le_mul_of_nonneg_left hgd.le (hρ0 y')
  calc ‖spatMol (ρ n) g x - g x‖ = ‖∫ y', F y'‖ := by rw [key]
    _ ≤ ∫ y', ρ n y' * ε :=
        norm_integral_le_of_norm_le (hρint.mul_const ε) (ae_of_all _ hbd)
    _ = ε := by rw [integral_mul_const, hρ1, one_mul]

/-- `L^p` bound for a function vanishing off a set of finite measure and bounded by `ε`. -/
theorem spatMolC2_bound (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (S : Set (ℝ × UnforcedLeray.Space)) (hS : MeasurableSet S)
    (hμS : volume S ≠ ⊤) (f : ℝ × UnforcedLeray.Space → ℂ)
    (hz : ∀ x, x ∉ S → f x = 0) (ε : ℝ) (hε : ∀ x, ‖f x‖ ≤ ε) :
    eLpNorm f p volume ≤ ENNReal.ofReal ε * (volume S) ^ (1 / p.toReal) := by
  have hf : f = S.indicator f := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx, hz x hx]
  rw [hf, eLpNorm_indicator_eq_eLpNorm_restrict hS]
  have : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμS.lt_top⟩
  refine (eLpNorm_le_of_ae_bound (ae_of_all _ hε)).trans ?_
  rw [Measure.restrict_apply_univ, one_div]
  exact le_of_eq (mul_comm _ _)

theorem spatMolContCompact_holds : SpatMolContCompact := by
  intro p hp1 hpt ρ hρ g hg hgc
  obtain ⟨r, hr⟩ := (hgc.isCompact.isBounded).subset_closedBall (0 : ℝ × UnforcedLeray.Space)
  have hgr : ∀ x : ℝ × UnforcedLeray.Space, r < ‖x‖ → g x = 0 := by
    intro x hx
    by_contra hne
    have hmem := subset_tsupport g (Function.mem_support.2 hne)
    have h4 := hr hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h4
    linarith
  have hS : MeasurableSet (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (r + 1)) :=
    Metric.isClosed_closedBall.measurableSet
  have hμS : volume (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (r + 1)) ≠ ⊤ :=
    (measure_closedBall_lt_top).ne
  have hρs1 : ∀ n, tsupport (ρ n) ⊆ Metric.closedBall (0 : UnforcedLeray.Space) 1 := by
    intro n
    refine (hρ n).2.2.2.2.trans (Metric.closedBall_subset_closedBall ?_)
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hzS : ∀ n, ∀ x, x ∉ Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (r + 1) →
      spatMol (ρ n) g x - g x = 0 := by
    intro n x hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact spatMolC2_zero r g hgr (ρ n) (hρs1 n) x hx
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hV : (volume (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (r + 1))) ^ (1 / p.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hμS
  have h0 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε) (𝓝 0) (𝓝 0) := by
    simpa using ENNReal.continuous_ofReal.tendsto 0
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal ε *
      (volume (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (r + 1))) ^ (1 / p.toReal))
      (𝓝 0) (𝓝 0) := by
    have key : Tendsto (fun ε : ℝ => ENNReal.ofReal ε *
        (volume (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (r + 1))) ^ (1 / p.toReal))
        (𝓝 0) (𝓝 (0 * (volume (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (r + 1))) ^ (1 / p.toReal))) :=
      ENNReal.Tendsto.mul_const h0 (Or.inr hV)
    rw [zero_mul] at key
    exact key
  have hev := hlim.eventually (eventually_lt_nhds hη)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.1 hev
  have hε : 0 < δ / 2 := half_pos hδpos
  have hεlt := hδ (y := δ / 2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    linarith)
  obtain ⟨N, hN⟩ := spatMolC2_unif g hg hgc ρ hρ (δ / 2) hε
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  calc eLpNorm (spatMol (ρ n) g - g) p volume
      ≤ ENNReal.ofReal (δ / 2) *
          (volume (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (r + 1))) ^ (1 / p.toReal) :=
        spatMolC2_bound p hp1 hpt _ hS hμS _ (fun x hx => hzS n x hx) (δ / 2)
          (fun x => hN n hn x)
    _ ≤ η := le_of_lt hεlt

end UnforcedLeray.Short.PartIIIb.Concrete
