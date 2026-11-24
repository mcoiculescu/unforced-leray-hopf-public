import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussInitial
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.AdjIntegrandRegular

/-!
# Part II-a, task `PartII-a:F05/1/11`: limits of the adjoint-resolvent integrand

Target: `AdjIntegrandLimits` (defined in `Short/PartII-a/Sub/F05_1.lean`).

Source of record: `the November 2 reference manuscript`, lines 1403-1413.

Proof.
* (a) `t → ∞`: `‖F(t)(p)‖ = ‖iteratedFDeriv ℝ 0 F(t) p‖ ≤ C e^{-(Re μ+1)t}` by
  `adjIntegrandRegular_proof` (iv) with `k = 0`, and the right side tends to `0`.
* (b) `t → 0⁺`: `F(t)(p) = c(t) • J(g(t))` with `c(t) = e^{-(μ+1)t}`,
  `J(w, q) = heatGauss Φ₀ w q` (jointly continuous by `heatGaussSmooth_proof`), and
  `g(t) = (adjW ν t, (p.1 + t, e^{-t/2} • p.2))` continuous with `g 0 = (0, p)`.
  Since `c(0) = 1` and `J(0, p) = Φ₀ p` (`heatGaussInitial_proof`), the claim follows by continuity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

namespace AdjIntegrandLimitsAux

theorem continuous_adjW' (ν : ℝ) : Continuous (fun t : ℝ => adjW ν t) := by
  show Continuous (fun t : ℝ => Real.sqrt (ν * (1 - Real.exp (-t))))
  have h1 : Continuous (fun t : ℝ => 1 - Real.exp (-t)) :=
    continuous_const.sub (Real.continuous_exp.comp continuous_neg)
  exact ((continuous_const : Continuous fun _ : ℝ => ν).mul h1).sqrt

theorem continuous_cExp' (μ : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (-((μ + 1) * (t : ℂ)))) := by
  have h : Continuous (fun t : ℝ => (μ + 1) * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  exact Complex.continuous_exp.comp h.neg

theorem continuous_scale' : Continuous (fun t : ℝ => Real.exp (-t / 2)) :=
  Real.continuous_exp.comp (continuous_neg.div_const 2)

/-- The curve `g(t) = (w(t), (p.1 + t, e^{-t/2} • p.2))`. -/
theorem continuous_curve (ν : ℝ) (p : ℝ × Space) :
    Continuous (fun t : ℝ => (adjW ν t, (p.1 + t, Real.exp (-t / 2) • p.2))) :=
  (continuous_adjW' ν).prodMk
    ((continuous_const.add continuous_id).prodMk
      (continuous_scale'.smul continuous_const))

end AdjIntegrandLimitsAux

open AdjIntegrandLimitsAux in
theorem adjIntegrandLimits_proof : UnforcedLeray.Short.PartIIa.AdjIntegrandLimits := by
  intro P ν hP hν μ hμ Φ₀ hΦ p
  obtain ⟨hJ, -⟩ := heatGaussSmooth_proof P hP Φ₀ hΦ
  have hI := (heatGaussInitial_proof P hP Φ₀ hΦ).1
  have hReg := adjIntegrandRegular_proof P ν hP hν μ hμ Φ₀ hΦ
  refine ⟨?_, ?_⟩
  · -- (a) decay as `t → ∞`
    obtain ⟨-, -, -, hb⟩ := hReg
    obtain ⟨C, -, hC⟩ := hb 0
    have hlim : Tendsto (fun t : ℝ => C * Real.exp (-(μ.re + 1) * t)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => (μ.re + 1) * t) atTop atTop :=
        tendsto_id.const_mul_atTop hμ
      have h2 : Tendsto (fun t : ℝ => Real.exp (-((μ.re + 1) * t))) atTop (𝓝 0) :=
        (Real.tendsto_exp_neg_atTop_nhds_zero).comp h1
      have h3 : Tendsto (fun t : ℝ => C * Real.exp (-((μ.re + 1) * t))) atTop (𝓝 (C * 0)) :=
        h2.const_mul C
      rw [mul_zero] at h3
      exact Tendsto.congr (fun t => by rw [neg_mul]) h3
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with t ht
    have := hC t ht p
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  · -- (b) initial value as `t → 0⁺`
    have hJc : Continuous (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) := hJ.continuous
    have hgc : Continuous (fun t : ℝ => (adjW ν t, (p.1 + t, Real.exp (-t / 2) • p.2))) :=
      continuous_curve ν p
    have hcc : Continuous (fun t : ℝ => Complex.exp (-((μ + 1) * (t : ℂ)))) :=
      continuous_cExp' μ
    have hg0 : ((adjW ν 0, (p.1 + 0, Real.exp (-0 / 2) • p.2)) : ℝ × (ℝ × Space)) = (0, p) := by
      simp only [adjW, neg_zero, Real.exp_zero, sub_self, mul_zero, Real.sqrt_zero,
        add_zero, zero_div, one_smul]
    have hc0 : Complex.exp (-((μ + 1) * ((0 : ℝ) : ℂ))) = 1 := by
      simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero]
    have hJg : Tendsto (fun t : ℝ => heatGauss Φ₀ (adjW ν t) (p.1 + t, Real.exp (-t / 2) • p.2))
        (𝓝 0) (𝓝 (Φ₀ p)) := by
      have h : Tendsto (fun t : ℝ => (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2)
          (adjW ν t, (p.1 + t, Real.exp (-t / 2) • p.2))) (𝓝 0)
          (𝓝 ((fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2)
            (adjW ν 0, (p.1 + 0, Real.exp (-0 / 2) • p.2)))) :=
        (hJc.tendsto _).comp (hgc.tendsto 0)
      have hval : (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) (0, p) = Φ₀ p := hI p
      rw [hg0, hval] at h
      exact h
    have hcT : Tendsto (fun t : ℝ => Complex.exp (-((μ + 1) * (t : ℂ)))) (𝓝 0) (𝓝 1) := by
      have h := hcc.tendsto 0
      rw [hc0] at h
      exact h
    have hfull := hcT.smul hJg
    rw [one_smul] at hfull
    exact hfull.mono_left nhdsWithin_le_nhds
