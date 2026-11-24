import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Helper for `NiceFieldsSeparate` (task `PartII-b:T11/6`): the disc mean value identity

For an entire function `f : ℂ → ℂ`, the integral of `f` over the Euclidean disc `ball z₀ R` equals
`(π R²) • f z₀`. Proof: translate to the disc at `0`, pass to polar coordinates
(`Complex.integral_comp_polarCoord_symm`), and use the circle mean value property
(`DiffContOnCl.circleAverage`) on each circle.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Real Complex Filter
open scoped Real

namespace UnforcedLeray.Short.IIb.SeparateDisc

/-- The circle integral of an entire function over a circle equals `2π` times the centre value. -/
theorem circle_integral_eq_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z0 : ℂ) (ρ : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, f (circleMap z0 ρ θ) = (2 * π) • f z0 := by
  have h := (hf.diffContOnCl (s := ball z0 |ρ|)).circleAverage (c := z0) (R := ρ)
  rw [circleAverage_def] at h
  have h2 : (2 * π : ℝ) ≠ 0 := by positivity
  rw [← h, smul_smul, mul_inv_cancel₀ h2, one_smul]

/-- The point `z₀ + polarCoord.symm p` is the point of the circle of radius `p.1` at angle `p.2`. -/
theorem add_polarCoord_symm_eq_circleMap (z0 : ℂ) (p : ℝ × ℝ) :
    z0 + Complex.polarCoord.symm p = circleMap z0 p.1 p.2 := by
  obtain ⟨x, y⟩ := p
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- **Disc mean value identity.** For an entire function `f`, the integral over the disc
`ball z₀ R` is `(π R²) • f z₀`. -/
theorem integral_ball_eq_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z0 : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ w in ball z0 R, f w = (π * R ^ 2) • f z0 := by
  -- Step 1: translate the disc to the origin.
  set F : ℂ → ℂ := (ball (0 : ℂ) R).indicator (fun u => f (z0 + u)) with hF
  have h1 : ∫ w in ball z0 R, f w = ∫ u, F u := by
    rw [← integral_indicator measurableSet_ball, ← integral_add_left_eq_self
      ((ball z0 R).indicator f) z0]
    congr 1
    ext x
    have hmem : z0 + x ∈ ball z0 R ↔ x ∈ ball (0 : ℂ) R := by
      simp [Metric.mem_ball, dist_eq_norm]
    by_cases hx : x ∈ ball (0 : ℂ) R
    · simp [hF, Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
    · simp [hF, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.1 hx)]
  rw [h1]
  -- Step 2: polar coordinates.
  have hpolar : ∫ u, F u = ∫ p in Complex.polarCoord.target,
      p.1 • F (Complex.polarCoord.symm p) :=
    (Complex.integral_comp_polarCoord_symm F).symm
  rw [hpolar]
  set S : Set (ℝ × ℝ) := Ioo (0 : ℝ) R ×ˢ Ioo (-π) π with hS
  have hST : S ⊆ Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    exact prod_mono (fun x hx => hx.1) subset_rfl
  have hzero : ∀ p ∈ Complex.polarCoord.target \ S,
      p.1 • F (Complex.polarCoord.symm p) = 0 := by
    intro p hp
    obtain ⟨hpT, hpS⟩ := hp
    rw [Complex.polarCoord_target] at hpT
    have hp1 : R ≤ p.1 := by
      by_contra hlt
      exact hpS ⟨⟨hpT.1, not_le.1 hlt⟩, hpT.2⟩
    have hnot : Complex.polarCoord.symm p ∉ ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hpT.1]
      exact not_lt.2 hp1
    have hF0 : F (Complex.polarCoord.symm p) = 0 := by
      rw [hF]
      exact Set.indicator_of_notMem hnot _
    rw [hF0, smul_zero]
  have hTm : MeasurableSet Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hST hzero]
  -- Step 3: on `S` the integrand is `p.1 • f (circleMap z0 p.1 p.2)`.
  have hSF : ∀ p ∈ S, p.1 • F (Complex.polarCoord.symm p) = p.1 • f (circleMap z0 p.1 p.2) := by
    intro p hp
    have hin : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
      exact hp.1.2
    simp only [hF, Set.indicator_of_mem hin]
    rw [add_polarCoord_symm_eq_circleMap]
  rw [setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) hSF]
  -- Step 4: continuity and integrability on the compact closure of `S`.
  set Ψ : ℝ × ℝ → ℂ := fun p => p.1 • f (circleMap z0 p.1 p.2) with hΨ
  have hΨc : Continuous Ψ := by
    have hc : Continuous fun p : ℝ × ℝ => circleMap z0 p.1 p.2 := by
      unfold circleMap
      fun_prop
    exact continuous_fst.smul (hf.continuous.comp hc)
  have hint : IntegrableOn Ψ S (volume.prod volume) := by
    have hK : IsCompact (Icc (0 : ℝ) R ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
    have hSK : S ⊆ Icc (0 : ℝ) R ×ˢ Icc (-π) π :=
      prod_mono (fun x hx => ⟨hx.1.le, hx.2.le⟩) (fun x hx => ⟨hx.1.le, hx.2.le⟩)
    exact (hΨc.continuousOn.integrableOn_compact hK).mono_set hSK
  rw [Measure.volume_eq_prod, setIntegral_prod Ψ (by simpa [Measure.volume_eq_prod] using hint)]
  -- Step 5: inner circle integrals.
  have hinner : ∀ x : ℝ, ∫ y in Ioo (-π) π, Ψ (x, y) = x • ((2 * π) • f z0) := by
    intro x
    simp only [hΨ]
    rw [integral_smul]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
    have hper : Function.Periodic (fun y => f (circleMap z0 x y)) (2 * π) := by
      intro y
      simp only [periodic_circleMap z0 x y]
    have hshift := hper.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, zero_add] at hshift
    rw [hshift]
    exact circle_integral_eq_of_differentiable hf z0 x
  have hfun : ∫ x in Ioo (0 : ℝ) R, ∫ y in Ioo (-π) π, Ψ (x, y) =
      ∫ x in Ioo (0 : ℝ) R, x • ((2 * π) • f z0) :=
    setIntegral_congr_fun measurableSet_Ioo (fun x _ => hinner x)
  rw [hfun, integral_smul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR, integral_id, smul_smul]
  congr 1
  ring

end UnforcedLeray.Short.IIb.SeparateDisc
