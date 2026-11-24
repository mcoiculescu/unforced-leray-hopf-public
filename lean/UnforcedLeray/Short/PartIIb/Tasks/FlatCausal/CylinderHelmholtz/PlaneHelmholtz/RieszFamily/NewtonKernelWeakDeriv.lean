import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonGradKernelLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Leaf `PartII-b:T12/1/1/2/4`: the weak derivative of the planar Newton kernel

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `ψ` and `k ∈ {0,1}`, `∫ N ∂_kψ = -∫ ∂_kN ψ`.  Proof: the plane is identified
with `ℝ × ℝ` (`planePt a b = ![a, b]`, measure preserving); Fubini reduces to the one-variable
integration by parts `integral_mul_deriv_eq_deriv_mul_of_integrable` on each line off the axis
(where the kernel is smooth), and the axis is Lebesgue-null.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The planar point with coordinates `a, b`. -/
abbrev planePt (a b : ℝ) : Pl := ![a, b]

/-- Change of variables from the plane to `ℝ × ℝ`. -/
theorem nkwd_integral_plane (G : Pl → ℝ) :
    ∫ x, G x = ∫ p : ℝ × ℝ, G (planePt p.1 p.2) := by
  have h := (MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ)).integral_comp' G
  exact h.symm

theorem nkwd_integrable_plane (G : Pl → ℝ) (hG : Integrable G volume) :
    Integrable (fun p : ℝ × ℝ => G (planePt p.1 p.2)) volume := by
  have hm := MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ)
  exact (hm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hG

theorem nkwd_hcs_line0 {g : Pl → ℝ} (hg : HasCompactSupport g) (b : ℝ) :
    HasCompactSupport (fun t : ℝ => g (planePt t b)) := by
  obtain ⟨r, hr⟩ := hg.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun t ht => ?_
  by_contra hne
  have hmem : planePt t b ∈ tsupport g := subset_tsupport _ (Function.mem_support.2 hne)
  have h1 := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h3 : |t| ≤ ‖planePt t b‖ := by
    have := norm_le_pi_norm (planePt t b) 0
    simpa [planePt, Real.norm_eq_abs] using this
  exact ht (abs_le.1 (le_trans h3 h1))

theorem nkwd_hcs_line1 {g : Pl → ℝ} (hg : HasCompactSupport g) (a : ℝ) :
    HasCompactSupport (fun t : ℝ => g (planePt a t)) := by
  obtain ⟨r, hr⟩ := hg.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun t ht => ?_
  by_contra hne
  have hmem : planePt a t ∈ tsupport g := subset_tsupport _ (Function.mem_support.2 hne)
  have h1 := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h3 : |t| ≤ ‖planePt a t‖ := by
    have := norm_le_pi_norm (planePt a t) 1
    simpa [planePt, Real.norm_eq_abs] using this
  exact ht (abs_le.1 (le_trans h3 h1))

theorem nkwd_cont_line0 {h : Pl → ℝ} (hh : Continuous h) (b : ℝ) :
    Continuous (fun t : ℝ => h (planePt t b)) := by
  refine hh.comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [planePt] <;> fun_prop

theorem nkwd_cont_line1 {h : Pl → ℝ} (hh : Continuous h) (a : ℝ) :
    Continuous (fun t : ℝ => h (planePt a t)) := by
  refine hh.comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [planePt] <;> fun_prop

theorem nkwd_hasDerivAt_line0 (b t : ℝ) :
    HasDerivAt (fun s : ℝ => planePt s b) (Pi.single 0 1) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [planePt] using hasDerivAt_id' t
  · simpa [planePt, Pi.single_apply] using hasDerivAt_const t b

theorem nkwd_hasDerivAt_line1 (a t : ℝ) :
    HasDerivAt (fun s : ℝ => planePt a s) (Pi.single 1 1) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [planePt, Pi.single_apply] using hasDerivAt_const t a
  · simpa [planePt] using hasDerivAt_id' t

theorem nkwd_kernel_line0 (b t : ℝ) :
    newtonKernel (planePt t b) = (4 * Real.pi)⁻¹ * Real.log (t ^ 2 + b ^ 2) := by
  simp [newtonKernel, planePt]

theorem nkwd_kernel_line1 (a t : ℝ) :
    newtonKernel (planePt a t) = (4 * Real.pi)⁻¹ * Real.log (a ^ 2 + t ^ 2) := by
  simp [newtonKernel, planePt]

/-- Derivative of the kernel along a line `s ↦ (s, b)` with `b ≠ 0`. -/
theorem nkwd_hasDerivAt_N0 {b : ℝ} (hb : b ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => newtonKernel (planePt s b)) (newtonGradKernel 0 (planePt t b)) t := by
  have hpos : t ^ 2 + b ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + b ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const (b ^ 2)
  have h2 := (h1.log hpos).const_mul ((4 * Real.pi)⁻¹)
  have hfun : (fun s : ℝ => newtonKernel (planePt s b)) =
      fun s => (4 * Real.pi)⁻¹ * Real.log (s ^ 2 + b ^ 2) := by
    funext s
    simp [newtonKernel, planePt]
  rw [hfun]
  refine h2.congr_deriv ?_
  simp only [newtonGradKernel, planePt, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- Derivative of the kernel along a line `s ↦ (a, s)` with `a ≠ 0`. -/
theorem nkwd_hasDerivAt_N1 {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => newtonKernel (planePt a s)) (newtonGradKernel 1 (planePt a t)) t := by
  have hpos : a ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => a ^ 2 + s ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add (a ^ 2)
  have h2 := (h1.log hpos).const_mul ((4 * Real.pi)⁻¹)
  have hfun : (fun s : ℝ => newtonKernel (planePt a s)) =
      fun s => (4 * Real.pi)⁻¹ * Real.log (a ^ 2 + s ^ 2) := by
    funext s
    simp [newtonKernel, planePt]
  rw [hfun]
  refine h2.congr_deriv ?_
  simp only [newtonGradKernel, planePt, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- One-variable integration by parts along the line `t ↦ (t, b)`, `b ≠ 0`. -/
theorem nkwd_ibp_line0 {ψ : Pl → ℝ} (hψ : IsTest ψ) {b : ℝ} (hb : b ≠ 0) :
    ∫ t, newtonKernel (planePt t b) * pd 0 ψ (planePt t b) =
      -∫ t, newtonGradKernel 0 (planePt t b) * ψ (planePt t b) := by
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hpd := pdTest 0 ψ hψ
  have hNd := nkwd_hasDerivAt_N0 hb
  have hvd : ∀ t, HasDerivAt (fun s => ψ (planePt s b)) (pd 0 ψ (planePt t b)) t := fun t =>
    (hψd (planePt t b)).hasFDerivAt.comp_hasDerivAt t (nkwd_hasDerivAt_line0 b t)
  have hNc : Continuous (fun s => newtonKernel (planePt s b)) :=
    continuous_iff_continuousAt.2 fun t => (hNd t).continuousAt
  have hGc : Continuous (fun s => newtonGradKernel 0 (planePt s b)) := by
    have hfun : (fun s => newtonGradKernel 0 (planePt s b)) =
        fun s => (2 * Real.pi)⁻¹ * s / (s ^ 2 + b ^ 2) := by
      funext s
      simp [newtonGradKernel, planePt]
    rw [hfun]
    exact (continuous_const.mul continuous_id).div (by fun_prop)
      (fun s => (by positivity : s ^ 2 + b ^ 2 ≠ 0))
  have hvc : Continuous (fun s => ψ (planePt s b)) := nkwd_cont_line0 hψ.1.continuous b
  have hv'c : Continuous (fun s => pd 0 ψ (planePt s b)) :=
    nkwd_cont_line0 hpd.1.continuous b
  have hvcs : HasCompactSupport (fun s => ψ (planePt s b)) := nkwd_hcs_line0 hψ.2 b
  have hv'cs : HasCompactSupport (fun s => pd 0 ψ (planePt s b)) := nkwd_hcs_line0 hpd.2 b
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hNd t) (fun t _ => hvd t)
    (Continuous.integrable_of_hasCompactSupport (hNc.mul hv'c) (hv'cs.mul_left))
    (Continuous.integrable_of_hasCompactSupport (hGc.mul hvc) (hvcs.mul_left))
    (Continuous.integrable_of_hasCompactSupport (hNc.mul hvc) (hvcs.mul_left))

/-- One-variable integration by parts along the line `t ↦ (a, t)`, `a ≠ 0`. -/
theorem nkwd_ibp_line1 {ψ : Pl → ℝ} (hψ : IsTest ψ) {a : ℝ} (ha : a ≠ 0) :
    ∫ t, newtonKernel (planePt a t) * pd 1 ψ (planePt a t) =
      -∫ t, newtonGradKernel 1 (planePt a t) * ψ (planePt a t) := by
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hpd := pdTest 1 ψ hψ
  have hNd := nkwd_hasDerivAt_N1 ha
  have hvd : ∀ t, HasDerivAt (fun s => ψ (planePt a s)) (pd 1 ψ (planePt a t)) t := fun t =>
    (hψd (planePt a t)).hasFDerivAt.comp_hasDerivAt t (nkwd_hasDerivAt_line1 a t)
  have hNc : Continuous (fun s => newtonKernel (planePt a s)) :=
    continuous_iff_continuousAt.2 fun t => (hNd t).continuousAt
  have hGc : Continuous (fun s => newtonGradKernel 1 (planePt a s)) := by
    have hfun : (fun s => newtonGradKernel 1 (planePt a s)) =
        fun s => (2 * Real.pi)⁻¹ * s / (a ^ 2 + s ^ 2) := by
      funext s
      simp [newtonGradKernel, planePt]
    rw [hfun]
    exact (continuous_const.mul continuous_id).div (by fun_prop)
      (fun s => (by positivity : a ^ 2 + s ^ 2 ≠ 0))
  have hvc : Continuous (fun s => ψ (planePt a s)) := nkwd_cont_line1 hψ.1.continuous a
  have hv'c : Continuous (fun s => pd 1 ψ (planePt a s)) :=
    nkwd_cont_line1 hpd.1.continuous a
  have hvcs : HasCompactSupport (fun s => ψ (planePt a s)) := nkwd_hcs_line1 hψ.2 a
  have hv'cs : HasCompactSupport (fun s => pd 1 ψ (planePt a s)) := nkwd_hcs_line1 hpd.2 a
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hNd t) (fun t _ => hvd t)
    (Continuous.integrable_of_hasCompactSupport (hNc.mul hv'c) (hv'cs.mul_left))
    (Continuous.integrable_of_hasCompactSupport (hGc.mul hvc) (hvcs.mul_left))
    (Continuous.integrable_of_hasCompactSupport (hNc.mul hvc) (hvcs.mul_left))

/-- The planar weak derivative in the first variable. -/
theorem nkwd_weak0 {ψ : Pl → ℝ} (hψ : IsTest ψ) :
    ∫ y, newtonKernel y * pd 0 ψ y = -∫ y, newtonGradKernel 0 y * ψ y := by
  have hpd := pdTest 0 ψ hψ
  have hF : Integrable (fun y => newtonKernel y * pd 0 ψ y) volume := by
    have := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (μ := volume) (newtonKernelLocInt) hpd.1.continuous hpd.2
    simpa [smul_eq_mul] using this
  have hG : Integrable (fun y => newtonGradKernel 0 y * ψ y) volume := by
    have := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (μ := volume) (newtonGradKernelLocInt 0) hψ.1.continuous hψ.2
    simpa [smul_eq_mul] using this
  have hae : ∀ᵐ b : ℝ, b ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := (0 : ℝ)))] with b hb
    simpa using hb
  calc ∫ y, newtonKernel y * pd 0 ψ y
      = ∫ p : ℝ × ℝ, newtonKernel (planePt p.1 p.2) * pd 0 ψ (planePt p.1 p.2) :=
        nkwd_integral_plane _
    _ = ∫ b, ∫ a, newtonKernel (planePt a b) * pd 0 ψ (planePt a b) :=
        integral_prod_symm _ (nkwd_integrable_plane _ hF)
    _ = ∫ b, -∫ a, newtonGradKernel 0 (planePt a b) * ψ (planePt a b) :=
        integral_congr_ae (hae.mono fun b hb => nkwd_ibp_line0 hψ hb)
    _ = -∫ b, ∫ a, newtonGradKernel 0 (planePt a b) * ψ (planePt a b) := integral_neg _
    _ = -∫ p : ℝ × ℝ, newtonGradKernel 0 (planePt p.1 p.2) * ψ (planePt p.1 p.2) :=
        congrArg Neg.neg (integral_prod_symm _
          (nkwd_integrable_plane (fun y => newtonGradKernel 0 y * ψ y) hG)).symm
    _ = -∫ y, newtonGradKernel 0 y * ψ y :=
        congrArg Neg.neg (nkwd_integral_plane (fun y => newtonGradKernel 0 y * ψ y)).symm

/-- The planar weak derivative in the second variable. -/
theorem nkwd_weak1 {ψ : Pl → ℝ} (hψ : IsTest ψ) :
    ∫ y, newtonKernel y * pd 1 ψ y = -∫ y, newtonGradKernel 1 y * ψ y := by
  have hpd := pdTest 1 ψ hψ
  have hF : Integrable (fun y => newtonKernel y * pd 1 ψ y) volume := by
    have := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (μ := volume) (newtonKernelLocInt) hpd.1.continuous hpd.2
    simpa [smul_eq_mul] using this
  have hG : Integrable (fun y => newtonGradKernel 1 y * ψ y) volume := by
    have := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (μ := volume) (newtonGradKernelLocInt 1) hψ.1.continuous hψ.2
    simpa [smul_eq_mul] using this
  have hae : ∀ᵐ a : ℝ, a ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := (0 : ℝ)))] with a ha
    simpa using ha
  calc ∫ y, newtonKernel y * pd 1 ψ y
      = ∫ p : ℝ × ℝ, newtonKernel (planePt p.1 p.2) * pd 1 ψ (planePt p.1 p.2) :=
        nkwd_integral_plane _
    _ = ∫ a, ∫ b, newtonKernel (planePt a b) * pd 1 ψ (planePt a b) :=
        integral_prod _ (nkwd_integrable_plane _ hF)
    _ = ∫ a, -∫ b, newtonGradKernel 1 (planePt a b) * ψ (planePt a b) :=
        integral_congr_ae (hae.mono fun a ha => nkwd_ibp_line1 hψ ha)
    _ = -∫ a, ∫ b, newtonGradKernel 1 (planePt a b) * ψ (planePt a b) := integral_neg _
    _ = -∫ p : ℝ × ℝ, newtonGradKernel 1 (planePt p.1 p.2) * ψ (planePt p.1 p.2) :=
        congrArg Neg.neg (integral_prod _
          (nkwd_integrable_plane (fun y => newtonGradKernel 1 y * ψ y) hG)).symm
    _ = -∫ y, newtonGradKernel 1 y * ψ y :=
        congrArg Neg.neg (nkwd_integral_plane (fun y => newtonGradKernel 1 y * ψ y)).symm

/-- **Leaf `PartII-b:T12/1/1/2/4`.**  `∫ N ∂_kψ = -∫ ∂_kN ψ` for a planar test `ψ`. -/
theorem newtonKernelWeakDeriv : NewtonKernelWeakDeriv := by
  intro k ψ hψ
  fin_cases k
  · exact nkwd_weak0 hψ
  · exact nkwd_weak1 hψ

end UnforcedLeray.Short.IIb.PlaneRiesz
