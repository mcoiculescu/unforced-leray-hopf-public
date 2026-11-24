import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.Calc

/-!
# Mean part helper: the derivative of the `sepW` integrand (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Scalar form of `y ↦ ∑_{jk} ∂_kK_{ij}(y - a) c_{jk}` and its derivative. -/
theorem mp_hasFDerivAt_sum (K : Fin 3 → Space → ℝ) (a y : Space)
    (hK : ∀ j, ContDiffAt ℝ 2 (K j) (y - a)) (c : Fin 3 → Fin 3 → ℝ) :
    HasFDerivAt (fun y' : Space => ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (K j) (y' - a) (coordinateVector k) : ℝ) : ℂ) * (c j k : ℂ))
      (∑ j : Fin 3, ∑ k : Fin 3, (c j k : ℂ) • (Complex.ofRealCLM.comp
        ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp
          (fderiv ℝ (fderiv ℝ (K j)) (y - a))))) y := by
  refine HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun k _ => ?_
  have h1 : HasFDerivAt (fderiv ℝ (K j)) (fderiv ℝ (fderiv ℝ (K j)) (y - a)) (y - a) :=
    (((hK j).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (fun y' => fderiv ℝ (K j) (y' - a)) (fderiv ℝ (fderiv ℝ (K j)) (y - a)) y :=
    (h1.comp y ((hasFDerivAt_id y).sub_const a)).congr_fderiv (by simp)
  have h3 : HasFDerivAt (fun y' => fderiv ℝ (K j) (y' - a) (coordinateVector k))
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp
        (fderiv ℝ (fderiv ℝ (K j)) (y - a))) y :=
    (ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).hasFDerivAt.comp y h2
  have h4 := (Complex.ofRealCLM.hasFDerivAt.comp y h3).mul_const (c j k : ℂ)
  exact h4

theorem mp_fderiv_F (ν : ℝ) (hν : 0 < ν) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (l : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1) (z y v : Space) (i : Fin 3) :
    fderiv ℝ (sepDiffF ν μ T τ (l, z)) y v i =
      -2 * ((l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
          ![v, coordinateVector k] : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)) := by
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl.1, hl.2])
  have hsm := sepDiffF_contDiff heatLerayKSmoothAll ν μ T τ hν (l, z) hl
  have hdiff : Differentiable ℝ (sepDiffF ν μ T τ (l, z)) :=
    (contDiff_pi.2 hsm).differentiable (by simp)
  have hcomp : HasFDerivAt (fun y' => sepDiffF ν μ T τ (l, z) y' i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ (sepDiffF ν μ T τ (l, z)) y)) y :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).hasFDerivAt.comp y
      (hdiff y).hasFDerivAt
  have hS := mp_hasFDerivAt_sum (fun j => fun x => heatLerayK (ν * (1 - l ^ 2)) i j x) (l • z) y
    (fun j => ((heatLerayKSmoothAll _ ht i j).contDiffAt).of_le (by norm_cast))
    (fun j k => T (τ + 2 * Real.log l) z j k)
  have hscal : HasFDerivAt (fun y' => sepDiffF ν μ T τ (l, z) y' i)
      ((-2 : ℂ) • (((l : ℂ) ^ (2 * μ + 2)) • (∑ j : Fin 3, ∑ k : Fin 3,
        ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp
        ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp
          (fderiv ℝ (fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)) (y - l • z))))))) y := by
    have := (hS.const_mul ((l : ℂ) ^ (2 * μ + 2))).const_mul (-2 : ℂ)
    simpa [sepDiffF] using this
  have heq := hcomp.unique hscal
  have := congrArg (fun L => L v) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at this
  rw [this]
  simp only [smul_apply, sum_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, ContinuousLinearMap.apply_apply, iteratedFDeriv_two_apply]
  congr 2
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp
  ring

end UnforcedLeray.Short.IIIa

end
