import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: cylinder tests approximating a smooth periodic field

`bsrCutoffApprox : BsrCutoffApprox` (statement in `BSRep/Defs.lean`): `ψ n x = φ x χ(x₂/(n+1))`
with `χ` the smooth bump of `ContDiffBump` (`rIn = 1`, `rOut = 2`) on `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

theorem bsrCutoffApprox : BsrCutoffApprox := by
  intro d φ hφ hper
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hfs : ContDiff ℝ ∞ (f : ℝ → ℝ) := f.contDiff
  have hfd : Differentiable ℝ (f : ℝ → ℝ) := hfs.differentiable (by simp)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ t : ℝ, ‖fderiv ℝ (f : ℝ → ℝ) t‖ ≤ K :=
    (hfs.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (f.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  -- the cutoff in `η` at the scale `n + 1`
  have hχs : ∀ n : ℕ, ContDiff ℝ ∞ (fun y : ℝ × ℝ => f (y.2 / ((n : ℝ) + 1))) :=
    fun n => hfs.comp (contDiff_snd.div_const _)
  have hχd : ∀ (n : ℕ) (y : ℝ × ℝ),
      ‖fderiv ℝ (fun y : ℝ × ℝ => f (y.2 / ((n : ℝ) + 1))) y‖ ≤ K := by
    intro n y
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h1 : HasFDerivAt (fun y : ℝ × ℝ => y.2 / ((n : ℝ) + 1))
        (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
      have h := (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := y)
      convert h using 1
      funext z
      simp [div_eq_inv_mul]
    have h2 : HasFDerivAt ((f : ℝ → ℝ) ∘ fun y : ℝ × ℝ => y.2 / ((n : ℝ) + 1))
        ((fderiv ℝ (f : ℝ → ℝ) (y.2 / ((n : ℝ) + 1))).comp
          (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) y :=
      HasFDerivAt.comp y (hfd (y.2 / ((n : ℝ) + 1))).hasFDerivAt h1
    show ‖fderiv ℝ ((f : ℝ → ℝ) ∘ fun y : ℝ × ℝ => y.2 / ((n : ℝ) + 1)) y‖ ≤ K
    rw [h2.fderiv]
    have hs : ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := by
      calc ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ‖
          ≤ ‖((n : ℝ) + 1)⁻¹‖ * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ 1 * 1 := by
            gcongr
            · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
              exact inv_le_one_of_one_le₀ hn
            · exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
        _ = 1 := one_mul 1
    calc ‖(fderiv ℝ (f : ℝ → ℝ) (y.2 / ((n : ℝ) + 1))).comp
          (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)‖
        ≤ ‖fderiv ℝ (f : ℝ → ℝ) (y.2 / ((n : ℝ) + 1))‖ *
            ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * 1 := mul_le_mul (hK _) hs (norm_nonneg _) hK0
      _ = K := mul_one K
  refine ⟨fun n y => φ y * f (y.2 / ((n : ℝ) + 1)), K, hK0, fun n => ?_, fun x => ?_,
    fun n j x => ?_⟩
  · -- cylinder tests
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine ⟨hφ.mul (hχs n), fun x => ?_, ⟨2 * ((n : ℝ) + 1), fun x hx => ?_⟩⟩
    · show φ (x.1 + d, x.2) * f (x.2 / ((n : ℝ) + 1)) = φ x * f (x.2 / ((n : ℝ) + 1))
      rw [hper x]
    · have hz : f (x.2 / ((n : ℝ) + 1)) = 0 := by
        refine f.zero_of_le_dist ?_
        show (2 : ℝ) ≤ dist (x.2 / ((n : ℝ) + 1)) 0
        rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hn, le_div_iff₀ hn]
        linarith
      show φ x * f (x.2 / ((n : ℝ) + 1)) = 0
      rw [hz, mul_zero]
  · -- eventual equality near `x`
    obtain ⟨N, hN⟩ := exists_nat_gt |x.2|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hU : IsOpen {y : ℝ × ℝ | |y.2| < (n : ℝ) + 1} :=
      isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
    have hxU : x ∈ {y : ℝ × ℝ | |y.2| < (n : ℝ) + 1} := by
      show |x.2| < (n : ℝ) + 1
      linarith
    have hev : (fun y : ℝ × ℝ => φ y * f (y.2 / ((n : ℝ) + 1))) =ᶠ[𝓝 x] φ := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      have hy' : |y.2| < (n : ℝ) + 1 := hy
      have h1 : f (y.2 / ((n : ℝ) + 1)) = 1 := by
        refine f.one_of_mem_closedBall ?_
        show dist (y.2 / ((n : ℝ) + 1)) 0 ≤ (1 : ℝ)
        rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_le_one hpos]
        exact hy'.le
      rw [h1, mul_one]
    refine ⟨hev.eq_of_nhds, fun j => ?_⟩
    unfold B0579.pd
    rw [hev.fderiv_eq]
  · -- the derivative bound
    have hχx : |f (x.2 / ((n : ℝ) + 1))| ≤ 1 := by
      rw [abs_of_nonneg f.nonneg]
      exact f.le_one
    have hdir : ‖B0579.dir j‖ ≤ 1 := by
      fin_cases j <;> simp [B0579.dir]
    have hmul : fderiv ℝ (fun y : ℝ × ℝ => φ y * f (y.2 / ((n : ℝ) + 1))) x =
        φ x • fderiv ℝ (fun y : ℝ × ℝ => f (y.2 / ((n : ℝ) + 1))) x +
          f (x.2 / ((n : ℝ) + 1)) • fderiv ℝ φ x :=
      fderiv_mul (hφd x) (((hχs n).differentiable (by simp)) x)
    unfold B0579.pd
    rw [hmul, ← Real.norm_eq_abs]
    calc ‖(φ x • fderiv ℝ (fun y : ℝ × ℝ => f (y.2 / ((n : ℝ) + 1))) x +
          f (x.2 / ((n : ℝ) + 1)) • fderiv ℝ φ x) (B0579.dir j)‖
        ≤ ‖φ x • fderiv ℝ (fun y : ℝ × ℝ => f (y.2 / ((n : ℝ) + 1))) x +
          f (x.2 / ((n : ℝ) + 1)) • fderiv ℝ φ x‖ * ‖B0579.dir j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖φ x • fderiv ℝ (fun y : ℝ × ℝ => f (y.2 / ((n : ℝ) + 1))) x +
          f (x.2 / ((n : ℝ) + 1)) • fderiv ℝ φ x‖ * 1 :=
          mul_le_mul_of_nonneg_left hdir (norm_nonneg _)
      _ ≤ ‖φ x • fderiv ℝ (fun y : ℝ × ℝ => f (y.2 / ((n : ℝ) + 1))) x‖ +
          ‖f (x.2 / ((n : ℝ) + 1)) • fderiv ℝ φ x‖ := by
          rw [mul_one]; exact norm_add_le _ _
      _ = |φ x| * ‖fderiv ℝ (fun y : ℝ × ℝ => f (y.2 / ((n : ℝ) + 1))) x‖ +
          |f (x.2 / ((n : ℝ) + 1))| * ‖fderiv ℝ φ x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |φ x| * K + 1 * ‖fderiv ℝ φ x‖ :=
          add_le_add (mul_le_mul_of_nonneg_left (hχd n x) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hχx (norm_nonneg _))
      _ = ‖fderiv ℝ φ x‖ + K * |φ x| := by ring

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.bsrCutoffApprox
