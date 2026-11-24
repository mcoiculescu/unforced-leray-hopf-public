import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- First derivative bound in a fixed direction. -/
theorem nzfpNorm1 (f : ℝ × ℝ → ℂ) (x v : ℝ × ℝ) :
    ‖fderiv ℝ f x v‖ ≤ ‖iteratedFDeriv ℝ 1 f x‖ * ‖v‖ := by
  rw [norm_iteratedFDeriv_one]
  exact (fderiv ℝ f x).le_opNorm v

/-- Second derivative bound in two directions. -/
theorem nzfpNorm2 (f : ℝ × ℝ → ℂ) (x w v : ℝ × ℝ) :
    ‖fderiv ℝ (fderiv ℝ f) x w v‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * (‖w‖ * ‖v‖) := by
  have h := (iteratedFDeriv ℝ 2 f x).le_opNorm (![w, v])
  rw [iteratedFDeriv_two_apply, Fin.prod_univ_two] at h
  simpa using h

/-- The `η`-derivative `∂_η φ` is differentiated in `s` as the second derivative. -/
theorem nzfpEtaDerivS (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (x : ℝ × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ φ y ((0:ℝ), (1:ℝ))) x ((1:ℝ), (0:ℝ)) =
      fderiv ℝ (fderiv ℝ φ) x ((1:ℝ), (0:ℝ)) ((0:ℝ), (1:ℝ)) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by simp)
  have hL : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
    ((hD.differentiable (by simp)) x).hasFDerivAt
  have hA := hL.clm_apply (hasFDerivAt_const ((0:ℝ), (1:ℝ)) x)
  have hf : fderiv ℝ (fun y => fderiv ℝ φ y ((0:ℝ), (1:ℝ))) x =
      (fderiv ℝ φ x).comp 0 + (fderiv ℝ (fderiv ℝ φ) x).flip ((0:ℝ), (1:ℝ)) := hA.fderiv
  rw [hf]
  simp

/-- Band property of `∂_η φ`: if `φ` vanishes on the lines `s ∉ [s0,s1]`, so does `∂_η φ`. -/
theorem nzfpEtaBand (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (s0 s1 : ℝ)
    (hband : ∀ x : ℝ × ℝ, φ x ≠ 0 → x.1 ∈ Icc s0 s1) (x : ℝ × ℝ) (hx : x.1 ∉ Icc s0 s1) :
    fderiv ℝ φ x ((0:ℝ), (1:ℝ)) = 0 := by
  have hz : (fun t : ℝ => φ (x.1, t)) = fun _ => (0 : ℂ) := by
    funext t
    by_contra h
    exact hx (hband (x.1, t) h)
  have hd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    ((hφ.differentiable (by simp)) x).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((x.1, t) : ℝ × ℝ)) ((0:ℝ), (1:ℝ)) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id' x.2)
  have hl : HasDerivAt (fun t : ℝ => φ (x.1, t)) (fderiv ℝ φ x ((0:ℝ), (1:ℝ))) x.2 :=
    hd.comp_hasDerivAt x.2 hline
  rw [hz] at hl
  exact hl.unique (hasDerivAt_const x.2 (0:ℂ))

theorem nzFpDecay1 : UnforcedLeray.Short.PartIIa.NzFpDecay1 := by
  intro k φ hφ
  obtain ⟨hs, hb, κ, C, hκ, hbd⟩ := hφ
  obtain ⟨s0, s1, hs0, hband⟩ := hb
  have h10 : ‖((1:ℝ), (0:ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
  have h01 : ‖((0:ℝ), (1:ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
  have hp : ‖((1:ℝ), (0:ℝ))‖ * ‖((0:ℝ), (1:ℝ))‖ ≤ 1 := by
    nlinarith [norm_nonneg ((1:ℝ), (0:ℝ)), norm_nonneg ((0:ℝ), (1:ℝ))]
  refine ⟨?_, ?_, ?_⟩
  · -- NzDecay1 φ
    refine ⟨hs, ⟨s0, s1, hs0, hband⟩, κ, C, hκ, fun x => ⟨?_, ?_⟩⟩
    · have h0 := hbd x 0 (Nat.zero_le _)
      rw [norm_iteratedFDeriv_zero] at h0
      exact h0
    · have h1 := hbd x 1 (by norm_num)
      calc ‖fderiv ℝ φ x ((1:ℝ), (0:ℝ))‖
          ≤ ‖iteratedFDeriv ℝ 1 φ x‖ * ‖((1:ℝ), (0:ℝ))‖ := nzfpNorm1 φ x _
        _ ≤ ‖iteratedFDeriv ℝ 1 φ x‖ := mul_le_of_le_one_right (norm_nonneg _) h10
        _ ≤ C * Real.exp (-κ * |x.2|) := h1
  · -- NzDecay1 (∂_η φ)
    have hD : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y ((0:ℝ), (1:ℝ))) := by
      have hD' := (contDiff_infty_iff_fderiv.mp hs).2
      exact hD'.clm_apply contDiff_const
    refine ⟨hD, ⟨s0, s1, hs0, ?_⟩, κ, C, hκ, fun x => ⟨?_, ?_⟩⟩
    · intro x hx
      by_contra hI
      exact hx (nzfpEtaBand φ hs s0 s1 hband x hI)
    · have h1 := hbd x 1 (by norm_num)
      calc ‖fderiv ℝ φ x ((0:ℝ), (1:ℝ))‖
          ≤ ‖iteratedFDeriv ℝ 1 φ x‖ * ‖((0:ℝ), (1:ℝ))‖ := nzfpNorm1 φ x _
        _ ≤ ‖iteratedFDeriv ℝ 1 φ x‖ := mul_le_of_le_one_right (norm_nonneg _) h01
        _ ≤ C * Real.exp (-κ * |x.2|) := h1
    · rw [nzfpEtaDerivS φ hs x]
      have h2 := hbd x 2 (by norm_num)
      calc ‖fderiv ℝ (fderiv ℝ φ) x ((1:ℝ), (0:ℝ)) ((0:ℝ), (1:ℝ))‖
          ≤ ‖iteratedFDeriv ℝ 2 φ x‖ * (‖((1:ℝ), (0:ℝ))‖ * ‖((0:ℝ), (1:ℝ))‖) := nzfpNorm2 φ x _ _
        _ ≤ ‖iteratedFDeriv ℝ 2 φ x‖ := mul_le_of_le_one_right (norm_nonneg _) hp
        _ ≤ C * Real.exp (-κ * |x.2|) := h2
  · -- NzDecay1 (I * (k * φ))
    refine ⟨contDiff_const.mul (contDiff_const.mul hs), ⟨s0, s1, hs0, ?_⟩, κ, |k| * C, hκ,
      fun x => ⟨?_, ?_⟩⟩
    · intro x hx
      exact hband x (fun h0 => hx (by simp [h0]))
    · have hd : DifferentiableAt ℝ φ x := (hs.differentiable (by simp)) x
      calc ‖Complex.I * ((k : ℂ) * φ x)‖ = |k| * ‖φ x‖ := by
            simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |k| * (C * Real.exp (-κ * |x.2|)) := mul_le_mul_of_nonneg_left (by
            have h0 := hbd x 0 (Nat.zero_le _)
            rw [norm_iteratedFDeriv_zero] at h0
            exact h0) (abs_nonneg k)
        _ = |k| * C * Real.exp (-κ * |x.2|) := by ring
    · have hd : DifferentiableAt ℝ φ x := (hs.differentiable (by simp)) x
      have hf : fderiv ℝ (fun y => Complex.I * ((k : ℂ) * φ y)) x =
          Complex.I • ((k : ℂ) • fderiv ℝ φ x) := by
        rw [fderiv_const_mul (hd.const_mul _), fderiv_const_mul hd]
      have hkey : ‖fderiv ℝ (fun y => Complex.I * ((k : ℂ) * φ y)) x ((1:ℝ), (0:ℝ))‖
          = |k| * ‖fderiv ℝ φ x ((1:ℝ), (0:ℝ))‖ := by
        rw [hf]
        simp [Complex.norm_real, Real.norm_eq_abs]
      have h1 := hbd x 1 (by norm_num)
      have hb1 : ‖fderiv ℝ φ x ((1:ℝ), (0:ℝ))‖ ≤ C * Real.exp (-κ * |x.2|) := by
        calc ‖fderiv ℝ φ x ((1:ℝ), (0:ℝ))‖
            ≤ ‖iteratedFDeriv ℝ 1 φ x‖ * ‖((1:ℝ), (0:ℝ))‖ := nzfpNorm1 φ x _
          _ ≤ ‖iteratedFDeriv ℝ 1 φ x‖ := mul_le_of_le_one_right (norm_nonneg _) h10
          _ ≤ C * Real.exp (-κ * |x.2|) := h1
      rw [hkey]
      calc |k| * ‖fderiv ℝ φ x ((1:ℝ), (0:ℝ))‖ ≤ |k| * (C * Real.exp (-κ * |x.2|)) :=
            mul_le_mul_of_nonneg_left hb1 (abs_nonneg k)
        _ = |k| * C * Real.exp (-κ * |x.2|) := by ring

end UnforcedLeray.Short.PartIIa
