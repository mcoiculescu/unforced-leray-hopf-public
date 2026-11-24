import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_8

/-!
# Part II-a, task `PartII-a:N02/4/4/8/2`: `NzFpMeridOpS`

Source of record: `the November 2 reference manuscript`, lines 1713-1727, 1744-1745.
The coordinate `i` of `opS^[α] (finite mode sum)` (`α ∈ {0, 1}`) is `opS^[α]` of the scalar mode sum of
the `i`-th coordinates: coordinates are continuous linear, so they commute with `fderiv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem nzFpMeridOpS : UnforcedLeray.Short.PartIIa.NzFpMeridOpS := by
  unfold UnforcedLeray.Short.PartIIa.NzFpMeridOpS
  intro c M a ha α hα i p
  have hcoord : ∀ q : Profile, nzModeSum c M a q i = nzModeSum c M (fun n x => a n x i) q := by
    intro q
    unfold nzModeSum
    have hL : ∀ (s : Finset ℤ) (f : ℤ → MeridC), (∑ n ∈ s, f n) i = ∑ n ∈ s, f n i := by
      intro s f
      have h := map_sum (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ) f s
      simpa using h
    rw [hL]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    first
    | rfl
    | simp [PiLp.smul_apply, smul_eq_mul]
  have hα' : α = 0 ∨ α = 1 := by
    have := Finset.mem_range.mp hα
    omega
  rcases hα' with rfl | rfl
  · simp only [Function.iterate_zero, id_eq]
    exact hcoord p
  · simp only [Function.iterate_one]
    have hterm : ∀ n ∈ M, Differentiable ℝ (fun p : Profile =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
          a n (p.1, p.2.2)) := by
      intro n hn
      have hq : Differentiable ℝ (fun p : Profile =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ))) := by
        fun_prop
      have hG : Differentiable ℝ (fun p : Profile => a n (p.1, p.2.2)) :=
        (((ha n hn).differentiable (by simp)).comp
          (differentiable_fst.prodMk (differentiable_snd.comp differentiable_snd)))
      exact hq.smul hG
    have hFd : Differentiable ℝ (nzModeSum c M a) := by
      unfold nzModeSum
      exact Differentiable.fun_sum hterm
    have hGF : nzModeSum c M (fun n x => a n x i) = fun q => nzModeSum c M a q i :=
      funext (fun q => (hcoord q).symm)
    have hG_fderiv : fderiv ℝ (fun q => nzModeSum c M a q i) p =
        ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ).comp
          (fderiv ℝ (nzModeSum c M a) p) :=
      ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp p
        (hFd p).hasFDerivAt |>.fderiv
    show (p.1 • fderiv ℝ (nzModeSum c M a) p (1, 0, 0)) i =
      p.1 • fderiv ℝ (nzModeSum c M (fun n x => a n x i)) p (1, 0, 0)
    rw [hGF, hG_fderiv]
    first
    | rfl
    | simp [PiLp.smul_apply, smul_eq_mul]

end UnforcedLeray.Short.PartIIa
