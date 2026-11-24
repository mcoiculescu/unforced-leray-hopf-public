import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1
import UnforcedLeray.Short.PartIIIa.T20_6_RealBiotSavartUniform
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique

/-!
# `PartIII-a:T21/2/3/1/9/1/3` (`LadKernelVel`)

Source: `the November 2 reference manuscript` lines 3236-3240, 3052-3057.

Proof. `CTE.realBiotSavartUniform` (at `m = 3`) gives a complex Biot-Savart velocity `u` of `ψ`.
Its imaginary part is a Biot-Savart velocity of the zero vorticity, so vanishes a.e. by
`CTE.isBiotSavart_unique`; its real part satisfies the clauses of `IsKernelBiotSavart` (`meanShear`
vanishes for `∫ ψ = 0`) by taking real parts of the clauses of `IsBiotSavart`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace KernelVelAux

lemma bs_congr_u {c : ℝ} {om : ℝ × ℝ → ℂ} {u u' : ℝ × ℝ → Fin 2 → ℂ}
    (h : IsBiotSavart c om u) (he : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), u x = u' x) :
    IsBiotSavart c om u' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => (h1 j).ae_eq ?_, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · filter_upwards [he] with x hx using by rw [hx]
  · refine (integral_congr_ae ?_).trans (h2 ψ hψ)
    filter_upwards [he] with x hx
    rw [hx]
  · refine (h3 ψ hψ).trans (integral_congr_ae ?_)
    filter_upwards [he] with x hx
    rw [hx]

lemma clauses {c : ℝ} {ψ : ℝ × ℝ → ℝ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (h : IsBiotSavart c (fun x => ((ψ x : ℝ) : ℂ)) u) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) :
    (∫ x in B0579.cell c, ((u x 0).re * B0579.pd 0 φ x + (u x 1).re * B0579.pd 1 φ x) = 0) ∧
    (∫ x in B0579.cell c, ψ x * φ x =
      ∫ x in B0579.cell c, ((u x 0).re * B0579.pd 1 φ x - (u x 1).re * B0579.pd 0 φ x)) ∧
    (∫ x in B0579.cell c, ((u x 0).im * B0579.pd 0 φ x + (u x 1).im * B0579.pd 1 φ x) = 0) ∧
    (0 = ∫ x in B0579.cell c, ((u x 0).im * B0579.pd 1 φ x - (u x 1).im * B0579.pd 0 φ x)) := by
  have I : ∀ j j', Integrable (fun x => u x j * ((B0579.pd j' φ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) := fun j j' => BSSubAux.integrable_u_pd h.1 hφ j j'
  have hs : Integrable (fun x => u x 0 * ((B0579.pd 0 φ x : ℝ) : ℂ) + u x 1 * ((B0579.pd 1 φ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) := (I 0 0).add (I 1 1)
  have hd : Integrable (fun x => u x 0 * ((B0579.pd 1 φ x : ℝ) : ℂ) - u x 1 * ((B0579.pd 0 φ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) := (I 0 1).sub (I 1 0)
  have e2 := h.2.1 φ hφ
  have e3 := h.2.2 φ hφ
  have hψφ : ∫ x in B0579.cell c, ((ψ x : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) =
      ((∫ x in B0579.cell c, ψ x * φ x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; simp
  rw [hψφ] at e3
  have r1 := integral_re hs
  have r2 := integral_re hd
  have i1 := integral_im hs
  have i2 := integral_im hd
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at r1 r2 i1 i2
  rw [e2] at r1 i1
  rw [← e3] at r2 i2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using r1
  · simpa using r2.symm
  · simpa using i1
  · simpa using i2.symm

end KernelVelAux

open KernelVelAux in
theorem ladKernelVel : LadKernelVel := by
  intro c ψ hc hψ hz
  have : Fact (0 < c) := ⟨by linarith⟩
  have hc0 : 0 < c := by linarith
  obtain ⟨C, -, hC⟩ := CTE.realBiotSavartUniform 3 (by norm_num)
  set U : B0579.X c 3 := B0579.testLp c 3 hψ with hU
  have hae : (U : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell c)] ψ := B0579.coeFn_testLp c 3 hψ
  have hUz : ∫ x in B0579.cell c, U x = 0 := by
    rw [integral_congr_ae hae]; exact hz
  obtain ⟨u, hu, -⟩ := hC c hc U hUz
  have hu' : IsBiotSavart c (fun x => ((ψ x : ℝ) : ℂ)) u := by
    refine isBiotSavart_congr_ae hu ?_
    filter_upwards [hae] with x hx
    simp [hx]
  have h1 := hu'.1
  -- imaginary part is a Biot-Savart velocity of zero
  have him : IsBiotSavart c (fun _ => (0 : ℂ)) (fun x j => (((u x j).im : ℝ) : ℂ)) := by
    refine ⟨fun j => ((h1 j).im).ofReal, fun φ hφ => ?_, fun φ hφ => ?_⟩
    · have := (clauses hu' hφ).2.2.1
      have key : ∫ x in B0579.cell c, (((u x 0).im : ℝ) : ℂ) * ((B0579.pd 0 φ x : ℝ) : ℂ) +
          (((u x 1).im : ℝ) : ℂ) * ((B0579.pd 1 φ x : ℝ) : ℂ) =
          ((∫ x in B0579.cell c, ((u x 0).im * B0579.pd 0 φ x + (u x 1).im * B0579.pd 1 φ x) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]; congr 1; funext x; push_cast; ring
      beta_reduce
      rw [key, this]; simp
    · have := (clauses hu' hφ).2.2.2
      have key : ∫ x in B0579.cell c, (((u x 0).im : ℝ) : ℂ) * ((B0579.pd 1 φ x : ℝ) : ℂ) -
          (((u x 1).im : ℝ) : ℂ) * ((B0579.pd 0 φ x : ℝ) : ℂ) =
          ((∫ x in B0579.cell c, ((u x 0).im * B0579.pd 1 φ x - (u x 1).im * B0579.pd 0 φ x) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]; congr 1; funext x; push_cast; ring
      beta_reduce
      simp only [zero_mul, integral_zero]
      rw [key, ← this]; simp
  have hzero : IsBiotSavart c (fun _ => (0 : ℂ)) (fun _ _ => (0 : ℂ)) := by
    refine ⟨fun j => MemLp.zero, fun φ hφ => by simp, fun φ hφ => by simp⟩
  have huni := CTE.isBiotSavart_unique c hc0 _ _ _ him hzero
  have hureal : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      u x = fun j => (((u x j).re : ℝ) : ℂ) := by
    filter_upwards [huni] with x hx
    funext j
    have := congrFun hx j
    apply Complex.ext <;> simp
    simpa using this
  refine ⟨fun x j => (u x j).re, ⟨fun j => ?_, fun φ hφ => (clauses hu' hφ).1,
    fun φ hφ => (clauses hu' hφ).2.1⟩, bs_congr_u hu' hureal⟩
  · rw [hz]
    have : (fun x => (u x j).re - meanShear c 0 x j) = fun x => (u x j).re := by
      funext x; simp [meanShear]
    rw [this]
    exact (h1 j).re

end UnforcedLeray.Short.IIIa
