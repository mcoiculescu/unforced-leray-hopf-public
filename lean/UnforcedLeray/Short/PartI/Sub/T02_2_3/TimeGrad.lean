import UnforcedLeray.Short.PartI.Sub.T02_2_3

/-!
# Part I, task `PartI:T02/2/3`: the time-integrated pressure gradient is bounded (conditional)

Source of record: `the November 2 reference manuscript`, line 447 and line 277.

`pbTimeGrad_of` derives `PbTimeGrad` (`Sub/T02_2_3.lean`) from `PbConvViscBound` and
`PbMomentumIntegrated`: `‖∫_a^b ∇p dσ‖ ≤ ‖v b z‖ + ‖v a z‖ + |G| T ≤ 2 M₀ + |G| T`, and the two
coordinates of the vector integral are the integrals of `∂_q p`, `∂_η p`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **`PbTimeGrad` from `PbConvViscBound` and `PbMomentumIntegrated`.** -/
theorem pbTimeGrad_of (hA : PbConvViscBound) (hB : PbMomentumIntegrated) : PbTimeGrad := by
  intro ν c T v p h
  obtain ⟨G, hG⟩ := hA ν c T v p h
  obtain ⟨M0, hM0⟩ := h.bounded 0
  have hv0 : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, ‖v s z‖ ≤ M0 := by
    intro s hs z
    have := hM0 s hs z
    rwa [norm_iteratedFDeriv_zero] at this
  refine ⟨2 * M0 + |G| * T, fun a ha b hb hab z => ?_⟩
  obtain ⟨hint, heq⟩ := hB ν c T v p h a ha b hb hab z
  have hX : ‖∫ σ in a..b, (Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z)‖
      ≤ |G| * T := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun σ => Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z)
      (a := a) (b := b) (C := |G|)
      (fun σ hσ => by
        rw [Set.uIoc_of_le hab] at hσ
        exact (hG σ ⟨ha.1.trans hσ.1.le, hσ.2.trans hb.2⟩ z).trans (le_abs_self G))
    refine h1.trans ?_
    have hba : |b - a| ≤ T := by
      rw [abs_of_nonneg (sub_nonneg.2 hab)]
      linarith [ha.1, hb.2]
    exact mul_le_mul_of_nonneg_left hba (abs_nonneg G)
  have hnorm : ‖∫ σ in a..b, Train.gradS (p σ) z‖ ≤ 2 * M0 + |G| * T := by
    rw [heq]
    calc ‖-(v b z - v a z) - ∫ σ in a..b,
            (Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z)‖
        ≤ ‖-(v b z - v a z)‖ + ‖∫ σ in a..b,
            (Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z)‖ := norm_sub_le _ _
      _ ≤ (‖v b z‖ + ‖v a z‖) + |G| * T := by
          rw [norm_neg]
          exact add_le_add (norm_sub_le _ _) hX
      _ ≤ 2 * M0 + |G| * T := by
          have h1 := hv0 b hb z
          have h2 := hv0 a ha z
          linarith
  have hcomm : ∀ i : Fin 2, (∫ σ in a..b, Train.gradS (p σ) z) i =
      ∫ σ in a..b, (Train.gradS (p σ) z) i := fun i =>
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).intervalIntegral_comp_comm hint).symm
  have hcoord : ∀ i : Fin 2, |∫ σ in a..b, (Train.gradS (p σ) z) i| ≤ 2 * M0 + |G| * T := by
    intro i
    rw [← hcomm i, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ i).trans hnorm
  constructor
  · have := hcoord 0
    simpa [Train.gradS] using this
  · have := hcoord 1
    simpa [Train.gradS] using this

end UnforcedLeray.Short.PartI
