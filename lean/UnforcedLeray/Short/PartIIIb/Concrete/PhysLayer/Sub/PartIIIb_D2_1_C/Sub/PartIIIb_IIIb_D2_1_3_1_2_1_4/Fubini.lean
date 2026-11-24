import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4

/-!
# `adjDomGradFubini`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480:
the slice-wise weak derivative identity applied to `θ = Θ(τ, ·)` and integrated over `τ ∈ (0, P]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem dy_apply_eq_fderiv_slice {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ)
    (j : Fin 3) (t : ℝ) (y : Space) (i : Fin 3) :
    dy j Θ (t, y) i = fderiv ℝ (fun z => Θ (t, z) i) y (EuclideanSpace.single j (1 : ℝ)) := by
  have hd : DifferentiableAt ℝ Θ (t, y) :=
    (hΘ.smooth.differentiable (by simp)) (t, y)
  have hs : HasFDerivAt (fun z : Space => (t, z)) (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  let pr : CVec3 →L[ℝ] ℂ := ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ)).restrictScalars ℝ
  have h1 : HasFDerivAt (fun z : Space => Θ (t, z))
      ((fderiv ℝ Θ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hd.hasFDerivAt.comp y hs
  have h2 := pr.hasFDerivAt.comp y h1
  have := h2.fderiv
  simp only [dy]
  rw [show (fun z => Θ (t, z) i) = pr ∘ (fun z : Space => Θ (t, z)) from rfl, this]
  simp [pr, coordinateVector]

theorem adjDomGradFubini : AdjDomGradFubini := by
  intro P hP Φ D j _ _ hslice Θ hΘ
  unfold pairF phaseInt
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  have hae := hslice
  filter_upwards [hae] with t ht _
  have hθ : ContDiff ℝ ∞ (fun z : Space => Θ (t, z)) :=
    hΘ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun z : Space => Θ (t, z)) := by
    obtain ⟨R, hR⟩ := hΘ.bounded_support
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) R) ?_
    intro y hy
    by_contra hn
    exact hy (hR t y (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hn))
  have hid := ht _ hθ hc
  have e1 : ∀ y : Space, dotL ((-dy j Θ) (t, y)) (Φ (t, y))
      = -(∑ i : Fin 3, Φ (t, y) i *
          fderiv ℝ (fun z => Θ (t, z) i) y (EuclideanSpace.single j (1 : ℝ))) := by
    intro y
    rw [dotL_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.neg_apply, PiLp.neg_apply, dy_apply_eq_fderiv_slice hΘ]
    ring
  have e2 : ∀ y : Space, dotL (Θ (t, y)) (D (t, y)) = ∑ i : Fin 3, D (t, y) i * Θ (t, y) i := by
    intro y
    rw [dotL_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [e1, e2]
  rw [integral_neg]
  have this : (∫ y : Space, ∑ i : Fin 3, Φ (t, y) i *
          fderiv ℝ (fun z => Θ (t, z) i) y (EuclideanSpace.single j (1 : ℝ)))
      = ∫ y : Space, ∑ i : Fin 3, Φ (t, y) i *
          fderiv ℝ (fun z => (fun z => Θ (t, z)) z i) y (EuclideanSpace.single j (1 : ℝ)) := rfl
  rw [this]
  exact hid

end UnforcedLeray.Short.PartIIIb.Concrete
