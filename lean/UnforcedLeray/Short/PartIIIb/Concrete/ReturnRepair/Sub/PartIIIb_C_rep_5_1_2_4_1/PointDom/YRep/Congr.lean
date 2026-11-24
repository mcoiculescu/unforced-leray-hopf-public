import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs

/-!
# `physDmu` depends only on the two slices through the point
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_physDmu_congr (ν μ : ℝ) (X₁ X₂ : ℝ → Space → Space) (τ : ℝ) (y : Space)
    (ht : (fun t => X₁ t y) =ᶠ[𝓝 τ] fun t => X₂ t y) (hy : X₁ τ =ᶠ[𝓝 y] X₂ τ) :
    physDmu ν μ X₁ τ y = physDmu ν μ X₂ τ y := by
  have h1 : fderiv ℝ (X₁ τ) y = fderiv ℝ (X₂ τ) y := hy.fderiv_eq
  have h2 : fderiv ℝ (X₁ τ) =ᶠ[𝓝 y] fderiv ℝ (X₂ τ) := hy.fderiv
  have h3 : physLap (X₁ τ) y = physLap (X₂ τ) y := by
    unfold physLap physPd2 physPd
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (fun y' => fderiv ℝ (X₁ τ) y' (coordinateVector j)) =ᶠ[𝓝 y]
        fun y' => fderiv ℝ (X₂ τ) y' (coordinateVector j) :=
      h2.mono fun y' hy' => by show fderiv ℝ (X₁ τ) y' (coordinateVector j) = _; rw [hy']
    rw [this.fderiv_eq]
  unfold physDmu
  rw [ht.deriv_eq, h1, h3, hy.self_of_nhds]

end UnforcedLeray.Short.PartIIIb.Concrete

end
