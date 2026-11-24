import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_1

/-!
# `PartII-b:T10/6/1/1`: `GActInv` (`gC g⁻¹ ∘ gC g = id`, SP 1912-1915)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.GActLeaf1

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem realC_single_leaf1 (k : Fin 3) :
    UnforcedLeray.B0412.realC (EuclideanSpace.single k (1 : ℝ)) =
      EuclideanSpace.single k (1 : ℂ) := by
  ext i
  by_cases h : i = k <;> simp [UnforcedLeray.B0412.realC_apply, Pi.single_apply, h]

theorem gC_symm_gC_leaf1 (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) :
    UnforcedLeray.B0412.gC g.symm (UnforcedLeray.B0412.gC g v) = v := by
  have hbasis : ∀ k : Fin 3,
      UnforcedLeray.B0412.gC g.symm
        (UnforcedLeray.B0412.gC g (EuclideanSpace.single k (1 : ℂ))) =
        EuclideanSpace.single k (1 : ℂ) := by
    intro k
    rw [← realC_single_leaf1 k, UnforcedLeray.B0412.gC_realC,
      UnforcedLeray.B0412.gC_realC, LinearIsometryEquiv.symm_apply_apply]
  have hv : v = ∑ k : Fin 3, v k • EuclideanSpace.single k (1 : ℂ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, hbasis]
  exact hv.symm

end UnforcedLeray.Short.IIb.GActLeaf1

theorem gActInv : UnforcedLeray.Short.IIb.GActInv := by
  unfold UnforcedLeray.Short.IIb.GActInv
  intro g Φ
  funext x
  simp only [UnforcedLeray.Short.IIb.gAct, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.symm_apply_apply, Prod.mk.eta]
  exact UnforcedLeray.Short.IIb.GActLeaf1.gC_symm_gC_leaf1 g (Φ x)
