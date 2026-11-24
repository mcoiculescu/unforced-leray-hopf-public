import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEWeak

/-!
# `GERaw` from the derivative of the raw residual (source 2542-2551, 1206-1222)

Task `PartIII-b:C/ward/12/3/1/2/4`.  Source of record
`the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

/-- **Derivative of the raw residual is in `Y_p`** (source 2542-2551 with the `U_raw` derivative
bounds 1206-1222: the unprojected derivatives of the train complete source are
`O(ϱ^{-3-k}(1+|y₃|/ϱ)^{-N})`, whose `p`th integral is finite; the raw field is the concrete
`p.Ufun`).  For each `j` there is `F ∈ Y_p` with
`⟪L₀ᵗ∂_jΦ, U_raw⟫ - ⟪(U_raw·∇)∂_jΦ, U_raw⟫ = ⟪Φ, F⟫` on solenoidal tests `Φ`
(`F` is minus the `j`-th derivative of the pointwise raw residual, after one integration
by parts, using `∂_j L₀ᵗ = L₀ᵗ∂_j + ½∂_j`). -/
def RawDerivRes : Prop := GERegime fun p _ _ =>
  ∀ j : Fin 3, ∃ F : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
    pairF p.period (UnforcedLeray.B0411.L0T p.ν (dy j Φ)) p.Ufun -
        pairF p.period (advT p.Ufun (dy j Φ)) p.Ufun =
      phasePair p.period UnforcedLeray.B0412.q0E Φ F

theorem gERaw_of (h : RawDerivRes) : GERaw := by
  refine geRegime_bind h h ?_
  intro p z g _ hA _ gF hRel j
  obtain ⟨F, hF⟩ := hA j
  refine ⟨F, fun Φ hΦ => ?_⟩
  rw [hRel (dy j Φ) (gEW_isSolTest_dy hΦ j)]
  exact hF Φ hΦ

end UnforcedLeray.Short.PartIIIb.Concrete
