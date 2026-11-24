import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinLeibniz
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinPairDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinAdjoint
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinRawDVSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinConvTPhaseTest
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection

/-!
# `GELin`: pointwise integration by parts (source 2525-2533)

Task `PartIII-b:C/ward/12/3/1/2/6/7`.  Source of record
`the November 2 reference manuscript` (Assemble).

Let `U = raw`, `Θ = convT U Φ`.  Leibniz gives `∂_jΘ = convT U (∂_jΦ) + convT (∂_jU) Φ`.
Pairing `∂_jΘ` against `w` and using the weak derivative (`gELinPairDeriv`) and transposition
(`gELinAdjoint`) gives the claim, with `GELinField = -S(U, g_j, h_j) - S(∂_jU, w, g)` by
`gELinField_eq`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseCell)

/-- Negation in the second argument of `pairF`. -/
theorem gELinIBP_pairF_neg (P : ℝ) [Fact (0 < P)] (F G : ℝ × UnforcedLeray.Space → CVec3) :
    pairF P F (fun x => -G x) = -pairF P F G := by
  simp only [pairF, UnforcedLeray.Cons.C03.Concrete.phaseInt, map_neg, integral_neg, smul_neg]

theorem gELinIBP : GELinIBP := by
  intro p z g h j hU hw hgh Φ hΦ
  have hRDV : IsSmoothPer p.period (rawDV p j) := gELinRawDVSmooth p hU j
  have hLeib := gELinLeibniz p hU j Φ hΦ.smooth
  have hdyΦ : IsPhaseTest p.period (dy j Φ) := hΦ.dy j
  have hsplit : dy j (convT p.raw Φ) = fun x => convT p.raw (dy j Φ) x + convT (rawDV p j) Φ x := by
    funext x
    exact congrFun hLeib x
  have hΘ : IsPhaseTest p.period (convT p.raw Φ) :=
    gELinConvTPhaseTest p.period p.raw hU Φ hΦ
  -- transposition identities and integrability
  have hA := gELinAdjoint p.period p.raw hU (g j) (h j) hgh Φ hΦ
  have hB := gELinAdjoint p.period (rawDV p j) hRDV (p.wOf z) g hw Φ hΦ
  have hI1 := (gELinAdjoint p.period p.raw hU (p.wOf z) g hw (dy j Φ) hdyΦ).2.1
  have hI2 := hB.2.1
  -- splitting of the pairing in the first argument
  have e1 : pairF p.period (dy j (convT p.raw Φ)) (fun x => rep (p.wOf z) x.1 x.2) =
      pairF p.period (convT p.raw (dy j Φ)) (fun x => rep (p.wOf z) x.1 x.2) +
        pairF p.period (convT (rawDV p j) Φ) (fun x => rep (p.wOf z) x.1 x.2) := by
    rw [hsplit]
    have hFG : Integrable (fun x => dotL (convT p.raw (dy j Φ) x + convT (rawDV p j) Φ x)
        (rep (p.wOf z) x.1 x.2)) (volume.restrict (phaseCell p.period)) := by
      refine (hI1.add hI2).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.add_apply, Pi.neg_apply, map_add, map_neg, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
    exact UnforcedLeray.Cons.C03.Concrete.pairF_add_left_of_integrable
      (F := convT p.raw (dy j Φ)) (G := convT (rawDV p j) Φ)
      (H := fun x => rep (p.wOf z) x.1 x.2) hI1 hI2 hFG
  -- weak derivative and transposition
  have e2 := gELinPairDeriv p.period (p.wOf z) (g j) j (hw j) (convT p.raw Φ) hΘ
  have e3 := hB.2.2
  have e4 := hA.2.2
  have e5 : pairF p.period (convT p.raw (dy j Φ)) (fun x => rep (p.wOf z) x.1 x.2) =
      -pairF p.period Φ (convTAdj p.raw (g j) (h j)) -
        pairF p.period Φ (convTAdj (rawDV p j) (p.wOf z) g) := by
    linear_combination -e1 + e2 - e4 - e3
  -- the field
  have hfield : GELinField p z g h j = fun x =>
      -(convTAdj p.raw (g j) (h j) x) + -(convTAdj (rawDV p j) (p.wOf z) g x) := by
    rw [gELinField_eq]
    funext x
    simp only [sub_eq_add_neg]
  have hA1 := hA.1
  have hC1 := hB.1
  have hF : Integrable (fun x => dotL (Φ x) (-(convTAdj p.raw (g j) (h j) x)))
      (volume.restrict (phaseCell p.period)) := by
    refine (hA1.neg).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, Pi.neg_apply, map_add, map_neg, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
  have hG : Integrable (fun x => dotL (Φ x) (-(convTAdj (rawDV p j) (p.wOf z) g x)))
      (volume.restrict (phaseCell p.period)) := by
    refine (hC1.neg).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, Pi.neg_apply, map_add, map_neg, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
  have hFG : Integrable (fun x => dotL (Φ x)
      (-(convTAdj p.raw (g j) (h j) x) + -(convTAdj (rawDV p j) (p.wOf z) g x)))
      (volume.restrict (phaseCell p.period)) := by
    refine (hA1.neg.add hC1.neg).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, Pi.neg_apply, map_add, map_neg, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
  have hsum : pairF p.period Φ (fun x =>
      -(convTAdj p.raw (g j) (h j) x) + -(convTAdj (rawDV p j) (p.wOf z) g x)) =
      pairF p.period Φ (fun x => -(convTAdj p.raw (g j) (h j) x)) +
        pairF p.period Φ (fun x => -(convTAdj (rawDV p j) (p.wOf z) g x)) :=
    UnforcedLeray.Cons.C03.Concrete.pairF_add_right_of_integrable
      (F := fun x => -(convTAdj p.raw (g j) (h j) x))
      (G := fun x => -(convTAdj (rawDV p j) (p.wOf z) g x)) (H := Φ) hF hG hFG
  have hn1 : pairF p.period Φ (fun x => -(convTAdj p.raw (g j) (h j) x)) =
      -pairF p.period Φ (convTAdj p.raw (g j) (h j)) :=
    gELinIBP_pairF_neg _ _ _
  have hn2 : pairF p.period Φ (fun x => -(convTAdj (rawDV p j) (p.wOf z) g x)) =
      -pairF p.period Φ (convTAdj (rawDV p j) (p.wOf z) g) :=
    gELinIBP_pairF_neg _ _ _
  rw [e5, hfield, hsum, hn1, hn2]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
