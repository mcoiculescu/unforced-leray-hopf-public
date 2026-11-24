import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5

/-!
# `PartIII-a:T21/2/2/3/5/3` (`e1PhysDeriv`): decomposition

Source `the November 2 reference manuscript` lines 2860-2864, 2945-2957, 3060-3062,
3137-3139.  `E1PhysDeriv` splits into
* `E1PhysDiff`: `physE1` is differentiable at `r = revAge ν s ζ` with the explicit derivative
  `physDerivForm` (fixed-cell product rule, from `AdjXDiff`, `wtRatio_le`, `continuousAt_wtRatio`);
* `E1PhysRate`: `-a(r)² · physDerivForm = e1Rate` under the equation hypotheses (rescale
  `x = √a y`, insert `∂_k∂_rφ` from the moving equation; no integration by parts: Reynolds' seam
  bookkeeping is already inside the fixed-cell derivative).

The leaves are decomposed further in `Sub/PartIII-a_T21_2_2_3_5_3_1.lean` (`E1PhysDiff`) and
`Sub/PartIII-a_T21_2_2_3_5_3_2.lean` (`E1PhysRate`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- The explicit derivative of `physE1` at age `r` (SP 2860-2864, 3060-3062):
`(a⁻²)' Σ_k ∫ wh |∂_kφ|² + a⁻² Σ_k [∫ ∂_r(wh) |∂_kφ|² + 2 ∫ wh Re(conj ∂_kφ(r) · ∂_k∂_rφ(r))]`,
`wh(a,x) = p_{c/√a}⁻¹(x/√a)`, `∂_k∂_rφ = pdCx k (adjDt t s φ r)`. Every sum and integral is
parenthesised: the binders `∑ k,` and `∫ x in S,` extend to the right, so each body is closed
explicitly (the first sum is a factor of the first product, the second sum is the last term). -/
def physDerivForm (ν c m : ℝ) (t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  deriv (fun r' => (clockA ν r')⁻¹ ^ 2) r *
      (∑ k : Fin 2, ∫ x in B0579.cell c,
        (periodicWeight (-m) (cellLen c (clockA ν r))
          (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)) * ‖pdCx k (φ r) x‖ ^ 2)) +
    (clockA ν r)⁻¹ ^ 2 * ∑ k : Fin 2,
      ((∫ x in B0579.cell c,
          (deriv (fun r' => periodicWeight (-m) (cellLen c (clockA ν r'))
            (x.1 / Real.sqrt (clockA ν r'), x.2 / Real.sqrt (clockA ν r'))) r *
            ‖pdCx k (φ r) x‖ ^ 2)) +
        2 * ∫ x in B0579.cell c,
          (periodicWeight (-m) (cellLen c (clockA ν r))
            (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)) *
            ((starRingEnd ℂ) (pdCx k (φ r) x) * pdCx k (adjDt t s φ r) x).re))

/-- **(i)** fixed-cell differentiation of the weighted norm (SP 2860-2864, 3060-3062). -/
def E1PhysDiff (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
      HasDerivAt (physE1 ν (ν ^ (-2 : ℝ)) m φ)
        (physDerivForm ν (ν ^ (-2 : ℝ)) m t s φ (revAge ν s ζ)) (revAge ν s ζ)

/-- **(ii)** the identification with the Reynolds-reduced rate (SP 2945-2957, 3137-3139). -/
def E1PhysRate (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ 1 χ →
      (∀ y : ℝ × ℝ, χ (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, y.2) = χ y) →
      (∀ y : ℝ × ℝ, HasDerivAt (fun ζ' => mvPhi ν φ s ζ' y)
        (adjGen (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y - χ y) ζ) →
      (∀ k : Fin 2, IntegrableOn
        (fun y => periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y * ‖pdCx k χ y‖ ^ 2)
        (B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ))) →
      -(clockA ν (revAge ν s ζ)) ^ 2 *
          physDerivForm ν (ν ^ (-2 : ℝ)) m t s φ (revAge ν s ζ) =
        e1Rate m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvBeta ν s ζ)
          (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) χ

theorem e1PhysDeriv_of (m : ℝ) (h1 : E1PhysDiff m) (h2 : E1PhysRate m) : E1PhysDeriv m := by
  intro ν tr t s φ ζ hζ χ hχ hper hder hint
  exact ⟨_, h1 ν tr t s φ ζ hζ, h2 ν tr t s φ ζ hζ χ hχ hper hder hint⟩

end UnforcedLeray.Short.IIIa.AdjE1
