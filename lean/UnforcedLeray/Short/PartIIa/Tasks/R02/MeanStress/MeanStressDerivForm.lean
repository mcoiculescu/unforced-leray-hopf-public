import UnforcedLeray.Short.PartIIa.Sub.R02_6

/-!
# Part II-a, task `PartII-a:R02/MeanStress/MeanStressDerivForm`: the derivative form of the mean stress

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`,
`g = \overline{v₁ v₂}`, `\bar v₂ = 0`).

The statement `MeanStressDerivForm` and the helper `fluctProd` are defined in
`Short/PartII-a/Sub/R02_6.lean`. The hypotheses are `TrainMeanEquations` (third conjunct
`\bar v₂ = 0`), `HmeanMulFluct`, `HmeanMixedDeriv` and `MeanStressSmooth`.

Route.
1. For `r > 0` and every `e`, `meanStress tr r e = hmean c (fluctProd tr r) e`: apply
   `HmeanMulFluct` to `f z = v₁(r, z)` and `g z = v₂(r, z)`, using `\bar v₂ = 0` for `hmean c g e = 0`.
2. For each `e`, the age derivatives `∂_s^k` at `s > 0` of `r ↦ meanStress tr r e` and of
   `r ↦ hmean c (fluctProd tr r) e` agree, since the two functions agree on the neighbourhood
   `Ioi 0` of `s`.
3. Hence the outer `∂_η^a` of the two sides agree after `funext`, and `HmeanMixedDeriv` applied to
   `f r z = fluctProd tr r z` (jointly smooth on `(0,∞) × Plane` by `MeanStressSmooth`) gives the
   right-hand side.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (meanStress hmean hfluct)

/-- The `j`-th velocity coordinate at a fixed age `r > 0` is continuous on the plane. -/
private theorem velCoord_continuous_of_pos {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (r : ℝ) (hr : 0 < r) (j : Fin 2) :
    Continuous (fun z : ℝ × ℝ => tr.v r z j) := by
  have hcoord : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 j) (Ici 0 ×ˢ univ) :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp_continuousOn
      tr.isTrain.smooth_v.continuousOn
  exact hcoord.comp_continuous (f := fun z : ℝ × ℝ => ((r, z) : ℝ × (ℝ × ℝ)))
    (by fun_prop) (fun z => Set.mk_mem_prod (Set.mem_Ici.mpr hr.le) (Set.mem_univ z))

theorem meanStressDerivForm_of (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (hMul : UnforcedLeray.Short.PartIIa.HmeanMulFluct)
    (hMix : UnforcedLeray.Short.PartIIa.HmeanMixedDeriv)
    (hSm : UnforcedLeray.Short.PartIIa.MeanStressSmooth) :
    UnforcedLeray.Short.PartIIa.MeanStressDerivForm := by
  unfold UnforcedLeray.Short.PartIIa.MeanStressDerivForm
  intro ν c hν hc tr hb a k s η hs
  -- (1) pointwise identity for every age `r > 0`
  have key : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      meanStress tr r e = hmean c (fun z => fluctProd tr r z) e := by
    intro r hr e
    have hcont0 : Continuous (fun z : ℝ × ℝ => tr.v r z 0) :=
      velCoord_continuous_of_pos tr r hr 0
    have hcont1 : Continuous (fun z : ℝ × ℝ => tr.v r z 1) :=
      velCoord_continuous_of_pos tr r hr 1
    have hzero : hmean c (fun z : ℝ × ℝ => tr.v r z 1) e = 0 :=
      ((hE ν c hν hc tr hb).2 r hr e).2.2
    have h : hmean c (fun z : ℝ × ℝ => tr.v r z 0 * tr.v r z 1) e =
        hmean c (fun z : ℝ × ℝ => hfluct c (fun w => tr.v r w 0) z *
          hfluct c (fun w => tr.v r w 1) z) e :=
      hMul c e hc (fun z => tr.v r z 0) (fun z => tr.v r z 1) hcont0 hcont1 hzero
    exact h
  -- (2) for each fixed `e`, the age derivatives at `s` agree
  have hfun : ∀ e : ℝ,
      iteratedDeriv k (fun r => meanStress tr r e) s =
        iteratedDeriv k (fun r => hmean c (fun z => fluctProd tr r z) e) s := by
    intro e
    refine Filter.EventuallyEq.iteratedDeriv_eq k ?_
    filter_upwards [Ioi_mem_nhds hs] with r hr
    exact key r (Set.mem_Ioi.mp hr) e
  have hfun2 : (fun e => iteratedDeriv k (fun r => meanStress tr r e) s) =
      (fun e => iteratedDeriv k (fun r => hmean c (fun z => fluctProd tr r z) e) s) := by
    funext e
    exact hfun e
  -- (3) mixed derivatives commute with the cell average
  have hf : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => fluctProd tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    (hSm ν c hν hc tr hb).2.1
  rw [hfun2]
  exact hMix c hc (fun r z => fluctProd tr r z) hf a k s η hs

end UnforcedLeray.Short.PartIIa
