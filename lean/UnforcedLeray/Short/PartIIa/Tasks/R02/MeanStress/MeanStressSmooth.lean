import UnforcedLeray.Short.PartIIa.Sub.R02_6
import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part II-a, task `PartII-a:R02/MeanStress/MeanStressSmooth`: smoothness of the mean stress

Source of record: `the November 2 reference manuscript`, lines 397-404
(`sct:mean`, `g = \overline{v₁ v₂}`).

The statement `MeanStressSmooth` (with `fluctProd`) is defined in `Short/PartII-a/Sub/R02_6.lean`;
`HmeanContDiff` is defined in `Short/PartI/Sub/T01.lean`.

Route. Put `v_j(s, z) = tr.v s z j`, the `j`-th coordinate of the train velocity.
* `v_j` is `C^∞` on `(0, ∞) × Plane` (restriction of `tr.isTrain.smooth_v`, then the continuous
  linear coordinate map `EuclideanSpace.proj j`).
* The mean stress is `meanStress tr s η = hmean c (v₁ v₂)(s, ·) (η)`, so it is `C^∞` by
  `HmeanContDiff` applied to the product `(s, z) ↦ v₁(s, z) v₂(s, z)`.
* `hfluct c (v_j(r, ·)) z = v_j(r, z) - hmean c (v_j(r, ·)) z.2`. The first term is `C^∞` in
  `(r, z)`; the second is `C^∞` by `HmeanContDiff` for `f = v_j`, composed with the smooth map
  `(r, z) ↦ (r, z.2)` (which sends `(0, ∞) × Plane` into `(0, ∞) × ℝ`).
* `fluctProd tr r z` is the product of the two fluctuations, `C^∞` by `ContDiffOn.mul`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (meanStress hmean hfluct)

/-- The `j`-th coordinate of the train velocity is `C^∞` on `(0, ∞) × Plane`. -/
private theorem meanStressSmooth_velCoord {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 j) (Ioi 0 ×ˢ univ) :=
  (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
    (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self (subset_refl _)))

/-- The product of the two velocity coordinates is `C^∞` on `(0, ∞) × Plane`. -/
private theorem meanStressSmooth_velProd {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 0 * tr.v x.1 x.2 1) (Ioi 0 ×ˢ univ) :=
  (meanStressSmooth_velCoord tr 0).mul (meanStressSmooth_velCoord tr 1)

/-- The fluctuation `hfluct c (v_j(r, ·)) z` is `C^∞` in `(r, z)` on `(0, ∞) × Plane`. -/
private theorem meanStressSmooth_fluct {ν c : ℝ} (hH : UnforcedLeray.Short.PartI.HmeanContDiff)
    (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => hfluct c (fun w => tr.v x.1 w j) x.2)
      (Ioi 0 ×ˢ univ) := by
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 j) (Ioi 0 ×ˢ univ) :=
    meanStressSmooth_velCoord tr j
  have hm : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => hmean c (fun w => tr.v y.1 w j) y.2)
      (Ioi 0 ×ˢ univ) :=
    hH c hc (fun s w => tr.v s w j) hv
  have hproj : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => (x.1, x.2.2)) (Ioi 0 ×ˢ univ) :=
    (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => (x.1, x.2.2))).contDiffOn
  have hmap : MapsTo (fun x : ℝ × (ℝ × ℝ) => (x.1, x.2.2)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
    fun x hx => ⟨hx.1, mem_univ _⟩
  have hcomp := hm.comp hproj hmap
  exact hv.sub hcomp

/-- **Smoothness of the mean stress and of the fluctuation products** (source lines 397-404):
`g(s, η) = \overline{v₁v₂}`, the fluctuations `ṽ_j` and their product `ṽ₁ṽ₂` are `C^∞` for
`s > 0`, given `HmeanContDiff` (horizontal averaging preserves smoothness). -/
theorem meanStressSmooth_of (hH : UnforcedLeray.Short.PartI.HmeanContDiff) :
    UnforcedLeray.Short.PartIIa.MeanStressSmooth := by
  unfold MeanStressSmooth
  intro ν c _hν hc tr _hb
  have hprod : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 0 * tr.v x.1 x.2 1)
      (Ioi 0 ×ˢ univ) :=
    meanStressSmooth_velProd tr
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hH c hc (fun s z => tr.v s z 0 * tr.v s z 1) hprod
  have h3 : ∀ j : Fin 2,
      ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => hfluct c (fun w => tr.v x.1 w j) x.2)
        (Ioi 0 ×ˢ univ) :=
    fun j => meanStressSmooth_fluct hH hc tr j
  have h2 : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => fluctProd tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    (h3 0).mul (h3 1)
  exact ⟨h1, h2, h3⟩

end UnforcedLeray.Short.PartIIa
