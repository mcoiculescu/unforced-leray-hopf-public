import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.CutoffCrossBound

/-!
# `spatialCurlSliceDerivBound`: spatial derivatives of a slice curl

Proves `SpatialCurlSliceDerivBound` (`Statements.lean`), source lines 1393-1400 (derivatives of the
curl). On a phase slice, `x ↦ spatialCurlST A (τ, x)` equals `L ∘ (fderiv (A (τ, ·)))` for the
continuous linear map `L T = ∑_j e_j × (T e_j)` on `Space →L Space`, with `‖L‖ ≤ 3`.
The `k`-th derivative bound then follows from `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`
and `norm_iteratedFDeriv_fderiv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

/-- Cross product is additive in its second argument. -/
private theorem ssc_crossProd_add (a x y : Space) :
    UnforcedLeray.Blueprint.crossProd a (x + y) =
      UnforcedLeray.Blueprint.crossProd a x + UnforcedLeray.Blueprint.crossProd a y := by
  unfold UnforcedLeray.Blueprint.crossProd
  simp only [WithLp.ofLp_add, map_add, WithLp.toLp_add]

/-- Cross product is homogeneous in its second argument. -/
private theorem ssc_crossProd_smul (a : Space) (c : ℝ) (x : Space) :
    UnforcedLeray.Blueprint.crossProd a (c • x) = c • UnforcedLeray.Blueprint.crossProd a x := by
  unfold UnforcedLeray.Blueprint.crossProd
  simp only [WithLp.ofLp_smul, map_smul, WithLp.toLp_smul]

/-- Coordinate derivative of a slice of a smooth joint field. -/
private theorem ssc_fderiv_slice {F : ℝ × Space → Space} (hF : ContDiff ℝ ∞ F)
    (τ : ℝ) (y : Space) (j : Fin 3) :
    fderiv ℝ (fun x : Space => F (τ, x)) y (coordinateVector j) =
      fderiv ℝ F (τ, y) (0, coordinateVector j) := by
  have hAt := hF.differentiable (by simp) (τ, y)
  have hcomp := hAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  have heq := hcomp.fderiv
  change fderiv ℝ (fun x : Space => F (τ, x)) y = _ at heq
  rw [heq]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The linear functional `T ↦ ∑_j e_j × (T e_j)` on `Space →L Space`. -/
private def sscLin : (Space →L[ℝ] Space) →ₗ[ℝ] Space where
  toFun T := ∑ j : Fin 3, UnforcedLeray.Blueprint.crossProd (coordinateVector j)
    (T (coordinateVector j))
  map_add' S T := by
    simp only [add_apply, ssc_crossProd_add, Finset.sum_add_distrib]
  map_smul' c T := by
    simp only [smul_apply, RingHom.id_apply, ssc_crossProd_smul,
      Finset.smul_sum]

/-- Norm bound `‖L T‖ ≤ 3 ‖T‖`. -/
private theorem ssc_bound (T : Space →L[ℝ] Space) : ‖sscLin T‖ ≤ 3 * ‖T‖ := by
  have hterm : ∀ j : Fin 3,
      ‖UnforcedLeray.Blueprint.crossProd (coordinateVector j) (T (coordinateVector j))‖ ≤ ‖T‖ := by
    intro j
    have h1 := UnforcedLeray.Short.IIb.cutoffCrossBound_norm_crossProd_le
      (coordinateVector j) (T (coordinateVector j))
    have h2 := T.le_opNorm (coordinateVector j)
    rw [RieszLp.norm_coordinateVector, mul_one] at h2
    rw [RieszLp.norm_coordinateVector, one_mul] at h1
    exact h1.trans h2
  have hdef : sscLin T = ∑ j : Fin 3,
      UnforcedLeray.Blueprint.crossProd (coordinateVector j) (T (coordinateVector j)) := rfl
  rw [hdef]
  calc ‖∑ j : Fin 3, UnforcedLeray.Blueprint.crossProd (coordinateVector j) (T (coordinateVector j))‖
      ≤ ∑ j : Fin 3,
        ‖UnforcedLeray.Blueprint.crossProd (coordinateVector j) (T (coordinateVector j))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖T‖ := Finset.sum_le_sum fun j _ => hterm j
    _ = 3 * ‖T‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- The continuous linear map `L T = ∑_j e_j × (T e_j)`. -/
private def sscL : (Space →L[ℝ] Space) →L[ℝ] Space :=
  LinearMap.mkContinuous sscLin 3 (fun T => ssc_bound T)

private theorem sscL_apply (T : Space →L[ℝ] Space) : sscL T = sscLin T := rfl

private theorem sscL_norm_le : ‖sscL‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound sscL (by norm_num) (fun T => by
    rw [sscL_apply]
    exact ssc_bound T)

/-- **Spatial derivatives of a slice curl** (`SpatialCurlSliceDerivBound`). -/
theorem spatialCurlSliceDerivBound : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.SpatialCurlSliceDerivBound := by
  intro A hA k τ y
  have hg : ContDiff ℝ ∞ (fun x : Space => A (τ, x)) :=
    hA.comp (contDiff_const.prodMk contDiff_id)
  have hfun : (fun x : Space => spatialCurlST A (τ, x)) =
      fun x => sscL (fderiv ℝ (fun x : Space => A (τ, x)) x) := by
    funext x
    have h2 : sscL (fderiv ℝ (fun x : Space => A (τ, x)) x) =
        ∑ j : Fin 3, UnforcedLeray.Blueprint.crossProd (coordinateVector j)
          (fderiv ℝ (fun x : Space => A (τ, x)) x (coordinateVector j)) := rfl
    rw [h2]
    unfold spatialCurlST
    apply Finset.sum_congr rfl
    intro j _
    rw [ssc_fderiv_slice hA τ x j]
  rw [hfun]
  have hdiff : ContDiffAt ℝ ∞ (fun x : Space => fderiv ℝ (fun x : Space => A (τ, x)) x) y :=
    (hg.fderiv_right (m := ∞) (by simp)).contDiffAt
  have h1 := sscL.norm_iteratedFDeriv_comp_left (f := fun x : Space =>
      fderiv ℝ (fun x : Space => A (τ, x)) x) (x := y) (n := k) (N := ∞) hdiff (by simp)
  rw [norm_iteratedFDeriv_fderiv] at h1
  calc ‖iteratedFDeriv ℝ k (fun x : Space => sscL (fderiv ℝ (fun x : Space => A (τ, x)) x)) y‖
      ≤ ‖sscL‖ * ‖iteratedFDeriv ℝ (k + 1) (fun x : Space => A (τ, x)) y‖ := h1
    _ ≤ 3 * ‖iteratedFDeriv ℝ (k + 1) (fun x : Space => A (τ, x)) y‖ :=
        mul_le_mul_of_nonneg_right sscL_norm_le (norm_nonneg _)

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
