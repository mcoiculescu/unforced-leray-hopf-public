import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.CutoffCrossBound

/-!
# `realCCurlSliceDerivBound`: spatial derivatives of the complexified slice curl

Proves `RealCCurlSliceDerivBound` (`Statements.lean`), source lines 1393-1400.
On a phase slice, `x ↦ realC (spatialCurlST G (τ, x))` equals `T (fderiv (G (τ, ·)) x)` for the
continuous linear map `T = cplxV ∘ L` with `L M = ∑_j e_j × (M e_j)` and `‖T‖ ≤ 3`
(`cplxV` is `realC`, a norm-preserving real-linear map). The bound then follows from
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` and `norm_iteratedFDeriv_fderiv`.
The argument repeats `SpatialCurlSliceDerivBound` with the extra `cplxV` factor.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

private theorem rcs_crossProd_add (a x y : Space) :
    UnforcedLeray.Blueprint.crossProd a (x + y) =
      UnforcedLeray.Blueprint.crossProd a x + UnforcedLeray.Blueprint.crossProd a y := by
  unfold UnforcedLeray.Blueprint.crossProd
  simp only [WithLp.ofLp_add, map_add, WithLp.toLp_add]

private theorem rcs_crossProd_smul (a : Space) (c : ℝ) (x : Space) :
    UnforcedLeray.Blueprint.crossProd a (c • x) = c • UnforcedLeray.Blueprint.crossProd a x := by
  unfold UnforcedLeray.Blueprint.crossProd
  simp only [WithLp.ofLp_smul, map_smul, WithLp.toLp_smul]

private theorem rcs_fderiv_slice {F : ℝ × Space → Space} (hF : ContDiff ℝ ∞ F)
    (τ : ℝ) (y : Space) (j : Fin 3) :
    fderiv ℝ (fun x : Space => F (τ, x)) y (coordinateVector j) =
      fderiv ℝ F (τ, y) (0, coordinateVector j) := by
  have hAt := hF.differentiable (by simp) (τ, y)
  have hcomp := hAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  have heq := hcomp.fderiv
  change fderiv ℝ (fun x : Space => F (τ, x)) y = _ at heq
  rw [heq]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The linear functional `M ↦ ∑_j e_j × (M e_j)` on `Space →L Space`. -/
private def rcsLin : (Space →L[ℝ] Space) →ₗ[ℝ] Space where
  toFun M := ∑ j : Fin 3, UnforcedLeray.Blueprint.crossProd (coordinateVector j)
    (M (coordinateVector j))
  map_add' S M := by
    simp only [ContinuousLinearMap.add_apply, rcs_crossProd_add, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, rcs_crossProd_smul,
      Finset.smul_sum]

private theorem rcs_bound (M : Space →L[ℝ] Space) : ‖rcsLin M‖ ≤ 3 * ‖M‖ := by
  have hterm : ∀ j : Fin 3,
      ‖UnforcedLeray.Blueprint.crossProd (coordinateVector j) (M (coordinateVector j))‖ ≤ ‖M‖ := by
    intro j
    have h1 := UnforcedLeray.Short.IIb.cutoffCrossBound_norm_crossProd_le
      (coordinateVector j) (M (coordinateVector j))
    have h2 := M.le_opNorm (coordinateVector j)
    rw [RieszLp.norm_coordinateVector, mul_one] at h2
    rw [RieszLp.norm_coordinateVector, one_mul] at h1
    exact h1.trans h2
  have hdef : rcsLin M = ∑ j : Fin 3,
      UnforcedLeray.Blueprint.crossProd (coordinateVector j) (M (coordinateVector j)) := rfl
  rw [hdef]
  calc ‖∑ j : Fin 3, UnforcedLeray.Blueprint.crossProd (coordinateVector j) (M (coordinateVector j))‖
      ≤ ∑ j : Fin 3,
        ‖UnforcedLeray.Blueprint.crossProd (coordinateVector j) (M (coordinateVector j))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖M‖ := Finset.sum_le_sum fun j _ => hterm j
    _ = 3 * ‖M‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

private def rcsL : (Space →L[ℝ] Space) →L[ℝ] Space :=
  LinearMap.mkContinuous rcsLin 3 (fun M => rcs_bound M)

private theorem rcsL_apply (M : Space →L[ℝ] Space) : rcsL M = rcsLin M := rfl

private theorem rcsL_norm_le : ‖rcsL‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound rcsL (by norm_num) (fun M => by
    rw [rcsL_apply]
    exact rcs_bound M)

/-- The complexified map `T M = realC (∑_j e_j × (M e_j))`. -/
private def rcsT : (Space →L[ℝ] Space) →L[ℝ] CVec3 :=
  UnforcedLeray.Axi.cplxV.comp rcsL

private theorem rcsT_norm_le : ‖rcsT‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound rcsT (by norm_num) (fun M => by
    have h := rcs_bound M
    have hc : ‖rcsT M‖ = ‖rcsL M‖ := by
      show ‖UnforcedLeray.Axi.cplxV (rcsL M)‖ = _
      rw [UnforcedLeray.Axi.norm_cplxV]
    rw [hc, rcsL_apply]
    linarith)

private theorem rcs_realC_eq : (UnforcedLeray.B0412.realC : Space → CVec3) =
    UnforcedLeray.Axi.cplxV := by
  funext z
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

/-- **Spatial derivatives of the complexified slice curl** (`RealCCurlSliceDerivBound`). -/
theorem realCCurlSliceDerivBound : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.RealCCurlSliceDerivBound := by
  intro G hG k τ y
  have hg : ContDiff ℝ ∞ (fun x : Space => G (τ, x)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hfun : (fun x : Space => realC (spatialCurlST G (τ, x))) =
      fun x => rcsT (fderiv ℝ (fun x : Space => G (τ, x)) x) := by
    funext x
    have h2 : rcsT (fderiv ℝ (fun x : Space => G (τ, x)) x) =
        UnforcedLeray.Axi.cplxV (∑ j : Fin 3, UnforcedLeray.Blueprint.crossProd
          (coordinateVector j) (fderiv ℝ (fun x : Space => G (τ, x)) x (coordinateVector j))) := rfl
    rw [h2, rcs_realC_eq]
    congr 1
    unfold spatialCurlST
    apply Finset.sum_congr rfl
    intro j _
    rw [rcs_fderiv_slice hG τ x j]
  rw [hfun]
  have hdiff : ContDiffAt ℝ ∞ (fun x : Space => fderiv ℝ (fun x : Space => G (τ, x)) x) y :=
    (hg.fderiv_right (m := ∞) (by simp)).contDiffAt
  have h1 := rcsT.norm_iteratedFDeriv_comp_left (f := fun x : Space =>
      fderiv ℝ (fun x : Space => G (τ, x)) x) (x := y) (n := k) (N := ∞) hdiff (by simp)
  rw [norm_iteratedFDeriv_fderiv] at h1
  calc ‖iteratedFDeriv ℝ k (fun x : Space => rcsT (fderiv ℝ (fun x : Space => G (τ, x)) x)) y‖
      ≤ ‖rcsT‖ * ‖iteratedFDeriv ℝ (k + 1) (fun x : Space => G (τ, x)) y‖ := h1
    _ ≤ 3 * ‖iteratedFDeriv ℝ (k + 1) (fun x : Space => G (τ, x)) y‖ :=
        mul_le_mul_of_nonneg_right rcsT_norm_le (norm_nonneg _)

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
