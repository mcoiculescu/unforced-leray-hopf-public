import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.AdjointTaylor

/-!
# Part II-a, task `PartII-a:F02/9`, helper: slice calculus for phase tests

Calculus of the slices `z ↦ K(Φ(t,z))` for a complex phase test `Φ` and `K ∈ {reV, imV}`:
derivatives, the vector Laplacian and radial derivative of a slice, operator-norm bounds on
the basis, and the algebra of `ofReV` / `ofImV`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.SliceCalc

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

section Generic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_slice {G : ℝ × Space → F} (hG : Differentiable ℝ G) (t : ℝ) (y : Space) :
    HasFDerivAt (fun z : Space => G (t, z))
      ((fderiv ℝ G (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y := by
  have h1 : HasFDerivAt (fun z : Space => ((t, z) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have h2 := (hG (t, y)).hasFDerivAt.comp y h1
  refine h2.congr_fderiv ?_
  ext a
  simp

theorem fderiv_clm_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × Space → F} (hG : Differentiable ℝ G) (K : F →L[ℝ] E) (t : ℝ) (y a : Space) :
    fderiv ℝ (fun z : Space => K (G (t, z))) y a = K (fderiv ℝ G (t, y) (0, a)) := by
  have h : HasFDerivAt (fun z : Space => K (G (t, z)))
      (K.comp ((fderiv ℝ G (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space))) y :=
    K.hasFDerivAt.comp y (hasFDerivAt_slice hG t y)
  rw [h.fderiv]
  rfl

theorem contDiff_dy {G : ℝ × Space → F} (hG : ContDiff ℝ ∞ G) (j : Fin 3) :
    ContDiff ℝ ∞ (PhaseSpace.dy j G) := by
  unfold PhaseSpace.dy
  exact (contDiff_infty_iff_fderiv.mp hG).2.clm_apply contDiff_const

theorem norm_clm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E →L[ℝ] Space) (hK : ‖K‖ ≤ 1) (x : E) : ‖K x‖ ≤ ‖x‖ :=
  (K.le_opNorm x).trans (by nlinarith [norm_nonneg x])

theorem opNorm_le_sum_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Space →L[ℝ] E) :
    ‖L‖ ≤ ∑ j : Fin 3, ‖L (coordinateVector j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound L (Finset.sum_nonneg fun j _ => norm_nonneg _) ?_
  intro x
  have hx : L x = ∑ j : Fin 3, x j • L (coordinateVector j) := by
    conv_lhs => rw [eq_sum_coordinateVector x]
    simp only [map_sum, map_smul]
  rw [hx]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg _)

theorem fderiv_fderiv_apply_formula {u : Space → Space} (hu : ContDiff ℝ ∞ u) (v w p : Space) :
    fderiv ℝ (fun q => fderiv ℝ u q w) p v = fderiv ℝ (fderiv ℝ u) p v w := by
  have hd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ u y w) ((fderiv ℝ (fderiv ℝ u) p).flip w) p := by
    simpa using (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const w p)
  rw [hx.fderiv]
  rfl

end Generic

section Slices

variable {G : ℝ × Space → CVec3}

theorem fderiv_clm_slice_self (hG : Differentiable ℝ G) (K : CVec3 →L[ℝ] Space) (t : ℝ)
    (y : Space) :
    fderiv ℝ (fun z : Space => K (G (t, z))) y y = K (radialT G (t, y)) := by
  rw [fderiv_clm_slice hG K t y y]
  congr 1
  have hy : ((0 : ℝ), y) = ∑ j : Fin 3, y j • ((0 : ℝ), coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      exact eq_sum_coordinateVector y
  rw [hy]
  simp only [map_sum, map_smul, radialT, PhaseSpace.dy]

theorem vecLaplacian_clm_slice (hG : ContDiff ℝ ∞ G) (K : CVec3 →L[ℝ] Space) (t : ℝ) (x : Space) :
    UnforcedLeray.B0418.vecLaplacian (fun z : Space => K (G (t, z))) x = K (lapT G (t, x)) := by
  unfold UnforcedLeray.B0418.vecLaplacian
  have key : ∀ i : Fin 3,
      fderiv ℝ (fun y : Space => fderiv ℝ (fun z : Space => K (G (t, z))) y
        (coordinateVector i)) x (coordinateVector i) = K (PhaseSpace.dy i (PhaseSpace.dy i G) (t, x)) := by
    intro i
    have hf : (fun y : Space => fderiv ℝ (fun z : Space => K (G (t, z))) y (coordinateVector i))
        = fun y : Space => K (PhaseSpace.dy i G (t, y)) :=
      funext fun y => fderiv_clm_slice (hG.differentiable (by simp)) K t y (coordinateVector i)
    rw [hf]
    exact fderiv_clm_slice ((contDiff_dy hG i).differentiable (by simp)) K t x (coordinateVector i)
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  simp only [lapT, map_sum]

theorem norm_fderiv_slice_le (hG : ContDiff ℝ ∞ G) (K : CVec3 →L[ℝ] Space) (hK : ‖K‖ ≤ 1)
    (t : ℝ) (y : Space) :
    ‖fderiv ℝ (fun z : Space => K (G (t, z))) y‖ ≤ ∑ j : Fin 3, ‖PhaseSpace.dy j G (t, y)‖ := by
  refine (opNorm_le_sum_basis _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [fderiv_clm_slice (hG.differentiable (by simp)) K t y (coordinateVector j)]
  exact norm_clm_le K hK _

theorem norm_fderiv_fderiv_slice_le (hG : ContDiff ℝ ∞ G) (K : CVec3 →L[ℝ] Space)
    (hK : ‖K‖ ≤ 1) (t : ℝ) (y : Space) :
    ‖fderiv ℝ (fderiv ℝ (fun z : Space => K (G (t, z)))) y‖ ≤
      ∑ j : Fin 3, ∑ k : Fin 3, ‖PhaseSpace.dy j (PhaseSpace.dy k G) (t, y)‖ := by
  have hu : ContDiff ℝ ∞ (fun z : Space => K (G (t, z))) :=
    K.contDiff.comp (hG.comp (contDiff_const.prodMk contDiff_id))
  refine (opNorm_le_sum_basis _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (opNorm_le_sum_basis _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← fderiv_fderiv_apply_formula hu (coordinateVector j) (coordinateVector k) y]
  have hf : (fun q : Space => fderiv ℝ (fun z : Space => K (G (t, z))) q (coordinateVector k))
      = fun q : Space => K (PhaseSpace.dy k G (t, q)) :=
    funext fun q => fderiv_clm_slice (hG.differentiable (by simp)) K t q (coordinateVector k)
  rw [hf, fderiv_clm_slice ((contDiff_dy hG k).differentiable (by simp)) K t y
    (coordinateVector j)]
  exact norm_clm_le K hK _

end Slices

end UnforcedLeray.Short.PartIIa.SliceCalc
