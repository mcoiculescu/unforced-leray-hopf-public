import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2

/-!
# `PartII-b:T10/7/1/1/2/4`: `gl_dyTransport` (chain rule for `∂_{y_j}` along the transport)

Source of record: `the November 2 reference manuscript` lines 1912-1921, chart 1639-1668.
Mathematics: `trF T Φ x = cApp T.symm (Φ (x.1, T x.2))`. The map `cApp T.symm` is `ℝ`-linear, so the
chain rule gives `∂_j (trF T Φ) x = cApp T.symm (fderiv Φ (x.1, T x.2) (0, T e_j))`, and expanding
`(0, T e_j) = ∑ₗ (T e_j)ₗ • (0, e_l)` yields the stated formula.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace DyTr

theorem reS_add' (u v : CVec3) : reS (u + v) = reS u + reS v := by
  ext i
  simp [reS]

theorem imS_add' (u v : CVec3) : imS (u + v) = imS u + imS v := by
  ext i
  simp [imS]

theorem reS_smul' (r : ℝ) (v : CVec3) : reS (r • v) = r • reS v := by
  ext i
  simp [reS]

theorem imS_smul' (r : ℝ) (v : CVec3) : imS (r • v) = r • imS v := by
  ext i
  simp [imS]

theorem realC_add' (x y : Space) :
    B0412.realC (x + y) = B0412.realC x + B0412.realC y := by
  ext i
  simp [B0412.realC_apply]

theorem realC_smul' (r : ℝ) (x : Space) :
    B0412.realC (r • x) = (r : ℂ) • B0412.realC x := by
  ext i
  simp [B0412.realC_apply]

theorem cApp_add' (S : Space ≃ₗᵢ[ℝ] Space) (u v : CVec3) :
    cApp S (u + v) = cApp S u + cApp S v := by
  unfold cApp
  simp only [reS_add', imS_add', map_add, realC_add', smul_add]
  abel

theorem cApp_smul' (S : Space ≃ₗᵢ[ℝ] Space) (r : ℝ) (v : CVec3) :
    cApp S (r • v) = r • cApp S v := by
  unfold cApp
  rw [reS_smul', imS_smul']
  simp only [map_smul, realC_smul', RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_add, smul_comm Complex.I]
  rfl

/-- `cApp S` as an `ℝ`-linear map on `ℂ³`. -/
def cAppL (S : Space ≃ₗᵢ[ℝ] Space) : CVec3 →ₗ[ℝ] CVec3 where
  toFun := cApp S
  map_add' := cApp_add' S
  map_smul' := fun r v => cApp_smul' S r v

/-- `cApp S` as a continuous `ℝ`-linear map on `ℂ³`. -/
def cAppCLM (S : Space ≃ₗᵢ[ℝ] Space) : CVec3 →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap (cAppL S)

theorem cAppCLM_apply (S : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : cAppCLM S v = cApp S v := rfl

theorem coord_decomp (v : Space) : (∑ l : Fin 3, v l • coordinateVector l) = v := by
  ext i
  simp [coordinateVector, Pi.single_apply, Finset.sum_apply]

end DyTr

theorem gl_dyTransport : UnforcedLeray.Short.IIb.GLDyTransport := by
  intro T Φ hΦ j x
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  let G : ℝ × Space →L[ℝ] ℝ × Space :=
    (ContinuousLinearMap.id ℝ ℝ).prodMap T.toContinuousLinearEquiv.toContinuousLinearMap
  have hG : ∀ p : ℝ × Space, G p = (p.1, T p.2) := fun p => rfl
  have hΨ : trF T Φ = (DyTr.cAppCLM T.symm) ∘ (Φ ∘ G) := rfl
  have hΦG : HasFDerivAt (Φ ∘ G) ((fderiv ℝ Φ (G x)).comp G) x :=
    (hdiff (G x)).hasFDerivAt.comp x G.hasFDerivAt
  have hfd : fderiv ℝ (trF T Φ) x = (DyTr.cAppCLM T.symm).comp ((fderiv ℝ Φ (G x)).comp G) := by
    rw [hΨ]
    exact ((DyTr.cAppCLM T.symm).hasFDerivAt.comp x hΦG).fderiv
  have hdecomp : G (0, coordinateVector j) =
      ∑ l : Fin 3, ((T (coordinateVector j)) l) • ((0 : ℝ), coordinateVector l) := by
    rw [hG]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · dsimp only
      simp only [Prod.snd_sum, Prod.smul_snd]
      exact (DyTr.coord_decomp (T (coordinateVector j))).symm
  have hkey : fderiv ℝ Φ (G x) (G (0, coordinateVector j)) =
      ∑ l : Fin 3, (T (coordinateVector j)) l • fderiv ℝ Φ (G x) (0, coordinateVector l) := by
    rw [hdecomp, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul]
  have hR : cApp T.symm (∑ l : Fin 3, (((T (coordinateVector j)) l : ℝ) : ℂ) •
      PhaseSpace.dy l Φ (x.1, T x.2)) =
      DyTr.cAppCLM T.symm (∑ l : Fin 3, (T (coordinateVector j)) l • PhaseSpace.dy l Φ (x.1, T x.2)) := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [hR]
  unfold PhaseSpace.dy
  rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hkey]
  simp only [map_sum, map_smul]
  rfl

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_dyTransport
