import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_1

/-!
# `PartII-b:T10/6/1/3`: `GActDrift` (`g·` commutes with the drift, SP 1912-1915)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GActLeaf3

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem smul_gC_leaf3 (g : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space) (r : ℝ)
    (v : CVec3) :
    UnforcedLeray.B0412.gC g (r • v) = r • UnforcedLeray.B0412.gC g v :=
  ((UnforcedLeray.B0412.gC g).restrictScalars ℝ).map_smul r v

theorem radialT_eq_fderiv_leaf3 (F : ℝ × UnforcedLeray.Space → CVec3)
    (p : ℝ × UnforcedLeray.Space) :
    PhaseSpace.radialT F p = fderiv ℝ F p (0, p.2) := by
  have hsum : ((0 : ℝ), p.2) = ∑ j : Fin 3, p.2 j • ((0 : ℝ), coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum]
      ext i
      simp [coordinateVector, Pi.single_apply]
  rw [hsum, map_sum]
  simp only [map_smul, PhaseSpace.radialT, PhaseSpace.dy, coordinateVector, smul_eq_mul]

theorem fderiv_gAct_leaf3 (g : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space)
    (Φ : ℝ × UnforcedLeray.Space → CVec3) (hΦ : Differentiable ℝ Φ) (x v : ℝ × UnforcedLeray.Space) :
    fderiv ℝ (UnforcedLeray.Short.IIb.gAct g Φ) x v =
      UnforcedLeray.B0412.gC g (fderiv ℝ Φ (x.1, g.symm x.2) (v.1, g.symm v.2)) := by
  set L : (ℝ × UnforcedLeray.Space) →L[ℝ] (ℝ × UnforcedLeray.Space) :=
    (ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Space).prod
      ((g.symm : UnforcedLeray.Space →L[ℝ] UnforcedLeray.Space).comp
        (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space)) with hLdef
  have hL : ∀ y : ℝ × UnforcedLeray.Space, L y = (y.1, g.symm y.2) := fun y => by
    simp [hLdef]
  have hΨ : UnforcedLeray.Short.IIb.gAct g Φ =
      fun y => UnforcedLeray.B0412.gC g (Φ (L y)) := by
    funext y
    simp [UnforcedLeray.Short.IIb.gAct, hL]
  have hd : HasFDerivAt (fun y => UnforcedLeray.B0412.gC g (Φ (L y)))
      (((UnforcedLeray.B0412.gC g).restrictScalars ℝ).comp
        ((fderiv ℝ Φ (L x)).comp L)) x :=
    ((UnforcedLeray.B0412.gC g).restrictScalars ℝ).hasFDerivAt.comp x
      ((hΦ (L x)).hasFDerivAt.comp x L.hasFDerivAt)
  rw [hΨ, hd.fderiv]
  simp [hL]

end UnforcedLeray.Short.IIb.GActLeaf3

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete in
theorem gActDrift : UnforcedLeray.Short.IIb.GActDrift := by
  unfold UnforcedLeray.Short.IIb.GActDrift
  intro P g Φ hΦ
  have hdiff : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hD : ∀ x, dτ (UnforcedLeray.Short.IIb.gAct g Φ) x =
      UnforcedLeray.B0412.gC g (dτ Φ (x.1, g.symm x.2)) := by
    intro x
    unfold dτ
    rw [UnforcedLeray.Short.IIb.GActLeaf3.fderiv_gAct_leaf3 g Φ hdiff]
    simp
  have hR : ∀ x, UnforcedLeray.PhaseSpace.radialT (UnforcedLeray.Short.IIb.gAct g Φ) x =
      UnforcedLeray.B0412.gC g (UnforcedLeray.PhaseSpace.radialT Φ (x.1, g.symm x.2)) := by
    intro x
    rw [UnforcedLeray.Short.IIb.GActLeaf3.radialT_eq_fderiv_leaf3,
      UnforcedLeray.Short.IIb.GActLeaf3.fderiv_gAct_leaf3 g Φ hdiff,
      UnforcedLeray.Short.IIb.GActLeaf3.radialT_eq_fderiv_leaf3]
  funext x
  simp only [UnforcedLeray.PhaseSpace.driftT]
  rw [hD, hR]
  simp only [UnforcedLeray.Short.IIb.gAct, UnforcedLeray.PhaseSpace.driftT, map_add, map_neg,
    UnforcedLeray.Short.IIb.GActLeaf3.smul_gC_leaf3]
