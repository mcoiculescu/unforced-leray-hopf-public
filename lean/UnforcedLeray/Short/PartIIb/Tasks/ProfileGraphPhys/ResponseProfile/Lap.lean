import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf3
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf2
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# `PartII-b:T10/5` helper: `gAct` commutes with the spatial Laplacian on phase tests

Source of record: `the November 2 reference manuscript`, lines 1912-1938.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.RespProf

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete InnerProductSpace Laplacian

/-- `lapT` of a smooth field is the Laplacian of the `y`-slice. -/
theorem lapT_eq_laplacian (Φ : ℝ × UnforcedLeray.Space → CVec3) (hΦ : ContDiff ℝ ∞ Φ)
    (τ : ℝ) (y : UnforcedLeray.Space) :
    lapT Φ (τ, y) = Δ (fun z : UnforcedLeray.Space => Φ (τ, z)) y := by
  set h : UnforcedLeray.Space → CVec3 := fun z => Φ (τ, z) with hh
  have hι : ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => ((τ, z) : ℝ × UnforcedLeray.Space)) :=
    contDiff_const.prodMk contDiff_id
  have hhs : ContDiff ℝ ∞ h := hΦ.comp hι
  have hfd : ∀ z v, fderiv ℝ h z v = fderiv ℝ Φ (τ, z) (0, v) := by
    intro z v
    have hd : HasFDerivAt (fun z : UnforcedLeray.Space => ((τ, z) : ℝ × UnforcedLeray.Space))
        ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _)) z :=
      (hasFDerivAt_const τ z).prodMk (hasFDerivAt_id z)
    have := ((hΦ.differentiable (by simp)) (τ, z)).hasFDerivAt.comp z hd
    rw [show h = Φ ∘ (fun z : UnforcedLeray.Space => ((τ, z) : ℝ × UnforcedLeray.Space)) from rfl,
      this.fderiv]
    simp
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis h (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [lapT, EuclideanSpace.basisFun_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ z, dy j Φ (τ, z) = fderiv ℝ h z (coordinateVector j) := by
    intro z; rw [hfd]; rfl
  have h2 : dy j (dy j Φ) (τ, y) =
      fderiv ℝ (fun z => fderiv ℝ h z (coordinateVector j)) y (coordinateVector j) := by
    have e : (fun z => dy j Φ (τ, z)) = fun z => fderiv ℝ h z (coordinateVector j) :=
      funext h1
    rw [← e]
    have hd : HasFDerivAt (fun z : UnforcedLeray.Space => ((τ, z) : ℝ × UnforcedLeray.Space))
        ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _)) y :=
      (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
    have hdy : Differentiable ℝ (dy j Φ) := by
      have : ContDiff ℝ 1 (dy j Φ) := by
        unfold dy
        exact (hΦ.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const
      exact this.differentiable (by simp)
    have := (hdy (τ, y)).hasFDerivAt.comp y hd
    show fderiv ℝ (dy j Φ) (τ, y) (0, coordinateVector j) = _
    have h3 : fderiv ℝ (fun z => dy j Φ (τ, z)) y (coordinateVector j) =
        fderiv ℝ (dy j Φ) (τ, y) (0, coordinateVector j) := by
      rw [show (fun z => dy j Φ (τ, z)) = dy j Φ ∘ (fun z : UnforcedLeray.Space =>
        ((τ, z) : ℝ × UnforcedLeray.Space)) from rfl, this.fderiv]
      simp
    rw [← h3, e]
  rw [h2, iteratedFDeriv_two_apply]
  have hdh : Differentiable ℝ (fderiv ℝ h) :=
    (hhs.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  rw [fderiv_clm_apply (hdh y) (differentiableAt_const _)]
  simp [UnforcedLeray.coordinateVector]

/-- The Laplacian commutes with composition by a linear isometry equivalence. -/
theorem laplacian_comp_isometry (U : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space)
    (h : UnforcedLeray.Space → CVec3) (hh : ContDiff ℝ 2 h) (y : UnforcedLeray.Space) :
    Δ (fun z => h (U z)) y = Δ h (U y) := by
  set v := EuclideanSpace.basisFun (Fin 3) ℝ with hv
  have hc : ContDiff ℝ 2 (h ∘ (U.toContinuousLinearEquiv : UnforcedLeray.Space →L[ℝ]
      UnforcedLeray.Space)) := hh.comp U.toContinuousLinearEquiv.contDiff
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (fun z => h (U z)) v,
    laplacian_eq_iteratedFDeriv_orthonormalBasis h (v.map U)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (U.toContinuousLinearEquiv : UnforcedLeray.Space →L[ℝ]
      UnforcedLeray.Space).iteratedFDeriv_comp_right hh y (i := 2) le_rfl
  have e : (fun z => h (U z)) = h ∘ (U.toContinuousLinearEquiv : UnforcedLeray.Space →L[ℝ]
      UnforcedLeray.Space) := rfl
  rw [e, this]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, OrthonormalBasis.coe_map]
  congr 1
  ext k
  fin_cases k <;> simp

theorem lapT_gAct (P : ℝ) (g : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space)
    (Φ : ℝ × UnforcedLeray.Space → CVec3) (hΦ : IsPhaseTest P Φ) :
    lapT (gAct g Φ) = gAct g (lapT Φ) := by
  have hg : ContDiff ℝ ∞ (gAct g Φ) := (gActPhaseTest P g Φ hΦ).smooth
  funext ⟨τ, y⟩
  rw [lapT_eq_laplacian _ hg]
  have hι : ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => ((τ, g.symm z) : ℝ × UnforcedLeray.Space)) :=
    contDiff_const.prodMk (g.symm.toContinuousLinearEquiv.contDiff)
  have hh : ContDiff ℝ 2 (fun z : UnforcedLeray.Space => Φ (τ, g.symm z)) :=
    (hΦ.smooth.comp hι).of_le (by simp)
  have e : (fun z : UnforcedLeray.Space => gAct g Φ (τ, z)) =
      ((UnforcedLeray.B0412.gC g).restrictScalars ℝ) ∘
        (fun z : UnforcedLeray.Space => Φ (τ, g.symm z)) := rfl
  rw [e, hh.contDiffAt.laplacian_CLM_comp_left, Function.comp_apply,
    laplacian_comp_isometry g.symm (fun z => Φ (τ, z))
      ((hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)),
    ← lapT_eq_laplacian _ hΦ.smooth]
  rfl

theorem nuLapT_gAct (P ν : ℝ) (g : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space)
    (Φ : ℝ × UnforcedLeray.Space → CVec3) (hΦ : IsPhaseTest P Φ) :
    nuLapT ν (gAct g Φ) = gAct g (nuLapT ν Φ) := by
  funext x
  simp only [nuLapT, Pi.smul_apply, lapT_gAct P g Φ hΦ, gAct]
  exact (UnforcedLeray.Short.IIb.GActLeaf3.smul_gC_leaf3 g ν _).symm

end UnforcedLeray.Short.IIb.RespProf
