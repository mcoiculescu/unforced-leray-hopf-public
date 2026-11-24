import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Calc1

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: derivative of the radial tests
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem coordVec_eq (j : Fin 3) : (coordinateVector j : Space) = EuclideanSpace.single j 1 := rfl

theorem eRD_eR {y : Space} (hy : y ∉ Axi.axis) : Axi.eRD y (Axi.eR y) = 0 := by
  ext k
  rw [Axi.eRD_apply_coord, Axi.ϱD_eR hy]
  fin_cases k
  · simp [Axi.hor, Axi.eR_apply_zero]
  · simp [Axi.hor, Axi.eR_apply_one]
  · simp [Axi.hor]

theorem eR_sum (y : Space) :
    ∑ j : Fin 3, Axi.eR y j • (EuclideanSpace.single j (1 : ℝ) : Space) = Axi.eR y := by
  ext k
  fin_cases k <;> simp [Fin.sum_univ_three]

theorem eRD_div {y : Space} (hy : y ∉ Axi.axis) :
    ∑ j : Fin 3, Axi.eRD y (EuclideanSpace.single j (1 : ℝ)) j = (Axi.ϱ y)⁻¹ := by
  have hρ := Axi.ϱ_ne_zero hy
  have h1 := Axi.eR_sq_sum hy
  simp only [Fin.sum_univ_three, Axi.eRD_apply_coord, Axi.ϱD_apply, Axi.hor,
    Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two]
  simp
  field_simp
  field_simp at h1
  linarith

theorem exists_EvD (i : Fin 2) {y : Space} (hy : y ∉ Axi.axis) :
    ∃ D : Space →L[ℝ] Space, HasFDerivAt (Evec i) D y ∧ D (Axi.eR y) = 0 := by
  fin_cases i
  · refine ⟨Axi.eRD y, ?_, eRD_eR hy⟩
    show HasFDerivAt (Evec 0) _ y
    rw [Evec_zero]
    exact Axi.hasFDerivAt_eR hy
  · refine ⟨0, ?_, by simp⟩
    show HasFDerivAt (Evec 1) _ y
    rw [Evec_one]
    exact hasFDerivAt_const _ _

theorem dy_tst {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (i : Fin 2) (j : Fin 3) (D : Space →L[ℝ] Space) {x : ℝ × Space} (hy : x.2 ∉ Axi.axis)
    (hD : HasFDerivAt (Evec i) D x.2) :
    dy j (tst c ε a φ i j) x =
      (Axi.eR x.2 j * ctLift c ε a φ x) • realCL (D (EuclideanSpace.single j 1)) +
      (Axi.eR x.2 j * fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single j 1) +
        ctLift c ε a φ x * Axi.eRD x.2 (EuclideanSpace.single j 1) j) • realCL (Evec i x.2) := by
  have hΨ : HasFDerivAt (ctLift c ε a φ) (fderiv ℝ (ctLift c ε a φ) x) x :=
    ((ctLift_contDiff hc hε hφ).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hA0 : HasFDerivAt (fun y : Space => Axi.eR y j)
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (Axi.eRD x.2)) x.2 :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x.2 (Axi.hasFDerivAt_eR hy)
  have hA : HasFDerivAt (fun x : ℝ × Space => Axi.eR x.2 j)
      (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (Axi.eRD x.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ Space)) x :=
    hA0.comp x hasFDerivAt_snd
  have hE0 : HasFDerivAt (fun y : Space => realCL (Evec i y)) (realCL.comp D) x.2 :=
    realCL.hasFDerivAt.comp x.2 hD
  have hE : HasFDerivAt (fun x : ℝ × Space => realCL (Evec i x.2))
      ((realCL.comp D).comp (ContinuousLinearMap.snd ℝ ℝ Space)) x :=
    hE0.comp x hasFDerivAt_snd
  have h := (hA.mul hΨ).smul hE
  have h2 : HasFDerivAt (tst c ε a φ i j) _ x := h
  unfold dy
  rw [h2.fderiv]
  simp [coordVec_eq, mul_comm, add_comm]

end UnforcedLeray.Short.IIb.GWQ
