import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.A
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2

/-!
# `wardX0DivFree_proved` (PartIII-b:IIIb-D2/3/2/11/2/4)

Source of record: `the November 2 reference manuscript` 3600-3610, 3611-3621.
`X₀ = W_μ - W_{μ+1}` (real parts of the complex `sepW`). The divergence of `X₀` is the real part of
the sum of the divergences of the two `sepW` fields, which vanish off the source disk
(`sepWDivFree_all`), once the real part commutes with the directional derivatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j`-th component of a derivative is the derivative of the `j`-th component. -/
lemma coord_fderiv (F : Space → Space) (y : Space) (hF : DifferentiableAt ℝ F y) (v : Space)
    (j : Fin 3) : fderiv ℝ F y v j = fderiv ℝ (fun x => F x j) y v := by
  have h : HasFDerivAt (fun x => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (F x))
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ F y)) y :=
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt).comp y hF.hasFDerivAt
  have hfun : (fun x => F x j) = fun x => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (F x) := rfl
  rw [hfun, h.fderiv]
  simp

/-- The derivative of a real part of a difference of two complex fields. -/
lemma re_sub_fderiv (A B : Space → ℂ) (y : Space) (hA : DifferentiableAt ℝ A y)
    (hB : DifferentiableAt ℝ B y) (v : Space) :
    fderiv ℝ (fun x => (A x - B x).re) y v = (fderiv ℝ A y v - fderiv ℝ B y v).re := by
  have hG : HasFDerivAt (fun x => A x - B x) (fderiv ℝ A y - fderiv ℝ B y) y :=
    hA.hasFDerivAt.sub hB.hasFDerivAt
  have hre : HasFDerivAt (fun x => (A x - B x).re)
      (Complex.reCLM.comp (fderiv ℝ A y - fderiv ℝ B y)) y :=
    Complex.reCLM.hasFDerivAt.comp y hG
  rw [hre.fderiv]
  simp

theorem wardX0DivFree_proved : WardX0DivFree := by
  intro ν μ R c g hν hR hc hμ hg τ y hy
  obtain ⟨hS1, hS2⟩ := smoothOldSource_proved ν R c g hν hR hc hg
  have hP : 0 < 2 * c / R := by positivity
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hyr : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hD0 := sepWDivFree_all ν (μ : ℂ) _ _ (oldPhys R c g) hν hμ0 hr hP hS1 hS2 τ y hyr
  have hD1 := sepWDivFree_all ν ((μ : ℂ) + 1) _ _ (oldPhys R c g) hν hμ1 hr hP hS1 hS2 τ y hyr
  have hsm0 := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) _ _ (oldPhys R c g) hν hμ0 hr hP
    hS1 hS2 τ
  have hsm1 := sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) _ _ (oldPhys R c g) hν hμ1
    hr hP hS1 hS2 τ
  have hopen : IsOpen {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hdA : ∀ i, DifferentiableAt ℝ
      (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ i) y := fun i =>
    ((hsm0 i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hyr)
  have hdB : ∀ i, DifferentiableAt ℝ
      (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ i) y := fun i =>
    ((hsm1 i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hyr)
  have hF : DifferentiableAt ℝ (fun y' => wardX0 ν μ R c g τ y') y := by
    rw [differentiableAt_piLp]
    intro i
    exact Complex.reCLM.differentiableAt.comp y ((hdA i).sub (hdB i))
  have hcomp : ∀ j : Fin 3, physPd (wardX0 ν μ R c g τ) j y j =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ j) y (coordinateVector j) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ j) y
          (coordinateVector j)).re := by
    intro j
    unfold physPd
    rw [coord_fderiv _ y hF _ j]
    exact re_sub_fderiv _ _ y (hdA j) (hdB j) _
  calc ∑ j : Fin 3, physPd (wardX0 ν μ R c g τ) j y j
      = ∑ j : Fin 3, (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ j) y
          (coordinateVector j) - fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1)
            (oldPhys R c g) y' τ j) y (coordinateVector j)).re :=
        Finset.sum_congr rfl (fun j _ => hcomp j)
    _ = (∑ j : Fin 3, (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ j) y
          (coordinateVector j) - fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1)
            (oldPhys R c g) y' τ j) y (coordinateVector j))).re := (Complex.re_sum _ _).symm
    _ = (∑ j : Fin 3, fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ j) y
          (coordinateVector j) - ∑ j : Fin 3, fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1)
            (oldPhys R c g) y' τ j) y (coordinateVector j)).re := by
        rw [Finset.sum_sub_distrib]
    _ = 0 := by rw [hD0, hD1]; simp

end UnforcedLeray.Short.PartIIIb.Concrete
