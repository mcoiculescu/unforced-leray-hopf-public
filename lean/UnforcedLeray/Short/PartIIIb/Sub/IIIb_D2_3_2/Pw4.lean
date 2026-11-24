import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.PointwiseDefs

/-!
# `pwDivSym_proved`: divergence of a symmetrized product (source 4258)

`div(a ⊗ b + b ⊗ a) = a·∇b + b·∇a` for solenoidal `a, b`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Coordinate `j` of a spatial field, as a continuous linear functional on its derivative. -/
theorem pw4_coord_hasFDerivAt (f : Space → Space) (j : Fin 3) (y : Space)
    (hf : DifferentiableAt ℝ f y) :
    HasFDerivAt (fun y' => f y' j) ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ f y)) y :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y hf.hasFDerivAt

theorem pw4_sym_fderiv (a b : Space → Space) (y : Space) (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) (i j : Fin 3) (v : Space) :
    fderiv ℝ (fun y' => a y' j * b y' i + b y' j * a y' i) y v =
      fderiv ℝ a y v j * b y i + a y j * fderiv ℝ b y v i +
        (fderiv ℝ b y v j * a y i + b y j * fderiv ℝ a y v i) := by
  have h1 := (pw4_coord_hasFDerivAt a j y ha).mul (pw4_coord_hasFDerivAt b i y hb)
  have h2 := (pw4_coord_hasFDerivAt b j y hb).mul (pw4_coord_hasFDerivAt a i y ha)
  have hf : fderiv ℝ (fun y' => a y' j * b y' i + b y' j * a y' i) y =
      _ := (h1.add h2).fderiv
  rw [hf]
  simp [ContinuousLinearMap.comp_apply]
  ring

theorem pw4_sum_coord (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j := by
  ext k
  simp [coordinateVector, Pi.single_apply]

theorem pw4_fderiv_eq_sum (b : Space → Space) (y v : Space) :
    fderiv ℝ b y v = ∑ j : Fin 3, v j • fderiv ℝ b y (coordinateVector j) := by
  conv_lhs => rw [pw4_sum_coord v]
  simp [map_sum, map_smul]

theorem pwDivSym_proved : PwDivSym := by
  intro a b ha hb hdiva hdivb y
  have hae : DifferentiableAt ℝ a y := (ha.differentiable (by simp)) y
  have hbe : DifferentiableAt ℝ b y := (hb.differentiable (by simp)) y
  have hd1 : ∑ j : Fin 3, fderiv ℝ a y (coordinateVector j) j = 0 := by
    simpa only [physPd] using hdiva y
  have hd2 : ∑ j : Fin 3, fderiv ℝ b y (coordinateVector j) j = 0 := by
    simpa only [physPd] using hdivb y
  ext i
  simp only [physDivSym, PiLp.toLp_apply]
  simp only [pw4_sym_fderiv a b y hae hbe i _, Finset.sum_add_distrib]
  rw [pw4_fderiv_eq_sum b y (a y), pw4_fderiv_eq_sum a y (b y)]
  have e1 : ∑ x : Fin 3, (fderiv ℝ a y (coordinateVector x)).ofLp x * (b y).ofLp i = 0 := by
    rw [← Finset.sum_mul, hd1, zero_mul]
  have e2 : ∑ x : Fin 3, (fderiv ℝ b y (coordinateVector x)).ofLp x * (a y).ofLp i = 0 := by
    rw [← Finset.sum_mul, hd2, zero_mul]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    PiLp.add_apply]
  linear_combination e1 + e2
