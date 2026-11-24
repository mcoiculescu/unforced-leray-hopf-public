import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.PointwiseDefs

/-!
# `pwPressure_proved`: the pressure identity (source 4237-4240)

`-[∇q, X] = ∇(X·∇q) - (DX + DXᵀ)∇q` for smooth `X` and `q`, using symmetry of the Hessian of `q`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Coordinate `i` of a spatial field, as a continuous linear functional on its derivative. -/
theorem pw3_coord_hasFDerivAt (f : Space → Space) (j : Fin 3) (y : Space)
    (hf : DifferentiableAt ℝ f y) :
    HasFDerivAt (fun y' => f y' j) ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ f y)) y :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y hf.hasFDerivAt

theorem pw3_comp_apply (F : Space → Space) (y v : Space) (hF : DifferentiableAt ℝ F y) (i : Fin 3) :
    fderiv ℝ F y v i = fderiv ℝ (fun y' => F y' i) y v := by
  rw [(pw3_coord_hasFDerivAt F i y hF).fderiv]
  rfl

theorem pw3_sum_coord (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j := by
  ext k
  simp [coordinateVector, Pi.single_apply]

theorem pw3_fderiv_eq_sum (b : Space → Space) (y v : Space) :
    fderiv ℝ b y v = ∑ j : Fin 3, v j • fderiv ℝ b y (coordinateVector j) := by
  conv_lhs => rw [pw3_sum_coord v]
  simp [map_sum, map_smul]

theorem pw3_hess_comp (q : Space → ℝ) (y v : Space) (hqd : DifferentiableAt ℝ (fderiv ℝ q) y)
    (i : Fin 3) :
    fderiv ℝ (fun y' => fderiv ℝ q y' (coordinateVector i)) y v =
      fderiv ℝ (fderiv ℝ q) y v (coordinateVector i) := by
  have h : HasFDerivAt (fun y' => fderiv ℝ q y' (coordinateVector i))
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).comp (fderiv ℝ (fderiv ℝ q) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).hasFDerivAt.comp y hqd.hasFDerivAt
  rw [h.fderiv]
  simp

theorem pw3_prod_fderiv (X : Space → Space) (q : Space → ℝ) (j : Fin 3) (y v : Space)
    (hX : DifferentiableAt ℝ X y) (hqj : DifferentiableAt ℝ (fun z => fderiv ℝ q z (coordinateVector j)) y) :
    fderiv ℝ (fun y' => X y' j * fderiv ℝ q y' (coordinateVector j)) y v =
      fderiv ℝ X y v j * fderiv ℝ q y (coordinateVector j) +
        X y j * fderiv ℝ (fun z => fderiv ℝ q z (coordinateVector j)) y v := by
  have h1 := (pw3_coord_hasFDerivAt X j y hX).mul hqj.hasFDerivAt
  have hf : fderiv ℝ (fun y' => X y' j * fderiv ℝ q y' (coordinateVector j)) y =
      _ := h1.fderiv
  rw [hf]
  simp [ContinuousLinearMap.comp_apply]
  ring

theorem pwPressure_proved : PwPressure := by
  intro X q hX hq y
  have hXe : DifferentiableAt ℝ X y := (hX.differentiable (by simp)) y
  have hqd : DifferentiableAt ℝ (fderiv ℝ q) y :=
    ((hq.fderiv_right (m := 1) (by simp)).differentiable (by simp)) y
  have hqe : ∀ j : Fin 3, DifferentiableAt ℝ (fun z => fderiv ℝ q z (coordinateVector j)) y :=
    fun j => hqd.clm_apply (differentiableAt_const _)
  have hsym : ∀ v w, fderiv ℝ (fderiv ℝ q) y v w = fderiv ℝ (fderiv ℝ q) y w v :=
    (hq.contDiffAt.isSymmSndFDerivAt (by simp))
  have hGd : DifferentiableAt ℝ (physGrad q) y := by
    refine (differentiableAt_piLp 2).2 (fun i => ?_)
    simpa [physGrad] using hqe i
  have hG : (fun y' => ∑ j : Fin 3, X y' j * physGrad q y' j) =
      fun y' => ∑ j : Fin 3, X y' j * fderiv ℝ q y' (coordinateVector j) := by
    funext z
    simp [physGrad]
  rw [hG]
  ext i
  have hA1 : fderiv ℝ X y (physGrad q y) i =
      ∑ j : Fin 3, fderiv ℝ q y (coordinateVector j) * fderiv ℝ X y (coordinateVector j) i := by
    conv_lhs => rw [pw3_fderiv_eq_sum X y (physGrad q y)]
    simp [physGrad, WithLp.ofLp_sum, Finset.sum_apply, mul_comm]
  have hA2 : fderiv ℝ (physGrad q) y (X y) i =
      ∑ j : Fin 3, X y j * fderiv ℝ (fderiv ℝ q) y (coordinateVector j) (coordinateVector i) := by
    rw [pw3_comp_apply (physGrad q) y (X y) hGd i]
    have hfun : (fun y' => physGrad q y' i) = fun y' => fderiv ℝ q y' (coordinateVector i) := by
      funext z
      simp [physGrad]
    rw [hfun, pw3_hess_comp q y (X y) hqd i]
    conv_lhs => rw [pw3_sum_coord (X y)]
    simp [map_sum, map_smul, sum_apply, smul_apply]
  have hA3 : (physGrad (fun y' => ∑ j : Fin 3, X y' j * fderiv ℝ q y' (coordinateVector j)) y) i =
      ∑ j : Fin 3, (fderiv ℝ X y (coordinateVector i) j * fderiv ℝ q y (coordinateVector j) +
        X y j * fderiv ℝ (fderiv ℝ q) y (coordinateVector i) (coordinateVector j)) := by
    simp only [physGrad, PiLp.toLp_apply]
    rw [fderiv_fun_sum (A := fun (j : Fin 3) (z : Space) => X z j * fderiv ℝ q z (coordinateVector j))
      (fun j _ => (((pw3_coord_hasFDerivAt X j y hXe).differentiableAt).mul (hqe j) : _))]
    simp only [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pw3_prod_fderiv X q j y _ hXe (hqe j), pw3_hess_comp q y _ hqd j]
  simp only [physBracket, PiLp.neg_apply, PiLp.sub_apply]
  rw [hA1, hA2, hA3]
  have hsumsym : ∑ j : Fin 3, X y j * fderiv ℝ (fderiv ℝ q) y (coordinateVector j) (coordinateVector i) =
      ∑ j : Fin 3, X y j * fderiv ℝ (fderiv ℝ q) y (coordinateVector i) (coordinateVector j) :=
    Finset.sum_congr rfl (fun j _ => by rw [hsym])
  simp only [physDXp, physPd, PiLp.toLp_apply, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_add]
  have hcomm : ∑ x : Fin 3, fderiv ℝ q y (coordinateVector x) * ((fderiv ℝ X y) (coordinateVector x)).ofLp i =
      ∑ x : Fin 3, ((fderiv ℝ X y) (coordinateVector x)).ofLp i * fderiv ℝ q y (coordinateVector x) :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  linarith [hsumsym, hcomm]
