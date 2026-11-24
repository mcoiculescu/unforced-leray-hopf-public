import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.PointwiseDefs

/-!
# `pwConvection_proved`: convection cancellation (source 4232-4236)

With `N = u·∇u` and `h = [u, X]`: `-[N, X] + u·∇h + h·∇u = (u⊗u):D²X`.
The leftover `(D²u)(X, u) - (D²u)(u, X)` vanishes by symmetry of the second derivative of `u`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pw2_sum_coord (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j := by
  ext k
  simp [coordinateVector, Pi.single_apply]

theorem pw2_clm_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Space →L[ℝ] F) (v : Space) :
    L v = ∑ j : Fin 3, v j • L (coordinateVector j) := by
  conv_lhs => rw [pw2_sum_coord v]
  simp [map_sum, map_smul]

theorem pw2_hess_vec (X : Space → Space) (y v : Space) (hd : DifferentiableAt ℝ (fderiv ℝ X) y)
    (l : Fin 3) :
    fderiv ℝ (fun z => fderiv ℝ X z (coordinateVector l)) y v =
      fderiv ℝ (fderiv ℝ X) y v (coordinateVector l) := by
  have h : HasFDerivAt (fun z => fderiv ℝ X z (coordinateVector l))
      ((ContinuousLinearMap.apply ℝ Space (coordinateVector l)).comp (fderiv ℝ (fderiv ℝ X) y)) y :=
    (ContinuousLinearMap.apply ℝ Space (coordinateVector l)).hasFDerivAt.comp y hd.hasFDerivAt
  rw [h.fderiv]
  simp

theorem pwConvection_proved : PwConvection := by
  intro u X hu hX y
  have hue : DifferentiableAt ℝ u y := (hu.differentiable (by simp)) y
  have hXe : DifferentiableAt ℝ X y := (hX.differentiable (by simp)) y
  have hud : DifferentiableAt ℝ (fderiv ℝ u) y :=
    ((hu.fderiv_right (m := 1) (by simp)).differentiable (by simp)) y
  have hXd : DifferentiableAt ℝ (fderiv ℝ X) y :=
    ((hX.fderiv_right (m := 1) (by simp)).differentiable (by simp)) y
  have hsymu : ∀ v w, fderiv ℝ (fderiv ℝ u) y v w = fderiv ℝ (fderiv ℝ u) y w v :=
    (hu.contDiffAt.isSymmSndFDerivAt (by simp))
  have hN : ∀ w, fderiv ℝ (fun z => fderiv ℝ u z (u z)) y w =
      fderiv ℝ u y (fderiv ℝ u y w) + fderiv ℝ (fderiv ℝ u) y w (u y) := by
    intro w
    rw [fderiv_clm_apply hud hue]
    simp
  have hh : ∀ w, fderiv ℝ (physBracket u X) y w =
      fderiv ℝ (fderiv ℝ X) y w (u y) + fderiv ℝ X y (fderiv ℝ u y w) -
        (fderiv ℝ (fderiv ℝ u) y w (X y) + fderiv ℝ u y (fderiv ℝ X y w)) := by
    intro w
    have hfun : physBracket u X = fun z => fderiv ℝ X z (u z) - fderiv ℝ u z (X z) := rfl
    rw [hfun, fderiv_fun_sub (hXd.clm_apply hue) (hud.clm_apply hXe),
      fderiv_clm_apply hXd hue, fderiv_clm_apply hud hXe]
    simp
    abel
  have h1 : physBracket (fun y' => fderiv ℝ u y' (u y')) X y =
      fderiv ℝ X y (fderiv ℝ u y (u y)) -
        (fderiv ℝ u y (fderiv ℝ u y (X y)) + fderiv ℝ (fderiv ℝ u) y (X y) (u y)) := by
    simp only [physBracket]
    rw [hN (X y)]
  have h2 : physBracket u X y = fderiv ℝ X y (u y) - fderiv ℝ u y (X y) := rfl
  have hP2 : ∀ j l : Fin 3, physPd2 X j l y =
      fderiv ℝ (fderiv ℝ X) y (coordinateVector j) (coordinateVector l) := by
    intro j l
    show fderiv ℝ (fun z => fderiv ℝ X z (coordinateVector l)) y (coordinateVector j) = _
    exact pw2_hess_vec X y _ hXd l
  have hUUD : physUUD2 u X y = fderiv ℝ (fderiv ℝ X) y (u y) (u y) := by
    unfold physUUD2
    simp only [hP2]
    rw [pw2_clm_sum (fderiv ℝ (fderiv ℝ X) y) (u y)]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, pw2_clm_sum _ (u y),
      Finset.smul_sum, smul_smul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [mul_comm]
  rw [h1, hh (u y), h2, map_sub, hUUD, hsymu (X y) (u y)]
  abel
