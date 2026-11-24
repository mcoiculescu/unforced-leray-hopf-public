import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonD3

/-!
# `NewtonD3Rot`: rotation covariance of `D³N` off `0` (task `PartIII-b:C/srcL/7/2`)

Source of record: `the November 2 reference manuscript`, lines 4776-4782
(`N(x) = 1/(4π|x|)` is rotation invariant).

Mirrors `XmtRefl.newtonD3_reflY` with the rotation `R_θ = rotAxL θ` in place of the reflection:
`N ∘ R_θ = N` gives `G_k(R_θ z) = Σ_d R_{kd} G_d(z)` (`G_k = ∂_k N`), hence
`H_jk(R_θ y) = Σ_{d,b} R_{kd} R_{jb} H_{bd}(y)` (`H_jk = ∂_j G_k`) on `ℝ³ \ {0}`, and
differentiating this identity at `w ≠ 0` (in the direction `R_θ⁻¹ e_i`) gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A linear functional on `ℝ³` expands in the standard basis. -/
theorem nd3r_lin_expand (L : Vec3 →L[ℝ] ℝ) (v : Vec3) :
    L v = ∑ d, v d * L (Pi.single d 1) := by
  have hv : v = ∑ d, v d • (Pi.single d (1 : ℝ) : Vec3) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, smul_eq_mul]

theorem nd3r_rot_inv (θ : ℝ) (y : Vec3) : rotAx θ (rotAx (-θ) y) = y := by
  simpa using rotAx_neg_rotAx (-θ) y

theorem nd3r_neg_single (θ : ℝ) (k : Fin 3) :
    rotAx (-θ) (Pi.single k 1) = fun d => rotMat θ k d := by
  funext d
  fin_cases k <;> fin_cases d <;>
    simp [rotAx, rotMat, Pi.single_apply, Real.cos_neg, Real.sin_neg]

/-- `N ∘ R_θ = N` differentiated: the gradient of `N` is rotated. -/
theorem nd3r_fderiv_newtonN (θ : ℝ) (z v : Vec3) :
    fderiv ℝ newtonN (rotAx θ z) (rotAx θ v) = fderiv ℝ newtonN z v := by
  have h1 : fderiv ℝ (fun y => newtonN (rotAx θ y)) z =
      (fderiv ℝ newtonN (rotAx θ z)).comp (rotAxL θ : Vec3 →L[ℝ] Vec3) :=
    ContinuousLinearEquiv.comp_right_fderiv (f := newtonN) (iso := rotAxL θ)
  have h2 : (fun y => newtonN (rotAx θ y)) = newtonN := funext fun y => newtonN_rotAx θ y
  rw [h2] at h1
  have h4 := congrArg (fun L : Vec3 →L[ℝ] ℝ => L v) h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, rotAxL_apply] at h4
  exact h4.symm

/-- `G_k(R_θ z) = Σ_d R_{kd} G_d(z)` for all `z`. -/
theorem nd3r_GG (θ : ℝ) (k : Fin 3) (z : Vec3) :
    NewtonD3.GG k (rotAx θ z) = ∑ d, rotMat θ k d * NewtonD3.GG d z := by
  have h := nd3r_fderiv_newtonN θ z (rotAx (-θ) (Pi.single k 1))
  rw [nd3r_rot_inv] at h
  unfold NewtonD3.GG
  rw [h, nd3r_neg_single θ k, nd3r_lin_expand (fderiv ℝ newtonN z)]

/-- `H_jk(R_θ y) = Σ_{d,b} R_{kd} R_{jb} H_{bd}(y)` for `y ≠ 0`. -/
theorem nd3r_HH (θ : ℝ) (j k : Fin 3) (y : Vec3) (hy : y ≠ 0) :
    NewtonD3.HH j k (rotAx θ y) =
      ∑ d, rotMat θ k d * ∑ b, rotMat θ j b * NewtonD3.HH b d y := by
  have hDiff : ∀ d, DifferentiableAt ℝ (NewtonD3.GG d) y := fun d =>
    NewtonD3.diffAt_of_punct (NewtonD3.GG_contDiffOn d) (show y ∈ NewtonD3.punct from hy)
  have hc : fderiv ℝ (fun z => NewtonD3.GG k (rotAx θ z)) y =
      (fderiv ℝ (NewtonD3.GG k) (rotAx θ y)).comp (rotAxL θ : Vec3 →L[ℝ] Vec3) :=
    ContinuousLinearEquiv.comp_right_fderiv (f := NewtonD3.GG k) (iso := rotAxL θ)
  have hsum : fderiv ℝ (fun z => NewtonD3.GG k (rotAx θ z)) y =
      ∑ d, rotMat θ k d • fderiv ℝ (NewtonD3.GG d) y := by
    have hfun : (fun z => NewtonD3.GG k (rotAx θ z)) =
        fun z => ∑ d, rotMat θ k d * NewtonD3.GG d z := funext fun z => nd3r_GG θ k z
    rw [hfun]
    exact (HasFDerivAt.fun_sum (u := Finset.univ) fun d _ =>
      (hDiff d).hasFDerivAt.const_mul (rotMat θ k d)).fderiv
  have hstep : fderiv ℝ (NewtonD3.GG k) (rotAx θ y) (Pi.single j 1) =
      fderiv ℝ (fun z => NewtonD3.GG k (rotAx θ z)) y (rotAx (-θ) (Pi.single j 1)) := by
    rw [hc]
    show _ = fderiv ℝ (NewtonD3.GG k) (rotAx θ y) (rotAx θ (rotAx (-θ) (Pi.single j 1)))
    rw [nd3r_rot_inv]
  calc fderiv ℝ (NewtonD3.GG k) (rotAx θ y) (Pi.single j 1)
      = fderiv ℝ (fun z => NewtonD3.GG k (rotAx θ z)) y (rotAx (-θ) (Pi.single j 1)) := hstep
    _ = (∑ d, rotMat θ k d • fderiv ℝ (NewtonD3.GG d) y) (rotAx (-θ) (Pi.single j 1)) := by
        rw [hsum]
    _ = ∑ d, rotMat θ k d * fderiv ℝ (NewtonD3.GG d) y (rotAx (-θ) (Pi.single j 1)) := by
        simp [ContinuousLinearMap.sum_apply]
    _ = ∑ d, rotMat θ k d * ∑ b, rotMat θ j b * NewtonD3.HH b d y := by
        refine Finset.sum_congr rfl fun d _ => ?_
        congr 1
        rw [nd3r_neg_single θ j, nd3r_lin_expand (fderiv ℝ (NewtonD3.GG d) y)]
        rfl

/-- **`NewtonD3Rot`** (source 4776-4782): rotation covariance of the third Newton derivatives off
`0`. -/
theorem newtonD3Rot : NewtonD3Rot := by
  intro θ w hw i j k
  have hEv : (fun y => NewtonD3.HH j k (rotAx θ y)) =ᶠ[𝓝 w]
      (fun y => ∑ d, rotMat θ k d * ∑ b, rotMat θ j b * NewtonD3.HH b d y) := by
    filter_upwards [NewtonD3.isOpen_punct.mem_nhds (show w ∈ NewtonD3.punct from hw)] with y hy
    exact nd3r_HH θ j k y hy
  have hF : ∀ b d, DifferentiableAt ℝ (NewtonD3.HH b d) w := fun b d =>
    NewtonD3.diffAt_of_punct (NewtonD3.HH_contDiffOn b d) (show w ∈ NewtonD3.punct from hw)
  have hR : fderiv ℝ (fun y => ∑ d, rotMat θ k d * ∑ b, rotMat θ j b * NewtonD3.HH b d y) w =
      ∑ d, rotMat θ k d • ∑ b, rotMat θ j b • fderiv ℝ (NewtonD3.HH b d) w := by
    exact (HasFDerivAt.fun_sum (u := Finset.univ) fun d _ =>
      (HasFDerivAt.fun_sum (u := Finset.univ) fun b _ =>
        (hF b d).hasFDerivAt.const_mul (rotMat θ j b)).const_mul (rotMat θ k d)).fderiv
  have hL : fderiv ℝ (fun y => NewtonD3.HH j k (rotAx θ y)) w (rotAx (-θ) (Pi.single i 1)) =
      newtonD3 (rotAx θ w) i j k := by
    have h1 : fderiv ℝ (fun y => NewtonD3.HH j k (rotAx θ y)) w =
        (fderiv ℝ (NewtonD3.HH j k) (rotAx θ w)).comp (rotAxL θ : Vec3 →L[ℝ] Vec3) :=
      ContinuousLinearEquiv.comp_right_fderiv (f := NewtonD3.HH j k) (iso := rotAxL θ)
    rw [h1]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, rotAxL_apply,
      nd3r_rot_inv]
    rfl
  have hexp : ∀ b d, fderiv ℝ (NewtonD3.HH b d) w (rotAx (-θ) (Pi.single i 1)) =
      ∑ a, rotMat θ i a * newtonD3 w a b d := by
    intro b d
    rw [nd3r_neg_single θ i, nd3r_lin_expand (fderiv ℝ (NewtonD3.HH b d) w)]
    rfl
  calc newtonD3 (rotAx θ w) i j k
      = fderiv ℝ (fun y => NewtonD3.HH j k (rotAx θ y)) w (rotAx (-θ) (Pi.single i 1)) := hL.symm
    _ = fderiv ℝ (fun y => ∑ d, rotMat θ k d * ∑ b, rotMat θ j b * NewtonD3.HH b d y) w
          (rotAx (-θ) (Pi.single i 1)) := by rw [hEv.fderiv_eq]
    _ = (∑ d, rotMat θ k d • ∑ b, rotMat θ j b • fderiv ℝ (NewtonD3.HH b d) w)
          (rotAx (-θ) (Pi.single i 1)) := by rw [hR]
    _ = ∑ a, ∑ b, ∑ d, rotMat θ i a * rotMat θ j b * rotMat θ k d * newtonD3 w a b d := by
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          hexp]
        simp only [Fin.sum_univ_three]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
