import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.HDeriv1

/-!
# Bound of the total `h`-derivative of the scalar kernel along `(1, v)`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem Jt_dir_bound (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
    ∀ (M : Matrix (Fin 3) (Fin 3) ℝ),
      ContDiff ℝ 2 (fun x' => xKer ν μ h x' M) ∧
      (∀ x : Space, DifferentiableAt ℝ (fun h' => xKer ν μ h' x M) h) ∧
      ∀ x : Space, x ≠ 0 →
        ‖xKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M ∧
        ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M ∧
        ‖iteratedFDeriv ℝ 2 (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 6)⁻¹ * IIIa.tensorNorm M ∧
        ‖deriv (fun h' => xKer ν μ h' x M) h‖ ≤
          C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M ∧
        ‖wKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M)
    (ν μ : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) {h : ℝ} (hh : 0 < h)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {x : Space} (hx : x ≠ 0) (v : Space) :
    |fderiv ℝ (Jt ν μ M) (h, x) (1, v)| ≤
      C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M *
        ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹ + (‖x‖ ^ 5)⁻¹ * ‖v‖) := by
  rw [Jt_dir ν μ hν M hh x v]
  obtain ⟨-, -, hb⟩ := hC ν μ h hν hμ0 hμ1 hh M
  obtain ⟨-, -, hp1, -⟩ := xKerA_props C hC0 hC ν μ h hν hμ0 hμ1 hh M
  have hd : HasDerivAt (fun h' => xKerA ν μ h' M x) ((deriv (fun h' => xKer ν μ h' x M) h) 2) h := by
    have := (kb_xKer_hasDeriv ν μ h hν hh x M)
    have h2 := (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h this
    rw [this.deriv]
    exact h2
  rw [hd.deriv]
  have e1 : |(deriv (fun h' => xKer ν μ h' x M) h) 2| ≤ ‖deriv (fun h' => xKer ν μ h' x M) h‖ := by
    have := PiLp.norm_apply_le (deriv (fun h' => xKer ν μ h' x M) h) 2
    simpa [Real.norm_eq_abs] using this
  have e2 : |fderiv ℝ (fun x' => xKerA ν μ h M x') x v| ≤
      C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M * (‖x‖ ^ 5)⁻¹ * ‖v‖ := by
    have hfd := hp1 x hx
    rw [norm_iteratedFDeriv_one] at hfd
    have := (fderiv ℝ (fun x' => xKerA ν μ h M x') x).le_opNorm v
    rw [Real.norm_eq_abs] at this
    calc |fderiv ℝ (fun x' => xKerA ν μ h M x') x v| ≤ _ := this
      _ ≤ _ := mul_le_mul_of_nonneg_right hfd (norm_nonneg _)
  have e3 := (hb x hx).2.2.2.1
  calc |(deriv (fun h' => xKer ν μ h' x M) h) 2 + fderiv ℝ (fun x' => xKerA ν μ h M x') x v|
      ≤ |(deriv (fun h' => xKer ν μ h' x M) h) 2| + |fderiv ℝ (fun x' => xKerA ν μ h M x') x v| :=
        abs_add_le _ _
    _ ≤ _ := by
      refine (add_le_add (e1.trans e3) e2).trans (le_of_eq ?_)
      ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
