import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Lap.Ode

/-!
# The Laplacian of the primitive field `Ψ_Z e_z` (`TCLap` leaves)

Source `the November 2 reference manuscript` 4176-4214:
`ΔΨ_Z e_z = (2Z_z + ρ(∂_ρZ_z - ∂_zZ_ρ)) e_z`, from `∇Ψ_Z = (y₁Z_z, y₂Z_z, -ϱ Z_ρ)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

variable {X : Space → Space} {a : ℝ}

theorem tcl_fderiv_coord (y v : Space) (i : Fin 3) :
    fderiv ℝ (fun y' : Space => y' i) y v = v i := by
  have := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt (x := y)
  simpa using congrArg (fun L : Space →L[ℝ] ℝ => L v) this.fderiv

theorem tcl_physLap_smul (u : Space → ℝ) (d : Fin 3 → Space → ℝ) (c : Space) {y : Space}
    {U : Set Space} (hU : U ∈ nhds y)
    (hu : ∀ y' ∈ U, DifferentiableAt ℝ u y')
    (hd : ∀ (j : Fin 3), ∀ y' ∈ U, fderiv ℝ u y' (coordinateVector j) = d j y')
    (hdy : ∀ j, DifferentiableAt ℝ (d j) y) :
    physLap (fun y' => u y' • c) y = (∑ j : Fin 3, fderiv ℝ (d j) y (coordinateVector j)) • c := by
  unfold physLap
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold physPd2 physPd
  have heq : (fun y' => fderiv ℝ (fun y' => u y' • c) y' (coordinateVector j)) =ᶠ[nhds y]
      fun y' => d j y' • c := by
    filter_upwards [hU] with y' hy'
    rw [fderiv_smul_const (hu y' hy')]
    simp [hd j y' hy']
  rw [heq.fderiv_eq, fderiv_smul_const (hdy j)]
  simp


theorem tcl_fd_mul (i : Fin 3) {f : Space → ℝ} {y : Space} (hf : DifferentiableAt ℝ f y)
    (v : Space) :
    fderiv ℝ (fun y' : Space => y' i * f y') y v = y i * fderiv ℝ f y v + f y * v i := by
  have hc : HasFDerivAt (fun y' : Space => y' i) (EuclideanSpace.proj i : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt
  have h := hc.mul hf.hasFDerivAt
  have e : (fun y' : Space => y' i * f y') = (fun y' : Space => y' i) * f := rfl
  rw [e, h.fderiv]
  simp

theorem tcb_axiC2 {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) : AxiC2 (sepX0 ν μ T τ) (R * Real.sqrt (5 * ν / 6)) where
  ha := H.ha
  smooth := tcb_smooth' H τ
  rep0 := fun y hy => (tcb_rep H.hν H.hμ H.ha H.hP H.hT H.hM H.hA τ hy).1
  rep1 := fun y hy => (tcb_rep H.hν H.hμ H.ha H.hP H.hT H.hM H.hA τ hy).2.1
  rep2 := fun y hy => (tcb_rep H.hν H.hμ H.ha H.hP H.hT H.hM H.hA τ hy).2.2
  div := fun y hy => tcb_div H.hν H.hμ H.ha H.hP H.hT H.hM τ hy

/-- `ΔΨ_Z e_z = (2 Z_z + ϱ (∂_ρ Z_z - ∂_z Z_ρ)) e_z`. -/
theorem tcl_lapPsi {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) {y : Space} (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    physLap (psiFld (sepX0 ν μ T) τ) y =
      (2 * sepX0 ν μ T τ y 2 +
        ϱ y * tclG (sepX0 ν μ T τ) (y 2) (ϱ y)) • (coordinateVector 2 : Space) := by
  have HA := tcb_axiC2 H τ
  have hρ : 0 < ϱ y := lt_of_le_of_lt H.ha hy
  have hU : IsOpen {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} :=
    isOpen_lt continuous_const continuous_ϱ
  have d0 : DifferentiableAt ℝ (fun y' : Space => y' 0) y :=
    (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).differentiableAt
  have d1 : DifferentiableAt ℝ (fun y' : Space => y' 1) y :=
    (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).differentiableAt
  let dd : Fin 3 → Space → ℝ := ![fun y' => y' 0 * sepX0 ν μ T τ y' 2,
    fun y' => y' 1 * sepX0 ν μ T τ y' 2,
    fun y' => -(y' 0 * sepX0 ν μ T τ y' 0 + y' 1 * sepX0 ν μ T τ y' 1)]
  have hdy : ∀ j, DifferentiableAt ℝ (dd j) y := by
    intro j
    fin_cases j
    · exact d0.mul (HA.dc 2 hy)
    · exact d1.mul (HA.dc 2 hy)
    · exact ((d0.mul (HA.dc 0 hy)).add (d1.mul (HA.dc 1 hy))).neg
  have hfd : ∀ j y', R * Real.sqrt (5 * ν / 6) < ϱ y' → fderiv ℝ (fun y' : Space =>
      outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)) y' (coordinateVector j) = dd j y' := by
    intro j y' hy'
    have hρ' : 0 < ϱ y' := lt_of_le_of_lt H.ha hy'
    have hdu := tcb_du H τ hy' (coordinateVector j)
    obtain ⟨r0, r1, r2⟩ := tcb_rep H.hν H.hμ H.ha H.hP H.hT H.hM H.hA τ hy'
    have hsq := tcl_sqsum hρ'
    rw [hdu]
    fin_cases j
    · show _ = y' 0 * sepX0 ν μ T τ y' 2
      simp [coordinateVector, r2]
    · show _ = y' 1 * sepX0 ν μ T τ y' 2
      simp [coordinateVector, r2]
    · show _ = -(y' 0 * sepX0 ν μ T τ y' 0 + y' 1 * sepX0 ν μ T τ y' 1)
      rw [r0, r1]
      simp [coordinateVector]
      field_simp
      linear_combination (sepX0 ν μ T τ (meridPt y')).ofLp 0 * hsq
  have key := tcl_physLap_smul (fun y' : Space => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)) dd
    (coordinateVector 2 : Space) (y := y)
    (U := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y}) (hU.mem_nhds hy)
    (fun y' hy' => tcb_u_diff H τ hy') (fun j y' hy' => hfd j y' hy') hdy
  show physLap (fun y' => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2) • (coordinateVector 2 : Space)) y = _
  rw [key]
  congr 1
  have f0 : fderiv ℝ (dd 0) y (coordinateVector 0) =
      y 0 * fderiv ℝ (fun y => sepX0 ν μ T τ y 2) y (coordinateVector 0) +
        sepX0 ν μ T τ y 2 := by
    have := tcl_fd_mul 0 (HA.dc 2 hy) (coordinateVector 0)
    show fderiv ℝ (fun y' : Space => y' 0 * sepX0 ν μ T τ y' 2) y (coordinateVector 0) = _
    rw [this]
    simp [coordinateVector]
  have f1 : fderiv ℝ (dd 1) y (coordinateVector 1) =
      y 1 * fderiv ℝ (fun y => sepX0 ν μ T τ y 2) y (coordinateVector 1) +
        sepX0 ν μ T τ y 2 := by
    have := tcl_fd_mul 1 (HA.dc 2 hy) (coordinateVector 1)
    show fderiv ℝ (fun y' : Space => y' 1 * sepX0 ν μ T τ y' 2) y (coordinateVector 1) = _
    rw [this]
    simp [coordinateVector]
  have f2 : fderiv ℝ (dd 2) y (coordinateVector 2) =
      -(y 0 * fderiv ℝ (fun y => sepX0 ν μ T τ y 0) y (coordinateVector 2) +
        y 1 * fderiv ℝ (fun y => sepX0 ν μ T τ y 1) y (coordinateVector 2)) := by
    show fderiv ℝ (fun y' : Space => -(y' 0 * sepX0 ν μ T τ y' 0 + y' 1 * sepX0 ν μ T τ y' 1))
      y (coordinateVector 2) = _
    have g0 := tcl_fd_mul 0 (HA.dc 0 hy) (coordinateVector 2)
    have g1 := tcl_fd_mul 1 (HA.dc 1 hy) (coordinateVector 2)
    have m0 : DifferentiableAt ℝ (fun y' : Space => y' 0 * sepX0 ν μ T τ y' 0) y := d0.mul (HA.dc 0 hy)
    have m1 : DifferentiableAt ℝ (fun y' : Space => y' 1 * sepX0 ν μ T τ y' 1) y := d1.mul (HA.dc 1 hy)
    rw [fderiv_fun_neg, fderiv_fun_add m0 m1]
    simp only [neg_apply, ContinuousLinearMap.add_apply]
    rw [g0, g1]
    simp [coordinateVector]
  rw [Fin.sum_univ_three, f0, f1, f2]
  have r1 := HA.r1 hy
  have r2 := HA.r2 hy
  unfold tclG
  have hm : meridPt y = (!₂[ϱ y, 0, y 2] : Space) := rfl
  rw [hm] at r1 r2
  linarith [r1, r2]

end UnforcedLeray.Short.PartIIIb.Concrete
