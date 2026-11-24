import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Rad.Basic

/-!
# Calculus on half-plane lines for an axisymmetric swirl-free field (`TCLap` leaves)

Source `the November 2 reference manuscript` 4176-4214.
Abstract hypotheses `AxiC2 X a` (meridian representation, `C²`, solenoidal off `ϱ ≤ a`) and the
line-derivative identities used to compute `Ψ_{ΔZ}` and `ΔΨ_Z`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `∂_j ∂_l f` of a scalar function (the derivative in direction `e_j` of `∂_l f`). -/
def sd2 (f : Space → ℝ) (j l : Fin 3) (y : Space) : ℝ :=
  fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector l)) y (coordinateVector j)

theorem tcl_path_rho (z ρ : ℝ) :
    HasDerivAt (fun ρ' : ℝ => (!₂[ρ', 0, z] : Space)) (coordinateVector 0) ρ := by
  have : (fun ρ' : ℝ => (!₂[ρ', 0, z] : Space)) =
      fun ρ' => (!₂[0, 0, z] : Space) + ρ' • (coordinateVector 0 : Space) := by
    funext ρ'
    ext i
    fin_cases i <;> simp [coordinateVector]
  rw [this]
  simpa using ((hasDerivAt_id ρ).smul_const (coordinateVector 0 : Space)).const_add
    (!₂[0, 0, z] : Space)

theorem tcl_path_z (ρ z : ℝ) :
    HasDerivAt (fun z' : ℝ => (!₂[ρ, 0, z'] : Space)) (coordinateVector 2) z := by
  have : (fun z' : ℝ => (!₂[ρ, 0, z'] : Space)) =
      fun z' => (!₂[ρ, 0, 0] : Space) + z' • (coordinateVector 2 : Space) := by
    funext z'
    ext i
    fin_cases i <;> simp [coordinateVector]
  rw [this]
  simpa using ((hasDerivAt_id z).smul_const (coordinateVector 2 : Space)).const_add
    (!₂[ρ, 0, 0] : Space)

theorem tcl_path_line (q v : Space) (s : ℝ) :
    HasDerivAt (fun t : ℝ => q + t • v) v s := by
  simpa using ((hasDerivAt_id s).smul_const v).const_add q

/-- Line derivative of a scalar function. -/
theorem tcl_line {f : Space → ℝ} {q : Space} (v : Space) (s : ℝ)
    (hf : DifferentiableAt ℝ f (q + s • v)) :
    HasDerivAt (fun t : ℝ => f (q + t • v)) (fderiv ℝ f (q + s • v) v) s :=
  hf.hasFDerivAt.comp_hasDerivAt s (tcl_path_line q v s)

/-- The derivative of `∂_w f` along a line is the second derivative. -/
theorem tcl_sd_line {f : Space → ℝ} {y : Space} (hf : ContDiffAt ℝ 2 f y) (v w : Space) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (y + s • v) w)
      (fderiv ℝ (fun y' => fderiv ℝ f y' w) y v) 0 := by
  have hd : DifferentiableAt ℝ (fun y' => fderiv ℝ f y' w) y :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hp := tcl_path_line y v 0
  have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)
  exact this

theorem tcl_hasDeriv_rho {f : Space → ℝ} {z ρ : ℝ} (hf : DifferentiableAt ℝ f (!₂[ρ, 0, z])) :
    HasDerivAt (fun ρ' : ℝ => f (!₂[ρ', 0, z])) (fderiv ℝ f (!₂[ρ, 0, z]) (coordinateVector 0))
      ρ :=
  hf.hasFDerivAt.comp_hasDerivAt ρ (tcl_path_rho z ρ)

theorem tcl_hasDeriv_z {f : Space → ℝ} {z ρ : ℝ} (hf : DifferentiableAt ℝ f (!₂[ρ, 0, z])) :
    HasDerivAt (fun z' : ℝ => f (!₂[ρ, 0, z'])) (fderiv ℝ f (!₂[ρ, 0, z]) (coordinateVector 2))
      z :=
  hf.hasFDerivAt.comp_hasDerivAt z (tcl_path_z ρ z)

/-- Components of the Hessian entries. -/
theorem tcl_physPd2_apply {X : Space → Space} {q : Space} (hX : ContDiffAt ℝ 2 X q)
    (j l i : Fin 3) :
    physPd2 X j l q i = sd2 (fun y => X y i) j l q := by
  have hXd : ∀ᶠ y' in nhds q, DifferentiableAt ℝ X y' :=
    (hX.eventually (by simp)).mono fun y' hy' => hy'.differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (fun y' => fderiv ℝ X y' (coordinateVector l)) q :=
    ((hX.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  unfold physPd2 physPd sd2
  rw [fderiv_apply_coord _ _ _ _ hF]
  have heq : (fun y' => fderiv ℝ X y' (coordinateVector l) i) =ᶠ[nhds q]
      fun y' => fderiv ℝ (fun y => X y i) y' (coordinateVector l) := by
    filter_upwards [hXd] with y' hy'
    exact fderiv_apply_coord _ _ _ _ hy'
  rw [heq.fderiv_eq]

end UnforcedLeray.Short.PartIIIb.Concrete
