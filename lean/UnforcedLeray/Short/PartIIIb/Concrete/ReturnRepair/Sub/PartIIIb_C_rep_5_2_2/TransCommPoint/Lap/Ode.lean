import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Lap.Axi

/-!
# The radial identity `(ρ g)' = ρ (ΔX)_z` on the half plane (`TCLap` leaves)

Source `the November 2 reference manuscript` 4176-4214:
`(ΔZ)_z = (∂_ρ² + ρ⁻¹∂_ρ + ∂_z²)Z_z` and `ρ(ΔZ)_z = ∂_ρ(ρ(∂_ρZ_z - ∂_zZ_ρ))` for solenoidal
axisymmetric swirl-free `Z`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

variable {X : Space → Space} {a : ℝ}

/-- `g(ρ) = ∂_ρ X_z - ∂_z X_ρ` on the half plane at height `z`. -/
def tclG (X : Space → Space) (z ρ : ℝ) : ℝ :=
  fderiv ℝ (fun y => X y 2) (!₂[ρ, 0, z]) (coordinateVector 0) -
    fderiv ℝ (fun y => X y 0) (!₂[ρ, 0, z]) (coordinateVector 2)

theorem tcl_dd {f : Space → ℝ} {ρ z : ℝ} (hf : ContDiffAt ℝ 2 f (!₂[ρ, 0, z])) (l : Fin 3) :
    HasDerivAt (fun ρ' : ℝ => fderiv ℝ f (!₂[ρ', 0, z]) (coordinateVector l))
      (sd2 f 0 l (!₂[ρ, 0, z])) ρ := by
  have hdiff : DifferentiableAt ℝ (fun y' => fderiv ℝ f y' (coordinateVector l)) (!₂[ρ, 0, z]) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  exact tcl_hasDeriv_rho (f := fun y' => fderiv ℝ f y' (coordinateVector l)) hdiff

theorem tcl_physLap_apply2 {X : Space → Space} {q : Space} (hX : ContDiffAt ℝ 2 X q) :
    physLap X q 2 = ∑ j : Fin 3, sd2 (fun y => X y 2) j j q := by
  unfold physLap
  rw [← Finset.sum_congr rfl fun j _ => tcl_physPd2_apply hX j j 2]
  simp

theorem AxiC2.ode (H : AxiC2 X a) {ρ z : ℝ} (hρ : a < ρ) :
    HasDerivAt (fun ρ' : ℝ => ρ' * tclG X z ρ')
      (ρ * physLap X (!₂[ρ, 0, z]) 2) ρ := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt H.ha hρ
  have hp := H.pt z hρ
  have hc2 := H.cdc 2 hp
  have hc0 := H.cdc 0 hp
  have h2 := tcl_dd (z := z) hc2 0
  have h0 := tcl_dd (z := z) hc0 2
  have hg : HasDerivAt (tclG X z) (sd2 (fun y => X y 2) 0 0 (!₂[ρ, 0, z]) -
      sd2 (fun y => X y 0) 0 2 (!₂[ρ, 0, z])) ρ := h2.sub h0
  have hm : HasDerivAt (fun ρ' : ℝ => ρ' * tclG X z ρ')
      (1 * tclG X z ρ + ρ * (sd2 (fun y => X y 2) 0 0 (!₂[ρ, 0, z]) -
        sd2 (fun y => X y 0) 0 2 (!₂[ρ, 0, z]))) ρ := (hasDerivAt_id ρ).mul hg
  refine HasDerivAt.congr_deriv hm ?_
  rw [tcl_physLap_apply2 (H.cd hp)]
  simp only [Fin.sum_univ_three]
  have e1 := H.i1 (z := z) hρ
  have e3 := H.i3 (z := z) hρ
  have e2 := H.i2 hp
  simp only [Fin.sum_univ_three] at e2
  have e4 := tcl_sd_symm hc0 2 0
  unfold tclG
  have hs22 : sd2 (fun y => X y 2) 2 2 (!₂[ρ, 0, z]) =
      -sd2 (fun y => X y 0) 0 2 (!₂[ρ, 0, z]) - fderiv ℝ (fun y => X y 0) (!₂[ρ, 0, z])
        (coordinateVector 2) / ρ := by
    linarith [e2, e3, e4]
  rw [e1, hs22]
  field_simp
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
