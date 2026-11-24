import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Lap.Psi

/-!
# The outward integral of `ρ(ΔX)_z` (`TCLap` leaves)

Source `the November 2 reference manuscript` 4176-4214:
`∫_r^∞ ρ(ΔZ)_z dρ = -r(∂_rZ_z - ∂_zZ_r)(r)` (fundamental theorem of calculus with the decay of
`ρ ∇X₀` and the integrability of `ρ ∇²X₀`, from `|D^jX₀| ≤ K(ϱ - r_o)^{-5/2-j}`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcl_comp_le {X : Space → Space} {q : Space} (hX : DifferentiableAt ℝ X q) (i : Fin 3)
    (j : Fin 3) : |fderiv ℝ (fun y => X y i) q (coordinateVector j)| ≤ ‖fderiv ℝ X q‖ := by
  rw [← fderiv_apply_coord X q (coordinateVector j) i hX]
  calc |fderiv ℝ X q (coordinateVector j) i| = ‖fderiv ℝ X q (coordinateVector j) i‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ X q (coordinateVector j)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖fderiv ℝ X q‖ * ‖(coordinateVector j : Space)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ X q‖ := by
        have : ‖(coordinateVector j : Space)‖ = 1 := by simp [coordinateVector]
        rw [this, mul_one]

theorem tcl_pd2_le {X : Space → Space} {q : Space} (hX : ContDiffAt ℝ 2 X q) (j : Fin 3) :
    ‖physPd2 X j j q‖ ≤ ‖iteratedFDeriv ℝ 2 X q‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ X) q :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have key : physPd2 X j j q = fderiv ℝ (fderiv ℝ X) q (coordinateVector j) (coordinateVector j) := by
    unfold physPd2 physPd
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hn : ‖fderiv ℝ (fderiv ℝ X) q‖ = ‖iteratedFDeriv ℝ 2 X q‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ X) (x := q)]
    exact norm_iteratedFDeriv_fderiv (n := 1)
  have he : ‖(coordinateVector j : Space)‖ = 1 := by simp [coordinateVector]
  rw [key]
  calc ‖fderiv ℝ (fderiv ℝ X) q (coordinateVector j) (coordinateVector j)‖
      ≤ ‖fderiv ℝ (fderiv ℝ X) q (coordinateVector j)‖ * ‖(coordinateVector j : Space)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ X) q‖ * ‖(coordinateVector j : Space)‖ * ‖(coordinateVector j : Space)‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ 2 X q‖ := by rw [he, hn]; ring

theorem tcl_physLap_comp (X : Space → Space) (q : Space) :
    physLap X q 2 = ∑ j : Fin 3, physPd2 X j j q 2 := by
  unfold physLap
  simp

theorem tcl_integral {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ z : ℝ) {r : ℝ} (hr : R * Real.sqrt (5 * ν / 6) < r) :
    ∫ ρ in Ioi r, ρ * physLap (sepX0 ν μ T τ) (!₂[ρ, 0, z]) 2 =
      -(r * tclG (sepX0 ν μ T τ) z r) := by
  have HA := tcb_axiC2 H τ
  set a := R * Real.sqrt (5 * ν / 6) with ha
  set X := sepX0 ν μ T τ with hX
  have hr0 : 0 < r := lt_of_le_of_lt H.ha hr
  obtain ⟨K1, hK1, hb1⟩ := tcb_bound 1 (by norm_num) H.hν H.hμ H.ha H.hP H.hT H.hM
  obtain ⟨K2, hK2, hb2⟩ := tcb_bound 2 (by norm_num) H.hν H.hμ H.ha H.hP H.hT H.hM
  obtain ⟨c1, hc1, hm1⟩ := tcb_maj H.ha hr 1
  obtain ⟨c2, hc2, hm2⟩ := tcb_maj H.ha hr 2
  set f : ℝ → ℝ := fun ρ => ρ * tclG X z ρ with hf
  have hderiv : ∀ ρ ∈ Ioi r, HasDerivAt f (ρ * physLap X (!₂[ρ, 0, z]) 2) ρ := fun ρ hρ =>
    HA.ode (lt_trans hr hρ)
  have hcont : ContinuousWithinAt f (Ici r) r := (HA.ode hr).continuousAt.continuousWithinAt
  -- pointwise bounds
  have hpt1 : ∀ ρ : ℝ, r ≤ ρ → |f ρ| ≤ 2 * K1 * c1 * ρ ^ (-(3 / 2 : ℝ)) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr0 hρ
    have hq : ϱ (!₂[ρ, 0, z] : Space) = ρ := tcb_varrho_pt hρ0.le z
    have hqa : a < ϱ (!₂[ρ, 0, z] : Space) := by rw [hq]; exact lt_of_lt_of_le hr hρ
    have b1 := hb1 τ _ hqa
    rw [hq, norm_iteratedFDeriv_one] at b1
    have hXd : DifferentiableAt ℝ X (!₂[ρ, 0, z]) := (HA.cd hqa).differentiableAt (by norm_num)
    have g1 := tcl_comp_le hXd 2 0
    have g2 := tcl_comp_le hXd 0 2
    have hG : |tclG X z ρ| ≤ 2 * (K1 * (ρ - a) ^ (-(5 / 2 : ℝ) - ((1 : ℕ) : ℝ))) := by
      unfold tclG
      calc _ ≤ |fderiv ℝ (fun y => X y 2) (!₂[ρ, 0, z]) (coordinateVector 0)| +
            |fderiv ℝ (fun y => X y 0) (!₂[ρ, 0, z]) (coordinateVector 2)| := abs_sub _ _
        _ ≤ _ := by linarith
    have hm := hm1 ρ hρ
    show |ρ * tclG X z ρ| ≤ _
    rw [abs_mul, abs_of_pos hρ0]
    calc ρ * |tclG X z ρ| ≤ ρ * (2 * (K1 * (ρ - a) ^ (-(5 / 2 : ℝ) - ((1 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hG hρ0.le
      _ = 2 * K1 * (ρ * (ρ - a) ^ (-(5 / 2 : ℝ) - ((1 : ℕ) : ℝ))) := by ring
      _ ≤ 2 * K1 * (c1 * ρ ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  have hpt2 : ∀ ρ : ℝ, r ≤ ρ →
      |ρ * physLap X (!₂[ρ, 0, z]) 2| ≤ 3 * K2 * c2 * ρ ^ (-(3 / 2 : ℝ)) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr0 hρ
    have hq : ϱ (!₂[ρ, 0, z] : Space) = ρ := tcb_varrho_pt hρ0.le z
    have hqa : a < ϱ (!₂[ρ, 0, z] : Space) := by rw [hq]; exact lt_of_lt_of_le hr hρ
    have b2 := hb2 τ _ hqa
    rw [hq] at b2
    have hXc := HA.cd hqa
    have hsum : |physLap X (!₂[ρ, 0, z]) 2| ≤ 3 * (K2 * (ρ - a) ^ (-(5 / 2 : ℝ) - ((2 : ℕ) : ℝ))) := by
      rw [tcl_physLap_comp, Fin.sum_univ_three]
      have t : ∀ j : Fin 3, |physPd2 X j j (!₂[ρ, 0, z]) 2| ≤
          K2 * (ρ - a) ^ (-(5 / 2 : ℝ) - ((2 : ℕ) : ℝ)) := fun j =>
        calc |physPd2 X j j (!₂[ρ, 0, z]) 2| = ‖physPd2 X j j (!₂[ρ, 0, z]) 2‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖physPd2 X j j (!₂[ρ, 0, z])‖ := PiLp.norm_apply_le _ 2
          _ ≤ ‖iteratedFDeriv ℝ 2 X (!₂[ρ, 0, z])‖ := tcl_pd2_le hXc j
          _ ≤ _ := b2
      calc _ ≤ |physPd2 X 0 0 (!₂[ρ, 0, z]) 2| + |physPd2 X 1 1 (!₂[ρ, 0, z]) 2| +
            |physPd2 X 2 2 (!₂[ρ, 0, z]) 2| := by
              refine (abs_add_le _ _).trans ?_
              gcongr
              exact abs_add_le _ _
        _ ≤ _ := by linarith [t 0, t 1, t 2]
    have hm := hm2 ρ hρ
    rw [abs_mul, abs_of_pos hρ0]
    calc ρ * |physLap X (!₂[ρ, 0, z]) 2| ≤ ρ * (3 * (K2 * (ρ - a) ^ (-(5 / 2 : ℝ) - ((2 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsum hρ0.le
      _ = 3 * K2 * (ρ * (ρ - a) ^ (-(5 / 2 : ℝ) - ((2 : ℕ) : ℝ))) := by ring
      _ ≤ 3 * K2 * (c2 * ρ ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  have hlim : Tendsto f atTop (nhds 0) := by
    have hz : Tendsto (fun ρ : ℝ => 2 * K1 * c1 * ρ ^ (-(3 / 2 : ℝ))) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul (2 * K1 * c1)
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop r] with ρ hρ
    rw [Real.norm_eq_abs]
    exact hpt1 ρ hρ
  have hint : IntegrableOn (fun ρ : ℝ => ρ * physLap X (!₂[ρ, 0, z]) 2) (Ioi r) := by
    have hB : IntegrableOn (fun ρ : ℝ => 3 * K2 * c2 * ρ ^ (-(3 / 2 : ℝ))) (Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hr0).const_mul _
    have hmeas : AEStronglyMeasurable (fun ρ : ℝ => ρ * physLap X (!₂[ρ, 0, z]) 2)
        (volume.restrict (Ioi r)) := by
      have h1 : AEStronglyMeasurable (deriv f) (volume.restrict (Ioi r)) :=
        (measurable_deriv f).aestronglyMeasurable
      refine h1.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      exact (hderiv ρ hρ).deriv
    refine Integrable.mono' hB hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    rw [Real.norm_eq_abs]
    exact hpt2 ρ (le_of_lt hρ)
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [this]
  simp [hf]

end UnforcedLeray.Short.PartIIIb.Concrete
