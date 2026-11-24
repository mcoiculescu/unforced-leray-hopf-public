import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_3.H2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_2.H3

/-!
# Helpers for `wardDYYoungL2_proved` (3): coefficient jet bounds and pointwise bound of `∂_j(tcComm)`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Product rule norm bound for `physPd (φ • F) j y`. -/
theorem w113_physPd_smul_norm_le {φ : Space → ℝ} {F : Space → Space} {y : Space}
    (hφ : DifferentiableAt ℝ φ y) (hF : DifferentiableAt ℝ F y) (j : Fin 3) :
    ‖physPd (fun x => φ x • F x) j y‖ ≤
      |φ y| * ‖physPd F j y‖ + |w112_sd1 φ j y| * ‖F y‖ := by
  have hsm := (hφ.hasFDerivAt.smul hF.hasFDerivAt).fderiv
  have happ := congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j)) hsm
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] at happ
  have heq : physPd (fun x => φ x • F x) j y =
      φ y • physPd F j y + w112_sd1 φ j y • F y := happ
  rw [heq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
  · rw [norm_smul, Real.norm_eq_abs]

/-- `R * Real.sqrt (5 * ν / 4) < r` implies `tcOut ν R r`. -/
theorem w113_tcOut_of_gt {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {r : ℝ}
    (h : R * Real.sqrt (5 * ν / 4) < r) : Sub8_1_1_2_3.tcOut ν R r := by
  left
  have hr : 0 < r := lt_of_le_of_lt (by positivity) h
  have hsq : 5 * ν / 4 * R ^ 2 < r ^ 2 := by
    have := pow_lt_pow_left₀ h (by positivity) two_ne_zero
    rw [mul_pow, Real.sq_sqrt (by positivity)] at this
    linarith
  rw [← mul_div_assoc, div_lt_iff₀ (pow_pos hr 2)]
  nlinarith [mul_pos hν (pow_pos hR 2)]

/-- `tcA1`, `tcA2`, `tcB1`, `tcB2` are `ContDiffOn ℝ 2` on `Ioi 0`. -/
theorem w113_tcCoeff_cdOn2 {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) :
    ContDiffOn ℝ 2 (tcA1 ν R χy) (Ioi 0) ∧
      ContDiffOn ℝ 2 (tcA2 ν R χy) (Ioi 0) ∧
      ContDiffOn ℝ 2 (tcB1 ν R χy) (Ioi 0) ∧
      ContDiffOn ℝ 2 (tcB2 ν R χy) (Ioi 0) := by
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  have hc0 := Sub8_1_1_2_3.tcC0_cdOn (ν := ν) (R := R) hχ
  have hc1 := Sub8_1_1_2_3.cdOn_deriv hc0
  have hc2 := Sub8_1_1_2_3.cdOn_deriv hc1
  have hf0 := Sub8_1_1_2_3.tcF0_cdOn (ν := ν) (R := R) hχ
  have hf1 := Sub8_1_1_2_3.cdOn_deriv hf0
  have hf2 := Sub8_1_1_2_3.cdOn_deriv hf1
  have dc1 : ContDiffOn ℝ 2 (deriv (tcC0 ν R χy)) (Ioi 0) :=
    hc1.of_le (WithTop.coe_le_coe.2 le_top)
  have dc2 : ContDiffOn ℝ 2 (deriv (deriv (tcC0 ν R χy))) (Ioi 0) :=
    hc2.of_le (WithTop.coe_le_coe.2 le_top)
  have df0 : ContDiffOn ℝ 2 (tcF0 ν R χy) (Ioi 0) :=
    hf0.of_le (WithTop.coe_le_coe.2 le_top)
  have df1 : ContDiffOn ℝ 2 (deriv (tcF0 ν R χy)) (Ioi 0) :=
    hf1.of_le (WithTop.coe_le_coe.2 le_top)
  have df2 : ContDiffOn ℝ 2 (deriv (deriv (tcF0 ν R χy))) (Ioi 0) :=
    hf2.of_le (WithTop.coe_le_coe.2 le_top)
  have hne : ∀ r ∈ Ioi (0 : ℝ), r ≠ 0 := fun r hr => ne_of_gt hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tcA1
    exact ((contDiffOn_const.mul contDiffOn_id).mul dc1).sub
      (contDiffOn_const.mul (dc2.add (dc1.div contDiffOn_id hne)))
  · unfold tcA2
    exact contDiffOn_const.mul dc1
  · unfold tcB1
    exact (contDiffOn_const.mul ((contDiffOn_id.mul df1).add (contDiffOn_const.mul df0))).sub
      (contDiffOn_const.mul (df2.add (df1.div contDiffOn_id hne)))
  · unfold tcB2
    exact contDiffOn_const.mul ((contDiffOn_id.mul df1).add df0)

/-- Generic 1-jet bound on `R√ν ≤ ϱ y` for `y ↦ ψ (ϱ y)` when `ψ` is `C²` on `Ioi 0` and vanishes for `r > r₂`. -/
theorem w113_radial_comp_jet1_bound {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {ψ : ℝ → ℝ}
    (hψc : ContDiffOn ℝ 2 ψ (Ioi 0))
    (hψgt : ∀ r : ℝ, R * Real.sqrt (5 * ν / 4) < r → ψ r = 0) :
    ContDiffOn ℝ 2 (fun y : Space => ψ (ϱ y)) (youngOpen ν R) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
          |ψ (ϱ y)| ≤ C ∧ ∀ j : Fin 3, |w112_sd1 (fun x => ψ (ϱ x)) j y| ≤ C) ∧
        (∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
          ψ (ϱ y) = 0 ∧ ∀ j : Fin 3, w112_sd1 (fun x => ψ (ϱ x)) j y = 0) := by
  have hϱ : ContDiffOn ℝ 2 (fun y : Space => ϱ y) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun y hy => t9_not_axis hν hR hy)
  have hmaps : MapsTo (fun y : Space => ϱ y) (youngOpen ν R) (Ioi 0) := fun y hy => by
    have hp := t9_thr_pos hν hR
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
    exact lt_trans hp hy'
  have hφc : ContDiffOn ℝ 2 (fun y : Space => ψ (ϱ y)) (youngOpen ν R) :=
    hψc.comp hϱ hmaps
  have hφz : ∀ (x : Space) (z : ℝ), ψ (ϱ (x + z • coordinateVector 2)) = ψ (ϱ x) := by
    intro x z; rw [w112_varrho_add_z]
  have hφgt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y → ψ (ϱ y) = 0 :=
    fun y hy => hψgt (ϱ y) hy
  obtain ⟨C, hC0, hbd, hgt⟩ := w112_radial_jet2_bound hν hR hφc hφz hφgt
  refine ⟨hφc, C, hC0, fun y hy => ⟨(hbd y hy).1, (hbd y hy).2.1⟩,
    fun y hy => ⟨(hgt y hy).1, (hgt y hy).2.1⟩⟩

/-- `w112_P01 y = !₂[y 0, y 1, 0]`. -/
theorem w113_P01_eq_vec (y : Space) : w112_P01 y = (!₂[y 0, y 1, 0] : Space) := by
  ext i
  fin_cases i <;> simp [w112_P01, coordinateVector]

theorem w113_radialUnit_eq_P01 (y : Space) : radialUnit y = (ϱ y)⁻¹ • w112_P01 y := by
  rw [w113_P01_eq_vec]; rfl

theorem w113_P01_add_z_inv (x : Space) (z : ℝ) :
    w112_P01 (x + z • coordinateVector 2) = w112_P01 x := by
  ext i
  fin_cases i <;> simp [w112_P01, coordinateVector]

theorem w113_radialUnit_cdOn2 {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) (k : Fin 3) :
    ContDiffOn ℝ 2 (fun y : Space => radialUnit y k) (youngOpen ν R) := by
  have hne : ∀ y ∈ youngOpen ν R, ϱ y ≠ 0 := fun y hy => by
    have hp := t9_thr_pos hν hR
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
    linarith
  have hϱ : ContDiffOn ℝ 2 (fun y : Space => ϱ y) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun y hy => t9_not_axis hν hR hy)
  have hP01 : ContDiff ℝ 2 (fun y : Space => w112_P01 y k) := by
    unfold w112_P01
    have h0 : ContDiff ℝ 2 (fun y : Space => y) := contDiff_id
    have h2 : ContDiff ℝ 2 (fun y : Space => y 2) :=
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff
    have hvec : ContDiff ℝ 2 (fun y : Space => y + (-y 2) • (coordinateVector 2 : Space)) :=
      h0.add (h2.neg.smul contDiff_const)
    exact (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hvec
  have hfun : (fun y : Space => radialUnit y k) = fun y => w112_P01 y k / ϱ y := by
    funext y
    rw [w113_radialUnit_eq_P01, PiLp.smul_apply, smul_eq_mul, inv_mul_eq_div]
  rw [hfun]
  exact hP01.contDiffOn.div hϱ hne

/-- 1-jet bound on `R√ν ≤ ϱ y` for `y ↦ tcA2 ν R χy (ϱ y) * radialUnit y k`. -/
theorem w113_tcA2_rad_jet1_bound {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (k : Fin 3) :
    ContDiffOn ℝ 2 (fun y : Space => tcA2 ν R χy (ϱ y) * radialUnit y k) (youngOpen ν R) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
          |tcA2 ν R χy (ϱ y) * radialUnit y k| ≤ C ∧
            ∀ j : Fin 3, |w112_sd1 (fun x => tcA2 ν R χy (ϱ x) * radialUnit x k) j y| ≤ C := by
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨_, hA2c, _, _⟩ := w113_tcCoeff_cdOn2 (ν := ν) (R := R) hχy
  have hA2gt : ∀ r : ℝ, R * Real.sqrt (5 * ν / 4) < r → tcA2 ν R χy r = 0 := by
    intro r hr
    have hr0 : r ≠ 0 := (lt_of_le_of_lt (by positivity) hr).ne'
    exact (Sub8_1_1_2_3.tc_coeff_zero hχ hr0 (w113_tcOut_of_gt hν hR hr)).2.1
  obtain ⟨hA2_cd, _⟩ := w113_radial_comp_jet1_bound hν hR hA2c hA2gt
  have hrad_cd := w113_radialUnit_cdOn2 hν hR k
  have hφc : ContDiffOn ℝ 2 (fun y : Space => tcA2 ν R χy (ϱ y) * radialUnit y k) (youngOpen ν R) :=
    hA2_cd.mul hrad_cd
  have hφz : ∀ (x : Space) (z : ℝ),
      tcA2 ν R χy (ϱ (x + z • coordinateVector 2)) * radialUnit (x + z • coordinateVector 2) k =
        tcA2 ν R χy (ϱ x) * radialUnit x k := by
    intro x z
    simp only [w113_radialUnit_eq_P01, PiLp.smul_apply, smul_eq_mul,
      w112_varrho_add_z, w113_P01_add_z_inv]
  have hφgt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
      tcA2 ν R χy (ϱ y) * radialUnit y k = 0 := by
    intro y hy
    rw [hA2gt (ϱ y) hy, zero_mul]
  obtain ⟨C, hC0, hbd, _⟩ := w112_radial_jet2_bound hν hR hφc hφz hφgt
  exact ⟨hφc, C, hC0, fun y hy => ⟨(hbd y hy).1, (hbd y hy).2.1⟩⟩

/-- Combined 1-jet bounds for all radial coefficients of `tcComm`. -/
theorem w113_tcCoeff_all_bounds {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
        |tcA1 ν R χy (ϱ y)| ≤ C ∧
        (∀ j : Fin 3, |w112_sd1 (fun x => tcA1 ν R χy (ϱ x)) j y| ≤ C) ∧
        (∀ k : Fin 3, |tcA2 ν R χy (ϱ y) * radialUnit y k| ≤ C) ∧
        (∀ k j : Fin 3, |w112_sd1 (fun x => tcA2 ν R χy (ϱ x) * radialUnit x k) j y| ≤ C) ∧
        |tcB1 ν R χy (ϱ y)| ≤ C ∧
        (∀ j : Fin 3, |w112_sd1 (fun x => tcB1 ν R χy (ϱ x)) j y| ≤ C) ∧
        |tcB2 ν R χy (ϱ y)| ≤ C ∧
        (∀ j : Fin 3, |w112_sd1 (fun x => tcB2 ν R χy (ϱ x)) j y| ≤ C)) ∧
      (∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
        tcB1 ν R χy (ϱ y) = 0 ∧
        ∀ j : Fin 3, w112_sd1 (fun x => tcB1 ν R χy (ϱ x)) j y = 0) := by
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hA1c, _, hB1c, hB2c⟩ := w113_tcCoeff_cdOn2 (ν := ν) (R := R) hχy
  have hgt_all : ∀ r : ℝ, R * Real.sqrt (5 * ν / 4) < r →
      tcA1 ν R χy r = 0 ∧ tcA2 ν R χy r = 0 ∧ tcB1 ν R χy r = 0 ∧ tcB2 ν R χy r = 0 := by
    intro r hr
    have hr0 : r ≠ 0 := (lt_of_le_of_lt (by positivity) hr).ne'
    exact Sub8_1_1_2_3.tc_coeff_zero hχ hr0 (w113_tcOut_of_gt hν hR hr)
  obtain ⟨_, CA1, hCA1, bA1, _⟩ :=
    w113_radial_comp_jet1_bound hν hR hA1c (fun r hr => (hgt_all r hr).1)
  obtain ⟨_, CB1, hCB1, bB1, gB1⟩ :=
    w113_radial_comp_jet1_bound hν hR hB1c (fun r hr => (hgt_all r hr).2.2.1)
  obtain ⟨_, CB2, hCB2, bB2, _⟩ :=
    w113_radial_comp_jet1_bound hν hR hB2c (fun r hr => (hgt_all r hr).2.2.2)
  obtain ⟨_, CA20, hCA20, bA20⟩ := w113_tcA2_rad_jet1_bound hχy hν hR 0
  obtain ⟨_, CA21, hCA21, bA21⟩ := w113_tcA2_rad_jet1_bound hχy hν hR 1
  obtain ⟨_, CA22, hCA22, bA22⟩ := w113_tcA2_rad_jet1_bound hχy hν hR 2
  set C := CA1 + CB1 + CB2 + CA20 + CA21 + CA22
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun y hy => ?_, gB1⟩
  obtain ⟨hA1_0, hA1_1⟩ := bA1 y hy
  obtain ⟨hB1_0, hB1_1⟩ := bB1 y hy
  obtain ⟨hB2_0, hB2_1⟩ := bB2 y hy
  obtain ⟨h20_0, h20_1⟩ := bA20 y hy
  obtain ⟨h21_0, h21_1⟩ := bA21 y hy
  obtain ⟨h22_0, h22_1⟩ := bA22 y hy
  refine ⟨by linarith, fun j => by linarith [hA1_1 j],
    fun k => by fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith,
    fun k j => by
      fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        linarith [h20_1 j, h21_1 j, h22_1 j],
    by linarith, fun j => by linarith [hB1_1 j],
    by linarith, fun j => by linarith [hB2_1 j]⟩

end UnforcedLeray.Short.PartIIIb.Concrete
end
