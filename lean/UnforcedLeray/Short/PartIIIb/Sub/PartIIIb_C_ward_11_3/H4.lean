import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_3.H3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff.Cut3

/-!
# Helpers for `wardDYYoungL2_proved` (4): `∂_j(tcComm)`, `∂_j(transField)`, and `∂_jY` measurability
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w113_radialUnit_eq_coord (x : Space) :
    radialUnit x =
      (radialUnit x 0) • (coordinateVector 0 : Space) +
        (radialUnit x 1) • (coordinateVector 1 : Space) := by
  ext i
  fin_cases i <;> simp [radialUnit, coordinateVector]

theorem w113_tcComm_eq_sum5 (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (x : Space) :
    tcComm ν R χy Z τ x =
      tcA1 ν R χy (ϱ x) • Z τ x +
      ((tcA2 ν R χy (ϱ x) * radialUnit x 0) • physPd (Z τ) 0 x +
        (tcA2 ν R χy (ϱ x) * radialUnit x 1) • physPd (Z τ) 1 x) +
      (tcB1 ν R χy (ϱ x) • (outPrim Z τ (ϱ x) (x 2) • coordinateVector 2) +
        tcB2 ν R χy (ϱ x) • (Z τ x 2 • coordinateVector 2)) := by
  unfold tcComm
  have hrad : (fderiv ℝ (Z τ) x) (radialUnit x) =
      (radialUnit x 0) • physPd (Z τ) 0 x + (radialUnit x 1) • physPd (Z τ) 1 x := by
    conv_lhs => rw [w113_radialUnit_eq_coord x]
    rw [map_add, map_smul, map_smul]
    rfl
  rw [hrad, smul_add, smul_smul, smul_smul, add_smul,
    mul_smul (tcB1 ν R χy (ϱ x)), mul_smul (tcB2 ν R χy (ϱ x))]

theorem w113_physPd_add_norm_le {F₁ F₂ : Space → Space} {y : Space}
    (h1 : DifferentiableAt ℝ F₁ y) (h2 : DifferentiableAt ℝ F₂ y) (j : Fin 3) :
    ‖physPd (fun x => F₁ x + F₂ x) j y‖ ≤ ‖physPd F₁ j y‖ + ‖physPd F₂ j y‖ := by
  have heq : physPd (fun x => F₁ x + F₂ x) j y = physPd F₁ j y + physPd F₂ j y := by
    unfold physPd
    rw [fderiv_fun_add h1 h2, add_apply]
  rw [heq]
  exact norm_add_le _ _

/-- Pointwise bound on `‖physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y‖` for `R√ν ≤ ϱ y`. -/
theorem w113_tcComm_pd_pt_bound {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
      |tcA1 ν R χy (ϱ y)| ≤ C ∧
      (∀ j : Fin 3, |w112_sd1 (fun x => tcA1 ν R χy (ϱ x)) j y| ≤ C) ∧
      (∀ k : Fin 3, |tcA2 ν R χy (ϱ y) * radialUnit y k| ≤ C) ∧
      (∀ k j : Fin 3, |w112_sd1 (fun x => tcA2 ν R χy (ϱ x) * radialUnit x k) j y| ≤ C) ∧
      |tcB1 ν R χy (ϱ y)| ≤ C ∧
      (∀ j : Fin 3, |w112_sd1 (fun x => tcB1 ν R χy (ϱ x)) j y| ≤ C) ∧
      |tcB2 ν R χy (ϱ y)| ≤ C ∧
      (∀ j : Fin 3, |w112_sd1 (fun x => tcB2 ν R χy (ϱ x)) j y| ≤ C))
    (hgt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
      tcB1 ν R χy (ϱ y) = 0 ∧
      ∀ j : Fin 3, w112_sd1 (fun x => tcB1 ν R χy (ϱ x)) j y = 0)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (j : Fin 3)
    {y : Space} (hy : R * Real.sqrt ν ≤ ϱ y) :
    ‖physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y‖ ≤
      C * ‖physPd2 (wardX0 ν μ R c g τ) j 0 y‖ +
      C * ‖physPd2 (wardX0 ν μ R c g τ) j 1 y‖ +
      (2 * C) * ‖physPd (wardX0 ν μ R c g τ) j y‖ +
      C * ‖physPd (wardX0 ν μ R c g τ) 0 y‖ +
      C * ‖physPd (wardX0 ν μ R c g τ) 1 y‖ +
      (2 * C + 2 * C * (R * Real.sqrt (5 * ν / 4))) * ‖wardX0 ν μ R c g τ y‖ +
      C * w2N ν μ R c (R * Real.sqrt (5 * ν / 4)) g τ y := by
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  set Z : Space → Space := wardX0 ν μ R c g τ
  set Ψ : Space → ℝ := fun x => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)
  set G3 : Space → Space := fun x => Ψ x • (coordinateVector 2 : Space)
  set G4 : Space → Space := fun x => Z x 2 • (coordinateVector 2 : Space)
  set φ1 : Space → ℝ := fun x => tcA1 ν R χy (ϱ x)
  set φ20 : Space → ℝ := fun x => tcA2 ν R χy (ϱ x) * radialUnit x 0
  set φ21 : Space → ℝ := fun x => tcA2 ν R χy (ϱ x) * radialUnit x 1
  set φ3 : Space → ℝ := fun x => tcB1 ν R χy (ϱ x)
  set φ4 : Space → ℝ := fun x => tcB2 ν R χy (ϱ x)
  obtain ⟨hA1c, _, hB1c, hB2c⟩ := w113_tcCoeff_cdOn2 (ν := ν) (R := R) hχy
  have hϱ2 : ContDiffOn ℝ 2 (fun w : Space => ϱ w) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun w hw => t9_not_axis hν hR hw)
  have hmaps : MapsTo (fun w : Space => ϱ w) (youngOpen ν R) (Ioi 0) := fun w hw => by
    have hp := t9_thr_pos hν hR
    have hw' : R * Real.sqrt (5 * ν / 6) < ϱ w := hw
    exact lt_trans hp hw'
  have hφ1d : DifferentiableAt ℝ φ1 y :=
    ((hA1c.comp hϱ2 hmaps).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hφ3d : DifferentiableAt ℝ φ3 y :=
    ((hB1c.comp hϱ2 hmaps).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hφ4d : DifferentiableAt ℝ φ4 y :=
    ((hB2c.comp hϱ2 hmaps).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hφ20d : DifferentiableAt ℝ φ20 y :=
    (((w113_tcA2_rad_jet1_bound hχy hν hR 0).1).contDiffAt
      (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hφ21d : DifferentiableAt ℝ φ21 y :=
    (((w113_tcA2_rad_jet1_bound hχy hν hR 1).1).contDiffAt
      (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hZc3 : ContDiffOn ℝ 3 Z (youngOpen ν R) :=
    (w2_smooth hν hR hc hμ hg τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hZc2 : ContDiffOn ℝ 2 Z (youngOpen ν R) := hZc3.of_le (by norm_num)
  have hZd : DifferentiableAt ℝ Z y :=
    (hZc2.contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hZc2' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) Z (youngOpen ν R) := hZc2
  have hfZ : ContDiffOn ℝ 1 (fderiv ℝ Z) (youngOpen ν R) :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hZc2').2.2
  have hZpd_d : ∀ k : Fin 3, DifferentiableAt ℝ (physPd Z k) y := fun k =>
    (((ContinuousLinearMap.apply ℝ Space (coordinateVector k)).contDiff.comp_contDiffOn
      hfZ).contDiffAt (hUo.mem_nhds hyU)).differentiableAt one_ne_zero
  have hΨc2 : ContDiffOn ℝ 2 Ψ (youngOpen ν R) :=
    (xc_outPrim_c3 hν hR hZc3 (w2_hdr hν hR hc hμ hg τ)).of_le (by norm_num)
  have hG3d : DifferentiableAt ℝ G3 y :=
    ((hΨc2.smul contDiffOn_const).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hZ2c2 : ContDiffOn ℝ 2 (fun x : Space => Z x 2) (youngOpen ν R) :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hZc2
  have hG4d : DifferentiableAt ℝ G4 y :=
    ((hZ2c2.smul contDiffOn_const).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have h1d : DifferentiableAt ℝ (fun x => φ1 x • Z x) y := hφ1d.smul hZd
  have h20d : DifferentiableAt ℝ (fun x => φ20 x • physPd Z 0 x) y := hφ20d.smul (hZpd_d 0)
  have h21d : DifferentiableAt ℝ (fun x => φ21 x • physPd Z 1 x) y := hφ21d.smul (hZpd_d 1)
  have h3d : DifferentiableAt ℝ (fun x => φ3 x • G3 x) y := hφ3d.smul hG3d
  have h4d : DifferentiableAt ℝ (fun x => φ4 x • G4 x) y := hφ4d.smul hG4d
  have hfun : tcComm ν R χy (wardX0 ν μ R c g) τ =
      fun x => (φ1 x • Z x + (φ20 x • physPd Z 0 x + φ21 x • physPd Z 1 x)) +
        (φ3 x • G3 x + φ4 x • G4 x) := by
    funext x
    exact w113_tcComm_eq_sum5 ν R χy (wardX0 ν μ R c g) τ x
  rw [hfun]
  have hadd1 := w113_physPd_add_norm_le (h1d.fun_add (h20d.fun_add h21d)) (h3d.fun_add h4d) j
  have hadd2 := w113_physPd_add_norm_le h1d (h20d.fun_add h21d) j
  have hadd3 := w113_physPd_add_norm_le h20d h21d j
  have hadd4 := w113_physPd_add_norm_le h3d h4d j
  have hs1 := w113_physPd_smul_norm_le hφ1d hZd j
  have hs20 := w113_physPd_smul_norm_le hφ20d (hZpd_d 0) j
  have hs21 := w113_physPd_smul_norm_le hφ21d (hZpd_d 1) j
  have hs3 := w113_physPd_smul_norm_le hφ3d hG3d j
  have hs4 := w113_physPd_smul_norm_le hφ4d hG4d j
  obtain ⟨cA1_0, cA1_1, cA2_0, cA2_1, cB1_0, cB1_1, cB2_0, cB2_1⟩ := hbd y hy
  have b1 : ‖physPd (fun x => φ1 x • Z x) j y‖ ≤ C * ‖physPd Z j y‖ + C * ‖Z y‖ :=
    hs1.trans (add_le_add
      (mul_le_mul_of_nonneg_right cA1_0 (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (cA1_1 j) (norm_nonneg _)))
  have b20 : ‖physPd (fun x => φ20 x • physPd Z 0 x) j y‖ ≤
      C * ‖physPd2 Z j 0 y‖ + C * ‖physPd Z 0 y‖ :=
    hs20.trans (add_le_add
      (mul_le_mul_of_nonneg_right (cA2_0 0) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (cA2_1 0 j) (norm_nonneg _)))
  have b21 : ‖physPd (fun x => φ21 x • physPd Z 1 x) j y‖ ≤
      C * ‖physPd2 Z j 1 y‖ + C * ‖physPd Z 1 y‖ :=
    hs21.trans (add_le_add
      (mul_le_mul_of_nonneg_right (cA2_0 1) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (cA2_1 1 j) (norm_nonneg _)))
  obtain ⟨hG3_0, hG3_1, _⟩ := w112_smul_e2_jets hUo hΨc2 hyU
  rw [hG3_0, hG3_1 j] at hs3
  have b3 : ‖physPd (fun x => φ3 x • G3 x) j y‖ ≤
      (2 * C * r2) * ‖Z y‖ + C * w2N ν μ R c r2 g τ y := by
    refine hs3.trans ?_
    by_cases hle : ϱ y ≤ r2
    · obtain ⟨_, hψ1, _⟩ := w112_psi_jet hν hR hc hμ hg τ hyU
      have hN : w2N ν μ R c r2 g τ y = |Ψ y| := by
        unfold w2N Ψ; simp only [hle, ↓reduceIte]
      rw [hN]
      have hp1 : |w112_sd1 Ψ j y| ≤ 2 * r2 * ‖Z y‖ :=
        (hψ1 j).2.trans (by nlinarith [norm_nonneg (Z y)])
      have m1 : |φ3 y| * |w112_sd1 Ψ j y| ≤ C * (2 * r2 * ‖Z y‖) :=
        mul_le_mul cB1_0 hp1 (abs_nonneg _) hC
      have m2 : |w112_sd1 φ3 j y| * |Ψ y| ≤ C * |Ψ y| :=
        mul_le_mul_of_nonneg_right (cB1_1 j) (abs_nonneg _)
      linarith
    · obtain ⟨hz0, hz1⟩ := hgt y (not_le.1 hle)
      change |tcB1 ν R χy (ϱ y)| * _ + |w112_sd1 (fun x => tcB1 ν R χy (ϱ x)) j y| * _ ≤ _
      rw [hz0, hz1 j]
      simp only [abs_zero, zero_mul, add_zero]
      have hr2nn : 0 ≤ r2 := by positivity
      have hZ0 := norm_nonneg (Z y)
      have hN0 := w2N_nonneg ν μ R c r2 g τ y
      positivity
  obtain ⟨hG4_0, hG4_1, _⟩ := w112_smul_e2_jets hUo hZ2c2 hyU
  rw [hG4_0, hG4_1 j] at hs4
  have hsd_Z2 : w112_sd1 (fun x : Space => Z x 2) j y = physPd Z j y 2 := by
    unfold w112_sd1 physPd
    have hd : HasFDerivAt (fun x : Space => (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) (Z x))
        ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp (fderiv ℝ Z y)) y :=
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp y hZd.hasFDerivAt
    exact congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector j)) hd.fderiv
  have b4 : ‖physPd (fun x => φ4 x • G4 x) j y‖ ≤ C * ‖physPd Z j y‖ + C * ‖Z y‖ := by
    refine hs4.trans ?_
    rw [hsd_Z2]
    have m1 : |φ4 y| * |physPd Z j y 2| ≤ C * ‖physPd Z j y‖ :=
      mul_le_mul cB2_0 (wyl_abs_apply_le _ 2) (abs_nonneg _) hC
    have m2 : |w112_sd1 φ4 j y| * |Z y 2| ≤ C * ‖Z y‖ :=
      mul_le_mul (cB2_1 j) (wyl_abs_apply_le _ 2) (abs_nonneg _) hC
    linarith
  linarith

/-! ## Measurable truncation of `tcComm` on `youngOpen ν R` -/

open scoped Classical in
/-- Truncation of `tcComm` replacing `physPd (Z τ)` with its indicator on `youngOpen ν R`. -/
def w113_tcCommU (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (x : Space) : Space :=
  tcA1 ν R χy (ϱ x) • Z τ x +
    ((tcA2 ν R χy (ϱ x) * radialUnit x 0) •
        (if x ∈ youngOpen ν R then physPd (Z τ) 0 x else 0) +
      (tcA2 ν R χy (ϱ x) * radialUnit x 1) •
        (if x ∈ youngOpen ν R then physPd (Z τ) 1 x else 0)) +
    (tcB1 ν R χy (ϱ x) • (outPrim Z τ (ϱ x) (x 2) • coordinateVector 2) +
      tcB2 ν R χy (ϱ x) • (Z τ x 2 • coordinateVector 2))

open scoped Classical in
theorem w113_tcCommU_eq_of_mem {ν R : ℝ} {χy : ℝ → ℝ} (Z : ℝ → Space → Space) (τ : ℝ)
    {x : Space} (hx : x ∈ youngOpen ν R) :
    w113_tcCommU ν R χy Z τ x = tcComm ν R χy Z τ x := by
  unfold w113_tcCommU
  simp only [hx, ↓reduceIte]
  exact (w113_tcComm_eq_sum5 ν R χy Z τ x).symm

theorem w113_tcCoeff_measurable (ν R : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy) :
    Measurable (tcA1 ν R χy) ∧ Measurable (tcA2 ν R χy) ∧
      Measurable (tcB1 ν R χy) ∧ Measurable (tcB2 ν R χy) := by
  have hc0 : Measurable (tcC0 ν R χy) := by
    unfold tcC0
    exact hχy.smooth.continuous.measurable.comp
      (measurable_const.mul (measurable_const.div (measurable_id.pow_const 2)))
  have hc1 : Measurable (deriv (tcC0 ν R χy)) := measurable_deriv _
  have hc2 : Measurable (deriv (deriv (tcC0 ν R χy))) := measurable_deriv _
  have hf0 : Measurable (tcF0 ν R χy) := w2a_measurable ν R χy
  have hf1 : Measurable (deriv (tcF0 ν R χy)) := measurable_deriv _
  have hf2 : Measurable (deriv (deriv (tcF0 ν R χy))) := measurable_deriv _
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tcA1
    exact ((measurable_const.mul measurable_id).mul hc1).sub
      (measurable_const.mul (hc2.add (hc1.div measurable_id)))
  · unfold tcA2
    exact measurable_const.mul hc1
  · unfold tcB1
    exact (measurable_const.mul ((measurable_id.mul hf1).add (measurable_const.mul hf0))).sub
      (measurable_const.mul (hf2.add (hf1.div measurable_id)))
  · unfold tcB2
    exact measurable_const.mul ((measurable_id.mul hf1).add hf0)

theorem w113_radialUnit_measurable (k : Fin 3) : Measurable (fun x : Space => radialUnit x k) := by
  have hfun : (fun x : Space => radialUnit x k) = fun x => (ϱ x)⁻¹ * w112_P01 x k := by
    funext x
    rw [w113_radialUnit_eq_P01, PiLp.smul_apply, smul_eq_mul]
  rw [hfun]
  have hP01 : Continuous (fun x : Space => w112_P01 x k) := by
    unfold w112_P01
    fun_prop
  exact continuous_ϱ.measurable.inv.mul hP01.measurable

theorem w113_tcCommU_measurable {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) :
    Measurable (fun x : ℝ × Space =>
      w113_tcCommU ν R χy (wardX0 ν μ R c g) x.1 x.2) := by
  classical
  obtain ⟨mA1, mA2, mB1, mB2⟩ := w113_tcCoeff_measurable ν R χy hχy
  have hϱm : Measurable (fun x : ℝ × Space => ϱ x.2) :=
    continuous_ϱ.measurable.comp measurable_snd
  have hZm := wardX0_measurable_of_measurable ν μ R c g hg.measurable
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hX0 := w10_X0_eq (μ := μ) hν hR hc hg
  have hdZ : ∀ τ y, y ∈ youngOpen ν R → DifferentiableAt ℝ (wardX0 ν μ R c g τ) y := by
    intro τ y hy
    rw [hX0]
    have e : sepX0 ν μ T τ = fun z => sepWre ν μ T τ z - sepWre ν (μ + 1) T τ z := by
      funext z; exact sepX0_eq_sub ν μ T τ z
    rw [e]
    exact (w10_diffV hν hμ hr0 hP hS hM τ hy).sub
      (w10_diffV hν (by linarith) hr0 hP hS hM τ hy)
  have hPd0 := w10_meas_pd hZm hUo.measurableSet hdZ 0
  have hPd1 := w10_meas_pd hZm hUo.measurableSet hdZ 1
  have hO := outPrim_measurable hZm
  have hq : Measurable (fun x : ℝ × Space => ((x.1, ϱ x.2, x.2 2) : ℝ × ℝ × ℝ)) :=
    measurable_fst.prodMk (hϱm.prodMk
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd))
  have hZ2 : Measurable (fun x : ℝ × Space => wardX0 ν μ R c g x.1 x.2 2) :=
    (EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp hZm
  have hm1 : Measurable (fun x : ℝ × Space =>
      tcA1 ν R χy (ϱ x.2) • wardX0 ν μ R c g x.1 x.2) :=
    (mA1.comp hϱm).smul hZm
  have hm20 : Measurable (fun x : ℝ × Space =>
      (tcA2 ν R χy (ϱ x.2) * radialUnit x.2 0) •
        (if x.2 ∈ youngOpen ν R then physPd (wardX0 ν μ R c g x.1) 0 x.2 else 0)) :=
    ((mA2.comp hϱm).mul ((w113_radialUnit_measurable 0).comp measurable_snd)).smul hPd0
  have hm21 : Measurable (fun x : ℝ × Space =>
      (tcA2 ν R χy (ϱ x.2) * radialUnit x.2 1) •
        (if x.2 ∈ youngOpen ν R then physPd (wardX0 ν μ R c g x.1) 1 x.2 else 0)) :=
    ((mA2.comp hϱm).mul ((w113_radialUnit_measurable 1).comp measurable_snd)).smul hPd1
  have hm3 : Measurable (fun x : ℝ × Space =>
      tcB1 ν R χy (ϱ x.2) •
        (outPrim (wardX0 ν μ R c g) x.1 (ϱ x.2) (x.2 2) • (coordinateVector 2 : Space))) :=
    (mB1.comp hϱm).smul ((hO.comp hq).smul measurable_const)
  have hm4 : Measurable (fun x : ℝ × Space =>
      tcB2 ν R χy (ϱ x.2) • (wardX0 ν μ R c g x.1 x.2 2 • (coordinateVector 2 : Space))) :=
    (mB2.comp hϱm).smul (hZ2.smul measurable_const)
  exact (hm1.add (hm20.add hm21)).add (hm3.add hm4)

/-- **`∂_j(tcComm)` on the young support**. -/
theorem w113_tcComm_pd_youngL2 (ν μ R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) :
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
      YoungL2Le c ν R C
        (fun τ => physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j) g := by
  classical
  obtain ⟨CX0, hX0⟩ := wardX0YoungL2_proved ν μ R c hν hR hc hμ
  obtain ⟨CD2, hD2⟩ := wardD2X0YoungL2_proved ν μ R c hν hR hc hμ
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2nn : 0 ≤ r2 := by positivity
  obtain ⟨K, hK, hΨ⟩ := w2_psiBd hν hR hc hμ r2
  obtain ⟨C, hC, hbd, hgt⟩ := w113_tcCoeff_all_bounds hχy hν hR
  set CX0' : ℝ := max CX0 0
  set CD2' : ℝ := max CD2 0
  have hCX0' : 0 ≤ CX0' := le_max_right _ _
  have hCD2' : 0 ≤ CD2' := le_max_right _ _
  set a1 : ℝ := C
  set a2 : ℝ := C
  set a3 : ℝ := 2 * C
  set a4 : ℝ := C
  set a5 : ℝ := C
  set a6 : ℝ := 2 * C + 2 * C * r2
  set a7 : ℝ := C
  have ha1 : 0 ≤ a1 := hC
  have ha2 : 0 ≤ a2 := hC
  have ha3 : 0 ≤ a3 := by positivity
  have ha4 : 0 ≤ a4 := hC
  have ha5 : 0 ≤ a5 := hC
  have ha6 : 0 ≤ a6 := by positivity
  have ha7 : 0 ≤ a7 := hC
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  refine ⟨a1 * CD2' + a2 * CD2' + a3 * CX0' + a4 * CX0' + a5 * CX0' + a6 * CX0' + a7 * K,
    fun g hg j => ?_⟩
  obtain ⟨hX0_val, hX0_pd⟩ := hX0 g hg
  have b1 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a1 * wardYoungRead ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j 0) q)
      (a1 * CD2') := by
    simpa [abs_of_nonneg ha1] using (wyl_bd_of_young (hD2 g hg j 0)).const_mul a1
  have b2 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a2 * wardYoungRead ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j 1) q)
      (a2 * CD2') := by
    simpa [abs_of_nonneg ha2] using (wyl_bd_of_young (hD2 g hg j 1)).const_mul a2
  have b3 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a3 * wardYoungRead ν R (fun τ => physPd (wardX0 ν μ R c g τ) j) q)
      (a3 * CX0') := by
    simpa [abs_of_nonneg ha3] using (wyl_bd_of_young (hX0_pd j)).const_mul a3
  have b4 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a4 * wardYoungRead ν R (fun τ => physPd (wardX0 ν μ R c g τ) 0) q)
      (a4 * CX0') := by
    simpa [abs_of_nonneg ha4] using (wyl_bd_of_young (hX0_pd 0)).const_mul a4
  have b5 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a5 * wardYoungRead ν R (fun τ => physPd (wardX0 ν μ R c g τ) 1) q)
      (a5 * CX0') := by
    simpa [abs_of_nonneg ha5] using (wyl_bd_of_young (hX0_pd 1)).const_mul a5
  have b6 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a6 * wardYoungRead ν R (wardX0 ν μ R c g) q)
      (a6 * CX0') := by
    simpa [abs_of_nonneg ha6] using (wyl_bd_of_young hX0_val).const_mul a6
  have b7 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a7 * wardYoungRead ν R (w2Phi ν μ R c r2 g) q)
      (a7 * K) := by
    simpa [abs_of_nonneg ha7] using (hΨ g hg).const_mul a7
  have hc1 : 0 ≤ a1 * CD2' := mul_nonneg ha1 hCD2'
  have hc2 : 0 ≤ a2 * CD2' := mul_nonneg ha2 hCD2'
  have hc3 : 0 ≤ a3 * CX0' := mul_nonneg ha3 hCX0'
  have hc4 : 0 ≤ a4 * CX0' := mul_nonneg ha4 hCX0'
  have hc5 : 0 ≤ a5 * CX0' := mul_nonneg ha5 hCX0'
  have hc6 : 0 ≤ a6 * CX0' := mul_nonneg ha6 hCX0'
  have hc7 : 0 ≤ a7 * K := mul_nonneg ha7 hK
  have b12 := b1.add b2 hc1 hc2
  have b123 := b12.add b3 (by positivity) hc3
  have b1234 := b123.add b4 (by positivity) hc4
  have b12345 := b1234.add b5 (by positivity) hc5
  have b123456 := b12345.add b6 (by positivity) hc6
  have b1234567 := b123456.add b7 (by positivity) hc7
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  have hX0_eq := w10_X0_eq (μ := μ) hν hR hc hg
  have hd_tc : ∀ τ y, y ∈ youngOpen ν R →
      DifferentiableAt ℝ (w113_tcCommU ν R χy (wardX0 ν μ R c g) τ) y := by
    intro τ y hy
    have hev : w113_tcCommU ν R χy (wardX0 ν μ R c g) τ =ᶠ[𝓝 y]
        tcComm ν R χy (wardX0 ν μ R c g) τ :=
      Filter.mem_of_superset (hUo.mem_nhds hy) fun z hz =>
        w113_tcCommU_eq_of_mem (wardX0 ν μ R c g) τ hz
    have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hy
    have hd : DifferentiableAt ℝ (tcComm ν R χy (wardX0 ν μ R c g) τ) y := by
      rw [hX0_eq]
      exact w113_tcComm_diffAt hχ hν hR hμ hP hS hM hAx τ hy0
    exact hd.congr_of_eventuallyEq hev
  have hPdm := w10_meas_pd (w113_tcCommU_measurable hχy hν hR hc hμ hg) hUo.measurableSet hd_tc j
  have hread : wardYoungRead ν R (fun τ => physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j) =
      wardYoungRead ν R (fun τ y =>
        if y ∈ youngOpen ν R then
          physPd (w113_tcCommU ν R χy (wardX0 ν μ R c g) τ) j y
        else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
    have hev : w113_tcCommU ν R χy (wardX0 ν μ R c g) τ =ᶠ[𝓝 y]
        tcComm ν R χy (wardX0 ν μ R c g) τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) fun z hz =>
        w113_tcCommU_eq_of_mem (wardX0 ν μ R c g) τ hz
    simp only [hyU, ↓reduceIte, physPd, hev.fderiv_eq]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R (fun τ => physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas hPdm).aestronglyMeasurable
  refine ⟨hFm, (eLpNorm_mono_real (fun q => ?_)).trans b1234567.2⟩
  rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ q)]
  by_cases hq : ν * q.1 ≤ 1
  · rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos _ hs]
      have r1 := wyl_youngRead_nonneg ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j 0) q
      have r2' := wyl_youngRead_nonneg ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j 1) q
      have r3 := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) j) q
      have r4 := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) 0) q
      have r5 := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) 1) q
      have r6 := wyl_youngRead_nonneg ν R (wardX0 ν μ R c g) q
      have r7 := wyl_youngRead_nonneg ν R (w2Phi ν μ R c r2 g) q
      positivity
    · rw [wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq, w2Phi_norm]
      set τ := NearInst.chartTau R q
      set y := NearInst.chartY R q
      have hy : R * Real.sqrt ν ≤ ϱ y := wyl_young_ϱ hν hR hs hq
      have hpt := w113_tcComm_pd_pt_bound hχy hν hR hc hμ hC hbd hgt hg τ j hy
      have hinv : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hpt hinv
      linarith
  · have hqS : q ∉ wardYoungSet ν := hq
    have h0 : wardYoungRead ν R
        (fun τ => physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j) q = 0 := by
      unfold wardYoungRead
      rw [indicator_of_notMem hqS]
    rw [h0]
    have r1 := wyl_youngRead_nonneg ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j 0) q
    have r2' := wyl_youngRead_nonneg ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j 1) q
    have r3 := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) j) q
    have r4 := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) 0) q
    have r5 := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) 1) q
    have r6 := wyl_youngRead_nonneg ν R (wardX0 ν μ R c g) q
    have r7 := wyl_youngRead_nonneg ν R (w2Phi ν μ R c r2 g) q
    positivity

/-- **`∂_j transField` on the young support**. -/
theorem w113_wardDYTransYoungL2 (ν μ R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) :
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
      YoungL2Le c ν R C (fun τ => physPd (transField ν μ R c χy g τ) j) g := by
  classical
  obtain ⟨C1, hC1⟩ := w113_streamCorrW_pd_youngL2 ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C2, hC2⟩ := w113_tcComm_pd_youngL2 ν μ R c χy hχy hν hR hc hμ
  refine ⟨max C1 0 + max C2 0, fun g hg j => ?_⟩
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hX0_eq := w10_X0_eq (μ := μ) hν hR hc hg
  set U : Set Space := youngOpen ν R
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  set F_U : ℝ → Space → Space := fun τ z =>
    streamCorr ν R χy (sepWre ν μ T) τ z + w113_tcCommU ν R χy (wardX0 ν μ R c g) τ z
  have hFU_meas : Measurable (fun x : ℝ × Space => F_U x.1 x.2) :=
    (w113_streamCorrW_measurable (χy := χy) (μ := μ) hν hg).add
      (w113_tcCommU_measurable hχy hν hR hc hμ hg)
  have hFU_eq : ∀ τ z, z ∈ U → F_U τ z = transField ν μ R c χy g τ z := by
    intro τ z hz
    have hz0 : 0 < ϱ z := lt_of_le_of_lt hr0 hz
    unfold F_U
    rw [w113_tcCommU_eq_of_mem (wardX0 ν μ R c g) τ hz, hX0_eq,
      ← w113_sepComm_eq_tcComm hχ hν hR hμ hP hS hM hAx τ hz0,
      ← w113_transField_eq hν hR hc hg τ z]
  have hd_FU : ∀ τ y, y ∈ U → DifferentiableAt ℝ (F_U τ) y := by
    intro τ y hy
    have hev : F_U τ =ᶠ[𝓝 y] transField ν μ R c χy g τ :=
      Filter.mem_of_superset (hUo.mem_nhds hy) (hFU_eq τ)
    exact (w113_transField_diffAt hχy hν hR hc hμ hg τ (lt_of_le_of_lt hr0 hy)).congr_of_eventuallyEq hev
  have hPdm := w10_meas_pd hFU_meas hUo.measurableSet hd_FU j
  have hread : wardYoungRead ν R (fun τ => physPd (transField ν μ R c χy g τ) j) =
      wardYoungRead ν R (fun τ y => if y ∈ U then physPd (F_U τ) j y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have hyU : y ∈ U := lt_of_lt_of_le hrr hy
    have hev : F_U τ =ᶠ[𝓝 y] transField ν μ R c χy g τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) (hFU_eq τ)
    simp only [hyU, ↓reduceIte, physPd, hev.fderiv_eq]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R (fun τ => physPd (transField ν μ R c χy g τ) j))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas hPdm).aestronglyMeasurable
  have hA := wyl_bd_of_young (hC1 g hg j)
  have hB := wyl_bd_of_young (hC2 g hg j)
  refine w10_young_of_sum hFm hA hB (le_max_right _ _) (le_max_right _ _) le_rfl
    fun q => w10_read_dom hν hR (fun τ y hy => ?_) q
  have hyU : y ∈ U := lt_of_lt_of_le hrr hy
  have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hyU
  have hev : transField ν μ R c χy g τ =ᶠ[𝓝 y]
      fun z => streamCorr ν R χy (sepWre ν μ T) τ z +
        tcComm ν R χy (wardX0 ν μ R c g) τ z := by
    filter_upwards [hUo.mem_nhds hyU] with z hz
    have hz0 : 0 < ϱ z := lt_of_le_of_lt hr0 hz
    rw [w113_transField_eq hν hR hc hg τ z,
      w113_sepComm_eq_tcComm hχ hν hR hμ hP hS hM hAx τ hz0, hX0_eq]
  have hd1 : DifferentiableAt ℝ (streamCorr ν R χy (sepWre ν μ T) τ) y :=
    w113_streamCorrW_diffAt hχy hν hR hc hμ hg τ hy0
  have hd2 : DifferentiableAt ℝ (tcComm ν R χy (wardX0 ν μ R c g) τ) y := by
    rw [hX0_eq]
    exact w113_tcComm_diffAt hχ hν hR hμ hP hS hM hAx τ hy0
  have hpd_eq : physPd (transField ν μ R c χy g τ) j y =
      physPd (streamCorr ν R χy (sepWre ν μ T) τ) j y +
        physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y := by
    unfold physPd
    rw [hev.fderiv_eq, fderiv_fun_add hd1 hd2, add_apply]
  rw [hpd_eq]
  exact norm_add_le _ _

/-- **Measurability** of the young reading of `∂_jY` for `ageμ c (-3/2)`. -/
theorem w113_wardDYYoungMeas (ν μ R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (g : Chart → Ten3) (hg : IsOldL2 c ν g) (j : Fin 3) :
    AEStronglyMeasurable
      (wardYoungRead ν R (fun τ => physPd (wardY ν μ R c χy g τ) j)) (ageμ c (-3 / 2)) := by
  classical
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  have hres : ShiftedResolventYoung ν μ R c g :=
    wardYShiftedRes_proved ν μ R c g hν hR hc hμ hg
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hW := w113_W_eq (μ := μ) hν hR hc hg
  have hX0_eq := w10_X0_eq (μ := μ) hν hR hc hg
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set U : Set Space := youngOpen ν R
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hYW_meas : Measurable fun x : ℝ × Space => wardYoungW ν μ R c χy g x.1 x.2 := by
    have hWm : Measurable fun x : ℝ × Space => sepWre ν μ T x.1 x.2 :=
      sepWre_measurable ν μ hν T (fun a b => hS.measurable a b)
    have hχm : Measurable fun x : ℝ × Space => χy (ν * age R x.2) := by
      have hage : Measurable fun x : ℝ × Space => ν * age R x.2 := by
        unfold age
        exact measurable_const.mul
          (measurable_const.div ((continuous_ϱ.measurable.comp measurable_snd).pow_const 2))
      exact hχy.smooth.continuous.measurable.comp hage
    have hfun : (fun x : ℝ × Space => wardYoungW ν μ R c χy g x.1 x.2) =
        fun x => χy (ν * age R x.2) • sepWre ν μ T x.1 x.2 := by
      funext x; simp only [wardYoungW, hW, hTdef]
    rw [hfun]
    exact hχm.smul hWm
  set Y_U : ℝ → Space → Space := fun τ z =>
    wardYoungW ν μ R c χy g τ z +
      (streamCorr ν R χy (sepWre ν μ T) τ z + w113_tcCommU ν R χy (wardX0 ν μ R c g) τ z)
  have hYU_meas : Measurable (fun x : ℝ × Space => Y_U x.1 x.2) :=
    hYW_meas.add ((w113_streamCorrW_measurable (χy := χy) (μ := μ) hν hg).add
      (w113_tcCommU_measurable hχy hν hR hc hμ hg))
  have hYU_eq : ∀ τ z, z ∈ U → Y_U τ z = wardY ν μ R c χy g τ z := by
    intro τ z hz
    have hz0 : 0 < ϱ z := lt_of_le_of_lt hr0 hz
    unfold Y_U
    rw [w113_tcCommU_eq_of_mem (wardX0 ν μ R c g) τ hz, hX0_eq,
      ← w113_sepComm_eq_tcComm hχ hν hR hμ hP hS hM hAx τ hz0,
      ← w113_transField_eq hν hR hc hg τ z,
      ← wardY_split hχ hν.le hres τ hz0]
  have hd_YU : ∀ τ y, y ∈ U → DifferentiableAt ℝ (Y_U τ) y := by
    intro τ y hy
    have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hy
    have hev : Y_U τ =ᶠ[𝓝 y]
        fun z => wardYoungW ν μ R c χy g τ z + transField ν μ R c χy g τ z := by
      filter_upwards [hUo.mem_nhds hy] with z hz
      have hz0 : 0 < ϱ z := lt_of_le_of_lt hr0 hz
      rw [hYU_eq τ z hz, wardY_split hχ hν.le hres τ hz0]
    exact ((w113_wardYoungW_diffAt hχy hν hR hc hμ hg τ hy0).add
      (w113_transField_diffAt hχy hν hR hc hμ hg τ hy0)).congr_of_eventuallyEq hev
  have hPdm := w10_meas_pd hYU_meas hUo.measurableSet hd_YU j
  have hread : wardYoungRead ν R (fun τ => physPd (wardY ν μ R c χy g τ) j) =
      wardYoungRead ν R (fun τ y => if y ∈ U then physPd (Y_U τ) j y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have hyU : y ∈ U := lt_of_lt_of_le hrr hy
    have hev : Y_U τ =ᶠ[𝓝 y] wardY ν μ R c χy g τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) (hYU_eq τ)
    simp only [hyU, ↓reduceIte, physPd, hev.fderiv_eq]
  rw [hread]
  exact (w10_read_meas hPdm).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
end
