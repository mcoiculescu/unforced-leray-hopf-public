import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Formula.Line

/-!
# The six line entries (`PartIII-b:C/rep/8/2/1/3/a`, helper 4)

Entries `(0,0),(0,2),(2,0),(2,2),(0,1),(2,1)` of the table, by differentiating the
azimuth-zero first derivatives along `y + t e₀` and `y + t e₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete

abbrev SProf : Set (ℝ × (ℝ × ℝ)) := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))

theorem contDiffAt_prof {R τ : ℝ} (hR : 0 < R) {B : ℝ × (ℝ × ℝ) → Merid}
    (hB : ContDiffOn ℝ 2 B SProf) {y : Space} (hy : y ∉ axis) :
    ContDiffAt ℝ 2 B (chart R τ y) :=
  hB.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds (mapsTo_chart R τ hR hy))

theorem chart_one_az {R τ : ℝ} (hR : 0 < R) {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    (chart R τ y).1 = R ^ 2 / y 0 ^ 2 := by
  show age R y = _
  rw [age, ϱ_az hy0 hy1]

theorem sqrt_chart_az {R τ : ℝ} (hR : 0 < R) {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    Real.sqrt (chart R τ y).1 = R / y 0 := by
  show √(age R y) = _
  rw [sqrt_age hR (not_axis_az hy0), ϱ_az hy0 hy1]

theorem hasDerivAt_merSp_line {R τ : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ axis)
    {F : ℝ × (ℝ × ℝ) → Merid} (hF : DifferentiableAt ℝ F (chart R τ y)) (v : Space) :
    HasDerivAt (fun t : ℝ => merSpL (F (chart R τ (y + t • v))))
      (merSp (fderiv ℝ F (chart R τ y) (chartD R y v))) 0 := by
  have h := hasDerivAt_prof_line hR hy hF v
  have := merSpL.hasFDerivAt.comp_hasDerivAt (0:ℝ) h
  rw [merSpL_apply] at this
  exact this

theorem hasDerivAt_coord_line (y v : Space) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => (y + t • v) i) (v i) 0 := by
  have : HasDerivAt (fun t : ℝ => y i + t * v i) (v i) 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const (v i)).const_add (y i)
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp

/-- Derivative of the hoop-direction first derivative along a line. -/
theorem hasDerivAt_one_line {R τ : ℝ} (hR : 0 < R) {y : Space} (hy0 : 0 < y 0)
    {B : ℝ × (ℝ × ℝ) → Merid} (hB : DifferentiableAt ℝ B (chart R τ y)) (v : Space) :
    HasDerivAt (fun t : ℝ => (B (chart R τ (y + t • v)) 0 * ((y + t • v) 0)⁻¹) •
        (coordinateVector 1 : Space))
      (((fderiv ℝ B (chart R τ y) (chartD R y v)) 0 * (y 0)⁻¹ +
        B (chart R τ y) 0 * (-(v 0) / y 0 ^ 2)) • (coordinateVector 1 : Space)) 0 := by
  have hy := not_axis_az hy0
  have h1 := hasDerivAt_prof_line hR hy hB v
  have h1' : HasDerivAt (fun t : ℝ => B (chart R τ (y + t • v)) 0)
      ((fderiv ℝ B (chart R τ y) (chartD R y v)) 0) 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
  have h2 := (hasDerivAt_coord_line y v 0).inv (by simpa using hy0.ne')
  have h3 := (h1'.mul h2).smul_const (coordinateVector 1 : Space)
  refine h3.congr_deriv ?_
  simp

theorem entry_00 {R τ : ℝ} (hR : 0 < R) {B : ℝ × (ℝ × ℝ) → Merid} (hB : ContDiffOn ℝ 2 B SProf)
    {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    physPd2 (Gf R τ B) 0 0 y = merSp (Drho R⁻¹ (Drho R⁻¹ B) (chart R τ y)) := by
  have hy := not_axis_az hy0
  have hBa := contDiffAt_prof (τ := τ) hR hB hy
  have hGa : ContDiffAt ℝ 2 (Gf R τ B) y := contDiffAt_frame R τ hR B hB hy
  refine entry_of_line hGa 0 0 hy0 hy1 (Or.inl rfl)
    (fun y' => merSpL (Drho R⁻¹ B (chart R τ y'))) _ ?_ ?_
  · intro y' h0 h1
    rw [physPd_Gf_zero hR h0 h1
      ((contDiffAt_prof hR hB (not_axis_az h0)).differentiableAt (by norm_num)), merSpL_apply]
  · have hF : DifferentiableAt ℝ (Drho R⁻¹ B) (chart R τ y) :=
      (contDiffAt_Drho R⁻¹ (age_pos hR.ne' hy) hBa).differentiableAt (by norm_num)
    have := hasDerivAt_merSp_line hR hy hF (coordinateVector 0)
    rwa [fderiv_prof_e0 hR hy0 hy1 hF] at this


theorem entry_02 {R τ : ℝ} (hR : 0 < R) {B : ℝ × (ℝ × ℝ) → Merid} (hB : ContDiffOn ℝ 2 B SProf)
    {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    physPd2 (Gf R τ B) 0 2 y = merSp (Drho R⁻¹ (Dz B) (chart R τ y)) := by
  have hy := not_axis_az hy0
  have hBa := contDiffAt_prof (τ := τ) hR hB hy
  have hGa : ContDiffAt ℝ 2 (Gf R τ B) y := contDiffAt_frame R τ hR B hB hy
  refine entry_of_line hGa 0 2 hy0 hy1 (Or.inl rfl)
    (fun y' => merSpL (Dz B (chart R τ y'))) _ ?_ ?_
  · intro y' h0 h1
    rw [physPd_Gf_two hR h0 h1
      ((contDiffAt_prof hR hB (not_axis_az h0)).differentiableAt (by norm_num)), merSpL_apply]
  · have hF : DifferentiableAt ℝ (Dz B) (chart R τ y) :=
      (contDiffAt_Dz (age_pos hR.ne' hy) hBa).differentiableAt (by norm_num)
    have := hasDerivAt_merSp_line hR hy hF (coordinateVector 0)
    rwa [fderiv_prof_e0 hR hy0 hy1 hF] at this

theorem entry_20 {R τ : ℝ} (hR : 0 < R) {B : ℝ × (ℝ × ℝ) → Merid} (hB : ContDiffOn ℝ 2 B SProf)
    {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    physPd2 (Gf R τ B) 2 0 y = merSp (Dz (Drho R⁻¹ B) (chart R τ y)) := by
  have hy := not_axis_az hy0
  have hBa := contDiffAt_prof (τ := τ) hR hB hy
  have hGa : ContDiffAt ℝ 2 (Gf R τ B) y := contDiffAt_frame R τ hR B hB hy
  refine entry_of_line hGa 2 0 hy0 hy1 (Or.inr rfl)
    (fun y' => merSpL (Drho R⁻¹ B (chart R τ y'))) _ ?_ ?_
  · intro y' h0 h1
    rw [physPd_Gf_zero hR h0 h1
      ((contDiffAt_prof hR hB (not_axis_az h0)).differentiableAt (by norm_num)), merSpL_apply]
  · have hF : DifferentiableAt ℝ (Drho R⁻¹ B) (chart R τ y) :=
      (contDiffAt_Drho R⁻¹ (age_pos hR.ne' hy) hBa).differentiableAt (by norm_num)
    have := hasDerivAt_merSp_line hR hy hF (coordinateVector 2)
    rwa [fderiv_prof_e3 hR hy0 hF] at this

theorem entry_22 {R τ : ℝ} (hR : 0 < R) {B : ℝ × (ℝ × ℝ) → Merid} (hB : ContDiffOn ℝ 2 B SProf)
    {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    physPd2 (Gf R τ B) 2 2 y = merSp (Dz (Dz B) (chart R τ y)) := by
  have hy := not_axis_az hy0
  have hBa := contDiffAt_prof (τ := τ) hR hB hy
  have hGa : ContDiffAt ℝ 2 (Gf R τ B) y := contDiffAt_frame R τ hR B hB hy
  refine entry_of_line hGa 2 2 hy0 hy1 (Or.inr rfl)
    (fun y' => merSpL (Dz B (chart R τ y'))) _ ?_ ?_
  · intro y' h0 h1
    rw [physPd_Gf_two hR h0 h1
      ((contDiffAt_prof hR hB (not_axis_az h0)).differentiableAt (by norm_num)), merSpL_apply]
  · have hF : DifferentiableAt ℝ (Dz B) (chart R τ y) :=
      (contDiffAt_Dz (age_pos hR.ne' hy) hBa).differentiableAt (by norm_num)
    have := hasDerivAt_merSp_line hR hy hF (coordinateVector 2)
    rwa [fderiv_prof_e3 hR hy0 hF] at this

theorem entry_01_raw {R τ : ℝ} (hR : 0 < R) {B : ℝ × (ℝ × ℝ) → Merid}
    (hB : ContDiffOn ℝ 2 B SProf) {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    physPd2 (Gf R τ B) 0 1 y =
      (((Drho R⁻¹ B (chart R τ y)) 0 * (y 0)⁻¹ + B (chart R τ y) 0 * (-1 / y 0 ^ 2)) •
        (coordinateVector 1 : Space)) := by
  have hy := not_axis_az hy0
  have hBa := contDiffAt_prof (τ := τ) hR hB hy
  have hGa : ContDiffAt ℝ 2 (Gf R τ B) y := contDiffAt_frame R τ hR B hB hy
  have hBd := hBa.differentiableAt (by norm_num)
  have := hasDerivAt_one_line hR hy0 hBd (coordinateVector 0)
  rw [fderiv_prof_e0 hR hy0 hy1 hBd] at this
  refine entry_of_line hGa 0 1 hy0 hy1 (Or.inl rfl)
    (fun y' => (B (chart R τ y') 0 * (y' 0)⁻¹) • (coordinateVector 1 : Space)) _ ?_ (this.congr_deriv (by simp [coordinateVector_apply]))
  intro y' h0 h1
  rw [physPd_Gf_one hR h0 h1
    ((contDiffAt_prof hR hB (not_axis_az h0)).differentiableAt (by norm_num)), div_eq_mul_inv]

theorem entry_21_raw {R τ : ℝ} (hR : 0 < R) {B : ℝ × (ℝ × ℝ) → Merid}
    (hB : ContDiffOn ℝ 2 B SProf) {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    physPd2 (Gf R τ B) 2 1 y =
      (((Dz B (chart R τ y)) 0 * (y 0)⁻¹) • (coordinateVector 1 : Space)) := by
  have hy := not_axis_az hy0
  have hBa := contDiffAt_prof (τ := τ) hR hB hy
  have hGa : ContDiffAt ℝ 2 (Gf R τ B) y := contDiffAt_frame R τ hR B hB hy
  have hBd := hBa.differentiableAt (by norm_num)
  have := hasDerivAt_one_line hR hy0 hBd (coordinateVector 2)
  rw [fderiv_prof_e3 hR hy0 hBd] at this
  refine entry_of_line hGa 2 1 hy0 hy1 (Or.inr rfl)
    (fun y' => (B (chart R τ y') 0 * (y' 0)⁻¹) • (coordinateVector 1 : Space)) _ ?_ (this.congr_deriv (by simp [coordinateVector_apply]))
  intro y' h0 h1
  rw [physPd_Gf_one hR h0 h1
    ((contDiffAt_prof hR hB (not_axis_az h0)).differentiableAt (by norm_num)), div_eq_mul_inv]

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux
