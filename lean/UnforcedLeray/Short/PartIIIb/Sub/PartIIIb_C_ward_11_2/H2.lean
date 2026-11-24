import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_2.H1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2

/-!
# Helpers for `wardD2XYoungL2_proved` (2): product rule for `physPd2` and second partials of `Ψ`

Source of record: `the November 2 reference manuscript` (73 pages),
3687-3713, 4178-4186.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- First partial derivative of a scalar field. -/
def w112_sd1 (φ : Space → ℝ) (k : Fin 3) (y : Space) : ℝ :=
  fderiv ℝ φ y (coordinateVector k)

/-- Second partial derivative `∂_j ∂_l φ` of a scalar field. -/
def w112_sd2 (φ : Space → ℝ) (j l : Fin 3) (y : Space) : ℝ :=
  fderiv ℝ (fun y' => w112_sd1 φ l y') y (coordinateVector j)

theorem w112_coord_abs_le (j i : Fin 3) : |(coordinateVector j : Space) i| ≤ 1 := by
  calc |(coordinateVector j : Space) i| ≤ ‖(coordinateVector j : Space)‖ := wyl_abs_apply_le _ i
    _ = 1 := wyl_norm_coordinateVector j

/-- Product rule for `physPd2 (φ • F) j l y` on an open set. -/
theorem w112_physPd2_smul {U : Set Space} (hUo : IsOpen U) {φ : Space → ℝ} {F : Space → Space}
    (hφ : ∀ y ∈ U, DifferentiableAt ℝ φ y)
    (hφ1 : ∀ l : Fin 3, ∀ y ∈ U, DifferentiableAt ℝ (fun y' => w112_sd1 φ l y') y)
    (hF : ∀ y ∈ U, DifferentiableAt ℝ F y)
    (hF1 : ∀ l : Fin 3, ∀ y ∈ U, DifferentiableAt ℝ (fun y' => physPd F l y') y)
    {y : Space} (hy : y ∈ U) (j l : Fin 3) :
    physPd2 (fun x => φ x • F x) j l y =
      φ y • physPd2 F j l y + w112_sd1 φ j y • physPd F l y +
        w112_sd1 φ l y • physPd F j y + w112_sd2 φ j l y • F y := by
  have hev : (fun y' => physPd (fun x => φ x • F x) l y') =ᶠ[𝓝 y]
      fun y' => φ y' • physPd F l y' + w112_sd1 φ l y' • F y' := by
    filter_upwards [hUo.mem_nhds hy] with y' hy'
    have hsm := ((hφ y' hy').hasFDerivAt.smul (hF y' hy').hasFDerivAt).fderiv
    have happ := congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector l)) hsm
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] at happ
    exact happ
  have hd1 := (hφ y hy).hasFDerivAt.smul (hF1 l y hy).hasFDerivAt
  have hd2 := (hφ1 l y hy).hasFDerivAt.smul (hF y hy).hasFDerivAt
  have hsum := (hd1.add hd2).congr_of_eventuallyEq hev
  have happ := congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j)) hsum.fderiv
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] at happ
  change (fderiv ℝ (fun y' => physPd (fun x => φ x • F x) l y') y) (coordinateVector j) = _
  rw [happ]
  unfold physPd2 physPd w112_sd1 w112_sd2
  abel

theorem w112_physPd2_smul_norm_le {U : Set Space} (hUo : IsOpen U) {φ : Space → ℝ}
    {F : Space → Space}
    (hφ : ∀ y ∈ U, DifferentiableAt ℝ φ y)
    (hφ1 : ∀ l : Fin 3, ∀ y ∈ U, DifferentiableAt ℝ (fun y' => w112_sd1 φ l y') y)
    (hF : ∀ y ∈ U, DifferentiableAt ℝ F y)
    (hF1 : ∀ l : Fin 3, ∀ y ∈ U, DifferentiableAt ℝ (fun y' => physPd F l y') y)
    {y : Space} (hy : y ∈ U) (j l : Fin 3) :
    ‖physPd2 (fun x => φ x • F x) j l y‖ ≤
      |φ y| * ‖physPd2 F j l y‖ + |w112_sd1 φ j y| * ‖physPd F l y‖ +
        |w112_sd1 φ l y| * ‖physPd F j y‖ + |w112_sd2 φ j l y| * ‖F y‖ := by
  rw [w112_physPd2_smul hUo hφ hφ1 hF hF1 hy j l]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
      · rw [norm_smul, Real.norm_eq_abs]
    · rw [norm_smul, Real.norm_eq_abs]
  · rw [norm_smul, Real.norm_eq_abs]

section Psi

variable {ν μ R c : ℝ} {g : Chart → Ten3}

/-- On `youngOpen ν R`, `Z(meridPt y)_2 = Z(y)_2` and `ϱ y * Z(meridPt y)_0 = y_0 Z(y)_0 + y_1 Z(y)_1`. -/
theorem w112_axi_merid (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : y ∈ youngOpen ν R) :
    wardX0 ν μ R c g τ (meridPt y) 2 = wardX0 ν μ R c g τ y 2 ∧
      ϱ y * wardX0 ν μ R c g τ (meridPt y) 0 =
        y 0 * wardX0 ν μ R c g τ y 0 + y 1 * wardX0 ν μ R c g τ y 1 := by
  have hyax : y ∉ axis := t9_not_axis hν hR hy
  have hρ : 0 < ϱ y := ϱ_pos hyax
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Axi.ϱ_sq y
  have hax := w2_axi hν hR hc hμ hg τ y hy hyax
  have h0 : wardX0 ν μ R c g τ y 0 = (y 0 / ϱ y) * wardX0 ν μ R c g τ (meridPt y) 0 := by
    have := congrArg (fun v : Space => v 0) hax
    simp [frameL_apply, eR, hor] at this
    rw [this]; ring
  have h1 : wardX0 ν μ R c g τ y 1 = (y 1 / ϱ y) * wardX0 ν μ R c g τ (meridPt y) 0 := by
    have := congrArg (fun v : Space => v 1) hax
    simp [frameL_apply, eR, hor] at this
    rw [this]; ring
  have h2 : wardX0 ν μ R c g τ y 2 = wardX0 ν μ R c g τ (meridPt y) 2 := by
    have := congrArg (fun v : Space => v 2) hax
    simpa [frameL_apply, eR, hor] using this
  refine ⟨h2.symm, ?_⟩
  rw [h0, h1]
  have hne : ϱ y ≠ 0 := hρ.ne'
  calc ϱ y * wardX0 ν μ R c g τ (meridPt y) 0
      = (ϱ y ^ 2 / ϱ y) * wardX0 ν μ R c g τ (meridPt y) 0 := by
        congr 1; field_simp
    _ = ((y 0 ^ 2 + y 1 ^ 2) / ϱ y) * wardX0 ν μ R c g τ (meridPt y) 0 := by rw [hρ2]
    _ = y 0 * (y 0 / ϱ y * wardX0 ν μ R c g τ (meridPt y) 0) +
          y 1 * (y 1 / ϱ y * wardX0 ν μ R c g τ (meridPt y) 0) := by ring

/-- Exact polynomial-times-`X₀` formula for `∂_l(Ψ_{X₀}(ϱ y, y_2))` on `youngOpen ν R`. -/
theorem w112_psi_sd1_eq (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) (τ : ℝ) (l : Fin 3) {y : Space} (hy : y ∈ youngOpen ν R) :
    w112_sd1 (fun x : Space => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)) l y =
      wardX0 ν μ R c g τ y 2 * (y 0 * coordinateVector l 0 + y 1 * coordinateVector l 1) -
        (y 0 * wardX0 ν μ R c g τ y 0 + y 1 * wardX0 ν μ R c g τ y 1) * coordinateVector l 2 := by
  have hyax : y ∉ axis := t9_not_axis hν hR hy
  have hρ : 0 < ϱ y := ϱ_pos hyax
  have hΨ := w2_psi_hasFDeriv hν hR hc hμ hg τ hy
  obtain ⟨hm2, hm0⟩ := w112_axi_merid hν hR hc hμ hg τ hy
  unfold w112_sd1
  rw [hΨ.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ϱD_apply, EuclideanSpace.proj, PiLp.proj_apply]
  rw [hm2, hm0]
  have hne : ϱ y ≠ 0 := hρ.ne'
  have h1 : ϱ y * wardX0 ν μ R c g τ y 2 *
      ((y 0 * coordinateVector l 0 + y 1 * coordinateVector l 1) / ϱ y) =
      wardX0 ν μ R c g τ y 2 * (y 0 * coordinateVector l 0 + y 1 * coordinateVector l 1) := by
    field_simp
  linarith

/-- Derivative of `y ↦ y a * F y b` at a point where `F` is differentiable. -/
theorem w112_hasFDerivAt_coord_mul {F : Space → Space} {y : Space} (hF : DifferentiableAt ℝ F y)
    (a b : Fin 3) :
    HasFDerivAt (fun x : Space => x a * F x b)
      (y a • ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp (fderiv ℝ F y)) +
        F y b • (EuclideanSpace.proj a : Space →L[ℝ] ℝ)) y := by
  have ha : HasFDerivAt (fun x : Space => x a) (EuclideanSpace.proj a : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt
  have hb : HasFDerivAt (fun x : Space => F x b)
      ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp (fderiv ℝ F y)) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.comp y hF.hasFDerivAt
  exact ha.mul hb

/-- Differentiability and bounds of the first and second partials of `Ψ_{X₀}(ϱ y, y_2)`. -/
theorem w112_psi_jet (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : y ∈ youngOpen ν R) :
    DifferentiableAt ℝ (fun x : Space => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)) y ∧
      (∀ l : Fin 3,
        DifferentiableAt ℝ
          (fun x : Space =>
            w112_sd1 (fun x' : Space => outPrim (wardX0 ν μ R c g) τ (ϱ x') (x' 2)) l x) y ∧
        |w112_sd1 (fun x : Space => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)) l y| ≤
          2 * ϱ y * ‖wardX0 ν μ R c g τ y‖) ∧
      (∀ j l : Fin 3,
        |w112_sd2 (fun x : Space => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)) j l y| ≤
          4 * ϱ y * ‖physPd (wardX0 ν μ R c g τ) j y‖ + 4 * ‖wardX0 ν μ R c g τ y‖) := by
  set Z := wardX0 ν μ R c g τ
  set Ψ : Space → ℝ := fun x => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hZ : DifferentiableAt ℝ Z y :=
    ((w2_smooth hν hR hc hμ hg τ).contDiffAt (hUo.mem_nhds hy)).differentiableAt (by simp)
  have hΨd : DifferentiableAt ℝ Ψ y := (w2_psi_hasFDeriv hν hR hc hμ hg τ hy).differentiableAt
  have hy0 : |y 0| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  have hy1 : |y 1| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 0)])
  have hρ0 : 0 ≤ ϱ y := ϱ_nonneg y
  have hd_ab : ∀ a b : Fin 3, HasFDerivAt (fun x : Space => x a * Z x b)
      (y a • ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp (fderiv ℝ Z y)) +
        Z y b • (EuclideanSpace.proj a : Space →L[ℝ] ℝ)) y :=
    fun a b => w112_hasFDerivAt_coord_mul hZ a b
  have hbd_ab : ∀ (a : Fin 3), |y a| ≤ ϱ y → ∀ (b j : Fin 3),
      |(y a • ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp (fderiv ℝ Z y)) +
        Z y b • (EuclideanSpace.proj a : Space →L[ℝ] ℝ)) (coordinateVector j)| ≤
        ϱ y * ‖physPd Z j y‖ + ‖Z y‖ := by
    intro a hya b j
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, EuclideanSpace.proj,
      PiLp.proj_apply, smul_eq_mul]
    have h1 : |y a * physPd Z j y b| ≤ ϱ y * ‖physPd Z j y‖ := by
      rw [abs_mul]
      exact mul_le_mul hya (wyl_abs_apply_le _ b) (abs_nonneg _) hρ0
    have h2 : |Z y b * coordinateVector j a| ≤ ‖Z y‖ := by
      rw [abs_mul]
      calc |Z y b| * |coordinateVector j a| ≤ ‖Z y‖ * 1 :=
            mul_le_mul (wyl_abs_apply_le _ b) (w112_coord_abs_le j a) (abs_nonneg _) (norm_nonneg _)
        _ = ‖Z y‖ := mul_one _
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hstep : ∀ l : Fin 3,
      DifferentiableAt ℝ (fun x => w112_sd1 Ψ l x) y ∧
      |w112_sd1 Ψ l y| ≤ 2 * ϱ y * ‖Z y‖ ∧
      ∀ j : Fin 3, |w112_sd2 Ψ j l y| ≤ 4 * ϱ y * ‖physPd Z j y‖ + 4 * ‖Z y‖ := by
    intro l
    have hev : (fun x => w112_sd1 Ψ l x) =ᶠ[𝓝 y] fun x =>
        (x 0 * Z x 2) * coordinateVector l 0 + (x 1 * Z x 2) * coordinateVector l 1 -
          ((x 0 * Z x 0) * coordinateVector l 2 + (x 1 * Z x 1) * coordinateVector l 2) := by
      filter_upwards [hUo.mem_nhds hy] with x hx
      rw [w112_psi_sd1_eq hν hR hc hμ hg τ l hx]
      ring
    have hd := (((hd_ab 0 2).mul_const (coordinateVector l 0)).add
      ((hd_ab 1 2).mul_const (coordinateVector l 1))).sub
      (((hd_ab 0 0).mul_const (coordinateVector l 2)).add
        ((hd_ab 1 1).mul_const (coordinateVector l 2)))
    have hd' := hd.congr_of_eventuallyEq hev
    refine ⟨hd'.differentiableAt, ?_, fun j => ?_⟩
    · rw [w112_psi_sd1_eq hν hR hc hμ hg τ l hy]
      have z0 := wyl_abs_apply_le (Z y) 0
      have z1 := wyl_abs_apply_le (Z y) 1
      have z2 := wyl_abs_apply_le (Z y) 2
      fin_cases l <;> simp [coordinateVector]
      · exact (mul_le_mul z2 hy0 (abs_nonneg _) (norm_nonneg _)).trans (by nlinarith [norm_nonneg (Z y)])
      · exact (mul_le_mul z2 hy1 (abs_nonneg _) (norm_nonneg _)).trans (by nlinarith [norm_nonneg (Z y)])
      · refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_neg, abs_mul, abs_mul]
        have m0 := mul_le_mul hy0 z0 (abs_nonneg _) hρ0
        have m1 := mul_le_mul hy1 z1 (abs_nonneg _) hρ0
        linarith
    · unfold w112_sd2
      rw [hd'.fderiv]
      simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
      have b02 := hbd_ab 0 hy0 2 j
      have b12 := hbd_ab 1 hy1 2 j
      have b00 := hbd_ab 0 hy0 0 j
      have b11 := hbd_ab 1 hy1 1 j
      have c0 := w112_coord_abs_le l 0
      have c1 := w112_coord_abs_le l 1
      have c2 := w112_coord_abs_le l 2
      set B := ϱ y * ‖physPd Z j y‖ + ‖Z y‖
      have hB0 : 0 ≤ B := by positivity
      have hcm : ∀ {c d : ℝ}, |c| ≤ 1 → |d| ≤ B → |c * d| ≤ B := fun {c d} hc hd => by
        rw [abs_mul]
        calc |c| * |d| ≤ 1 * B := mul_le_mul hc hd (abs_nonneg _) zero_le_one
          _ = B := one_mul B
      calc _ ≤ (B + B) + (B + B) := by
            refine (abs_sub _ _).trans (add_le_add ?_ ?_)
            · exact (abs_add_le _ _).trans (add_le_add (hcm c0 b02) (hcm c1 b12))
            · exact (abs_add_le _ _).trans (add_le_add (hcm c2 b00) (hcm c2 b11))
        _ = 4 * ϱ y * ‖physPd Z j y‖ + 4 * ‖Z y‖ := by simp only [B]; ring
  exact ⟨hΨd, fun l => ⟨(hstep l).1, (hstep l).2.1⟩, fun j l => (hstep l).2.2 j⟩

end Psi

end UnforcedLeray.Short.PartIIIb.Concrete
end
