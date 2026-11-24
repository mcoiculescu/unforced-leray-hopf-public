import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3

/-!
# Measurability in `σ` of the dilated family (task `PartIII-b:C/srcL/6/3/3`)

Proves `XSPsiFamMeas` (see `Sub/PartIII-b_C_srcL_6_3.lean`).  For fixed `y` in the region
`U = {b < cylR y ^ 2}` and `σ > 1`, the iterated derivative of `y' ↦ σ * Z (scaleXY σ y') 2` is

  `σ • (D^n (Z₂) (scaleXY σ y)).compContinuousLinearMap (fun _ ↦ dilL σ)`,

where `Z₂ y' = Z y' 2` and `dilL σ` is the linear map `scaleXY σ` (chain rule on the open set
`dilL σ ⁻¹' U`).  Both factors are continuous in `σ` on `(1, ∞)`: the first because `D^n Z₂` is
continuous on `U` and `σ ↦ scaleXY σ y` is continuous into `U`; the second because the
composition `(f, g) ↦ g.compContinuousLinearMap f` is continuous.  Hence `σ ↦ ...` is continuous on
`(1, ∞)` and thus a.e. strongly measurable on `volume.restrict (Ioi 1)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The first summand `y ↦ (y 0, y 1, 0)` of the dilation. -/
private def dilD1 : Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => ![y 0, y 1, 0]
      map_add' := fun x y => by funext i; fin_cases i <;> simp
      map_smul' := fun c x => by funext i; fin_cases i <;> simp }

/-- The second summand `y ↦ (0, 0, y 2)` of the dilation. -/
private def dilD2 : Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => ![0, 0, y 2]
      map_add' := fun x y => by funext i; fin_cases i <;> simp
      map_smul' := fun c x => by funext i; fin_cases i <;> simp }

/-- The dilation `scaleXY σ` as a continuous linear map, depending continuously on `σ`. -/
private def dilL (σ : ℝ) : Vec3 →L[ℝ] Vec3 := σ • dilD1 + dilD2

private theorem dilL_apply (σ : ℝ) (y : Vec3) : dilL σ y = scaleXY σ y := by
  funext i
  fin_cases i <;> simp [dilL, dilD1, dilD2, scaleXY]

private theorem dilL_cont : Continuous (fun σ : ℝ => dilL σ) := by
  unfold dilL
  exact (continuous_id.smul continuous_const).add continuous_const

private theorem scaleXY_mem {b σ : ℝ} (hσ : 1 ≤ σ) {y : Vec3} (hy : b < cylR y ^ 2) :
    b < cylR (scaleXY σ y) ^ 2 := by
  rw [cylR_sq] at hy ⊢
  unfold scaleXY
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hσ1 : (1 : ℝ) ≤ σ ^ 2 := by nlinarith
  have hnn : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
  have hid : (σ * y 0) ^ 2 + (σ * y 1) ^ 2 = σ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by ring
  rw [hid]
  nlinarith [mul_nonneg hnn (sub_nonneg.mpr hσ1)]

private theorem dilL_mem {b σ : ℝ} (hσ : 1 < σ) {y : Vec3} (hy : b < cylR y ^ 2) :
    dilL σ y ∈ {y : Vec3 | b < cylR y ^ 2} := by
  show b < cylR (dilL σ y) ^ 2
  rw [dilL_apply]
  exact scaleXY_mem (le_of_lt hσ) hy

/-- Chain rule and scalar factor for the family, at `σ > 1`. -/
private theorem iteratedFDeriv_family_eq (b : ℝ) (Z : Vec3 → Vec3)
    (hZ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z {y | b < cylR y ^ 2})
    (n : ℕ) {σ : ℝ} (hσ : 1 < σ) {y : Vec3} (hy : b < cylR y ^ 2) :
    iteratedFDeriv ℝ n (fun y' => σ * Z (scaleXY σ y') 2) y =
      σ • ((iteratedFDerivWithin ℝ n (fun v => Z v 2) {y | b < cylR y ^ 2} (dilL σ y)).compContinuousLinearMap
        (fun _ => dilL σ)) := by
  have hUo : IsOpen {y : Vec3 | b < cylR y ^ 2} := isOpen_lt continuous_const (continuous_cylR.pow 2)
  have hUu : UniqueDiffOn ℝ {y : Vec3 | b < cylR y ^ 2} := hUo.uniqueDiffOn
  have hZc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => Z v 2) {y | b < cylR y ^ 2} :=
    (contDiff_apply ℝ ℝ 2).comp_contDiffOn hZ
  have hpre : IsOpen (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) :=
    hUo.preimage (dilL σ).continuous
  have hmapsto : MapsTo (dilL σ) (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2})
      {y : Vec3 | b < cylR y ^ 2} := fun z hz => hz
  have hyP : y ∈ dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2} := dilL_mem hσ hy
  have hZcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((fun v => Z v 2) ∘ dilL σ)
      (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) :=
    ContDiffOn.comp hZc (dilL σ).contDiff.contDiffOn hmapsto
  have hfun : (fun y' => σ * Z (scaleXY σ y') 2)
      = σ • ((fun v => Z v 2) ∘ dilL σ) := by
    funext y'
    simp [dilL_apply, smul_eq_mul]
  have key := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := σ • ((fun v => Z v 2) ∘ dilL σ)) n hpre hyP
  rw [hfun, ← key]
  have hc1 : iteratedFDerivWithin ℝ n (σ • ((fun v => Z v 2) ∘ dilL σ))
      (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) y
      = σ • iteratedFDerivWithin ℝ n ((fun v => Z v 2) ∘ dilL σ)
          (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) y :=
    iteratedFDerivWithin_const_smul_apply
      (hZcomp.contDiffWithinAt hyP |>.of_le (by exact_mod_cast le_top)) hpre.uniqueDiffOn hyP
  have hc2 : iteratedFDerivWithin ℝ n ((fun v => Z v 2) ∘ dilL σ)
      (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) y
      = (iteratedFDerivWithin ℝ n (fun v => Z v 2) {y | b < cylR y ^ 2} (dilL σ y)).compContinuousLinearMap
          (fun _ => dilL σ) :=
    ContinuousLinearMap.iteratedFDerivWithin_comp_right (dilL σ) hZc
      hUu hpre.uniqueDiffOn hyP (by exact_mod_cast le_top)
  rw [hc1, hc2]

/-- Continuity in `σ > 1` of the right-hand side. -/
private theorem rhs_continuousOn (b : ℝ) (Z : Vec3 → Vec3)
    (hZ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z {y | b < cylR y ^ 2})
    (n : ℕ) {y : Vec3} (hy : b < cylR y ^ 2) :
    ContinuousOn (fun σ : ℝ => σ • ((iteratedFDerivWithin ℝ n (fun v => Z v 2) {y | b < cylR y ^ 2}
        (dilL σ y)).compContinuousLinearMap (fun _ => dilL σ))) (Ioi 1) := by
  have hUo : IsOpen {y : Vec3 | b < cylR y ^ 2} := isOpen_lt continuous_const (continuous_cylR.pow 2)
  have hUu : UniqueDiffOn ℝ {y : Vec3 | b < cylR y ^ 2} := hUo.uniqueDiffOn
  have hZc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => Z v 2) {y | b < cylR y ^ 2} :=
    (contDiff_apply ℝ ℝ 2).comp_contDiffOn hZ
  have hcontW : ContinuousOn (iteratedFDerivWithin ℝ n (fun v => Z v 2) {y | b < cylR y ^ 2})
      {y | b < cylR y ^ 2} :=
    hZc.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hUu
  have hdy : ContinuousOn (fun σ : ℝ => dilL σ y) (Ioi 1) :=
    (dilL_cont.clm_apply continuous_const).continuousOn
  have hM : ContinuousOn (fun σ : ℝ => iteratedFDerivWithin ℝ n (fun v => Z v 2)
      {y | b < cylR y ^ 2} (dilL σ y)) (Ioi 1) :=
    hcontW.comp hdy (fun σ hσ => dilL_mem hσ hy)
  have hΨ : ContinuousOn (fun σ : ℝ =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin n => Vec3) (fun _ : Fin n => Vec3) ℝ) (fun _ => dilL σ)) (Ioi 1) :=
    ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin n => Vec3) (fun _ : Fin n => Vec3) ℝ).cont.comp
      (continuous_pi fun _ => dilL_cont)).continuousOn
  exact continuousOn_id.smul (hΨ.clm_apply hM)

theorem xsPsiFamMeas : XSPsiFamMeas := by
  intro b Z hH n y hy
  obtain ⟨-, hZ, -⟩ := hH
  have hcont : ContinuousOn
      (fun σ : ℝ => iteratedFDeriv ℝ n (fun y' => σ * Z (scaleXY σ y') 2) y) (Ioi 1) :=
    (rhs_continuousOn b Z hZ n hy).congr
      (fun σ hσ => iteratedFDeriv_family_eq b Z hZ n hσ hy)
  exact hcont.aestronglyMeasurable measurableSet_Ioi

end UnforcedLeray.Short.PartIIIb.Concrete
