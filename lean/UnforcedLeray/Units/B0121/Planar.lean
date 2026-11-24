import UnforcedLeray.Units.B0121.Gauss

/-!
# B0121 helper: `X_G` inside `L²(ℝ², G⁻¹ dy)`

Blueprint unit B0121 (`eq:st18-t00100`, `paper/main.tex` lines 1856--1865). The derivatives of
`eq:st18-t00100` act on the planar function `f(r, ϑ) = f₂(r) e^{2iϑ}` of `f ∈ X_G`
(`eq:st18-t00005`, tex line 674; B0010's `angularTwoField`), measured in the ambient Gaussian
space `L²(ℝ², G⁻¹ dy)` (tex lines 1859--1862).

* `planar f`: the planar function of `f ∈ X_G`;
* `memGaussL2_angularTwoField`: it lies in `L²(ℝ², G⁻¹ dy)`, with
  `‖f‖²_{L²(ℝ², G⁻¹ dy)} = 2π ‖f‖²_{X_G}` (`gaussNormSq_angularTwoField`; the pairing of `X_G`
  omits the angular factor `2π`, tex line 678);
* `toXG χ = U_G⁻¹ χ ∈ X_G` for angular-two Schwartz `χ` (B0094) and the pairing formulas
  `inner_J_eq_toXG`, `integral_planar_mul_conj_conjG`, `planar_sub_gS`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap InnerProductSpace ComplexConjugate ContDiff Real ENNReal

namespace UnforcedLeray.B0121

open UnforcedLeray.B0094 UnforcedLeray.B0010 UnforcedLeray.GaussianVortex

/-- The planar function `f(r, ϑ) = f₂(r) e^{2iϑ}` of `f ∈ X_G` (tex line 674), built from the
`L²` representative `f₂ = ⇑f` of the profile (B0010's `angularTwoField`). -/
def planar (f : XG) : ℝ × ℝ → ℂ := angularTwoField ⇑f

theorem measurable_polarCoord_fun : Measurable fun z : ℝ × ℝ => polarCoord z := by
  have h : (fun z : ℝ × ℝ => polarCoord z) =
      fun z => (Real.sqrt (z.1 ^ 2 + z.2 ^ 2), Complex.arg (Complex.equivRealProd.symm z)) := by
    funext z
    rfl
  rw [h]
  refine Measurable.prodMk ?_ ?_
  · exact (Real.continuous_sqrt.comp (by fun_prop)).measurable
  · exact Complex.measurable_arg.comp Complex.equivRealProdCLM.symm.continuous.measurable

theorem stronglyMeasurable_angularTwoField {h₂ : ℝ → ℂ} (hm : StronglyMeasurable h₂) :
    StronglyMeasurable (angularTwoField h₂) := by
  unfold angularTwoField
  have h1 : StronglyMeasurable fun z : ℝ × ℝ => h₂ (polarCoord z).1 :=
    hm.comp_measurable measurable_polarCoord_fun.fst
  have h2 : Measurable fun z : ℝ × ℝ => Complex.exp (2 * Complex.I * ((polarCoord z).2 : ℂ)) :=
    Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp measurable_polarCoord_fun.snd))
  exact h1.mul h2.stronglyMeasurable

theorem norm_exp_two_mul_I (θ : ℝ) : ‖Complex.exp (2 * Complex.I * (θ : ℂ))‖ = 1 := by
  rw [show 2 * Complex.I * (θ : ℂ) = ((2 * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem gaussianWeight_polarCoord_symm (p : ℝ × ℝ) (hp : 0 < p.1) :
    B0093.gaussianWeight (polarCoord.symm p) = radialGaussianWeight p.1 := by
  have hs : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    linear_combination p.1 ^ 2 * Real.sin_sq_add_cos_sq p.2
  have h := gaussianWeight_eq_radial (polarCoord.symm p)
  simp only [polarCoord_symm_apply] at h ⊢
  rw [show B0093.gaussianWeight (p.1 * Real.cos p.2, p.1 * Real.sin p.2) =
    B0010.gaussianWeight (p.1 * Real.cos p.2, p.1 * Real.sin p.2) from rfl, h]
  simp only [radiusSq]
  rw [hs, Real.sqrt_sq hp.le]

/-- **The planar function of an `X_G` profile lies in `L²(ℝ², G⁻¹ dy)`**. -/
theorem memGaussL2_angularTwoField {h₂ : ℝ → ℂ} (hm : StronglyMeasurable h₂)
    (hL : MemLp h₂ 2 xGMeasure) : MemGaussL2 (angularTwoField h₂) := by
  set F := angularTwoField h₂ with hF
  have hFs : StronglyMeasurable F := stronglyMeasurable_angularTwoField hm
  have hcm : AEStronglyMeasurable (B0093.conjG F) volume := by
    have e : B0093.conjG F = fun z => (((sqG z)⁻¹ : ℝ) : ℂ) * F z := funext (conjG_apply F)
    rw [e]
    exact ((Complex.continuous_ofReal.comp
      (contDiff_sqG.continuous.inv₀ fun z => (sqG_pos z).ne')).aestronglyMeasurable).mul
        hFs.aestronglyMeasurable
  rw [MemGaussL2, memLp_two_iff_integrable_sq_norm hcm]
  refine ⟨(hcm.norm.pow 2), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => by positivity)]
  simp_rw [norm_conjG_sq]
  rw [← lintegral_comp_polarCoord_symm]
  have hfin := (memLp_iff_lintegral hm.aestronglyMeasurable).1 hL
  set φ : ℝ → ℝ≥0∞ := fun r => ‖h₂ r‖ₑ ^ 2 * ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r)
  have hφm : AEMeasurable φ (volume.restrict (Ioi 0)) := by
    refine (hm.measurable.enorm.pow_const 2).mul ?_ |>.aemeasurable
    refine ENNReal.measurable_ofReal.comp ?_
    unfold radialGaussianWeight radialOmega
    fun_prop
  calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (‖F (polarCoord.symm p)‖ ^ 2 *
          (B0093.gaussianWeight (polarCoord.symm p))⁻¹)
      = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, φ p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
        rw [polarCoord_target]
        refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
        have hr : 0 < p.1 := hp.1
        have hFp : F (polarCoord.symm p) = h₂ p.1 * Complex.exp (2 * Complex.I * (p.2 : ℂ)) := by
          rw [hF, polarCoord_symm_apply]
          exact angularTwoField_polar h₂ hr p.2
        rw [hFp, gaussianWeight_polarCoord_symm p hr, norm_mul, norm_exp_two_mul_I, mul_one,
          smul_eq_mul, mul_one, ← ENNReal.ofReal_mul hr.le]
        simp only [φ]
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = (∫⁻ r in Ioi 0, φ r) * ∫⁻ _ in Ioo (-π) π, (1 : ℝ≥0∞) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_mul hφm aemeasurable_const
    _ < ⊤ := by
        refine ENNReal.mul_lt_top hfin ?_
        rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top

theorem memGaussL2_planar (f : XG) : MemGaussL2 (planar f) :=
  memGaussL2_angularTwoField (Lp.stronglyMeasurable f) (Lp.memLp f)

/-- `∫ |f|² G⁻¹ dy = 2π ‖f‖²_{X_G}` (the pairing of `X_G` omits the factor `2π`, tex line 678). -/
theorem gaussNormSq_angularTwoField {h₂ : ℝ → ℂ} (hL : MemLp h₂ 2 xGMeasure) :
    gaussNormSq (angularTwoField h₂) = 2 * π * ‖hL.toLp h₂‖ ^ 2 := by
  have h := norm_sq_toLp_eq_planar hL
  have hint : ∫ z : ℝ × ℝ, angularTwoField h₂ z * conj (angularTwoField h₂ z) *
      (((B0010.gaussianWeight z)⁻¹ : ℝ) : ℂ) = ((gaussNormSq (angularTwoField h₂) : ℝ) : ℂ) := by
    rw [gaussNormSq, ← integral_complex_ofReal]
    congr 1
    funext z
    rw [Complex.mul_conj']
    push_cast
    rfl
  rw [hint] at h
  have h' : ‖hL.toLp h₂‖ ^ 2 = (2 * π)⁻¹ * gaussNormSq (angularTwoField h₂) := by
    exact_mod_cast h
  rw [h']
  field_simp

/-! ## `U_G⁻¹` of angular-two Schwartz functions -/

/-- `U_G⁻¹ χ ∈ X_G` for `χ ∈ 𝓢(ℝ², ℂ)` (profile `schProf χ r = √G(r) χ(r, 0)`, B0094). -/
def toXG (χ : S2) : XG := (memLp_schProf χ).toLp (schProf χ)

theorem toXG_add (χ ψ : S2) : toXG (χ + ψ) = toXG χ + toXG ψ := toLp_schProf_add χ ψ

theorem toXG_smul (c : ℂ) (χ : S2) : toXG (c • χ) = c • toXG χ := toLp_schProf_smul c χ

theorem toXG_zero : toXG 0 = 0 := by
  have h := toXG_smul 0 0
  rwa [zero_smul, zero_smul] at h

theorem toXG_sum {ι : Type*} (s : Finset ι) (χ : ι → S2) :
    toXG (∑ i ∈ s, χ i) = ∑ i ∈ s, toXG (χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using toXG_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toXG_add, ih]

/-- For `χ` of angular weight two, the planar function of `U_G⁻¹ χ` is `√G χ`. -/
theorem angularTwoField_schProf_eq_gS {χ : S2} (hχ : IsAngularTwo χ) :
    angularTwoField (schProf χ) = ⇑(gS χ) := by
  rw [angularTwoField_schProf hχ]
  funext z
  rw [B0093.conjGInv, gS_apply, Complex.real_smul]
  rfl

/-- `⟪J ψ, J φ⟫_{L²(ℝ²)} = 2π ⟪U_G⁻¹ ψ, U_G⁻¹ φ⟫_{X_G}` for angular-two Schwartz `ψ, φ`. -/
theorem inner_J_eq_toXG {ψ φ : S2} (hψ : IsAngularTwo ψ) (hφ : IsAngularTwo φ) :
    ⟪J ψ, J φ⟫_ℂ = 2 * π * ⟪toXG ψ, toXG φ⟫_ℂ := by
  rw [inner_J, ← pairing_eq_inner, toXG, toXG, pairing_toLp_eq_planar,
    angularTwoField_schProf_eq_gS hφ, angularTwoField_schProf_eq_gS hψ, ← mul_assoc,
    mul_inv_cancel₀ (by simp [Real.pi_ne_zero]), one_mul, pairS]
  congr 1
  funext z
  rw [gS_apply, gS_apply, map_mul]
  simp only [sqGc, Complex.conj_ofReal]
  have hG : B0010.gaussianWeight z = sqG z ^ 2 := (sqG_sq z).symm
  rw [hG]
  have hs : (sqG z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sqG_pos z).ne'
  push_cast
  field_simp

/-- `∫ f conj(U_G η) dy = 2π ⟪U_G⁻¹ η, f⟫_{X_G}` for angular-two Schwartz `η`. -/
theorem integral_planar_mul_conj_conjG (f : XG) {η : S2} (hη : IsAngularTwo η) :
    ∫ z, planar f z * conj (B0093.conjG ⇑η z) = 2 * π * ⟪toXG η, f⟫_ℂ := by
  have e : ∀ z, planar f z * conj (B0093.conjG ⇑η z) =
      angularTwoField (⇑f) z * conj (angularTwoField (schProf η) z) *
        (((B0010.gaussianWeight z)⁻¹ : ℝ) : ℂ) := by
    intro z
    rw [angularTwoField_schProf_eq_gS hη, gS_apply, conjG_apply, planar]
    simp only [map_mul, sqGc, Complex.conj_ofReal]
    have hG : B0010.gaussianWeight z = sqG z ^ 2 := (sqG_sq z).symm
    rw [hG]
    have hs : (sqG z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sqG_pos z).ne'
    push_cast
    field_simp
  simp_rw [e]
  rw [integral_plane_pairing, ← pairing_toLp (Lp.memLp f) (memLp_schProf η), Lp.toLp_coeFn,
    pairing_eq_inner]
  rfl

/-- The difference of the planar function of `f` and `√G χ` lies in `L²(ℝ², G⁻¹ dy)`, with
squared norm `2π ‖f - U_G⁻¹ χ‖²_{X_G}`. -/
theorem planar_sub_gS (f : XG) {χ : S2} (hχ : IsAngularTwo χ) :
    ∃ h : MemGaussL2 (fun z => planar f z - gS χ z),
      ‖h.toLp (B0093.conjG fun z => planar f z - gS χ z)‖ ^ 2 =
        2 * π * ‖f - toXG χ‖ ^ 2 := by
  have hL : MemLp (fun r => (⇑f) r - schProf χ r) 2 xGMeasure := (Lp.memLp f).sub (memLp_schProf χ)
  have hm : StronglyMeasurable (fun r => (⇑f) r - schProf χ r) :=
    (Lp.stronglyMeasurable f).sub (continuous_schProf χ).stronglyMeasurable
  have e : (fun z => planar f z - gS χ z) = angularTwoField (fun r => (⇑f) r - schProf χ r) := by
    funext z
    rw [planar, ← angularTwoField_schProf_eq_gS hχ]
    simp only [angularTwoField]
    ring
  have hG := memGaussL2_angularTwoField hm hL
  rw [← e] at hG
  refine ⟨hG, ?_⟩
  rw [norm_toLp_sq, e, gaussNormSq_angularTwoField hL]
  congr 2
  show ‖((Lp.memLp f).sub (memLp_schProf χ)).toLp (⇑f - schProf χ)‖ = ‖f - toXG χ‖
  rw [MemLp.toLp_sub (Lp.memLp f) (memLp_schProf χ), Lp.toLp_coeFn]
  rfl

end UnforcedLeray.B0121
