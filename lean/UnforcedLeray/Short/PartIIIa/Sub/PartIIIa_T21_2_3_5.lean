import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3

/-!
# Part III-a, `PartIII-a:T21/2/3/5`: `NegNormPairing`, decomposed

Source: `the November 2 reference manuscript` (SP) lines 2823-2826 (definition of
the weak-source norm as a dual norm).  The only analytic input is that a function with weak
cell derivatives (tested against the cylinder tests) is a.e.-strongly measurable
(`WeakCellMeas`): this is needed so that `h1Norm = 0` forces `Φ = 0` a.e.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **Measurability of weakly differentiable functions** (SP 2823-2826): if `φ` has a weak
cell derivative `g` in direction `j` (both pairings integrable against all cylinder tests) then
`φ` is a.e.-strongly measurable on the cell.  (Take tests `ψ = x_j · bump`, so that
`∂_j ψ = 1` on the bump's core, and use a countable cover of the cell.) -/
def WeakCellMeas : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (φ g : ℝ × ℝ → ℂ), HasWeakCellDerivC c j φ g →
    AEStronglyMeasurable φ (volume.restrict (B0579.cell c))

lemma hasWeakCellDerivC_smul (c : ℝ) (j : Fin 2) (φ g : ℝ × ℝ → ℂ) (k : ℂ)
    (h : HasWeakCellDerivC c j φ g) : HasWeakCellDerivC c j (fun x => k * φ x) (fun x => k * g x) := by
  obtain ⟨hi, he⟩ := h
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · have := (hi ψ hψ).1.const_mul k
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_assoc]
  · have := (hi ψ hψ).2.const_mul k
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_assoc]
  · have h1 := he ψ hψ
    have e1 : ∫ x in B0579.cell c, k * φ x * (B0579.pd j ψ x : ℂ)
        = k * ∫ x in B0579.cell c, φ x * (B0579.pd j ψ x : ℂ) := by
      rw [← integral_const_mul]; simp only [mul_assoc]
    have e2 : ∫ x in B0579.cell c, k * g x * (ψ x : ℂ)
        = k * ∫ x in B0579.cell c, g x * (ψ x : ℂ) := by
      rw [← integral_const_mul]; simp only [mul_assoc]
    rw [e1, e2, h1]; ring

lemma xNorm_const_mul (c m : ℝ) (k : ℂ) (f : ℝ × ℝ → ℂ) :
    xNorm c m (fun x => k * f x) = ‖k‖ₑ * xNorm c m f := by
  unfold xNorm
  have := eLpNorm_const_smul (p := 2) (μ := B0579.cellMeasure c m) k f
  simpa [Pi.smul_def, smul_eq_mul] using this

lemma h1Norm_const_mul (c m : ℝ) (k : ℂ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) :
    h1Norm c m (fun x => k * φ x) (fun j x => k * g j x) = ‖k‖ₑ * h1Norm c m φ g := by
  unfold h1Norm
  simp only [xNorm_const_mul, mul_pow]
  rw [← Finset.mul_sum, ← mul_add, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The `negNorm` pairing bound from measurability of weakly differentiable functions. -/
theorem negNormPairing_of (hM : WeakCellMeas) : NegNormPairing := by
  intro c m F Φ g hg hN
  set N := h1Norm c m Φ g with hNdef
  by_cases h0 : N = 0
  · have hx : xNorm c (-m) Φ = 0 := by
      have h1 : xNorm c (-m) Φ ^ 2 + ∑ j, xNorm c (-m) (g j) ^ 2 = 0 := by
        have := h0
        unfold h1Norm at this
        rcases ENNReal.rpow_eq_zero_iff.mp this with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · norm_num at h
      have h2 : xNorm c (-m) Φ ^ 2 = 0 := by
        rcases add_eq_zero.mp h1 with ⟨a, _⟩; exact a
      exact pow_eq_zero_iff (by norm_num) |>.mp h2
    have hm : AEStronglyMeasurable Φ (B0579.cellMeasure c (-m)) :=
      (hM c 0 Φ (g 0) (hg 0)).mono_ac (B0579.cellMeasure_ac c (-m))
    have hz : Φ =ᵐ[B0579.cellMeasure c (-m)] 0 := by
      have := (eLpNorm_eq_zero_iff hm (by norm_num : (2:ℝ≥0∞) ≠ 0)).mp hx
      exact this
    have hz' : Φ =ᵐ[volume.restrict (B0579.cell c)] 0 := (B0579.ac_cellMeasure c (-m)).ae_le hz
    have : ∫ x in B0579.cell c, F x * Φ x = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hz'] with x hx
      simp [hx]
    rw [this]; simp
  · have hpos : 0 < N.toReal := ENNReal.toReal_pos h0 hN
    set r := N.toReal with hr
    have hk : ((r⁻¹ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (inv_pos.mpr hpos).ne'
    have hN' : h1Norm c m (fun x => ((r⁻¹ : ℝ) : ℂ) * Φ x) (fun j x => ((r⁻¹ : ℝ) : ℂ) * g j x)
        ≤ 1 := by
      rw [h1Norm_const_mul]
      have : ‖((r⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal r⁻¹ := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      rw [this, ← hNdef, ← ENNReal.ofReal_toReal hN, ← hr, ← ENNReal.ofReal_mul (inv_pos.mpr hpos).le,
        inv_mul_cancel₀ hpos.ne']
      simp
    have hle : (⨆ (_ : ∀ j, HasWeakCellDerivC c j (fun x => ((r⁻¹ : ℝ) : ℂ) * Φ x)
          (fun x => ((r⁻¹ : ℝ) : ℂ) * g j x))
        (_ : h1Norm c m (fun x => ((r⁻¹ : ℝ) : ℂ) * Φ x) (fun j x => ((r⁻¹ : ℝ) : ℂ) * g j x) ≤ 1),
        ENNReal.ofReal ‖∫ x in B0579.cell c, F x * (((r⁻¹ : ℝ) : ℂ) * Φ x)‖) ≤ negNorm c m F :=
      le_iSup₂ (f := fun (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) =>
        ⨆ (_ : ∀ j, HasWeakCellDerivC c j φ (g j)) (_ : h1Norm c m φ g ≤ 1),
          ENNReal.ofReal ‖∫ x in B0579.cell c, F x * φ x‖)
        (fun x => ((r⁻¹ : ℝ) : ℂ) * Φ x) (fun j x => ((r⁻¹ : ℝ) : ℂ) * g j x)
    have hle2 : ENNReal.ofReal ‖∫ x in B0579.cell c, F x * (((r⁻¹ : ℝ) : ℂ) * Φ x)‖
        ≤ negNorm c m F :=
      le_trans (le_iSup₂_of_le (fun j => hasWeakCellDerivC_smul c j Φ (g j) _ (hg j)) hN' le_rfl) hle
    have e : ∫ x in B0579.cell c, F x * (((r⁻¹ : ℝ) : ℂ) * Φ x)
        = ((r⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell c, F x * Φ x := by
      rw [← integral_const_mul]; congr 1; ext x; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      ENNReal.ofReal_mul (inv_pos.mpr hpos).le] at hle2
    have h3 : ENNReal.ofReal ‖∫ x in B0579.cell c, F x * Φ x‖
        = ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖∫ x in B0579.cell c, F x * Φ x‖) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne']; simp
    have hN2 : ENNReal.ofReal r = N := ENNReal.ofReal_toReal hN
    rw [h3, hN2, mul_comm (negNorm c m F)]
    exact mul_le_mul_right hle2 N

end UnforcedLeray.Short.IIIa
