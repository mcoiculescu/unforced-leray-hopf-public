import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont.Holder

/-!
# `PartII-b:T08/3` helper: the Hölder bound `|⟨Φ, u⟩| ≤ K ‖u‖_{Y_r}` (SP 1902-1906)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

theorem holder_abstract (P r : ℝ) (hP : 0 < P) (hr : 1 < r) (g : ℝ × Space → ℝ≥0∞)
    (hg : Measurable g) (u : ℝ × Space → CVec3) (hu : Measurable u) (w : ℝ × Space → ℝ≥0∞)
    (hw : ∀ᵐ z ∂(hSlab P), w z ≤ g z * ‖u z‖ₑ) :
    ∫⁻ z, w z ∂(hSlab P) ≤ (∫⁻ z, g z ^ Real.conjExponent r ∂(hSlab P)) ^
      (1 / Real.conjExponent r) * (ENNReal.ofReal P ^ (1 / r) * phaseLpNorm P r u) := by
  have hr0 : 0 < r := by linarith
  have hpq : (Real.conjExponent r).HolderConjugate r :=
    (Real.HolderConjugate.conjExponent hr).symm
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (hSlab P) hpq hg.aemeasurable
    (hu.enorm).aemeasurable
  have hUr := holder_Ur P r hP hr0 u hu
  refine (lintegral_mono_ae hw).trans (hH.trans (le_of_eq ?_))
  congr 1
  show (∫⁻ z, ‖u z‖ₑ ^ r ∂(hSlab P)) ^ (1 / r) = _
  rw [hUr, ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hr0).le, ← ENNReal.rpow_mul,
    mul_one_div_cancel hr0.ne', ENNReal.rpow_one]

theorem holder_integral (P : ℝ) (hP : 0 < P) (f : ℝ × Space → ℂ) (hf : Measurable f)
    (B : ℝ≥0∞) (hBtop : B ≠ ⊤) (hB : ∫⁻ z, ‖f z‖ₑ ∂(hSlab P) ≤ B) :
    Integrable f (hSlab P) ∧ ‖phaseInt P f‖ ≤ P⁻¹ * B.toReal := by
  have hint : Integrable f (hSlab P) :=
    ⟨hf.aestronglyMeasurable, lt_of_le_of_lt hB hBtop.lt_top⟩
  refine ⟨hint, ?_⟩
  rw [phaseInt_eq_slab hint, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hP.le)]
  have h1 : ‖∫ z, f z ∂(hSlab P)‖ ≤ B.toReal :=
    (norm_integral_le_lintegral_norm f).trans (ENNReal.toReal_mono hBtop
      (le_trans (le_of_eq (by simp only [ofReal_norm])) hB))
  exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hP.le)

theorem holder_measurable_dot (Φ u : ℝ × Space → CVec3) (hΦ : Measurable Φ)
    (hu : Measurable u) : Measurable fun z => dotL (Φ z) (u z) :=
  by
  have h : (fun z => dotL (Φ z) (u z)) = fun z => ∑ i : Fin 3, Φ z i * u z i :=
    funext fun z => dotL_apply _ _
  rw [h]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.measurable.comp hΦ)).mul
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.measurable.comp hu)

theorem holder_ae_pt (P C R : ℝ) (hC0 : 0 ≤ C) (Φ u : ℝ × Space → CVec3)
    (hRsupp : ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0)
    (hCb : ∀ τ ∈ Icc 0 P, ∀ y, ‖Φ (τ, y)‖ ≤ C) :
    ∀ᵐ z ∂(hSlab P), ‖dotL (Φ z) (u z)‖ₑ ≤
      holderF (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C) R z * ‖u z‖ₑ := by
  have hae : ∀ᵐ z ∂(hSlab P), z.1 ∈ Ioc (0 : ℝ) P :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hae] with z hz
  exact holder_pt C R hC0 Φ u hRsupp z (hCb z.1 ⟨hz.1.le, hz.2⟩ z.2)

theorem phase_holder_bound (P r : ℝ) (hP : 0 < P) (hr : 1 < r) (Φ : ℝ × Space → CVec3)
    (hΦ : IsPhaseTest P Φ) :
    ∃ K : ℝ, ∀ u : ℝ × Space → CVec3, Measurable u → phaseLpNorm P r u ≠ ⊤ →
      Integrable (fun z => dotL (Φ z) (u z)) (hSlab P) ∧
        ‖pairF P Φ u‖ ≤ K * (phaseLpNorm P r u).toReal := by
  obtain ⟨C, R, hC0, hR0, hRsupp, hCb⟩ := phaseTest_bound P Φ hΦ
  have hΦm : Measurable Φ := hΦ.smooth.continuous.measurable
  have hr0 : 0 < r := by linarith
  have hp0 : 0 < Real.conjExponent r :=
    ((Real.HolderConjugate.conjExponent hr).symm).pos
  have hFp := holderF_lintegral_lt_top P R (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C)
    (Real.conjExponent r) hp0
  have hAtop := (ENNReal.rpow_lt_top_of_nonneg (one_div_pos.2 hp0).le hFp.ne).ne
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = (∫⁻ z, holderF (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C) R z ^
      Real.conjExponent r ∂(hSlab P)) ^ (1 / Real.conjExponent r) := ⟨_, rfl⟩
  have hAtop' : A ≠ ⊤ := by rw [hA]; exact hAtop
  refine ⟨P⁻¹ * A.toReal * P ^ (1 / r), fun u hu hfin => ?_⟩
  have hB : ∫⁻ z, ‖dotL (Φ z) (u z)‖ₑ ∂(hSlab P) ≤
      A * (ENNReal.ofReal P ^ (1 / r) * phaseLpNorm P r u) := by
    rw [hA]
    exact holder_abstract P r hP hr _ (measurable_holderF _ R) u hu _
      (holder_ae_pt P C R hC0 Φ u hRsupp hCb)
  have hBtop : A * (ENNReal.ofReal P ^ (1 / r) * phaseLpNorm P r u) ≠ ⊤ :=
    ENNReal.mul_ne_top hAtop' (ENNReal.mul_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (one_div_pos.2 hr0).le ENNReal.ofReal_ne_top).ne hfin)
  obtain ⟨hint, hnorm⟩ := holder_integral P hP _ (holder_measurable_dot Φ u hΦm hu) _ hBtop hB
  refine ⟨hint, ?_⟩
  have h2 : (A * (ENNReal.ofReal P ^ (1 / r) * phaseLpNorm P r u)).toReal =
      A.toReal * P ^ (1 / r) * (phaseLpNorm P r u).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hP.le,
      mul_assoc]
  refine hnorm.trans (le_of_eq ?_)
  rw [h2]
  ring

end UnforcedLeray.Short.IIb
