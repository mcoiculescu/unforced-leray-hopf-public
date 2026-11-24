import UnforcedLeray.Short.PartIIb.Sub.T15_2_10
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogAvgConverges.AEMeas

/-!
# Part II-b, task `PartII-b:T15/2/10/1`: a.e. slice integrability

Source: `the November 2 reference manuscript`, lines 1975-1979.
Proves `LogAcSlice` (`Sub/T15_2_10.lean`). Tonelli with translation invariance of `logMeas c`
in the first coordinate gives `∫_x ∫_{uIoc 0 h} ‖G(x.1+σ, x.2)‖² = |h| ‖G‖²  < ∞`, so for a.e. `x`
the slice has finite `L²`, hence `L¹`, norm on the finite-measure set `uIoc 0 h`.
A measurable representative `G'` of `G` is used so that sections are measurable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- `a ≤ 1 + a²` in `ℝ≥0∞`. -/
theorem logAcSlice_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  rcases le_total a 1 with h | h
  · exact h.trans le_self_add
  · exact (le_self_pow₀ h two_ne_zero).trans le_add_self

/-- **Leaf `PartII-b:T15/2/10/1`** (a.e. slice integrability; SP 1975-1979). -/
theorem logAcSlice : UnforcedLeray.Short.IIb.LogAcSlice := by
  intro c G hc hG h
  obtain ⟨G', hG'm, hGG'⟩ : ∃ G' : Coord → ℂ, Measurable G' ∧ G =ᵐ[logMeas c] G' :=
    ⟨hG.1.mk G, hG.1.stronglyMeasurable_mk.measurable, hG.1.ae_eq_mk⟩
  -- finiteness of the global squared norm
  have hK : ∫⁻ y, ‖G' y‖ₑ ^ 2 ∂(logMeas c) < ⊤ := by
    have h1 : ∫⁻ y, ‖G' y‖ₑ ^ 2 ∂(logMeas c) = ∫⁻ y, ‖G y‖ₑ ^ 2 ∂(logMeas c) :=
      lintegral_congr_ae (hGG'.mono fun y hy => by simp only [hy])
    rw [h1, logTC_sq c G]
    exact ENNReal.pow_lt_top hG.eLpNorm_lt_top
  -- a.e. equality of `G` and `G'` along slices
  have hshearQ : Measurable (fun p : ℝ × Coord => (p.2.1 + p.1, p.2.2)) :=
    (measurable_snd.fst.add measurable_fst).prodMk measurable_snd.snd
  have hEq : ∀ᵐ z ∂(volume.prod (logMeas c)),
      G (z.2.1 + z.1, z.2.2) = G' (z.2.1 + z.1, z.2.2) :=
    (logAcAEMeas_qmp c).ae_eq_comp hGG'
  have hEqS : ∀ᵐ w ∂((logMeas c).prod volume),
      G ((Prod.swap w).2.1 + (Prod.swap w).1, (Prod.swap w).2.2) =
        G' ((Prod.swap w).2.1 + (Prod.swap w).1, (Prod.swap w).2.2) :=
    (Measure.measurePreserving_swap (μ := logMeas c) (ν := volume)).quasiMeasurePreserving.ae hEq
  have hAe : ∀ᵐ x ∂(logMeas c), ∀ᵐ σ ∂volume, G (x.1 + σ, x.2) = G' (x.1 + σ, x.2) :=
    (Measure.ae_ae_of_ae_prod hEqS).mono fun x hx => hx.mono fun σ hσ => hσ
  -- Tonelli for the squared norm of the measurable representative
  have hFmm : Measurable (fun p : Coord × ℝ => ‖G' (p.1.1 + p.2, p.1.2)‖ₑ ^ 2) :=
    ((hG'm.comp ((measurable_fst.fst.add measurable_snd).prodMk measurable_fst.snd)).enorm).pow_const 2
  have hinner : ∀ σ : ℝ, ∫⁻ y, ‖G' (y.1 + σ, y.2)‖ₑ ^ 2 ∂(logMeas c) =
      ∫⁻ y, ‖G' y‖ₑ ^ 2 ∂(logMeas c) := fun σ =>
    (logTC_measurePreserving c σ).lintegral_comp (hG'm.enorm.pow_const 2)
  have hTfin : ∫⁻ y, (∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖G' (y.1 + σ, y.2)‖ₑ ^ 2) ∂(logMeas c) < ⊤ := by
    rw [lintegral_lintegral_swap (f := fun (x : Coord) (σ : ℝ) => ‖G' (x.1 + σ, x.2)‖ₑ ^ 2)
      hFmm.aemeasurable]
    simp only [hinner]
    rw [setLIntegral_const, Real.volume_uIoc, sub_zero]
    exact ENNReal.mul_lt_top hK (by simp)
  have hI1 : Measurable (fun y : Coord => ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖G' (y.1 + σ, y.2)‖ₑ ^ 2) :=
    hFmm.lintegral_prod_right'
  have hae : ∀ᵐ y ∂(logMeas c), ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖G' (y.1 + σ, y.2)‖ₑ ^ 2 < ⊤ :=
    ae_lt_top' hI1.aemeasurable hTfin.ne
  filter_upwards [hAe, hae] with x hxeq hxfin
  rw [intervalIntegrable_iff]
  have hcongr : (fun σ : ℝ => G (x.1 + σ, x.2)) =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) h)]
      (fun σ : ℝ => G' (x.1 + σ, x.2)) := ae_restrict_of_ae hxeq
  have hmeasσ : Measurable (fun σ : ℝ => G' (x.1 + σ, x.2)) :=
    hG'm.comp ((measurable_id.const_add x.1).prodMk measurable_const)
  unfold IntegrableOn
  refine Integrable.congr ?_ hcongr.symm
  refine ⟨hmeasσ.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hSfin : volume (Set.uIoc (0 : ℝ) h) < ⊤ := by
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_lt_top
  calc ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖G' (x.1 + σ, x.2)‖ₑ
      ≤ ∫⁻ σ in Set.uIoc (0 : ℝ) h, (1 + ‖G' (x.1 + σ, x.2)‖ₑ ^ 2) :=
        lintegral_mono fun σ => logAcSlice_le_one_add_sq _
    _ = volume (Set.uIoc (0 : ℝ) h) + ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖G' (x.1 + σ, x.2)‖ₑ ^ 2 := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hSfin, hxfin⟩

end UnforcedLeray.Short.IIb
