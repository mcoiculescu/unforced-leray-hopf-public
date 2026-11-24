import UnforcedLeray.Short.PartIIIa.CanonicalTransfer
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4
import UnforcedLeray.Short.PartIIIa.T07_ScalingJaInv
import UnforcedLeray.Units.B0579
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Part III-b, KcEmbed: `J_a⁻¹` preserves central evenness and zero circulation

Source of record: `the November 2 reference manuscript` (SP), eq:ct-embeddings,
lines 3228-3240, and 3176-3184. The map `y ↦ √a • y` sends the cell of width `c/√a` onto the cell
of width `c`, and `J_a⁻¹ g(y) = a² g(√a y)` is even when `g` is.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem jscaleInv_even_zeroCirc (c a : ℝ) (hc : 0 < c) (ha : 0 < a) (g : ℝ × ℝ → ℂ) (he : IIIa.IsCentrallyEven g) (hz : IIIa.HasZeroCirculation c g) : IIIa.IsCentrallyEven (IIIa.JscaleInv a g) ∧ IIIa.HasZeroCirculation (IIIa.cellLen c a) (IIIa.JscaleInv a g) := by
  have he' : ∀ p : ℝ × ℝ, g (-p) = g p := he
  have hz' : IntegrableOn g (UnforcedLeray.B0579.cell c) ∧
      ∫ x in UnforcedLeray.B0579.cell c, g x = 0 := hz
  obtain ⟨hzi, hzc⟩ := hz'
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hR : Real.sqrt a ≠ 0 := hr.ne'
  refine ⟨?_, ?_⟩
  · intro x
    simp only [IIIa.JscaleInv]
    have e : (Real.sqrt a * (-x).1, Real.sqrt a * (-x).2) =
        -(Real.sqrt a * x.1, Real.sqrt a * x.2) := by
      simp [Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, mul_neg]
    rw [e, he']
  · -- the representative of `g` on the cell
    obtain ⟨h, hgh⟩ : ∃ h : ℝ × ℝ → ℂ,
        g =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)] h :=
      ⟨_, (Integrable.aestronglyMeasurable hzi).ae_eq_mk⟩
    have hh : IntegrableOn h (UnforcedLeray.B0579.cell c) := Integrable.congr hzi hgh
    have hae : IIIa.JscaleInv a g =ᵐ[volume.restrict (UnforcedLeray.B0579.cell (IIIa.cellLen c a))]
        IIIa.JscaleInv a h :=
      IIIa.jscale_ae_of_ae c a ha g h hgh
    have hdc : IIIa.cellLen c a * Real.sqrt a = c := by
      unfold IIIa.cellLen
      exact div_mul_cancel₀ c hR
    have hiff : ∀ y : ℝ × ℝ, Real.sqrt a • y ∈ UnforcedLeray.B0579.cell c ↔
        y ∈ UnforcedLeray.B0579.cell (IIIa.cellLen c a) := by
      intro y
      have h1 := IIIa.T07.smul_mem_cell_iff (IIIa.cellLen c a) (Real.sqrt a) hr y
      rwa [hdc] at h1
    have hC : MeasurableSet (UnforcedLeray.B0579.cell c) :=
      UnforcedLeray.B0579.measurableSet_cell c
    have hD : MeasurableSet (UnforcedLeray.B0579.cell (IIIa.cellLen c a)) :=
      UnforcedLeray.B0579.measurableSet_cell _
    have hind : ∀ y : ℝ × ℝ,
        (UnforcedLeray.B0579.cell (IIIa.cellLen c a)).indicator (IIIa.JscaleInv a h) y =
          (UnforcedLeray.B0579.cell c).indicator (fun x => ((a ^ 2 : ℝ) : ℂ) * h x)
            (Real.sqrt a • y) := by
      intro y
      by_cases hy : y ∈ UnforcedLeray.B0579.cell (IIIa.cellLen c a)
      · rw [indicator_of_mem hy, indicator_of_mem ((hiff y).2 hy)]
        simp only [IIIa.JscaleInv, IIIa.T07.sqrt_smul_eq]
      · rw [indicator_of_notMem hy,
          indicator_of_notMem (fun h' => hy ((hiff y).1 h'))]
    have hfun : (UnforcedLeray.B0579.cell (IIIa.cellLen c a)).indicator (IIIa.JscaleInv a h) =
        fun y => (UnforcedLeray.B0579.cell c).indicator
          (fun x => ((a ^ 2 : ℝ) : ℂ) * h x) (Real.sqrt a • y) :=
      funext hind
    have hGint : IntegrableOn (IIIa.JscaleInv a h)
        (UnforcedLeray.B0579.cell (IIIa.cellLen c a)) := by
      rw [← integrable_indicator_iff hD, hfun]
      exact Integrable.comp_smul
        ((integrable_indicator_iff hC).2 (Integrable.const_mul hh ((a ^ 2 : ℝ) : ℂ))) hR
    have hJint : IntegrableOn (IIIa.JscaleInv a g)
        (UnforcedLeray.B0579.cell (IIIa.cellLen c a)) :=
      Integrable.congr hGint hae.symm
    have hIC : ∫ x, (UnforcedLeray.B0579.cell c).indicator
        (fun x => ((a ^ 2 : ℝ) : ℂ) * h x) x = 0 := by
      rw [integral_indicator hC, integral_const_mul, ← integral_congr_ae hgh, hzc, mul_zero]
    have e2 : ∫ x in UnforcedLeray.B0579.cell (IIIa.cellLen c a), IIIa.JscaleInv a g x =
        ∫ x, (UnforcedLeray.B0579.cell c).indicator
          (fun x => ((a ^ 2 : ℝ) : ℂ) * h x) (Real.sqrt a • x) := by
      rw [integral_congr_ae hae, ← integral_indicator hD]
      congr 1
    unfold IIIa.HasZeroCirculation
    refine ⟨hJint, ?_⟩
    rw [e2, Measure.integral_comp_smul, hIC, smul_zero]
