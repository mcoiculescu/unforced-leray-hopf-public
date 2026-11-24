import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace

/-- Pairing against a fixed dual field is continuous under actual `L^p` convergence, by the
bilinear Holder estimate and the `L^1` norm of the product. -/
theorem tendsto_integral_dotL_of_eLpNorm
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {F : α → CVec3} {G : α → CVec3} {Fseq : ℕ → α → CVec3}
    (hF : MemLp F p μ) (hG : MemLp G q μ)
    (hseq : ∀ k, MemLp (Fseq k) p μ)
    (hconv : Tendsto (fun k => eLpNorm (Fseq k - F) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, dotL (Fseq k x) (G x) ∂μ)
      atTop (𝓝 (∫ x, dotL (F x) (G x) ∂μ)) := by
  let E : ℕ → α → CVec3 := fun k x => Fseq k x - F x
  let I : (α → CVec3) → ℂ := fun H => ∫ x, dotL (H x) (G x) ∂μ
  have hE (k : ℕ) : MemLp (E k) p μ := by
    exact (hseq k).sub hF
  have hInt (H : α → CVec3) (hH : MemLp H p μ) :
      Integrable (fun x => dotL (H x) (G x)) μ :=
    integrable_dotL_of_memLp_holder hH hG
  let C : ℝ≥0∞ := ‖dotL‖₊ * eLpNorm G q μ
  have hCfinite : C ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.coe_ne_top
    · exact ne_of_lt hG.eLpNorm_lt_top
  have herror (k : ℕ) :
      ‖I (E k)‖ ≤
        (C * eLpNorm (E k) p μ).toReal := by
    have hI : Integrable (fun x => dotL (E k x) (G x)) μ := hInt (E k) (hE k)
    have hHolder := eLpNorm_dotL_bilinear_le (p := p) (q := q)
      (hE k).aestronglyMeasurable hG.aestronglyMeasurable
    have hfinite :
        C * eLpNorm (E k) p μ ≠ ⊤ :=
      ENNReal.mul_ne_top hCfinite (ne_of_lt (hE k).eLpNorm_lt_top)
    calc
      ‖I (E k)‖ ≤
          (∫⁻ x, ENNReal.ofReal ‖dotL (E k x) (G x)‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
      _ = (eLpNorm (fun x => dotL (E k x) (G x)) 1 μ).toReal := by
        congr 1
        rw [eLpNorm_one_eq_lintegral_enorm]
        apply lintegral_congr_ae
        filter_upwards with x
        simp
      _ ≤ (C * eLpNorm (E k) p μ).toReal := by
        apply ENNReal.toReal_mono hfinite
        calc
          eLpNorm (fun x => dotL (E k x) (G x)) 1 μ ≤
              ‖dotL‖₊ * (eLpNorm (E k) p μ * eLpNorm G q μ) := hHolder
          _ = C * eLpNorm (E k) p μ := by
            simp only [C]
            ac_rfl
  have hEreal : Tendsto (fun k => (eLpNorm (E k) p μ).toReal)
      atTop (𝓝 0) := by
    exact (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hconv
  have hsmallReal : Tendsto
      (fun k => (C * eLpNorm (E k) p μ).toReal)
      atTop (𝓝 0) := by
    have hmul : Tendsto (fun k => C.toReal * (eLpNorm (E k) p μ).toReal)
        atTop (𝓝 0) := by
      simpa [mul_comm] using hEreal.const_mul C.toReal
    exact Tendsto.congr (fun k => ENNReal.toReal_mul.symm) hmul
  have hnorm : Tendsto (fun k => ‖I (E k)‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => norm_nonneg _) herror hsmallReal
  have hsub (k : ℕ) :
      (∫ x, dotL (Fseq k x) (G x) ∂μ) - (∫ x, dotL (F x) (G x) ∂μ) = I (E k) := by
    rw [← integral_sub (hInt (Fseq k) (hseq k)) (hInt F hF)]
    congr 1
    funext x
    simp [I, E, dotL_apply, sub_mul]
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa only [hsub, I] using hnorm

#print axioms tendsto_integral_dotL_of_eLpNorm

end UnforcedLeray.Cons.C03.Concrete
