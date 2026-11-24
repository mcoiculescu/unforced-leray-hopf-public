import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.WeakLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Helpers for `PPLShift` / `PPLNorm`: Hölder pairing of `ℂ²`-valued functions

Source of record: `the November 2 reference manuscript` lines 1933-1935.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

lemma cs_pair (a b : CMerid) : ‖∑ i : Fin 2, a i * b i‖ ≤ ‖a‖ * ‖b‖ := by
  have h : ∑ i : Fin 2, a i * b i = inner ℂ (conjVec b) a := by
    simp [PiLp.inner_apply, conjVec_apply, mul_comm]
  rw [h]
  simpa [norm_conjVec, mul_comm] using norm_inner_le_norm (𝕜 := ℂ) (conjVec b) a

lemma aesm_pair {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → CMerid}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun z => ∑ i : Fin 2, f z i * g z i) μ := by
  have hp : ∀ (i : Fin 2) (h : α → CMerid), AEStronglyMeasurable h μ →
      AEStronglyMeasurable (fun z => h z i) μ := fun i h hh =>
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous).comp_aestronglyMeasurable hh
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hp i f hf).mul (hp i g hg)

theorem eLpNorm_pair_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}
    [ENNReal.HolderTriple p q 1] {f g : α → CMerid}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun z => ∑ i : Fin 2, f z i * g z i) 1 μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (r := 1) (p := p) (q := q) hf hg
    (fun a b : CMerid => ∑ i : Fin 2, a i * b i) 1
    (ae_of_all _ fun x => by simpa using cs_pair (f x) (g x))
  simpa using this

theorem enorm_integral_pair_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}
    [ENNReal.HolderTriple p q 1] {f g : α → CMerid}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ‖∫ z, ∑ i : Fin 2, f z i * g z i ∂μ‖ₑ ≤ eLpNorm f p μ * eLpNorm g q μ :=
  (enorm_integral_le_lintegral_enorm _).trans
    (by rw [← eLpNorm_one_eq_lintegral_enorm]; exact eLpNorm_pair_le hf hg)

instance holderTriple_two_two_one : ENNReal.HolderTriple 2 2 1 :=
  ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩

theorem integrable_pair {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → CMerid}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => ∑ i : Fin 2, f z i * g z i) μ := by
  rw [← memLp_one_iff_integrable]
  refine ⟨aesm_pair hf.1 hg.1, ?_⟩
  exact lt_of_le_of_lt (eLpNorm_pair_le (p := 2) (q := 2) hf.1 hg.1)
    (ENNReal.mul_lt_top hf.2 hg.2)

end UnforcedLeray.Short.IIb
