import UnforcedLeray.Analysis.Sturm.CompactL2
import NonUniqueEuler.H.Infra.SobolevOneD.Energy.Conv
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# L² translations and continuity of the actual Green convolutions

Reflection followed by translation acts continuously on Lebesgue L².
Pairing translated real kernels with an L² input therefore yields continuous
pointwise convolutions, including the signed exponential derivative kernel.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Sturm

open NonUniqueEuler.Sob.EnergyAux

/-- The L² class represented by `y ↦ f (x - y)`. -/
def reflectedTranslateL2 (x : ℝ) (f : ComplexL2) : ComplexL2 :=
  Lp.compMeasurePreserving (fun y => x - y) (volume.measurePreserving_sub_left x) f

theorem continuous_reflectedTranslateL2 (f : ComplexL2) :
    Continuous (fun x => reflectedTranslateL2 x f) := by
  let t : C(ℝ × ℝ, ℝ) := ⟨fun p => p.1 - p.2, continuous_fst.sub continuous_snd⟩
  exact (continuous_const : Continuous (fun _ : ℝ => f)).compMeasurePreservingLp
    t.curry.continuous (fun x => volume.measurePreserving_sub_left x) (by norm_num)

theorem norm_reflectedTranslateL2 (x : ℝ) (f : ComplexL2) :
    ‖reflectedTranslateL2 x f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (volume.measurePreserving_sub_left x)

theorem coeFn_reflectedTranslateL2_toLp (x : ℝ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    reflectedTranslateL2 x (hg.toLp g) =ᵐ[volume] fun y => g (x - y) :=
  (hg.comp_measurePreserving (volume.measurePreserving_sub_left x)).coeFn_toLp

theorem memLp_k0_complex {L : ℝ} (hL : 0 < L) :
    MemLp (fun y : ℝ => (k0 L y : ℂ)) 2 (volume : Measure ℝ) := by
  refine memLp_two_of_le_k0 hL
    (Complex.continuous_ofReal.comp (continuous_k0 L)).aestronglyMeasurable
    (C := 1) (a := 0) ?_
  intro y
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (k0_pos L y),
    sub_zero, one_mul, le_refl]

theorem memLp_k1_complex {L : ℝ} (hL : 0 < L) :
    MemLp (fun y : ℝ => (k1 L y : ℂ)) 2 (volume : Measure ℝ) := by
  refine memLp_two_of_le_k0 hL
    (Complex.measurable_ofReal.comp (measurable_k1 L)).aestronglyMeasurable
    (C := 1) (a := 0) ?_
  intro y
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_k1, sub_zero, one_mul, le_refl]

theorem memLp_k0_shift_complex {L : ℝ} (hL : 0 < L) (x : ℝ) :
    MemLp (fun y : ℝ => (k0 L (x - y) : ℂ)) 2 (volume : Measure ℝ) :=
  (memLp_k0_complex hL).comp_measurePreserving (volume.measurePreserving_sub_left x)

theorem memLp_k1_shift_complex {L : ℝ} (hL : 0 < L) (x : ℝ) :
    MemLp (fun y : ℝ => (k1 L (x - y) : ℂ)) 2 (volume : Measure ℝ) :=
  (memLp_k1_complex hL).comp_measurePreserving (volume.measurePreserving_sub_left x)

theorem memLp_k0_shift_real {L : ℝ} (hL : 0 < L) (x : ℝ) :
    MemLp (fun y : ℝ => k0 L (x - y)) 2 (volume : Measure ℝ) := by
  have h := (memLp_k0_shift_complex hL x).re
  change MemLp (fun y : ℝ => (k0 L (x - y) : ℂ).re) 2 (volume : Measure ℝ) at h
  simpa only [Complex.ofReal_re] using h

theorem memLp_k1_shift_real {L : ℝ} (hL : 0 < L) (x : ℝ) :
    MemLp (fun y : ℝ => k1 L (x - y)) 2 (volume : Measure ℝ) := by
  have h := (memLp_k1_shift_complex hL x).re
  change MemLp (fun y : ℝ => (k1 L (x - y) : ℂ).re) 2 (volume : Measure ℝ) at h
  simpa only [Complex.ofReal_re] using h

/-- The actual real-kernel convolution is a Hilbert-space pairing of L² classes. -/
theorem inner_reflectedTranslateL2_realKernel {K : ℝ → ℝ}
    (hK : MemLp (fun y => (K y : ℂ)) 2 (volume : Measure ℝ))
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) (x : ℝ) :
    ⟪reflectedTranslateL2 x (hK.toLp (fun y => (K y : ℂ))), hf.toLp f⟫_ℂ =
      ∫ y, (K (x - y) : ℂ) * f y := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_reflectedTranslateL2_toLp x hK, hf.coeFn_toLp] with y hk hy
  simp only [RCLike.inner_apply, hk, hy, Complex.conj_ofReal, mul_comm]

theorem continuous_convolution_realKernel {K : ℝ → ℝ}
    (hK : MemLp (fun y => (K y : ℂ)) 2 (volume : Measure ℝ))
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    Continuous (fun x => ∫ y, (K (x - y) : ℂ) * f y) := by
  have hc := (continuous_reflectedTranslateL2 (hK.toLp (fun y => (K y : ℂ)))).inner (𝕜 := ℂ)
    (continuous_const : Continuous (fun _ : ℝ => hf.toLp f))
  simpa only [inner_reflectedTranslateL2_realKernel hK hf] using hc

theorem continuous_psi0_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) : Continuous (psi0 L f) :=
  continuous_convolution_realKernel (memLp_k0_complex hL) hf

theorem continuous_psi1_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) : Continuous (psi1 L f) :=
  continuous_convolution_realKernel (memLp_k1_complex hL) hf

end UnforcedLeray.Sturm
