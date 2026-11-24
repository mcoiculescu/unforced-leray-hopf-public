import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsTestConvBound
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsDecayL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Integrability of the Biot-Savart pairing on `ℝ³ × ℝ³` (BSPairIntegrable)

Source `the November 2 reference manuscript` lines 1351-1362.

For continuous compactly supported `A` and `f ∈ L²`, the integrand
`(y,z) ↦ A(y) · (f(z) × K(y-z))` is dominated by `4‖dotL‖ ‖f(z)‖ ‖A(y)‖ ‖K(y-z)‖`.  The `y`-integral
of `‖A(y)‖ ‖K(y-z)‖` is `≤ C (1+‖z‖²)⁻¹` (`BSTestConvBound`), and `‖f‖ (1+‖z‖²)⁻¹ ∈ L¹` by
Cauchy-Schwarz (`BSDecayL2`).  Fubini-Tonelli form `integrable_prod_iff'` then gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- `crossC` is jointly continuous. -/
theorem crossC_continuous' : Continuous (fun p : CVec3 × CVec3 => crossC p.1 p.2) := by
  unfold crossC
  fun_prop

/-- Norm bound for the complex cross product. -/
theorem crossC_norm_le' (a b : CVec3) : ‖crossC a b‖ ≤ 4 * ‖a‖ * ‖b‖ := by
  have ha : ∀ i, ‖a i‖ ≤ ‖a‖ := fun i => PiLp.norm_apply_le a i
  have hb : ∀ i, ‖b i‖ ≤ ‖b‖ := fun i => PiLp.norm_apply_le b i
  have hab : 0 ≤ ‖a‖ * ‖b‖ := by positivity
  have key : ∀ p q r s : ℂ, ‖p‖ ≤ ‖a‖ → ‖q‖ ≤ ‖b‖ → ‖r‖ ≤ ‖a‖ → ‖s‖ ≤ ‖b‖ →
      ‖p * q - r * s‖ ≤ 2 * (‖a‖ * ‖b‖) := by
    intro p q r s hp hq hr hs
    calc ‖p * q - r * s‖ ≤ ‖p * q‖ + ‖r * s‖ := norm_sub_le _ _
      _ = ‖p‖ * ‖q‖ + ‖r‖ * ‖s‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ := by
          have h1 : ‖p‖ * ‖q‖ ≤ ‖a‖ * ‖b‖ :=
            mul_le_mul hp hq (norm_nonneg _) (norm_nonneg _)
          have h2 : ‖r‖ * ‖s‖ ≤ ‖a‖ * ‖b‖ :=
            mul_le_mul hr hs (norm_nonneg _) (norm_nonneg _)
          linarith
      _ = 2 * (‖a‖ * ‖b‖) := by ring
  have h0 := key (a 1) (b 2) (a 2) (b 1) (ha 1) (hb 2) (ha 2) (hb 1)
  have h1 := key (a 2) (b 0) (a 0) (b 2) (ha 2) (hb 0) (ha 0) (hb 2)
  have h2 := key (a 0) (b 1) (a 1) (b 0) (ha 0) (hb 1) (ha 1) (hb 0)
  have c0 : (crossC a b) 0 = a 1 * b 2 - a 2 * b 1 := by simp [crossC]
  have c1 : (crossC a b) 1 = a 2 * b 0 - a 0 * b 2 := by simp [crossC]
  have c2 : (crossC a b) 2 = a 0 * b 1 - a 1 * b 0 := by simp [crossC]
  have e0 : ‖(crossC a b) 0‖ ^ 2 ≤ (2 * (‖a‖ * ‖b‖)) ^ 2 := by
    rw [c0]; exact pow_le_pow_left₀ (norm_nonneg _) h0 2
  have e1 : ‖(crossC a b) 1‖ ^ 2 ≤ (2 * (‖a‖ * ‖b‖)) ^ 2 := by
    rw [c1]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e2 : ‖(crossC a b) 2‖ ^ 2 ≤ (2 * (‖a‖ * ‖b‖)) ^ 2 := by
    rw [c2]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_three]
  nlinarith [e0, e1, e2, hab]

/-- Measurability of the Biot-Savart kernel. -/
theorem bsKernel_measurable : Measurable bsKernel := by
  unfold bsKernel
  fun_prop

/-- The pairing integrand is dominated pointwise. -/
theorem bsPair_pointwise (A : Space → CVec3) (f : Space → CVec3) (y z : Space) :
    ‖dotL (A y) (crossC (f z) (bsKernel (y - z)))‖ ≤
      (4 * ‖dotL‖ * ‖f z‖) * (‖A y‖ * ‖bsKernel (y - z)‖) := by
  calc ‖dotL (A y) (crossC (f z) (bsKernel (y - z)))‖
      ≤ ‖dotL‖ * ‖A y‖ * ‖crossC (f z) (bsKernel (y - z))‖ :=
        ContinuousLinearMap.le_opNorm₂ dotL (A y) _
    _ ≤ ‖dotL‖ * ‖A y‖ * (4 * ‖f z‖ * ‖bsKernel (y - z)‖) := by
        gcongr
        exact crossC_norm_le' _ _
    _ = (4 * ‖dotL‖ * ‖f z‖) * (‖A y‖ * ‖bsKernel (y - z)‖) := by ring

/-- The one-variable decay bound `‖f‖ (1+|z|²)⁻¹ ∈ L¹`. -/
theorem bsDecayMul_integrable (f : Space → CVec3) (hf : MemLp f 2 volume) :
    Integrable (fun z : Space => ‖f z‖ * (1 + ‖z‖ ^ 2)⁻¹) volume := by
  have h1 : MemLp (fun z : Space => ‖f z‖) 2 volume := hf.norm
  have h2 : MemLp (fun z : Space => (1 + ‖z‖ ^ 2)⁻¹) 2 volume := bsDecayL2
  exact h1.integrable_mul h2

/-- Joint measurability of the pairing integrand. -/
theorem bsPair_aesm (A : Space → CVec3) (hA : Continuous A) (f : Space → CVec3)
    (hf : MemLp f 2 volume) :
    AEStronglyMeasurable
      (fun p : Space × Space => dotL (A p.1) (crossC (f p.2) (bsKernel (p.1 - p.2))))
      (volume.prod volume) := by
  have hKp : Measurable (fun p : Space × Space => bsKernel (p.1 - p.2)) :=
    bsKernel_measurable.comp (measurable_fst.sub measurable_snd)
  have hfp : AEStronglyMeasurable (fun p : Space × Space => f p.2) (volume.prod volume) :=
    hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hcp : AEStronglyMeasurable
      (fun p : Space × Space => crossC (f p.2) (bsKernel (p.1 - p.2))) (volume.prod volume) :=
    crossC_continuous'.comp_aestronglyMeasurable₂ (g := fun a b : CVec3 => crossC a b) hfp
      hKp.aestronglyMeasurable
  have hAp : AEStronglyMeasurable (fun p : Space × Space => A p.1) (volume.prod volume) :=
    (hA.measurable.comp measurable_fst).aestronglyMeasurable
  have hdot : Continuous (fun p : CVec3 × CVec3 => dotL p.1 p.2) := dotL.continuous₂
  exact hdot.comp_aestronglyMeasurable₂ (g := fun a b : CVec3 => dotL a b) hAp hcp

/-- Each `y`-section of the pairing integrand is integrable. -/
theorem bsSection_integrable (A : Space → CVec3) (hA : Continuous A)
    (hAint : ∀ z : Space, Integrable (fun y : Space => ‖A y‖ * ‖bsKernel (y - z)‖) volume)
    (f : Space → CVec3) (z : Space) :
    Integrable (fun y : Space => dotL (A y) (crossC (f z) (bsKernel (y - z)))) volume := by
  have hcont : Continuous (fun v : CVec3 => crossC (f z) v) :=
    crossC_continuous'.comp (continuous_const.prodMk continuous_id)
  have hcz : Measurable (fun y : Space => crossC (f z) (bsKernel (y - z))) :=
    hcont.measurable.comp (bsKernel_measurable.comp (measurable_id.sub measurable_const))
  have hdot : Continuous (fun p : CVec3 × CVec3 => dotL p.1 p.2) := dotL.continuous₂
  have hmeas : AEStronglyMeasurable
      (fun y : Space => dotL (A y) (crossC (f z) (bsKernel (y - z)))) volume :=
    hdot.comp_aestronglyMeasurable₂ (g := fun a b : CVec3 => dotL a b) hA.aestronglyMeasurable
      hcz.aestronglyMeasurable
  refine Integrable.mono' ((hAint z).const_mul (4 * ‖dotL‖ * ‖f z‖)) hmeas ?_
  exact Filter.Eventually.of_forall (fun y => bsPair_pointwise A f y z)

/-- The convolution bound for the norm weight `‖A‖` (from `BSTestConvBound`). -/
theorem bsWeightConv (A : Space → CVec3) (hA : Continuous A) (hAc : HasCompactSupport A) :
    ∃ C : ℝ, ∀ z : Space,
      Integrable (fun y : Space => ‖A y‖ * ‖bsKernel (y - z)‖) volume ∧
        ∫ y : Space, ‖A y‖ * ‖bsKernel (y - z)‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹ := by
  have hnr : ∀ y : Space, ‖((‖A y‖ : ℝ) : ℂ)‖ = ‖A y‖ := fun y => by simp
  have hAn : Continuous (fun y : Space => ((‖A y‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hA.norm
  have hAns : HasCompactSupport (fun y : Space => ((‖A y‖ : ℝ) : ℂ)) := by
    have h1 : HasCompactSupport (fun y : Space => ‖A y‖) :=
      hAc.comp_left (g := fun v : CVec3 => ‖v‖) norm_zero
    exact h1.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  obtain ⟨C, hC⟩ := bsTestConvBound (fun y : Space => ((‖A y‖ : ℝ) : ℂ)) hAn hAns
  refine ⟨C, fun z => ?_⟩
  have h := hC z
  simp only [hnr] at h
  exact h

/-- Outer measurability of the `y`-integrated norm. -/
theorem bsPair_outer_meas (A : Space → CVec3) (hA : Continuous A) (f : Space → CVec3)
    (hF : AEStronglyMeasurable
      (fun p : Space × Space => dotL (A p.1) (crossC (f p.2) (bsKernel (p.1 - p.2))))
      (volume.prod volume)) :
    AEStronglyMeasurable
      (fun z : Space => ∫ x : Space, ‖dotL (A x) (crossC (f z) (bsKernel (x - z)))‖) volume := by
  exact (hF.norm.prod_swap).integral_prod_right'

/-- Pointwise `z`-bound for the `y`-integrated norm. -/
theorem bsPair_outer_bound (A : Space → CVec3) (f : Space → CVec3) (C : ℝ) (z : Space)
    (hint_y : Integrable (fun y : Space => ‖A y‖ * ‖bsKernel (y - z)‖) volume)
    (hconv : ∫ y : Space, ‖A y‖ * ‖bsKernel (y - z)‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) :
    ‖∫ x : Space, ‖dotL (A x) (crossC (f z) (bsKernel (x - z)))‖‖
      ≤ (4 * ‖dotL‖ * C) * (‖f z‖ * (1 + ‖z‖ ^ 2)⁻¹) := by
  have hnn : 0 ≤ ∫ x : Space, ‖dotL (A x) (crossC (f z) (bsKernel (x - z)))‖ :=
    integral_nonneg (fun x => norm_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  have hle : ∫ x : Space, ‖dotL (A x) (crossC (f z) (bsKernel (x - z)))‖
      ≤ ∫ x : Space, (4 * ‖dotL‖ * ‖f z‖) * (‖A x‖ * ‖bsKernel (x - z)‖) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg _))
      (hint_y.const_mul _) (Filter.Eventually.of_forall (fun x => bsPair_pointwise A f x z))
  rw [integral_const_mul] at hle
  have hfz : 0 ≤ 4 * ‖dotL‖ * ‖f z‖ := by positivity
  calc ∫ x : Space, ‖dotL (A x) (crossC (f z) (bsKernel (x - z)))‖
      ≤ (4 * ‖dotL‖ * ‖f z‖) * ∫ x : Space, ‖A x‖ * ‖bsKernel (x - z)‖ := hle
    _ ≤ (4 * ‖dotL‖ * ‖f z‖) * (C * (1 + ‖z‖ ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hconv hfz
    _ = (4 * ‖dotL‖ * C) * (‖f z‖ * (1 + ‖z‖ ^ 2)⁻¹) := by ring

/-- Core of the pairing integrability: Tonelli in `z` with the `y`-integral bounded. -/
theorem bsPair_core (A : Space → CVec3) (hA : Continuous A) (f : Space → CVec3)
    (hf : MemLp f 2 volume) (C : ℝ)
    (hint_y : ∀ z : Space, Integrable (fun y : Space => ‖A y‖ * ‖bsKernel (y - z)‖) volume)
    (hconv : ∀ z : Space, ∫ y : Space, ‖A y‖ * ‖bsKernel (y - z)‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) :
    Integrable (fun p : Space × Space => dotL (A p.1) (crossC (f p.2) (bsKernel (p.1 - p.2))))
      (volume.prod volume) := by
  have hF := bsPair_aesm A hA f hf
  have hdec := bsDecayMul_integrable f hf
  have hsec : ∀ z : Space,
      Integrable (fun x : Space => dotL (A x) (crossC (f z) (bsKernel (x - z)))) volume :=
    fun z => bsSection_integrable A hA hint_y f z
  have hgm := bsPair_outer_meas A hA f hF
  have hb : ∀ z : Space, ‖∫ x : Space, ‖dotL (A x) (crossC (f z) (bsKernel (x - z)))‖‖
      ≤ (4 * ‖dotL‖ * C) * (‖f z‖ * (1 + ‖z‖ ^ 2)⁻¹) :=
    fun z => bsPair_outer_bound A f C z (hint_y z) (hconv z)
  exact (integrable_prod_iff' hF).2
    ⟨Filter.Eventually.of_forall hsec,
      Integrable.mono' (hdec.const_mul (4 * ‖dotL‖ * C)) hgm (Filter.Eventually.of_forall hb)⟩

theorem bsPairIntegrable : BSPairIntegrable := by
  intro A hA hAc f hf
  obtain ⟨C, hC⟩ := bsWeightConv A hA hAc
  exact bsPair_core A hA f hf C (fun z => (hC z).1) (fun z => (hC z).2)

end UnforcedLeray.Short.PartIIIb.Concrete
