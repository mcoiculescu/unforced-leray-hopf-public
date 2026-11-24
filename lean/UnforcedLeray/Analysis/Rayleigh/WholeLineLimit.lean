import UnforcedLeray.Analysis.Rayleigh.H2Compactness
import UnforcedLeray.Analysis.Rayleigh.LimitEquation
import UnforcedLeray.Analysis.Rayleigh.Semicircle

/-!
# The actual nonzero whole-line Gaussian limit from expanding annular modes

The data below retain the concrete continuous field, its L² class, actual
weak first/second derivatives, and the almost-everywhere undivided Rayleigh
equation. The same strict subsequence carries the speed, local-uniform field,
and all three weak L² limits. The speed obeys the true rotating semicircle.

This is an intermediate construction from a normalized sequence of genuine
unstable annular modes. Existence of that input sequence is an explicit
hypothesis, not an axiom or an unconditional Gaussian instability theorem.
Strict positivity of the limiting imaginary speed remains to be proved.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.Rayleigh
open Sturm NonUniqueEuler.Sob

/-- Concrete limiting objects and their proved analytic properties. -/
structure GaussianWholeLineLimit
    (c : ℕ → ℂ) (F : ℕ → ℝ → ℂ) (l r : ℕ → ℝ)
    (hmode : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n)) where
  speed : ℂ
  field : ℝ → ℂ
  fieldClass : ComplexL2
  gradientClass : ComplexL2
  residualClass : ComplexL2
  subsequence : ℕ → ℕ
  subsequence_strict : StrictMono subsequence
  field_continuous : Continuous field
  field_memLp : MemLp field 2 volume
  field_mass_le_one : (∫ t, ‖field t‖ ^ 2) ≤ 1
  field_not_ae_zero : ¬ field =ᵐ[volume] (0 : ℝ → ℂ)
  represents_field : field =ᵐ[volume] (fieldClass : ℝ → ℂ)
  fieldClass_ne_zero : fieldClass ≠ 0
  field_h2 : MemH1On 2 univ field
  fieldClass_h2 : MemH1On 2 univ (fieldClass : ℝ → ℂ)
  fieldClass_weak_first :
    HasWeakDerivOn univ [1] (fieldClass : ℝ → ℂ) (gradientClass : ℝ → ℂ)
  fieldClass_weak_second : HasWeakDerivOn univ [1, 1] (fieldClass : ℝ → ℂ)
    ((residualClass + (4 : ℂ) • fieldClass : ComplexL2) : ℝ → ℂ)
  fieldClass_norm_le_one : ‖fieldClass‖ ≤ 1
  gradientClass_norm_le_two : ‖gradientClass‖ ≤ 2
  residualClass_norm_le_eight : ‖residualClass‖ ≤ 8
  speed_tendsto : Tendsto (fun n => c (subsequence n)) atTop (𝓝 speed)
  speed_im_nonneg : 0 ≤ speed.im
  speed_semicircle : (speed.re - 1 / 2) ^ 2 + speed.im ^ 2 ≤ 1 / 4
  field_tendstoLocallyUniformly : TendstoLocallyUniformly
    (fun n => zeroExtension (l (subsequence n)) (r (subsequence n)) (F (subsequence n)))
    field atTop
  fieldClass_weak_tendsto : WeakL2.WeakTendsto
    (fun n => (hmode (subsequence n)).toShifted.fieldL2) atTop fieldClass
  gradientClass_weak_tendsto : WeakL2.WeakTendsto
    (fun n => (hmode (subsequence n)).toShifted.derivativeL2) atTop gradientClass
  residualClass_weak_tendsto : WeakL2.WeakTendsto
    (fun n => (hmode (subsequence n)).toShifted.residualL2) atTop residualClass
  equation_class_ae : ∀ᵐ t ∂volume,
    ((neutralOmega t : ℂ) - speed) * residualClass t -
      (gaussianRayleighCoefficient t : ℂ) * fieldClass t = 0

namespace GaussianWholeLineLimit
variable {c : ℕ → ℂ} {F : ℕ → ℝ → ℂ} {l r : ℕ → ℝ}
    {hmode : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n)}
    (U : GaussianWholeLineLimit c F l r hmode)

/-- The actual continuous representative satisfies the same almost-everywhere equation. -/
theorem equation_ae : ∀ᵐ t ∂volume,
    ((neutralOmega t : ℂ) - U.speed) * U.residualClass t -
      (gaussianRayleighCoefficient t : ℂ) * U.field t = 0 := by
  filter_upwards [U.equation_class_ae, U.represents_field] with t ht hrep
  rw [hrep]
  exact ht

/-- The explicit gradient class is the continuous field's actual weak derivative. -/
theorem field_weak_first :
    HasWeakDerivOn univ [1] U.field (U.gradientClass : ℝ → ℂ) := by
  apply U.fieldClass_weak_first.congr_ae
  · filter_upwards [U.represents_field] with t ht
    intro _
    exact ht.symm
  · exact Eventually.of_forall fun _ _ => rfl

/-- The explicit second derivative belongs to L² and is identified distributionally. -/
theorem field_weak_second : HasWeakDerivOn univ [1, 1] U.field
    ((U.residualClass + (4 : ℂ) • U.fieldClass : ComplexL2) : ℝ → ℂ) := by
  apply U.fieldClass_weak_second.congr_ae
  · filter_upwards [U.represents_field] with t ht
    intro _
    exact ht.symm
  · exact Eventually.of_forall fun _ _ => rfl

/-- Closed-interval speed bounds follow from the actual limiting semicircle. -/
theorem speed_re_bounds : 0 ≤ U.speed.re ∧ U.speed.re ≤ 1 := by
  have h := U.speed_semicircle
  constructor <;> nlinarith [sq_nonneg U.speed.re, sq_nonneg U.speed.im,
    sq_nonneg (U.speed.re - 1)]

theorem speed_im_le_half : U.speed.im ≤ 1 / 2 := by
  have h := U.speed_semicircle
  nlinarith [sq_nonneg (U.speed.re - 1 / 2)]

/-- The true compactness disk improves from radius two to radius one. -/
theorem speed_norm_le_one : ‖U.speed‖ ≤ 1 := by
  have h := U.speed_semicircle
  have hr := U.speed_re_bounds.2
  have hn : ‖U.speed‖ ^ 2 = U.speed.re ^ 2 + U.speed.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg U.speed]

/-- The actual second derivative class has the uniform norm bound twelve. -/
theorem secondClass_norm_le_twelve :
    ‖U.residualClass + (4 : ℂ) • U.fieldClass‖ ≤ 12 := by
  have hn := norm_add_le U.residualClass ((4 : ℂ) • U.fieldClass)
  norm_num [norm_smul] at hn
  have hf := U.fieldClass_norm_le_one
  have hk := U.residualClass_norm_le_eight
  linarith

end GaussianWholeLineLimit

/-- Construct the full actual limiting object from normalized genuine annular
modes and expanding endpoints. No annular existence premise is suppressed. -/
theorem wholeLineLimit_of_annular_sequence
    (c : ℕ → ℂ) (F : ℕ → ℝ → ℂ) (l r : ℕ → ℝ)
    (hmode : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1)
    (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop) :
    Nonempty (GaussianWholeLineLimit c F l r hmode) := by
  obtain ⟨speed, f, u, g, k, φ, hφ, hfcont, hfmem, hfmass, hfne, hrep, hune,
      hfH2, huH2, hfirst, hsecond, hun, hgn, hkn, hspeed, him, _, hlocal, hwu, hwg, hwk⟩ :=
    exists_nonzero_H2_gaussian_annular_limit c F l r hmode hmass hl hr
  have heq := gaussian_equation_of_weak_limits (fun n => hmode (φ n)) hspeed hwu hwk
  have hre : Tendsto (fun n => (c (φ n)).re) atTop (𝓝 speed.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hspeed
  have himconv : Tendsto (fun n => (c (φ n)).im) atTop (𝓝 speed.im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hspeed
  have hcircle : (speed.re - 1 / 2) ^ 2 + speed.im ^ 2 ≤ 1 / 4 :=
    le_of_tendsto (((hre.sub_const (1 / 2)).pow 2).add (himconv.pow 2))
      (Eventually.of_forall fun n => ((hmode (φ n)).normalized_semicircle (hmass (φ n))).1)
  exact ⟨{
    speed := speed
    field := f
    fieldClass := u
    gradientClass := g
    residualClass := k
    subsequence := φ
    subsequence_strict := hφ
    field_continuous := hfcont
    field_memLp := hfmem
    field_mass_le_one := hfmass
    field_not_ae_zero := hfne
    represents_field := hrep
    fieldClass_ne_zero := hune
    field_h2 := hfH2
    fieldClass_h2 := huH2
    fieldClass_weak_first := hfirst
    fieldClass_weak_second := hsecond
    fieldClass_norm_le_one := hun
    gradientClass_norm_le_two := hgn
    residualClass_norm_le_eight := hkn
    speed_tendsto := hspeed
    speed_im_nonneg := him
    speed_semicircle := hcircle
    field_tendstoLocallyUniformly := hlocal
    fieldClass_weak_tendsto := hwu
    gradientClass_weak_tendsto := hwg
    residualClass_weak_tendsto := hwk
    equation_class_ae := heq
  }⟩

end UnforcedLeray.Rayleigh
