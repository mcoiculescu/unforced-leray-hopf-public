import NonUniqueEuler.H.Infra.SobolevOneD.Energy.Yukawa

/-!
# The actual free one-dimensional Green operator for arbitrary positive mass

`freeResolvent L f` is convolution with `exp(-L|x|)/(2L)`. This sign gives
`-u'' + L²u = f`. The derivative identities below come from the actual
kernel calculations in the reusable NonUniqueEuler infrastructure. Compactly
supported L² data produce actual L² first and second weak derivatives.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob NonUniqueEuler.Sob.EnergyAux

def freeResolvent (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (((2 * L)⁻¹ : ℝ) : ℂ) * psi0 L f x

def freeResolventDeriv (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(1 / 2 : ℂ) * psi1 L f x

def freeResolventSecond (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (L : ℂ) ^ 2 * freeResolvent L f x - f x

theorem hasDerivAt_freeResolvent {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : Integrable f) (x : ℝ) :
    HasDerivAt (freeResolvent L f) (freeResolventDeriv L f x) x := by
  have h := (hasDerivAt_psi0 hL.le hf x).const_mul ((((2 * L)⁻¹ : ℝ) : ℂ))
  refine h.congr_deriv ?_
  unfold freeResolventDeriv
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  push_cast
  field_simp

theorem continuous_freeResolvent {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : Integrable f) : Continuous (freeResolvent L f) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_freeResolvent hL hf x).continuousAt

theorem integral_freeResolvent_mul_deriv {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : Integrable f) {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ') :
    (∫ x, freeResolvent L f x * φ' x) = - ∫ x, freeResolventDeriv L f x * φ x := by
  unfold freeResolvent freeResolventDeriv
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul, integral_psi0_mul_deriv hL hf hφ]
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  push_cast
  field_simp

theorem integral_freeResolventDeriv_mul_deriv {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : Integrable f) {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ')
    (hfφ : Integrable fun x => f x * φ x)
    (huφ : Integrable fun x => freeResolvent L f x * φ x) :
    (∫ x, freeResolventDeriv L f x * φ' x) =
      - ∫ x, freeResolventSecond L f x * φ x := by
  unfold freeResolventDeriv freeResolventSecond
  simp_rw [sub_mul, mul_assoc]
  rw [integral_const_mul, integral_psi1_mul_deriv hL hf hφ hfφ,
    integral_sub (huφ.const_mul _) hfφ, integral_const_mul]
  unfold freeResolvent
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  push_cast
  field_simp
  ring

section CompactData
variable {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ} (hf : Integrable f) {a b : ℝ}
  (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0)
include hL hf hfab

theorem integrable_freeResolvent : Integrable (freeResolvent L f) := by
  have hp : Integrable (psi0 L f) :=
    integrable_of_le_k0 hL (continuous_psi0 hL.le hf).aestronglyMeasurable
      (norm_psi0_le hL.le hf hfab)
  exact hp.const_mul _

theorem integrable_freeResolventDeriv : Integrable (freeResolventDeriv L f) := by
  have hp : Integrable (psi1 L f) :=
    integrable_of_le_k0 hL (aestronglyMeasurable_psi1 L hf) (norm_psi1_le hL.le hf hfab)
  exact hp.const_mul _

theorem memLp_freeResolvent : MemLp (freeResolvent L f) 2 := by
  have hp : MemLp (psi0 L f) 2 :=
    memLp_two_of_le_k0 hL (continuous_psi0 hL.le hf).aestronglyMeasurable
      (norm_psi0_le hL.le hf hfab)
  exact hp.const_mul _

theorem memLp_freeResolventDeriv : MemLp (freeResolventDeriv L f) 2 := by
  have hp : MemLp (psi1 L f) 2 :=
    memLp_two_of_le_k0 hL (aestronglyMeasurable_psi1 L hf) (norm_psi1_le hL.le hf hfab)
  exact hp.const_mul _

omit hfab in
theorem freeResolvent_weak_one :
    HasWeakDerivOn univ (derivList 1) (freeResolvent L f) (freeResolventDeriv L f) := by
  intro φ hφ
  rw [iterDirDeriv_derivList_one,
    integral_freeResolvent_mul_deriv hL hf (testLike_of_isTestFn hφ)]
  simp

theorem freeResolventDeriv_weak_one :
    HasWeakDerivOn univ (derivList 1) (freeResolventDeriv L f) (freeResolventSecond L f) := by
  intro φ hφ
  rw [iterDirDeriv_derivList_one,
    integral_freeResolventDeriv_mul_deriv hL hf (testLike_of_isTestFn hφ)
      (integrable_mul_testFn hf hφ)
      (integrable_mul_testFn (integrable_freeResolvent hL hf hfab) hφ)]
  simp

theorem freeResolvent_weak_two :
    HasWeakDerivOn univ (derivList 2) (freeResolvent L f) (freeResolventSecond L f) := by
  have h := (freeResolvent_weak_one hL hf).trans (freeResolventDeriv_weak_one hL hf hfab)
  exact h

end CompactData

theorem memLp_freeResolventSecond {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) {a b : ℝ} (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) :
    MemLp (freeResolventSecond L f) 2 :=
  ((memLp_freeResolvent hL (integrable_of_memLp_two hf hfab) hfab).const_mul _).sub hf

/-- The actual differential equation, with the correct positive-resolvent sign. -/
theorem freeResolvent_equation (L : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    -freeResolventSecond L f x + (L : ℂ) ^ 2 * freeResolvent L f x = f x := by
  unfold freeResolventSecond
  ring

end UnforcedLeray.Sturm
