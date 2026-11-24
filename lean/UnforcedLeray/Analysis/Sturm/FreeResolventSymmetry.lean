import UnforcedLeray.Analysis.Sturm.FreeResolvent

/-!
# Linearity and symmetry of the actual free Green kernel

The free resolvent is convolution with the real even kernel
`exp(-L * |x|) / (2 * L)`. Its integral pairing is symmetric by Fubini.
The identities concern the actual kernel on the real line, and will allow
its extension from compactly supported L² inputs to a bounded operator.
-/

noncomputable section

open MeasureTheory Filter
open scoped ComplexConjugate

namespace UnforcedLeray.Sturm

open NonUniqueEuler.Sob.EnergyAux

theorem freeResolvent_congr_ae (L : ℝ) {f g : ℝ → ℂ}
    (h : f =ᵐ[volume] g) : freeResolvent L f = freeResolvent L g := by
  funext x
  unfold freeResolvent psi0
  congr 1
  apply integral_congr_ae
  exact h.mono fun y hy => by simp only [hy]

@[simp]
theorem freeResolvent_zero (L : ℝ) : freeResolvent L 0 = 0 := by
  funext x
  simp [freeResolvent, psi0]

theorem freeResolvent_add {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    freeResolvent L (f + g) = freeResolvent L f + freeResolvent L g := by
  funext x
  simp only [freeResolvent, psi0, Pi.add_apply, mul_add]
  rw [integral_add (integrable_k0_sub_mul' L (hL := hL.le) x hf)
    (integrable_k0_sub_mul' L (hL := hL.le) x hg)]
  ring

theorem freeResolvent_smul (L : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    freeResolvent L (c • f) = c • freeResolvent L f := by
  funext x
  simp only [freeResolvent, psi0, Pi.smul_apply, smul_eq_mul]
  have h : (fun y => (k0 L (x - y) : ℂ) * (c * f y)) =
      fun y => c * ((k0 L (x - y) : ℂ) * f y) := by
    funext y
    ring
  rw [h, integral_const_mul]
  ring

theorem freeResolvent_conj (L : ℝ) (f : ℝ → ℂ) :
    freeResolvent L (fun x => conj (f x)) = fun x => conj (freeResolvent L f x) := by
  funext x
  simp only [freeResolvent, psi0, map_mul, Complex.conj_ofReal]
  rw [← integral_conj]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by simp

/-- The bilinear symmetry identity for the real even Green kernel. -/
theorem integral_freeResolvent_mul {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, freeResolvent L f x * g x) = ∫ x, f x * freeResolvent L g x := by
  have hk : ∀ z, |k0 L z| ≤ 1 := fun z => by
    rw [abs_of_pos (k0_pos L z)]
    exact k0_le_one hL.le z
  have heven : ∀ x y, k0 L (x - y) = k0 L (y - x) := by
    intro x y
    simp only [k0, abs_sub_comm x y]
  have htranspose : ∀ y, (∫ x, (k0 L (x - y) : ℂ) * g x) = psi0 L g y := by
    intro y
    unfold psi0
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [heven x y]
  have hpair : (∫ x, psi0 L f x * g x) = ∫ x, f x * psi0 L g x := by
    simpa only [psi0, htranspose] using
      (integral_conv_mul (continuous_k0 L).measurable hk hf hg)
  calc
    (∫ x, freeResolvent L f x * g x) =
        (((2 * L)⁻¹ : ℝ) : ℂ) * ∫ x, psi0 L f x * g x := by
      simp only [freeResolvent, mul_assoc, integral_const_mul]
    _ = (((2 * L)⁻¹ : ℝ) : ℂ) * ∫ x, f x * psi0 L g x := by rw [hpair]
    _ = ∫ x, f x * freeResolvent L g x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by unfold freeResolvent; ring

/-- The sesquilinear symmetry identity needed for L² selfadjointness. -/
theorem integral_freeResolvent_mul_conj {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, freeResolvent L f x * conj (g x)) =
      ∫ x, f x * conj (freeResolvent L g x) := by
  have h := integral_freeResolvent_mul hL hf (integrable_conj hg)
  simpa only [freeResolvent_conj] using h

end UnforcedLeray.Sturm
