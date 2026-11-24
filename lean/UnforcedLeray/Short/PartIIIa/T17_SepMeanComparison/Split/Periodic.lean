import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Split helper: lintegral of a periodic function and the affine phase change (T17/1)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem t17s_periodic_lintegral (c : ℝ) (hc : 0 < c) (φ : ℝ → ℝ≥0∞)
    (hφ : ∀ q, φ (q + c) = φ q) (B : ℝ) :
    ∫⁻ q in Ioc B (B + c), φ q = ∫⁻ q in Ioc 0 (0 + c), φ q := by
  have h1 := isAddFundamentalDomain_Ioc hc B
  have h2 := isAddFundamentalDomain_Ioc hc 0
  refine h1.setLIntegral_eq h2 φ ?_
  intro g x
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
  have hper : Function.Periodic φ c := hφ
  have h3 : (g +ᵥ x : ℝ) = x + n • c := by
    rw [AddSubgroup.vadd_def, vadd_eq_add, hn, add_comm]
  rw [h3]
  exact hper.zsmul n x

/-- The affine phase change: `∫_{τ ∈ (0, 2εc]} φ(B + τ/(2ε)) dτ = 2ε ∫_{(0,c]} φ`. -/
theorem t17s_affine_lintegral (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (φ : ℝ → ℝ≥0∞)
    (hφ : ∀ q, φ (q + c) = φ q) (B : ℝ) :
    ∫⁻ τ in Ioc 0 (2 * ε * c), φ (B + τ / (2 * ε)) = ENNReal.ofReal (2 * ε) * ∫⁻ q in Ioc 0 c, φ q := by
  have hε2 : 0 < 2 * ε := by positivity
  have himg : (fun τ : ℝ => B + τ / (2 * ε)) '' Ioc 0 (2 * ε * c) = Ioc B (B + c) := by
    ext q
    simp only [mem_image, mem_Ioc]
    constructor
    · rintro ⟨τ, ⟨h1, h2⟩, rfl⟩
      constructor
      · have : 0 < τ / (2 * ε) := by positivity
        linarith
      · have : τ / (2 * ε) ≤ c := by
          rw [div_le_iff₀ hε2]; linarith
        linarith
    · rintro ⟨h1, h2⟩
      refine ⟨(q - B) * (2 * ε), ⟨?_, ?_⟩, ?_⟩
      · exact mul_pos (by linarith) hε2
      · nlinarith
      · field_simp; ring
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioc 0 (2 * ε * c))
    (f := fun τ : ℝ => B + τ / (2 * ε)) (f' := fun _ => (2 * ε)⁻¹) measurableSet_Ioc
    (fun x _ => by
      have := ((hasDerivAt_id x).div_const (2 * ε)).const_add B
      simpa using this.hasDerivWithinAt)
    (fun a _ b _ h => by
      have : a / (2 * ε) = b / (2 * ε) := by simpa using h
      exact (div_left_inj' hε2.ne').1 this) φ
  rw [himg] at key
  have h2 := t17s_periodic_lintegral c hc φ hφ B
  rw [zero_add] at h2
  rw [h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at key
  simp only [abs_inv, abs_of_pos hε2] at key
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul hε2.le, mul_inv_cancel₀ hε2.ne']
  simp

end UnforcedLeray.Short.IIIa

end
