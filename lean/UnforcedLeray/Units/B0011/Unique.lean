import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.Order.Field

/-!
# Unit B0011, helper: uniqueness for `ψ'' + ψ'/r - 4ψ/r² = f` on `(0, ∞)`

Adapted from the reference formalization
`NonUniqueEuler/lean/NonUniqueEuler/H/Sec4/Sector/GreenUnique.lean` (same Lean and Mathlib
versions), specialised to the angular index `2` and with weaker boundary conditions: instead
of `φ = O(r²)` at `0` and `φ = O(r⁻²)` at `∞` we only assume `φ r² → 0` as `r → 0⁺` and
`φ r⁻² → 0` as `r → ∞`, where `φ = ψ₁ - ψ₂`. These exclude exactly the homogeneous solutions
`r⁻²` and `r²`.

The general homogeneous solution is obtained from the two first integrals
`(rφ' + 2φ)/r²` and `(rφ' - 2φ)r²`, which have zero derivative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics

namespace UnforcedLeray.B0011

/-- The difference of two solutions solves the homogeneous equation. -/
theorem homogeneous_of_sub {f ψ₁ ψ₂ ψ₁' ψ₂' : ℝ → ℂ}
    (hf : ∀ a' b' : ℝ, 0 < a' → 0 < b' → IntervalIntegrable f volume a' b')
    (hd₁ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₁ (ψ₁' r) r) (hc₁ : ContinuousOn ψ₁' (Ioi 0))
    (hi₁ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₁' b - ψ₁' a = ∫ r in a..b, (f r - ψ₁' r / (r : ℂ) + 4 * ψ₁ r / (r : ℂ) ^ 2))
    (hd₂ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₂ (ψ₂' r) r) (hc₂ : ContinuousOn ψ₂' (Ioi 0))
    (hi₂ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₂' b - ψ₂' a = ∫ r in a..b, (f r - ψ₂' r / (r : ℂ) + 4 * ψ₂ r / (r : ℂ) ^ 2))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (ψ₁' b - ψ₂' b) - (ψ₁' a - ψ₂' a) =
      ∫ r in a..b, (-((ψ₁' r - ψ₂' r) / (r : ℂ)) + 4 * (ψ₁ r - ψ₂ r) / (r : ℂ) ^ 2) := by
  have hsub : uIcc a b ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (lt_min ha hb) hr.1
  have hr0 : ∀ r ∈ uIcc a b, (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt (hsub hr)
  have hcont : ∀ {ψ ψ' : ℝ → ℂ}, (∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) →
      ContinuousOn ψ' (Ioi 0) → IntervalIntegrable (fun r : ℝ => f r - ψ' r / (r : ℂ) +
        4 * ψ r / (r : ℂ) ^ 2) volume a b := by
    intro ψ ψ' hd hc
    have hψ : ContinuousOn ψ (uIcc a b) := fun r hr =>
      (hd r (hsub hr)).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (fun r : ℝ => -(ψ' r / (r : ℂ)) + 4 * ψ r / (r : ℂ) ^ 2)
        (uIcc a b) :=
      ((hc.mono hsub).div Complex.continuous_ofReal.continuousOn hr0).neg.add
        ((continuousOn_const.mul hψ).div (Complex.continuous_ofReal.continuousOn.pow 2)
          fun r hr => pow_ne_zero 2 (hr0 r hr))
    exact ((hf a b ha hb).add h2.intervalIntegrable).congr fun r _ => by ring
  rw [show (ψ₁' b - ψ₂' b) - (ψ₁' a - ψ₂' a) = (ψ₁' b - ψ₁' a) - (ψ₂' b - ψ₂' a) by ring,
    hi₁ a b ha hb, hi₂ a b ha hb, ← intervalIntegral.integral_sub (hcont hd₁ hc₁)
      (hcont hd₂ hc₂)]
  congr 1
  funext r
  ring

/-- Uniqueness for `ψ'' + ψ'/r - 4ψ/r² = f` on `(0, ∞)` (integrated form): if
`φ = ψ₁ - ψ₂` satisfies `φ r² → 0` as `r → 0⁺` and `φ r⁻² → 0` as `r → ∞`, then `φ = 0`. -/
theorem eqOn_of_delta2 {f ψ₁ ψ₂ ψ₁' ψ₂' : ℝ → ℂ}
    (hf : ∀ a' b' : ℝ, 0 < a' → 0 < b' → IntervalIntegrable f volume a' b')
    (hd₁ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₁ (ψ₁' r) r) (hc₁ : ContinuousOn ψ₁' (Ioi 0))
    (hi₁ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₁' b - ψ₁' a = ∫ r in a..b, (f r - ψ₁' r / (r : ℂ) + 4 * ψ₁ r / (r : ℂ) ^ 2))
    (hd₂ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₂ (ψ₂' r) r) (hc₂ : ContinuousOn ψ₂' (Ioi 0))
    (hi₂ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₂' b - ψ₂' a = ∫ r in a..b, (f r - ψ₂' r / (r : ℂ) + 4 * ψ₂ r / (r : ℂ) ^ 2))
    (h0 : Tendsto (fun r : ℝ => (ψ₁ r - ψ₂ r) * (r : ℂ) ^ 2) (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto (fun r : ℝ => (ψ₁ r - ψ₂ r) * ((r : ℂ) ^ 2)⁻¹) atTop (𝓝 0)) :
    EqOn ψ₁ ψ₂ (Ioi 0) := by
  set φ : ℝ → ℂ := fun r => ψ₁ r - ψ₂ r with hφ
  set φ' : ℝ → ℂ := fun r => ψ₁' r - ψ₂' r with hφ'
  set hh : ℝ → ℂ := fun r => -(φ' r / (r : ℂ)) + 4 * φ r / (r : ℂ) ^ 2 with hhh
  have hφd : ∀ r : ℝ, 0 < r → HasDerivAt φ (φ' r) r := fun r hr => (hd₁ r hr).sub (hd₂ r hr)
  have hφc : ContinuousOn φ' (Ioi 0) := hc₁.sub hc₂
  have hφi : ∀ a b : ℝ, 0 < a → 0 < b → φ' b - φ' a = ∫ r in a..b, hh r := by
    intro a b ha hb
    exact homogeneous_of_sub hf hd₁ hc₁ hi₁ hd₂ hc₂ hi₂ ha hb
  have hhc : ContinuousOn hh (Ioi 0) := by
    have hφcont : ContinuousOn φ (Ioi 0) := fun r hr =>
      (hφd r hr).continuousAt.continuousWithinAt
    have hr0 : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt hr
    exact (hφc.div Complex.continuous_ofReal.continuousOn hr0).neg.add
      ((continuousOn_const.mul hφcont).div (Complex.continuous_ofReal.continuousOn.pow 2)
        fun r hr => pow_ne_zero 2 (hr0 r hr))
  -- `φ'` is differentiable with derivative `hh`
  have hφ'd : ∀ r : ℝ, 0 < r → HasDerivAt φ' (hh r) r := by
    intro r hr
    have hF : HasDerivAt (fun s => φ' r + ∫ u in r..s, hh u) (hh r) r :=
      (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
        (hhc.stronglyMeasurableAtFilter isOpen_Ioi r hr)
        (hhc.continuousAt (Ioi_mem_nhds hr))).const_add _
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with s hs
    rw [← hφi r s hr hs]
    ring
  have hid : ∀ r : ℝ, HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := fun r =>
    (hasDerivAt_id r).ofReal_comp
  -- first integral `(rφ' + 2φ)/r²`
  have hu : ∃ A : ℂ, ∀ r ∈ Ioi (0 : ℝ),
      ((r : ℂ) * φ' r + 2 * φ r) / (r : ℂ) ^ 2 = A := by
    have hder : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt
        (fun r : ℝ => ((r : ℂ) * φ' r + 2 * φ r) / (r : ℂ) ^ 2) 0 r := by
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr)
      have h1 := (((hid r).mul (hφ'd r hr)).add ((hφd r hr).const_mul 2)).div
        ((hid r).pow 2) (pow_ne_zero 2 hr0)
      refine h1.congr_deriv ?_
      simp only [hhh, Pi.pow_apply, Pi.add_apply, Pi.mul_apply]
      field_simp
      push_cast
      ring
    obtain ⟨A, hA⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hder r hr).deriv)
    exact ⟨A, hA⟩
  -- second integral `(rφ' - 2φ)r²`
  have hv : ∃ B : ℂ, ∀ r ∈ Ioi (0 : ℝ),
      ((r : ℂ) * φ' r - 2 * φ r) * (r : ℂ) ^ 2 = B := by
    have hder : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt
        (fun r : ℝ => ((r : ℂ) * φ' r - 2 * φ r) * (r : ℂ) ^ 2) 0 r := by
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr)
      have h1 := (((hid r).mul (hφ'd r hr)).sub ((hφd r hr).const_mul 2)).mul ((hid r).pow 2)
      refine h1.congr_deriv ?_
      simp only [hhh, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
      field_simp
      push_cast
      ring
    obtain ⟨B, hB⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hder r hr).deriv)
    exact ⟨B, hB⟩
  obtain ⟨A, hA⟩ := hu
  obtain ⟨B, hB⟩ := hv
  -- `4 φ r² = A r⁴ - B`
  have hrel : ∀ r : ℝ, 0 < r → A * (r : ℂ) ^ 4 - 4 * (φ r * (r : ℂ) ^ 2) = B := by
    intro r hr
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    have e1 := hA r hr
    have e2 := hB r hr
    rw [div_eq_iff (pow_ne_zero 2 hr0)] at e1
    linear_combination (-(r : ℂ) ^ 2) * e1 + e2
  -- `B = 0`, from the behaviour at `0`
  have hB0 : B = 0 := by
    have ht2 : Tendsto (fun r : ℝ => A * (r : ℂ) ^ 4) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => A * (r : ℂ) ^ 4) (𝓝 0) (𝓝 (A * ((0 : ℝ) : ℂ) ^ 4)) :=
        ((continuous_const.mul (Complex.continuous_ofReal.pow _))).tendsto 0
      rw [Complex.ofReal_zero, zero_pow (by norm_num), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have ht := ht2.sub (h0.const_mul 4)
    rw [mul_zero, sub_zero] at ht
    have hev : (fun r : ℝ => A * (r : ℂ) ^ 4 - 4 * (φ r * (r : ℂ) ^ 2)) =ᶠ[𝓝[>] 0]
        fun _ => B := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hrel r hr
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) ht
  -- `A = 0`, from the behaviour at `∞`
  have hA0 : A = 0 := by
    have hev : (fun r : ℝ => φ r * ((r : ℂ) ^ 2)⁻¹) =ᶠ[atTop] fun _ => A / 4 := by
      filter_upwards [Ioi_mem_atTop 0] with r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      have e := hrel r hr
      rw [hB0, sub_eq_zero] at e
      have e' : A * (r : ℂ) ^ 2 = 4 * φ r := by
        refine mul_right_cancel₀ (pow_ne_zero 2 hr0) ?_
        linear_combination e
      field_simp
      linear_combination (-1 : ℂ) * e'
    have := tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hinf
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact h
    · norm_num at h
  intro r hr
  have e := hrel r hr
  rw [hA0, hB0, zero_mul, zero_sub, neg_eq_zero] at e
  have hr0 : (r : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr))
  have : φ r = 0 := by
    rcases mul_eq_zero.1 e with h | h
    · norm_num at h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact h'
      · exact absurd h' hr0
  exact sub_eq_zero.1 this

end UnforcedLeray.B0011
