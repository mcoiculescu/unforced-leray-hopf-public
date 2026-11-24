import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Algebra.Order.Field

/-!
# Uniqueness for `Δ_n ψ = f` on `(0, ∞)`, every `n ≥ 1` (helper of INF12 target P4)

Scoping note `INF10-INF12-INF18-Planar.md`, §5, target **P4** (`eqOn_greenN_of_tendsto`); blueprint
unit `B0011` (`paper/main.tex` lines 683–689: `R` is "the unique inverse of `Δ₂` that is regular
at `0` and decaying at `∞`") and unit `B0079` (lines 1366–1379, the Green inverse of `Δ_n`).

Generalisation from `n = 2` to every `n ≥ 1` of the drafted `Units/B0011/Unique.lean`
(`eqOn_of_delta2`), itself adapted from the reference formalization
`NonUniqueEuler/lean/NonUniqueEuler/H/Sec4/Sector/GreenUnique.lean`. The equation is
`ψ'' + ψ'/r - n²ψ/r² = f`, in the integrated form of `B0079.IsDeltaNSol`. For the difference
`φ` of two solutions the two first integrals `(rφ' + nφ) r⁻ⁿ` and `(rφ' - nφ) rⁿ` are constant,
so `2n φ rⁿ = A r²ⁿ - B`; the boundary conditions `φ rⁿ → 0` at `0⁺` and `φ r⁻ⁿ → 0` at `∞`
(which exclude exactly the homogeneous solutions `r⁻ⁿ` and `rⁿ`) force `B = 0` and `A = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Planar

/-- The difference of two integrated solutions of `Δ_nψ = f` solves the homogeneous equation. -/
theorem homogeneous_of_sub_deltaN (n : ℕ) {f ψ₁ ψ₂ ψ₁' ψ₂' : ℝ → ℂ}
    (hf : ∀ a' b' : ℝ, 0 < a' → 0 < b' → IntervalIntegrable f volume a' b')
    (hd₁ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₁ (ψ₁' r) r) (hc₁ : ContinuousOn ψ₁' (Ioi 0))
    (hi₁ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₁' b - ψ₁' a = ∫ r in a..b, (f r - ψ₁' r / (r : ℂ) + (n : ℂ) ^ 2 * ψ₁ r / (r : ℂ) ^ 2))
    (hd₂ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₂ (ψ₂' r) r) (hc₂ : ContinuousOn ψ₂' (Ioi 0))
    (hi₂ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₂' b - ψ₂' a = ∫ r in a..b, (f r - ψ₂' r / (r : ℂ) + (n : ℂ) ^ 2 * ψ₂ r / (r : ℂ) ^ 2))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (ψ₁' b - ψ₂' b) - (ψ₁' a - ψ₂' a) =
      ∫ r in a..b, (-((ψ₁' r - ψ₂' r) / (r : ℂ)) +
        (n : ℂ) ^ 2 * (ψ₁ r - ψ₂ r) / (r : ℂ) ^ 2) := by
  have hsub : uIcc a b ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (lt_min ha hb) hr.1
  have hr0 : ∀ r ∈ uIcc a b, (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt (hsub hr)
  have hcont : ∀ {ψ ψ' : ℝ → ℂ}, (∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) →
      ContinuousOn ψ' (Ioi 0) → IntervalIntegrable (fun r : ℝ => f r - ψ' r / (r : ℂ) +
        (n : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2) volume a b := by
    intro ψ ψ' hd hc
    have hψ : ContinuousOn ψ (uIcc a b) := fun r hr =>
      (hd r (hsub hr)).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (fun r : ℝ => -(ψ' r / (r : ℂ)) + (n : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2)
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

/-- **Uniqueness for `Δ_nψ = f` on `(0, ∞)`, `n ≥ 1`** (integrated form): if `φ = ψ₁ - ψ₂`
satisfies `φ(r) rⁿ → 0` as `r → 0⁺` and `φ(r) r⁻ⁿ → 0` as `r → ∞`, then `ψ₁ = ψ₂` on
`(0, ∞)`. -/
theorem eqOn_of_deltaN {n : ℕ} (hn : 1 ≤ n) {f ψ₁ ψ₂ ψ₁' ψ₂' : ℝ → ℂ}
    (hf : ∀ a' b' : ℝ, 0 < a' → 0 < b' → IntervalIntegrable f volume a' b')
    (hd₁ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₁ (ψ₁' r) r) (hc₁ : ContinuousOn ψ₁' (Ioi 0))
    (hi₁ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₁' b - ψ₁' a = ∫ r in a..b, (f r - ψ₁' r / (r : ℂ) + (n : ℂ) ^ 2 * ψ₁ r / (r : ℂ) ^ 2))
    (hd₂ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₂ (ψ₂' r) r) (hc₂ : ContinuousOn ψ₂' (Ioi 0))
    (hi₂ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₂' b - ψ₂' a = ∫ r in a..b, (f r - ψ₂' r / (r : ℂ) + (n : ℂ) ^ 2 * ψ₂ r / (r : ℂ) ^ 2))
    (h0 : Tendsto (fun r : ℝ => (ψ₁ r - ψ₂ r) * (r : ℂ) ^ n) (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto (fun r : ℝ => (ψ₁ r - ψ₂ r) * ((r : ℂ) ^ n)⁻¹) atTop (𝓝 0)) :
    EqOn ψ₁ ψ₂ (Ioi 0) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  set φ : ℝ → ℂ := fun r => ψ₁ r - ψ₂ r with hφ
  set φ' : ℝ → ℂ := fun r => ψ₁' r - ψ₂' r with hφ'
  set N : ℂ := ((m + 1 : ℕ) : ℂ) with hN
  set hh : ℝ → ℂ := fun r => -(φ' r / (r : ℂ)) + N ^ 2 * φ r / (r : ℂ) ^ 2 with hhh
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Nat.succ_ne_zero m
  have hφd : ∀ r : ℝ, 0 < r → HasDerivAt φ (φ' r) r := fun r hr => (hd₁ r hr).sub (hd₂ r hr)
  have hφc : ContinuousOn φ' (Ioi 0) := hc₁.sub hc₂
  have hφi : ∀ a b : ℝ, 0 < a → 0 < b → φ' b - φ' a = ∫ r in a..b, hh r := by
    intro a b ha hb
    exact homogeneous_of_sub_deltaN (m + 1) hf hd₁ hc₁ hi₁ hd₂ hc₂ hi₂ ha hb
  have hhc : ContinuousOn hh (Ioi 0) := by
    have hφcont : ContinuousOn φ (Ioi 0) := fun r hr =>
      (hφd r hr).continuousAt.continuousWithinAt
    have hr0 : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt hr
    exact (hφc.div Complex.continuous_ofReal.continuousOn hr0).neg.add
      ((continuousOn_const.mul hφcont).div (Complex.continuous_ofReal.continuousOn.pow 2)
        fun r hr => pow_ne_zero 2 (hr0 r hr))
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
  -- first integral `(rφ' + nφ) / rⁿ`
  have hu : ∃ A : ℂ, ∀ r ∈ Ioi (0 : ℝ),
      ((r : ℂ) * φ' r + N * φ r) / (r : ℂ) ^ (m + 1) = A := by
    have hder : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt
        (fun r : ℝ => ((r : ℂ) * φ' r + N * φ r) / (r : ℂ) ^ (m + 1)) 0 r := by
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr)
      have h1 := (((hid r).mul (hφ'd r hr)).add ((hφd r hr).const_mul N)).div
        ((hid r).pow (m + 1)) (pow_ne_zero (m + 1) hr0)
      refine h1.congr_deriv ?_
      simp only [hhh, Nat.add_sub_cancel, hN, Pi.pow_apply, Pi.add_apply, Pi.sub_apply,
        Pi.mul_apply, Pi.div_apply]
      push_cast
      field_simp
      ring
    obtain ⟨A, hA⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hder r hr).deriv)
    exact ⟨A, hA⟩
  -- second integral `(rφ' - nφ) rⁿ`
  have hv : ∃ B : ℂ, ∀ r ∈ Ioi (0 : ℝ),
      ((r : ℂ) * φ' r - N * φ r) * (r : ℂ) ^ (m + 1) = B := by
    have hder : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt
        (fun r : ℝ => ((r : ℂ) * φ' r - N * φ r) * (r : ℂ) ^ (m + 1)) 0 r := by
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr)
      have h1 := (((hid r).mul (hφ'd r hr)).sub ((hφd r hr).const_mul N)).mul
        ((hid r).pow (m + 1))
      refine h1.congr_deriv ?_
      simp only [hhh, Nat.add_sub_cancel, hN, Pi.pow_apply, Pi.add_apply, Pi.sub_apply,
        Pi.mul_apply, Pi.div_apply]
      push_cast
      field_simp
      ring
    obtain ⟨B, hB⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hder r hr).deriv)
    exact ⟨B, hB⟩
  obtain ⟨A, hA⟩ := hu
  obtain ⟨B, hB⟩ := hv
  -- `2n φ rⁿ = A r²ⁿ - B`
  have hrel : ∀ r : ℝ, 0 < r →
      A * ((r : ℂ) ^ (m + 1)) ^ 2 - 2 * N * (φ r * (r : ℂ) ^ (m + 1)) = B := by
    intro r hr
    have hr0 : (r : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast ne_of_gt hr)
    have e1 := hA r hr
    have e2 := hB r hr
    rw [div_eq_iff hr0] at e1
    linear_combination (-(r : ℂ) ^ (m + 1)) * e1 + e2
  have hpow0 : Tendsto (fun r : ℝ => (r : ℂ) ^ (m + 1)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun r : ℝ => (r : ℂ) ^ (m + 1)) (𝓝 0) (𝓝 (((0 : ℝ) : ℂ) ^ (m + 1))) :=
      (Complex.continuous_ofReal.pow _).tendsto 0
    rw [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero m)] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- `B = 0`, from the behaviour at `0`
  have hB0 : B = 0 := by
    have ht2 : Tendsto (fun r : ℝ => A * ((r : ℂ) ^ (m + 1)) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := (hpow0.pow 2).const_mul A
      rwa [zero_pow two_ne_zero, mul_zero] at this
    have ht := ht2.sub (h0.const_mul (2 * N))
    rw [mul_zero, sub_zero] at ht
    have hev : (fun r : ℝ => A * ((r : ℂ) ^ (m + 1)) ^ 2 -
        2 * N * (φ r * (r : ℂ) ^ (m + 1))) =ᶠ[𝓝[>] 0] fun _ => B := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hrel r hr
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) ht
  -- `A = 0`, from the behaviour at `∞`
  have hA0 : A = 0 := by
    have hev : (fun r : ℝ => φ r * ((r : ℂ) ^ (m + 1))⁻¹) =ᶠ[atTop]
        fun _ => A / (2 * N) := by
      filter_upwards [Ioi_mem_atTop 0] with r hr
      have hr0 : (r : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast ne_of_gt hr)
      have e := hrel r hr
      rw [hB0, sub_eq_zero] at e
      have e' : A * (r : ℂ) ^ (m + 1) = 2 * N * φ r := by
        refine mul_right_cancel₀ hr0 ?_
        linear_combination e
      field_simp
      linear_combination (-1 : ℂ) * e'
    have := tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hinf
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact h
    · exact absurd h (mul_ne_zero two_ne_zero hN0)
  intro r hr
  have e := hrel r hr
  rw [hA0, hB0, zero_mul, zero_sub, neg_eq_zero] at e
  have hr0 : (r : ℂ) ^ (m + 1) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr))
  have : φ r = 0 := by
    rcases mul_eq_zero.1 e with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hN0)
    · rcases mul_eq_zero.1 h with h' | h'
      · exact h'
      · exact absurd h' hr0
  exact sub_eq_zero.1 this

end UnforcedLeray.Planar
