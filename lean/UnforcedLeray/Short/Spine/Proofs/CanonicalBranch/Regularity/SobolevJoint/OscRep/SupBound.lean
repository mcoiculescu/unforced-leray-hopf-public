import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.Sobolev1D
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.EnergyBound

/-!
# Leaf B6 (`OscSupBound`): sup bounds for `φ` and `φ'`, linear in `n`

Source of record: `the November 2 reference manuscript`, lines 1134-1140.
The Prop `OscSupBound` is proved exactly as stated in `Short/Spine/Sub/SP_CAN4_4_1.lean`.

Argument. Fix `0 < a < b`, let `M = |K|` where `K` comes from `oscEnergyBound_proof a b`, and let
`s = 1 + n ≥ 1`.
* `∫_a^b |φ|² ≤ M` and `∫_a^b |φ'|² ≤ M s`. The 1D Sobolev inequality for `g = φ` gives
  `|φ x|² ≤ (1/(b-a) + 1) M + M s ≤ K2 s²`, with `K2 = (1/(b-a) + 2) M`.
* With `g = φ'`, the ODE `φ'' = c₁ φ' + c₀ φ` (`OscOde.deriv2`) and the bounds
  `|c₁| ≤ c₁₀ := 1/a + b/2`, `|c₀ n| ≤ c₀₀ s` (`c₀₀ = 4 (1/a)² + 2`) on `[a, b]` give
  `|φ''|² ≤ 2 c₁₀² |φ'|² + 2 c₀₀² s² |φ|²` pointwise, so `∫_a^b |φ''|² ≤ K3 s²`. The 1D Sobolev
  inequality for `g = φ'` then gives `|φ' x|² ≤ K4 s²`, with `K4 = (1/(b-a) + 1) M + K3`.
* `C = K2 + K4 + 1` satisfies `C ≥ 1`, `C² ≥ K2`, `C² ≥ K4`, so `|φ x|, |φ' x| ≤ C s`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

theorem oscSupBound_proof : UnforcedLeray.Short.Spine.OscSupBound := by
  intro a b ha hab
  obtain ⟨K, hK⟩ := oscEnergyBound_proof a b ha hab
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = |K| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; exact abs_nonneg K
  have hKM : K ≤ M := by rw [hMdef]; exact le_abs_self K
  have hba : 0 < b - a := by linarith
  have hba0 : 0 ≤ 1 / (b - a) := by positivity
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le ha ht.1
  have hII : ∀ f : ℝ → ℝ, ContinuousOn f (Icc a b) → IntervalIntegrable f volume a b :=
    fun f hf => hf.intervalIntegrable_of_Icc hab.le
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = 1 / a + b / 2 := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c : ℝ, c = 4 * (1 / a) ^ 2 + 2 := ⟨_, rfl⟩
  have hc1_0 : 0 ≤ c1 := by
    have h1 : 0 < 1 / a := by positivity
    have h2 : 0 < b := by linarith
    rw [hc1]
    linarith
  have hc0_0 : 0 ≤ c0 := by rw [hc0]; positivity
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = (1 / (b - a) + 2) * M := ⟨_, rfl⟩
  obtain ⟨K3, hK3⟩ : ∃ K3 : ℝ, K3 = 2 * c1 ^ 2 * M + 2 * c0 ^ 2 * M := ⟨_, rfl⟩
  obtain ⟨K4, hK4⟩ : ∃ K4 : ℝ, K4 = (1 / (b - a) + 1) * M + K3 := ⟨_, rfl⟩
  have hK2_0 : 0 ≤ K2 := by rw [hK2]; positivity
  have hK3_0 : 0 ≤ K3 := by rw [hK3]; positivity
  have hK4_0 : 0 ≤ K4 := by rw [hK4]; positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = K2 + K4 + 1 := ⟨_, rfl⟩
  have hC1' : 1 ≤ C := by rw [hC]; linarith
  have hCsq : C ≤ C ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) hC1'
  have hK2C : K2 ≤ C ^ 2 := by
    have : K2 ≤ C := by rw [hC]; linarith
    exact le_trans this hCsq
  have hK4C : K4 ≤ C ^ 2 := by
    have : K4 ≤ C := by rw [hC]; linarith
    exact le_trans this hCsq
  -- the square-root step: `x² ≤ y²`, `0 ≤ x`, `0 ≤ y` give `x ≤ y`
  have fin : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ 2 ≤ y ^ 2 → x ≤ y :=
    fun x y hx hy h => (sq_le_sq₀ hx hy).1 h
  refine ⟨C, fun n φ hφ hint => ?_⟩
  obtain ⟨hE1, hE2⟩ := hK n φ hφ hint
  have hE1' : ∫ r in a..b, ‖φ r‖ ^ 2 ≤ M := le_trans hE1 hKM
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs2 : (1 + (n : ℝ)) ≤ (1 + (n : ℝ)) ^ 2 := by
    rw [sq]; exact le_mul_of_one_le_right (by linarith) (by linarith)
  have hs1 : (1 : ℝ) ≤ 1 + (n : ℝ) := by linarith
  have hs3 : (1 : ℝ) ≤ (1 + (n : ℝ)) ^ 2 := le_trans hs1 hs2
  have hE2' : ∫ r in a..b, ‖deriv φ r‖ ^ 2 ≤ M * (1 + n) :=
    le_trans hE2 (mul_le_mul_of_nonneg_right hKM (by linarith))
  -- regularity on `[a, b]`
  have hφc : ContinuousOn φ (Icc a b) := hφ.1.continuousOn.mono hsub
  have hg : ContDiffOn ℝ ∞ (deriv φ) (Ioi 0) := hφ.1.deriv_of_isOpen isOpen_Ioi (by simp)
  have hgc : ContinuousOn (deriv φ) (Icc a b) := hg.continuousOn.mono hsub
  have hg2c : ContinuousOn (deriv (deriv φ)) (Icc a b) :=
    (hg.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hsub
  -- coefficient bounds on `[a, b]`
  have hC1b : ∀ r ∈ Icc a b, ‖oscC1 r‖ ≤ c1 := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    have h1 : 1 / r ≤ 1 / a := one_div_le_one_div_of_le ha hr.1
    have h1' : 0 < 1 / r := by positivity
    have h2 : 0 < 1 / a := by positivity
    have h3 : 0 < b := by linarith
    unfold oscC1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le, hc1]
    constructor <;> linarith [hr.2]
  have hC0b : ∀ n' : ℕ, ∀ r ∈ Icc a b, ‖oscC0 n' r‖ ≤ c0 * (1 + (n' : ℝ)) := by
    intro n' r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    have h1 : 1 / r ≤ 1 / a := one_div_le_one_div_of_le ha hr.1
    have h1' : 0 < 1 / r := by positivity
    have hsq : (1 / r) ^ 2 ≤ (1 / a) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self h1'.le h1
    have h4 : 4 / r ^ 2 = 4 * (1 / r) ^ 2 := by ring
    have hn' : (0 : ℝ) ≤ n' := Nat.cast_nonneg n'
    have hA0 : (0 : ℝ) ≤ (1 / a) ^ 2 := sq_nonneg _
    have hB0 : (0 : ℝ) ≤ (1 / r) ^ 2 := sq_nonneg _
    have hAn : (0 : ℝ) ≤ (1 / a) ^ 2 * n' := mul_nonneg hA0 hn'
    unfold oscC0
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le, hc0, h4]
    constructor <;> linarith
  -- pointwise bound for `φ''` on `[a, b]`
  have hgnorm : ∀ r ∈ Icc a b, ‖deriv (deriv φ) r‖ ^ 2 ≤
      2 * c1 ^ 2 * ‖deriv φ r‖ ^ 2 + 2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2 * ‖φ r‖ ^ 2 := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    have hX : deriv (deriv φ) r = oscC1 r * deriv φ r + oscC0 n r * φ r :=
      OscOde.deriv2 hφ hr0
    have hn1 : ‖oscC1 r * deriv φ r‖ ≤ c1 * ‖deriv φ r‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC1b r hr) (norm_nonneg _)
    have hn2 : ‖oscC0 n r * φ r‖ ≤ (c0 * (1 + (n : ℝ))) * ‖φ r‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC0b n r hr) (norm_nonneg _)
    have hY : ‖deriv (deriv φ) r‖ ≤ c1 * ‖deriv φ r‖ + (c0 * (1 + (n : ℝ))) * ‖φ r‖ := by
      rw [hX]; exact (norm_add_le _ _).trans (add_le_add hn1 hn2)
    have hsqY := mul_self_le_mul_self (norm_nonneg _) hY
    linarith [sq_nonneg (c1 * ‖deriv φ r‖ - c0 * (1 + (n : ℝ)) * ‖φ r‖)]
  -- integrability
  have hI_gg : IntervalIntegrable (fun r => ‖deriv (deriv φ) r‖ ^ 2) volume a b :=
    hII _ (hg2c.norm.pow 2)
  have hI_g : IntervalIntegrable (fun r => ‖deriv φ r‖ ^ 2) volume a b :=
    hII _ (hgc.norm.pow 2)
  have hI_φ : IntervalIntegrable (fun r => ‖φ r‖ ^ 2) volume a b :=
    hII _ (hφc.norm.pow 2)
  have hI_A : IntervalIntegrable (fun r => 2 * c1 ^ 2 * ‖deriv φ r‖ ^ 2) volume a b :=
    hI_g.const_mul _
  have hI_B : IntervalIntegrable (fun r => 2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2 * ‖φ r‖ ^ 2) volume a b :=
    hI_φ.const_mul _
  have hmono : ∫ r in a..b, ‖deriv (deriv φ) r‖ ^ 2 ≤
      ∫ r in a..b, (2 * c1 ^ 2 * ‖deriv φ r‖ ^ 2 + 2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2 * ‖φ r‖ ^ 2) :=
    intervalIntegral.integral_mono_on hab.le hI_gg (hI_A.add hI_B) (fun r hr => hgnorm r hr)
  have hadd : ∫ r in a..b, (2 * c1 ^ 2 * ‖deriv φ r‖ ^ 2 + 2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2 * ‖φ r‖ ^ 2)
      = (∫ r in a..b, 2 * c1 ^ 2 * ‖deriv φ r‖ ^ 2)
        + (∫ r in a..b, 2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2 * ‖φ r‖ ^ 2) :=
    intervalIntegral.integral_add hI_A hI_B
  have hcm1 : ∫ r in a..b, 2 * c1 ^ 2 * ‖deriv φ r‖ ^ 2
      = 2 * c1 ^ 2 * ∫ r in a..b, ‖deriv φ r‖ ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  have hcm2 : ∫ r in a..b, 2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2 * ‖φ r‖ ^ 2
      = 2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2 * ∫ r in a..b, ‖φ r‖ ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  have hI2 : ∫ r in a..b, ‖deriv (deriv φ) r‖ ^ 2 ≤
      2 * c1 ^ 2 * (M * (1 + n)) + 2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2 * M := by
    have e1 : (2 * c1 ^ 2) * ∫ r in a..b, ‖deriv φ r‖ ^ 2 ≤ (2 * c1 ^ 2) * (M * (1 + n)) :=
      mul_le_mul_of_nonneg_left hE2' (by positivity)
    have e2 : (2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2) * ∫ r in a..b, ‖φ r‖ ^ 2
        ≤ (2 * c0 ^ 2 * (1 + (n : ℝ)) ^ 2) * M :=
      mul_le_mul_of_nonneg_left hE1' (by positivity)
    linarith
  -- `|φ x|²` bound
  have hF : ∀ x ∈ Icc a b, ‖φ x‖ ^ 2 ≤ K2 * (1 + (n : ℝ)) ^ 2 := by
    intro x hx
    have hsob := oscSobolev1D_proof φ a b ha hab hφ.1 x hx
    have t1 : (1 / (b - a) + 1) * ∫ r in a..b, ‖φ r‖ ^ 2 ≤ (1 / (b - a) + 1) * M :=
      mul_le_mul_of_nonneg_left hE1' (by positivity)
    have t2 : (1 / (b - a) + 1) * M * 1 ≤ (1 / (b - a) + 1) * M * (1 + (n : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs3 (by positivity)
    have t3 : M * (1 + (n : ℝ)) ≤ M * (1 + (n : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs2 hM0
    rw [hK2]
    linarith
  -- `|φ' x|²` bound
  have hG : ∀ x ∈ Icc a b, ‖deriv φ x‖ ^ 2 ≤ K4 * (1 + (n : ℝ)) ^ 2 := by
    intro x hx
    have hsob := oscSobolev1D_proof (deriv φ) a b ha hab hg x hx
    have t1 : (1 / (b - a) + 1) * ∫ r in a..b, ‖deriv φ r‖ ^ 2
        ≤ (1 / (b - a) + 1) * (M * (1 + n)) :=
      mul_le_mul_of_nonneg_left hE2' (by positivity)
    have t2 : (1 / (b - a) + 1) * (M * (1 + n)) ≤ (1 / (b - a) + 1) * M * (1 + (n : ℝ)) ^ 2 := by
      have : (1 / (b - a) + 1) * (M * (1 + n)) = (1 / (b - a) + 1) * M * (1 + n) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hs2 (by positivity)
    have t3 : 2 * c1 ^ 2 * (M * (1 + n)) ≤ 2 * c1 ^ 2 * M * (1 + (n : ℝ)) ^ 2 := by
      have : 2 * c1 ^ 2 * (M * (1 + n)) = (2 * c1 ^ 2 * M) * (1 + n) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hs2 (by positivity)
    rw [hK4, hK3]
    linarith
  intro r hr
  have hF' : ‖φ r‖ ^ 2 ≤ (C * (1 + (n : ℝ))) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hK2C (sq_nonneg (1 + (n : ℝ)))
    have hF2 := hF r hr
    linarith
  have hG' : ‖deriv φ r‖ ^ 2 ≤ (C * (1 + (n : ℝ))) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hK4C (sq_nonneg (1 + (n : ℝ)))
    have hG2 := hG r hr
    linarith
  have hCs : 0 ≤ C * (1 + (n : ℝ)) := mul_nonneg (by linarith) (by linarith)
  exact ⟨fin _ _ (norm_nonneg _) hCs hF', fin _ _ (norm_nonneg _) hCs hG'⟩

end UnforcedLeray.Short.Spine
