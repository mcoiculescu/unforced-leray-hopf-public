import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.Monotone
import Mathlib.Data.ENNReal.Operations

/-!
# Minkowski's integral inequality in squared `lintegral` form (helper for `heatIntGradSlice`)

For a measurable `H : α × β → ℝ≥0∞` and a finite measure `ν` on `β`:
`∫⁻ y, (∫⁻ x, H x y ∂μ)² ∂ν ≤ (∫⁻ x, (∫⁻ y, H x y ² ∂ν)^(1/2) ∂μ)²`.
Proof by duality with truncation `min (G y) n` (so that all quantities are finite).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.MinkowskiL2

theorem sq_rpow_half_self (A : ℝ≥0∞) : (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem iSup_min_nat (g : ℝ≥0∞) : ⨆ n : ℕ, min g (n : ℝ≥0∞) = g := by
  apply le_antisymm (iSup_le fun n => min_le_left _ _)
  by_cases hg : g = ⊤
  · subst hg
    simp [ENNReal.iSup_natCast]
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hg
    exact le_iSup_of_le n (by rw [min_eq_left hn.le])

theorem iSup_min_sq (g : ℝ≥0∞) : ⨆ n : ℕ, (min g (n : ℝ≥0∞)) ^ 2 = g ^ 2 := by
  have hc : ContinuousAt (fun t : ℝ≥0∞ => t ^ 2) (⨆ n : ℕ, min g (n : ℝ≥0∞)) :=
    (ENNReal.continuous_pow 2).continuousAt
  have Mf : Monotone (fun t : ℝ≥0∞ => t ^ 2) := fun a b h => pow_le_pow_left₀ (by positivity) h 2
  have fbot : (fun t : ℝ≥0∞ => t ^ 2) ⊥ = ⊥ := by simp
  have key := Monotone.map_iSup_of_continuousAt (g := fun n : ℕ => min g (n : ℝ≥0∞)) hc Mf fbot
  simp only [iSup_min_nat] at key
  exact key.symm

theorem minkowski_truncated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsFiniteMeasure ν]
    (H : α → β → ℝ≥0∞) (hH : Measurable (fun p : α × β => H p.1 p.2)) (n : ℝ≥0∞) (hn : n ≠ ⊤) :
    ∫⁻ y, (min (∫⁻ x, H x y ∂μ) n) ^ 2 ∂ν ≤
      (∫⁻ x, (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) ^ 2 := by
  have hGm : Measurable (fun y : β => ∫⁻ x, H x y ∂μ) := hH.lintegral_prod_left'
  set G : β → ℝ≥0∞ := fun y => ∫⁻ x, H x y ∂μ with hGdef
  set T : β → ℝ≥0∞ := fun y => min (G y) n with hTdef
  have hTm : Measurable T := hGm.min measurable_const
  have hTn : ∀ y, T y ≤ n := fun y => min_le_right _ _
  have hTfin : ∀ y, T y ≠ ⊤ := fun y => ne_top_of_le_ne_top hn (hTn y)
  set S : ℝ≥0∞ := ∫⁻ y, T y ^ 2 ∂ν with hS
  have hSfin : S ≠ ⊤ := by
    have h1 : S ≤ ∫⁻ _y, n ^ 2 ∂ν := lintegral_mono fun y => by
      gcongr
      exact hTn y
    rw [lintegral_const] at h1
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top hn) (measure_ne_top ν univ)) h1
  -- step 1: T² ≤ T·G
  have hstep1 : S ≤ ∫⁻ y, T y * G y ∂ν := lintegral_mono fun y => by
    rw [sq]
    gcongr
    exact min_le_left _ _
  -- step 2: pull `T y` into the x-integral
  have hstep2 : ∫⁻ y, T y * G y ∂ν = ∫⁻ y, ∫⁻ x, T y * H x y ∂μ ∂ν :=
    lintegral_congr fun y => (lintegral_const_mul' _ _ (hTfin y)).symm
  -- step 3: Tonelli
  have hmeas2 : Measurable (fun p : β × α => T p.1 * H p.2 p.1) :=
    (hTm.comp measurable_fst).mul (hH.comp measurable_swap)
  have hstep3 : ∫⁻ y, ∫⁻ x, T y * H x y ∂μ ∂ν = ∫⁻ x, ∫⁻ y, T y * H x y ∂ν ∂μ :=
    lintegral_lintegral_swap (f := fun y x => T y * H x y) hmeas2.aemeasurable
  -- step 4: Hölder in y for each fixed x
  have hholder : ∀ x : α, ∫⁻ y, T y * H x y ∂ν ≤
      (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := by
    intro x
    have hf : Measurable (fun y : β => H x y) := hH.comp measurable_prodMk_left
    have H2 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
      hf.aemeasurable hTm.aemeasurable
    simp only [Pi.mul_apply, ENNReal.rpow_two] at H2
    calc ∫⁻ y, T y * H x y ∂ν = ∫⁻ y, H x y * T y ∂ν :=
          lintegral_congr fun y => mul_comm _ _
      _ ≤ _ := H2
  -- step 5: combine
  have hS1 : S ≤ (∫⁻ x, (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) * S ^ (1 / 2 : ℝ) := by
    have hpow : S ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSfin
    calc S ≤ ∫⁻ y, T y * G y ∂ν := hstep1
      _ = ∫⁻ y, ∫⁻ x, T y * H x y ∂μ ∂ν := hstep2
      _ = ∫⁻ x, ∫⁻ y, T y * H x y ∂ν ∂μ := hstep3
      _ ≤ ∫⁻ x, (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) ∂μ :=
          lintegral_mono fun x => hholder x
      _ = (∫⁻ x, (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) * S ^ (1 / 2 : ℝ) :=
          lintegral_mul_const' _ _ hpow
  -- step 6: conclude S ≤ R²
  set R : ℝ≥0∞ := ∫⁻ x, (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ with hR
  show S ≤ R ^ 2
  have hsq := sq_rpow_half_self S
  by_cases h0 : S ^ (1 / 2 : ℝ) = 0
  · have hS0 : S = 0 := by
      rw [← hsq, h0, zero_pow two_ne_zero]
    rw [hS0]
    exact bot_le
  · have hs_top : S ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSfin
    have hss : S ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) = S := by
      rw [← sq]
      exact hsq
    have h2 : S ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) ≤ R * S ^ (1 / 2 : ℝ) := by
      rw [hss]
      exact hS1
    have hle : S ^ (1 / 2 : ℝ) ≤ R := (ENNReal.mul_le_mul_iff_left h0 hs_top).1 h2
    calc S = (S ^ (1 / 2 : ℝ)) ^ 2 := hsq.symm
      _ ≤ R ^ 2 := by gcongr

/-- Minkowski's integral inequality (squared, `lintegral` form) for a finite measure `ν`. -/
theorem minkowski_sq_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsFiniteMeasure ν]
    (H : α → β → ℝ≥0∞) (hH : Measurable (fun p : α × β => H p.1 p.2)) :
    ∫⁻ y, (∫⁻ x, H x y ∂μ) ^ 2 ∂ν ≤
      (∫⁻ x, (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) ^ 2 := by
  have hGm : Measurable (fun y : β => ∫⁻ x, H x y ∂μ) := hH.lintegral_prod_left'
  have hmono : ∀ y : β, Monotone (fun n : ℕ => min (∫⁻ x, H x y ∂μ) (n : ℝ≥0∞)) :=
    fun y a b h => min_le_min_left _ (by exact_mod_cast h)
  calc ∫⁻ y, (∫⁻ x, H x y ∂μ) ^ 2 ∂ν
      = ∫⁻ y, ⨆ n : ℕ, (min (∫⁻ x, H x y ∂μ) (n : ℝ≥0∞)) ^ 2 ∂ν :=
        lintegral_congr fun y => (iSup_min_sq _).symm
    _ = ⨆ n : ℕ, ∫⁻ y, (min (∫⁻ x, H x y ∂μ) (n : ℝ≥0∞)) ^ 2 ∂ν := by
        apply lintegral_iSup
        · intro n
          exact ((hGm.min measurable_const).pow_const 2)
        · intro a b hab y
          exact pow_le_pow_left₀ (by positivity) (hmono y hab) 2
    _ ≤ _ := iSup_le fun n =>
        minkowski_truncated H hH (n : ℝ≥0∞) (ENNReal.natCast_ne_top n)

end UnforcedLeray.Short.PartIIa.N01.MinkowskiL2
