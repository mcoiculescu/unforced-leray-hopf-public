import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/19`: the weighted pressure jets `WJetP` from `TailW`, `BandP`, `EtaSegment`

Source of record: `the November 2 reference manuscript` 5464-5465, 5484-5495, 460-478.
* Tail region `|η| ≥ C_p/ν + 2`: `TailW` (the `p` term).
* Band region, spatial order `m = m'+1`: `BandP` at `ℓ, m'`, with the weight `≤ (C_p+3)^4 ν⁻⁴`.
* Band region, `m = 0`: the fundamental theorem of calculus in `η` (`EtaSegment`) for `F = tr.p`
  from the endpoint `η* = C_p/ν + 2` (where `TailW` applies), with the `η`-derivative bounded by
  `BandP` at `ℓ, 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- Monotonicity of the power bound in the exponent, `t = ν⁻¹ ≥ 1`. -/
theorem wJetP_mono {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (C : ℝ) {k K : ℕ} (hk : k ≤ K) :
    C * ν⁻¹ ^ k ≤ |C| * ν⁻¹ ^ K := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  calc C * ν⁻¹ ^ k ≤ |C| * ν⁻¹ ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (inv_nonneg.2 hν.le) _)
    _ ≤ |C| * ν⁻¹ ^ K := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hk) (abs_nonneg C)

/-- The band weight: `|x| < C_p/ν + 2` gives `(1+|x|)⁴ ≤ (C_p+3)⁴ ν⁻⁴`. -/
theorem wJetP_weight {ν Cp x : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hCp : 0 ≤ Cp)
    (h : |x| < Cp / ν + 2) : (1 + |x|) ^ 4 ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hd : Cp / ν = Cp * ν⁻¹ := div_eq_mul_inv Cp ν
  rw [hd] at h
  have hbound : 1 + |x| ≤ (Cp + 3) * ν⁻¹ := by nlinarith
  calc (1 + |x|) ^ 4 ≤ ((Cp + 3) * ν⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) hbound 4
    _ = (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := by ring

/-- **Weighted pressure jets** (source 5464-5495, 460-478). -/
theorem wJetP_of (h1 : TailW) (h2 : BandP) (h3 : EtaSegment) : WJetP := by
  intro ℓ m
  rcases m with _ | m'
  · -- order `m = 0`: the tail, and the band through `EtaSegment` from the endpoint `η*`
    obtain ⟨Cp, C₁, k₁, a₁, hCp, ha₁, H1⟩ := h1 ℓ 0
    obtain ⟨C₂, k₂, a₂, ha₂, H2⟩ := h2 ℓ 0
    have hX0 : 0 ≤ |C₁| + 2 * (Cp + 2) * |C₂| := by
      have hCp2 : 0 ≤ Cp + 2 := by linarith
      exact add_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hCp2) (abs_nonneg _))
    refine ⟨|C₁| + (Cp + 3) ^ 4 * (|C₁| + 2 * (Cp + 2) * |C₂|), k₁ + k₂ + 5,
      min (min a₁ a₂) 1, lt_min (lt_min ha₁ ha₂) one_pos, ?_⟩
    intro ν hν hνle tr htr s hs hsS z
    have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
    have hνa1 : ν ≤ a₁ := hνle.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hνa2 : ν ≤ a₂ := hνle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
    have ht0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hC1 : 0 ≤ |C₁| := abs_nonneg C₁
    have hX : 0 ≤ (Cp + 3) ^ 4 * (|C₁| + 2 * (Cp + 2) * |C₂|) :=
      mul_nonneg (by positivity) hX0
    have hK : 0 ≤ ν⁻¹ ^ (k₁ + k₂ + 5) := pow_nonneg ht0 _
    have e : (|C₁| + (Cp + 3) ^ 4 * (|C₁| + 2 * (Cp + 2) * |C₂|)) * ν⁻¹ ^ (k₁ + k₂ + 5) =
        |C₁| * ν⁻¹ ^ (k₁ + k₂ + 5) +
          (Cp + 3) ^ 4 * (|C₁| + 2 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 5) := by ring
    rw [e]
    have hC1K : 0 ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 5) := mul_nonneg hC1 hK
    by_cases hcase : Cp / ν + 2 ≤ |z.2|
    · -- tail region
      have h := H1 ν hν hνa1 tr htr s hs hsS z hcase
      have hw : 0 ≤ (1 + |z.2|) ^ 4 := by positivity
      have hp0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z)
      have hψ0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z)
      have hv0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s z)
      have hsub : (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖ ≤
          (1 + |z.2|) ^ 4 * (‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s z‖ +
            ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖ +
            ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hw
      have hm := wJetP_mono hν hν1 C₁ (show k₁ ≤ k₁ + k₂ + 5 by omega)
      have hXK : 0 ≤ (Cp + 3) ^ 4 * (|C₁| + 2 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 5) := mul_nonneg hX hK
      linarith
    · -- band region: `|z.2| < η*`, `η* = C_p/ν + 2`
      rw [not_le] at hcase
      obtain ⟨η, hη⟩ : ∃ η : ℝ, η = Cp / ν + 2 := ⟨_, rfl⟩
      have hCpν : 0 ≤ Cp / ν := div_nonneg hCp.le hν.le
      have hη0 : 0 ≤ η := by linarith
      have hηt : η ≤ (Cp + 2) * ν⁻¹ := by
        rw [hη, div_eq_mul_inv]; nlinarith
      have hcaseη : |z.2| < η := by rw [hη]; exact hcase
      -- the endpoint value, from the tail bound at `(z.1, η*)`
      have hend : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s (z.1, η)‖ ≤ |C₁| * ν⁻¹ ^ k₁ := by
        have hH := H1 ν hν hνa1 tr htr s hs hsS (z.1, η) (by
          show Cp / ν + 2 ≤ |η|
          rw [abs_of_nonneg hη0]
          linarith)
        dsimp only at hH
        have h1le : (1:ℝ) ≤ (1 + |η|) ^ 4 := one_le_pow₀ (by linarith [abs_nonneg η])
        have hsum2 : (1 + |η|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s (z.1, η)‖ ≤
            (1 + |η|) ^ 4 * (‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s (z.1, η)‖ +
              ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s (z.1, η)‖ +
              ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s (z.1, η)‖) :=
          mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s (z.1, η)), norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s (z.1, η))]) (by positivity)
        have hpp : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s (z.1, η)‖ ≤
            (1 + |η|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s (z.1, η)‖ :=
          le_mul_of_one_le_left (norm_nonneg _) h1le
        have hC1le : C₁ * ν⁻¹ ^ k₁ ≤ |C₁| * ν⁻¹ ^ k₁ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₁) (pow_nonneg ht0 _)
        linarith
      -- the `η`-derivative bound: `BandP` at order `0` (its `∂_η` is `m = 1`)
      have hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.p x.1 x.2) (Ioi 0 ×ˢ univ) :=
        tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self (Set.Subset.refl _))
      have hB : ∀ t ∈ uIcc z.2 η,
          ‖UnforcedLeray.Short.PartI.ageJet ℓ 1 tr.p s (z.1, t)‖ ≤ |C₂| * ν⁻¹ ^ k₂ := by
        intro t _
        exact (H2 ν hν hνa2 tr htr s hs hsS (z.1, t)).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C₂) (pow_nonneg ht0 _))
      have hseg := h3 tr.p hF ℓ s hs z.1 z.2 η (|C₂| * ν⁻¹ ^ k₂) hB
      have hseg' : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖ ≤
          ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s (z.1, η)‖ +
            |C₂| * ν⁻¹ ^ k₂ * |z.2 - η| := hseg
      have habs : |z.2 - η| ≤ 2 * ((Cp + 2) * ν⁻¹) := by
        rw [abs_le]
        constructor <;> linarith [neg_abs_le z.2, le_abs_self z.2]
      have hBabs : |C₂| * ν⁻¹ ^ k₂ * |z.2 - η| ≤
          |C₂| * ν⁻¹ ^ k₂ * (2 * ((Cp + 2) * ν⁻¹)) :=
        mul_le_mul_of_nonneg_left habs (mul_nonneg (abs_nonneg _) (pow_nonneg ht0 _))
      have hpz : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖ ≤
          |C₁| * ν⁻¹ ^ k₁ + |C₂| * ν⁻¹ ^ k₂ * (2 * ((Cp + 2) * ν⁻¹)) := by
        linarith
      have hM1 : |C₁| * ν⁻¹ ^ k₁ ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hC1
      have hnn : 0 ≤ 2 * (Cp + 2) * |C₂| :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (abs_nonneg _)
      have hM3 : 2 * (Cp + 2) * |C₂| * ν⁻¹ ^ (k₂ + 1) ≤
          2 * (Cp + 2) * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hnn
      have hpzM : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖ ≤
          (|C₁| + 2 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 1) := by
        calc ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖
            ≤ |C₁| * ν⁻¹ ^ k₁ + |C₂| * ν⁻¹ ^ k₂ * (2 * ((Cp + 2) * ν⁻¹)) := hpz
          _ = |C₁| * ν⁻¹ ^ k₁ + 2 * (Cp + 2) * |C₂| * ν⁻¹ ^ (k₂ + 1) := by ring
          _ ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 1) + 2 * (Cp + 2) * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 1) :=
              add_le_add hM1 hM3
          _ = (|C₁| + 2 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 1) := by ring
      have hw4 : (1 + |z.2|) ^ 4 ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 :=
        wJetP_weight hν hν1 hCp.le (by rw [← hη]; exact hcaseη)
      have hWt : 0 ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := mul_nonneg (by positivity) (pow_nonneg ht0 _)
      have hfin : (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖ ≤
          (Cp + 3) ^ 4 * (|C₁| + 2 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 5) := by
        calc (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖
            ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 * ((|C₁| + 2 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 1)) :=
              mul_le_mul hw4 hpzM (norm_nonneg _) hWt
          _ = (Cp + 3) ^ 4 * (|C₁| + 2 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 5) := by ring
      linarith
  · -- order `m = m'+1`: `BandP` at `ℓ, m'` and `TailW` at `ℓ, m'+1`
    obtain ⟨Cp, C₁, k₁, a₁, hCp, ha₁, H1⟩ := h1 ℓ (m' + 1)
    obtain ⟨C₂, k₂, a₂, ha₂, H2⟩ := h2 ℓ m'
    refine ⟨|C₁| + (Cp + 3) ^ 4 * |C₂|, k₁ + k₂ + 8, min (min a₁ a₂) 1,
      lt_min (lt_min ha₁ ha₂) one_pos, ?_⟩
    intro ν hν hνle tr htr s hs hsS z
    have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
    have hνa1 : ν ≤ a₁ := hνle.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hνa2 : ν ≤ a₂ := hνle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
    have ht0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hK : 0 ≤ ν⁻¹ ^ (k₁ + k₂ + 8) := pow_nonneg ht0 _
    have hC1 : 0 ≤ |C₁| := abs_nonneg C₁
    have hC2 : 0 ≤ (Cp + 3) ^ 4 * |C₂| := mul_nonneg (by positivity) (abs_nonneg C₂)
    have e : (|C₁| + (Cp + 3) ^ 4 * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 8) =
        |C₁| * ν⁻¹ ^ (k₁ + k₂ + 8) + (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 8) := by ring
    rw [e]
    by_cases hcase : Cp / ν + 2 ≤ |z.2|
    · have h := H1 ν hν hνa1 tr htr s hs hsS z hcase
      have hw : 0 ≤ (1 + |z.2|) ^ 4 := by positivity
      have hp0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.p s z)
      have hψ0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.ψ s z)
      have hv0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.v s z)
      have hsub : (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.p s z‖ ≤
          (1 + |z.2|) ^ 4 * (‖UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.v s z‖ +
            ‖UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.p s z‖ +
            ‖UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.ψ s z‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hw
      have hm := wJetP_mono hν hν1 C₁ (show k₁ ≤ k₁ + k₂ + 8 by omega)
      have hC1K' : 0 ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 8) := mul_nonneg hC1 hK
      have hX : 0 ≤ (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 8) := mul_nonneg hC2 hK
      linarith
    · rw [not_le] at hcase
      have hd : Cp / ν = Cp * ν⁻¹ := div_eq_mul_inv Cp ν
      have hbound : 1 + |z.2| ≤ (Cp + 3) * ν⁻¹ := by
        rw [hd] at hcase
        nlinarith
      have hw4 : (1 + |z.2|) ^ 4 ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := by
        calc (1 + |z.2|) ^ 4 ≤ ((Cp + 3) * ν⁻¹) ^ 4 :=
              pow_le_pow_left₀ (by positivity) hbound 4
          _ = (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := by ring
      have hv2 := H2 ν hν hνa2 tr htr s hs hsS z
      have hvm := wJetP_mono hν hν1 C₂ (show k₂ ≤ k₂ + 4 by omega)
      have hA : (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.p s z‖ ≤
          (Cp + 3) ^ 4 * ν⁻¹ ^ 4 * (|C₂| * ν⁻¹ ^ (k₂ + 4)) :=
        mul_le_mul hw4 (le_trans hv2 hvm) (norm_nonneg _)
          (mul_nonneg (by positivity) (pow_nonneg ht0 _))
      have e2 : (Cp + 3) ^ 4 * ν⁻¹ ^ 4 * (|C₂| * ν⁻¹ ^ (k₂ + 4)) =
          (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (4 + k₂ + 4) := by ring
      have hmono : (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (4 + k₂ + 4) ≤
          (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 8) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hC2
      have hC1K' : 0 ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 8) := mul_nonneg hC1 hK
      linarith [hA, e2, hmono, hC1K']

end UnforcedLeray.Short.PartIIIb.Concrete
