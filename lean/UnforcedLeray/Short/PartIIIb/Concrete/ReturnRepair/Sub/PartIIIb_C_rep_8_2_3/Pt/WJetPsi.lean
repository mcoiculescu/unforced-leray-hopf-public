import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartI.Sub.T01

/-!
# `PartIII-b:C/rep/8/2/3/2/20`: the weighted stream jets `WJetPsi`

Source of record: `the November 2 reference manuscript` 2045-2051, 5464-5465,
5484-5495, 460-478.
* The stream pair `IsStreamPair tr.ψ tr.v` (`ψ` smooth by `TrainStreamSmooth`, `v` by the train,
  the stream identity by `IsTrain.stream`).
* Spatial order `m = m'+1`: `StreamShift` gives `‖∂_s^ℓ D^{m'+1}ψ‖ ≤ 2‖∂_s^ℓ D^{m'} v‖`, and the
  weighted velocity jet `WJetV` at `m'` gives the bound.
* Order `m = 0`: the tail region by `TailW` (the `ψ` term); the band region by `EtaSegment` for
  `F = tr.ψ` from the endpoint `η* = C_p/ν + 2`, with the `η`-derivative bounded by
  `StreamShift` at `m = 0` and `SupV` for `v`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- The stream pair of a BUC train at `c = cOf ν`. -/
theorem wJetPsi_pair {hS : UnforcedLeray.Short.PartI.TrainStreamSmooth} {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    UnforcedLeray.Short.IIb.IsStreamPair tr.ψ tr.v :=
  ⟨hS ν (cOf ν) hν (inv_pos.2 (pow_pos hν 2)) tr htr,
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self (Set.Subset.refl _)),
    fun s hs z => tr.isTrain.stream s hs.le z⟩

/-- Monotonicity of the power bound in the exponent, `t = ν⁻¹ ≥ 1`. -/
theorem wJetPsi_mono {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (C : ℝ) {k K : ℕ} (hk : k ≤ K) :
    C * ν⁻¹ ^ k ≤ |C| * ν⁻¹ ^ K := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  calc C * ν⁻¹ ^ k ≤ |C| * ν⁻¹ ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (inv_nonneg.2 hν.le) _)
    _ ≤ |C| * ν⁻¹ ^ K := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hk) (abs_nonneg C)

/-- The band weight: `|x| < C_p/ν + 2` gives `(1+|x|)⁴ ≤ (C_p+3)⁴ ν⁻⁴`. -/
theorem wJetPsi_weight {ν Cp x : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (h : |x| < Cp / ν + 2) : (1 + |x|) ^ 4 ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hd : Cp / ν = Cp * ν⁻¹ := div_eq_mul_inv Cp ν
  rw [hd] at h
  have hbound : 1 + |x| ≤ (Cp + 3) * ν⁻¹ := by nlinarith
  calc (1 + |x|) ^ 4 ≤ ((Cp + 3) * ν⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) hbound 4
    _ = (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := by ring

/-- **Weighted stream jets** (source 2045-2051, 5464-5495, 460-478). -/
theorem wJetPsi_of (hS : UnforcedLeray.Short.PartI.TrainStreamSmooth) (h0 : WJetV) (h1 : TailW)
    (h2 : SupV) (h3 : StreamShift) (h4 : EtaSegment) : WJetPsi := by
  intro ℓ m
  rcases m with _ | m'
  · -- order `m = 0`
    obtain ⟨Cp, C₁, k₁, a₁, hCp, ha₁, H1⟩ := h1 ℓ 0
    obtain ⟨C₂, k₂, a₂, ha₂, H2⟩ := h2 ℓ 0
    have hX0 : 0 ≤ |C₁| + 4 * (Cp + 2) * |C₂| := by
      have hCp2 : 0 ≤ Cp + 2 := by linarith
      exact add_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hCp2) (abs_nonneg _))
    refine ⟨|C₁| + (Cp + 3) ^ 4 * (|C₁| + 4 * (Cp + 2) * |C₂|), k₁ + k₂ + 5,
      min (min a₁ a₂) 1, lt_min (lt_min ha₁ ha₂) one_pos, ?_⟩
    intro ν hν hνle tr htr s hs hsS z
    have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
    have hνa1 : ν ≤ a₁ := hνle.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hνa2 : ν ≤ a₂ := hνle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
    have ht0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hC1 : 0 ≤ |C₁| := abs_nonneg C₁
    have hX : 0 ≤ (Cp + 3) ^ 4 * (|C₁| + 4 * (Cp + 2) * |C₂|) :=
      mul_nonneg (by positivity) hX0
    have hK : 0 ≤ ν⁻¹ ^ (k₁ + k₂ + 5) := pow_nonneg ht0 _
    have e : (|C₁| + (Cp + 3) ^ 4 * (|C₁| + 4 * (Cp + 2) * |C₂|)) * ν⁻¹ ^ (k₁ + k₂ + 5) =
        |C₁| * ν⁻¹ ^ (k₁ + k₂ + 5) +
          (Cp + 3) ^ 4 * (|C₁| + 4 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 5) := by ring
    rw [e]
    have hC1K : 0 ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 5) := mul_nonneg hC1 hK
    have hXK : 0 ≤ (Cp + 3) ^ 4 * (|C₁| + 4 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 5) :=
      mul_nonneg hX hK
    have hpair := wJetPsi_pair (hS := hS) hν tr htr
    by_cases hcase : Cp / ν + 2 ≤ |z.2|
    · -- tail region
      have h := H1 ν hν hνa1 tr htr s hs hsS z hcase
      have hw : 0 ≤ (1 + |z.2|) ^ 4 := by positivity
      have hp0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z)
      have hψ0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z)
      have hv0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s z)
      have hsub : (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖ ≤
          (1 + |z.2|) ^ 4 * (‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s z‖ +
            ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s z‖ +
            ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hw
      have hm := wJetPsi_mono hν hν1 C₁ (show k₁ ≤ k₁ + k₂ + 5 by omega)
      linarith
    · -- band region
      rw [not_le] at hcase
      obtain ⟨η, hη⟩ : ∃ η : ℝ, η = Cp / ν + 2 := ⟨_, rfl⟩
      have hCpν : 0 ≤ Cp / ν := div_nonneg hCp.le hν.le
      have hη0 : 0 ≤ η := by linarith
      have hηt : η ≤ (Cp + 2) * ν⁻¹ := by
        rw [hη, div_eq_mul_inv]; nlinarith
      have hcaseη : |z.2| < η := by rw [hη]; exact hcase
      have hend : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s (z.1, η)‖ ≤ |C₁| * ν⁻¹ ^ k₁ := by
        have hH := H1 ν hν hνa1 tr htr s hs hsS (z.1, η) (by
          show Cp / ν + 2 ≤ |η|
          rw [abs_of_nonneg hη0]
          linarith)
        dsimp only at hH
        have h1le : (1:ℝ) ≤ (1 + |η|) ^ 4 := one_le_pow₀ (by linarith [abs_nonneg η])
        have hsum2 : (1 + |η|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s (z.1, η)‖ ≤
            (1 + |η|) ^ 4 * (‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s (z.1, η)‖ +
              ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s (z.1, η)‖ +
              ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s (z.1, η)‖) :=
          mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s (z.1, η)), norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.p s (z.1, η))]) (by positivity)
        have hpp : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s (z.1, η)‖ ≤
            (1 + |η|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s (z.1, η)‖ :=
          le_mul_of_one_le_left (norm_nonneg _) h1le
        have hC1le : C₁ * ν⁻¹ ^ k₁ ≤ |C₁| * ν⁻¹ ^ k₁ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₁) (pow_nonneg ht0 _)
        linarith
      have hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
        hS ν (cOf ν) hν (inv_pos.2 (pow_pos hν 2)) tr htr
      have hB : ∀ t ∈ uIcc z.2 η,
          ‖UnforcedLeray.Short.PartI.ageJet ℓ 1 tr.ψ s (z.1, t)‖ ≤ 2 * (|C₂| * ν⁻¹ ^ k₂) := by
        intro t _
        have hp : ‖UnforcedLeray.Short.PartI.ageJet ℓ 1 tr.ψ s (z.1, t)‖ ≤
            2 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s (z.1, t)‖ :=
          h3 tr.ψ tr.v hpair ℓ 0 s hs (z.1, t)
        have hv := (H2 ν hν hνa2 tr htr s hs hsS (z.1, t)).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C₂) (pow_nonneg ht0 _))
        linarith
      have hseg := h4 tr.ψ hF ℓ s hs z.1 z.2 η (2 * (|C₂| * ν⁻¹ ^ k₂)) hB
      have hseg' : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖ ≤
          ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s (z.1, η)‖ +
            2 * (|C₂| * ν⁻¹ ^ k₂) * |z.2 - η| := hseg
      have habs : |z.2 - η| ≤ 2 * ((Cp + 2) * ν⁻¹) := by
        rw [abs_le]
        constructor <;> linarith [neg_abs_le z.2, le_abs_self z.2]
      have hBabs : 2 * (|C₂| * ν⁻¹ ^ k₂) * |z.2 - η| ≤
          2 * (|C₂| * ν⁻¹ ^ k₂) * (2 * ((Cp + 2) * ν⁻¹)) :=
        mul_le_mul_of_nonneg_left habs
          (mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) (pow_nonneg ht0 _)))
      have hpz : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖ ≤
          |C₁| * ν⁻¹ ^ k₁ + 2 * (|C₂| * ν⁻¹ ^ k₂) * (2 * ((Cp + 2) * ν⁻¹)) := by
        linarith
      have hM1 : |C₁| * ν⁻¹ ^ k₁ ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hC1
      have hnn : 0 ≤ 4 * (Cp + 2) * |C₂| :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (abs_nonneg _)
      have hM3 : 4 * (Cp + 2) * |C₂| * ν⁻¹ ^ (k₂ + 1) ≤
          4 * (Cp + 2) * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hnn
      have hpzM : ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖ ≤
          (|C₁| + 4 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 1) := by
        calc ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖
            ≤ |C₁| * ν⁻¹ ^ k₁ + 2 * (|C₂| * ν⁻¹ ^ k₂) * (2 * ((Cp + 2) * ν⁻¹)) := hpz
          _ = |C₁| * ν⁻¹ ^ k₁ + 4 * (Cp + 2) * |C₂| * ν⁻¹ ^ (k₂ + 1) := by ring
          _ ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 1) + 4 * (Cp + 2) * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 1) :=
              add_le_add hM1 hM3
          _ = (|C₁| + 4 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 1) := by ring
      have hw4 : (1 + |z.2|) ^ 4 ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 :=
        wJetPsi_weight hν hν1 (by rw [← hη]; exact hcaseη)
      have hWt : 0 ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := mul_nonneg (by positivity) (pow_nonneg ht0 _)
      have hfin : (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖ ≤
          (Cp + 3) ^ 4 * (|C₁| + 4 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 5) := by
        calc (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.ψ s z‖
            ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 * ((|C₁| + 4 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 1)) :=
              mul_le_mul hw4 hpzM (norm_nonneg _) hWt
          _ = (Cp + 3) ^ 4 * (|C₁| + 4 * (Cp + 2) * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 5) := by ring
      linarith
  · -- order `m = m'+1`: `StreamShift` and `WJetV` at `m'` (no transverse weight is needed)
    obtain ⟨C₀, kv, av, hav, H0⟩ := h0 ℓ m'
    refine ⟨2 * |C₀|, kv, av, hav, ?_⟩
    intro ν hν hνa tr htr s hs hsS z
    have ht0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hw : 0 ≤ (1 + |z.2|) ^ 4 := by positivity
    have hpsi := h3 tr.ψ tr.v (wJetPsi_pair (hS := hS) hν tr htr) ℓ m' s hs z
    have hv := H0 ν hν hνa tr htr s hs hsS z
    have hC0 : C₀ * ν⁻¹ ^ kv ≤ |C₀| * ν⁻¹ ^ kv :=
      mul_le_mul_of_nonneg_right (le_abs_self C₀) (pow_nonneg ht0 _)
    calc (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ (m' + 1) tr.ψ s z‖
        ≤ (1 + |z.2|) ^ 4 * (2 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m' tr.v s z‖) :=
          mul_le_mul_of_nonneg_left hpsi hw
      _ = 2 * ((1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m' tr.v s z‖) := by ring
      _ ≤ 2 * (C₀ * ν⁻¹ ^ kv) := mul_le_mul_of_nonneg_left hv (by norm_num)
      _ ≤ 2 * (|C₀| * ν⁻¹ ^ kv) := mul_le_mul_of_nonneg_left hC0 (by norm_num)
      _ = 2 * |C₀| * ν⁻¹ ^ kv := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
