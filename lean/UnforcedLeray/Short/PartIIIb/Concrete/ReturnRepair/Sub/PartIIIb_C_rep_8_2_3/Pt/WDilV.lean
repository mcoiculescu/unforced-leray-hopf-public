import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/21`: the weighted dilation jets of the velocity, `WDil trainFv`

Source of record: `the November 2 reference manuscript` 5464-5465 (`σ = log s`),
5477-5482 (`𝔴_4`).  Route: `DilJetBound` (chain rule in `σ`), `JointAgeVec` (joint derivatives
from the age jets, `K_i`), and `WJetV` (weighted age jets, uniformized by `tp_unif` over `ℓ, m ≤ 4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- The velocity jet predicate of `WJetV`, as a function of the constants. -/
def VelPred (ℓ m : ℕ) (C : ℝ) (k : ℕ) (a : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ ≤ C * ν⁻¹ ^ k

/-- Monotonicity of `VelPred` in `C ≥ 0`, `k` and the threshold `a' ≤ min a 1`. -/
theorem velPred_mono (ℓ m : ℕ) (C C' : ℝ) (k k' : ℕ) (a a' : ℝ) (hC : C ≤ C') (hC' : 0 ≤ C')
    (hk : k ≤ k') (ha : a' ≤ a) (ha1 : a' ≤ 1) (ha0 : 0 < a') (H : VelPred ℓ m C k a) :
    VelPred ℓ m C' k' a' := by
  intro ν hν hνa tr hb s hs hs1 z
  have hν1 : ν ≤ 1 := hνa.trans ha1
  have hx : (1 : ℝ) ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hpow : ν⁻¹ ^ k ≤ ν⁻¹ ^ k' := pow_le_pow_right₀ hx hk
  have hp : 0 ≤ ν⁻¹ ^ k := by positivity
  have h0 := H ν hν (hνa.trans ha) tr hb s hs hs1 z
  calc (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖
      ≤ C * ν⁻¹ ^ k := h0
    _ ≤ C' * ν⁻¹ ^ k := mul_le_mul_of_nonneg_right hC hp
    _ ≤ C' * ν⁻¹ ^ k' := mul_le_mul_of_nonneg_left hpow hC'

theorem wDilV_of (h1 : DilJetBound) (h2 : JointAgeVec) (h3 : WJetV) : WDil trainFv := by
  unfold DilJetBound at h1
  unfold JointAgeVec at h2
  obtain ⟨C₀, k₀, a₀, hC₀, ha₀, ha₀1, H₀⟩ :=
    tp_unif (P := VelPred) velPred_mono (fun ℓ m => h3 ℓ m) 4
  choose K hK0 hK using h2
  unfold WDil
  refine ⟨24 * 16 * 5 * (∑ i ∈ Finset.range 5, K i) * C₀, k₀ + 4, a₀, ha₀, ?_⟩
  intro L hbuc hLa j hj p hp0 hp1
  have hν : 0 < L.ν := L.ν_pos
  have hν1 : L.ν ≤ 1 := hLa.trans ha₀1
  have hx : (1 : ℝ) ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hX0 : 0 ≤ C₀ * L.ν⁻¹ ^ k₀ := mul_nonneg hC₀ (by positivity)
  have hSK0 : 0 ≤ ∑ i ∈ Finset.range 5, K i :=
    Finset.sum_nonneg fun i _ => hK0 i
  have hp1' : p.1 ≤ L.ν⁻¹ := by rw [← one_div]; exact hp1
  set A : ℝ := (1 + |p.2.2|) ^ 4 with hAdef
  have hA : 0 ≤ A := by positivity
  -- the train velocity is jointly smooth on `(0,∞) × ℝ²`
  have hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => L.train.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    L.train.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Set.Subset.rfl)
  -- the dilation chain rule (`DilJetBound`)
  have hD : ‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ ≤
      (j.factorial : ℝ) * (∑ i ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖) *
        (1 + p.1) ^ j :=
    h1 _ (fun x : ℝ × Plane => L.train.v x.1 x.2) hG j p.1 hp0 p.2
  -- per-order bound of the weighted joint derivative, via the age jets and `VelPred`
  have hterm : ∀ i ∈ Finset.range (j + 1),
      A * ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖ ≤
        5 * K i * (C₀ * L.ν⁻¹ ^ k₀) := by
    intro i hi
    have hi5 : i ≤ 4 := by have := Finset.mem_range.1 hi; omega
    have hKi := hK i L.train.v hG (p.1, p.2) hp0
    have hsum : ∀ ℓ ∈ Finset.range (i + 1),
        A * ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) L.train.v p.1 p.2‖ ≤ C₀ * L.ν⁻¹ ^ k₀ := by
      intro ℓ hℓ
      have hℓ' : ℓ ≤ i := by have := Finset.mem_range.1 hℓ; omega
      exact H₀ ℓ (i - ℓ) (by omega) (by omega) L.ν hν hLa L.train hbuc p.1 hp0 hp1 p.2
    calc A * ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖
        ≤ A * (K i * ∑ ℓ ∈ Finset.range (i + 1),
            ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) L.train.v p.1 p.2‖) :=
          mul_le_mul_of_nonneg_left hKi hA
      _ = K i * (A * ∑ ℓ ∈ Finset.range (i + 1),
            ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) L.train.v p.1 p.2‖) := by ring
      _ ≤ K i * ∑ ℓ ∈ Finset.range (i + 1), (C₀ * L.ν⁻¹ ^ k₀) :=
          mul_le_mul_of_nonneg_left (by rw [Finset.mul_sum]; exact Finset.sum_le_sum hsum)
            (hK0 i)
      _ = K i * (((i + 1 : ℕ) : ℝ) * (C₀ * L.ν⁻¹ ^ k₀)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (K i * (C₀ * L.ν⁻¹ ^ k₀)) := by
          have hcast : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
            exact_mod_cast (show i + 1 ≤ 5 by omega)
          have hm := mul_le_mul_of_nonneg_right hcast (mul_nonneg (hK0 i) hX0)
          calc K i * (((i + 1 : ℕ) : ℝ) * (C₀ * L.ν⁻¹ ^ k₀))
              = ((i + 1 : ℕ) : ℝ) * (K i * (C₀ * L.ν⁻¹ ^ k₀)) := by ring
            _ ≤ 5 * (K i * (C₀ * L.ν⁻¹ ^ k₀)) := hm
      _ = 5 * K i * (C₀ * L.ν⁻¹ ^ k₀) := by ring
  -- sum over the orders `i ≤ j < 5`, dominated by the sum over `range 5`
  have hST : ∑ i ∈ Finset.range (j + 1),
      A * ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖ ≤
        5 * (∑ i ∈ Finset.range 5, K i) * (C₀ * L.ν⁻¹ ^ k₀) := by
    have hsub : ∑ i ∈ Finset.range (j + 1),
        5 * K i * (C₀ * L.ν⁻¹ ^ k₀) ≤
        ∑ i ∈ Finset.range 5, 5 * K i * (C₀ * L.ν⁻¹ ^ k₀) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        have := Finset.mem_range.1 hi
        exact Finset.mem_range.2 (by omega)
      · intro i _ _
        exact mul_nonneg (mul_nonneg (by norm_num) (hK0 i)) hX0
    calc _ ≤ ∑ i ∈ Finset.range (j + 1), 5 * K i * (C₀ * L.ν⁻¹ ^ k₀) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ i ∈ Finset.range 5, 5 * K i * (C₀ * L.ν⁻¹ ^ k₀) := hsub
      _ = 5 * (∑ i ∈ Finset.range 5, K i) * (C₀ * L.ν⁻¹ ^ k₀) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- the factorial and the dilation power
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ 24 := by
    have h24 : j.factorial ≤ 24 :=
      (Nat.factorial_le (show j ≤ 4 by omega)).trans (by norm_num [Nat.factorial])
    exact_mod_cast h24
  have hpowN : (1 + p.1) ^ j ≤ 16 * L.ν⁻¹ ^ 4 := by
    have h1s : 1 + p.1 ≤ 2 * L.ν⁻¹ := by linarith
    have hj4 : (1 + p.1) ^ j ≤ (1 + p.1) ^ 4 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h2s : (1 + p.1) ^ 4 ≤ (2 * L.ν⁻¹) ^ 4 :=
      pow_le_pow_left₀ (by linarith) h1s 4
    have h3s : (2 * L.ν⁻¹) ^ 4 = 16 * L.ν⁻¹ ^ 4 := by ring
    linarith
  have hT0 : 0 ≤ ∑ i ∈ Finset.range (j + 1),
      A * ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg hA (norm_nonneg _)
  have hAsum : A * ∑ i ∈ Finset.range (j + 1),
      ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖ =
      ∑ i ∈ Finset.range (j + 1),
        A * ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖ :=
    Finset.mul_sum _ _ _
  have key : (j.factorial : ℝ) * (∑ i ∈ Finset.range (j + 1),
      A * ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖) *
      (1 + p.1) ^ j ≤
      24 * (5 * (∑ i ∈ Finset.range 5, K i) * (C₀ * L.ν⁻¹ ^ k₀)) * (16 * L.ν⁻¹ ^ 4) := by
    apply mul_le_mul
    · exact mul_le_mul hfac hST hT0 (by norm_num)
    · exact hpowN
    · exact pow_nonneg (by linarith) _
    · exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hSK0) hX0)
  calc A * ‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖
      ≤ A * ((j.factorial : ℝ) * (∑ i ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖) *
        (1 + p.1) ^ j) := mul_le_mul_of_nonneg_left hD hA
    _ = (j.factorial : ℝ) * (A * ∑ i ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖) *
        (1 + p.1) ^ j := by ring
    _ = (j.factorial : ℝ) * (∑ i ∈ Finset.range (j + 1),
        A * ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => L.train.v x.1 x.2) (p.1, p.2)‖) *
        (1 + p.1) ^ j := by rw [hAsum]
    _ ≤ 24 * (5 * (∑ i ∈ Finset.range 5, K i) * (C₀ * L.ν⁻¹ ^ k₀)) * (16 * L.ν⁻¹ ^ 4) := key
    _ = 24 * 16 * 5 * (∑ i ∈ Finset.range 5, K i) * C₀ * L.ν⁻¹ ^ (k₀ + 4) := by
        rw [pow_add]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
