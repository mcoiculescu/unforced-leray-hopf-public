import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1

/-!
# Weighted age-jets of the fluctuation `ψ̃ = ψ - S` (source 439-446, `ρ = 2`, `m = 3`)

Proves `bgFluctWeighted_of`: from `PartI.TrainFluctuationDecay` (`sct:fluctuation`) the weighted
bound `BgFluctWeighted` for the train `p.train` with period `p.c = (p.ν²)⁻¹ = trainPeriod 2 p.ν`.
Finitely many `(ℓ, j)` with `ℓ + j ≤ 3` are combined by a finite infimum of the thresholds and a
finite sum of the constants.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI (ageJet meanStream polyP wSupNorm TrainFluctuationDecay IsBUCTrain)

/-- `trainPeriod 2 ν = (ν²)⁻¹`. -/
theorem fluct_trainPeriod_two_eq_inv {ν : ℝ} (hν : 0 < ν) :
    UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
  unfold UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

theorem fluct_polyP_nonneg {C : ℝ} {N : ℕ} {ν c : ℝ} (hC : 0 ≤ C) (hν : 0 < ν) (hc : 0 ≤ c) :
    0 ≤ polyP C N ν c := by
  unfold polyP
  have h1 : 0 ≤ 1 + c + ν⁻¹ := by
    have := inv_nonneg.2 hν.le
    linarith
  exact mul_nonneg hC (pow_nonneg h1 N)

/-- The weight comparison `(1+|η|)³ ≤ 3 √(jap 3 z)`. -/
theorem fluct_weight_le (z : Plane) :
    (1 + |z.2|) ^ 3 ≤ 3 * Real.sqrt (UnforcedLeray.Train.jap 3 z) := by
  have hb0 : 0 ≤ Real.sqrt (1 + z.2 ^ 2) := Real.sqrt_nonneg _
  have hb2 : Real.sqrt (1 + z.2 ^ 2) ^ 2 = 1 + z.2 ^ 2 := Real.sq_sqrt (by positivity)
  have hjap : UnforcedLeray.Train.jap 3 z = (Real.sqrt (1 + z.2 ^ 2) ^ 3) ^ 2 := by
    unfold UnforcedLeray.Train.jap
    rw [show (Real.sqrt (1 + z.2 ^ 2) ^ 3) ^ 2 = (Real.sqrt (1 + z.2 ^ 2) ^ 2) ^ 3 by ring, hb2]
  rw [hjap, Real.sqrt_sq (by positivity)]
  have ha0 : 0 ≤ 1 + |z.2| := by positivity
  have habs : |z.2| ^ 2 = z.2 ^ 2 := sq_abs _
  have h1 : (1 + |z.2|) ^ 2 ≤ 2 * Real.sqrt (1 + z.2 ^ 2) ^ 2 := by
    rw [hb2]
    nlinarith [sq_nonneg (|z.2| - 1), habs]
  have h2 : 1 + |z.2| ≤ 3 / 2 * Real.sqrt (1 + z.2 ^ 2) := by
    nlinarith [h1, hb0, sq_nonneg (Real.sqrt (1 + z.2 ^ 2))]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha0,
    mul_le_mul_of_nonneg_right h2 (sq_nonneg (Real.sqrt (1 + z.2 ^ 2)))]

theorem fluct_enn_to_real {E : Type*} [NormedAddCommGroup E] {a b : ℝ} {x : E}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ENNReal.ofReal a * ‖x‖ₑ ≤ ENNReal.ofReal b) :
    a * ‖x‖ ≤ b := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul ha] at h
  exact (ENNReal.ofReal_le_ofReal_iff hb).1 h

theorem fluct_wSup_pt {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f : Plane → E) (K : ℝ≥0∞)
    (h : wSupNorm m f ≤ K) (z : Plane) :
    ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ ≤ K :=
  le_trans (le_iSup (fun z : Plane => ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ) z) h

/-- One pair `(ℓ, j)`: the threshold `ν₀` and the constants `C, N` of `TrainFluctuationDecay` at
`ρ = 2`, `m = 3`, turned into a pointwise weighted bound for the fluctuation of `ψ`. -/
theorem fluct_pointwise (hF : TrainFluctuationDecay) (ℓ j : ℕ) :
    ∃ (C : ℝ) (N : ℕ) (nu0 : ℝ), 0 < C ∧ 0 < nu0 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ nu0 → ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            (1 + |z.2|) ^ 3 * ‖ageJet ℓ j (fun r z => tr.ψ r z - meanStream tr r z.2) s z‖
              ≤ 3 * polyP C N ν c := by
  obtain ⟨C, N, κ, nu0, hC, hκ, hnu0, H⟩ := hF 2 (by norm_num) 3 ℓ j
  refine ⟨C, N, nu0, hC, hnu0, ?_⟩
  intro ν hν hνν0 c hc tr htr s hs z
  have hc' : c = UnforcedLeray.Short.PartI.trainPeriod 2 ν :=
    hc.trans (fluct_trainPeriod_two_eq_inv hν).symm
  subst hc'
  obtain ⟨⟨_, hB⟩, _⟩ := H ν hν hνν0 tr htr s hs
  have hpt := fluct_wSup_pt 3 _ _ hB z
  have hcnn : 0 ≤ UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    unfold UnforcedLeray.Short.PartI.trainPeriod
    exact Real.rpow_nonneg hν.le _
  have hexp : Real.exp (-(κ * ν * s / UnforcedLeray.Short.PartI.trainPeriod 2 ν ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.2 (div_nonneg (mul_nonneg (mul_nonneg hκ.le hν.le) hs.le) (sq_nonneg _))
  have hK' : 0 ≤ polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ * ν * s / UnforcedLeray.Short.PartI.trainPeriod 2 ν ^ 2)) :=
    mul_nonneg (fluct_polyP_nonneg hC.le hν hcnn) (Real.exp_pos _).le
  have hreal := fluct_enn_to_real (Real.sqrt_nonneg _) hK' hpt
  calc (1 + |z.2|) ^ 3 * ‖ageJet ℓ j (fun r z => tr.ψ r z - meanStream tr r z.2) s z‖
      ≤ (3 * Real.sqrt (UnforcedLeray.Train.jap 3 z)) *
          ‖ageJet ℓ j (fun r z => tr.ψ r z - meanStream tr r z.2) s z‖ :=
        mul_le_mul_of_nonneg_right (fluct_weight_le z) (norm_nonneg _)
    _ = 3 * (Real.sqrt (UnforcedLeray.Train.jap 3 z) *
          ‖ageJet ℓ j (fun r z => tr.ψ r z - meanStream tr r z.2) s z‖) := by ring
    _ ≤ 3 * (polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-(κ * ν * s / UnforcedLeray.Short.PartI.trainPeriod 2 ν ^ 2))) :=
        mul_le_mul_of_nonneg_left hreal (by norm_num)
    _ ≤ 3 * polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
        mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right (fluct_polyP_nonneg hC.le hν hcnn) hexp) (by norm_num)

/-- **Weighted age-jets of the fluctuation `ψ̃ = ψ - S`** (source 439-446, `ρ = 2`, `m = 3`). -/
theorem bgFluctWeighted_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay) :
    BgFluctWeighted := by
  intro dm dp hdm
  have key : ∀ ℓ j : ℕ, ∃ (C : ℝ) (N : ℕ) (nu0 : ℝ), 0 < C ∧ 0 < nu0 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ nu0 → ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            (1 + |z.2|) ^ 3 * ‖ageJet ℓ j (fun r z => tr.ψ r z - meanStream tr r z.2) s z‖
              ≤ 3 * polyP C N ν c :=
    fun ℓ j => fluct_pointwise hF ℓ j
  choose C N nu0 hC hnu0 H using key
  have hne : (Finset.range 4 ×ˢ Finset.range 4).Nonempty := ⟨(0, 0), by simp⟩
  refine ⟨(Finset.range 4 ×ˢ Finset.range 4).inf' hne (fun q => nu0 q.1 q.2), ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro q _
    exact hnu0 q.1 q.2
  · intro p d hreg hν
    have hνle : ∀ q ∈ Finset.range 4 ×ˢ Finset.range 4, p.ν ≤ nu0 q.1 q.2 :=
      fun q hq => le_trans hν (Finset.inf'_le _ hq)
    refine ⟨∑ q ∈ Finset.range 4 ×ˢ Finset.range 4,
      3 * polyP (C q.1 q.2) (N q.1 q.2) p.ν p.c, ?_⟩
    intro ℓ j hℓj s hs z
    have hmem : (ℓ, j) ∈ Finset.range 4 ×ˢ Finset.range 4 :=
      Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
    have h1 := H ℓ j p.ν p.ν_pos (hνle _ hmem) p.c hreg.c_eq p.train hreg.train_buc s hs z
    refine le_trans h1 ?_
    exact Finset.single_le_sum
      (f := fun q : ℕ × ℕ => 3 * polyP (C q.1 q.2) (N q.1 q.2) p.ν p.c)
      (fun q _ => mul_nonneg (by norm_num)
        (fluct_polyP_nonneg (hC q.1 q.2).le p.ν_pos p.c_pos.le)) hmem

end UnforcedLeray.Short.PartIIIb.Concrete
