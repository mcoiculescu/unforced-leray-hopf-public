import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Defs

/-!
# The fluctuation part of the flat train bound (source 2726-2727, `sct:fluctuation` 439-446)

`TrainFluctuationDecay` (`PartI/StatementsTrain.lean`) gives, at ages `s > 0`, the sup-norm bound
`wSupNorm m (ageJet 0 0 (hfluct c (tr.v ·)) s) ≤ P e^{-κνs/c²}` with `c = ν^{-2}` after the period
transport `trainPeriod 2 ν = (ν²)⁻¹`.  At `c = (ν²)⁻¹` one has `κνs/c² = κν⁵s`, and
`√s e^{-κν⁵s} ≤ (√(κν⁵))⁻¹ ≤ (√κ)⁻¹ ν^{-3}` for `ν ≤ 1`; `W ≤ √(jap m η)`
(`transWeight_le_sqrt_jap`) and `P ≤ |C| 3^N ν^{-2N}` (`polyP_le_of_sq_inv`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Train (jap)

/-- The pointwise value of a weighted sup-norm bound (copy of `PartIIa.lmc_pt_of_sup`). -/
theorem fluct_pt_of_sup {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f : ℝ × ℝ → E) {K : ℝ}
    (hK : 0 ≤ K) (h : UnforcedLeray.Short.PartI.wSupNorm m f ≤ ENNReal.ofReal K) (z : ℝ × ℝ) :
    Real.sqrt (jap m z) * ‖f z‖ ≤ K := by
  have h1 : ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ ≤ ENNReal.ofReal K :=
    le_trans (le_iSup (fun w : ℝ × ℝ => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) z) h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hK] at h1
  exact h1

/-- The zeroth age and spatial jet has the norm of the field (copy of
`PartIIa.lmc_norm_ageJet_zero`). -/
theorem fluct_norm_ageJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → ℝ × ℝ → E) (t : ℝ) (z : ℝ × ℝ) :
    ‖UnforcedLeray.Short.PartI.ageJet 0 0 F t z‖ = ‖F t z‖ := by
  simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero,
    norm_iteratedFDeriv_zero]

/-- **The fluctuation part of the flat train bound** (source 2726-2727; `sct:fluctuation`,
439-446, sup-norm conjunct at `ℓ = j = 0`, `ρ = 2`). -/
theorem flatFluctBound_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay) :
    FlatFluctBound := by
  intro mZ hmZ
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, h⟩ := hF 2 (by norm_num) ⌈mZ⌉₊ 0 0
  refine ⟨|C| * 3 ^ N * (Real.sqrt κ)⁻¹, 2 * N + 3, min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro ν hν c hc
  have hν0 : 0 < ν := hν.1
  have hνa : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  subst hc
  intro tr hbuc p hp
  have hh := h ν hν0 hνa
  rw [trainPeriod_two hν0] at hh
  have hK := (hh tr hbuc p.1 hp).2.1.2
  have hν0inv : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν0.le
  have hP0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ := by
    unfold UnforcedLeray.Short.PartI.polyP
    have : 0 ≤ 1 + (ν ^ 2)⁻¹ + ν⁻¹ := by positivity
    exact mul_nonneg hC.le (pow_nonneg this N)
  have hK0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ *
      Real.exp (-(κ * ν * p.1 / ((ν ^ 2)⁻¹) ^ 2)) := mul_nonneg hP0 (Real.exp_pos _).le
  have hpt : Real.sqrt (jap ⌈mZ⌉₊ p.2) *
      ‖UnforcedLeray.Short.PartI.hfluct (ν ^ 2)⁻¹ (tr.v p.1) p.2‖ ≤
      UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ *
        Real.exp (-(κ * ν * p.1 / ((ν ^ 2)⁻¹) ^ 2)) := by
    have h1 := fluct_pt_of_sup ⌈mZ⌉₊
      (UnforcedLeray.Short.PartI.ageJet 0 0
        (fun r => UnforcedLeray.Short.PartI.hfluct (ν ^ 2)⁻¹ (tr.v r)) p.1) hK0 hK p.2
    rwa [fluct_norm_ageJet_zero] at h1
  have hW : UnforcedLeray.Short.IIIa.transWeight mZ p ≤ Real.sqrt (jap ⌈mZ⌉₊ p.2) :=
    transWeight_le_sqrt_jap hmZ hp.le
  have hF0 : 0 ≤ ‖UnforcedLeray.Short.PartI.hfluct (ν ^ 2)⁻¹ (tr.v p.1) p.2‖ := norm_nonneg _
  have hs0 : 0 ≤ Real.sqrt p.1 := Real.sqrt_nonneg _
  have hexp : κ * ν * p.1 / ((ν ^ 2)⁻¹) ^ 2 = κ * ν ^ 5 * p.1 := by
    field_simp
  have hsq : Real.sqrt p.1 * Real.exp (-((κ * ν ^ 5) * p.1)) ≤
      (Real.sqrt (κ * ν ^ 5))⁻¹ :=
    sqrt_mul_exp_neg_le (mul_pos hκ (pow_pos hν0 5)) hp.le
  have hPC : UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ ≤
      |C| * 3 ^ N * ν⁻¹ ^ (2 * N) :=
    polyP_le_of_sq_inv C N hν0 hν1
  have hsq3 : ν ^ 3 ≤ Real.sqrt (ν ^ 5) := by
    have h6 : (ν ^ 3) ^ 2 ≤ ν ^ 5 := by
      have : (ν ^ 3) ^ 2 = ν ^ 5 * ν := by ring
      rw [this]
      exact mul_le_of_le_one_right (pow_nonneg hν0.le 5) hν1
    calc ν ^ 3 = Real.sqrt ((ν ^ 3) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (ν ^ 5) := Real.sqrt_le_sqrt h6
  have hInv : (Real.sqrt (κ * ν ^ 5))⁻¹ ≤ (Real.sqrt κ)⁻¹ * ν⁻¹ ^ 3 := by
    rw [Real.sqrt_mul hκ.le, mul_inv, inv_pow]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    exact inv_anti₀ (pow_pos hν0 3) hsq3
  calc Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
        ‖UnforcedLeray.Short.PartI.hfluct (ν ^ 2)⁻¹ (tr.v p.1) p.2‖
      ≤ Real.sqrt p.1 * (Real.sqrt (jap ⌈mZ⌉₊ p.2) *
          ‖UnforcedLeray.Short.PartI.hfluct (ν ^ 2)⁻¹ (tr.v p.1) p.2‖) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW hF0) hs0
    _ ≤ Real.sqrt p.1 * (UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ *
          Real.exp (-(κ * ν * p.1 / ((ν ^ 2)⁻¹) ^ 2))) := mul_le_mul_of_nonneg_left hpt hs0
    _ = Real.sqrt p.1 * (UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ *
          Real.exp (-((κ * ν ^ 5) * p.1))) := by rw [hexp]
    _ = UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ *
          (Real.sqrt p.1 * Real.exp (-((κ * ν ^ 5) * p.1))) := by ring
    _ ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ * (Real.sqrt (κ * ν ^ 5))⁻¹ :=
        mul_le_mul_of_nonneg_left hsq hP0
    _ ≤ (|C| * 3 ^ N * ν⁻¹ ^ (2 * N)) * ((Real.sqrt κ)⁻¹ * ν⁻¹ ^ 3) :=
        mul_le_mul hPC hInv (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (mul_nonneg (mul_nonneg (abs_nonneg C) (by positivity)) (pow_nonneg hν0inv _))
    _ = (|C| * 3 ^ N * (Real.sqrt κ)⁻¹) * ν⁻¹ ^ (2 * N + 3) := by
        rw [pow_add]
        ring

end UnforcedLeray.Short.PartIIIb.NearInst
