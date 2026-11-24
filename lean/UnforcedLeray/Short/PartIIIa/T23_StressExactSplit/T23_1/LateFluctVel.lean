import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org

/-!
# `PartIII-a:T23/1/1`: the late fluctuation velocity (`lateFluctVel_of`)

Source of record: `the November 2 reference manuscript` lines 2726-2727 and
439-446 (`sct:fluctuation`). Uses the Part I decay `TrainFluctuationDecay` at `ρ = 2`, `ℓ = j = 0`,
`m = ⌈m_Z⌉₊`, the weight comparison `transWeight_le_sqrt_jap`, and the exponential absorption
`one_add_mul_exp_neg_le` with `a = κ ν^5` (since `c = ν^{-2}`, `κ ν s / c² = κ ν^5 s`).
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-- At `ℓ = j = 0` the jet is the value: `‖ageJet 0 0 F s z‖ = ‖F s z‖`. -/
theorem lfv_norm_ageJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet 0 0 F s z‖ = ‖F s z‖ := by
  unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
  simp [norm_iteratedFDeriv_zero, iteratedDeriv_zero]

/-- Pointwise reading of a weighted sup bound: `√(jap m z) ‖f z‖ ≤ K`. -/
theorem lfv_pointwise_of_wSup {E : Type*} [NormedAddCommGroup E] {m : ℕ}
    {f : UnforcedLeray.Cyl.Plane → E} {K : ℝ} (hK : 0 ≤ K)
    (h : UnforcedLeray.Short.PartI.wSupNorm m f ≤ ENNReal.ofReal K) (z : UnforcedLeray.Cyl.Plane) :
    Real.sqrt (UnforcedLeray.Train.jap m z) * ‖f z‖ ≤ K := by
  have h1 := (le_iSup
    (fun z : UnforcedLeray.Cyl.Plane =>
      ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ) z).trans h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hK).1 h1

theorem lateFluctVel_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay) :
    UnforcedLeray.Short.IIIa.LateFluctVel := by
  intro mZ hmZ
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, H⟩ := hF 2 (by norm_num) ⌈mZ⌉₊ 0 0
  refine ⟨|C| * 3 ^ N * (1 + κ⁻¹), 2 * N + 5, min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro ν hν c hc tr hbuc s hs q η
  have hν0 : 0 < ν := hν.1
  have hνν₀ : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hcT := period_eq_trainPeriod hν0 hc
  subst hcT
  have hH := H ν hν0 hνν₀ tr hbuc s (by linarith)
  dsimp only at hH
  have hsup := hH.2.1.2
  -- the period relation, used only through scalar identities
  have hc2 : UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := hc
  have hc0 : 0 ≤ UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    unfold UnforcedLeray.Short.PartI.trainPeriod
    exact (Real.rpow_pos_of_pos hν0 _).le
  set P := UnforcedLeray.Short.PartI.polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
    with hPdef
  set E := Real.exp (-(κ * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) with hEdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    unfold UnforcedLeray.Short.PartI.polyP
    have : 0 ≤ 1 + UnforcedLeray.Short.PartI.trainPeriod 2 ν + ν⁻¹ := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
      linarith
    exact mul_nonneg hC.le (pow_nonneg this N)
  have hPle : P ≤ |C| * 3 ^ N * ν⁻¹ ^ (2 * N) := by
    rw [hPdef, hc2]
    exact polyP_le_inv_pow C N hν0 hν1
  have hexp : -(κ * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2) =
      -((κ * ν ^ 5) * s) := by
    rw [hc2, inv_pow, div_inv_eq_mul]
    ring
  have hEb : (1 + s) * E ≤ (1 + κ⁻¹) * ν⁻¹ ^ 5 := by
    have ha : 0 < κ * ν ^ 5 := by positivity
    have h1 := one_add_mul_exp_neg_le ha (s := s) (by linarith)
    rw [hEdef, hexp]
    have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0).2 hν1
    have ht5 : 1 ≤ ν⁻¹ ^ 5 := one_le_pow₀ ht
    have hk5 : (κ * ν ^ 5)⁻¹ = κ⁻¹ * ν⁻¹ ^ 5 := by
      rw [mul_inv, ← inv_pow]
    rw [hk5] at h1
    have hκi : 0 ≤ κ⁻¹ := inv_nonneg.2 hκ.le
    nlinarith
  -- the weighted velocity bound at the point `(q, η)`
  have hK0 : 0 ≤ P * E := mul_nonneg hPnn (Real.exp_nonneg _)
  have hz := lfv_pointwise_of_wSup hK0 hsup (q, η)
  rw [lfv_norm_ageJet_zero] at hz
  have hW : transWeight mZ (s, (q, η)) ≤ Real.sqrt (UnforcedLeray.Train.jap ⌈mZ⌉₊ (q, η)) :=
    transWeight_le_sqrt_jap hmZ (p := (s, (q, η))) (by show (0 : ℝ) ≤ s; linarith)
  have hWv : transWeight mZ (s, (q, η)) *
      ‖UnforcedLeray.Short.PartI.hfluct (UnforcedLeray.Short.PartI.trainPeriod 2 ν) (tr.v s) (q, η)‖ ≤
      P * E := by
    calc transWeight mZ (s, (q, η)) *
          ‖UnforcedLeray.Short.PartI.hfluct (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
            (tr.v s) (q, η)‖
        ≤ Real.sqrt (UnforcedLeray.Train.jap ⌈mZ⌉₊ (q, η)) *
          ‖UnforcedLeray.Short.PartI.hfluct (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
            (tr.v s) (q, η)‖ :=
          mul_le_mul_of_nonneg_right hW (norm_nonneg _)
      _ ≤ P * E := hz
  have h1s : 0 < 1 + s := by linarith
  have hsinv : 0 < (1 + s)⁻¹ := inv_pos.2 h1s
  have hcancel : (1 + s)⁻¹ * ((1 + s) * E) = E := by
    rw [← mul_assoc, inv_mul_cancel₀ h1s.ne', one_mul]
  rw [Real.rpow_neg_one]
  calc transWeight mZ (s, (q, η)) *
        ‖UnforcedLeray.Short.PartI.hfluct (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
          (tr.v s) (q, η)‖
      ≤ P * E := hWv
    _ = (1 + s)⁻¹ * ((1 + s) * E) * P := by rw [hcancel]; ring
    _ ≤ (1 + s)⁻¹ * ((1 + κ⁻¹) * ν⁻¹ ^ 5) * P :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEb hsinv.le) hPnn
    _ ≤ (1 + s)⁻¹ * ((1 + κ⁻¹) * ν⁻¹ ^ 5) * (|C| * 3 ^ N * ν⁻¹ ^ (2 * N)) :=
        mul_le_mul_of_nonneg_left hPle (by positivity)
    _ = |C| * 3 ^ N * (1 + κ⁻¹) * ν⁻¹ ^ (2 * N + 5) * (1 + s)⁻¹ := by
        rw [pow_add]; ring

end UnforcedLeray.Short.IIIa
