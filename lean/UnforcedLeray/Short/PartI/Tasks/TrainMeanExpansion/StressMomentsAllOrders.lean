import UnforcedLeray.Short.PartI.Sub.PartI_T23

/-!
# `PartI:T23/1`: all-order spatial and time moment integrability of `meanStress` at fixed parameters

Source of record: `the November 2 reference manuscript`, lines 427-435, 450-456,
528-530.

This file proves `trainMeanStressMomentsAllOrders_proof`:
given `hTails : TrainStreamVelocityPressureTails` and `hFD : TrainFluctuationDecay`, for every
`ρ > 1/2` there exists a single smallness threshold `ν₀ > 0` (chosen from the base `(0, 0)` order
of `hTails.2.1` and `(0, 0, 0)` order of `hFD`) such that for all `0 < ν ≤ ν₀`, every `BUC` train
`tr` at period `c = trainPeriod ρ ν`, and every `k : ℕ`:
1. `η ↦ η^{2k} * meanStress tr t η` is integrable on `ℝ` for all `t > 0`, and
2. `t ↦ ∫ η, η^{2k} * meanStress tr t η` is integrable on `Ioi 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

namespace StressMomentsAllOrders

/-- If `0 ≤ X`, `0 ≤ A`, `0 ≤ B`, `X ≤ A ^ 2`, and `X ≤ B ^ 2`, then `X ≤ A * B`. -/
private theorem le_mul_of_le_sq {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : X ≤ A ^ 2) (h2 : X ≤ B ^ 2) : X ≤ A * B := by
  have hsq : X ^ 2 ≤ (A * B) ^ 2 := by
    calc X ^ 2 = X * X := sq X
      _ ≤ A ^ 2 * B ^ 2 := mul_le_mul h1 h2 hX (sq_nonneg A)
      _ = (A * B) ^ 2 := (mul_pow A B 2).symm
  exact (abs_le_of_sq_le_sq' hsq (mul_nonneg hA hB)).2

/-- For `x ≥ 0` and `α > 0`, `(1 + x) ^ (m + 1) ≤ (1 + ((m + 1 : ℕ) : ℝ) / α) ^ (m + 1) * exp (α * x)`. -/
private theorem one_add_pow_le_exp {x α : ℝ} (hx : 0 ≤ x) (hα : 0 < α) (m : ℕ) :
    (1 + x) ^ (m + 1) ≤ (1 + (((m + 1 : ℕ) : ℝ) / α)) ^ (m + 1) * Real.exp (α * x) := by
  set M : ℝ := ((m + 1 : ℕ) : ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  set δ : ℝ := α / M
  have hδ : 0 < δ := div_pos hα hM
  have hδ_inv : δ⁻¹ = M / α := inv_div α M
  have h1 : 1 + x ≤ (1 + δ⁻¹) * (1 + δ * x) := by
    have hmul : δ⁻¹ * (δ * x) = x := by field_simp [hδ.ne']
    have hnn1 : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
    have hnn2 : 0 ≤ δ * x := mul_nonneg hδ.le hx
    nlinarith
  have h2 : 1 + δ * x ≤ Real.exp (δ * x) := by
    linarith [Real.add_one_le_exp (δ * x)]
  have h3 : 1 + x ≤ (1 + (M / α)) * Real.exp (δ * x) := by
    rw [← hδ_inv]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  calc (1 + x) ^ (m + 1)
      ≤ ((1 + (M / α)) * Real.exp (δ * x)) ^ (m + 1) :=
        pow_le_pow_left₀ (by positivity) h3 (m + 1)
    _ = (1 + (M / α)) ^ (m + 1) * (Real.exp (δ * x)) ^ (m + 1) := mul_pow _ _ _
    _ = (1 + (M / α)) ^ (m + 1) * Real.exp (α * x) := by
        congr 1
        rw [← Real.exp_nat_mul]
        congr 1
        change M * (α / M * x) = α * x
        field_simp [hM.ne']

/-- Pointwise bound on `meanStress tr t η` from a uniform bound on `‖tr.v t (q, η)‖`. -/
private theorem norm_meanStress_le_of_norm_v_le {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {t η M : ℝ} (_hM : 0 ≤ M)
    (hv : ∀ q : ℝ, ‖tr.v t (q, η)‖ ≤ M) :
    ‖meanStress tr t η‖ ≤ M ^ 2 := by
  unfold meanStress hmean
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
  have hbd : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖tr.v t (q, η) 0 * tr.v t (q, η) 1‖ ≤ M ^ 2 := by
    intro q _
    rw [norm_mul]
    have h0 := PiLp.norm_apply_le (tr.v t (q, η)) 0
    have h1 := PiLp.norm_apply_le (tr.v t (q, η)) 1
    calc ‖tr.v t (q, η) 0‖ * ‖tr.v t (q, η) 1‖
        ≤ ‖tr.v t (q, η)‖ * ‖tr.v t (q, η)‖ :=
          mul_le_mul h0 h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖tr.v t (q, η)‖ ^ 2 := (sq _).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hv q) 2
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (-c / 2) (c / 2)) measure_Ioc_lt_top hbd
  rw [Real.volume_real_Ioc_of_le (by linarith)] at hint
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 0 * tr.v t (q, η) 1‖
      ≤ c⁻¹ * (M ^ 2 * (c / 2 - -c / 2)) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hc.le)
    _ = M ^ 2 := by
        rw [show c / 2 - -c / 2 = c by ring]
        field_simp [hc.ne']

/-- Combining the linear and Gaussian transverse tail exponentials into a single linear exponential
in `l ≥ 0` with denominator `D = c + C₀ + ν * t`. -/
private theorem tail_exp_sum_le {b c C₀ ν t l : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hC₀ : 0 < C₀) (hν : 0 < ν) (ht : 0 < t) (hl : 0 ≤ l) :
    Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * t))) ≤
      (1 + Real.exp (b / C₀)) * Real.exp (-(b * l / (c + C₀ + ν * t))) := by
  set D : ℝ := c + C₀ + ν * t
  have hνt : 0 < ν * t := mul_pos hν ht
  have hCt : 0 < C₀ + ν * t := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have h1 : Real.exp (-(b * l / c)) ≤ Real.exp (-(b * l / D)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) hc (by dsimp [D]; linarith)
  have h2_exp : -(b * l ^ 2 / (C₀ + ν * t)) ≤ b / C₀ - b * l / D := by
    rcases le_total l 1 with hl1 | hl1
    · have h_le : b * l / D ≤ b / C₀ := by
        calc b * l / D ≤ b * 1 / D := by gcongr
          _ = b / D := by ring
          _ ≤ b / C₀ := div_le_div_of_nonneg_left hb.le hC₀ (by dsimp [D]; linarith)
      have h_nn : 0 ≤ b * l ^ 2 / (C₀ + ν * t) := by positivity
      linarith
    · have h_le : b * l / D ≤ b * l ^ 2 / (C₀ + ν * t) := by
        calc b * l / D ≤ b * l / (C₀ + ν * t) :=
              div_le_div_of_nonneg_left (by positivity) hCt (by dsimp [D]; linarith)
          _ ≤ b * l ^ 2 / (C₀ + ν * t) := by
              gcongr
              nlinarith
      have h_nn : 0 ≤ b / C₀ := by positivity
      linarith
  have h2 : Real.exp (-(b * l ^ 2 / (C₀ + ν * t))) ≤
      Real.exp (b / C₀) * Real.exp (-(b * l / D)) := by
    rw [← Real.exp_add, ← sub_eq_add_neg]
    exact Real.exp_le_exp.2 h2_exp
  calc Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * t)))
      ≤ Real.exp (-(b * l / D)) + Real.exp (b / C₀) * Real.exp (-(b * l / D)) :=
        add_le_add h1 h2
    _ = (1 + Real.exp (b / C₀)) * Real.exp (-(b * l / D)) := by ring

/-- Even-power polynomial weight absorption into `exp (-(b * |η| / D))` with an integrable
`(1 + η ^ 2)⁻¹` factor remaining. -/
private theorem pow_mul_exp_eta_le_inv_one_add_sq {b D : ℝ} (hb : 0 < b) (hD : 0 < D)
    (k : ℕ) (η : ℝ) :
    η ^ (2 * k) * Real.exp (-(b * |η| / D)) ≤
      (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) * (1 + η ^ 2)⁻¹ := by
  have hα : 0 < b / D := div_pos hb hD
  have h_one_add := one_add_pow_le_exp (abs_nonneg η) hα (2 * k + 1)
  have h_lhs : η ^ (2 * k) * (1 + η ^ 2) ≤ (1 + |η|) ^ (2 * k + 1 + 1) := by
    have h_even : η ^ (2 * k) = |η| ^ (2 * k) := by
      rw [pow_mul, pow_mul, sq_abs]
    have h_sq : 1 + η ^ 2 ≤ (1 + |η|) ^ 2 := by
      have : η ^ 2 = |η| ^ 2 := (sq_abs η).symm
      have : 0 ≤ |η| := abs_nonneg η
      nlinarith
    have h_pow : |η| ^ (2 * k) ≤ (1 + |η|) ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg η) (by linarith) (2 * k)
    rw [h_even, show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add]
    exact mul_le_mul h_pow h_sq (by positivity) (by positivity)
  have h_exp_eq : (b / D) * |η| = b * |η| / D := by ring
  rw [h_exp_eq] at h_one_add
  have h_comb : η ^ (2 * k) * (1 + η ^ 2) * Real.exp (-(b * |η| / D)) ≤
      (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) := by
    calc η ^ (2 * k) * (1 + η ^ 2) * Real.exp (-(b * |η| / D))
        ≤ (1 + |η|) ^ (2 * k + 1 + 1) * Real.exp (-(b * |η| / D)) :=
          mul_le_mul_of_nonneg_right h_lhs (Real.exp_nonneg _)
      _ ≤ ((1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) *
            Real.exp (b * |η| / D)) * Real.exp (-(b * |η| / D)) :=
          mul_le_mul_of_nonneg_right h_one_add (Real.exp_nonneg _)
      _ = (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have h_pos : 0 < 1 + η ^ 2 := by positivity
  calc η ^ (2 * k) * Real.exp (-(b * |η| / D))
      = (η ^ (2 * k) * (1 + η ^ 2) * Real.exp (-(b * |η| / D))) * (1 + η ^ 2)⁻¹ := by
        field_simp [h_pos.ne']
    _ ≤ (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) * (1 + η ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h_comb (inv_nonneg.2 h_pos.le)

end StressMomentsAllOrders

open StressMomentsAllOrders

/-- **Proof of `TrainMeanStressMomentsAllOrders` (`PartI:T23/1`)**:
combining the `(0, 0)` transverse velocity tail from `hTails.2.1` and the `(0, 0, 0)` unweighted
fluctuation decay from `hFD` gives a single smallness threshold `ν₀ > 0` at which all spatial
moments `η ↦ η^{2k} * meanStress tr t η` are integrable on `ℝ` for every `t > 0` and their spatial
integrals are integrable in time on `Ioi 0` for every `k : ℕ`. -/
theorem trainMeanStressMomentsAllOrders_proof
    (hTails : TrainStreamVelocityPressureTails) (hFD : TrainFluctuationDecay) :
    TrainMeanStressMomentsAllOrders := by
  intro ρ hρ
  obtain ⟨b, C₀, C', hb, hC₀, hC', C₁, N₁, ν₁, hC₁, hν₁, hTail⟩ := hTails.2.1 ρ hρ 0 0
  obtain ⟨C₂, N₂, κ, ν₂, hC₂, hκ, hν₂, hFluct⟩ := hFD ρ hρ 0 0 0
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro ν hν hν_le tr htr k
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  set R₀ : ℝ := C' / ν + 2
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  set P₂ : ℝ := polyP C₂ N₂ ν c
  have hP₂ : 0 < P₂ := by dsimp [P₂, polyP]; positivity
  set P₁ : ℝ := C₁ * (1 + c + ν⁻¹) ^ N₁ * (1 + Real.exp (b / C₀))
  have hP₁ : 0 < P₁ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    dsimp [P₁]; positivity
  set B₀ : ℝ := P₂ * (P₂ + P₁) * Real.exp (b * R₀ / c)
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  -- Jointly (t, η)-uniform bound on ‖meanStress tr t η‖ for t > 0
  have h_stress_bd : ∀ t : ℝ, 0 < t → ∀ η : ℝ,
      ‖meanStress tr t η‖ ≤
        B₀ * (1 + t) ^ N₁ * Real.exp (-(κ * ν * t / c ^ 2)) *
          Real.exp (-(b * |η| / (c + C₀ + ν * t))) := by
    intro t ht η
    set D : ℝ := c + C₀ + ν * t
    have hνt : 0 < ν * t := mul_pos hν ht
    have hD : 0 < D := by dsimp [D]; positivity
    have hc_le_D : c ≤ D := by dsimp [D]; linarith
    -- Bound 1: unweighted fluctuation decay at m = 0
    have hsup := (hFluct ν hν hν₂_le tr htr t ht).2.1.2
    let A₁ : ℝ := P₂ * Real.exp (-(κ * ν * t / c ^ 2))
    have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
    have hbd1 : ‖meanStress tr t η‖ ≤ A₁ ^ 2 := by
      have h := PartI_T23.meanStress_bound_of_wSupNorm hν hc tr htr ht 0 hA₁ hsup η
      simpa [pow_zero, div_one] using h
    -- Bound 2: spatial tail for |η| ≥ R₀ and fallback to A₁ for |η| ≤ R₀
    let A₂ : ℝ := (P₂ + P₁) * Real.exp (b * R₀ / c) * (1 + t) ^ N₁ *
      Real.exp (-(b * |η| / D))
    have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
    have hbd2 : ‖meanStress tr t η‖ ≤ A₂ ^ 2 := by
      rcases le_total |η| R₀ with hη | hη
      · have h_exp1 : Real.exp (-(κ * ν * t / c ^ 2)) ≤ 1 :=
          Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
        have h_t1 : 1 ≤ (1 + t) ^ N₁ := one_le_pow₀ (by linarith)
        have h_eta_le : b * |η| / D ≤ b * R₀ / c := by
          calc b * |η| / D ≤ b * R₀ / D := by gcongr
            _ ≤ b * R₀ / c := div_le_div_of_nonneg_left (by positivity) hc hc_le_D
        have h_exp2 : 1 ≤ Real.exp (b * R₀ / c) * Real.exp (-(b * |η| / D)) := by
          rw [← Real.exp_add, ← sub_eq_add_neg]
          exact Real.one_le_exp (by linarith)
        have hA₁_le_A₂ : A₁ ≤ A₂ := by
          calc A₁ = P₂ * Real.exp (-(κ * ν * t / c ^ 2)) := rfl
            _ ≤ P₂ * 1 := mul_le_mul_of_nonneg_left h_exp1 hP₂.le
            _ ≤ (P₂ + P₁) * 1 := by linarith
            _ ≤ (P₂ + P₁) * (Real.exp (b * R₀ / c) * Real.exp (-(b * |η| / D))) :=
                mul_le_mul_of_nonneg_left h_exp2 (by positivity)
            _ = (P₂ + P₁) * Real.exp (b * R₀ / c) * 1 * Real.exp (-(b * |η| / D)) := by ring
            _ ≤ (P₂ + P₁) * Real.exp (b * R₀ / c) * (1 + t) ^ N₁ *
                  Real.exp (-(b * |η| / D)) := by
                gcongr
        exact hbd1.trans (pow_le_pow_left₀ hA₁ hA₁_le_A₂ 2)
      · set l : ℝ := |η| - R₀
        have hl : 0 ≤ l := sub_nonneg.2 hη
        let M : ℝ := P₁ * Real.exp (b * R₀ / c) * (1 + t) ^ N₁ * Real.exp (-(b * |η| / D))
        have hM_nn : 0 ≤ M := by dsimp [M]; positivity
        have hv_pt : ∀ q : ℝ, ‖tr.v t (q, η)‖ ≤ M := by
          intro q
          have hz : C' / ν + 2 + l ≤ |((q, η) : Plane).2| := by
            change C' / ν + 2 + (|η| - (C' / ν + 2)) ≤ |η|
            linarith
          have h_tail_q := (hTail t ht.le ν hν hν₁_le tr htr l hl t ht le_rfl (q, η) hz).2.1
          rw [PartI_T23.norm_ageJet_zero_zero] at h_tail_q
          have h_sum := tail_exp_sum_le hb hc hC₀ hν ht hl
          have h_poly : polyPS C₁ N₁ ν c t * (1 + Real.exp (b / C₀)) = P₁ * (1 + t) ^ N₁ := by
            dsimp [polyPS, P₁]
            rw [mul_pow]
            ring
          have h_l_exp : Real.exp (-(b * l / D)) ≤
              Real.exp (b * R₀ / c) * Real.exp (-(b * |η| / D)) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            have hR_le : b * R₀ / D ≤ b * R₀ / c :=
              div_le_div_of_nonneg_left (by positivity) hc hc_le_D
            have h_eq : -(b * l / D) = b * R₀ / D + -(b * |η| / D) := by
              dsimp [l]; ring
            linarith
          calc ‖tr.v t (q, η)‖
              ≤ polyPS C₁ N₁ ν c t *
                  (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * t)))) := h_tail_q
            _ ≤ polyPS C₁ N₁ ν c t *
                  ((1 + Real.exp (b / C₀)) * Real.exp (-(b * l / D))) :=
                mul_le_mul_of_nonneg_left h_sum (by unfold polyPS; have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le; positivity)
            _ = (polyPS C₁ N₁ ν c t * (1 + Real.exp (b / C₀))) * Real.exp (-(b * l / D)) := by ring
            _ = P₁ * (1 + t) ^ N₁ * Real.exp (-(b * l / D)) := by rw [h_poly]
            _ ≤ P₁ * (1 + t) ^ N₁ * (Real.exp (b * R₀ / c) * Real.exp (-(b * |η| / D))) :=
                mul_le_mul_of_nonneg_left h_l_exp (by positivity)
            _ = M := by dsimp [M]; ring
        have hM_le_A₂ : M ≤ A₂ := by
          dsimp [M, A₂]
          gcongr
          linarith
        exact (norm_meanStress_le_of_norm_v_le hc tr hM_nn hv_pt).trans
          (pow_le_pow_left₀ hM_nn hM_le_A₂ 2)
    have h_prod := le_mul_of_le_sq (norm_nonneg _) hA₁ hA₂ hbd1 hbd2
    calc ‖meanStress tr t η‖ ≤ A₁ * A₂ := h_prod
      _ = B₀ * (1 + t) ^ N₁ * Real.exp (-(κ * ν * t / c ^ 2)) *
            Real.exp (-(b * |η| / D)) := by
          dsimp [A₁, A₂, B₀]
          ring
  -- Constants for polynomial-in-(1+t) bound on the k-th spatial moment
  set L₀ : ℝ := 1 + ((2 * k + 1 + 1 : ℕ) : ℝ) * (c + C₀ + ν) / b
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  set K_k : ℝ := B₀ * L₀ ^ (2 * k + 1 + 1)
  have hK_k : 0 < K_k := by dsimp [K_k]; positivity
  have h_pt_k : ∀ t : ℝ, 0 < t → ∀ η : ℝ,
      ‖η ^ (2 * k) * meanStress tr t η‖ ≤
        (K_k * (1 + t) ^ (N₁ + (2 * k + 1 + 1)) * Real.exp (-(κ * ν * t / c ^ 2))) *
          (1 + η ^ 2)⁻¹ := by
    intro t ht η
    set D : ℝ := c + C₀ + ν * t
    have hD : 0 < D := by dsimp [D]; positivity
    have hD_le : D ≤ (c + C₀ + ν) * (1 + t) := by
      dsimp [D]
      nlinarith
    have hpos_pow : 0 ≤ η ^ (2 * k) := by rw [pow_mul]; positivity
    have h_str := h_stress_bd t ht η
    have h_eta := pow_mul_exp_eta_le_inv_one_add_sq hb hD k η
    have h_factor_le : 1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D)) ≤ L₀ * (1 + t) := by
      rw [div_div_eq_mul_div]
      calc 1 + ((2 * k + 1 + 1 : ℕ) : ℝ) * D / b
          ≤ 1 + ((2 * k + 1 + 1 : ℕ) : ℝ) * ((c + C₀ + ν) * (1 + t)) / b := by gcongr
        _ = 1 + (((2 * k + 1 + 1 : ℕ) : ℝ) * (c + C₀ + ν) / b) * (1 + t) := by ring
        _ ≤ (1 + t) + (((2 * k + 1 + 1 : ℕ) : ℝ) * (c + C₀ + ν) / b) * (1 + t) := by linarith
        _ = L₀ * (1 + t) := by dsimp [L₀]; ring
    have h_pow_factor : (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) ≤
        L₀ ^ (2 * k + 1 + 1) * (1 + t) ^ (2 * k + 1 + 1) := by
      calc (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1)
          ≤ (L₀ * (1 + t)) ^ (2 * k + 1 + 1) :=
            pow_le_pow_left₀ (by positivity) h_factor_le _
        _ = L₀ ^ (2 * k + 1 + 1) * (1 + t) ^ (2 * k + 1 + 1) := mul_pow _ _ _
    rw [norm_mul, Real.norm_of_nonneg hpos_pow]
    calc η ^ (2 * k) * ‖meanStress tr t η‖
        ≤ η ^ (2 * k) * (B₀ * (1 + t) ^ N₁ * Real.exp (-(κ * ν * t / c ^ 2)) *
            Real.exp (-(b * |η| / D))) :=
          mul_le_mul_of_nonneg_left h_str hpos_pow
      _ = (B₀ * (1 + t) ^ N₁ * Real.exp (-(κ * ν * t / c ^ 2))) *
            (η ^ (2 * k) * Real.exp (-(b * |η| / D))) := by ring
      _ ≤ (B₀ * (1 + t) ^ N₁ * Real.exp (-(κ * ν * t / c ^ 2))) *
            ((1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) * (1 + η ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left h_eta (by positivity)
      _ ≤ (B₀ * (1 + t) ^ N₁ * Real.exp (-(κ * ν * t / c ^ 2))) *
            ((L₀ ^ (2 * k + 1 + 1) * (1 + t) ^ (2 * k + 1 + 1)) * (1 + η ^ 2)⁻¹) := by
          gcongr
      _ = (K_k * (1 + t) ^ (N₁ + (2 * k + 1 + 1)) * Real.exp (-(κ * ν * t / c ^ 2))) *
            (1 + η ^ 2)⁻¹ := by
          dsimp [K_k]
          rw [pow_add]
          ring
  -- Spatial integrability and moment bound for each t > 0
  have h_spatial : ∀ t : ℝ, 0 < t →
      Integrable (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) volume ∧
      ‖∫ η : ℝ, η ^ (2 * k) * meanStress tr t η‖ ≤
        Real.pi * K_k * (1 + t) ^ (N₁ + (2 * k + 1 + 1)) * Real.exp (-(κ * ν * t / c ^ 2)) := by
    intro t ht
    let C_t : ℝ := K_k * (1 + t) ^ (N₁ + (2 * k + 1 + 1)) * Real.exp (-(κ * ν * t / c ^ 2))
    have hg : Integrable (fun η : ℝ => C_t * (1 + η ^ 2)⁻¹) volume :=
      integrable_inv_one_add_sq.const_mul C_t
    have hcont : Continuous (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) :=
      (continuous_pow (2 * k)).mul (PartI_T23.continuous_meanStress hc.le tr ht.le)
    refine ⟨hg.mono' hcont.aestronglyMeasurable (Eventually.of_forall (h_pt_k t ht)), ?_⟩
    calc ‖∫ η : ℝ, η ^ (2 * k) * meanStress tr t η‖
        ≤ ∫ η : ℝ, C_t * (1 + η ^ 2)⁻¹ :=
          norm_integral_le_of_norm_le hg (Eventually.of_forall (h_pt_k t ht))
      _ = Real.pi * K_k * (1 + t) ^ (N₁ + (2 * k + 1 + 1)) * Real.exp (-(κ * ν * t / c ^ 2)) := by
          rw [integral_const_mul, integral_univ_inv_one_add_sq]
          dsimp [C_t]
          ring
  refine ⟨fun t ht => (h_spatial t ht).1, ?_⟩
  -- Time integrability on Ioi 0
  let G : ℝ × ℝ → ℝ := (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator
    (fun x : ℝ × ℝ => x.2 ^ (2 * k) * meanStress tr x.1 x.2)
  have hS_meas : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    (isOpen_Ioi.prod isOpen_univ).measurableSet
  have hG_contOn : ContinuousOn (fun x : ℝ × ℝ => x.2 ^ (2 * k) * meanStress tr x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    (continuousOn_snd.pow (2 * k)).mul (PartI_T23.contDiffOn_meanStress hc tr).continuousOn
  have hG_aem : AEStronglyMeasurable G (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (aestronglyMeasurable_indicator_iff hS_meas).2 (hG_contOn.aestronglyMeasurable hS_meas)
  have h_int_aem : AEStronglyMeasurable (fun t : ℝ => ∫ η : ℝ, G (t, η)) volume :=
    hG_aem.integral_prod_right'
  have h_aem_Ioi : AEStronglyMeasurable
      (fun t : ℝ => ∫ η : ℝ, η ^ (2 * k) * meanStress tr t η) (volume.restrict (Ioi 0)) := by
    refine h_int_aem.restrict.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    congr 1
    funext η
    have hmem : ((t, η) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨ht', mem_univ η⟩
    simp [G, hmem]
  set m_t : ℕ := N₁ + 2 * k + 1
  set γ : ℝ := κ * ν / (2 * c ^ 2)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  set C_time : ℝ := Real.pi * K_k * (1 + (((m_t + 1 : ℕ) : ℝ) / γ)) ^ (m_t + 1)
  have hexp_int : IntegrableOn (fun t : ℝ => C_time * Real.exp (-γ * t)) (Ioi 0) volume :=
    (exp_neg_integrableOn_Ioi 0 hγ).const_mul C_time
  refine hexp_int.mono' h_aem_Ioi ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_pos : 0 < t := ht
  have hbd := (h_spatial t ht_pos).2
  have h_m_eq : N₁ + (2 * k + 1 + 1) = m_t + 1 := by dsimp [m_t]; ring
  rw [h_m_eq] at hbd
  have h_absorb := one_add_pow_le_exp ht_pos.le hγ m_t
  have h_exp_split : Real.exp (γ * t) * Real.exp (-(κ * ν * t / c ^ 2)) = Real.exp (-γ * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [γ]
    ring
  calc ‖∫ η : ℝ, η ^ (2 * k) * meanStress tr t η‖
      ≤ Real.pi * K_k * (1 + t) ^ (m_t + 1) * Real.exp (-(κ * ν * t / c ^ 2)) := hbd
    _ ≤ Real.pi * K_k * ((1 + (((m_t + 1 : ℕ) : ℝ) / γ)) ^ (m_t + 1) * Real.exp (γ * t)) *
          Real.exp (-(κ * ν * t / c ^ 2)) := by
        gcongr
    _ = C_time * (Real.exp (γ * t) * Real.exp (-(κ * ν * t / c ^ 2))) := by
        dsimp [C_time]; ring
    _ = C_time * Real.exp (-γ * t) := by rw [h_exp_split]

end UnforcedLeray.Short.PartI
