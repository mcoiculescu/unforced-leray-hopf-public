import UnforcedLeray.Short.PartI.Sub.PartI_T22_2
import UnforcedLeray.Short.PartI.Sub.PartI_T20_1.Base
import UnforcedLeray.Lib.Kernels.ParamIntegral
import UnforcedLeray.Units.B0151.DivCurl

/-!
# `PartI:T22/2/1` (`VelFluctHigherStep.lean`): higher-age post-overlap velocity-fluctuation step

Source of record: `the November 2 reference manuscript`, lines 439–446 and 523–526.

Proves `trainPostOverlapVelFluctHigherStep_proof : TrainPostOverlapVelFluctHigherStep` by expressing
the age-`(ℓ + 1)` slice of the velocity fluctuation `v_fluct = fun r => hfluct c (tr.v r)` via the
horizontally oscillated momentum equation:
1. The viscous term `vhaOsc c (ν * lapS (tr.v r · k))` equals `ν * lapS (v_fluct r · k)` because
   `vhaOsc c` commutes with `partialX` and `partialY` (`PartI_T21_2.partialX_vhaOsc`,
   `PartI_T21_2.partialY_vhaOsc`).
2. Every term in `Train.advection (tr.v r)` retains a `v_fluct` factor because
   `Cyl.partialQ (tr.v r · k) = Cyl.partialQ (v_fluct r · k)` and `tr.v r w 1 = v_fluct r w 1`
   (`trainMeanV2`).
3. The pressure gradient `Train.gradS (tr.p r)` is controlled at age order `ℓ` by the induction
   hypothesis `hIH ℓ le_rfl`, and horizontal averaging of the advection-plus-pressure-gradient
   term is bounded via `PartI_T21.norm_ageJet_hmean_scalar_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet jap)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm)

namespace PartI_T22_2_1

/-! ### 1. Pointwise extraction from `wSupNorm 0` and polynomial-exponential absorption -/

theorem norm_le_of_wSupNorm_zero_le {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {B : ℝ} (hB : 0 ≤ B)
    (hSup : wSupNorm 0 f ≤ ENNReal.ofReal B) (z : Plane) :
    ‖f z‖ ≤ B := by
  have hz : ENNReal.ofReal (Real.sqrt (jap 0 z)) * ‖f z‖ₑ ≤ ENNReal.ofReal B :=
    (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap 0 w)) * ‖f w‖ₑ) z).trans hSup
  have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
  rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm] at hz
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hz

theorem wSupNorm_zero_le_of_norm_le {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {B : ℝ} (hpt : ∀ z : Plane, ‖f z‖ ≤ B) :
    wSupNorm 0 f ≤ ENNReal.ofReal B := by
  unfold wSupNorm
  refine iSup_le fun z => ?_
  have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
  rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hpt z)

/-- Direct product absorption `polyPS C₁ N₁ ν c s * (polyP C₂ N₂ ν c * exp(-(lam * ν * s / c²)))`
into `polyP (C₁ * C₂ * K_abs) (4 * N₁ + N₂) ν c * exp(-((lam / 2) * ν * s / c²))`. -/
theorem polyPS_mul_polyP_exp_le {C₁ C₂ lam ν c s : ℝ} (N₁ N₂ : ℕ)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hlam : 0 < lam) (hν : 0 < ν) (hc : 1 ≤ c) (hs : 0 ≤ s) :
    let K_abs : ℝ := (N₁.factorial : ℝ) * ((lam / 2) ^ N₁)⁻¹ * Real.exp (lam / 2)
    polyPS C₁ N₁ ν c s * (polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2))) ≤
      polyP (C₁ * C₂ * K_abs) (4 * N₁ + N₂) ν c *
        Real.exp (-((lam / 2) * ν * s / c ^ 2)) := by
  intro K_abs
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  set X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hX1 : 1 ≤ X := by linarith
  have hcX : c ≤ X := by linarith
  have hνX : ν⁻¹ ≤ X := by linarith
  set u : ℝ := ν * s / c ^ 2
  have hu : 0 ≤ u := by positivity
  have hs_u : s = c ^ 2 * ν⁻¹ * u := by
    dsimp [u]
    field_simp
  have h1s : 1 + s ≤ X ^ 3 * (1 + u) := by
    have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0.le hcX 2
    have hmul : c ^ 2 * ν⁻¹ ≤ X ^ 3 := by
      calc c ^ 2 * ν⁻¹ ≤ X ^ 2 * X := mul_le_mul hc2 hνX hν_inv (by positivity)
        _ = X ^ 3 := by ring
    have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX1
    calc 1 + s = 1 + (c ^ 2 * ν⁻¹) * u := by rw [hs_u]
      _ ≤ X ^ 3 + X ^ 3 * u := add_le_add hX3 (mul_le_mul_of_nonneg_right hmul hu)
      _ = X ^ 3 * (1 + u) := by ring
  have hX1s : (X * (1 + s)) ^ N₁ ≤ X ^ (4 * N₁) * (1 + u) ^ N₁ := by
    calc (X * (1 + s)) ^ N₁
        ≤ (X * (X ^ 3 * (1 + u))) ^ N₁ := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left h1s (by positivity)
      _ = (X ^ 4 * (1 + u)) ^ N₁ := by rw [← mul_assoc, ← pow_succ']
      _ = X ^ (4 * N₁) * (1 + u) ^ N₁ := by rw [mul_pow, ← pow_mul]
  have habs : (1 + u) ^ N₁ ≤ K_abs * Real.exp (lam / 2 * u) := by
    have h := Real.pow_div_factorial_le_exp (lam / 2 * (1 + u)) (by positivity) N₁
    have hf : (0 : ℝ) < N₁.factorial := by exact_mod_cast N₁.factorial_pos
    have hlp : 0 < (lam / 2) ^ N₁ := by positivity
    rw [div_le_iff₀ hf, mul_pow] at h
    have hexp_add : Real.exp (lam / 2 * (1 + u)) = Real.exp (lam / 2) * Real.exp (lam / 2 * u) := by
      rw [mul_add, mul_one, Real.exp_add]
    rw [hexp_add] at h
    dsimp [K_abs]
    calc (1 + u) ^ N₁
        = ((lam / 2) ^ N₁)⁻¹ * ((lam / 2) ^ N₁ * (1 + u) ^ N₁) := by field_simp
      _ ≤ ((lam / 2) ^ N₁)⁻¹ * (Real.exp (lam / 2) * Real.exp (lam / 2 * u) * N₁.factorial) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hlp.le)
      _ = (N₁.factorial : ℝ) * ((lam / 2) ^ N₁)⁻¹ * Real.exp (lam / 2) *
            Real.exp (lam / 2 * u) := by ring
  have hA_le : polyPS C₁ N₁ ν c s ≤ C₁ * X ^ (4 * N₁) * (K_abs * Real.exp (lam / 2 * u)) := by
    unfold polyPS
    calc C₁ * (X * (1 + s)) ^ N₁
        ≤ C₁ * (X ^ (4 * N₁) * (1 + u) ^ N₁) :=
          mul_le_mul_of_nonneg_left hX1s hC₁.le
      _ = C₁ * X ^ (4 * N₁) * (1 + u) ^ N₁ := by ring
      _ ≤ C₁ * X ^ (4 * N₁) * (K_abs * Real.exp (lam / 2 * u)) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
  have hexp_comb : Real.exp (lam / 2 * u) * Real.exp (-(lam * u)) =
      Real.exp (-((lam / 2) * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hB_nn : 0 ≤ polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2)) := by
    unfold polyP; positivity
  have hexp_u : Real.exp (-(lam * ν * s / c ^ 2)) = Real.exp (-(lam * u)) := by
    congr 1; dsimp [u]; ring
  have hexp_u2 : Real.exp (-((lam / 2) * u)) = Real.exp (-((lam / 2) * ν * s / c ^ 2)) := by
    congr 1; dsimp [u]; ring
  have hB_eq : polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2)) =
      C₂ * X ^ N₂ * Real.exp (-(lam * u)) := by
    rw [hexp_u]
    unfold polyP
    dsimp [X]
  calc polyPS C₁ N₁ ν c s * (polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2)))
      ≤ (C₁ * X ^ (4 * N₁) * (K_abs * Real.exp (lam / 2 * u))) *
          (polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2))) :=
        mul_le_mul_of_nonneg_right hA_le hB_nn
    _ = C₁ * C₂ * K_abs * (X ^ (4 * N₁) * X ^ N₂) *
          (Real.exp (lam / 2 * u) * Real.exp (-(lam * u))) := by
        rw [hB_eq]
        ring
    _ = polyP (C₁ * C₂ * K_abs) (4 * N₁ + N₂) ν c *
          Real.exp (-((lam / 2) * ν * s / c ^ 2)) := by
        rw [← pow_add, hexp_comb, hexp_u2]
        unfold polyP
        dsimp [X]

/-! ### 2. Uniform rectangle bounds for `tr.v` (`polyPS`) and `(v_fluct, tr.p)` (`polyP * exp`) -/

theorem polyPS_mono {C₁ C₂ : ℝ} {N₁ N₂ : ℕ} {ν c s : ℝ}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hN : N₁ ≤ N₂) (hν : 0 < ν) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    polyPS C₁ N₁ ν c s ≤ polyPS C₂ N₂ ν c s := by
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ (1 + c + ν⁻¹) * (1 + s) := by nlinarith
  have hC₂ : 0 ≤ C₂ := hC₁.trans hC
  unfold polyPS
  exact mul_le_mul hC (pow_le_pow_right₀ h1X hN) (by positivity) hC₂

theorem uniform_vel_polyPS_row
    (hTails : TrainStreamVelocityPressureTails)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (r : ℕ) :
    ∀ K : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ i ≤ K,
            ‖ageJet r i tr.v s z‖ ≤ polyPS C N ν (trainPeriod ρ ν) s
  | 0 => by
    obtain ⟨C, N, ν₀, hC, hν₀, h0⟩ := hTails.2.2 ρ hρ 0 r 0
    refine ⟨C, N, ν₀, hC, hν₀, fun ν hν hν_le tr htr s hs z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    have hB : 0 ≤ polyPS C N ν c s := by unfold polyPS; positivity
    exact norm_le_of_wSupNorm_zero_le hB (h0 ν hν hν_le tr htr s hs).2.2.1.2 z
  | K + 1 => by
    obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ := uniform_vel_polyPS_row hTails hρ r K
    obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hK1⟩ := hTails.2.2 ρ hρ 0 r (K + 1)
    refine ⟨max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z i hi
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hi with hiK | rfl
    · exact (hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z i hiK).trans
        (polyPS_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc.le hs.le)
    · have hB : 0 ≤ polyPS C₂ N₂ ν c s := by unfold polyPS; positivity
      have hpt := norm_le_of_wSupNorm_zero_le hB
        (hK1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs).2.2.1.2 z
      exact hpt.trans
        (polyPS_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc.le hs.le)

theorem uniform_vel_polyPS_rect
    (hTails : TrainStreamVelocityPressureTails)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (K : ℕ) :
    ∀ L : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ r ≤ L, ∀ i ≤ K,
            ‖ageJet r i tr.v s z‖ ≤ polyPS C N ν (trainPeriod ρ ν) s
  | 0 => by
    obtain ⟨C, N, ν₀, hC, hν₀, h0⟩ := uniform_vel_polyPS_row hTails hρ 0 K
    refine ⟨C, N, ν₀, hC, hν₀, fun ν hν hν_le tr htr s hs z r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 ν hν hν_le tr htr s hs z i hi
  | L + 1 => by
    obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ := uniform_vel_polyPS_rect hTails hρ K L
    obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hL1⟩ := uniform_vel_polyPS_row hTails hρ (L + 1) K
    refine ⟨max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z r hr i hi
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hr with hrL | rfl
    · exact (hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z r hrL i hi).trans
        (polyPS_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc.le hs.le)
    · exact (hL1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs z i hi).trans
        (polyPS_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc.le hs.le)

theorem polyP_exp_mono (C₁ C₂ lam₁ lam₂ : ℝ) (N₁ N₂ : ℕ) {ν c s : ℝ}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hN : N₁ ≤ N₂) (hlam : lam₂ ≤ lam₁)
    (hν : 0 < ν) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    polyP C₁ N₁ ν c * Real.exp (-(lam₁ * ν * s / c ^ 2)) ≤
      polyP C₂ N₂ ν c * Real.exp (-(lam₂ * ν * s / c ^ 2)) := by
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  have hC₂ : 0 ≤ C₂ := hC₁.trans hC
  apply mul_le_mul
  · unfold polyP
    exact mul_le_mul hC (pow_le_pow_right₀ h1X hN) (by positivity) hC₂
  · apply Real.exp_le_exp.2
    apply neg_le_neg
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlam hν.le) hs) (sq_nonneg c)
  · exact Real.exp_nonneg _
  · unfold polyP; positivity

theorem uniform_velPress_exp_row {r : ℕ}
    (hOrd : TrainPostOverlapVelPressOrderSup r)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    ∀ K : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            ∀ z : Plane, ∀ i ≤ K,
              let c := trainPeriod ρ ν
              let M := polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))
              ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M ∧
              ‖ageJet r i tr.p s z‖ ≤ M
  | 0 => by
    obtain ⟨C, N, lam, ν₀, hC, hlam, hν₀, h0⟩ := hOrd ρ hρ 0
    refine ⟨C, N, lam, ν₀, hC, hlam, hν₀, fun ν hν hν_le tr htr s hs hsc z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    have hM : 0 ≤ polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)) := by
      unfold polyP; positivity
    obtain ⟨hv, hp⟩ := h0 ν hν hν_le tr htr s hs hsc
    exact ⟨norm_le_of_wSupNorm_zero_le hM hv z, norm_le_of_wSupNorm_zero_le hM hp z⟩
  | K + 1 => by
    obtain ⟨C₁, N₁, lam₁, ν₁, hC₁, hlam₁, hν₁, hIH⟩ := uniform_velPress_exp_row hOrd hρ K
    obtain ⟨C₂, N₂, lam₂, ν₂, hC₂, hlam₂, hν₂, hK1⟩ := hOrd ρ hρ (K + 1)
    refine ⟨max C₁ C₂, max N₁ N₂, min lam₁ lam₂, min ν₁ ν₂,
      lt_max_of_lt_left hC₁, lt_min hlam₁ hlam₂, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs hsc z i hi
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hi with hiK | rfl
    · obtain ⟨hv, hp⟩ := hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs hsc z i hiK
      have hm := polyP_exp_mono (ν := ν) (c := c) (s := s) C₁ (max C₁ C₂) lam₁ (min lam₁ lam₂)
        N₁ (max N₁ N₂) hC₁.le (le_max_left _ _) (le_max_left _ _) (min_le_left _ _) hν hc.le hs.le
      exact ⟨hv.trans hm, hp.trans hm⟩
    · have hM₂ : 0 ≤ polyP C₂ N₂ ν c * Real.exp (-(lam₂ * ν * s / c ^ 2)) := by
        unfold polyP; positivity
      obtain ⟨hv, hp⟩ := hK1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs hsc
      have hm := polyP_exp_mono (ν := ν) (c := c) (s := s) C₂ (max C₁ C₂) lam₂ (min lam₁ lam₂)
        N₂ (max N₁ N₂) hC₂.le (le_max_right _ _) (le_max_right _ _) (min_le_right _ _) hν hc.le hs.le
      exact ⟨(norm_le_of_wSupNorm_zero_le hM₂ hv z).trans hm,
        (norm_le_of_wSupNorm_zero_le hM₂ hp z).trans hm⟩

theorem uniform_velPress_exp_rect {L : ℕ}
    (hIH : ∀ r ≤ L, TrainPostOverlapVelPressOrderSup r)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (K : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            ∀ z : Plane, ∀ r ≤ L, ∀ i ≤ K,
              let c := trainPeriod ρ ν
              let M := polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))
              ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M ∧
              ‖ageJet r i tr.p s z‖ ≤ M := by
  induction L with
  | zero =>
    obtain ⟨C, N, lam, ν₀, hC, hlam, hν₀, h0⟩ :=
      uniform_velPress_exp_row (hIH 0 le_rfl) hρ K
    refine ⟨C, N, lam, ν₀, hC, hlam, hν₀, fun ν hν hν_le tr htr s hs hsc z r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 ν hν hν_le tr htr s hs hsc z i hi
  | succ L ih =>
    obtain ⟨C₁, N₁, lam₁, ν₁, hC₁, hlam₁, hν₁, hL⟩ :=
      ih (fun r hr => hIH r (Nat.le_succ_of_le hr))
    obtain ⟨C₂, N₂, lam₂, ν₂, hC₂, hlam₂, hν₂, hL1⟩ :=
      uniform_velPress_exp_row (hIH (L + 1) le_rfl) hρ K
    refine ⟨max C₁ C₂, max N₁ N₂, min lam₁ lam₂, min ν₁ ν₂,
      lt_max_of_lt_left hC₁, lt_min hlam₁ hlam₂, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs hsc z r hr i hi
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hr with hrL | rfl
    · obtain ⟨hv, hp⟩ := hL ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs hsc z r hrL i hi
      have hm := polyP_exp_mono (ν := ν) (c := c) (s := s) C₁ (max C₁ C₂) lam₁ (min lam₁ lam₂)
        N₁ (max N₁ N₂) hC₁.le (le_max_left _ _) (le_max_left _ _) (min_le_left _ _) hν hc.le hs.le
      exact ⟨hv.trans hm, hp.trans hm⟩
    · obtain ⟨hv, hp⟩ := hL1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs hsc z i hi
      have hm := polyP_exp_mono (ν := ν) (c := c) (s := s) C₂ (max C₁ C₂) lam₂ (min lam₁ lam₂)
        N₂ (max N₁ N₂) hC₂.le (le_max_right _ _) (le_max_right _ _) (min_le_right _ _) hν hc.le hs.le
      exact ⟨hv.trans hm, hp.trans hm⟩

/-! ### 3. Fluctuation identities for `tr.v` and advection jet bound -/

noncomputable def vecSingleCLM (k : Fin 2) : ℝ →L[ℝ] Vec :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single k (1 : ℝ))

theorem vecSingleCLM_apply (k : Fin 2) (x : ℝ) :
    vecSingleCLM k x = x • EuclideanSpace.single k (1 : ℝ) := rfl

theorem norm_vecSingleCLM_le_one (k : Fin 2) : ‖vecSingleCLM k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [vecSingleCLM_apply, norm_smul, PiLp.norm_single, norm_one, mul_one, one_mul]

theorem vec_eq_sum_vecSingleCLM (v : Vec) :
    vecSingleCLM 0 (v 0) + vecSingleCLM 1 (v 1) = v := by
  ext i
  fin_cases i <;>
    simp [vecSingleCLM_apply, PiLp.add_apply, PiLp.smul_apply]

theorem norm_iteratedFDeriv_vec_le_add_proj {u : Plane → Vec} (hu : ContDiff ℝ ∞ u)
    (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j u z‖ ≤
      ‖iteratedFDeriv ℝ j (fun w => u w 0) z‖ + ‖iteratedFDeriv ℝ j (fun w => u w 1) z‖ := by
  let u₀ : Plane → ℝ := fun w => u w 0
  let u₁ : Plane → ℝ := fun w => u w 1
  have hu₀ : ContDiff ℝ ∞ u₀ :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hu₁ : ContDiff ℝ ∞ u₁ :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hF₀ : ContDiff ℝ ∞ (vecSingleCLM 0 ∘ u₀) := (vecSingleCLM 0).contDiff.comp hu₀
  have hF₁ : ContDiff ℝ ∞ (vecSingleCLM 1 ∘ u₁) := (vecSingleCLM 1).contDiff.comp hu₁
  have heq : u = (vecSingleCLM 0 ∘ u₀) + (vecSingleCLM 1 ∘ u₁) :=
    funext fun w => (vec_eq_sum_vecSingleCLM (u w)).symm
  have hc₀ : ContDiffAt ℝ j (vecSingleCLM 0 ∘ u₀) z :=
    (hF₀.of_le (by exact_mod_cast le_top)).contDiffAt
  have hc₁ : ContDiffAt ℝ j (vecSingleCLM 1 ∘ u₁) z :=
    (hF₁.of_le (by exact_mod_cast le_top)).contDiffAt
  have hadd : iteratedFDeriv ℝ j u z =
      iteratedFDeriv ℝ j (vecSingleCLM 0 ∘ u₀) z + iteratedFDeriv ℝ j (vecSingleCLM 1 ∘ u₁) z := by
    rw [heq]
    exact iteratedFDeriv_add_apply hc₀ hc₁
  have hb₀ : ‖iteratedFDeriv ℝ j (vecSingleCLM 0 ∘ u₀) z‖ ≤ ‖iteratedFDeriv ℝ j u₀ z‖ := by
    refine ((vecSingleCLM 0).norm_iteratedFDeriv_comp_left
      hu₀.contDiffAt (by exact_mod_cast le_top)).trans ?_
    exact (mul_le_mul_of_nonneg_right (norm_vecSingleCLM_le_one 0) (norm_nonneg _)).trans (by linarith)
  have hb₁ : ‖iteratedFDeriv ℝ j (vecSingleCLM 1 ∘ u₁) z‖ ≤ ‖iteratedFDeriv ℝ j u₁ z‖ := by
    refine ((vecSingleCLM 1).norm_iteratedFDeriv_comp_left
      hu₁.contDiffAt (by exact_mod_cast le_top)).trans ?_
    exact (mul_le_mul_of_nonneg_right (norm_vecSingleCLM_le_one 1) (norm_nonneg _)).trans (by linarith)
  rw [hadd]
  exact (norm_add_le _ _).trans (add_le_add hb₀ hb₁)

theorem norm_ageJet_vec_le_add_proj {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j V s z‖ ≤
      ‖ageJet ℓ j (fun r w => V r w 0) s z‖ + ‖ageJet ℓ j (fun r w => V r w 1) s z‖ := by
  have hu : ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv ℓ (fun r => V r w) s) :=
    PartI_T22.contDiff_slice_iteratedDeriv hV ℓ hs
  have hproj0 : (fun w : Plane => (iteratedDeriv ℓ (fun r => V r w) s) 0) =
      fun w => iteratedDeriv ℓ (fun r => V r w 0) s :=
    funext fun w => (PartI_T20.iteratedDeriv_vec_proj_eq hV 0 ℓ hs w).symm
  have hproj1 : (fun w : Plane => (iteratedDeriv ℓ (fun r => V r w) s) 1) =
      fun w => iteratedDeriv ℓ (fun r => V r w 1) s :=
    funext fun w => (PartI_T20.iteratedDeriv_vec_proj_eq hV 1 ℓ hs w).symm
  unfold ageJet jet
  have h := norm_iteratedFDeriv_vec_le_add_proj hu j z
  rwa [hproj0, hproj1] at h

theorem advection_apply_eq (u : Plane → Vec) (w : Plane) (k : Fin 2) :
    Train.advection u w k =
      u w 0 * Cyl.partialQ (fun x => u x k) w + u w 1 * Cyl.partialEta (fun x => u x k) w := by
  fin_cases k <;> simp [Train.advection, toVec_zero, toVec_one]

theorem partialQ_train_v_eq_fluct {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (r : ℝ) (k : Fin 2) (w : Plane) :
    Cyl.partialQ (fun y => tr.v r y k) w =
      Cyl.partialQ (fun y => (hfluct c (tr.v r) y) k) w := by
  have hfun : (fun q : ℝ => (hfluct c (tr.v r) (q, w.2)) k) =
      fun q : ℝ => tr.v r (q, w.2) k - (hmean c (tr.v r) w.2) k := by
    funext q
    rfl
  change deriv (fun q : ℝ => tr.v r (q, w.2) k) w.1 =
    deriv (fun q : ℝ => (hfluct c (tr.v r) (q, w.2)) k) w.1
  rw [hfun, deriv_sub_const]

theorem train_v_one_eq_fluct {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r) (w : Plane) :
    tr.v r w 1 = (hfluct c (tr.v r) w) 1 := by
  have hvc : Continuous (tr.v r) := (bucVel_vslice_contDiff tr hr.le).continuous
  have hm1 := PartI_T22.hmean_apply_vec' c hvc w.2 1
  have hv2_0 : hmean c (fun y => tr.v r y 1) w.2 = 0 := trainMeanV2 ν c hν hc tr r hr w.2
  change tr.v r w 1 = (tr.v r w - hmean c (tr.v r) w.2) 1
  rw [PiLp.sub_apply, hm1, hv2_0, sub_zero]

theorem ageJet_train_v_one_eq_fluct {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (r i : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet r i (fun t w => tr.v t w 1) s z =
      ageJet r i (fun t w => (hfluct c (tr.v t) w) 1) s z := by
  unfold ageJet
  congr 1
  funext w
  have hev : (fun t => tr.v t w 1) =ᶠ[𝓝 s] fun t => (hfluct c (tr.v t) w) 1 := by
    filter_upwards [Ioi_mem_nhds hs] with t ht using train_v_one_eq_fluct hν hc tr ht w
  exact hev.iteratedDeriv_eq r

/-- Componentwise advection age-jet bound retaining a `v_fluct` factor in every term:
`‖ageJet ℓ j (fun r w => Train.advection (tr.v r) w k) s z‖ ≤ 2 * 2 ^ (ℓ + j) * M_V * M_fl`. -/
theorem norm_ageJet_advection_train_comp_le {ν c M_V M_fl : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hMV : 0 ≤ M_V) (hMfl : 0 ≤ M_fl)
    (tr : B0140.TrainSol ν c) (k : Fin 2) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i tr.v s z‖ ≤ M_V)
    (hFl_bd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M_fl) :
    ‖ageJet ℓ j (fun r w => Train.advection (tr.v r) w k) s z‖ ≤
      2 * (2 : ℝ) ^ (ℓ + j) * M_V * M_fl := by
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_fl : Sm (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_vk : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_flk : PartI_T20.SmR (fun x : ℝ × Plane => (hfluct c (tr.v x.1) x.2) k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_fl
  have hsm_Q : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun y => tr.v x.1 y k) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => tr.v r w k) hsm_vk
  have hsm_E : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun y => tr.v x.1 y k) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => tr.v r w k) hsm_vk
  let A₀ : ℝ → Plane → ℝ := fun r w => tr.v r w 0 * Cyl.partialQ (fun y => tr.v r y k) w
  let A₁ : ℝ → Plane → ℝ := fun r w => tr.v r w 1 * Cyl.partialEta (fun y => tr.v r y k) w
  have hfun : (fun r w => Train.advection (tr.v r) w k) = fun r w => A₀ r w + A₁ r w :=
    funext fun r => funext fun w => advection_apply_eq (tr.v r) w k
  rw [hfun, PartI_T20.ageJet_add A₀ A₁ (hsm_v0.mul hsm_Q) (hsm_v1.mul hsm_E) hs ℓ j z]
  have hQ_eq : (fun t w => Cyl.partialQ (fun y => tr.v t y k) w) =
      fun t w => Cyl.partialQ (fun y => (hfluct c (tr.v t) y) k) w :=
    funext fun t => funext fun w => partialQ_train_v_eq_fluct tr t k w
  have hb₀ : ‖ageJet ℓ j A₀ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_V * M_fl := by
    refine PartI_T20.norm_ageJet_mul_le hsm_v0 hsm_Q ℓ j hs hMV hMfl z
      (fun r hr i hi => (PartI_T20.norm_ageJet_vec_proj_le hsm_v 0 r i hs z).trans
        (hV_bd r hr i (by omega)))
      (fun r hr i hi => ?_)
    rw [hQ_eq]
    exact ((PartI_T20.norm_ageJet_partialQ_le
      (F := fun t w => (hfluct c (tr.v t) w) k) hsm_flk r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hsm_fl k r (i + 1) hs z)).trans
      (hFl_bd r hr (i + 1) (by omega))
  have hb₁ : ‖ageJet ℓ j A₁ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_fl * M_V := by
    refine PartI_T20.norm_ageJet_mul_le hsm_v1 hsm_E ℓ j hs hMfl hMV z
      (fun r hr i hi => ?_)
      (fun r hr i hi =>
        ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => tr.v t w k) hsm_vk r i hs z).trans
          (PartI_T20.norm_ageJet_vec_proj_le hsm_v k r (i + 1) hs z)).trans
        (hV_bd r hr (i + 1) (by omega)))
    rw [ageJet_train_v_one_eq_fluct hν hc tr r i hs z]
    exact (PartI_T20.norm_ageJet_vec_proj_le hsm_fl 1 r i hs z).trans
      (hFl_bd r hr i (by omega))
  calc ‖ageJet ℓ j A₀ s z + ageJet ℓ j A₁ s z‖
      ≤ ‖ageJet ℓ j A₀ s z‖ + ‖ageJet ℓ j A₁ s z‖ := norm_add_le _ _
    _ ≤ (2 : ℝ) ^ (ℓ + j) * M_V * M_fl + (2 : ℝ) ^ (ℓ + j) * M_fl * M_V := add_le_add hb₀ hb₁
    _ = 2 * (2 : ℝ) ^ (ℓ + j) * M_V * M_fl := by ring

/-! ### 4. Horizontally oscillated momentum identity for `v_fluct` -/

theorem smR_advection_comp {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) (k : Fin 2) :
    PartI_T20.SmR (fun x : ℝ × Plane => (Train.advection (V x.1) x.2) k) := by
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_vk : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_Q : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun y => V x.1 y k) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w k) hsm_vk
  have hsm_E : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun y => V x.1 y k) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w k) hsm_vk
  have hfun : (fun x : ℝ × Plane => (Train.advection (V x.1) x.2) k) =
      fun x : ℝ × Plane => V x.1 x.2 0 * Cyl.partialQ (fun y => V x.1 y k) x.2 +
        V x.1 x.2 1 * Cyl.partialEta (fun y => V x.1 y k) x.2 :=
    funext fun x => advection_apply_eq (V x.1) x.2 k
  rw [hfun]
  exact (hsm_v0.mul hsm_Q).add (hsm_v1.mul hsm_E)

theorem smR_gradS_comp {P : ℝ → Plane → ℝ}
    (hP : PartI_T20.SmR (fun x : ℝ × Plane => P x.1 x.2)) (k : Fin 2) :
    PartI_T20.SmR (fun x : ℝ × Plane => (Train.gradS (P x.1) x.2) k) := by
  fin_cases k
  · change PartI_T20.SmR (fun x : ℝ × Plane => (Train.gradS (P x.1) x.2) 0)
    have hfun : (fun x : ℝ × Plane => (Train.gradS (P x.1) x.2) 0) =
        fun x : ℝ × Plane => Cyl.partialQ (P x.1) x.2 := by
      funext x
      exact toVec_zero _
    rw [hfun]
    exact PartI_T20.smR_partialQ hP
  · change PartI_T20.SmR (fun x : ℝ × Plane => (Train.gradS (P x.1) x.2) 1)
    have hfun : (fun x : ℝ × Plane => (Train.gradS (P x.1) x.2) 1) =
        fun x : ℝ × Plane => Cyl.partialEta (P x.1) x.2 := by
      funext x
      exact toVec_one _
    rw [hfun]
    exact PartI_T20.smR_partialEta hP

theorem hmean_const_mul (c a : ℝ) {f : Plane → ℝ} (_hf : Continuous f) (η : ℝ) :
    hmean c (fun w => a * f w) η = a * hmean c f η := by
  unfold hmean
  rw [smul_eq_mul, smul_eq_mul, integral_const_mul]
  ring

theorem hmean_sub (c : ℝ) {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g) (η : ℝ) :
    hmean c (fun w => f w - g w) η = hmean c f η - hmean c g η := by
  have hfi : Integrable (fun q : ℝ => f (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (hf.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have hgi : Integrable (fun q : ℝ => g (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (hg.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  unfold hmean
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, integral_sub hfi hgi]
  ring

theorem hmean_add (c : ℝ) {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g) (η : ℝ) :
    hmean c (fun w => f w + g w) η = hmean c f η + hmean c g η := by
  have hfi : Integrable (fun q : ℝ => f (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (hf.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have hgi : Integrable (fun q : ℝ => g (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (hg.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  unfold hmean
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, integral_add hfi hgi]
  ring

def vhaOsc (c : ℝ) (q : Plane → ℝ) : Plane → ℝ :=
  fun z => q z - hmean c q z.2

theorem contDiffOn_snd_lift {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => g x.1 x.2.2) (Ioi 0 ×ˢ univ) := by
  have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
  exact hg.comp hproj.contDiffOn (fun _ hx => ⟨hx.1, mem_univ _⟩)

private def sndPlane1D : Plane →L[ℝ] Plane :=
  (0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem sndPlane1D_apply (w : Plane) : sndPlane1D w = (0, w.2) := rfl

private theorem norm_sndPlane1D_le_one : ‖sndPlane1D‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul, sndPlane1D_apply, Prod.norm_def, Prod.norm_def, norm_zero]
  exact max_le ((norm_nonneg w.1).trans (le_max_left _ _)) (le_max_right _ _)

private theorem slice_snd1D_iteratedFDeriv {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (q : ℝ) (n : ℕ) (w : Plane) :
    iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w =
      (iteratedFDeriv ℝ n G (q, w.2)).compContinuousLinearMap
        (fun _ : Fin n => sndPlane1D) := by
  have hsmooth : ContDiff ℝ ∞ (fun z : Plane => G (z + (q, 0))) :=
    hG.comp (contDiff_id.add contDiff_const)
  have hfun : (fun w' : Plane => G (q, w'.2)) =
      (fun z : Plane => G (z + (q, 0))) ∘ sndPlane1D := by
    funext w'
    simp [sndPlane1D_apply]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (i := n)
    sndPlane1D hsmooth w (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  have hw : sndPlane1D w + (q, 0) = (q, w.2) := by ext <;> simp [sndPlane1D_apply]
  rw [hw]

private theorem norm_slice_snd1D_iteratedFDeriv_le {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (q : ℝ) (n : ℕ) (w : Plane) :
    ‖iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w‖ ≤
      ‖iteratedFDeriv ℝ n G (q, w.2)‖ := by
  rw [slice_snd1D_iteratedFDeriv hG q n w]
  have hprod : ∏ _i : Fin n, ‖sndPlane1D‖ ≤ 1 := by
    calc ∏ _i : Fin n, ‖sndPlane1D‖
        ≤ ∏ _i : Fin n, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_sndPlane1D_le_one)
      _ = 1 := Finset.prod_const_one
  calc ‖(iteratedFDeriv ℝ n G (q, w.2)).compContinuousLinearMap (fun _ => sndPlane1D)‖
      ≤ ‖iteratedFDeriv ℝ n G (q, w.2)‖ * ∏ _i : Fin n, ‖sndPlane1D‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n G (q, w.2)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n G (q, w.2)‖ := mul_one _

private theorem slice_snd1D_continuous {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (w : Plane) :
    Continuous (fun q : ℝ => iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w) := by
  have hcont : Continuous (fun q : ℝ => iteratedFDeriv ℝ n G (q, w.2)) :=
    (hG.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ =>
      A.compContinuousLinearMap (fun _ : Fin n => sndPlane1D)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => sndPlane1D)).continuous
  refine (hT.comp hcont).congr fun q => ?_
  exact (slice_snd1D_iteratedFDeriv hG q n w).symm

private theorem slice_snd1D_locDominated {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G) (c : ℝ) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (Ioc (-c / 2) (c / 2)))
      (fun (q : ℝ) (w : Plane) => G (q, w.2)) univ := by
  intro n x _
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    isCompact_Icc.prod (isCompact_closedBall x 1)
  have hcont : ContinuousOn (fun p : ℝ × Plane => iteratedFDeriv ℝ n G (p.1, p.2.2))
      (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    ((hG.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos,
    fun _ => C, integrable_const _, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-c / 2) (c / 2)))]
    with q hq y hy
  exact (norm_slice_snd1D_iteratedFDeriv_le hG q n y).trans
    (hC (q, y) ⟨Ioc_subset_Icc_self hq, hy⟩)

theorem iteratedDeriv_hmean_scalar_eq {c : ℝ} (hc : 0 < c) {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ∀ (ℓ : ℕ) {s : ℝ}, 0 < s → ∀ η : ℝ,
      iteratedDeriv ℓ (fun r => hmean c (f r) η) s =
        hmean c (fun w => iteratedDeriv ℓ (fun r => f r w) s) η
  | 0, _, _, _ => rfl
  | ℓ + 1, s, hs, η => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => hmean c (f r) η) =ᶠ[𝓝 s]
        fun r => hmean c (fun w => iteratedDeriv ℓ (fun r' => f r' w) r) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using iteratedDeriv_hmean_scalar_eq hc hf ℓ hr η
    rw [hev.deriv_eq, hmeanDerivS c hc (fun r w => iteratedDeriv ℓ (fun r' => f r' w) r)
      (PartI_T22.contDiffOn_iteratedDeriv_age hf ℓ) s hs η]
    simp only [iteratedDeriv_succ]

theorem norm_ageJet_hmean_scalar_le {c B : ℝ} (hc : 0 < c) (_hB : 0 ≤ B)
    {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ m : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hpt : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖ageJet ℓ m f s (q, z.2)‖ ≤ B) :
    ‖ageJet ℓ m (fun r w => hmean c (f r) w.2) s z‖ ≤ B := by
  let G : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => f r w) s
  have hG : ContDiff ℝ ∞ G := PartI_T22.contDiff_slice_iteratedDeriv hf ℓ hs
  have hhm_eq : ageJet ℓ m (fun r w => hmean c (f r) w.2) s z =
      jet m (fun w : Plane => hmean c G w.2) z := by
    unfold ageJet jet
    congr 1
    funext w
    exact iteratedDeriv_hmean_scalar_eq hc hf ℓ hs w.2
  rw [hhm_eq]
  let μ : Measure ℝ := volume.restrict (Ioc (-c / 2) (c / 2))
  let S : ℝ →L[ℝ] ℝ := c⁻¹ • ContinuousLinearMap.id ℝ ℝ
  let I : Plane → ℝ := fun w => ∫ q, G (q, w.2) ∂μ
  have hsmooth : ∀ q : ℝ, ContDiff ℝ ∞ (fun w : Plane => G (q, w.2)) :=
    fun _ => hG.comp (contDiff_const.prodMk contDiff_snd)
  have hmeas : ∀ (n : ℕ) (w : Plane),
      AEStronglyMeasurable (fun q => iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w) μ :=
    fun n w => (slice_snd1D_continuous hG n w).aestronglyMeasurable
  have hdom := slice_snd1D_locDominated hG c
  have hI_cd : ContDiffOn ℝ ∞ I univ :=
    UnforcedLeray.Kernels.contDiffOn_integral isOpen_univ (ae_of_all _ hsmooth) hmeas hdom
  have hI_at : ContDiffAt ℝ m I z :=
    (hI_cd.contDiffAt (isOpen_univ.mem_nhds (mem_univ z))).of_le (by exact_mod_cast le_top)
  have hfun : (fun w : Plane => hmean c G w.2) = S ∘ I := rfl
  unfold jet
  rw [hfun, S.iteratedFDeriv_comp_left hI_at le_rfl]
  have hS_norm : ‖S‖ ≤ c⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le) fun x => ?_
    simp [S, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
  have hint_le := UnforcedLeray.Kernels.norm_iteratedFDeriv_integral_le isOpen_univ
    (ae_of_all _ hsmooth) hmeas hdom m (mem_univ z)
  have hslice_le : ∀ q ∈ Ioc (-c / 2) (c / 2),
      ‖iteratedFDeriv ℝ m (fun w : Plane => G (q, w.2)) z‖ ≤ B := by
    intro q hq
    exact (norm_slice_snd1D_iteratedFDeriv_le hG q m z).trans (hpt q hq)
  have hint_bound : ∫ q in Ioc (-c / 2) (c / 2),
      ‖iteratedFDeriv ℝ m (fun w : Plane => G (q, w.2)) z‖ ≤ B * c := by
    have h0 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => ‖iteratedFDeriv ℝ m (fun w : Plane => G (q, w.2)) z‖)
      (C := B) measure_Ioc_lt_top (fun q hq => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hslice_le q hq)
    rw [Real.volume_real_Ioc_of_le (by linarith), show c / 2 - -c / 2 = c by ring] at h0
    exact (le_abs_self _).trans h0
  calc ‖S.compContinuousMultilinearMap (iteratedFDeriv ℝ m I z)‖
      ≤ ‖S‖ * ‖iteratedFDeriv ℝ m I z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ c⁻¹ * (∫ q, ‖iteratedFDeriv ℝ m (fun w : Plane => G (q, w.2)) z‖ ∂μ) :=
        mul_le_mul hS_norm hint_le (norm_nonneg _) (inv_nonneg.2 hc.le)
    _ ≤ c⁻¹ * (B * c) := mul_le_mul_of_nonneg_left hint_bound (inv_nonneg.2 hc.le)
    _ = B := by field_simp [hc.ne']

theorem partialX_vhaOsc {c : ℝ} (hc : 0 < c) {q : Plane → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqp : B0151.IsPeriodicQ c q) :
    GaussianVortex.partialX (vhaOsc c q) = vhaOsc c (GaussianVortex.partialX q) := by
  funext z
  have h1 : GaussianVortex.partialX (vhaOsc c q) z = GaussianVortex.partialX q z := by
    show deriv (fun x : ℝ => q (x, z.2) - hmean c q z.2) z.1 =
      deriv (fun x : ℝ => q (x, z.2)) z.1
    exact deriv_sub_const (hmean c q z.2)
  have hC2 := Cyl.C2.of_contDiff (hq.of_le (by norm_num))
  have hqp' : Cyl.IsPeriodic c q := fun w => hqp w.1 w.2
  have hint0 : ∫ x in Ioc (-c / 2) (c / 2), Cyl.partialQ q (x, z.2) = 0 :=
    cpHL_integral_partialQ_zero hc (hq.differentiable (by simp)) hC2.contQ hqp' z.2
  have hm0 : hmean c (GaussianVortex.partialX q) z.2 = 0 := by
    unfold hmean
    change c⁻¹ • ∫ x in Ioc (-c / 2) (c / 2), Cyl.partialQ q (x, z.2) = 0
    rw [hint0, smul_zero]
  change GaussianVortex.partialX (vhaOsc c q) z =
    GaussianVortex.partialX q z - hmean c (GaussianVortex.partialX q) z.2
  rw [h1, hm0, sub_zero]

theorem partialY_vhaOsc (c : ℝ) {q : Plane → ℝ} (hq : ContDiff ℝ ∞ q) :
    GaussianVortex.partialY (vhaOsc c q) = vhaOsc c (GaussianVortex.partialY q) := by
  funext z
  have hqd : Differentiable ℝ q := hq.differentiable (by simp)
  have hpath : HasDerivAt (fun y : ℝ => ((z.1, y) : Plane)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hd_q : HasDerivAt (fun y : ℝ => q (z.1, y)) (GaussianVortex.partialY q z) z.2 :=
    ((hqd z).comp z.2 hpath.differentiableAt).hasDerivAt
  have hd_m : HasDerivAt (hmean c q) (hmean c (GaussianVortex.partialY q) z.2) z.2 :=
    cpH2_hasDerivAt_hmean (hq.of_le (by norm_num)) z.2
  exact (hd_q.sub hd_m).deriv

theorem iteratedDeriv_hfluct_v_comp_eq {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (k : Fin 2) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    iteratedDeriv ℓ (fun r => (hfluct c (tr.v r) z) k) s =
      vhaOsc c (fun w => iteratedDeriv ℓ (fun r => tr.v r w k) s) z := by
  have hv_joint : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hvk_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
  have hmk_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (fun w => tr.v x.1 w k) x.2.2)
      (Ioi 0 ×ˢ univ) :=
    contDiffOn_snd_lift (g := fun r η => hmean c (fun w => tr.v r w k) η)
      (hmeanContDiff c hc (fun r w => tr.v r w k) hvk_sm)
  have hev : (fun r => (hfluct c (tr.v r) z) k) =ᶠ[𝓝 s]
      fun r => tr.v r z k - hmean c (fun w => tr.v r w k) z.2 := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    have hvc : Continuous (tr.v r) := (bucVel_vslice_contDiff tr hr.le).continuous
    change (tr.v r z - hmean c (tr.v r) z.2) k = _
    rw [PiLp.sub_apply, PartI_T22.hmean_apply_vec' c hvc z.2 k]
  have hsub := iteratedDeriv_sub
    (PartI_T22.contDiffAt_age_slice (F := fun r w => tr.v r w k) hvk_sm hs z ℓ)
    (PartI_T22.contDiffAt_age_slice (F := fun r w => hmean c (fun y => tr.v r y k) w.2) hmk_sm hs z ℓ)
  rw [hev.iteratedDeriv_eq ℓ]
  exact hsub.trans (by rw [iteratedDeriv_hmean_scalar_eq hc hvk_sm ℓ hs z.2]; rfl)

theorem vhaOsc_lapS_eq {c : ℝ} (hc : 0 < c) {q : Plane → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqp : B0151.IsPeriodicQ c q) (z : Plane) :
    vhaOsc c (Train.lapS q) z = Train.lapS (vhaOsc c q) z := by
  have hQ1 : ContDiff ℝ ∞ (GaussianVortex.partialX q) := B0151.contDiff_partialX_infty hq
  have hQ2 : ContDiff ℝ ∞ (GaussianVortex.partialX (GaussianVortex.partialX q)) :=
    B0151.contDiff_partialX_infty hQ1
  have hE1 : ContDiff ℝ ∞ (GaussianVortex.partialY q) := B0151.contDiff_partialY_infty hq
  have hE2 : ContDiff ℝ ∞ (GaussianVortex.partialY (GaussianVortex.partialY q)) :=
    B0151.contDiff_partialY_infty hE1
  have hQ1_per : B0151.IsPeriodicQ c (GaussianVortex.partialX q) :=
    B0151.periodic_derivWord hqp [true]
  have hXX : GaussianVortex.partialX (GaussianVortex.partialX (vhaOsc c q)) =
      vhaOsc c (GaussianVortex.partialX (GaussianVortex.partialX q)) := by
    rw [partialX_vhaOsc hc hq hqp, partialX_vhaOsc hc hQ1 hQ1_per]
  have hYY : GaussianVortex.partialY (GaussianVortex.partialY (vhaOsc c q)) =
      vhaOsc c (GaussianVortex.partialY (GaussianVortex.partialY q)) := by
    rw [partialY_vhaOsc c hq, partialY_vhaOsc c hE1]
  change vhaOsc c
    (fun w => GaussianVortex.partialX (GaussianVortex.partialX q) w +
      GaussianVortex.partialY (GaussianVortex.partialY q) w) z =
    GaussianVortex.partialX (GaussianVortex.partialX (vhaOsc c q)) z +
      GaussianVortex.partialY (GaussianVortex.partialY (vhaOsc c q)) z
  rw [hXX, hYY]
  unfold vhaOsc
  rw [hmean_add c hQ2.continuous hE2.continuous z.2]
  ring

theorem deriv_vel_comp_eq_momentum {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (k : Fin 2) {r : ℝ} (hr : 0 < r) (w : Plane) :
    deriv (fun t => tr.v t w k) r =
      ν * Train.lapS (fun y => tr.v r y k) w -
        ((Train.advection (tr.v r) w) k + (Train.gradS (tr.p r) w) k) := by
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hd := PartI_T20.iteratedDeriv_vec_proj_eq hsm_v k 1 hr w
  rw [iteratedDeriv_one, iteratedDeriv_one] at hd
  rw [hd]
  fin_cases k
  · have hm := congrArg (fun X : Vec => X 0) (tr.isTrain.momentum r hr w)
    simp only [Train.momentumResidual, Train.vecLaplacian,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      toVec_zero, PiLp.zero_apply] at hm
    change (deriv (fun t => tr.v t w) r) 0 =
      ν * Train.lapS (fun y => tr.v r y 0) w -
        ((Train.advection (tr.v r) w) 0 + (Train.gradS (tr.p r) w) 0)
    linarith
  · have hm := congrArg (fun X : Vec => X 1) (tr.isTrain.momentum r hr w)
    simp only [Train.momentumResidual, Train.vecLaplacian,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      toVec_one, PiLp.zero_apply] at hm
    change (deriv (fun t => tr.v t w) r) 1 =
      ν * Train.lapS (fun y => tr.v r y 1) w -
        ((Train.advection (tr.v r) w) 1 + (Train.gradS (tr.p r) w) 1)
    linarith

/-- Pointwise age-derivative identity for each component `k : Fin 2` of `v_fluct`:
`deriv (fun t => (hfluct c (tr.v t) z) k) r = ν * lapS (v_fluct r · k) z - AdvGrad_k r z + hmean c (AdvGrad_k r) z.2`. -/
theorem deriv_hfluct_v_comp_eq {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (k : Fin 2) {r : ℝ} (hr : 0 < r) (z : Plane) :
    let v_fluct : ℝ → Plane → Vec := fun t => hfluct c (tr.v t)
    let AdvGrad_k : ℝ → Plane → ℝ := fun t w =>
      (Train.advection (tr.v t) w) k + (Train.gradS (tr.p t) w) k
    deriv (fun t => (v_fluct t z) k) r =
      (ν * Train.lapS (fun y => (v_fluct r y) k) z - AdvGrad_k r z) +
        hmean c (AdvGrad_k r) z.2 := by
  intro v_fluct AdvGrad_k
  have h1 := iteratedDeriv_hfluct_v_comp_eq hc tr k 1 hr z
  rw [iteratedDeriv_one] at h1
  have h2 : (fun w : Plane => iteratedDeriv 1 (fun t => tr.v t w k) r) =
      fun w : Plane => ν * Train.lapS (fun y => tr.v r y k) w - AdvGrad_k r w := by
    funext w
    rw [iteratedDeriv_one]
    exact deriv_vel_comp_eq_momentum tr k hr w
  rw [h1, h2]
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_vk : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hu_k : ContDiff ℝ ∞ (fun y : Plane => tr.v r y k) :=
    PartI_T20.contDiff_slice_of_smR (F := fun t y => tr.v t y k) hsm_vk hr
  have hup_k : B0151.IsPeriodicQ c (fun y : Plane => tr.v r y k) := fun q η =>
    congrArg (fun u : Vec => u k) (tr.isTrain.periodic_v r hr.le (q, η))
  have hlap_cd : ContDiff ℝ ∞ (Train.lapS (fun y : Plane => tr.v r y k)) := by
    unfold Train.lapS
    exact (B0151.contDiff_partialX_infty (B0151.contDiff_partialX_infty hu_k)).add
      (B0151.contDiff_partialY_infty (B0151.contDiff_partialY_infty hu_k))
  have hsm_adv_k : PartI_T20.SmR (fun x : ℝ × Plane => (Train.advection (tr.v x.1) x.2) k) :=
    smR_advection_comp hsm_v k
  have hsm_gp_k : PartI_T20.SmR (fun x : ℝ × Plane => (Train.gradS (tr.p x.1) x.2) k) :=
    smR_gradS_comp hsm_p k
  have hadv_cont : Continuous (AdvGrad_k r) :=
    (PartI_T20.contDiff_slice_of_smR (F := AdvGrad_k) (hsm_adv_k.add hsm_gp_k) hr).continuous
  have hosc_lap := vhaOsc_lapS_eq hc hu_k hup_k z
  have hvfl_eq : vhaOsc c (fun y : Plane => tr.v r y k) =
      fun y : Plane => (v_fluct r y) k := by
    funext y
    have hvc : Continuous (tr.v r) := (bucVel_vslice_contDiff tr hr.le).continuous
    change tr.v r y k - hmean c (fun w => tr.v r w k) y.2 =
      (tr.v r y - hmean c (tr.v r) y.2) k
    rw [PiLp.sub_apply, PartI_T22.hmean_apply_vec' c hvc y.2 k]
  rw [hvfl_eq] at hosc_lap
  unfold vhaOsc at hosc_lap ⊢
  have hsub_m := hmean_sub c (f := fun w => ν * Train.lapS (fun y => tr.v r y k) w)
    (g := AdvGrad_k r) (continuous_const.mul hlap_cd.continuous) hadv_cont z.2
  have hmul_m := hmean_const_mul c ν (f := Train.lapS (fun y => tr.v r y k)) hlap_cd.continuous z.2
  dsimp only
  rw [hsub_m, hmul_m, ← hosc_lap]
  ring

theorem norm_ageJet_gradS_comp_le {P : ℝ → Plane → ℝ}
    (hP : PartI_T20.SmR (fun x : ℝ × Plane => P x.1 x.2)) (k : Fin 2)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => (Train.gradS (P r) w) k) s z‖ ≤ ‖ageJet ℓ (j + 1) P s z‖ := by
  fin_cases k
  · change ‖ageJet ℓ j (fun r w => (Train.gradS (P r) w) 0) s z‖ ≤ ‖ageJet ℓ (j + 1) P s z‖
    have hfun : (fun r w => (Train.gradS (P r) w) 0) = fun r w => Cyl.partialQ (P r) w := by
      funext r w; exact toVec_zero _
    rw [hfun]
    exact PartI_T20.norm_ageJet_partialQ_le hP ℓ j hs z
  · change ‖ageJet ℓ j (fun r w => (Train.gradS (P r) w) 1) s z‖ ≤ ‖ageJet ℓ (j + 1) P s z‖
    have hfun : (fun r w => (Train.gradS (P r) w) 1) = fun r w => Cyl.partialEta (P r) w := by
      funext r w; exact toVec_one _
    rw [hfun]
    exact PartI_T20.norm_ageJet_partialEta_le hP ℓ j hs z

/-- Componentwise bound on `ageJet (ℓ + 1) j (fun r w => (v_fluct r w) k) s z` from rectangle bounds
`M_V` on `tr.v` and `M_fl` on `(v_fluct, tr.p)`. -/
theorem norm_ageJet_succ_hfluct_v_comp_le {ν c M_V M_fl : ℝ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c) (hMV : 0 ≤ M_V) (hMfl : 0 ≤ M_fl)
    (tr : B0140.TrainSol ν c) (k : Fin 2) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hV_bd : ∀ w : Plane, ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i tr.v s w‖ ≤ M_V)
    (hFl_bd : ∀ w : Plane, ∀ r ≤ ℓ, ∀ i ≤ j + 2,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s w‖ ≤ M_fl ∧
      ‖ageJet r i tr.p s w‖ ≤ M_fl) :
    ‖ageJet (ℓ + 1) j (fun r w => (hfluct c (tr.v r) w) k) s z‖ ≤
      6 * M_fl + 4 * (2 : ℝ) ^ (ℓ + j) * M_V * M_fl := by
  let v_fluct : ℝ → Plane → Vec := fun t => hfluct c (tr.v t)
  let V_k : ℝ → Plane → ℝ := fun r w => ν * Train.lapS (fun y => (v_fluct r y) k) w
  let AdvGrad_k : ℝ → Plane → ℝ := fun r w =>
    (Train.advection (tr.v r) w) k + (Train.gradS (tr.p r) w) k
  let M_k : ℝ → Plane → ℝ := fun r w => hmean c (AdvGrad_k r) w.2
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_fl : Sm (fun x : ℝ × Plane => v_fluct x.1 x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_flk : PartI_T20.SmR (fun x : ℝ × Plane => (v_fluct x.1 x.2) k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_fl
  have hsm_Vk : PartI_T20.SmR (fun x : ℝ × Plane => V_k x.1 x.2) :=
    PartI_T20.smR_mul_lapS (F := fun r y => (v_fluct r y) k) hsm_flk ν
  have hsm_adv_k : PartI_T20.SmR (fun x : ℝ × Plane => (Train.advection (tr.v x.1) x.2) k) :=
    smR_advection_comp hsm_v k
  have hsm_gp_k : PartI_T20.SmR (fun x : ℝ × Plane => (Train.gradS (tr.p x.1) x.2) k) :=
    smR_gradS_comp hsm_p k
  have hsm_AG : PartI_T20.SmR (fun x : ℝ × Plane => AdvGrad_k x.1 x.2) :=
    hsm_adv_k.add hsm_gp_k
  have hsm_Mk : PartI_T20.SmR (fun x : ℝ × Plane => M_k x.1 x.2) :=
    contDiffOn_snd_lift (g := fun r η => hmean c (AdvGrad_k r) η)
      (hmeanContDiff c hc AdvGrad_k hsm_AG)
  have hstep : ageJet (ℓ + 1) j (fun r w => (v_fluct r w) k) s =
      ageJet ℓ j (fun r w => (V_k r w - AdvGrad_k r w) + M_k r w) s := by
    unfold ageJet
    congr 1
    funext w
    rw [iteratedDeriv_succ']
    have hev : deriv (fun r => (v_fluct r w) k) =ᶠ[𝓝 s]
        fun r => (V_k r w - AdvGrad_k r w) + M_k r w := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using deriv_hfluct_v_comp_eq hc tr k hr w
    exact hev.iteratedDeriv_eq ℓ
  have hsplit : ageJet (ℓ + 1) j (fun r w => (v_fluct r w) k) s z =
      (ageJet ℓ j V_k s z - ageJet ℓ j AdvGrad_k s z) + ageJet ℓ j M_k s z := by
    rw [hstep, PartI_T22.ageJet_add (fun r w => V_k r w - AdvGrad_k r w) M_k
      (hsm_Vk.sub hsm_AG) hsm_Mk hs ℓ j z,
      PartI_T22.ageJet_sub V_k AdvGrad_k hsm_Vk hsm_AG hs ℓ j z]
  have hb_V : ‖ageJet ℓ j V_k s z‖ ≤ 2 * M_fl := by
    calc ‖ageJet ℓ j V_k s z‖
        ≤ (2 * ν) * ‖ageJet ℓ (j + 2) (fun r w => (v_fluct r w) k) s z‖ :=
          PartI_T20.norm_ageJet_mul_lapS_le (F := fun r w => (v_fluct r w) k) hsm_flk hν.le ℓ j hs z
      _ ≤ (2 * ν) * ‖ageJet ℓ (j + 2) v_fluct s z‖ :=
          mul_le_mul_of_nonneg_left
            (PartI_T20.norm_ageJet_vec_proj_le hsm_fl k ℓ (j + 2) hs z) (by positivity)
      _ ≤ (2 * ν) * M_fl :=
          mul_le_mul_of_nonneg_left (hFl_bd z ℓ le_rfl (j + 2) le_rfl).1 (by positivity)
      _ ≤ 2 * M_fl := by nlinarith
  let B_AG : ℝ := 2 * (2 : ℝ) ^ (ℓ + j) * M_V * M_fl + 2 * M_fl
  have hBAG_nn : 0 ≤ B_AG := by dsimp [B_AG]; positivity
  have hb_AG : ∀ w : Plane, ‖ageJet ℓ j AdvGrad_k s w‖ ≤ B_AG := by
    intro w
    rw [PartI_T22.ageJet_add (fun r y => (Train.advection (tr.v r) y) k)
      (fun r y => (Train.gradS (tr.p r) y) k) hsm_adv_k hsm_gp_k hs ℓ j w]
    have hadv := norm_ageJet_advection_train_comp_le hν hc hMV hMfl tr k ℓ j hs w
      (hV_bd w) (fun r hr i hi => (hFl_bd w r hr i (by omega)).1)
    have hgp : ‖ageJet ℓ j (fun r y => (Train.gradS (tr.p r) y) k) s w‖ ≤ 2 * M_fl := by
      have h1 := (norm_ageJet_gradS_comp_le hsm_p k ℓ j hs w).trans
        (hFl_bd w ℓ le_rfl (j + 1) (by omega)).2
      linarith
    exact (norm_add_le _ _).trans (add_le_add hadv hgp)
  have hb_M : ‖ageJet ℓ j M_k s z‖ ≤ B_AG :=
    norm_ageJet_hmean_scalar_le hc hBAG_nn hsm_AG ℓ j hs z
      (fun q _ => hb_AG (q, z.2))
  have hb_AG_z := hb_AG z
  rw [hsplit]
  have htri1 := norm_add_le (ageJet ℓ j V_k s z - ageJet ℓ j AdvGrad_k s z) (ageJet ℓ j M_k s z)
  have htri2 := norm_sub_le (ageJet ℓ j V_k s z) (ageJet ℓ j AdvGrad_k s z)
  dsimp [B_AG] at hb_AG_z hb_M
  linarith

end PartI_T22_2_1

open PartI_T22_2_1 in
/-- **Higher-age velocity-fluctuation inductive step (`PartI:T22/2/1`)**:
proves `TrainPostOverlapVelFluctHigherStep`. -/
theorem trainPostOverlapVelFluctHigherStep_proof : TrainPostOverlapVelFluctHigherStep := by
  intro hTails _hVel0 _hSP0 _hOv ℓ hIH ρ hρ j
  obtain ⟨C_V, N_V, ν_V, hC_V, hν_V, hV_rect⟩ :=
    uniform_vel_polyPS_rect hTails hρ (j + 1) ℓ
  obtain ⟨C_fl, N_fl, lam_fl, ν_fl, hC_fl, hlam_fl, hν_fl, hFl_rect⟩ :=
    uniform_velPress_exp_rect hIH hρ (j + 2)
  obtain ⟨νp, hνp, _hνp1, hp_asymp⟩ := trainPeriodAsymptotics_proof ρ hρ 1 one_pos
  let K_abs : ℝ := (N_V.factorial : ℝ) * ((lam_fl / 2) ^ N_V)⁻¹ * Real.exp (lam_fl / 2)
  have hfac_pos : (0 : ℝ) < N_V.factorial := by exact_mod_cast N_V.factorial_pos
  have hK_abs : 0 < K_abs := by dsimp [K_abs]; positivity
  let C_out : ℝ := 12 * C_fl + 8 * (2 : ℝ) ^ (ℓ + j) * (C_V * C_fl * K_abs)
  let N_out : ℕ := 4 * N_V + N_fl
  let lam_out : ℝ := lam_fl / 2
  let ν₀ : ℝ := min (min ν_V ν_fl) (min νp 1)
  have hC_out : 0 < C_out := by dsimp [C_out]; positivity
  have hlam_out : 0 < lam_out := by dsimp [lam_out]; positivity
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_V hν_fl) (lt_min hνp zero_lt_one)
  refine ⟨C_out, N_out, lam_out, ν₀, hC_out, hlam_out, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hν_V_le : ν ≤ ν_V := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_fl_le : ν ≤ ν_fl := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_p_le : ν ≤ νp := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : ν ≤ 1 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hc1, _⟩ := hp_asymp ν hν hν_p_le
  let c := trainPeriod ρ ν
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let M_V : ℝ := polyPS C_V N_V ν c s
  let M_fl : ℝ := polyP C_fl N_fl ν c * Real.exp (-(lam_fl * ν * s / c ^ 2))
  have hMV : 0 ≤ M_V := by dsimp [M_V]; unfold polyPS; positivity
  have hMfl : 0 ≤ M_fl := by dsimp [M_fl]; unfold polyP; positivity
  refine wSupNorm_zero_le_of_norm_le fun z => ?_
  have hsm_fl : Sm (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hvec := norm_ageJet_vec_le_add_proj
    (V := fun r w => hfluct c (tr.v r) w) hsm_fl (ℓ + 1) j hs z
  have h0 := norm_ageJet_succ_hfluct_v_comp_le hν hν1 hc hMV hMfl tr 0 ℓ j hs z
    (hV_rect ν hν hν_V_le tr htr s hs) (hFl_rect ν hν hν_fl_le tr htr s hs hsc)
  have h1 := norm_ageJet_succ_hfluct_v_comp_le hν hν1 hc hMV hMfl tr 1 ℓ j hs z
    (hV_rect ν hν hν_V_le tr htr s hs) (hFl_rect ν hν hν_fl_le tr htr s hs hsc)
  have hpt : ‖ageJet (ℓ + 1) j (fun r => hfluct c (tr.v r)) s z‖ ≤
      12 * M_fl + 8 * (2 : ℝ) ^ (ℓ + j) * (M_V * M_fl) := by linarith
  refine hpt.trans ?_
  have habs := polyPS_mul_polyP_exp_le N_V N_fl hC_V hC_fl hlam_fl hν hc1 hs.le
  have hMfl_le : M_fl ≤ polyP C_fl N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) :=
    polyP_exp_mono C_fl C_fl lam_fl lam_out N_fl N_out hC_fl.le le_rfl
      (Nat.le_add_left N_fl (4 * N_V)) (by dsimp [lam_out]; linarith) hν hc.le hs.le
  calc 12 * M_fl + 8 * (2 : ℝ) ^ (ℓ + j) * (M_V * M_fl)
      ≤ 12 * (polyP C_fl N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2))) +
          8 * (2 : ℝ) ^ (ℓ + j) *
            (polyP (C_V * C_fl * K_abs) N_out ν c *
              Real.exp (-(lam_out * ν * s / c ^ 2))) :=
        add_le_add (mul_le_mul_of_nonneg_left hMfl_le (by norm_num))
          (mul_le_mul_of_nonneg_left habs (by positivity))
    _ = polyP C_out N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) := by
        unfold polyP
        dsimp [C_out]
        ring

end UnforcedLeray.Short.PartI

end
