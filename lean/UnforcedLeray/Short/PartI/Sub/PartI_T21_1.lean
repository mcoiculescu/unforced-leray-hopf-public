import UnforcedLeray.Short.PartI.Sub.PartI_T21

/-!
# `PartI:T21/1` (`Sub/PartI_T21_1.lean`): decomposition of `TrainStreamVelocityPressureTransverseTail`

Source of record: `the November 2 reference manuscript`, lines 499-526
(old 493-515), in the proof of Lemma `sct:heat`.

This module develops the structure and helper estimates for `PartI:T21/1`
(`TrainStreamVelocityPressureTransverseTail`):
1. **Gaussian tail shift and monotony helpers** (`PartI_T21.gaussian_shift_mul_le`,
   `PartI_T21.tail_kernel_mono`, `PartI_T21.polyPS_mono`):
   for `a, u ≥ 0` and `b, A > 0`, `exp(-b (a + u)² / A) ≤ exp(-b a² / A) * exp(-b u² / A)`,
   and the combined cylinder/Gaussian tail factor
   `exp(-b l / c) + exp(-b l² / (C₀ + ν S_*))` is monotone in `(b, C₀)` and `polyPS`.
2. **Decomposition into the three physical cylinder-Poisson steps** (source lines 499-526):
   * `TrainNonzeroModeStreamVelTail` (`PartI:T21/1/1`, source lines 499-503): nonzero-mode
     (`n ≠ 0`) cylinder Biot-Savart tail for the fluctuations `ψ̃ = ψ - S` and `ṽ = hfluct c v`
     from `TrainVorticityGaussianTail`;
   * `TrainZeroModeStreamVelTail` (`PartI:T21/1/2`, source lines 504-513): zero-mode (`n = 0`)
     1D integration tail for the horizontal mean stream `S` and mean velocity `\bar v` from
     `-∂_η² S = \bar ω`, evenness of `S` (`PartI_T21.train_meanStream_even`), and zero total
     circulation;
   * `TrainPressureTransverseTail` (`PartI:T21/1/3`, source lines 517-525): cylinder Poisson
     tail for the Leray pressure `p` from `-Δ p = ∂_i ∂_j (v_i v_j)` and the velocity/stream
     tails.
3. **Unconditional parameter-unification and triangle-inequality assembly**
   (`trainStreamVelocityPressureTransverseTail_of`), composed by `PartI:T21/1`
   (`Short/PartI/Sub/PartI_T21/TransverseTail.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap)

/-! ### 1. Physical sub-obligations for `PartI:T21/1` (source lines 499-526) -/

/-- **Sub-obligation 1a (`TrainNonzeroModeStreamVelTail`, `PartI:T21/1/1`, source lines 499-503)**:
on the cylinder `(ℝ / cℤ) × ℝ`, the horizontal fluctuations
`ψ̃(r, z) = tr.ψ r z - meanStream tr r z.2` and `ṽ(r, z) = hfluct c (tr.v r) z` have zero
horizontal mean and solve `-Δ ψ̃ = ω̃`, `ṽ = ∇^⊥ ψ̃`. Convolving the nonzero-mode (`k_n = 2π|n|/c`)
Green's kernel `(2 k_n)⁻¹ exp(-k_n |η - η'|)` with the Gaussian vorticity tail
(`TrainVorticityGaussianTail`) and summing over `n ≠ 0` gives the combined exponential + Gaussian
transverse tail on `|z.2| ≥ C'/ν + 2 + l`. -/
def TrainNonzeroModeStreamVelTail : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
          let c := trainPeriod ρ ν
          let K : ℝ := polyPS C N ν c S_ *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))
          ‖ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤ K ∧
          ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ ≤ K

/-- **Sub-obligation 1b (`TrainZeroModeStreamVelTail`, `PartI:T21/1/2`, source lines 504-513)**:
the zero mode `S(r, η) = meanStream tr r η` satisfies `-∂_η² S = \bar ω`, `\bar v₁ = -∂_η S`,
`\bar v₂ = 0`, `S(r, -η) = S(r, η)` (`PartI_T21.train_meanStream_even`), and zero total
circulation `∫_{-∞}^∞ \bar ω(r, η) dη = 0`. Integrating `\bar ω` from `|z.2| ≥ C'/ν + 2 + l` to
`∞` bounds the mean contribution `ageJet ℓ j tr.ψ - ageJet ℓ j ψ̃` and
`ageJet ℓ j tr.v - ageJet ℓ j ṽ` by a Gaussian tail `polyPS C N ν c S_ * exp(-b l² / (C₀ + ν S_))`. -/
def TrainZeroModeStreamVelTail : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
          let c := trainPeriod ρ ν
          let K_g : ℝ := polyPS C N ν c S_ * Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))
          ‖ageJet ℓ j tr.ψ s z -
              ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤ K_g ∧
          ‖ageJet ℓ j tr.v s z -
              ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ ≤ K_g

/-- **Sub-obligation 1c (`TrainPressureTransverseTail`, `PartI:T21/1/3`, source lines 517-525)**:
on the cylinder, `-Δ p = ∂_i ∂_j (v_i v_j)` with source quadratically small in `v` and its
derivatives; repeating the zero-mode + nonzero-mode cylinder Poisson inversion yields the
same combined exponential + Gaussian transverse tail for `ageJet ℓ j tr.p`. -/
def TrainPressureTransverseTail : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
          let c := trainPeriod ρ ν
          let K : ℝ := polyPS C N ν c S_ *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))
          ‖ageJet ℓ j tr.p s z‖ ≤ K

namespace PartI_T21

abbrev TrainNonzeroModeStreamVelTail : Prop :=
  UnforcedLeray.Short.PartI.TrainNonzeroModeStreamVelTail

abbrev TrainZeroModeStreamVelTail : Prop :=
  UnforcedLeray.Short.PartI.TrainZeroModeStreamVelTail

abbrev TrainPressureTransverseTail : Prop :=
  UnforcedLeray.Short.PartI.TrainPressureTransverseTail

/-! ### 2. Gaussian tail shift and monotony helpers -/

/-- For `a, u ≥ 0` and `b, A > 0`, since `(a + u)² ≥ a² + u²`,
`exp(-b (a + u)² / A) ≤ exp(-b a² / A) * exp(-b u² / A)`. -/
theorem gaussian_shift_mul_le {b A a u : ℝ} (hb : 0 < b) (hA : 0 < A)
    (ha : 0 ≤ a) (hu : 0 ≤ u) :
    Real.exp (-(b * (a + u) ^ 2 / A)) ≤
      Real.exp (-(b * a ^ 2 / A)) * Real.exp (-(b * u ^ 2 / A)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hsq : a ^ 2 + u ^ 2 ≤ (a + u) ^ 2 := by nlinarith
  have hnum : b * a ^ 2 + b * u ^ 2 ≤ b * (a + u) ^ 2 := by nlinarith
  have hdiv : (b * a ^ 2 + b * u ^ 2) / A ≤ b * (a + u) ^ 2 / A :=
    div_le_div_of_nonneg_right hnum hA.le
  linarith [show -(b * a ^ 2 / A) + -(b * u ^ 2 / A) = -((b * a ^ 2 + b * u ^ 2) / A) by ring]

/-- Monotonicity of the combined cylinder/Gaussian tail factor
`exp(-b l / c) + exp(-b l² / (C₀ + ν S_))` when decreasing `b` and increasing `C₀`. -/
theorem tail_kernel_mono {b₁ b₂ C₀₁ C₀₂ c ν S_ l : ℝ}
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hC₀₁ : 0 < C₀₁) (hC₀ : C₀₁ ≤ C₀₂)
    (hc : 0 < c) (hν : 0 < ν) (hS_ : 0 ≤ S_) (hl : 0 ≤ l) :
    Real.exp (-(b₂ * l / c)) + Real.exp (-(b₂ * l ^ 2 / (C₀₁ + ν * S_))) ≤
      Real.exp (-(b₁ * l / c)) + Real.exp (-(b₁ * l ^ 2 / (C₀₂ + ν * S_))) := by
  have hexp1 : Real.exp (-(b₂ * l / c)) ≤ Real.exp (-(b₁ * l / c)) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hl) hc.le
  have hexp2 : Real.exp (-(b₂ * l ^ 2 / (C₀₁ + ν * S_))) ≤
      Real.exp (-(b₁ * l ^ 2 / (C₀₂ + ν * S_))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have hnum : b₁ * l ^ 2 ≤ b₂ * l ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg l)
    have hden_pos : 0 < C₀₁ + ν * S_ := by positivity
    have hden : C₀₁ + ν * S_ ≤ C₀₂ + ν * S_ := add_le_add hC₀ le_rfl
    have hb₂ : 0 < b₂ := hb₁.trans_le hb
    exact div_le_div₀ (by positivity) hnum hden_pos hden
  exact add_le_add hexp1 hexp2

/-- Monotonicity of `polyPS C N ν c S_` in `(C, N)` for `ν > 0, c ≥ 0, S_ ≥ 0`. -/
theorem polyPS_mono {C₁ C₂ ν c S_ : ℝ} {N₁ N₂ : ℕ}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hN : N₁ ≤ N₂)
    (hν : 0 < ν) (hc : 0 ≤ c) (hS_ : 0 ≤ S_) :
    polyPS C₁ N₁ ν c S_ ≤ polyPS C₂ N₂ ν c S_ := by
  unfold polyPS
  have h1X : 1 ≤ (1 + c + ν⁻¹) * (1 + S_) := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    nlinarith [mul_nonneg hc hS_, mul_nonneg this hS_]
  exact mul_le_mul hC (pow_le_pow_right₀ h1X hN) (by positivity) (hC₁.trans hC)

end PartI_T21

/-! ### 3. Conditional assembly of `TrainStreamVelocityPressureTransverseTail` -/

/-- **Conditional assembly of `TrainStreamVelocityPressureTransverseTail` (`PartI:T21/1`)**:
combines the nonzero-mode fluctuation tail (`TrainNonzeroModeStreamVelTail`), the zero-mode
mean tail (`TrainZeroModeStreamVelTail`), and the cylinder pressure tail
(`TrainPressureTransverseTail`). Composed by `PartI:T21/1` in
`Short/PartI/Sub/PartI_T21/TransverseTail.lean`. -/
theorem trainStreamVelocityPressureTransverseTail_of
    (hFluct : TrainNonzeroModeStreamVelTail)
    (hZero : TrainZeroModeStreamVelTail)
    (hPress : TrainPressureTransverseTail)
    (_hOv : TrainOverlap)
    (_hVort : TrainVorticityGaussianTail) :
    TrainStreamVelocityPressureTransverseTail := by
  intro ρ hρ ℓ j
  obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hF⟩ := hFluct ρ hρ ℓ j
  obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂, N₂, ν₂, hC₂, hν₂, hZ⟩ := hZero ρ hρ ℓ j
  obtain ⟨b₃, C₀₃, C'₃, hb₃, hC₀₃, hC'₃, C₃, N₃, ν₃, hC₃, hν₃, hP⟩ := hPress ρ hρ ℓ j
  let b := min b₁ (min b₂ b₃)
  let C₀ := max C₀₁ (max C₀₂ C₀₃)
  let C' := max C'₁ (max C'₂ C'₃)
  let C := C₁ + C₂ + C₃
  let N := max N₁ (max N₂ N₃)
  let ν₀ := min ν₁ (min ν₂ ν₃)
  have hb : 0 < b := lt_min hb₁ (lt_min hb₂ hb₃)
  have hC₀ : 0 < C₀ := lt_max_of_lt_left hC₀₁
  have hC' : 0 < C' := lt_max_of_lt_left hC'₁
  have hC : 0 < C := by dsimp [C]; linarith
  have hν₀ : 0 < ν₀ := lt_min hν₁ (lt_min hν₂ hν₃)
  refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, ?_⟩
  intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₃_le : ν ≤ ν₃ := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hz₁ : C'₁ / ν + 2 + l ≤ |z.2| := by
    have : C'₁ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
    linarith
  have hz₂ : C'₂ / ν + 2 + l ≤ |z.2| := by
    have hle : C'₂ ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
    have : C'₂ / ν ≤ C' / ν := div_le_div_of_nonneg_right hle hν.le
    linarith
  have hz₃ : C'₃ / ν + 2 + l ≤ |z.2| := by
    have hle : C'₃ ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
    have : C'₃ / ν ≤ C' / ν := div_le_div_of_nonneg_right hle hν.le
    linarith
  obtain ⟨hψ_f, hv_f⟩ := hF S_ hS_ ν hν hν₁_le tr htr l hl s hs hsS z hz₁
  obtain ⟨hψ_z, hv_z⟩ := hZ S_ hS_ ν hν hν₂_le tr htr l hl s hs hsS z hz₂
  have hp := hP S_ hS_ ν hν hν₃_le tr htr l hl s hs hsS z hz₃
  let c := trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  set E_out : ℝ := Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))
  have hE_nn : 0 ≤ E_out := by dsimp [E_out]; positivity
  have hE₁ : Real.exp (-(b₁ * l / c)) + Real.exp (-(b₁ * l ^ 2 / (C₀₁ + ν * S_))) ≤ E_out :=
    PartI_T21.tail_kernel_mono hb (min_le_left _ _) hC₀₁ (le_max_left _ _) hc hν hS_ hl
  have hE₂ : Real.exp (-(b₂ * l ^ 2 / (C₀₂ + ν * S_))) ≤ E_out := by
    have h := PartI_T21.tail_kernel_mono (b₁ := b) (b₂ := b₂) (C₀₁ := C₀₂) (C₀₂ := C₀)
      hb ((min_le_right _ _).trans (min_le_left _ _)) hC₀₂
      ((le_max_left _ _).trans (le_max_right _ _)) hc hν hS_ hl
    exact (le_add_of_nonneg_left (Real.exp_nonneg _)).trans h
  have hE₃ : Real.exp (-(b₃ * l / c)) + Real.exp (-(b₃ * l ^ 2 / (C₀₃ + ν * S_))) ≤ E_out :=
    PartI_T21.tail_kernel_mono hb ((min_le_right _ _).trans (min_le_right _ _)) hC₀₃
      ((le_max_right _ _).trans (le_max_right _ _)) hc hν hS_ hl
  have hP₁ : polyPS C₁ N₁ ν c S_ ≤ polyPS C₁ N ν c S_ :=
    PartI_T21.polyPS_mono hC₁.le le_rfl (le_max_left _ _) hν hc.le hS_
  have hP₂ : polyPS C₂ N₂ ν c S_ ≤ polyPS C₂ N ν c S_ :=
    PartI_T21.polyPS_mono hC₂.le le_rfl ((le_max_left _ _).trans (le_max_right _ _)) hν hc.le hS_
  have hP₃ : polyPS C₃ N₃ ν c S_ ≤ polyPS C N ν c S_ :=
    PartI_T21.polyPS_mono hC₃.le (by dsimp [C]; linarith)
      ((le_max_right _ _).trans (le_max_right _ _)) hν hc.le hS_
  have hsum_poly : polyPS C₁ N ν c S_ * E_out + polyPS C₂ N ν c S_ * E_out ≤
      polyPS C N ν c S_ * E_out := by
    unfold polyPS
    have hX_nn : 0 ≤ ((1 + c + ν⁻¹) * (1 + S_)) ^ N := by positivity
    calc C₁ * ((1 + c + ν⁻¹) * (1 + S_)) ^ N * E_out +
          C₂ * ((1 + c + ν⁻¹) * (1 + S_)) ^ N * E_out
        = (C₁ + C₂) * ((1 + c + ν⁻¹) * (1 + S_)) ^ N * E_out := by ring
      _ ≤ C * ((1 + c + ν⁻¹) * (1 + S_)) ^ N * E_out := by
          apply mul_le_mul_of_nonneg_right _ hE_nn
          apply mul_le_mul_of_nonneg_right _ hX_nn
          dsimp [C]
          linarith
  have hK₁ : polyPS C₁ N₁ ν c S_ *
      (Real.exp (-(b₁ * l / c)) + Real.exp (-(b₁ * l ^ 2 / (C₀₁ + ν * S_)))) ≤
      polyPS C₁ N ν c S_ * E_out :=
    mul_le_mul hP₁ hE₁ (by positivity) (by unfold polyPS; positivity)
  have hK₂ : polyPS C₂ N₂ ν c S_ * Real.exp (-(b₂ * l ^ 2 / (C₀₂ + ν * S_))) ≤
      polyPS C₂ N ν c S_ * E_out :=
    mul_le_mul hP₂ hE₂ (by positivity) (by unfold polyPS; positivity)
  refine ⟨?_, ?_, ?_⟩
  · have htri : ‖ageJet ℓ j tr.ψ s z‖ ≤
        ‖ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ +
        ‖ageJet ℓ j tr.ψ s z -
          ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ := by
      simpa [add_sub_cancel] using
        norm_add_le (ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z)
          (ageJet ℓ j tr.ψ s z -
            ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z)
    exact htri.trans ((add_le_add (hψ_f.trans hK₁) (hψ_z.trans hK₂)).trans hsum_poly)
  · have htri : ‖ageJet ℓ j tr.v s z‖ ≤
        ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ +
        ‖ageJet ℓ j tr.v s z - ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ := by
      simpa [add_sub_cancel] using
        norm_add_le (ageJet ℓ j (fun r => hfluct c (tr.v r)) s z)
          (ageJet ℓ j tr.v s z - ageJet ℓ j (fun r => hfluct c (tr.v r)) s z)
    exact htri.trans ((add_le_add (hv_f.trans hK₁) (hv_z.trans hK₂)).trans hsum_poly)
  · exact hp.trans (mul_le_mul hP₃ hE₃ (by positivity) (by unfold polyPS; positivity))

namespace PartI_T21

theorem trainStreamVelocityPressureTransverseTail_of
    (hFluct : TrainNonzeroModeStreamVelTail)
    (hZero : TrainZeroModeStreamVelTail)
    (hPress : TrainPressureTransverseTail)
    (hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail) :
    TrainStreamVelocityPressureTransverseTail :=
  UnforcedLeray.Short.PartI.trainStreamVelocityPressureTransverseTail_of hFluct hZero hPress hOv hVort

end PartI_T21

end UnforcedLeray.Short.PartI
