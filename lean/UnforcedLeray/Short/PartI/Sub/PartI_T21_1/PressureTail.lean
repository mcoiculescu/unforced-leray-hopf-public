import UnforcedLeray.Short.PartI.Sub.PartI_T21_1
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.NonzeroModeTail.LocalMP
import UnforcedLeray.Short.PartI.Sub.PartI_T20_1.PressureStep
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations

/-!
# `PartI:T21/1/3` (`Sub/PartI_T21_1/PressureTail.lean`): Cylinder Poisson transverse tail for pressure

Source of record: `the November 2 reference manuscript`, lines 517-525
(old 506-515), in the proof of Lemma `sct:heat`.

Proves `trainPressureTransverseTail_proof`:
```lean
theorem trainPressureTransverseTail_proof
    (hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail)
    (hFluct : TrainNonzeroModeStreamVelTail)
    (hZero : TrainZeroModeStreamVelTail) :
    TrainPressureTransverseTail
```
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet)

namespace PartI_T21

/-! ### 1. Combined velocity transverse tail uniformly over `r ≤ L` and `i ≤ K` -/

/-- Single-index `(r, i)` transverse tail for `tr.v` by combining `hFluct` and `hZero`. -/
theorem vel_tail_single
    (hFluct : TrainNonzeroModeStreamVelTail)
    (hZero : TrainZeroModeStreamVelTail)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (r i : ℕ) :
    ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
      ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
            let c := trainPeriod ρ ν
            ‖ageJet r i tr.v s z‖ ≤ polyPS C N ν c S_ *
              (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))) := by
  obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hF⟩ := hFluct ρ hρ r i
  obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂, N₂, ν₂, hC₂, hν₂, hZ⟩ := hZero ρ hρ r i
  let b := min b₁ b₂
  let C₀ := max C₀₁ C₀₂
  let C' := max C'₁ C'₂
  let C := C₁ + C₂
  let N := max N₁ N₂
  let ν₀ := min ν₁ ν₂
  have hb : 0 < b := lt_min hb₁ hb₂
  have hC₀ : 0 < C₀ := lt_max_of_lt_left hC₀₁
  have hC' : 0 < C' := lt_max_of_lt_left hC'₁
  have hC : 0 < C := add_pos hC₁ hC₂
  have hν₀ : 0 < ν₀ := lt_min hν₁ hν₂
  refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, ?_⟩
  intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  have hz₁ : C'₁ / ν + 2 + l ≤ |z.2| := by
    have : C'₁ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
    linarith
  have hz₂ : C'₂ / ν + 2 + l ≤ |z.2| := by
    have : C'₂ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_right _ _) hν.le
    linarith
  obtain ⟨_, hv_f⟩ := hF S_ hS_ ν hν hν₁_le tr htr l hl s hs hsS z hz₁
  obtain ⟨_, hv_z⟩ := hZ S_ hS_ ν hν hν₂_le tr htr l hl s hs hsS z hz₂
  let c := trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  set E_out : ℝ := Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))
  have hE₁ : Real.exp (-(b₁ * l / c)) + Real.exp (-(b₁ * l ^ 2 / (C₀₁ + ν * S_))) ≤ E_out :=
    tail_kernel_mono hb (min_le_left _ _) hC₀₁ (le_max_left _ _) hc hν hS_ hl
  have hE₂ : Real.exp (-(b₂ * l ^ 2 / (C₀₂ + ν * S_))) ≤ E_out := by
    have h := tail_kernel_mono (b₁ := b) (b₂ := b₂) (C₀₁ := C₀₂) (C₀₂ := C₀)
      hb (min_le_right _ _) hC₀₂ (le_max_right _ _) hc hν hS_ hl
    exact (le_add_of_nonneg_left (Real.exp_nonneg _)).trans h
  have hP₁ : polyPS C₁ N₁ ν c S_ ≤ polyPS C₁ N ν c S_ :=
    polyPS_mono hC₁.le le_rfl (le_max_left _ _) hν hc.le hS_
  have hP₂ : polyPS C₂ N₂ ν c S_ ≤ polyPS C₂ N ν c S_ :=
    polyPS_mono hC₂.le le_rfl (le_max_right _ _) hν hc.le hS_
  have hK₁ : polyPS C₁ N₁ ν c S_ *
      (Real.exp (-(b₁ * l / c)) + Real.exp (-(b₁ * l ^ 2 / (C₀₁ + ν * S_)))) ≤
      polyPS C₁ N ν c S_ * E_out :=
    mul_le_mul hP₁ hE₁ (by positivity) (by unfold polyPS; positivity)
  have hK₂ : polyPS C₂ N₂ ν c S_ * Real.exp (-(b₂ * l ^ 2 / (C₀₂ + ν * S_))) ≤
      polyPS C₂ N ν c S_ * E_out :=
    mul_le_mul hP₂ hE₂ (by positivity) (by unfold polyPS; positivity)
  have hsum : polyPS C₁ N ν c S_ * E_out + polyPS C₂ N ν c S_ * E_out =
      polyPS C N ν c S_ * E_out := by
    unfold polyPS
    dsimp [C]
    ring
  have htri : ‖ageJet r i tr.v s z‖ ≤
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ +
      ‖ageJet r i tr.v s z - ageJet r i (fun t => hfluct c (tr.v t)) s z‖ := by
    simpa [add_sub_cancel] using
      norm_add_le (ageJet r i (fun t => hfluct c (tr.v t)) s z)
        (ageJet r i tr.v s z - ageJet r i (fun t => hfluct c (tr.v t)) s z)
  exact htri.trans ((add_le_add (hv_f.trans hK₁) (hv_z.trans hK₂)).trans (le_of_eq hsum))

/-- Uniform velocity transverse tail across `i ≤ K` at fixed age order `r`. -/
theorem uniform_vel_tail_row
    (hFluct : TrainNonzeroModeStreamVelTail)
    (hZero : TrainZeroModeStreamVelTail)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (r : ℕ) :
    ∀ K : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
      ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
            ∀ i ≤ K,
              let c := trainPeriod ρ ν
              ‖ageJet r i tr.v s z‖ ≤ polyPS C N ν c S_ *
                (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))
  | 0 => by
    obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, h0⟩ :=
      vel_tail_single hFluct hZero hρ r 0
    refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀,
      fun S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact h0 S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz
  | K + 1 => by
    obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ :=
      uniform_vel_tail_row hFluct hZero hρ r K
    obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂, N₂, ν₂, hC₂, hν₂, hK1⟩ :=
      vel_tail_single hFluct hZero hρ r (K + 1)
    let b := min b₁ b₂
    let C₀ := max C₀₁ C₀₂
    let C' := max C'₁ C'₂
    let C := max C₁ C₂
    let N := max N₁ N₂
    let ν₀ := min ν₁ ν₂
    have hb : 0 < b := lt_min hb₁ hb₂
    have hC₀ : 0 < C₀ := lt_max_of_lt_left hC₀₁
    have hC' : 0 < C' := lt_max_of_lt_left hC'₁
    have hC : 0 < C := lt_max_of_lt_left hC₁
    have hν₀ : 0 < ν₀ := lt_min hν₁ hν₂
    refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, ?_⟩
    intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz i hi
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hi with hiK | rfl
    · have hz₁ : C'₁ / ν + 2 + l ≤ |z.2| := by
        have : C'₁ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
        linarith
      have h1 := hIH S_ hS_ ν hν (hν_le.trans (min_le_left _ _)) tr htr l hl s hs hsS z hz₁ i hiK
      refine h1.trans (mul_le_mul
        (polyPS_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc.le hS_)
        (tail_kernel_mono hb (min_le_left _ _) hC₀₁ (le_max_left _ _) hc hν hS_ hl)
        (by positivity) (by unfold polyPS; positivity))
    · have hz₂ : C'₂ / ν + 2 + l ≤ |z.2| := by
        have : C'₂ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_right _ _) hν.le
        linarith
      have h2 := hK1 S_ hS_ ν hν (hν_le.trans (min_le_right _ _)) tr htr l hl s hs hsS z hz₂
      refine h2.trans (mul_le_mul
        (polyPS_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc.le hS_)
        (tail_kernel_mono hb (min_le_right _ _) hC₀₂ (le_max_right _ _) hc hν hS_ hl)
        (by positivity) (by unfold polyPS; positivity))

/-- Uniform velocity transverse tail across `r ≤ L` and `i ≤ K`. -/
theorem uniform_vel_tail_rect
    (hFluct : TrainNonzeroModeStreamVelTail)
    (hZero : TrainZeroModeStreamVelTail)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (K : ℕ) :
    ∀ L : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
      ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
            ∀ r ≤ L, ∀ i ≤ K,
              let c := trainPeriod ρ ν
              ‖ageJet r i tr.v s z‖ ≤ polyPS C N ν c S_ *
                (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))
  | 0 => by
    obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, h0⟩ :=
      uniform_vel_tail_row hFluct hZero hρ 0 K
    refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀,
      fun S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz i hi
  | L + 1 => by
    obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ :=
      uniform_vel_tail_rect hFluct hZero hρ K L
    obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂, N₂, ν₂, hC₂, hν₂, hL1⟩ :=
      uniform_vel_tail_row hFluct hZero hρ (L + 1) K
    let b := min b₁ b₂
    let C₀ := max C₀₁ C₀₂
    let C' := max C'₁ C'₂
    let C := max C₁ C₂
    let N := max N₁ N₂
    let ν₀ := min ν₁ ν₂
    have hb : 0 < b := lt_min hb₁ hb₂
    have hC₀ : 0 < C₀ := lt_max_of_lt_left hC₀₁
    have hC' : 0 < C' := lt_max_of_lt_left hC'₁
    have hC : 0 < C := lt_max_of_lt_left hC₁
    have hν₀ : 0 < ν₀ := lt_min hν₁ hν₂
    refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, ?_⟩
    intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz r hr i hi
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hr with hrL | rfl
    · have hz₁ : C'₁ / ν + 2 + l ≤ |z.2| := by
        have : C'₁ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
        linarith
      have h1 := hIH S_ hS_ ν hν (hν_le.trans (min_le_left _ _)) tr htr l hl s hs hsS z hz₁ r hrL i hi
      refine h1.trans (mul_le_mul
        (polyPS_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc.le hS_)
        (tail_kernel_mono hb (min_le_left _ _) hC₀₁ (le_max_left _ _) hc hν hS_ hl)
        (by positivity) (by unfold polyPS; positivity))
    · have hz₂ : C'₂ / ν + 2 + l ≤ |z.2| := by
        have : C'₂ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_right _ _) hν.le
        linarith
      have h2 := hL1 S_ hS_ ν hν (hν_le.trans (min_le_right _ _)) tr htr l hl s hs hsS z hz₂ i hi
      refine h2.trans (mul_le_mul
        (polyPS_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc.le hS_)
        (tail_kernel_mono hb (min_le_right _ _) hC₀₂ (le_max_right _ _) hc hν hS_ hl)
        (by positivity) (by unfold polyPS; positivity))

/-! ### 2. Slice-localized horizontal mean bound for pressure word derivatives -/

/-- Horizontal average bound on `B0151.derivWord w (iteratedDeriv ℓ tr.p s)` at height `z.2`
using only velocity bounds along the horizontal line `(q, z.2)`. -/
theorem abs_hmean_derivWord_p_slice_le {ν c M_V : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ k : ℕ) {w : List Bool} (hw : w.length = k) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hV_slice : ∀ q : ℝ, ∀ r ≤ ℓ, ∀ i ≤ k, ‖ageJet r i tr.v s (q, z.2)‖ ≤ M_V) :
    |hmean c (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)) z.2| ≤
      (2 : ℝ) ^ (ℓ + k) * M_V * M_V := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_sq : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1 ^ 2) := by
    have : (fun x : ℝ × Plane => tr.v x.1 x.2 1 ^ 2) =
        fun x : ℝ × Plane => tr.v x.1 x.2 1 * tr.v x.1 x.2 1 :=
      funext fun _ => sq _
    rw [this]
    exact hsm_v1.mul hsm_v1
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  let G_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.v r z' 1 ^ 2) s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hG_sm : ContDiff ℝ ∞ G_ℓ :=
    PartI_T20_1.contDiff_iteratedDeriv_slice (F := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs
  have hP_per : Cyl.IsPeriodic c P_ℓ :=
    PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ hs
  have hG_per : Cyl.IsPeriodic c G_ℓ := by
    refine PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr z' => ?_) ℓ hs
    exact congrArg (fun v : Vec => v 1 ^ 2) (tr.isTrain.periodic_v r hr.le z')
  have hmean_eq : ∀ η : ℝ, hmean c P_ℓ η = -hmean c G_ℓ η := by
    intro η
    rw [← PartI_T20_1.iteratedDeriv_hmean_eq hc hsm_p ℓ hs η,
      ← PartI_T20_1.iteratedDeriv_hmean_eq hc (F := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs η,
      ← iteratedDeriv_neg]
    have hev : (fun r => hmean c (tr.p r) η) =ᶠ[𝓝 s]
        fun r => -hmean c (fun z' : Plane => tr.v r z' 1 ^ 2) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using
        PartI_T20_1.train_hmean_p_eq_neg_v1_sq hν hc1 tr htr hr η
    exact hev.iteratedDeriv_eq ℓ
  have hword_eq := PartI_T20_1.hmean_derivWord_neg_eq hc hP_sm hG_sm hP_per hG_per hmean_eq w z.2
  rw [hword_eq, abs_neg]
  have hslice_eq : hmean c (B0151.derivWord w G_ℓ) z.2 =
      hmean c (fun w' : Plane => B0151.derivWord w G_ℓ (w'.1, z.2)) z.2 := rfl
  rw [hslice_eq]
  refine cylpHmeanAbsLe hc (fun w' => ?_) z.2
  have hsq_fn : (fun r (z' : Plane) => tr.v r z' 1 ^ 2) =
      fun r z' => tr.v r z' 1 * tr.v r z' 1 := by
    funext r z'; exact sq _
  calc |B0151.derivWord w G_ℓ (w'.1, z.2)|
      ≤ ‖ageJet ℓ k (fun r z' => tr.v r z' 1 ^ 2) s (w'.1, z.2)‖ :=
        PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => tr.v r z' 1 ^ 2)
          hsm_sq ℓ k hw hs (w'.1, z.2)
    _ = ‖ageJet ℓ k (fun r z' => tr.v r z' 1 * tr.v r z' 1) s (w'.1, z.2)‖ := by rw [hsq_fn]
    _ ≤ (2 : ℝ) ^ (ℓ + k) * M_V * M_V := by
        refine PartI_T20.norm_ageJet_mul_le
          (A := fun r z' => tr.v r z' 1) (B := fun r z' => tr.v r z' 1)
          hsm_v1 hsm_v1 ℓ k hs hMV hMV (w'.1, z.2) (fun r hr i hi => ?_) (fun r hr i hi => ?_)
        · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs (w'.1, z.2)).trans
            (hV_slice w'.1 r hr i hi)
        · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs (w'.1, z.2)).trans
            (hV_slice w'.1 r hr i hi)

/-- Comparison of the `l / 2` velocity tail factor with the `l` pressure tail factor when
`b ≤ b_t / 4`. -/
theorem half_tail_kernel_le {b b_t C₀ l c ν S_ : ℝ}
    (hb : 0 < b) (hb_4 : b ≤ b_t / 4) (hC₀ : 0 < C₀) (hl : 0 ≤ l)
    (hc : 0 < c) (hν : 0 < ν) (hS_ : 0 ≤ S_) :
    Real.exp (-(b_t * (l / 2) / c)) + Real.exp (-(b_t * (l / 2) ^ 2 / (C₀ + ν * S_))) ≤
      Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))) := by
  have hexp1 : Real.exp (-(b_t * (l / 2) / c)) ≤ Real.exp (-(b * l / c)) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply div_le_div_of_nonneg_right _ hc.le
    nlinarith
  have hexp2 : Real.exp (-(b_t * (l / 2) ^ 2 / (C₀ + ν * S_))) ≤
      Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hsq : b_t * (l / 2) ^ 2 = (b_t / 4) * l ^ 2 := by ring
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hb_4 (sq_nonneg l)
  exact add_le_add hexp1 hexp2

/-- Algebraic envelope bound assembling the oscillating and mean pressure pieces into
`polyPS C_out N_out ν c S_ * E_out`. -/
theorem pressure_tail_envelope_le
    {C_V C_t S_zeta b l c ν S_ E_out : ℝ} {N_V N_t ℓ j : ℕ}
    (hC_V : 0 < C_V) (_hC_t : 0 < C_t) (hS_nn : 0 ≤ S_zeta)
    (_hb : 0 < b) (hb_pi : b ≤ Real.pi) (hl : 0 ≤ l) (hc : 0 < c) (hν : 0 < ν) (hS_ : 0 ≤ S_)
    (hE_nn : 0 ≤ E_out) (hE_le_two : E_out ≤ 2)
    (hE_exp1 : Real.exp (-(b * l / c)) ≤ E_out) :
    let P_V : ℝ := polyP C_V N_V ν c
    let P_t : ℝ := polyPS C_t N_t ν c S_
    let M_far : ℝ := P_t * E_out
    let G_all : ℝ := 4 * (2 : ℝ) ^ (ℓ + j) * P_V * P_V
    let G_far : ℝ := 4 * (2 : ℝ) ^ (ℓ + j) * M_far * M_far
    let B_word : ℝ :=
      ((G_far + 2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c))) * c ^ 2 /
        (2 * Real.pi ^ 2)) * S_zeta +
        (2 : ℝ) ^ (ℓ + j) * M_far * M_far
    let C_osc_const : ℝ := (4 / (2 * Real.pi ^ 2)) * S_zeta
    let C_out : ℝ :=
      (2 : ℝ) ^ (ℓ + 2 * j) *
        (2 * C_t ^ 2 + 2 * C_osc_const * (C_t ^ 2 + C_V ^ 2))
    let N_out : ℕ := max (2 * N_t + 2) (2 * N_V + 2)
    (2 : ℝ) ^ j * B_word ≤ polyPS C_out N_out ν c S_ * E_out := by
  intro P_V P_t M_far G_all G_far B_word C_osc_const C_out N_out
  have hPV_nn : 0 ≤ P_V := by dsimp [P_V]; unfold polyP; positivity
  have hC_osc_nn : 0 ≤ C_osc_const := by dsimp [C_osc_const]; positivity
  have hE_sq : E_out * E_out ≤ 2 * E_out :=
    mul_le_mul_of_nonneg_right hE_le_two hE_nn
  have hexp_pi : Real.exp (-(2 * Real.pi * (l / 2) / c)) ≤ E_out := by
    have h1 : Real.exp (-(2 * Real.pi * (l / 2) / c)) ≤ Real.exp (-(b * l / c)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      apply div_le_div_of_nonneg_right _ hc.le
      nlinarith
    exact h1.trans hE_exp1
  have hMfar_sq : M_far * M_far ≤ 2 * P_t ^ 2 * E_out := by
    calc M_far * M_far
        = P_t ^ 2 * (E_out * E_out) := by dsimp [M_far]; ring
      _ ≤ P_t ^ 2 * (2 * E_out) := mul_le_mul_of_nonneg_left hE_sq (sq_nonneg P_t)
      _ = 2 * P_t ^ 2 * E_out := by ring
  let Y : ℝ := (1 + c + ν⁻¹) * (1 + S_)
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  have h1S : 1 ≤ 1 + S_ := by linarith
  have h1Y : 1 ≤ Y := one_le_mul_of_one_le_of_one_le h1X h1S
  have hcY : c ≤ Y := by
    dsimp [Y]
    have hcX : c ≤ 1 + c + ν⁻¹ := by linarith
    calc c = c * 1 := (mul_one c).symm
      _ ≤ (1 + c + ν⁻¹) * (1 + S_) := mul_le_mul hcX h1S zero_le_one (by positivity)
  have hc2Y : c ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hc.le hcY 2
  have hPV_le_Y : P_V ≤ C_V * Y ^ N_V := by
    dsimp [P_V, Y]
    unfold polyP
    rw [mul_pow]
    have hpowS : (1 : ℝ) ≤ (1 + S_) ^ N_V := one_le_pow₀ h1S
    calc C_V * (1 + c + ν⁻¹) ^ N_V
        = C_V * ((1 + c + ν⁻¹) ^ N_V * 1) := by ring
      _ ≤ C_V * ((1 + c + ν⁻¹) ^ N_V * (1 + S_) ^ N_V) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpowS (by positivity)) hC_V.le
  have hPt_eq : P_t = C_t * Y ^ N_t := by dsimp [P_t, Y]; unfold polyPS; rfl
  have hpow_t0 : Y ^ (2 * N_t) ≤ Y ^ N_out :=
    pow_le_pow_right₀ h1Y ((Nat.le_add_right (2 * N_t) 2).trans (le_max_left _ _))
  have hpow_t2 : Y ^ (2 * N_t + 2) ≤ Y ^ N_out :=
    pow_le_pow_right₀ h1Y (le_max_left _ _)
  have hpow_V2 : Y ^ (2 * N_V + 2) ≤ Y ^ N_out :=
    pow_le_pow_right₀ h1Y (le_max_right _ _)
  have hPt2_c2 : P_t ^ 2 * c ^ 2 ≤ C_t ^ 2 * Y ^ N_out := by
    calc P_t ^ 2 * c ^ 2
        = C_t ^ 2 * (Y ^ N_t * Y ^ N_t * c ^ 2) := by rw [hPt_eq]; ring
      _ ≤ C_t ^ 2 * (Y ^ N_t * Y ^ N_t * Y ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hc2Y (by positivity)) (sq_nonneg C_t)
      _ = C_t ^ 2 * Y ^ (2 * N_t + 2) := by
          rw [show 2 * N_t + 2 = N_t + N_t + 2 by omega, pow_add, pow_add]
      _ ≤ C_t ^ 2 * Y ^ N_out := mul_le_mul_of_nonneg_left hpow_t2 (sq_nonneg C_t)
  have hPt2_1 : P_t ^ 2 ≤ C_t ^ 2 * Y ^ N_out := by
    calc P_t ^ 2
        = C_t ^ 2 * (Y ^ N_t * Y ^ N_t) := by rw [hPt_eq]; ring
      _ = C_t ^ 2 * Y ^ (2 * N_t) := by rw [two_mul, pow_add]
      _ ≤ C_t ^ 2 * Y ^ N_out := mul_le_mul_of_nonneg_left hpow_t0 (sq_nonneg C_t)
  have hPV2_c2 : P_V * P_V * c ^ 2 ≤ C_V ^ 2 * Y ^ N_out := by
    have hPV_sq : P_V * P_V ≤ (C_V * Y ^ N_V) * (C_V * Y ^ N_V) :=
      mul_le_mul hPV_le_Y hPV_le_Y hPV_nn (by positivity)
    calc P_V * P_V * c ^ 2
        ≤ (C_V * Y ^ N_V) * (C_V * Y ^ N_V) * Y ^ 2 :=
          mul_le_mul hPV_sq hc2Y (sq_nonneg c) (by positivity)
      _ = C_V ^ 2 * Y ^ (2 * N_V + 2) := by
          rw [show 2 * N_V + 2 = N_V + N_V + 2 by omega, pow_add, pow_add]
          ring
      _ ≤ C_V ^ 2 * Y ^ N_out := mul_le_mul_of_nonneg_left hpow_V2 (sq_nonneg C_V)
  have hGfar_c2 : (G_far * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta ≤
      (2 : ℝ) ^ (ℓ + j) * (2 * C_osc_const * C_t ^ 2) * Y ^ N_out * E_out := by
    calc (G_far * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta
        = (2 : ℝ) ^ (ℓ + j) * C_osc_const * ((M_far * M_far) * c ^ 2) := by
          dsimp [G_far, C_osc_const]
          ring
      _ ≤ (2 : ℝ) ^ (ℓ + j) * C_osc_const * ((2 * P_t ^ 2 * E_out) * c ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hMfar_sq (sq_nonneg c)) (by positivity)
      _ = (2 : ℝ) ^ (ℓ + j) * (2 * C_osc_const) * (P_t ^ 2 * c ^ 2) * E_out := by ring
      _ ≤ (2 : ℝ) ^ (ℓ + j) * (2 * C_osc_const) * (C_t ^ 2 * Y ^ N_out) * E_out := by
          apply mul_le_mul_of_nonneg_right _ hE_nn
          exact mul_le_mul_of_nonneg_left hPt2_c2 (by positivity)
      _ = (2 : ℝ) ^ (ℓ + j) * (2 * C_osc_const * C_t ^ 2) * Y ^ N_out * E_out := by ring
  have hGall_c2 :
      (2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c)) * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta ≤
        (2 : ℝ) ^ (ℓ + j) * (2 * C_osc_const * C_V ^ 2) * Y ^ N_out * E_out := by
    calc (2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c)) * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta
        = (2 : ℝ) ^ (ℓ + j) * (2 * C_osc_const) * (P_V * P_V * c ^ 2) *
            Real.exp (-(2 * Real.pi * (l / 2) / c)) := by
          dsimp [G_all, C_osc_const]
          ring
      _ ≤ (2 : ℝ) ^ (ℓ + j) * (2 * C_osc_const) * (C_V ^ 2 * Y ^ N_out) * E_out := by
          apply mul_le_mul _ hexp_pi (Real.exp_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hPV2_c2 (by positivity)
      _ = (2 : ℝ) ^ (ℓ + j) * (2 * C_osc_const * C_V ^ 2) * Y ^ N_out * E_out := by ring
  have hmean_term : (2 : ℝ) ^ (ℓ + j) * M_far * M_far ≤
      (2 : ℝ) ^ (ℓ + j) * (2 * C_t ^ 2) * Y ^ N_out * E_out := by
    calc (2 : ℝ) ^ (ℓ + j) * M_far * M_far
        = (2 : ℝ) ^ (ℓ + j) * (M_far * M_far) := by ring
      _ ≤ (2 : ℝ) ^ (ℓ + j) * (2 * P_t ^ 2 * E_out) :=
          mul_le_mul_of_nonneg_left hMfar_sq (by positivity)
      _ = (2 : ℝ) ^ (ℓ + j) * 2 * P_t ^ 2 * E_out := by ring
      _ ≤ (2 : ℝ) ^ (ℓ + j) * 2 * (C_t ^ 2 * Y ^ N_out) * E_out := by
          apply mul_le_mul_of_nonneg_right _ hE_nn
          exact mul_le_mul_of_nonneg_left hPt2_1 (by positivity)
      _ = (2 : ℝ) ^ (ℓ + j) * (2 * C_t ^ 2) * Y ^ N_out * E_out := by ring
  have hBword_le : B_word ≤
      (2 : ℝ) ^ (ℓ + j) * (2 * C_t ^ 2 + 2 * C_osc_const * (C_t ^ 2 + C_V ^ 2)) *
        Y ^ N_out * E_out := by
    have hsplit : B_word =
        (G_far * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta +
        (2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c)) * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta +
        (2 : ℝ) ^ (ℓ + j) * M_far * M_far := by
      dsimp [B_word]
      ring
    rw [hsplit]
    linarith
  calc (2 : ℝ) ^ j * B_word
      ≤ (2 : ℝ) ^ j *
          ((2 : ℝ) ^ (ℓ + j) * (2 * C_t ^ 2 + 2 * C_osc_const * (C_t ^ 2 + C_V ^ 2)) *
            Y ^ N_out * E_out) :=
        mul_le_mul_of_nonneg_left hBword_le (by positivity)
    _ = polyPS C_out N_out ν c S_ * E_out := by
        dsimp [C_out, Y]
        unfold polyPS
        rw [show ℓ + 2 * j = j + (ℓ + j) by omega, pow_add]
        ring

end PartI_T21

/-! ### 3. Main theorem: `trainPressureTransverseTail_proof` (`PartI:T21/1/3`) -/

/-- **Cylinder Poisson transverse tail for the train pressure (`PartI:T21/1/3`)**:
proves `TrainPressureTransverseTail` from `hOv`, `hVort`, `hFluct`, and `hZero`. -/
theorem trainPressureTransverseTail_proof
    (hOv : TrainOverlap)
    (_hVort : TrainVorticityGaussianTail)
    (hFluct : TrainNonzeroModeStreamVelTail)
    (hZero : TrainZeroModeStreamVelTail) :
    TrainPressureTransverseTail := by
  intro ρ hρ ℓ j
  -- Global all-age vorticity and velocity jet bounds from `PartI:T20/1`
  have hAll := PartI_T20_1.trainVorticityAndVelocityAgeJet_all
    trainPressureAgeJetSupStep_proof hOv (train_vorticity_spatial_jet_tail hOv)
  have hVortAt : ∀ r ≤ ℓ, TrainVorticityGaussianTailAt r := fun r _ => (hAll r).1
  have hVelAt : ∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r := fun r _ => (hAll r).2
  -- Global velocity bound across `r ≤ ℓ` and `i ≤ j + 1`
  obtain ⟨C_V, N_V, ν_V, hC_V, hν_V, hV_glob⟩ :=
    PartI_T20.uniform_velocity_sup_rect hρ (j + 1) ℓ hVelAt
  -- Global pressure bound at `(ℓ, j)` for `qMode` boundedness
  obtain ⟨C_P, N_P, ν_P, hC_P, hν_P, hP_glob⟩ :=
    trainPressureAgeJetSupStep_proof hOv ℓ hVortAt hVelAt ρ hρ j
  -- Transverse tail velocity bound across `r ≤ ℓ` and `i ≤ j + 1`
  obtain ⟨b_t, C₀_t, C'_t, hb_t, hC₀_t, hC'_t, C_t, N_t, ν_t, hC_t, hν_t, hV_tail⟩ :=
    PartI_T21.uniform_vel_tail_rect hFluct hZero hρ (j + 1) ℓ
  -- Output parameters
  let b : ℝ := min (b_t / 4) Real.pi
  let C₀ : ℝ := C₀_t
  let C' : ℝ := C'_t
  let S_zeta : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hS_nn : 0 ≤ S_zeta := tsum_nonneg fun _ => by positivity
  let C_osc_const : ℝ := (4 / (2 * Real.pi ^ 2)) * S_zeta
  have hC_osc_nn : 0 ≤ C_osc_const := by dsimp [C_osc_const]; positivity
  let C_out : ℝ :=
    (2 : ℝ) ^ (ℓ + 2 * j) *
      (2 * C_t ^ 2 + 2 * C_osc_const * (C_t ^ 2 + C_V ^ 2))
  let N_out : ℕ := max (2 * N_t + 2) (2 * N_V + 2)
  let ν₀ : ℝ := min (min ν_V ν_P) (min ν_t 1)
  have hb : 0 < b := lt_min (by positivity) Real.pi_pos
  have hC₀ : 0 < C₀ := hC₀_t
  have hC' : 0 < C' := hC'_t
  have hC_out : 0 < C_out := by dsimp [C_out]; positivity
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_V hν_P) (lt_min hν_t zero_lt_one)
  refine ⟨b, C₀, C', hb, hC₀, hC', C_out, N_out, ν₀, hC_out, hν₀, ?_⟩
  intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz
  have hν_V_le : ν ≤ ν_V := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_P_le : ν ≤ ν_P := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_t_le : ν ≤ ν_t := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : ν ≤ 1 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hc1 : 1 ≤ c := by
    unfold c trainPeriod
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  set E_out : ℝ := Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))
  have hE_nn : 0 ≤ E_out := by dsimp [E_out]; positivity
  have hE_le_two : E_out ≤ 2 := by
    have h1 : Real.exp (-(b * l / c)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (mul_nonneg hb.le hl) hc.le))
    have h2 : Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (mul_nonneg hb.le (sq_nonneg l)) (by positivity)))
    exact (add_le_add h1 h2).trans (by norm_num)
  -- Compare the `l / 2` velocity tail factor with `E_out`
  have hl_half : 0 ≤ l / 2 := by positivity
  have hE_half :
      Real.exp (-(b_t * (l / 2) / c)) + Real.exp (-(b_t * (l / 2) ^ 2 / (C₀_t + ν * S_))) ≤
        E_out :=
    PartI_T21.half_tail_kernel_le hb (min_le_left _ _) hC₀_t hl hc hν hS_
  -- Global and far velocity envelopes
  let P_V : ℝ := polyP C_V N_V ν c
  let P_t : ℝ := polyPS C_t N_t ν c S_
  let M_far : ℝ := P_t * E_out
  have hPV_nn : 0 ≤ P_V := by dsimp [P_V]; unfold polyP; positivity
  have hPt_nn : 0 ≤ P_t := by dsimp [P_t]; unfold polyPS; positivity
  have hMfar_nn : 0 ≤ M_far := mul_nonneg hPt_nn hE_nn
  have hV_all_bd : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i tr.v s w'‖ ≤ P_V :=
    fun w' r hr i hi => hV_glob ν hν hν_V_le tr htr s hs w' r hr i hi
  have hV_far_bd : ∀ w' : Plane, |w'.2 - z.2| ≤ l / 2 →
      ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i tr.v s w'‖ ≤ M_far := by
    intro w' hw' r hr i hi
    have hw'_z : C'_t / ν + 2 + l / 2 ≤ |w'.2| := by
      have htri : |z.2| - |w'.2 - z.2| ≤ |w'.2| := by
        have h := abs_sub_abs_le_abs_sub z.2 w'.2
        rw [abs_sub_comm] at h
        linarith [le_abs_self (|z.2| - |w'.2|)]
      linarith
    have hraw := hV_tail S_ hS_ ν hν hν_t_le tr htr (l / 2) hl_half s hs hsS w' hw'_z r hr i hi
    exact hraw.trans (mul_le_mul_of_nonneg_left hE_half hPt_nn)
  -- Set up the pressure slice `P_ℓ` and its word derivatives
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hP_per : Cyl.IsPeriodic c P_ℓ :=
    PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ hs
  let G_all : ℝ := 4 * (2 : ℝ) ^ (ℓ + j) * P_V * P_V
  let G_far : ℝ := 4 * (2 : ℝ) ^ (ℓ + j) * M_far * M_far
  have hGall_nn : 0 ≤ G_all := by dsimp [G_all]; positivity
  have hGfar_nn : 0 ≤ G_far := by dsimp [G_far]; positivity
  let B_word : ℝ :=
    ((G_far + 2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c))) * c ^ 2 /
      (2 * Real.pi ^ 2)) * S_zeta +
      (2 : ℝ) ^ (ℓ + j) * M_far * M_far
  have hBword_nn : 0 ≤ B_word := by dsimp [B_word]; positivity
  have hword_bd : ∀ w ∈ wordsOfLength j, |B0151.derivWord w P_ℓ z| ≤ B_word := by
    intro w hw
    have hlen : w.length = j := by
      unfold wordsOfLength at hw
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hw
      simp
    let q_w : Plane → ℝ := B0151.derivWord w P_ℓ
    have hqw_sm : ContDiff ℝ 2 q_w := (B0151.contDiff_derivWord hP_sm w).of_le (by simp)
    have hqw_per : Cyl.IsPeriodic c q_w := PartI_T20_1.isPeriodic_derivWord hP_per w
    have hAll_lap : ∀ w' : Plane, |Train.lapS q_w w'| ≤ G_all := fun w' =>
      PartI_T20_1.abs_lapS_derivWord_p_le hν hc1 hPV_nn tr ℓ j hlen hs w' (hV_all_bd w')
    have hFar_lap : ∀ w' : Plane, |w'.2 - z.2| ≤ l / 2 → |Train.lapS q_w w'| ≤ G_far :=
      fun w' hw' =>
        PartI_T20_1.abs_lapS_derivWord_p_le hν hc1 hMfar_nn tr ℓ j hlen hs w' (hV_far_bd w' hw')
    have hMode_bdd : ∀ (n : ℤ), n ≠ 0 →
        ∃ M : ℝ, ∀ η : ℝ, ‖Cyl.qMode c hc n (fun w' : Plane => ((q_w w' : ℝ) : ℂ)) η‖ ≤ M := by
      intro n _hn
      refine ⟨polyP C_P N_P ν c, fun η => ?_⟩
      refine (cylPoisQModeEstimates c hc n _).1 (polyP C_P N_P ν c) (fun w' => ?_) η
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |q_w w'|
          ≤ ‖ageJet ℓ j tr.p s w'‖ :=
            PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet hsm_p ℓ j hlen hs w'
        _ ≤ polyP C_P N_P ν c := hP_glob ν hν hν_P_le tr htr s hs w'
    have hosc := PartI_T21.cylPoisOscPartLocalBound_of_modeBdd hc hl_half hGall_nn hGfar_nn
      hqw_sm hqw_per z hAll_lap hFar_lap hMode_bdd
    have hmean_bd := PartI_T21.abs_hmean_derivWord_p_slice_le hν hc1 hMfar_nn tr htr ℓ j hlen hs z
      (fun q r hr i hi => hV_far_bd (q, z.2) (by simp [hl_half]) r hr i (by omega))
    have htri : |q_w z| ≤ |q_w z - hmean c q_w z.2| + |hmean c q_w z.2| := by
      simpa [sub_add_cancel] using abs_add_le (q_w z - hmean c q_w z.2) (hmean c q_w z.2)
    exact htri.trans (add_le_add hosc hmean_bd)
  -- Sum over all words of length `j`
  have hjet_word := (cylJetWord_proof P_ℓ hP_sm j z).2
  have hcard_nat : (wordsOfLength j).card ≤ 2 ^ j := by
    unfold wordsOfLength
    exact Finset.card_image_le.trans (by simp)
  have hcard : ((wordsOfLength j).card : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hcard_nat
  have hjet_le : ‖ageJet ℓ j tr.p s z‖ ≤ (2 : ℝ) ^ j * B_word := by
    change ‖iteratedFDeriv ℝ j P_ℓ z‖ ≤ _
    calc ‖iteratedFDeriv ℝ j P_ℓ z‖
        ≤ ∑ w ∈ wordsOfLength j, |B0151.derivWord w P_ℓ z| := hjet_word
      _ ≤ ∑ _w ∈ wordsOfLength j, B_word := Finset.sum_le_sum fun w hw => hword_bd w hw
      _ = ((wordsOfLength j).card : ℝ) * B_word := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ j * B_word := mul_le_mul_of_nonneg_right hcard hBword_nn
  exact hjet_le.trans (PartI_T21.pressure_tail_envelope_le
    hC_V hC_t hS_nn hb (min_le_right _ _) hl hc hν hS_ hE_nn hE_le_two
    (le_add_of_nonneg_right (Real.exp_nonneg _)))

end UnforcedLeray.Short.PartI

end
