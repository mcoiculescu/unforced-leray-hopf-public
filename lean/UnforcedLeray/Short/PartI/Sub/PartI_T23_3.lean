import UnforcedLeray.Short.PartI.Sub.PartI_T23_2
import UnforcedLeray.Short.PartI.Sub.PartI_T21_2.InteriorStripBounds
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1.MeanJetFormula

/-!
# `PartI:T23/3` (`Sub/PartI_T23_3.lean`): `TrainMeanStreamLpBound`

Source of record: `the November 2 reference manuscript`, lines 459-462 and
539-540, in the proof of Lemma `sct:expansion`:
"In particular, replacing the remainder power by `(m - b - 1)/2 - ℓ + 1/(2p)` bounds `S` itself
with `s` replaced by `1 + s`."

This module establishes:
1. **`PartI_T23.trainInteriorStripJetBounds_of_tails`**: derives `TrainInteriorStripJetBounds`
   directly from `hTails : TrainStreamVelocityPressureTails` (using `hTails.2.2` at weight `m = 0`
   for `tr.v` and `tr.p`, together with `PartI_T21_2.trainInteriorStripStreamJetBounds_of_vel_at`
   and `hTails.2.1` for `tr.ψ`).
2. **`PartI_T23.iteratedDeriv_slice_add`**: additivity of nested slice derivatives
   `∂_η^b ∂_s^ℓ (A + B)` at `s > 0` for jointly `C^∞` functions `A, B` on `(0, ∞) × ℝ`.
3. **`PartI_T23.meanStream_pointwise_bound_pos_le_one`**: weighted pointwise mixed-derivative
   bound for `meanStream` on `0 < s ≤ 1` from `hTails : TrainStreamVelocityPressureTails` and
   `PartIIIb.Concrete.meanJetFormula`.
4. **`PartI_T23.meanStream_pointwise_bound_ge_one_of_remainder`**: weighted pointwise
   mixed-derivative bound for `meanStream` on `s ≥ 1` from `TrainMeanRemainderPointwiseBound`
   (at `N = 0`) and `hFD : TrainFluctuationDecay`.
5. **`PartI_T23.meanStream_pointwise_bound_zero_age_zero_deriv`** and
   **`PartI_T23.trainMeanStreamZeroAgeDerivBound_of_tails`**: weighted pointwise bounds at `s = 0`
   for `ℓ = 0` (via `meanStream_zero_eq_vortexMeanStream`) and for `ℓ ≥ 1` (by transferring the
   uniform `0 < s ≤ 1` bounds to two-sided derivatives at `s = 0` via `ZeroOrRightTendsto`).
6. **`trainMeanStreamLpBound_of`**: derives `TrainMeanStreamLpBound` for all `s ≥ 0` and
   `1 ≤ p ≤ ∞` from `hTails`, `hFD`, and `TrainMeanRemainderLpBound` (`PartI:T23/2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ContDiff
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (jap)

namespace PartI_T23

/-! ### 1. Interior-strip jet bounds from `TrainStreamVelocityPressureTails` -/

/-- Unconditional derivation of `TrainInteriorStripJetBounds` from
`hTails : TrainStreamVelocityPressureTails`: `hTails.2.2` (`TrainWeightedJetBounds`) at weight
`m = 0` bounds `ageJet ℓ j tr.v` and `ageJet ℓ j tr.p` globally on `Plane`, and combining this with
`hTails.2.1` (`TrainStreamVelocityPressureTransverseTail`) via
`PartI_T21_2.trainInteriorStripStreamJetBounds_of_vel_at` bounds `ageJet ℓ j tr.ψ` on every
interior strip `|z.2| ≤ C' / ν + 2`. -/
theorem trainInteriorStripJetBounds_of_tails
    (hTails : TrainStreamVelocityPressureTails) : TrainInteriorStripJetBounds := by
  have hVel : PartI_T21_2.TrainInteriorStripVelJetBounds := by
    intro ρ hρ ℓ j _C' _hC'
    obtain ⟨C, N, ν₀, hC, hν₀, hW⟩ := hTails.2.2 ρ hρ 0 ℓ j
    refine ⟨C, N, ν₀, hC, hν₀, ?_⟩
    intro ν hν hν_le tr htr s hs z _hz
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    have hB_nn : 0 ≤ polyPS C N ν (trainPeriod ρ ν) s := by
      unfold polyPS
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      positivity
    have hsup := (hW ν hν hν_le tr htr s hs).2.2.1.2
    have hpt := UnforcedLeray.Short.PartIIa.pointwise_of_wSupNorm (m := 2 * 0) hB_nn hsup z
    rw [UnforcedLeray.Short.PartIIa.sqrt_jap_even, pow_zero, one_mul] at hpt
    exact hpt
  have hPress : PartI_T21_2.TrainInteriorStripPressJetBounds := by
    intro ρ hρ ℓ j _C' _hC'
    obtain ⟨C, N, ν₀, hC, hν₀, hW⟩ := hTails.2.2 ρ hρ 0 ℓ j
    refine ⟨C, N, ν₀, hC, hν₀, ?_⟩
    intro ν hν hν_le tr htr s hs z _hz
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    have hB_nn : 0 ≤ polyPS C N ν (trainPeriod ρ ν) s := by
      unfold polyPS
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      positivity
    have hsup := (hW ν hν hν_le tr htr s hs).2.2.2.2.2
    have hpt := UnforcedLeray.Short.PartIIa.pointwise_of_wSupNorm (m := 2 * 0) hB_nn hsup z
    rw [UnforcedLeray.Short.PartIIa.sqrt_jap_even, pow_zero, one_mul] at hpt
    exact hpt
  intro ρ hρ ℓ j C' hC'
  obtain ⟨C_ψ, N_ψ, ν_ψ, hC_ψ, hν_ψ, hΨ⟩ :=
    PartI_T21_2.trainInteriorStripStreamJetBounds_of_vel_at hTails.2.1 ρ hρ ℓ j C' hC'
      (fun C'' hC'' => hVel ρ hρ ℓ (j - 1) C'' hC'')
  obtain ⟨C_v, N_v, ν_v, hC_v, hν_v, hV⟩ := hVel ρ hρ ℓ j C' hC'
  obtain ⟨C_p, N_p, ν_p, hC_p, hν_p, hP⟩ := hPress ρ hρ ℓ j C' hC'
  let C_int : ℝ := max C_ψ (max C_v C_p)
  let N_int : ℕ := max N_ψ (max N_v N_p)
  let ν₀ : ℝ := min ν_ψ (min ν_v ν_p)
  refine ⟨C_int, N_int, ν₀, lt_max_of_lt_left hC_ψ, lt_min hν_ψ (lt_min hν_v hν_p), ?_⟩
  intro ν hν hν_le tr htr s hs z hz
  have hν_ψ_le : ν ≤ ν_ψ := hν_le.trans (min_le_left _ _)
  have hν_v_le : ν ≤ ν_v := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_p_le : ν ≤ ν_p := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := (Real.rpow_pos_of_pos hν _).le
  refine ⟨(hΨ ν hν hν_ψ_le tr htr s hs z hz).trans
      (PartI_T21.polyPS_mono hC_ψ.le (le_max_left _ _) (le_max_left _ _) hν hc0 hs.le),
    (hV ν hν hν_v_le tr htr s hs z hz).trans
      (PartI_T21.polyPS_mono hC_v.le
        ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _)) hν hc0 hs.le),
    (hP ν hν hν_p_le tr htr s hs z hz).trans
      (PartI_T21.polyPS_mono hC_p.le
        ((le_max_right _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _)) hν hc0 hs.le)⟩

/-! ### 2. Additivity of nested slice derivatives and `rpow` comparison helpers -/

/-- Additivity of nested slice derivatives `∂_η^b ∂_s^ℓ (A + B)` at `s > 0` for jointly `C^∞`
functions `A, B` on `(0, ∞) × ℝ`. -/
theorem iteratedDeriv_slice_add {A B : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => A x.1 x.2) (Ioi 0 ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => B x.1 x.2) (Ioi 0 ×ˢ univ))
    (b ℓ : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => A r e + B r e) s) η =
      iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => A r e) s) η +
        iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => B r e) s) η := by
  have hr_eq : ∀ e : ℝ, iteratedDeriv ℓ (fun r => A r e + B r e) s =
      iteratedDeriv ℓ (fun r => A r e) s + iteratedDeriv ℓ (fun r => B r e) s := by
    intro e
    have hφ : ContDiff ℝ ∞ (fun r : ℝ => ((r, e) : ℝ × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    have hA_r : ContDiffOn ℝ ∞ (fun r : ℝ => A r e) (Ioi 0) :=
      hA.comp hφ.contDiffOn (fun r hr => ⟨hr, trivial⟩)
    have hB_r : ContDiffOn ℝ ∞ (fun r : ℝ => B r e) (Ioi 0) :=
      hB.comp hφ.contDiffOn (fun r hr => ⟨hr, trivial⟩)
    have hA_at : ContDiffAt ℝ ℓ (fun r : ℝ => A r e) s :=
      (hA_r.contDiffAt (isOpen_Ioi.mem_nhds hs)).of_le (by exact_mod_cast le_top)
    have hB_at : ContDiffAt ℝ ℓ (fun r : ℝ => B r e) s :=
      (hB_r.contDiffAt (isOpen_Ioi.mem_nhds hs)).of_le (by exact_mod_cast le_top)
    exact iteratedDeriv_add hA_at hB_at
  have hHA := UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 A hA ℓ
  have hHB := UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 B hB ℓ
  have hψ : ContDiff ℝ ∞ (fun e : ℝ => ((s, e) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  have hA_e : ContDiff ℝ ∞ (fun e : ℝ => iteratedDeriv ℓ (fun r => A r e) s) := by
    have hcomp : ContDiffOn ℝ ∞
        ((fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => A r x.2) x.1) ∘
          (fun e : ℝ => ((s, e) : ℝ × ℝ))) univ :=
      hHA.comp (contDiffOn_univ.mpr hψ) (fun _ _ => ⟨hs, trivial⟩)
    exact contDiffOn_univ.mp hcomp
  have hB_e : ContDiff ℝ ∞ (fun e : ℝ => iteratedDeriv ℓ (fun r => B r e) s) := by
    have hcomp : ContDiffOn ℝ ∞
        ((fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => B r x.2) x.1) ∘
          (fun e : ℝ => ((s, e) : ℝ × ℝ))) univ :=
      hHB.comp (contDiffOn_univ.mpr hψ) (fun _ _ => ⟨hs, trivial⟩)
    exact contDiffOn_univ.mp hcomp
  have hfun : (fun e => iteratedDeriv ℓ (fun r => A r e + B r e) s) =
      fun e => iteratedDeriv ℓ (fun r => A r e) s + iteratedDeriv ℓ (fun r => B r e) s :=
    funext hr_eq
  rw [hfun]
  exact iteratedDeriv_add
    (hA_e.contDiffAt.of_le (by exact_mod_cast le_top))
    (hB_e.contDiffAt.of_le (by exact_mod_cast le_top))

/-- For `0 ≤ s ≤ 1` and any `α : ℝ`, `1 ≤ (2 : ℝ) ^ |α| * (1 + s) ^ α`. -/
theorem one_le_two_rpow_abs_mul_one_add_rpow (α : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 ≤ (2 : ℝ) ^ |α| * (1 + s) ^ α := by
  have h1s : 0 < 1 + s := by linarith
  have hle : (1 + s) ^ (-α) ≤ (2 : ℝ) ^ |α| := by
    rcases le_total 0 (-α) with hα | hα
    · calc (1 + s) ^ (-α) ≤ (2 : ℝ) ^ (-α) := Real.rpow_le_rpow h1s.le (by linarith) hα
        _ ≤ (2 : ℝ) ^ |α| := Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_abs α)
    · calc (1 + s) ^ (-α) ≤ (1 + s) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hα
        _ = 1 := Real.rpow_zero _
        _ ≤ (2 : ℝ) ^ |α| := Real.one_le_rpow (by norm_num) (abs_nonneg α)
  calc (1 : ℝ) = (1 + s) ^ (-α) * (1 + s) ^ α := by
        rw [← Real.rpow_add h1s, neg_add_cancel, Real.rpow_zero]
    _ ≤ (2 : ℝ) ^ |α| * (1 + s) ^ α :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg h1s.le _)

/-- For `1 ≤ s` and any `α : ℝ`, `s ^ α ≤ (2 : ℝ) ^ |α| * (1 + s) ^ α`. -/
theorem rpow_le_two_rpow_abs_mul_one_add_rpow (α : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    s ^ α ≤ (2 : ℝ) ^ |α| * (1 + s) ^ α := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have h1s : 0 < 1 + s := by linarith
  rcases le_total 0 α with hα | hα
  · have h1 : s ^ α ≤ (1 + s) ^ α := Real.rpow_le_rpow hs0.le (by linarith) hα
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ |α| :=
      Real.one_le_rpow (by norm_num) (abs_nonneg α)
    calc s ^ α ≤ 1 * (1 + s) ^ α := by linarith
      _ ≤ (2 : ℝ) ^ |α| * (1 + s) ^ α :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg h1s.le _)
  · have hα' : 0 ≤ -α := neg_nonneg.2 hα
    have h12 : 1 + s ≤ 2 * s := by linarith
    have h1 : (1 + s) ^ (-α) ≤ (2 : ℝ) ^ (-α) * s ^ (-α) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs0.le]
      exact Real.rpow_le_rpow h1s.le h12 hα'
    rw [abs_of_nonpos hα]
    have h2 : (1 + s) ^ (-α) * (1 + s) ^ α = 1 := by
      rw [← Real.rpow_add h1s, neg_add_cancel, Real.rpow_zero]
    have h3 : s ^ (-α) * s ^ α = 1 := by
      rw [← Real.rpow_add hs0, neg_add_cancel, Real.rpow_zero]
    have hmul := mul_le_mul_of_nonneg_right h1
      (mul_nonneg (Real.rpow_nonneg hs0.le α) (Real.rpow_nonneg h1s.le α))
    calc s ^ α = ((1 + s) ^ (-α) * (1 + s) ^ α) * s ^ α := by rw [h2, one_mul]
      _ = (1 + s) ^ (-α) * (s ^ α * (1 + s) ^ α) := by ring
      _ ≤ ((2 : ℝ) ^ (-α) * s ^ (-α)) * (s ^ α * (1 + s) ^ α) := hmul
      _ = (2 : ℝ) ^ (-α) * (s ^ (-α) * s ^ α) * (1 + s) ^ α := by ring
      _ = (2 : ℝ) ^ (-α) * (1 + s) ^ α := by rw [h3, mul_one]

/-! ### 3. Pointwise bound for `0 < s ≤ 1` from `TrainStreamVelocityPressureTails` -/

/-- **Weighted pointwise bound for `meanStream` on `0 < s ≤ 1`** from
`TrainStreamVelocityPressureTails`, `TrainInteriorStripJetBounds`, and
`PartIIIb.Concrete.meanJetFormula`. -/
theorem meanStream_pointwise_bound_pos_le_one
    (hTails : TrainStreamVelocityPressureTails)
    (hInt : TrainInteriorStripJetBounds)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (m b ℓ : ℕ) :
    ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ η : ℝ,
          |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| ≤
            polyP C M ν c * (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ) := by
  obtain ⟨C₀, N₀, ν₀, hC₀, hν₀, hJ⟩ :=
    PartI_T21.wSupNorm_stream_vel_pressure_of_interior_and_tail hTails.2.1 hInt ρ hρ (2 * m) ℓ b
  set α : ℝ := ((m : ℝ) - b - 1) / 2 - ℓ
  refine ⟨(2 : ℝ) ^ N₀ * (2 : ℝ) ^ |α| * C₀, N₀, ν₀, by positivity, hν₀, ?_⟩
  intro ν hν hν_le tr htr c s hs0 hs1 η
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  have hsup := (hJ ν hν hν_le tr htr s hs0).1
  have hB_nn : 0 ≤ polyPS C₀ N₀ ν c s := by
    unfold polyPS
    have : 0 ≤ c := hc0.le
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have : 0 ≤ 1 + s := by linarith
    positivity
  have hpt : ∀ q : ℝ, |η| ^ m *
      ‖(ageJet ℓ b tr.ψ s (q, η)) (fun _ => ((0 : ℝ), (1 : ℝ)))‖ ≤ polyPS C₀ N₀ ν c s := by
    intro q
    have hw := UnforcedLeray.Short.PartIIa.pointwise_of_wSupNorm hB_nn hsup (q, η)
    rw [UnforcedLeray.Short.PartIIa.sqrt_jap_even] at hw
    have hη : |η| ^ m ≤ (1 + ((q, η) : ℝ × ℝ).2 ^ 2) ^ m := by
      refine pow_le_pow_left₀ (abs_nonneg η) ?_ m
      dsimp only
      nlinarith [sq_abs η, sq_nonneg (|η| - 1 / 2), abs_nonneg η]
    have hop : ‖(ageJet ℓ b tr.ψ s (q, η)) (fun _ => ((0 : ℝ), (1 : ℝ)))‖ ≤
        ‖ageJet ℓ b tr.ψ s (q, η)‖ := by
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have : ∏ _i : Fin b, ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
      rw [this, mul_one]
    exact (mul_le_mul hη hop (norm_nonneg _) (by positivity)).trans hw
  have hjet := UnforcedLeray.Short.PartIIIb.Concrete.meanJetFormula ν c hν hc0 tr htr b ℓ s hs0 η
  have havg : |η| ^ m *
      |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| ≤
      polyPS C₀ N₀ ν c s := by
    have h := UnforcedLeray.Short.PartIIa.avg_bound (c := c) (η := η) hc0
      (pow_nonneg (abs_nonneg η) m)
      (fun q η' => (ageJet ℓ b tr.ψ s (q, η')) (fun _ => ((0 : ℝ), (1 : ℝ))))
      (fun q _ => by simpa [Real.norm_eq_abs] using hpt q)
    unfold hmean at h
    rw [smul_eq_mul] at h
    rwa [← hjet] at h
  have hpoly : polyPS C₀ N₀ ν c s ≤ polyP ((2 : ℝ) ^ N₀ * C₀) N₀ ν c := by
    unfold polyPS polyP
    rw [mul_pow]
    have h1s : (1 + s) ^ N₀ ≤ (2 : ℝ) ^ N₀ :=
      pow_le_pow_left₀ (by linarith) (by linarith) N₀
    have hX : 0 ≤ C₀ * (1 + c + ν⁻¹) ^ N₀ := by
      have : 0 ≤ c := hc0.le
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      positivity
    calc C₀ * ((1 + c + ν⁻¹) ^ N₀ * (1 + s) ^ N₀)
        = (C₀ * (1 + c + ν⁻¹) ^ N₀) * (1 + s) ^ N₀ := by ring
      _ ≤ (C₀ * (1 + c + ν⁻¹) ^ N₀) * (2 : ℝ) ^ N₀ := mul_le_mul_of_nonneg_left h1s hX
      _ = (2 : ℝ) ^ N₀ * C₀ * (1 + c + ν⁻¹) ^ N₀ := by ring
  have h1s_pow := one_le_two_rpow_abs_mul_one_add_rpow α hs0.le hs1
  calc |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η|
      ≤ polyP ((2 : ℝ) ^ N₀ * C₀) N₀ ν c * 1 := by
        rw [mul_one]
        exact havg.trans hpoly
    _ ≤ polyP ((2 : ℝ) ^ N₀ * C₀) N₀ ν c * ((2 : ℝ) ^ |α| * (1 + s) ^ α) :=
        mul_le_mul_of_nonneg_left h1s_pow (by
          unfold polyP
          have : 0 ≤ c := hc0.le
          have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
          positivity)
    _ = polyP ((2 : ℝ) ^ N₀ * (2 : ℝ) ^ |α| * C₀) N₀ ν c * (1 + s) ^ α := by
        unfold polyP
        ring

/-! ### 4. Unconditional pointwise bound for `s ≥ 1` from `TrainMeanRemainderPointwiseBound` -/

/-- **Unconditional weighted pointwise bound for `meanStream` on `s ≥ 1`** from
`TrainMeanRemainderPointwiseBound` (at `N = 0`) and `TrainFluctuationDecay`. -/
theorem meanStream_pointwise_bound_ge_one_of_remainder
    (hRem : TrainMeanRemainderPointwiseBound) (hFD : TrainFluctuationDecay)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (m b ℓ : ℕ) :
    ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
          |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| ≤
            polyP C M ν c * (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ) := by
  obtain ⟨C₁, M₁, ν₁, hC₁, hν₁, hR⟩ := hRem ρ hρ 0 m b ℓ
  obtain ⟨C₂, M₂, ν₂, hC₂, hν₂, hCoeff⟩ := meanCoeff_bound_of_fluctDecay hFD ρ hρ 0
  obtain ⟨D, hD, hG⟩ := heatKernel1_weighted_jet_bound m b ℓ
  set α : ℝ := ((m : ℝ) - b - 1) / 2 - ℓ
  let M : ℕ := max M₁ (M₂ + (b + 1))
  refine ⟨(2 : ℝ) ^ |α| * (C₁ + C₂ * D), M, min (min ν₁ ν₂) 1,
    mul_pos (by positivity) (add_pos hC₁ (mul_pos hC₂ hD)),
    lt_min (lt_min hν₁ hν₂) one_pos, ?_⟩
  intro ν hν hν_le tr htr c s hs η
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hSmR : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr 0 x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartIIa.meanRemainderSmooth_of trainMeanEquations_proof
      UnforcedLeray.Short.PartIIa.heatKernelIterSmooth ν c hν hc0 tr htr 0
  have hSmG : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => meanCoeff tr 0 * heatKernel1 (ν * x.1) x.2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.mul (UnforcedLeray.Short.PartIIa.heatKernel1_contDiffOn_scaled hν)
  have hdecomp : ∀ r e : ℝ,
      meanStream tr r e = meanRemainder tr 0 r e + meanCoeff tr 0 * heatKernel1 (ν * r) e := by
    intro r e
    unfold meanRemainder
    rw [Finset.sum_range_one, Nat.mul_zero, iteratedDeriv_zero, sub_add_cancel]
  have hslice_eq : iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η =
      iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr 0 r e) s) η +
        meanCoeff tr 0 *
          iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η := by
    have hadd := iteratedDeriv_slice_add
      (A := fun r e => meanRemainder tr 0 r e)
      (B := fun r e => meanCoeff tr 0 * heatKernel1 (ν * r) e)
      hSmR hSmG b ℓ hs0 η
    have hmul : iteratedDeriv b
        (fun e => iteratedDeriv ℓ (fun r => meanCoeff tr 0 * heatKernel1 (ν * r) e) s) η =
        meanCoeff tr 0 *
          iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η := by
      have hr : (fun e => iteratedDeriv ℓ (fun r => meanCoeff tr 0 * heatKernel1 (ν * r) e) s) =
          fun e => meanCoeff tr 0 * iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s :=
        funext fun e => iteratedDeriv_const_mul_field (meanCoeff tr 0)
          (fun r => heatKernel1 (ν * r) e)
      rw [hr, iteratedDeriv_const_mul_field]
    rw [← hmul, ← hadd]
    congr 2
    ext e
    congr 2
    ext r
    exact hdecomp r e
  have hR_pt := hR ν hν hν₁_le tr htr s hs η
  have hα_rem : ((m : ℝ) - b - 2 * (0 : ℕ) - 3) / 2 - ℓ ≤ α := by
    dsimp [α]; push_cast; linarith
  have hs_rem : s ^ (((m : ℝ) - b - 2 * (0 : ℕ) - 3) / 2 - ℓ) ≤ s ^ α :=
    Real.rpow_le_rpow_of_exponent_le hs hα_rem
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith [hc0.le]
  have hP₁ : polyP C₁ M₁ ν c ≤ polyP C₁ M ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₁.le
  have hterm1 : |η| ^ m *
      |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr 0 r e) s) η| ≤
      polyP C₁ M ν c * s ^ α :=
    hR_pt.trans (mul_le_mul hP₁ hs_rem (Real.rpow_nonneg hs0.le _) (by unfold polyP; positivity))
  have hC_bd := hCoeff ν hν hν₂_le tr htr
  have hG_bd := hG hν hν1 hc0.le hs η
  have hη_le : |η| ^ m ≤ (1 + |η|) ^ m :=
    pow_le_pow_left₀ (abs_nonneg η) (by linarith [abs_nonneg η]) m
  have hP₂D : polyP C₂ M₂ ν c * polyP D (b + 1) ν c ≤ polyP (C₂ * D) M ν c := by
    unfold polyP
    calc (C₂ * (1 + c + ν⁻¹) ^ M₂) * (D * (1 + c + ν⁻¹) ^ (b + 1))
        = (C₂ * D) * (1 + c + ν⁻¹) ^ (M₂ + (b + 1)) := by rw [pow_add]; ring
      _ ≤ (C₂ * D) * (1 + c + ν⁻¹) ^ M :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) (by positivity)
  have hterm2 : |η| ^ m * |meanCoeff tr 0 *
      iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η| ≤
      polyP (C₂ * D) M ν c * s ^ α := by
    rw [abs_mul]
    calc |η| ^ m * (|meanCoeff tr 0| *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η|)
        = |meanCoeff tr 0| * (|η| ^ m *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η|) := by
          ring
      _ ≤ |meanCoeff tr 0| * ((1 + |η|) ^ m *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hη_le (abs_nonneg _)) (abs_nonneg _)
      _ ≤ polyP C₂ M₂ ν c * (polyP D (b + 1) ν c * s ^ α) :=
          mul_le_mul hC_bd hG_bd (by positivity) (by unfold polyP; positivity)
      _ = (polyP C₂ M₂ ν c * polyP D (b + 1) ν c) * s ^ α := by ring
      _ ≤ polyP (C₂ * D) M ν c * s ^ α :=
          mul_le_mul_of_nonneg_right hP₂D (Real.rpow_nonneg hs0.le _)
  rw [hslice_eq]
  have htri : |η| ^ m *
      |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr 0 r e) s) η +
        meanCoeff tr 0 *
          iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η| ≤
      polyP (C₁ + C₂ * D) M ν c * s ^ α := by
    calc |η| ^ m *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr 0 r e) s) η +
            meanCoeff tr 0 *
              iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η|
        ≤ |η| ^ m *
            (|iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr 0 r e) s) η| +
              |meanCoeff tr 0 *
                iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ = |η| ^ m *
            |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr 0 r e) s) η| +
          |η| ^ m * |meanCoeff tr 0 *
            iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η| := by
          ring
      _ ≤ polyP C₁ M ν c * s ^ α + polyP (C₂ * D) M ν c * s ^ α := add_le_add hterm1 hterm2
      _ = polyP (C₁ + C₂ * D) M ν c * s ^ α := by unfold polyP; ring
  have hs1s := rpow_le_two_rpow_abs_mul_one_add_rpow α hs
  calc |η| ^ m *
        |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr 0 r e) s) η +
          meanCoeff tr 0 *
            iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η|
      ≤ polyP (C₁ + C₂ * D) M ν c * ((2 : ℝ) ^ |α| * (1 + s) ^ α) :=
        htri.trans (mul_le_mul_of_nonneg_left hs1s (by unfold polyP; positivity))
    _ = polyP ((2 : ℝ) ^ |α| * (C₁ + C₂ * D)) M ν c * (1 + s) ^ α := by
        unfold polyP; ring

/-! ### 5. Unconditional pointwise bounds at `s = 0` (`ℓ = 0` and `ℓ ≥ 1`) -/

/-- **Unconditional weighted pointwise bound for `meanStream` at `s = 0, ℓ = 0`** from
`PartI_T21.meanStream_zero_eq_vortexMeanStream` and `heatKernel1_weighted_jet_bound`. -/
theorem meanStream_pointwise_bound_zero_age_zero_deriv (ρ : ℝ) (hρ : 1 / 2 < ρ) (m b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ν ≤ 1 →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        ∀ η : ℝ,
          |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv 0 (fun r => meanStream tr r e) 0) η| ≤
            polyP C 0 ν c * (1 + (0 : ℝ)) ^ (((m : ℝ) - b - 1) / 2 - (0 : ℕ)) := by
  obtain ⟨D, hD, hG⟩ := heatKernel1_weighted_jet_bound m b 0
  refine ⟨8 * Real.pi * D * (2 : ℝ) ^ (b + 1), by positivity, ?_⟩
  intro ν hν hν1 tr _ c η
  have hc1 : 1 ≤ c :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hfun : (fun e => iteratedDeriv 0 (fun r => meanStream tr r e) 0) =
      fun e => -(8 * Real.pi * c⁻¹) *
        iteratedDeriv 0 (fun r => heatKernel1 (1 * r) e) 1 := by
    funext e
    rw [iteratedDeriv_zero, iteratedDeriv_zero,
      meanStream_zero_eq_vortexMeanStream hc1 tr e]
    unfold vortexMeanStream Train.width
    rw [mul_zero, add_zero, one_mul]
  rw [hfun, iteratedDeriv_const_mul_field, abs_mul, abs_neg,
    abs_of_pos (mul_pos (by positivity) (inv_pos.2 hc0))]
  have hc_inv : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  have hη_le : |η| ^ m ≤ (1 + |η|) ^ m :=
    pow_le_pow_left₀ (abs_nonneg η) (by linarith [abs_nonneg η]) m
  have hG1 := hG (ν := 1) (c := 0) one_pos le_rfl le_rfl (s := 1) le_rfl η
  simp only [Real.one_rpow, mul_one, polyP, add_zero, inv_one,
    show (1 : ℝ) + 1 = 2 by norm_num] at hG1
  simp only [add_zero, Real.one_rpow, mul_one, polyP, pow_zero]
  calc |η| ^ m * (8 * Real.pi * c⁻¹ *
        |iteratedDeriv b (fun e => iteratedDeriv 0 (fun r => heatKernel1 (1 * r) e) 1) η|)
      = 8 * Real.pi * c⁻¹ * (|η| ^ m *
        |iteratedDeriv b (fun e => iteratedDeriv 0 (fun r => heatKernel1 (1 * r) e) 1) η|) := by ring
    _ ≤ 8 * Real.pi * 1 * ((1 + |η|) ^ m *
        |iteratedDeriv b (fun e => iteratedDeriv 0 (fun r => heatKernel1 (1 * r) e) 1) η|) := by
        refine mul_le_mul
          (mul_le_mul_of_nonneg_left hc_inv (by positivity))
          (mul_le_mul_of_nonneg_right hη_le (abs_nonneg _))
          (by positivity) (by positivity)
    _ ≤ 8 * Real.pi * 1 * (D * (2 : ℝ) ^ (b + 1)) :=
        mul_le_mul_of_nonneg_left hG1 (by positivity)
    _ = 8 * Real.pi * D * (2 : ℝ) ^ (b + 1) := by ring

/-- Auxiliary relation for transferring uniform bounds on `(0, 1]` to two-sided derivatives at `s = 0`:
at every point `e : ℝ`, either `h e = 0` or `ψ s e → h e` as `s → 0⁺`. -/
def ZeroOrRightTendsto (h : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ e : ℝ, h e = 0 ∨ Tendsto (fun s => ψ s e) (𝓝[>] 0) (𝓝 (h e))

/-- Iterated derivatives of a smooth function `φ : ℝ → ℝ` are smooth. -/
theorem contDiff_iteratedDeriv (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∀ k : ℕ, ContDiff ℝ ∞ (iteratedDeriv k φ)
  | 0 => by
    rw [iteratedDeriv_zero]
    exact hφ
  | k + 1 => by
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp (contDiff_iteratedDeriv φ hφ k)).2

/-- If `f` tends to `a` along `l` and frequently equals `b`, then `a = b`. -/
theorem eq_of_tendsto_of_frequently_eq {α : Type*} {l : Filter α} {f : α → ℝ} {a b : ℝ}
    (ht : Tendsto f l (𝓝 a)) (hf : ∃ᶠ x in l, f x = b) : a = b := by
  by_contra hab
  have hopen : {b}ᶜ ∈ 𝓝 a := isClosed_singleton.isOpen_compl.mem_nhds hab
  exact hf (ht.eventually hopen)

/-- For a smooth function `φ : ℝ → ℝ` with `|deriv φ y| ≤ B₁` and `|deriv (deriv φ) y| ≤ B₂` on `ℝ`,
and any `e < x`, the secant slope `(φ x - φ e) / (x - e)` satisfies
`|φ x - φ e| ≤ B₁ * (x - e)` and `|deriv φ e - (φ x - φ e) / (x - e)| ≤ B₂ * (x - e)`. -/
theorem smooth_secant_bounds {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {B₁ B₂ : ℝ}
    (hB₁ : ∀ y : ℝ, |deriv φ y| ≤ B₁) (hB₂ : ∀ y : ℝ, |deriv (deriv φ) y| ≤ B₂)
    {e x : ℝ} (hex : e < x) :
    |φ x - φ e| ≤ B₁ * (x - e) ∧
      |deriv φ e - (φ x - φ e) / (x - e)| ≤ B₂ * (x - e) := by
  have hB₂_nn : 0 ≤ B₂ := (abs_nonneg _).trans (hB₂ e)
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdφ_cd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hdφ_diff : Differentiable ℝ (deriv φ) := hdφ_cd.differentiable (by simp)
  obtain ⟨c₁, ⟨hc₁_gt, hc₁_lt⟩, hc₁_eq⟩ := exists_deriv_eq_slope φ hex
    hφ_diff.continuous.continuousOn hφ_diff.differentiableOn
  obtain ⟨c₂, ⟨hc₂_gt, hc₂_lt⟩, hc₂_eq⟩ := exists_deriv_eq_slope (deriv φ) hc₁_gt
    hdφ_diff.continuous.continuousOn hdφ_diff.differentiableOn
  have hxe_pos : 0 < x - e := sub_pos.2 hex
  have hc₁e_pos : 0 < c₁ - e := sub_pos.2 hc₁_gt
  constructor
  · have hsub : φ x - φ e = deriv φ c₁ * (x - e) :=
      ((eq_div_iff hxe_pos.ne').mp hc₁_eq).symm
    rw [hsub, abs_mul, abs_of_pos hxe_pos]
    exact mul_le_mul_of_nonneg_right (hB₁ c₁) hxe_pos.le
  · have hsub : deriv φ c₁ - deriv φ e = deriv (deriv φ) c₂ * (c₁ - e) :=
      ((eq_div_iff hc₁e_pos.ne').mp hc₂_eq).symm
    have hdiff : deriv φ e - (φ x - φ e) / (x - e) = -(deriv (deriv φ) c₂ * (c₁ - e)) := by
      rw [← hc₁_eq]; linarith
    rw [hdiff, abs_neg, abs_mul, abs_of_pos hc₁e_pos]
    calc |deriv (deriv φ) c₂| * (c₁ - e)
        ≤ B₂ * (c₁ - e) := mul_le_mul_of_nonneg_right (hB₂ c₂) hc₁e_pos.le
      _ ≤ B₂ * (x - e) := mul_le_mul_of_nonneg_left (by linarith) hB₂_nn

/-- For `H : ℝ → ℝ` that is smooth on `(0, ∞)` with `|deriv (deriv H) r| ≤ M` on `(0, 1]`,
either `deriv H 0 = 0` or `deriv H s → deriv H 0` as `s → 0⁺`. -/
theorem deriv_zero_or_tendsto_nhdsWithin_Ioi {H : ℝ → ℝ}
    (hH_pos : ContDiffOn ℝ ∞ H (Ioi 0)) {M : ℝ} (hM : 0 ≤ M)
    (hM_bd : ∀ r ∈ Ioc (0 : ℝ) 1, |deriv (deriv H) r| ≤ M) :
    deriv H 0 = 0 ∨ Tendsto (deriv H) (𝓝[>] 0) (𝓝 (deriv H 0)) := by
  by_cases hH0 : DifferentiableAt ℝ H 0
  · right
    have hH_diff_pos : ∀ r > 0, DifferentiableAt ℝ H r := fun r hr =>
      (hH_pos.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)
    have hdH_pos : ContDiffOn ℝ ∞ (deriv H) (Ioi 0) :=
      hH_pos.deriv_of_isOpen isOpen_Ioi (by simp)
    have hdH_diff_pos : ∀ r > 0, DifferentiableAt ℝ (deriv H) r := fun r hr =>
      (hdH_pos.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)
    have hsec : ∀ s ∈ Ioc (0 : ℝ) 1, |deriv H s - (H s - H 0) / s| ≤ M * s := by
      intro s ⟨hs0, hs1⟩
      have hcont : ContinuousOn H (Icc 0 s) := by
        intro r hr
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · exact hH0.continuousAt.continuousWithinAt
        · exact (hH_diff_pos r hr_pos).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ H (Ioo 0 s) := fun r hr =>
        (hH_diff_pos r hr.1).differentiableWithinAt
      obtain ⟨c₁, ⟨hc₁_pos, hc₁_lt⟩, hc₁_eq⟩ := exists_deriv_eq_slope H hs0 hcont hdiff
      rw [sub_zero] at hc₁_eq
      have hd_cont : ContinuousOn (deriv H) (Icc c₁ s) := fun r hr =>
        (hdH_diff_pos r (hc₁_pos.trans_le hr.1)).continuousAt.continuousWithinAt
      have hd_diff : DifferentiableOn ℝ (deriv H) (Ioo c₁ s) := fun r hr =>
        (hdH_diff_pos r (hc₁_pos.trans hr.1)).differentiableWithinAt
      obtain ⟨c₂, ⟨hc₂_gt, hc₂_lt⟩, hc₂_eq⟩ :=
        exists_deriv_eq_slope (deriv H) hc₁_lt hd_cont hd_diff
      have hsc₁_pos : 0 < s - c₁ := sub_pos.2 hc₁_lt
      have hsub : deriv H s - deriv H c₁ = deriv (deriv H) c₂ * (s - c₁) :=
        ((eq_div_iff hsc₁_pos.ne').mp hc₂_eq).symm
      have hdiff_eq : deriv H s - (H s - H 0) / s = deriv (deriv H) c₂ * (s - c₁) := by
        rw [← hc₁_eq, hsub]
      rw [hdiff_eq, abs_mul, abs_of_pos hsc₁_pos]
      have hc₂_mem : c₂ ∈ Ioc (0 : ℝ) 1 := ⟨hc₁_pos.trans hc₂_gt, hc₂_lt.le.trans hs1⟩
      calc |deriv (deriv H) c₂| * (s - c₁)
          ≤ M * (s - c₁) := mul_le_mul_of_nonneg_right (hM_bd c₂ hc₂_mem) hsc₁_pos.le
        _ ≤ M * s := mul_le_mul_of_nonneg_left (by linarith) hM
    have hslope : Tendsto (fun s : ℝ => (H s - H 0) / s) (𝓝[>] 0) (𝓝 (deriv H 0)) := by
      have h1 := (hasDerivAt_iff_tendsto_slope.mp hH0.hasDerivAt).mono_left
        (nhdsWithin_mono 0 fun s (hs : 0 < s) => hs.ne')
      refine h1.congr fun s => ?_
      simp [slope_def_field, div_eq_inv_mul]
    have hrem : Tendsto (fun s : ℝ => deriv H s - (H s - H 0) / s) (𝓝[>] 0) (𝓝 0) := by
      have hMs : Tendsto (fun s : ℝ => M * s) (𝓝[>] 0) (𝓝 0) := by
        have hc : Continuous (fun s : ℝ => M * s) := continuous_const.mul continuous_id'
        simpa [mul_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hMs
      filter_upwards [Ioc_mem_nhdsGT one_pos] with s hs
      simpa [Real.norm_eq_abs] using hsec s hs
    simpa using (hslope.add hrem).congr fun s => by ring
  · exact Or.inl (deriv_zero_of_not_differentiableAt hH0)

/-- Inductive step for `ZeroOrRightTendsto`: if `ZeroOrRightTendsto h ψ` holds and `ψ s` is smooth
for `s ∈ Ioc 0 1` with `|deriv (ψ s) y| ≤ B₁` and `|deriv (deriv (ψ s)) y| ≤ B₂` uniformly in
`s ∈ Ioc 0 1` and `y ∈ ℝ`, then `ZeroOrRightTendsto (deriv h) (fun s => deriv (ψ s))` holds. -/
theorem ZeroOrRightTendsto.deriv_step {h : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hQ : ZeroOrRightTendsto h ψ)
    (hψ_sm : ∀ s ∈ Ioc (0 : ℝ) 1, ContDiff ℝ ∞ (ψ s))
    {B₁ B₂ : ℝ} (hB₁ : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ y : ℝ, |deriv (ψ s) y| ≤ B₁)
    (hB₂ : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ y : ℝ, |deriv (deriv (ψ s)) y| ≤ B₂) :
    ZeroOrRightTendsto (deriv h) (fun s => deriv (ψ s)) := by
  intro e
  have hself : ∀ᶠ x in 𝓝[>] e, e < x := self_mem_nhdsWithin
  by_cases hh : DifferentiableAt ℝ h e
  · by_cases hfreq : ∃ᶠ x in 𝓝[≠] e, h x = 0
    · have hhe : h e = 0 :=
        eq_of_tendsto_of_frequently_eq
          (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hfreq
      have hsl : Tendsto (slope h e) (𝓝[≠] e) (𝓝 (deriv h e)) :=
        hasDerivAt_iff_tendsto_slope.mp hh.hasDerivAt
      have hfreq_sl : ∃ᶠ x in 𝓝[≠] e, slope h e x = 0 := by
        refine hfreq.mono fun x hx => ?_
        simp [slope_def_field, hx, hhe]
      exact Or.inl (eq_of_tendsto_of_frequently_eq hsl hfreq_sl)
    · right
      have hev_ne : ∀ᶠ x in 𝓝[≠] e, h x ≠ 0 := not_frequently.mp hfreq
      have hev_gt : ∀ᶠ x in 𝓝[>] e, Tendsto (fun s => ψ s x) (𝓝[>] 0) (𝓝 (h x)) := by
        filter_upwards [hev_ne.filter_mono (nhdsWithin_mono e fun x (hx : e < x) => hx.ne')]
          with x hx_ne
        exact (hQ x).resolve_left hx_ne
      -- First show `ψ s e → h e` as `s → 0⁺`
      have hψ_e : Tendsto (fun s => ψ s e) (𝓝[>] 0) (𝓝 (h e)) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        have h1 : ∀ᶠ x in 𝓝[>] e, |h x - h e| < ε / 3 := by
          have hht : Tendsto h (𝓝[>] e) (𝓝 (h e)) :=
            hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          simpa [Real.dist_eq] using Metric.tendsto_nhds.mp hht (ε / 3) (by positivity)
        have h2 : ∀ᶠ x in 𝓝[>] e, B₁ * (x - e) < ε / 3 := by
          have hc_cont : Continuous (fun x : ℝ => B₁ * (x - e)) :=
            continuous_const.mul (continuous_id'.sub continuous_const)
          have hc : Tendsto (fun x : ℝ => B₁ * (x - e)) (𝓝[>] e) (𝓝 0) := by
            simpa [sub_self, mul_zero] using (hc_cont.tendsto e).mono_left nhdsWithin_le_nhds
          exact (tendsto_order.mp hc).2 (ε / 3) (by positivity)
        have hex : ∃ x : ℝ, (e < x ∧ Tendsto (fun s => ψ s x) (𝓝[>] 0) (𝓝 (h x))) ∧
            |h x - h e| < ε / 3 ∧ B₁ * (x - e) < ε / 3 :=
          ((hself.and hev_gt).and (h1.and h2)).exists
        obtain ⟨x, ⟨hex_lt, htx⟩, hhx, hB₁x⟩ := hex
        have htx_ev := Metric.tendsto_nhds.mp htx (ε / 3) (by positivity)
        filter_upwards [Ioc_mem_nhdsGT one_pos, htx_ev] with s hs hsx
        rw [Real.dist_eq] at hsx ⊢
        have hsec := (smooth_secant_bounds (hψ_sm s hs) (hB₁ s hs) (hB₂ s hs) hex_lt).1
        have h_tri : |ψ s e - h e| ≤ |ψ s x - ψ s e| + |ψ s x - h x| + |h x - h e| := by
          calc |ψ s e - h e|
              = |-(ψ s x - ψ s e) + (ψ s x - h x) + (h x - h e)| := by ring_nf
            _ ≤ |-(ψ s x - ψ s e) + (ψ s x - h x)| + |h x - h e| := abs_add_le _ _
            _ ≤ (|-(ψ s x - ψ s e)| + |ψ s x - h x|) + |h x - h e| :=
                add_le_add (abs_add_le _ _) le_rfl
            _ = |ψ s x - ψ s e| + |ψ s x - h x| + |h x - h e| := by rw [abs_neg]
        linarith
      -- Now show `deriv (ψ s) e → deriv h e` as `s → 0⁺`
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hsl_gt : Tendsto (fun x : ℝ => (h x - h e) / (x - e)) (𝓝[>] e) (𝓝 (deriv h e)) := by
        have h1 := (hasDerivAt_iff_tendsto_slope.mp hh.hasDerivAt).mono_left
          (nhdsWithin_mono e fun x (hx : e < x) => hx.ne')
        refine h1.congr fun x => ?_
        simp [slope_def_field, div_eq_inv_mul]
      have h1 : ∀ᶠ x in 𝓝[>] e, |(h x - h e) / (x - e) - deriv h e| < ε / 3 := by
        simpa [Real.dist_eq] using Metric.tendsto_nhds.mp hsl_gt (ε / 3) (by positivity)
      have h2 : ∀ᶠ x in 𝓝[>] e, B₂ * (x - e) < ε / 3 := by
        have hc_cont : Continuous (fun x : ℝ => B₂ * (x - e)) :=
          continuous_const.mul (continuous_id'.sub continuous_const)
        have hc : Tendsto (fun x : ℝ => B₂ * (x - e)) (𝓝[>] e) (𝓝 0) := by
          simpa [sub_self, mul_zero] using (hc_cont.tendsto e).mono_left nhdsWithin_le_nhds
        exact (tendsto_order.mp hc).2 (ε / 3) (by positivity)
      have hex : ∃ x : ℝ, (e < x ∧ Tendsto (fun s => ψ s x) (𝓝[>] 0) (𝓝 (h x))) ∧
          |(h x - h e) / (x - e) - deriv h e| < ε / 3 ∧ B₂ * (x - e) < ε / 3 :=
        ((hself.and hev_gt).and (h1.and h2)).exists
      obtain ⟨x, ⟨hex_lt, htx⟩, hsl_x, hB₂x⟩ := hex
      have hsec_tendsto : Tendsto (fun s : ℝ => (ψ s x - ψ s e) / (x - e))
          (𝓝[>] 0) (𝓝 ((h x - h e) / (x - e))) :=
        (htx.sub hψ_e).div_const (x - e)
      have hsec_ev := Metric.tendsto_nhds.mp hsec_tendsto (ε / 3) (by positivity)
      filter_upwards [Ioc_mem_nhdsGT one_pos, hsec_ev] with s hs hs_sec
      rw [Real.dist_eq] at hs_sec ⊢
      have hsec_bd := (smooth_secant_bounds (hψ_sm s hs) (hB₁ s hs) (hB₂ s hs) hex_lt).2
      have h_tri : |deriv (ψ s) e - deriv h e| ≤
          |deriv (ψ s) e - (ψ s x - ψ s e) / (x - e)| +
            |(ψ s x - ψ s e) / (x - e) - (h x - h e) / (x - e)| +
            |(h x - h e) / (x - e) - deriv h e| := by
        calc |deriv (ψ s) e - deriv h e|
            = |(deriv (ψ s) e - (ψ s x - ψ s e) / (x - e)) +
                ((ψ s x - ψ s e) / (x - e) - (h x - h e) / (x - e)) +
                ((h x - h e) / (x - e) - deriv h e)| := by ring_nf
          _ ≤ |(deriv (ψ s) e - (ψ s x - ψ s e) / (x - e)) +
                ((ψ s x - ψ s e) / (x - e) - (h x - h e) / (x - e))| +
                |(h x - h e) / (x - e) - deriv h e| := abs_add_le _ _
          _ ≤ (|deriv (ψ s) e - (ψ s x - ψ s e) / (x - e)| +
                |(ψ s x - ψ s e) / (x - e) - (h x - h e) / (x - e)|) +
                |(h x - h e) / (x - e) - deriv h e| :=
              add_le_add (abs_add_le _ _) le_rfl
      linarith
  · exact Or.inl (deriv_zero_of_not_differentiableAt hh)

/-- For every `ρ > 1/2`, `ℓ ≥ 1`, and `b : ℕ`, there is `ν_b > 0` such that for all `0 < ν ≤ ν_b`
and all BUC trains `tr`, `ZeroOrRightTendsto` holds between
`iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) 0)` and
`fun s => iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s)`. -/
theorem zeroOrRightTendsto_meanStream_of_tails
    (hTails : TrainStreamVelocityPressureTails)
    (hInt : TrainInteriorStripJetBounds)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∀ b : ℕ, ∃ ν_b : ℝ, 0 < ν_b ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν_b → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ZeroOrRightTendsto
          (iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) 0))
          (fun s => iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s)) := by
  intro b
  induction b with
  | zero =>
    obtain ⟨C₀, M₀, ν₀, hC₀, hν₀, hbd⟩ :=
      meanStream_pointwise_bound_pos_le_one hTails hInt ρ hρ 0 0 (ℓ + 1)
    refine ⟨ν₀, hν₀, ?_⟩
    intro ν hν hν_le tr htr e
    simp only [iteratedDeriv_zero]
    have hc0 : 0 < trainPeriod ρ ν := Real.rpow_pos_of_pos hν (-ρ)
    have hSmS : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
      (trainMeanEquations_proof ν (trainPeriod ρ ν) hν hc0 tr htr).1
    set k : ℕ := ℓ - 1
    have hk1 : k + 1 = ℓ := Nat.sub_add_cancel hℓ
    set H : ℝ → ℝ := fun r => iteratedDeriv k (fun t => meanStream tr t e) r
    have hH_pos : ContDiffOn ℝ ∞ H (Ioi 0) := by
      have hHk := UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 (meanStream tr) hSmS k
      have hline : ContDiff ℝ ∞ (fun r : ℝ => ((r, e) : ℝ × ℝ)) :=
        contDiff_id.prodMk contDiff_const
      exact hHk.comp hline.contDiffOn (fun r hr => ⟨hr, trivial⟩)
    have hdH : deriv H = fun r => iteratedDeriv ℓ (fun t => meanStream tr t e) r := by
      ext r
      rw [← hk1, iteratedDeriv_succ]
    have hddH : deriv (deriv H) =
        fun r => iteratedDeriv (ℓ + 1) (fun t => meanStream tr t e) r := by
      ext r
      rw [hdH, iteratedDeriv_succ]
    set α : ℝ := ((0 : ℕ) - (0 : ℕ) - 1) / 2 - ((ℓ + 1 : ℕ) : ℝ)
    set B : ℝ := polyP C₀ M₀ ν (trainPeriod ρ ν) * (2 : ℝ) ^ |α|
    have hB_nn : 0 ≤ B := by
      dsimp [B]
      unfold polyP
      have : 0 ≤ trainPeriod ρ ν := hc0.le
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      positivity
    have hB_bd : ∀ r ∈ Ioc (0 : ℝ) 1, |deriv (deriv H) r| ≤ B := by
      intro r ⟨hr0, hr1⟩
      rw [hddH]
      have h1 := hbd ν hν hν_le tr htr r hr0 hr1 e
      simp only [pow_zero, one_mul, iteratedDeriv_zero] at h1
      have h1r : (1 + r) ^ α ≤ (2 : ℝ) ^ |α| := by
        have h1r_pos : 0 < 1 + r := by linarith
        rcases le_total 0 α with hα | hα
        · calc (1 + r) ^ α ≤ (2 : ℝ) ^ α := Real.rpow_le_rpow h1r_pos.le (by linarith) hα
            _ ≤ (2 : ℝ) ^ |α| := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self α)
        · calc (1 + r) ^ α ≤ (1 + r) ^ (0 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) hα
            _ = 1 := Real.rpow_zero _
            _ ≤ (2 : ℝ) ^ |α| := Real.one_le_rpow (by norm_num) (abs_nonneg α)
      refine h1.trans (mul_le_mul_of_nonneg_left h1r ?_)
      unfold polyP
      have : 0 ≤ trainPeriod ρ ν := hc0.le
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      positivity
    have hres := deriv_zero_or_tendsto_nhdsWithin_Ioi hH_pos hB_nn hB_bd
    rwa [hdH] at hres
  | succ b ih =>
    obtain ⟨ν_b, hν_b, hQ_b⟩ := ih
    obtain ⟨C₁, M₁, ν₁, hC₁, hν₁, hbd₁⟩ :=
      meanStream_pointwise_bound_pos_le_one hTails hInt ρ hρ 0 (b + 1) ℓ
    obtain ⟨C₂, M₂, ν₂, hC₂, hν₂, hbd₂⟩ :=
      meanStream_pointwise_bound_pos_le_one hTails hInt ρ hρ 0 (b + 2) ℓ
    refine ⟨min ν_b (min ν₁ ν₂), lt_min hν_b (lt_min hν₁ hν₂), ?_⟩
    intro ν hν hν_le tr htr
    have hν_b_le : ν ≤ ν_b := hν_le.trans (min_le_left _ _)
    have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hc0 : 0 < trainPeriod ρ ν := Real.rpow_pos_of_pos hν (-ρ)
    have hSmS : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
      (trainMeanEquations_proof ν (trainPeriod ρ ν) hν hc0 tr htr).1
    set ψ : ℝ → ℝ → ℝ := fun s e => iteratedDeriv ℓ (fun r => meanStream tr r e) s
    have hsm_b : ∀ s ∈ Ioc (0 : ℝ) 1, ContDiff ℝ ∞ (iteratedDeriv b (ψ s)) := by
      intro s ⟨hs0, _⟩
      have hH := UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 (meanStream tr) hSmS ℓ
      have hline : ContDiff ℝ ∞ (fun e : ℝ => ((s, e) : ℝ × ℝ)) :=
        contDiff_const.prodMk contDiff_id
      have hψ_s : ContDiff ℝ ∞ (ψ s) :=
        contDiffOn_univ.mp (hH.comp (contDiffOn_univ.mpr hline) (fun _ _ => ⟨hs0, trivial⟩))
      exact contDiff_iteratedDeriv (ψ s) hψ_s b
    set α₁ : ℝ := ((0 : ℕ) - ((b + 1 : ℕ) : ℝ) - 1) / 2 - ℓ
    set α₂ : ℝ := ((0 : ℕ) - ((b + 2 : ℕ) : ℝ) - 1) / 2 - ℓ
    set B₁ : ℝ := polyP C₁ M₁ ν (trainPeriod ρ ν) * (2 : ℝ) ^ |α₁|
    set B₂ : ℝ := polyP C₂ M₂ ν (trainPeriod ρ ν) * (2 : ℝ) ^ |α₂|
    have h1s_le (α : ℝ) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) : (1 + s) ^ α ≤ (2 : ℝ) ^ |α| := by
      rcases hs with ⟨hs0, hs1⟩
      have h1s_pos : 0 < 1 + s := by linarith
      rcases le_total 0 α with hα | hα
      · calc (1 + s) ^ α ≤ (2 : ℝ) ^ α := Real.rpow_le_rpow h1s_pos.le (by linarith) hα
          _ ≤ (2 : ℝ) ^ |α| := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self α)
      · calc (1 + s) ^ α ≤ (1 + s) ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) hα
          _ = 1 := Real.rpow_zero _
          _ ≤ (2 : ℝ) ^ |α| := Real.one_le_rpow (by norm_num) (abs_nonneg α)
    have hB₁_bd : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ y : ℝ, |deriv (iteratedDeriv b (ψ s)) y| ≤ B₁ := by
      intro s hs y
      rw [← iteratedDeriv_succ]
      have h1 := hbd₁ ν hν hν₁_le tr htr s hs.1 hs.2 y
      simp only [pow_zero, one_mul] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left (h1s_le α₁ hs) ?_)
      unfold polyP
      have : 0 ≤ trainPeriod ρ ν := hc0.le
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      positivity
    have hB₂_bd : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ y : ℝ,
        |deriv (deriv (iteratedDeriv b (ψ s))) y| ≤ B₂ := by
      intro s hs y
      rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
      have h1 := hbd₂ ν hν hν₂_le tr htr s hs.1 hs.2 y
      simp only [pow_zero, one_mul] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left (h1s_le α₂ hs) ?_)
      unfold polyP
      have : 0 ≤ trainPeriod ρ ν := hc0.le
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      positivity
    have hstep := (hQ_b ν hν hν_b_le tr htr).deriv_step hsm_b hB₁_bd hB₂_bd
    intro e
    simpa [iteratedDeriv_succ] using hstep e

end PartI_T23

/-! ### 6. Boundary leaf at `s = 0, ℓ ≥ 1` and assembly of `TrainMeanStreamLpBound` -/

/-- **Boundary slice-derivative bound for `meanStream` at `s = 0` when `ℓ ≥ 1`**
(source lines 459-462, 539-540): for `s = 0` and `ℓ ≥ 1`,
`|η|^m |∂_η^b (∂_s^ℓ S(0, ·))(η)| ≤ polyP C M ν c`. -/
def TrainMeanStreamZeroAgeDerivBound : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ m b ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ,
    0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      let c := trainPeriod ρ ν
      ∀ η : ℝ,
        |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) 0) η| ≤
          polyP C M ν c

namespace PartI_T23

/-- **Unconditional proof of `TrainMeanStreamZeroAgeDerivBound` from
`TrainStreamVelocityPressureTails`**: transfers the uniform `(0, 1]` bound of
`meanStream_pointwise_bound_pos_le_one` to `s = 0` via `zeroOrRightTendsto_meanStream_of_tails`. -/
theorem trainMeanStreamZeroAgeDerivBound_of_tails
    (hTails : TrainStreamVelocityPressureTails) : TrainMeanStreamZeroAgeDerivBound := by
  have hInt := trainInteriorStripJetBounds_of_tails hTails
  intro ρ hρ m b ℓ hℓ
  obtain ⟨C, M, ν₁, hC, hν₁, hLe1⟩ :=
    meanStream_pointwise_bound_pos_le_one hTails hInt ρ hρ m b ℓ
  obtain ⟨ν₂, hν₂, hQ⟩ :=
    zeroOrRightTendsto_meanStream_of_tails hTails hInt ρ hρ ℓ hℓ b
  refine ⟨C, M, min ν₁ ν₂, hC, lt_min hν₁ hν₂, ?_⟩
  intro ν hν hν_le tr htr c η
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  have hP_nn : 0 ≤ polyP C M ν c := by
    unfold polyP
    have : 0 ≤ c := hc0.le
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    positivity
  rcases hQ ν hν hν₂_le tr htr η with hzero | htend
  · rw [hzero, abs_zero, mul_zero]
    exact hP_nn
  · have h_lhs : Tendsto
        (fun s : ℝ => |η| ^ m *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η|)
        (𝓝[>] 0)
        (𝓝 (|η| ^ m *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) 0) η|)) :=
      tendsto_const_nhds.mul htend.abs
    set α : ℝ := ((m : ℝ) - b - 1) / 2 - ℓ
    have h_rhs : Tendsto (fun s : ℝ => polyP C M ν c * (1 + s) ^ α)
        (𝓝[>] 0) (𝓝 (polyP C M ν c)) := by
      have h1s : ContinuousAt (fun s : ℝ => polyP C M ν c * (1 + s) ^ α) 0 :=
        continuousAt_const.mul
          ((continuousAt_const.add continuousAt_id).rpow continuousAt_const
            (Or.inl (by norm_num)))
      simpa [add_zero, Real.one_rpow, mul_one] using
        h1s.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto h_lhs h_rhs ?_
    filter_upwards [Ioc_mem_nhdsGT one_pos] with s ⟨hs0, hs1⟩
    exact hLe1 ν hν hν₁_le tr htr s hs0 hs1 η

end PartI_T23

/-- **Full weighted pointwise bound for `meanStream` on `s ≥ 0`** assembled from
`TrainStreamVelocityPressureTails` (for `0 ≤ s ≤ 1`) and `TrainMeanRemainderPointwiseBound` +
`TrainFluctuationDecay` (for `s ≥ 1`). -/
theorem trainMeanStreamPointwise_of
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (hRem : TrainMeanRemainderPointwiseBound)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (m b ℓ : ℕ) :
    ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        ∀ s : ℝ, 0 ≤ s → ∀ η : ℝ,
          |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| ≤
            polyP C M ν c * (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ) := by
  have hInt := PartI_T23.trainInteriorStripJetBounds_of_tails hTails
  have hZero := PartI_T23.trainMeanStreamZeroAgeDerivBound_of_tails hTails
  obtain ⟨C₁, M₁, ν₁, hC₁, hν₁, hLe1⟩ :=
    PartI_T23.meanStream_pointwise_bound_pos_le_one hTails hInt ρ hρ m b ℓ
  obtain ⟨C₂, M₂, ν₂, hC₂, hν₂, hGe1⟩ :=
    PartI_T23.meanStream_pointwise_bound_ge_one_of_remainder hRem hFD ρ hρ m b ℓ
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ_pos
  · obtain ⟨C₀, hC₀, hAt0⟩ := PartI_T23.meanStream_pointwise_bound_zero_age_zero_deriv ρ hρ m b
    let C := max C₀ (max C₁ C₂)
    let M := max M₁ M₂
    let ν₀ := min (min ν₁ ν₂) 1
    refine ⟨C, M, ν₀, lt_max_of_lt_left hC₀, lt_min (lt_min hν₁ hν₂) one_pos, ?_⟩
    intro ν hν hν_le tr htr c s hs η
    have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
    have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
      have : 0 ≤ c := Real.rpow_nonneg hν.le _
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    have h1s_nn : 0 ≤ (1 + s) ^ (((m : ℝ) - b - 1) / 2 - (0 : ℕ)) :=
      Real.rpow_nonneg (by linarith) _
    rcases eq_or_lt_of_le hs with rfl | hs_pos
    · refine (hAt0 ν hν hν1 tr htr η).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ h1s_nn
      unfold polyP
      calc C₀ * (1 + c + ν⁻¹) ^ 0 ≤ C * (1 + c + ν⁻¹) ^ 0 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ C * (1 + c + ν⁻¹) ^ M :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (Nat.zero_le M))
              (hC₀.le.trans (le_max_left _ _))
    · rcases le_or_gt s 1 with hs1 | hs1
      · refine (hLe1 ν hν hν₁_le tr htr s hs_pos hs1 η).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ h1s_nn
        unfold polyP
        exact mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
          (pow_le_pow_right₀ hX1 (le_max_left _ _)) (by positivity)
          (hC₀.le.trans (le_max_left _ _))
      · refine (hGe1 ν hν hν₂_le tr htr s hs1.le η).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ h1s_nn
        unfold polyP
        exact mul_le_mul ((le_max_right _ _).trans (le_max_right _ _))
          (pow_le_pow_right₀ hX1 (le_max_right _ _)) (by positivity)
          (hC₀.le.trans (le_max_left _ _))
  · obtain ⟨C₀, M₀, ν₀', hC₀, hν₀', hAt0⟩ := hZero ρ hρ m b ℓ hℓ_pos
    let C := max C₀ (max C₁ C₂)
    let M := max M₀ (max M₁ M₂)
    let ν₀ := min ν₀' (min ν₁ ν₂)
    refine ⟨C, M, ν₀, lt_max_of_lt_left hC₀, lt_min hν₀' (lt_min hν₁ hν₂), ?_⟩
    intro ν hν hν_le tr htr c s hs η
    have hν₀'_le : ν ≤ ν₀' := hν_le.trans (min_le_left _ _)
    have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
      have : 0 ≤ c := Real.rpow_nonneg hν.le _
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    have h1s_nn : 0 ≤ (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ) :=
      Real.rpow_nonneg (by linarith) _
    rcases eq_or_lt_of_le hs with rfl | hs_pos
    · simp only [add_zero, Real.one_rpow, mul_one]
      refine (hAt0 ν hν hν₀'_le tr htr η).trans ?_
      unfold polyP
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hX1 (le_max_left _ _))
        (by positivity) (hC₀.le.trans (le_max_left _ _))
    · rcases le_or_gt s 1 with hs1 | hs1
      · refine (hLe1 ν hν hν₁_le tr htr s hs_pos hs1 η).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ h1s_nn
        unfold polyP
        exact mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
          (pow_le_pow_right₀ hX1 ((le_max_left _ _).trans (le_max_right _ _)))
          (by positivity) (hC₀.le.trans (le_max_left _ _))
      · refine (hGe1 ν hν hν₂_le tr htr s hs1.le η).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ h1s_nn
        unfold polyP
        exact mul_le_mul ((le_max_right _ _).trans (le_max_right _ _))
          (pow_le_pow_right₀ hX1 ((le_max_right _ _).trans (le_max_right _ _)))
          (by positivity) (hC₀.le.trans (le_max_left _ _))

/-- **Conditional assembly of `TrainMeanStreamLpBound` (`PartI:T23/3`)**: derives the full
`L^p(ℝ)` bound (`1 ≤ p ≤ ∞`) for all `s ≥ 0` from `TrainStreamVelocityPressureTails`,
`TrainFluctuationDecay`, and `TrainMeanRemainderLpBound` (`PartI:T23/2`) via
`PartI_T23.eLpNorm_pow_mul_le_of_pointwise` at scale `R = 1 + s ≥ 1`. -/
theorem trainMeanStreamLpBound_of
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (_hMP : OverlapMeanPrimitive)
    (hRemLp : TrainMeanRemainderLpBound) :
    TrainMeanStreamLpBound := by
  have hRem := trainMeanRemainderPointwiseBound_of_lp hRemLp
  intro ρ hρ m b ℓ p hp
  obtain ⟨C₀, M₀, ν₀, hC₀, hν₀, h0⟩ :=
    trainMeanStreamPointwise_of hTails hFD hRem ρ hρ m b ℓ
  obtain ⟨C₂, M₂, ν₂, hC₂, hν₂, h2⟩ :=
    trainMeanStreamPointwise_of hTails hFD hRem ρ hρ (m + 2) b ℓ
  refine ⟨Real.pi * (C₀ + C₂), max M₀ M₂, min ν₀ ν₂,
    mul_pos Real.pi_pos (add_pos hC₀ hC₂), lt_min hν₀ hν₂, ?_⟩
  intro ν hν hν_le tr htr c s hs
  have hν₀_le : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  have h1s : 1 ≤ 1 + s := by linarith
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ c := Real.rpow_nonneg hν.le _
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hP₀ : polyP C₀ M₀ ν c ≤ polyP C₀ (max M₀ M₂) ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₀.le
  have hP₂ : polyP C₂ M₂ ν c ≤ polyP C₂ (max M₀ M₂) ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) hC₂.le
  set α : ℝ := ((m : ℝ) - b - 1) / 2 - ℓ
  have hα2 : (((m + 2 : ℕ) : ℝ) - b - 1) / 2 - ℓ = α + 1 := by
    dsimp [α]; push_cast; ring
  have hpt0 : ∀ η : ℝ, |η| ^ m * |iteratedDeriv b
      (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| ≤
      polyP C₀ (max M₀ M₂) ν c * (1 + s) ^ α := fun η =>
    (h0 ν hν hν₀_le tr htr s hs η).trans
      (mul_le_mul_of_nonneg_right hP₀ (Real.rpow_nonneg (zero_le_one.trans h1s) _))
  have hpt2 : ∀ η : ℝ, |η| ^ (m + 2) * |iteratedDeriv b
      (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| ≤
      polyP C₂ (max M₀ M₂) ν c * (1 + s) ^ (α + 1) := by
    intro η
    have h := h2 ν hν hν₂_le tr htr s hs η
    rw [hα2] at h
    exact h.trans (mul_le_mul_of_nonneg_right hP₂ (Real.rpow_nonneg (zero_le_one.trans h1s) _))
  have hA₀ : 0 ≤ polyP C₀ (max M₀ M₂) ν c := by unfold polyP; positivity
  have hA₂ : 0 ≤ polyP C₂ (max M₀ M₂) ν c := by unfold polyP; positivity
  refine (PartI_T23.eLpNorm_pow_mul_le_of_pointwise
    (fun η => iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η)
    m h1s hA₀ hA₂ hp hpt0 hpt2).trans (le_of_eq ?_)
  congr 1
  unfold polyP
  ring

end UnforcedLeray.Short.PartI
