import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.ZeroModeTail.MeanVorticityFTC
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.ZeroModeTail.Jet1D

/-!
# `PartI:T21/1/2`: Zero-mode stream and velocity transverse tail (`ZeroModeTail.lean`)

Source of record: `the November 2 reference manuscript`, lines 504-513
(old 498-506).

Proves `trainZeroModeStreamVelTail_proof`:
```lean
theorem trainZeroModeStreamVelTail_proof
    (hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail) :
    TrainZeroModeStreamVelTail
```
unconditionally for all `ℓ, j : ℕ`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet)

namespace PartI_T21

/-! ### 1. Monotonicity and finite aggregation of `TrainVorticityGaussianTail` -/

/-- Monotonicity of `polyP C N ν c` in `(C, N)` for `ν > 0, c ≥ 0`. -/
private theorem polyP_mono {C₁ C₂ ν c : ℝ} {N₁ N₂ : ℕ}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hN : N₁ ≤ N₂) (hν : 0 < ν) (hc : 0 ≤ c) :
    polyP C₁ N₁ ν c ≤ polyP C₂ N₂ ν c := by
  unfold polyP
  have h1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  exact mul_le_mul hC (pow_le_pow_right₀ h1 hN) (by positivity) (hC₁.trans hC)

/-- Monotonicity of the Gaussian factor `exp(-(b * (max (|z.2| - C'/ν) 0)² / (C₀ + ν * s)))`
when decreasing `b` (`0 < b₁ ≤ b₂`) and increasing `C₀` (`0 < C₀₁ ≤ C₀₂`) and `C'` (`C'₁ ≤ C'₂`). -/
private theorem exp_gaussian_mono (z : Plane) {b₁ b₂ C₀₁ C₀₂ C'₁ C'₂ ν s : ℝ}
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hC₀₁ : 0 < C₀₁) (hC₀ : C₀₁ ≤ C₀₂)
    (hC' : C'₁ ≤ C'₂) (hν : 0 < ν) (hs : 0 ≤ s) :
    Real.exp (-(b₂ * (max (|z.2| - C'₁ / ν) 0) ^ 2 / (C₀₁ + ν * s))) ≤
      Real.exp (-(b₁ * (max (|z.2| - C'₂ / ν) 0) ^ 2 / (C₀₂ + ν * s))) := by
  apply Real.exp_le_exp.2
  apply neg_le_neg
  have hd : max (|z.2| - C'₂ / ν) 0 ≤ max (|z.2| - C'₁ / ν) 0 :=
    max_le_max (sub_le_sub_left (div_le_div_of_nonneg_right hC' hν.le) _) le_rfl
  have hsq : (max (|z.2| - C'₂ / ν) 0) ^ 2 ≤ (max (|z.2| - C'₁ / ν) 0) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) hd 2
  have hnum : b₁ * (max (|z.2| - C'₂ / ν) 0) ^ 2 ≤ b₂ * (max (|z.2| - C'₁ / ν) 0) ^ 2 :=
    mul_le_mul hb hsq (sq_nonneg _) (hb₁.le.trans hb)
  have hden_pos : 0 < C₀₁ + ν * s := by positivity
  have hden : C₀₁ + ν * s ≤ C₀₂ + ν * s := add_le_add hC₀ le_rfl
  have hb₂ : 0 < b₂ := hb₁.trans_le hb
  exact div_le_div₀ (by positivity) hnum hden_pos hden

/-- Uniform vorticity Gaussian tail bound across all age orders `k ≤ ℓ` at spatial order `0`. -/
theorem uniform_vorticity_tail_age₀ (hVort : TrainVorticityGaussianTail)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    ∀ ℓ : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
      ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ k ≤ ℓ,
              let c := trainPeriod ρ ν
              let d := max (|z.2| - C' / ν) 0
              ‖ageJet k 0 (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
                polyP C N ν c * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))
  | 0 => by
    obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, h0⟩ := hVort ρ hρ 0 0
    refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀,
      fun ν hν hν_le tr htr s hs z k hk => ?_⟩
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact h0 ν hν hν_le tr htr s hs z
  | ℓ + 1 => by
    obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ :=
      uniform_vorticity_tail_age₀ hVort hρ ℓ
    obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂, N₂, ν₂, hC₂, hν₂, hL1⟩ :=
      hVort ρ hρ (ℓ + 1) 0
    refine ⟨min b₁ b₂, max C₀₁ C₀₂, max C'₁ C'₂, lt_min hb₁ hb₂,
      lt_max_of_lt_left hC₀₁, lt_max_of_lt_left hC'₁,
      max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z k hk
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    rcases Nat.of_le_succ hk with hkL | rfl
    · have h1 := hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z k hkL
      refine h1.trans (mul_le_mul
        (polyP_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc0)
        (exp_gaussian_mono z (lt_min hb₁ hb₂) (min_le_left _ _) hC₀₁ (le_max_left _ _)
          (le_max_left _ _) hν hs.le)
        (Real.exp_nonneg _) (by unfold polyP; positivity))
    · have h2 := hL1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs z
      refine h2.trans (mul_le_mul
        (polyP_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc0)
        (exp_gaussian_mono z (lt_min hb₁ hb₂) (min_le_right _ _) hC₀₂ (le_max_right _ _)
          (le_max_right _ _) hν hs.le)
        (Real.exp_nonneg _) (by unfold polyP; positivity))

/-! ### 2. Polynomial envelope comparison for 0, 1, and 2 integrations -/

/-- Bounds `M`, `M * (A / (4 * b))`, and `M * (A / (4 * b)) ^ 2` simultaneously by
`polyPS (C * (1 + (C₀ + ν₀) / (4 * b)) ^ 2) (N + 2) ν c S_` when `M = polyP C N ν c` and
`A = C₀ + ν * S_` with `0 < ν ≤ ν₀` and `0 ≤ S_`. -/
theorem polyP_mul_factor_le_polyPS {b C₀ C ν₀ ν c S_ : ℝ} {N : ℕ}
    (hb : 0 < b) (hC₀ : 0 < C₀) (hC : 0 < C) (hν : 0 < ν) (hν_le : ν ≤ ν₀)
    (hc : 0 ≤ c) (hS_ : 0 ≤ S_) :
    let D := 1 + (C₀ + ν₀) / (4 * b)
    let M := polyP C N ν c
    let A := C₀ + ν * S_
    let P := polyPS (C * D ^ 2) (N + 2) ν c S_
    M ≤ P ∧ M * (A / (4 * b)) ≤ P ∧ M * (A / (4 * b)) ^ 2 ≤ P := by
  intro D M A P
  have hν₀ : 0 < ν₀ := hν.trans_le hν_le
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have : 0 ≤ (C₀ + ν₀) / (4 * b) := by positivity
    linarith
  have hS1 : 1 ≤ 1 + S_ := by linarith
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hA_pos : 0 < A := by dsimp [A]; positivity
  have hA_le : A / (4 * b) ≤ D * (1 + S_) := by
    have hA_bound : A ≤ (C₀ + ν₀) * (1 + S_) := by
      dsimp [A]
      nlinarith
    have hdiv : A / (4 * b) ≤ ((C₀ + ν₀) / (4 * b)) * (1 + S_) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hA_bound (by positivity)
    have hD_le : (C₀ + ν₀) / (4 * b) ≤ D := by dsimp [D]; linarith
    exact hdiv.trans (mul_le_mul_of_nonneg_right hD_le (by positivity))
  have hDS1 : 1 ≤ D * (1 + S_) := one_le_mul_of_one_le_of_one_le hD1 hS1
  have h1_le_sq : 1 ≤ D ^ 2 * (1 + S_) ^ 2 := by
    have : 1 ^ 2 ≤ (D * (1 + S_)) ^ 2 := pow_le_pow_left₀ zero_le_one hDS1 2
    linarith [show (D * (1 + S_)) ^ 2 = D ^ 2 * (1 + S_) ^ 2 by ring]
  have hA_le_sq : A / (4 * b) ≤ D ^ 2 * (1 + S_) ^ 2 := by
    calc A / (4 * b) ≤ D * (1 + S_) := hA_le
      _ = (D * (1 + S_)) * 1 := (mul_one _).symm
      _ ≤ (D * (1 + S_)) * (D * (1 + S_)) :=
          mul_le_mul_of_nonneg_left hDS1 (by positivity)
      _ = D ^ 2 * (1 + S_) ^ 2 := by ring
  have hA2_le_sq : (A / (4 * b)) ^ 2 ≤ D ^ 2 * (1 + S_) ^ 2 := by
    have : (A / (4 * b)) ^ 2 ≤ (D * (1 + S_)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hA_le 2
    linarith [show (D * (1 + S_)) ^ 2 = D ^ 2 * (1 + S_) ^ 2 by ring]
  have hM_nonneg : 0 ≤ M := by dsimp [M]; unfold polyP; positivity
  have hbase_le : M * (D ^ 2 * (1 + S_) ^ 2) ≤ P := by
    dsimp [M, P]
    unfold polyP polyPS
    rw [mul_pow]
    have hpowX : (1 + c + ν⁻¹) ^ N ≤ (1 + c + ν⁻¹) ^ (N + 2) :=
      pow_le_pow_right₀ hX1 (Nat.le_add_right N 2)
    have hpowS : (1 + S_) ^ 2 ≤ (1 + S_) ^ (N + 2) :=
      pow_le_pow_right₀ hS1 (Nat.le_add_left 2 N)
    calc C * (1 + c + ν⁻¹) ^ N * (D ^ 2 * (1 + S_) ^ 2)
        = (C * D ^ 2) * ((1 + c + ν⁻¹) ^ N * (1 + S_) ^ 2) := by ring
      _ ≤ (C * D ^ 2) * ((1 + c + ν⁻¹) ^ (N + 2) * (1 + S_) ^ (N + 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hpowX hpowS (by positivity) (by positivity))
            (by positivity)
      _ = C * D ^ 2 * ((1 + c + ν⁻¹) ^ (N + 2) * (1 + S_) ^ (N + 2)) := by ring
  refine ⟨?_, ?_, ?_⟩
  · calc M = M * 1 := (mul_one M).symm
      _ ≤ M * (D ^ 2 * (1 + S_) ^ 2) := mul_le_mul_of_nonneg_left h1_le_sq hM_nonneg
      _ ≤ P := hbase_le
  · exact (mul_le_mul_of_nonneg_left hA_le_sq hM_nonneg).trans hbase_le
  · exact (mul_le_mul_of_nonneg_left hA2_le_sq hM_nonneg).trans hbase_le

/-! ### 3. Pointwise age-derivative tail bounds for `meanVel1` and `meanStream` -/

/-- From the uniform vorticity Gaussian tail across `k ≤ ℓ` at spatial order `0`, bounds
`|iteratedDeriv ℓ (fun r => meanVel1 tr r η₀) s|` and
`|iteratedDeriv ℓ (fun r => meanStream tr r η₀) s|` at `η₀ ≥ C' / ν + 2 + l` and `0 < s ≤ S_`. -/
theorem iteratedDeriv_meanVel1_meanStream_tail_bound
    {ν c b C₀ C' C S_ l s η₀ : ℝ} {N ℓ : ℕ}
    (hν : 0 < ν) (hc : 0 < c) (hb : 0 < b) (hC₀ : 0 < C₀) (hC' : 0 < C') (hC : 0 < C)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hl : 0 ≤ l) (hs : 0 < s) (hsS : s ≤ S_) (hη₀ : C' / ν + 2 + l ≤ η₀)
    (hvort : ∀ r : ℝ, 0 < r → ∀ z : Plane, ∀ k ≤ ℓ,
      ‖ageJet k 0 (fun t w => Cyl.curl (tr.v t) w) r z‖ ≤
        polyP C N ν c * Real.exp (-(b * (max (|z.2| - C' / ν) 0) ^ 2 / (C₀ + ν * r)))) :
    let M := polyP C N ν c
    let A := C₀ + ν * S_
    |iteratedDeriv ℓ (fun r => meanVel1 tr r η₀) s| ≤
      M * (A / (4 * b)) * Real.exp (-(b * l ^ 2 / A)) ∧
    |iteratedDeriv ℓ (fun r => meanStream tr r η₀) s| ≤
      M * (A / (4 * b)) ^ 2 * Real.exp (-(b * l ^ 2 / A)) := by
  intro M A
  have hM_pos : 0 < M := by dsimp [M]; unfold polyP; positivity
  have hA_pos : 0 < A := by dsimp [A]; linarith [mul_nonneg hν.le (hs.le.trans hsS)]
  -- Step 1: Pointwise bound on `|iteratedDeriv k (fun r => hmean c (Cyl.curl (tr.v r)) ζ) r|`
  have hW_bound : ∀ r : ℝ, 0 < r → ∀ ζ : ℝ, ∀ k ≤ ℓ,
      |iteratedDeriv k (fun t => hmean c (Cyl.curl (tr.v t)) ζ) r| ≤
        M * Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / (C₀ + ν * r))) := by
    intro r hr ζ k hk
    have hB0 : 0 ≤ M * Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / (C₀ + ν * r))) :=
      mul_nonneg hM_pos.le (Real.exp_nonneg _)
    have h1 := norm_ageJet_hmean_scalar_le (f := fun t w => Cyl.curl (tr.v t) w) hc hB0
      (PartI_T20.smR_curl (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)))
      k 0 hr (0, ζ) (fun q _ => hvort r hr (q, ζ) k hk)
    unfold ageJet jet at h1
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  -- Step 2: Apply `iteratedDeriv_eq_integral_Ioi` on `Ioo 0 R` with `R = s + 1`
  let R : ℝ := s + 1
  have hsR : s ∈ Ioo 0 R := ⟨hs, by dsimp [R]; linarith⟩
  let A_R : ℝ := C₀ + ν * R
  have hA_R_pos : 0 < A_R := by dsimp [A_R, R]; positivity
  let a_R : ℝ := 4 * b / A_R
  have ha_R_pos : 0 < a_R := by dsimp [a_R]; positivity
  let B_R : ℝ := M * Real.exp (-(b * l ^ 2 / A_R))
  have hB_R_nonneg : 0 ≤ B_R := by dsimp [B_R]; positivity
  have hW_dom_R : ∀ k ≤ ℓ, ∀ r ∈ Ioo 0 R, ∀ ζ : ℝ, η₀ ≤ ζ →
      |iteratedDeriv k (fun t => hmean c (Cyl.curl (tr.v t)) ζ) r| ≤
        B_R * Real.exp (-a_R * (ζ - η₀)) := by
    intro k hk r hr ζ hζ
    have hAr : C₀ + ν * r ≤ A_R := by dsimp [A_R]; nlinarith [hr.2]
    have hAr_pos : 0 < C₀ + ν * r := by linarith [mul_pos hν hr.1]
    have hexp_mono : Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / (C₀ + ν * r))) ≤
        Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / A_R)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_left (by positivity) hAr_pos hAr
    have hlin := gaussian_linear_tail_bound hb hA_R_pos hC' hν hl hη₀ hζ
    calc |iteratedDeriv k (fun t => hmean c (Cyl.curl (tr.v t)) ζ) r|
        ≤ M * Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / (C₀ + ν * r))) :=
          hW_bound r hr.1 ζ k hk
      _ ≤ M * Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / A_R)) :=
          mul_le_mul_of_nonneg_left hexp_mono hM_pos.le
      _ ≤ M * (Real.exp (-(b * l ^ 2 / A_R)) * Real.exp (-a_R * (ζ - η₀))) :=
          mul_le_mul_of_nonneg_left (by simpa [a_R] using hlin) hM_pos.le
      _ = B_R * Real.exp (-a_R * (ζ - η₀)) := by dsimp [B_R]; ring
  have hW_smooth : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => hmean c (Cyl.curl (tr.v x.1)) x.2)
      (Ioi 0 ×ˢ univ) := contDiffOn_hmean_curl hc tr
  have hU_smooth : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2)
      (Ioi 0 ×ˢ univ) := contDiffOn_meanVel1 hc tr
  -- Commute `iteratedDeriv k` with `∫ ζ in Ioi ξ` for `meanVel1` at all `ξ ≥ η₀`
  have hU_int : ∀ k ≤ ℓ, ∀ r ∈ Ioo 0 R, ∀ ξ : ℝ, η₀ ≤ ξ →
      iteratedDeriv k (fun t => meanVel1 tr t ξ) r =
        ∫ ζ in Ioi ξ, iteratedDeriv k (fun t => hmean c (Cyl.curl (tr.v t)) ζ) r := by
    refine iteratedDeriv_eq_integral_Ioi (F := fun t ξ => meanVel1 tr t ξ)
      (G := fun t ζ => hmean c (Cyl.curl (tr.v t)) ζ) (R := R) (η₀ := η₀) (ℓ := ℓ)
      hW_smooth ?_ ?_
    · intro t ht ξ hξ
      have hcont0 : Continuous (hmean c (Cyl.curl (tr.v t))) := by
        simpa [iteratedDeriv_zero] using
          continuous_slice_iteratedDeriv_1D (G := fun r ζ => hmean c (Cyl.curl (tr.v r)) ζ)
            hW_smooth 0 ht.1
      have hint0 := (abs_integral_Ioi_exp_reproduce hcont0 hB_R_nonneg ha_R_pos
        (fun ζ hζ => by simpa [iteratedDeriv_zero] using hW_dom_R 0 (Nat.zero_le ℓ) t ht ζ hζ) hξ).1
      exact meanVel1_eq_integral_Ioi_curl hν hc tr htr ht.1.le ξ hint0
    · intro j hj ξ hξ
      refine ⟨B_R * Real.exp (-a_R * (ξ - η₀)), a_R,
        mul_nonneg hB_R_nonneg (Real.exp_nonneg _), ha_R_pos, ?_⟩
      intro t ht ζ hζ
      have hζ₀ : η₀ ≤ ζ := hξ.trans (le_of_lt hζ)
      have hexp_split : Real.exp (-a_R * (ζ - η₀)) =
          Real.exp (-a_R * (ξ - η₀)) * Real.exp (-a_R * (ζ - ξ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc |iteratedDeriv j (fun u => hmean c (Cyl.curl (tr.v u)) ζ) t|
          ≤ B_R * Real.exp (-a_R * (ζ - η₀)) := hW_dom_R j hj t ht ζ hζ₀
        _ = (B_R * Real.exp (-a_R * (ξ - η₀))) * Real.exp (-a_R * (ζ - ξ)) := by
            rw [hexp_split]; ring
  -- Deduce uniform exponential domination for `meanVel1` on `Ioo 0 R` and `ξ ≥ η₀`
  have hU_dom_R : ∀ k ≤ ℓ, ∀ r ∈ Ioo 0 R, ∀ ξ : ℝ, η₀ ≤ ξ →
      |iteratedDeriv k (fun t => meanVel1 tr t ξ) r| ≤
        (B_R * a_R⁻¹) * Real.exp (-a_R * (ξ - η₀)) := by
    intro k hk r hr ξ hξ
    rw [hU_int k hk r hr ξ hξ]
    have hcont : Continuous (fun ζ : ℝ =>
        iteratedDeriv k (fun t => hmean c (Cyl.curl (tr.v t)) ζ) r) :=
      continuous_slice_iteratedDeriv_1D (G := fun t ζ => hmean c (Cyl.curl (tr.v t)) ζ)
        hW_smooth k hr.1
    exact (abs_integral_Ioi_exp_reproduce hcont hB_R_nonneg ha_R_pos
      (fun ζ hζ => hW_dom_R k hk r hr ζ hζ) hξ).2
  -- Commute `iteratedDeriv ℓ` with `∫ ξ in Ioi η₀` for `meanStream` at `r = s`
  have hS_int_s : iteratedDeriv ℓ (fun t => meanStream tr t η₀) s =
      ∫ ξ in Ioi η₀, iteratedDeriv ℓ (fun t => meanVel1 tr t ξ) s := by
    refine iteratedDeriv_eq_integral_Ioi (F := fun t η => meanStream tr t η)
      (G := fun t ξ => meanVel1 tr t ξ) (R := R) (η₀ := η₀) (ℓ := ℓ)
      hU_smooth ?_ ?_ ℓ le_rfl s hsR η₀ le_rfl
    · intro t ht η hη
      have hcont0 : Continuous (meanVel1 tr t) := by
        simpa [iteratedDeriv_zero] using
          continuous_slice_iteratedDeriv_1D hU_smooth 0 ht.1
      have hint0 := (abs_integral_Ioi_exp_reproduce hcont0
        (mul_nonneg hB_R_nonneg (inv_nonneg.2 ha_R_pos.le)) ha_R_pos
        (fun ξ hξ => by simpa [iteratedDeriv_zero] using hU_dom_R 0 (Nat.zero_le ℓ) t ht ξ hξ) hη).1
      exact meanStream_eq_integral_Ioi_meanVel1 hν hc tr ht.1.le η hint0
    · intro j hj η hη
      refine ⟨(B_R * a_R⁻¹) * Real.exp (-a_R * (η - η₀)), a_R,
        mul_nonneg (mul_nonneg hB_R_nonneg (inv_nonneg.2 ha_R_pos.le)) (Real.exp_nonneg _),
        ha_R_pos, ?_⟩
      intro t ht ξ hξ
      have hξ₀ : η₀ ≤ ξ := hη.trans (le_of_lt hξ)
      have hexp_split : Real.exp (-a_R * (ξ - η₀)) =
          Real.exp (-a_R * (η - η₀)) * Real.exp (-a_R * (ξ - η)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc |iteratedDeriv j (fun u => meanVel1 tr u ξ) t|
          ≤ (B_R * a_R⁻¹) * Real.exp (-a_R * (ξ - η₀)) := hU_dom_R j hj t ht ξ hξ₀
        _ = ((B_R * a_R⁻¹) * Real.exp (-a_R * (η - η₀))) * Real.exp (-a_R * (ξ - η)) := by
            rw [hexp_split]; ring
  -- Step 3: Evaluate bounds at `r = s ≤ S_` with denominator `A = C₀ + ν * S_`
  let a : ℝ := 4 * b / A
  have ha_pos : 0 < a := by dsimp [a]; positivity
  let B : ℝ := M * Real.exp (-(b * l ^ 2 / A))
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hW_dom_s : ∀ ζ : ℝ, η₀ ≤ ζ →
      |iteratedDeriv ℓ (fun t => hmean c (Cyl.curl (tr.v t)) ζ) s| ≤
        B * Real.exp (-a * (ζ - η₀)) := by
    intro ζ hζ
    have hAs : C₀ + ν * s ≤ A := by dsimp [A]; nlinarith
    have hAs_pos : 0 < C₀ + ν * s := by positivity
    have hexp_mono : Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / (C₀ + ν * s))) ≤
        Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / A)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_left (by positivity) hAs_pos hAs
    have hlin := gaussian_linear_tail_bound hb hA_pos hC' hν hl hη₀ hζ
    calc |iteratedDeriv ℓ (fun t => hmean c (Cyl.curl (tr.v t)) ζ) s|
        ≤ M * Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / (C₀ + ν * s))) :=
          hW_bound s hs ζ ℓ le_rfl
      _ ≤ M * Real.exp (-(b * (max (|ζ| - C' / ν) 0) ^ 2 / A)) :=
          mul_le_mul_of_nonneg_left hexp_mono hM_pos.le
      _ ≤ M * (Real.exp (-(b * l ^ 2 / A)) * Real.exp (-a * (ζ - η₀))) :=
          mul_le_mul_of_nonneg_left (by simpa [a] using hlin) hM_pos.le
      _ = B * Real.exp (-a * (ζ - η₀)) := by dsimp [B]; ring
  have hU_bound_s : ∀ ξ : ℝ, η₀ ≤ ξ →
      |iteratedDeriv ℓ (fun t => meanVel1 tr t ξ) s| ≤
        (B * a⁻¹) * Real.exp (-a * (ξ - η₀)) := by
    intro ξ hξ
    rw [hU_int ℓ le_rfl s hsR ξ hξ]
    have hcont : Continuous (fun ζ : ℝ =>
        iteratedDeriv ℓ (fun t => hmean c (Cyl.curl (tr.v t)) ζ) s) :=
      continuous_slice_iteratedDeriv_1D (G := fun t ζ => hmean c (Cyl.curl (tr.v t)) ζ)
        hW_smooth ℓ hs
    exact (abs_integral_Ioi_exp_reproduce hcont hB_nonneg ha_pos hW_dom_s hξ).2
  have ha_inv : a⁻¹ = A / (4 * b) := by
    dsimp [a]
    rw [inv_div]
  refine ⟨?_, ?_⟩
  · have h1 := hU_bound_s η₀ le_rfl
    rw [sub_self, mul_zero, Real.exp_zero, mul_one, ha_inv] at h1
    calc |iteratedDeriv ℓ (fun r => meanVel1 tr r η₀) s|
        ≤ B * (A / (4 * b)) := h1
      _ = M * (A / (4 * b)) * Real.exp (-(b * l ^ 2 / A)) := by dsimp [B]; ring
  · rw [hS_int_s]
    have hcont_U : Continuous (fun ξ : ℝ =>
        iteratedDeriv ℓ (fun t => meanVel1 tr t ξ) s) :=
      continuous_slice_iteratedDeriv_1D hU_smooth ℓ hs
    have h2 := (abs_integral_Ioi_exp_reproduce hcont_U
      (mul_nonneg hB_nonneg (inv_nonneg.2 ha_pos.le)) ha_pos hU_bound_s le_rfl).2
    rw [sub_self, mul_zero, Real.exp_zero, mul_one, ha_inv] at h2
    calc |∫ ξ in Ioi η₀, iteratedDeriv ℓ (fun t => meanVel1 tr t ξ) s|
        ≤ B * (A / (4 * b)) * (A / (4 * b)) := h2
      _ = M * (A / (4 * b)) ^ 2 * Real.exp (-(b * l ^ 2 / A)) := by dsimp [B]; ring

end PartI_T21

/-! ### 4. Main theorem: `trainZeroModeStreamVelTail_proof` -/

/-- **Zero-mode stream and velocity transverse tail (`PartI:T21/1/2`)**:
proves `TrainZeroModeStreamVelTail` unconditionally for all `ℓ, j : ℕ` from
`hOv : TrainOverlap` and `hVort : TrainVorticityGaussianTail`. -/
theorem trainZeroModeStreamVelTail_proof
    (_hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail) :
    TrainZeroModeStreamVelTail := by
  intro ρ hρ ℓ j
  -- Obtain uniform vorticity Gaussian tail across `k ≤ ℓ` at spatial order 0
  obtain ⟨b₀, C₀₀, C'₀, hb₀, hC₀₀, hC'₀, C₀_p, N₀, ν₀₀, hC₀_p, hν₀₀, hvort₀⟩ :=
    PartI_T21.uniform_vorticity_tail_age₀ hVort hρ ℓ
  -- Obtain vorticity Gaussian tail at `(ℓ, j - 2)` and `(ℓ, j - 1)` for higher spatial orders
  obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁_p, N₁, ν₀₁, hC₁_p, hν₀₁, hvort₁⟩ :=
    hVort ρ hρ ℓ (j - 2)
  obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂_p, N₂, ν₀₂, hC₂_p, hν₀₂, hvort₂⟩ :=
    hVort ρ hρ ℓ (j - 1)
  -- Combine parameters across the three bounds
  let b := min b₀ (min b₁ b₂)
  let C₀ := max C₀₀ (max C₀₁ C₀₂)
  let C' := max C'₀ (max C'₁ C'₂)
  let C_p := max C₀_p (max C₁_p C₂_p)
  let N := max N₀ (max N₁ N₂)
  let ν₀ := min ν₀₀ (min ν₀₁ ν₀₂)
  have hb : 0 < b := lt_min hb₀ (lt_min hb₁ hb₂)
  have hC₀ : 0 < C₀ := lt_max_of_lt_left hC₀₀
  have hC' : 0 < C' := lt_max_of_lt_left hC'₀
  have hC_p : 0 < C_p := lt_max_of_lt_left hC₀_p
  have hν₀ : 0 < ν₀ := lt_min hν₀₀ (lt_min hν₀₁ hν₀₂)
  let D := 1 + (C₀ + ν₀) / (4 * b)
  have hD_pos : 0 < D := by dsimp [D]; positivity
  refine ⟨b, C₀, C', hb, hC₀, hC', C_p * D ^ 2, N + 2, ν₀, by positivity, hν₀, ?_⟩
  intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz c K_g
  have hc : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  rw [PartI_T21.ageJet_train_ψ_sub_fluct_eq hν hc tr htr hs ℓ j z,
      PartI_T21.ageJet_train_v_sub_fluct_eq hc tr hs ℓ j z]
  have hv_le_U := PartI_T21.norm_ageJet_hmean_v_le_meanVel1 hν hc tr ℓ j hs z
  -- Obtain the polynomial envelope comparisons
  obtain ⟨hM_le_P, hMA_le_P, hMA2_le_P⟩ :=
    PartI_T21.polyP_mul_factor_le_polyPS (N := N) hb hC₀ hC_p hν hν_le hc.le hS_
  -- Uniform `k ≤ ℓ` spatial-0 vorticity bound under combined parameters
  have hvort₀_comb : ∀ r : ℝ, 0 < r → ∀ w : Plane, ∀ k ≤ ℓ,
      ‖ageJet k 0 (fun t u => Cyl.curl (tr.v t) u) r w‖ ≤
        polyP C_p N ν c * Real.exp (-(b * (max (|w.2| - C' / ν) 0) ^ 2 / (C₀ + ν * r))) := by
    intro r hr w k hk
    have h0 := hvort₀ ν hν (hν_le.trans (min_le_left _ _)) tr htr r hr w k hk
    refine h0.trans (mul_le_mul
      (PartI_T21.polyP_mono hC₀_p.le (le_max_left _ _) (le_max_left _ _) hν hc.le)
      (PartI_T21.exp_gaussian_mono w hb (min_le_left _ _) hC₀₀ (le_max_left _ _)
        (le_max_left _ _) hν hr.le)
      (Real.exp_nonneg _) (by unfold polyP; positivity))
  -- Apply `iteratedDeriv_meanVel1_meanStream_tail_bound` at `η₀ = |z.2|`
  obtain ⟨hU0_bound, hS0_bound⟩ :=
    PartI_T21.iteratedDeriv_meanVel1_meanStream_tail_bound
      hν hc hb hC₀ hC' hC_p tr htr hl hs hsS hz hvort₀_comb
  have hU0_Kg : ‖ageJet ℓ 0 (fun r w => meanVel1 tr r w.2) s z‖ ≤ K_g := by
    rw [PartI_T21.norm_ageJet_zero_meanVel1_eq_abs hc tr ℓ hs z]
    exact hU0_bound.trans (mul_le_mul_of_nonneg_right hMA_le_P (Real.exp_nonneg _))
  have hS0_Kg : ‖ageJet ℓ 0 (fun r w => meanStream tr r w.2) s z‖ ≤ K_g := by
    rw [PartI_T21.norm_ageJet_zero_meanStream_eq_abs hc tr ℓ hs z]
    exact hS0_bound.trans (mul_le_mul_of_nonneg_right hMA2_le_P (Real.exp_nonneg _))
  -- Helper: Gaussian exponent at `(q, z.2)` and `s ≤ S_` is bounded by `exp(-(b * l ^ 2 / (C₀ + ν * S_)))`
  have hexp_l : ∀ b_i C₀_i C'_i : ℝ, b ≤ b_i → 0 < C₀_i → C₀_i ≤ C₀ → C'_i ≤ C' →
      ∀ q : ℝ, Real.exp (-(b_i * (max (|(q, z.2).2| - C'_i / ν) 0) ^ 2 / (C₀_i + ν * s))) ≤
        Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))) := by
    intro b_i C₀_i C'_i hbi hC₀i_pos hC₀i hC'i q
    have hstep1 := PartI_T21.exp_gaussian_mono (q, z.2) hb hbi hC₀i_pos hC₀i hC'i hν hs.le
    refine hstep1.trans ?_
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have hdl : l ≤ max (|(q, z.2).2| - C' / ν) 0 := by
      refine le_trans ?_ (le_max_left _ _)
      change l ≤ |z.2| - C' / ν
      linarith
    have hsq : l ^ 2 ≤ (max (|(q, z.2).2| - C' / ν) 0) ^ 2 :=
      pow_le_pow_left₀ hl hdl 2
    have hnum : b * l ^ 2 ≤ b * (max (|(q, z.2).2| - C' / ν) 0) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hb.le
    have hden_pos : 0 < C₀ + ν * s := by positivity
    have hden : C₀ + ν * s ≤ C₀ + ν * S_ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsS hν.le)
    exact div_le_div₀ (by positivity) hnum hden_pos hden
  have hKg_nonneg : 0 ≤ K_g := by dsimp [K_g]; unfold polyPS; positivity
  have hW_jm2_Kg : ‖ageJet ℓ (j - 2) (fun r w => hmean c (Cyl.curl (tr.v r)) w.2) s z‖ ≤ K_g := by
    refine PartI_T21.norm_ageJet_hmean_scalar_le (f := fun t w => Cyl.curl (tr.v t) w) hc hKg_nonneg
      (PartI_T20.smR_curl (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)))
      ℓ (j - 2) hs z (fun q _ => ?_)
    have h1 := hvort₁ ν hν (hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))) tr htr s hs (q, z.2)
    have hP1 : polyP C₁_p N₁ ν c ≤ polyPS (C_p * D ^ 2) (N + 2) ν c S_ :=
      (PartI_T21.polyP_mono hC₁_p.le ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _)) hν hc.le).trans hM_le_P
    have hE1 := hexp_l b₁ C₀₁ C'₁ ((min_le_right _ _).trans (min_le_left _ _)) hC₀₁
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)) q
    exact h1.trans (mul_le_mul hP1 hE1 (Real.exp_nonneg _) (by unfold polyPS; positivity))
  have hW_jm1_Kg : ‖ageJet ℓ (j - 1) (fun r w => hmean c (Cyl.curl (tr.v r)) w.2) s z‖ ≤ K_g := by
    refine PartI_T21.norm_ageJet_hmean_scalar_le (f := fun t w => Cyl.curl (tr.v t) w) hc hKg_nonneg
      (PartI_T20.smR_curl (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)))
      ℓ (j - 1) hs z (fun q _ => ?_)
    have h2 := hvort₂ ν hν (hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))) tr htr s hs (q, z.2)
    have hP2 : polyP C₂_p N₂ ν c ≤ polyPS (C_p * D ^ 2) (N + 2) ν c S_ :=
      (PartI_T21.polyP_mono hC₂_p.le ((le_max_right _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _)) hν hc.le).trans hM_le_P
    have hE2 := hexp_l b₂ C₀₂ C'₂ ((min_le_right _ _).trans (min_le_right _ _)) hC₀₂
      ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) q
    exact h2.trans (mul_le_mul hP2 hE2 (Real.exp_nonneg _) (by unfold polyPS; positivity))
  -- Conclude for all `j : ℕ` by cases `j = 0`, `j = 1`, `j = m + 2`
  rcases j with _ | _ | m
  · exact ⟨hS0_Kg, hv_le_U.trans hU0_Kg⟩
  · have hS1_Kg : ‖ageJet ℓ 1 (fun r w => meanStream tr r w.2) s z‖ ≤ K_g :=
      (PartI_T21.norm_ageJet_meanStream_succ_le hν hc tr htr ℓ 0 hs z).trans hU0_Kg
    have hU1_Kg : ‖ageJet ℓ 1 (fun r w => meanVel1 tr r w.2) s z‖ ≤ K_g :=
      (PartI_T21.norm_ageJet_meanVel1_succ_le hc tr ℓ 0 hs z).trans hW_jm1_Kg
    exact ⟨hS1_Kg, hv_le_U.trans hU1_Kg⟩
  · have hSm2_Kg : ‖ageJet ℓ (m + 2) (fun r w => meanStream tr r w.2) s z‖ ≤ K_g :=
      ((PartI_T21.norm_ageJet_meanStream_succ_le hν hc tr htr ℓ (m + 1) hs z).trans
        (PartI_T21.norm_ageJet_meanVel1_succ_le hc tr ℓ m hs z)).trans hW_jm2_Kg
    have hUm2_Kg : ‖ageJet ℓ (m + 2) (fun r w => meanVel1 tr r w.2) s z‖ ≤ K_g :=
      (PartI_T21.norm_ageJet_meanVel1_succ_le hc tr ℓ (m + 1) hs z).trans hW_jm1_Kg
    exact ⟨hSm2_Kg, hv_le_U.trans hUm2_Kg⟩

end UnforcedLeray.Short.PartI
