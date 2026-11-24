import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.VMeas

/-!
# Mean part helper: differentiation of the `sepVmu0` integral under the sign (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mpVF_zero (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ((ℝ × ℝ) × ℝ))
    (h : G p.2.1 p.2.2 = 0) (x : Space) (i : Fin 3) : mpVF μ G p x i = 0 := by
  simp [mpVF, h]

theorem mpVF'_zero (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ((ℝ × ℝ) × ℝ))
    (h : G p.2.1 p.2.2 = 0) (x : Space) (i : Fin 3) : mpVF' μ G p x i = 0 := by
  ext v
  simp [mpVF', h]

/-- Pointwise bounds on the integrand and its derivative, on the ball of radius `(ρi-ρo)/2`. -/
theorem mp_V_pointwise (hK : SepKernelBounds) :
    ∃ b0 b1 : ℝ, 0 ≤ b0 ∧ 0 ≤ b1 ∧ ∀ (μ : ℂ), -(1 / 4) < μ.re → ∀ (ρo ρi : ℝ), 0 ≤ ρo → ρo < ρi →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ), (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
      ∀ (xo x : Space), ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ‖xo - x‖ < (ρi - ρo) / 2 →
      ∀ (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ i : Fin 3,
        ‖mpVF μ G p x i‖ ≤ b0 * ((ρi - ρo) / 2) ^ (-4 : ℝ) * tensorNorm (G p.2.1 p.2.2) ∧
        ‖mpVF' μ G p x i‖ ≤ b1 * ((ρi - ρo) / 2) ^ (-5 : ℝ) * tensorNorm (G p.2.1 p.2.2) := by
  obtain ⟨C0, hC0⟩ := hK 0
  obtain ⟨C1, hC1⟩ := hK 1
  refine ⟨18 * max C0 0, 18 * max C1 0, by positivity, by positivity, ?_⟩
  intro μ hμ ρo ρi hρo hρ G hGs xo x hxo hx p hp i
  set D1 := (ρi - ρo) / 2 with hD1
  have hD1pos : 0 < D1 := by rw [hD1]; linarith
  by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
  · -- on the support: the kernel stays at distance `D1`
    have hgap := mp_gap ρo ρi xo x hxo p.1 hp p.2 hw
    have hnorm : D1 ≤ ‖x - p.1 • mpV3 p.2‖ := by
      refine le_trans ?_ (rho_le_norm _)
      rw [hD1]; linarith
    have hne : x - p.1 • mpV3 p.2 ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hnorm; linarith
    have hw1 := mp_norm_cpow_le μ hμ p.1 hp
    constructor
    · -- value
      have hb : ∀ j k : Fin 3, ‖((fderiv ℝ (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2)
          (coordinateVector k) : ℝ) : ℂ) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)‖ ≤
          (max C0 0 * D1 ^ (-4 : ℝ)) * tensorNorm (G p.2.1 p.2.2) := by
        intro j k
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        have h1 : |fderiv ℝ (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2) (coordinateVector k)| ≤
            ‖fderiv ℝ (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2)‖ * 1 := by
          have := (fderiv ℝ (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2)).le_opNorm (coordinateVector k)
          rw [mp_norm_e] at this
          simpa using this
        have h2 : ‖fderiv ℝ (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2)‖ ≤ max C0 0 * D1 ^ (-4 : ℝ) := by
          rw [← norm_iteratedFDeriv_one]
          refine ((hC0 _ hne i j).2.1).trans ?_
          have h3 : ‖x - p.1 • mpV3 p.2‖ ^ (-4 - ((0 : ℕ) : ℝ)) ≤ D1 ^ (-4 : ℝ) := by
            have := Real.rpow_le_rpow_of_nonpos hD1pos hnorm (by norm_num : (-4 - ((0 : ℕ) : ℝ)) ≤ 0)
            simpa using this
          calc C0 * ‖x - p.1 • mpV3 p.2‖ ^ (-4 - ((0 : ℕ) : ℝ)) ≤ max C0 0 * ‖x - p.1 • mpV3 p.2‖ ^ (-4 - ((0 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
            _ ≤ _ := mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
        exact mul_le_mul (h1.trans (by simpa using h2)) (mp_entry_le _ j k) (abs_nonneg _)
          (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hD1pos.le _))
      have hs := mp_sum9 _ _ hb
      unfold mpVF
      rw [norm_mul, norm_mul]
      have hn2 : ‖(-2 : ℂ)‖ = 2 := by simp
      rw [hn2]
      calc 2 * (‖(p.1 : ℂ) ^ (2 * μ + 2)‖ * ‖∑ j : Fin 3, ∑ k : Fin 3, _‖)
          ≤ 2 * (1 * (9 * ((max C0 0 * D1 ^ (-4 : ℝ)) * tensorNorm (G p.2.1 p.2.2)))) := by
            gcongr
        _ = _ := by ring
    · -- derivative
      have hb : ∀ j : Fin 3, ‖fderiv ℝ (fderiv ℝ (fun x => heatLerayK0 i j x)) (x - p.1 • mpV3 p.2)‖ ≤
          max C1 0 * D1 ^ (-5 : ℝ) := by
        intro j
        have e : ‖fderiv ℝ (fderiv ℝ (fun x => heatLerayK0 i j x)) (x - p.1 • mpV3 p.2)‖ =
            ‖iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2)‖ := by
          rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
        rw [e]
        refine ((hC1 _ hne i j).2.1).trans ?_
        have h3 : ‖x - p.1 • mpV3 p.2‖ ^ (-4 - ((1 : ℕ) : ℝ)) ≤ D1 ^ (-5 : ℝ) := by
          have := Real.rpow_le_rpow_of_nonpos hD1pos hnorm (by norm_num : (-4 - ((1 : ℕ) : ℝ)) ≤ 0)
          norm_num at this ⊢
          exact this
        calc C1 * ‖x - p.1 • mpV3 p.2‖ ^ (-4 - ((1 : ℕ) : ℝ)) ≤ max C1 0 * ‖x - p.1 • mpV3 p.2‖ ^ (-4 - ((1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
          _ ≤ _ := mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
      have hs := mp_clm_bound (fun j k => G p.2.1 p.2.2 j k)
        (fun j => fderiv ℝ (fderiv ℝ (fun x => heatLerayK0 i j x)) (x - p.1 • mpV3 p.2))
        (max C1 0 * D1 ^ (-5 : ℝ)) (tensorNorm (G p.2.1 p.2.2)) (fun j k => mp_entry_le _ j k) hb
      unfold mpVF'
      set A : Space →L[ℝ] ℂ := ∑ j : Fin 3, ∑ k : Fin 3, ((G p.2.1 p.2.2 j k : ℝ) : ℂ) •
        (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp
          (fderiv ℝ (fderiv ℝ (fun x => heatLerayK0 i j x)) (x - p.1 • mpV3 p.2)))) with hA
      have hn2 : ‖(-2 : ℂ)‖ = 2 := by simp
      have e1 := norm_smul_le (-2 : ℂ) (((p.1 : ℂ) ^ (2 * μ + 2)) • A)
      have e2 := norm_smul_le ((p.1 : ℂ) ^ (2 * μ + 2)) A
      rw [hn2] at e1
      calc ‖(-2 : ℂ) • (((p.1 : ℂ) ^ (2 * μ + 2)) • A)‖
          ≤ 2 * ‖((p.1 : ℂ) ^ (2 * μ + 2)) • A‖ := e1
        _ ≤ 2 * (‖(p.1 : ℂ) ^ (2 * μ + 2)‖ * ‖A‖) := by gcongr
        _ ≤ 2 * (1 * (9 * tensorNorm (G p.2.1 p.2.2) * (max C1 0 * D1 ^ (-5 : ℝ)))) := by
            gcongr
        _ = _ := by ring
  · push_neg at hw
    have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw
    rw [mpVF_zero μ G p h0, mpVF'_zero μ G p h0]
    simp only [norm_zero]
    have : 0 ≤ tensorNorm (G p.2.1 p.2.2) := Real.sqrt_nonneg _
    constructor <;> positivity

end UnforcedLeray.Short.IIIa

end
