import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2

/-!
# Decomposition of `TrainMeanWtdMixed` (SP 456-457 at bounded ages; threshold after the orders, SP 247-258)

Source: `the November 2 reference manuscript`.
At bounded ages the weighted mean-stream bound follows from the transverse tails of `ψ`
(`sct:transverse`, SP 460-467; "These formulas prove the mean tails and polynomial weighted bounds
for all fields at every age", SP 509-511) by averaging in `q` (`S = \bar ψ`), so no Duhamel
analysis is needed: `∂_s^ℓ ∂_η^b S = \overline{∂_s^ℓ ∂_η^b ψ}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology MeasureTheory

/-- **Weighted jets of the train stream `ψ`, bounded ages** (SP 460-467 `sct:transverse` for
`|η| ≥ C'/ν+2` together with the bounded jets on the transverse band `|η| ≤ C'/ν+2`, `0 < s ≤ S`).
The threshold `ν₀` is fixed after the derivative orders `ℓ, j` and before the weight `m` and the
age bound `S` (SP 247-258; as in `PartI.TrainTransverseTails`, `StatementsTrain.lean:284`, whose
`ν₀` depends on `ρ, ℓ, j` and whose tails are exponential, so every weight is absorbed at fixed
`ν`): `(1+|η|)^m ‖∂_s^ℓ D^j ψ(s, q, η)‖ ≤ C` for `0 < s ≤ S`, all `(q, η)`. -/
def PsiJetWtd : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = Short.PartI.trainPeriod ρ ν →
    ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
      ∀ (m : ℕ) (S : ℝ), ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ S → ∀ z : ℝ × ℝ,
        (1 + |z.2|) ^ m * ‖Short.PartI.ageJet ℓ j tr.ψ s z‖ ≤ C

/-- **Mean of the jets** (`S = \bar ψ`, differentiation under the horizontal mean over the window
`(-c/2, c/2]`; `Short.PartI.HmeanDerivS`, `Short/PartI/Sub/T01.lean:81`): for `s > 0`,
`∂_η^b ∂_s^ℓ S(s, η) = c⁻¹ ∫_{-c/2}^{c/2} (∂_s^ℓ D^b ψ)(s, q, η)[e₂, …, e₂] dq`. -/
def MeanJetFormula : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
    ∀ (b ℓ : ℕ) (s : ℝ), 0 < s → ∀ η : ℝ,
      iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => Short.PartI.meanStream tr r e) s) η =
        c⁻¹ * ∫ q in Ioc (-c / 2) (c / 2),
          (Short.PartI.ageJet ℓ b tr.ψ s (q, η)) (fun _ => ((0 : ℝ), (1 : ℝ)))

theorem trainMeanWtdMixed_of (h1 : PsiJetWtd) (h2 : MeanJetFormula) : TrainMeanWtdMixed := by
  intro ρ hρ b ℓ
  obtain ⟨ν₀, hν₀, h⟩ := h1 ρ hρ ℓ b
  refine ⟨ν₀, hν₀, fun ν c hν hle hc tr htr m S => ?_⟩
  have hc0 : 0 < c := by subst hc; exact Real.rpow_pos_of_pos hν _
  obtain ⟨C, hC⟩ := h ν c hν hle hc tr htr m S
  refine ⟨max C 0, fun s hs hsS η => ?_⟩
  rw [h2 ν c hν hc0 tr htr b ℓ s hs η]
  have hw : 0 ≤ (1 + |η|) ^ m := by positivity
  have hmeas : (0 : ℝ) ≤ c := hc0.le
  have hpt : ∀ q : ℝ, ‖(Short.PartI.ageJet ℓ b tr.ψ s (q, η)) (fun _ => ((0 : ℝ), (1 : ℝ)))‖
      * (1 + |η|) ^ m ≤ C := by
    intro q
    have h0 := hC s hs hsS (q, η)
    have hn : ‖(Short.PartI.ageJet ℓ b tr.ψ s (q, η)) (fun _ => ((0 : ℝ), (1 : ℝ)))‖ ≤
        ‖Short.PartI.ageJet ℓ b tr.ψ s (q, η)‖ := by
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have : ∏ _i : Fin b, ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
      rw [this, mul_one]
    calc _ ≤ ‖Short.PartI.ageJet ℓ b tr.ψ s (q, η)‖ * (1 + |η|) ^ m :=
          mul_le_mul_of_nonneg_right hn hw
      _ = (1 + |(q, η).2|) ^ m * ‖Short.PartI.ageJet ℓ b tr.ψ s (q, η)‖ := by
          simp only; ring
      _ ≤ C := h0
  set g : ℝ → ℝ := fun q => (Short.PartI.ageJet ℓ b tr.ψ s (q, η)) (fun _ => ((0 : ℝ), (1 : ℝ)))
  by_cases hint : IntegrableOn g (Ioc (-c / 2) (c / 2))
  · have hnorm : ‖∫ q in Ioc (-c / 2) (c / 2), g q‖ ≤ ∫ q in Ioc (-c / 2) (c / 2), C * ((1 + |η|) ^ m)⁻¹ := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ?_ (Eventually.of_forall fun q => ?_)
      · exact integrableOn_const (by simp [Real.volume_Ioc])
      · have := hpt q
        have hpos : 0 < (1 + |η|) ^ m := by positivity
        rw [le_mul_inv_iff₀ hpos]; exact this
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith)] at hnorm
    simp only [smul_eq_mul] at hnorm
    have hpos : 0 < (1 + |η|) ^ m := by positivity
    rw [norm_mul, norm_inv, Real.norm_of_nonneg hc0.le]
    have h3 : ‖∫ q in Ioc (-c / 2) (c / 2), g q‖ ≤ c * (C * ((1 + |η|) ^ m)⁻¹) := by
      have : c / 2 - -c / 2 = c := by ring
      rwa [this] at hnorm
    calc (1 + |η|) ^ m * (c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), g q‖)
        ≤ (1 + |η|) ^ m * (c⁻¹ * (c * (C * ((1 + |η|) ^ m)⁻¹))) := by gcongr
      _ = C := by field_simp
      _ ≤ max C 0 := le_max_left _ _
  · rw [integral_undef hint]; simp
