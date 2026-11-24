import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1.EarlyJet2
import UnforcedLeray.Short.PartIIa.Tasks.R02LateTable

/-!
# Sub-decomposition of `PartIII-b:C/ward/12/3/2/2/1/2/1/2`: `ResProfileLateHeatDecomp2`

Source of record: `the November 2 reference manuscript`, lines 1243-1285,
1310-1325, 2548-2551 (the late-age `s ≥ 1` residual table and finite-order heat decomposition
of the lifted residual).

## Mathematical structure and decomposition

On `{m | 0 < m.1}` (`x = chartSwap m ∈ ageDomain`), `resChartProfile p m` is the five-block
polynomial meridional profile (`EarlyJet2Sub.resChartProfile_eq_resPolyMerid`):
- Radial (`meridE0`): `ringEps p.R * coeffA₁ + ringEps p.R ^ 2 * coeffB₁`
- Axial (`meridE1`): `ringEps p.R * coeffA₂ + ringEps p.R ^ 2 * coeffB₂ + ringEps p.R ^ 3 * coeffB₃`

Splitting the stream `ψ = S + ψ̃` (`psiFam = meanFam + fluctFam`) decomposes each coefficient into
its pure `q`-independent mean-stream part (`meanA1`, `meanB1`, `Jet.B2.meanB2`, `meanB3`) and its
fluctuation/pressure/`A₂` part (`fluctA1`, `fluctB1`, `Jet.A2.coefA2`, `Jet.B2.fluctB2`, `fluctB3`):
1. **Fluctuation, pressure, and `A₂` cancellation (proved unconditionally in this file)**:
   All five families `Jet.A2.coefA2`, `Jet.B2.fluctB2`, `fluctB1`, `fluctB3`, `fluctA1` belong to
   `Jet.JE n` for every `n : ℕ` (`coefA2_je`, `fluctB2_je`, `fluctB1_je`, `fluctB3_je`,
   `fluctA1_je`, using the unconditional Part I theorems assembled in `R02LateTable`). By
   `Jet.A2.ageJE_of`, all mixed directional partials `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] ·))`
   (`ℓ, a, b ≤ 2`) belong to `Jet.JE 0` at a single viscosity threshold `ν₀ > 0` independent of `N`,
   and `exp_neg_le_rpow_neg` absorbs `e^{-κ ν s / c²}` into `B_N s^{-N}` for every `N : ℕ` with
   `F_heat = 0` (`je_late_iteratedFDeriv_bound`).
2. **Reduction of `q`-independent remainder partials to `K^k ∂_η^j` jets (proved in this file)**:
   `wtd_partials_of_K_eta_jets` proves that for any smooth `q`-independent profile `f` on
   `ageDomain`, the mixed partials `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))` (`ℓ, a, b ≤ 2`)
   with weight `(1 + η² / s)²` are bounded by `9 B s^{-N}` as soon as the `K^k ∂_η^j` jets
   `ageOperator^[k] (partialEta^[j] f)` (`k ≤ 2, j ≤ 4`) with weights `(1 + η² / s)^m` (`m ≤ 4`)
   are bounded by `B s^{-N}`.
3. **Four mean-stream block heat-split leaves (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/1`..`/4`)**:
   - `MeanBlockB1LateHeatSplit2` (`12/1`): linear radial mean block `ringEps p.R ^ 2 * meanB1`
   - `MeanBlockB3LateHeatSplit2` (`12/2`): linear axial mean block `ringEps p.R ^ 3 * meanB3`
   - `MeanBlockA1LateHeatSplit2` (`12/3`): quadratic radial mean block `ringEps p.R * meanA1`
   - `MeanBlockB2LateHeatSplit2` (`12/4`): quadratic axial mean block `ringEps p.R ^ 2 * Jet.B2.meanB2`
   The assembly theorem `resProfileLateHeatDecomp2_of_blocks` combines these four leaves with the
   unconditional fluctuation/pressure/`A₂` bounds to yield `ResProfileLateHeatDecomp2`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal BigOperators
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Short.IIb (trainStream trainPressure rawResidualC
  isExactPlanarTrain_params_rpow)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FarDecaySub EarlyJet2Sub

namespace LateHeatDecomp2Sub

/-! ### Step 1: Assembly of `LateIngredients` and `RingLateTable` from Part I -/

/-- All seven fields of `PartIIa.LateIngredients` follow from `TrainFluctuationDecay` and
`TrainMeanExpansion` (using the unconditionally proved `trainStreamSmooth` and
`trainMeanEquations_proof`). -/
theorem lateIngredients_of_partI (hF : TrainFluctuationDecay) (hM : TrainMeanExpansion) :
    LateIngredients where
  smooth := lateProfileSmooth_of trainStreamSmooth
  fluct := lateFluctuationProfile_of hF (lateProfileSmooth_of trainStreamSmooth)
  remainder :=
    lateMeanRemainder_of hM trainMeanEquations_proof (lateProfileSmooth_of trainStreamSmooth)
  coeff := lateMeanCoeff_of hF trainMeanEquations_proof
  heat := lateHeatProfile
  stress := lateMeanStress_of hF trainMeanEquations_proof (lateProfileSmooth_of trainStreamSmooth)
  comm := profileCommutators

/-- Unconditional `PartIIa.LateIngredients` assembled from the proved Part I theorems. -/
theorem lateIngredients : LateIngredients := by
  have hHN := overlap_highnorm_uniform
  have hFD := overlap_fluctuation_decay hHN
  have hMP := overlap_mean_primitive
  have hMD := overlap_mean_decay hHN hFD hMP
  have hOv := trainOverlap_proof hFD hMD
  have hVort := train_vorticity_gaussian_tail hOv
  have hTails := train_stream_velocity_pressure_tails hOv hVort
  have hFluct := trainFluctuationDecay_proof hTails hFD hOv
  have hMean := trainMeanExpansion_proof hTails hFluct hMP
  exact lateIngredients_of_partI hFluct hMean

/-- The full five-block late residual table `PartIIa.RingLateTable` follows from
`TrainFluctuationDecay` and `TrainMeanExpansion`. -/
theorem ringLateTable_of_partI (hF : TrainFluctuationDecay) (hM : TrainMeanExpansion) :
    RingLateTable := by
  have hI := lateIngredients_of_partI hF hM
  exact ringLateTable_of (ringLateA1_of hI) (ringLateB1_of hI) (ringLateB2_of hI)
    (ringLateB3_of hI) (ringLateA2_of hI trainMeanEquations_proof)

/-! ### Step 2: Exponential absorption and `l = 0` late decay of `resChartProfile` -/

/-- For `a > 0`, `s ≥ 1`, and any `N : ℕ`, `e^{-a s} ≤ (N! / a^N) s^{-N}`. -/
theorem exp_neg_le_rpow_neg {a s : ℝ} (ha : 0 < a) (hs : 1 ≤ s) (N : ℕ) :
    Real.exp (-(a * s)) ≤ ((N.factorial : ℝ) / a ^ N) * s ^ (-(N : ℝ)) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have has : 0 ≤ a * s := mul_nonneg ha.le hs0.le
  have hpow := Real.pow_div_factorial_le_exp (a * s) has N
  rw [mul_pow] at hpow
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have haN : 0 < a ^ N := pow_pos ha N
  have hsN_id : s ^ N * s ^ (-(N : ℝ)) = 1 := by
    rw [← Real.rpow_natCast s N, ← Real.rpow_add hs0, add_neg_cancel, Real.rpow_zero]
  have hexp_id : Real.exp (-(a * s)) * Real.exp (a * s) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : Real.exp (-(a * s)) * (a ^ N * s ^ N / (N.factorial : ℝ)) ≤ 1 := by
    calc Real.exp (-(a * s)) * (a ^ N * s ^ N / (N.factorial : ℝ))
        ≤ Real.exp (-(a * s)) * Real.exp (a * s) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = 1 := hexp_id
  have h2 := mul_le_mul_of_nonneg_right h1
    (mul_nonneg (div_nonneg hfac.le haN.le) (Real.rpow_nonneg hs0.le (-(N : ℝ))))
  have hlhs :
      Real.exp (-(a * s)) * (a ^ N * s ^ N / (N.factorial : ℝ)) *
        ((N.factorial : ℝ) / a ^ N * s ^ (-(N : ℝ))) = Real.exp (-(a * s)) := by
    have hcancel :
        (a ^ N / a ^ N) * ((N.factorial : ℝ) / (N.factorial : ℝ)) *
          (s ^ N * s ^ (-(N : ℝ))) = 1 := by
      rw [div_self haN.ne', div_self hfac.ne', hsN_id, mul_one, mul_one]
    calc Real.exp (-(a * s)) * (a ^ N * s ^ N / (N.factorial : ℝ)) *
          ((N.factorial : ℝ) / a ^ N * s ^ (-(N : ℝ)))
        = Real.exp (-(a * s)) *
            ((a ^ N / a ^ N) * ((N.factorial : ℝ) / (N.factorial : ℝ)) *
              (s ^ N * s ^ (-(N : ℝ)))) := by ring
      _ = Real.exp (-(a * s)) * 1 := by rw [hcancel]
      _ = Real.exp (-(a * s)) := mul_one _
  rw [hlhs, one_mul] at h2
  exact h2

/-- Radial and axial unit basis vectors of `Axi.Merid = EuclideanSpace ℝ (Fin 2)`. -/
def meridE0 : Axi.Merid := !₂[(1 : ℝ), 0]
def meridE1 : Axi.Merid := !₂[(0 : ℝ), 1]

theorem merid_eq_smul_add_smul (v : Axi.Merid) :
    v = v 0 • meridE0 + v 1 • meridE1 := by
  ext i
  fin_cases i <;> simp [meridE0, meridE1]

/-- Norm of a meridional vector `v : Axi.Merid` (`EuclideanSpace ℝ (Fin 2)`) is bounded by
`|v 0| + |v 1|`. -/
theorem merid_norm_le_abs_add_abs (v : Axi.Merid) : ‖v‖ ≤ |v 0| + |v 1| := by
  have h : v = v 0 • meridE0 + v 1 • meridE1 := merid_eq_smul_add_smul v
  calc ‖v‖ = ‖v 0 • meridE0 + v 1 • meridE1‖ := by rw [← h]
    _ ≤ ‖v 0 • meridE0‖ + ‖v 1 • meridE1‖ := norm_add_le _ _
    _ = |v 0| * ‖meridE0‖ + |v 1| * ‖meridE1‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = |v 0| + |v 1| := by
        rw [meridE0, meridE1, norm_merid_e0, norm_merid_e1, mul_one, mul_one]

/-- From `PartIIa.RingLateTable`, the order-`0` jet of `resChartProfile p` satisfies the
normalized-weight late decay `(1 + η² / s)^k ‖D⁰(resChartProfile p)(m)‖ ≤ C s^{-3/2}` for all
`m` with `1 ≤ m.1`. -/
theorem resChartProfile_late_norm_zero_wtd (hLate : RingLateTable) (k : ℕ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℝ × (ℝ × ℝ), 1 ≤ m.1 →
          (1 + m.2.2 ^ 2 / m.1) ^ k * ‖iteratedFDeriv ℝ 0 (resChartProfile p) m‖ ≤
            C * m.1 ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨ν₀, hν₀, C₀, d₀, κ, hκ, H⟩ := hLate 2 k (by norm_num)
  refine ⟨ν₀, hν₀, fun p htr hν hc hR _ => ?_⟩
  have hmem : p.ν ∈ Ioo 0 ν₀ := ⟨p.ν_pos, hν⟩
  have hexact : IsExactPlanarTrain p.ν (p.ν ^ (-(2 : ℝ))) (trainStream p) (trainPressure p) :=
    isExactPlanarTrain_params_rpow p htr hc
  have hc_rpow : p.c = p.ν ^ (-(2 : ℝ)) := by
    rw [hc, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg p.ν_pos.le, Real.rpow_natCast]
  have htab := H p.ν hmem (trainStream p) (trainPressure p) hexact
  rw [← hc_rpow] at htab
  obtain ⟨hA1, hB1, hB2, hB3, hA2⟩ := htab
  set B : ℝ := max (polyConst C₀ d₀ p.ν p.c) 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hBL : polyConst C₀ d₀ p.ν p.c ≤ B := le_max_left _ _
  have hA1_0 : WtdBound k (coeffA₁ p.ν (trainStream p) (trainPressure p)) 2 B :=
    WtdBound.mono' hBL hA1.1
  have hB1_0 : WtdBound k (coeffB₁ p.ν (trainStream p)) 2 B :=
    WtdBound.mono' hBL hB1.1
  have hB2_0 : WtdBound k (coeffB₂ p.ν (trainStream p)) (3 / 2) B :=
    WtdBound.mono' hBL hB2.1
  have hB3_0 : WtdBound k (coeffB₃ p.ν (trainStream p)) (3 / 2) B :=
    WtdBound.mono' hBL hB3.1
  have hA2_0 : ExpBound κ p.ν p.c k (coeffA₂ p.ν (trainStream p)) B :=
    ExpBound.mono' p.ν_pos p.c_pos le_rfl hBL hA2.1
  set a : ℝ := κ * p.ν / p.c ^ 2
  have ha : 0 < a := by
    unfold a
    have hν : 0 < p.ν := p.ν_pos
    have hc0 : 0 < p.c := p.c_pos
    positivity
  set C_exp : ℝ := ((2 : ℕ).factorial : ℝ) / a ^ 2
  have hCexp0 : 0 ≤ C_exp := by
    unfold C_exp
    positivity
  refine ⟨4 * B + B * C_exp, by positivity, fun m hm => ?_⟩
  rw [norm_iteratedFDeriv_zero]
  have hW0 : 0 ≤ (1 + m.2.2 ^ 2 / m.1) ^ k := by positivity
  have hrad := resChartProfile_late_radial_wtd p htr hR hA1_0 hB1_0 hm
  have hax := resChartProfile_late_axial_wtd p htr hR hA2_0 hB2_0 hB3_0 hm
  have hs2_le : m.1 ^ (-2 : ℝ) ≤ m.1 ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have hexp_eq : -(κ * p.ν * m.1 / p.c ^ 2) = -(a * m.1) := by
    unfold a
    ring
  have hexp_le : Real.exp (-(κ * p.ν * m.1 / p.c ^ 2)) ≤ C_exp * m.1 ^ (-(3 / 2 : ℝ)) := by
    rw [hexp_eq]
    have h1 := exp_neg_le_rpow_neg ha hm 2
    have h2 : (-((2 : ℕ) : ℝ)) = (-2 : ℝ) := by norm_num
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hs2_le hCexp0)
  have hmer := merid_norm_le_abs_add_abs (resChartProfile p m)
  calc (1 + m.2.2 ^ 2 / m.1) ^ k * ‖resChartProfile p m‖
      ≤ (1 + m.2.2 ^ 2 / m.1) ^ k * (|resChartProfile p m 0| + |resChartProfile p m 1|) :=
        mul_le_mul_of_nonneg_left hmer hW0
    _ = (1 + m.2.2 ^ 2 / m.1) ^ k * |resChartProfile p m 0| +
          (1 + m.2.2 ^ 2 / m.1) ^ k * |resChartProfile p m 1| := by ring
    _ ≤ 2 * B * m.1 ^ (-2 : ℝ) +
          (B * Real.exp (-(κ * p.ν * m.1 / p.c ^ 2)) + 2 * B * m.1 ^ (-(3 / 2 : ℝ))) :=
        add_le_add hrad hax
    _ ≤ 2 * B * m.1 ^ (-(3 / 2 : ℝ)) +
          (B * (C_exp * m.1 ^ (-(3 / 2 : ℝ))) + 2 * B * m.1 ^ (-(3 / 2 : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left hs2_le (by positivity))
          (add_le_add (mul_le_mul_of_nonneg_left hexp_le hB0) le_rfl)
    _ = (4 * B + B * C_exp) * m.1 ^ (-(3 / 2 : ℝ)) := by ring

/-- Order-`0` late weighted decay of `resChartProfile p` from `TrainFluctuationDecay` and
`TrainMeanExpansion`. -/
theorem resChartProfile_late_norm_zero_wtd_of_partI
    (hF : TrainFluctuationDecay) (hM : TrainMeanExpansion) (k : ℕ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℝ × (ℝ × ℝ), 1 ≤ m.1 →
          (1 + m.2.2 ^ 2 / m.1) ^ k * ‖iteratedFDeriv ℝ 0 (resChartProfile p) m‖ ≤
            C * m.1 ^ (-(3 / 2 : ℝ)) :=
  resChartProfile_late_norm_zero_wtd (ringLateTable_of_partI hF hM) k

/-- Unconditional order-`0` late weighted decay of `resChartProfile p`. -/
theorem resChartProfile_late_norm_zero_wtd_uncond (k : ℕ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℝ × (ℝ × ℝ), 1 ≤ m.1 →
          (1 + m.2.2 ^ 2 / m.1) ^ k * ‖iteratedFDeriv ℝ 0 (resChartProfile p) m‖ ≤
            C * m.1 ^ (-(3 / 2 : ℝ)) :=
  resChartProfile_late_norm_zero_wtd ringLateTable k

/-! ### Step 3: Converting directional partials of a remainder profile into full second jets -/

/-- If a meridional chart profile `r_rem` has radial and axial profile components `f₀, f₁` on
`ageDomain` whose mixed directional partials `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f_i))`
(`ℓ, a, b ≤ 2`) satisfy the normalized-weight late bound `B s^{-N}` on `1 ≤ s`, then `r_rem` is
smooth on `{m | 0 < m.1}` and its full Fréchet jets of order `l ≤ 2` satisfy
`(1 + η² / s)² ‖D^l r_rem(m)‖ ≤ 18 B s^{-N}` for all `1 ≤ m.1`. -/
theorem wtd_late_jet2_of_merid_partials
    {r_rem : ℝ × (ℝ × ℝ) → Axi.Merid} {f₀ f₁ : ProfilePoint → ℝ}
    (hf₀ : ContDiffOn ℝ ∞ f₀ ageDomain) (hf₁ : ContDiffOn ℝ ∞ f₁ ageDomain)
    (h_eq : ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 →
      r_rem m = f₀ (chartSwap m) • meridE0 + f₁ (chartSwap m) • meridE1)
    {B : ℝ} (hB0 : 0 ≤ B) {N : ℕ}
    (hpart₀ : ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
      (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
        |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f₀))) x| ≤ B * x.2.2 ^ (-(N : ℝ)))
    (hpart₁ : ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
      (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
        |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f₁))) x| ≤ B * x.2.2 ^ (-(N : ℝ))) :
    ContDiffOn ℝ ∞ r_rem {m : ℝ × (ℝ × ℝ) | 0 < m.1} ∧
      ∀ m : ℝ × (ℝ × ℝ), 1 ≤ m.1 → ∀ l ≤ 2,
        (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l r_rem m‖ ≤
          18 * B * m.1 ^ (-(N : ℝ)) := by
  let F_prof : ProfilePoint → Axi.Merid := fun x => f₀ x • meridE0 + f₁ x • meridE1
  have hF_prof : ContDiffOn ℝ ∞ F_prof ageDomain :=
    (hf₀.smul contDiffOn_const).add (hf₁.smul contDiffOn_const)
  have hopen : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} := isOpen_lt continuous_const continuous_fst
  have hrem_sm : ContDiffOn ℝ ∞ r_rem {m : ℝ × (ℝ × ℝ) | 0 < m.1} := by
    refine (hF_prof.comp chartSwapLIE.contDiff.contDiffOn (fun m hm => hm)).congr ?_
    intro m hm
    exact h_eq m hm
  refine ⟨hrem_sm, fun m hm l hl => ?_⟩
  have hm0 : 0 < m.1 := lt_of_lt_of_le one_pos hm
  set x : ProfilePoint := chartSwap m
  have hx : x ∈ ageDomain := hm0
  have hx1 : 1 ≤ x.2.2 := hm
  set W : ℝ := (1 + m.2.2 ^ 2 / m.1) ^ 2
  have hW0 : 0 ≤ W := by unfold W; positivity
  have hBN0 : 0 ≤ B * m.1 ^ (-(N : ℝ)) :=
    mul_nonneg hB0 (Real.rpow_nonneg hm0.le _)
  have hjet₀ : W * ‖iteratedFDeriv ℝ l f₀ x‖ ≤ 9 * (B * m.1 ^ (-(N : ℝ))) :=
    wtd_norm_iteratedFDeriv_le_of_partials hf₀ hx hW0 hBN0 (hpart₀ x hx1) hl
  have hjet₁ : W * ‖iteratedFDeriv ℝ l f₁ x‖ ≤ 9 * (B * m.1 ^ (-(N : ℝ))) :=
    wtd_norm_iteratedFDeriv_le_of_partials hf₁ hx hW0 hBN0 (hpart₁ x hx1) hl
  have hev : r_rem =ᶠ[𝓝 m] fun w => F_prof (chartSwap w) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hm0) (fun w hw => h_eq w hw)
  have hnorm_comp : ‖iteratedFDeriv ℝ l r_rem m‖ = ‖iteratedFDeriv ℝ l F_prof x‖ := by
    rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds, norm_iteratedFDeriv_comp_chartSwap F_prof m l]
  rw [hnorm_comp]
  have hnhds : ageDomain ∈ 𝓝 x := FarDecaySub.isOpen_ageDomain.mem_nhds hx
  have cf₀ : ContDiffAt ℝ ∞ f₀ x := hf₀.contDiffAt hnhds
  have cf₁ : ContDiffAt ℝ ∞ f₁ x := hf₁.contDiffAt hnhds
  have csm₀ : ContDiffAt ℝ l (fun y => f₀ y • meridE0) x :=
    (cf₀.smul contDiffAt_const).of_le (by exact_mod_cast le_top)
  have csm₁ : ContDiffAt ℝ l (fun y => f₁ y • meridE1) x :=
    (cf₁.smul contDiffAt_const).of_le (by exact_mod_cast le_top)
  have hfderiv_eq :
      iteratedFDeriv ℝ l F_prof x =
        iteratedFDeriv ℝ l (fun y => f₀ y • meridE0) x +
          iteratedFDeriv ℝ l (fun y => f₁ y • meridE1) x :=
    iteratedFDeriv_add_apply csm₀ csm₁
  have hnorm_le :
      ‖iteratedFDeriv ℝ l F_prof x‖ ≤
        ‖iteratedFDeriv ℝ l f₀ x‖ + ‖iteratedFDeriv ℝ l f₁ x‖ := by
    rw [hfderiv_eq]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_iteratedFDeriv_smul_merid_le cf₀ meridE0 norm_merid_e0.le l)
        (norm_iteratedFDeriv_smul_merid_le cf₁ meridE1 norm_merid_e1.le l))
  calc W * ‖iteratedFDeriv ℝ l F_prof x‖
      ≤ W * (‖iteratedFDeriv ℝ l f₀ x‖ + ‖iteratedFDeriv ℝ l f₁ x‖) :=
        mul_le_mul_of_nonneg_left hnorm_le hW0
    _ = W * ‖iteratedFDeriv ℝ l f₀ x‖ + W * ‖iteratedFDeriv ℝ l f₁ x‖ := by ring
    _ ≤ 9 * (B * m.1 ^ (-(N : ℝ))) + 9 * (B * m.1 ^ (-(N : ℝ))) := add_le_add hjet₀ hjet₁
    _ = 18 * B * m.1 ^ (-(N : ℝ)) := by ring

/-! ### Step 4: Reducing `q`-independent remainder partials to `K^k ∂_η^j` jets -/

theorem fderiv_apply_eq_zero_of_eqOn_zero {g : ProfilePoint → ℝ}
    (hg : ∀ y ∈ ageDomain, g y = 0) (v : ProfilePoint) {x : ProfilePoint} (hx : x ∈ ageDomain) :
    fderiv ℝ g x v = 0 := by
  have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (FarDecaySub.isOpen_ageDomain.mem_nhds hx) (fun y hy => hg y hy)
  rw [hev.fderiv_eq, fderiv_const_apply, zero_apply]

theorem iterate_eq_zero_of_eqOn_zero (D : (ProfilePoint → ℝ) → (ProfilePoint → ℝ))
    (hD : ∀ g : ProfilePoint → ℝ, (∀ y ∈ ageDomain, g y = 0) → ∀ y ∈ ageDomain, D g y = 0) :
    ∀ (n : ℕ) {g : ProfilePoint → ℝ}, (∀ y ∈ ageDomain, g y = 0) →
      ∀ y ∈ ageDomain, (D^[n] g) y = 0
  | 0, _, hg, y, hy => hg y hy
  | n + 1, _, hg, y, hy => by
    rw [Function.iterate_succ_apply']
    exact hD _ (iterate_eq_zero_of_eqOn_zero D hD n hg) y hy

/-- If `partialQ f = 0` on `ageDomain`, then `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f)) = 0`
on `ageDomain` whenever `1 ≤ b`. -/
theorem partialAge_eta_q_eq_zero_of_q_zero {f : ProfilePoint → ℝ}
    (hq : ∀ y ∈ ageDomain, partialQ f y = 0) (ℓ a : ℕ) {b : ℕ} (hb : 1 ≤ b)
    {x : ProfilePoint} (hx : x ∈ ageDomain) :
    (partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))) x = 0 := by
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [add_comm 1 b']
  have hQb : ∀ y ∈ ageDomain, (partialQ^[b' + 1] f) y = 0 := by
    intro y hy
    rw [Function.iterate_succ_apply]
    exact iterate_eq_zero_of_eqOn_zero partialQ
      (fun g hg z hz => fderiv_apply_eq_zero_of_eqOn_zero hg eqDir hz) b' hq y hy
  have hEtab : ∀ y ∈ ageDomain, (partialEta^[a] (partialQ^[b' + 1] f)) y = 0 :=
    iterate_eq_zero_of_eqOn_zero partialEta
      (fun g hg z hz => fderiv_apply_eq_zero_of_eqOn_zero hg eηDir hz) a hQb
  exact iterate_eq_zero_of_eqOn_zero partialAge
    (fun g hg z hz => fderiv_apply_eq_zero_of_eqOn_zero hg esDir hz) ℓ hEtab x hx

theorem ha1_age_abs_le (f : ProfilePoint → ℝ) {x : ProfilePoint} (hx : 1 ≤ x.2.2) :
    |partialAge f x| ≤ |ageOperator f x| + (1 + x.2.1 ^ 2 / x.2.2) * |partialEta f x| := by
  simpa using Jet.A2.ha1_age_pt f 0 x hx

/-- For any smooth `q`-independent profile `f` on `ageDomain`, bounds on the `K^k ∂_η^j` jets
`(1 + η² / s)^m |(ageOperator^[k] (partialEta^[j] f)) x| ≤ B` (`m ≤ 4, k ≤ 2, j ≤ 4`) at a late
point `1 ≤ x.2.2` imply the mixed directional-partial bounds
`(1 + η² / s)² |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))) x| ≤ 9 B` for all `ℓ, a, b ≤ 2`. -/
theorem wtd_partials_of_K_eta_jets {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f ageDomain) (hq : ∀ y ∈ ageDomain, partialQ f y = 0)
    {x : ProfilePoint} (hx1 : 1 ≤ x.2.2) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : ∀ m ≤ 4, ∀ k ≤ 2, ∀ j ≤ 4,
      (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(ageOperator^[k] (partialEta^[j] f)) x| ≤ B) :
    ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
      (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
        |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))) x| ≤ 9 * B := by
  have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
  set U : ℝ := 1 + x.2.1 ^ 2 / x.2.2
  have hU0 : 0 ≤ U := by unfold U; positivity
  intro ℓ hℓ a ha b hb
  rcases Nat.eq_zero_or_pos b with rfl | hb_pos
  · simp only [Function.iterate_zero, id_eq]
    set g : ProfilePoint → ℝ := partialEta^[a] f
    have hg : ContDiffOn ℝ ∞ g ageDomain := contDiffOn_partialEta_iter hf a
    have hg_at : ContDiffAt ℝ 2 g x :=
      (hg.contDiffAt (FarDecaySub.isOpen_ageDomain.mem_nhds hx0)).of_le (by norm_num)
    have h_eta_g : ∀ j : ℕ, partialEta^[j] g = partialEta^[j + a] f := fun j => by
      dsimp [g]
      rw [← Function.iterate_add_apply]
    interval_cases ℓ
    · simp only [Function.iterate_zero, id_eq]
      have h0 := hK 2 (by omega) 0 (by omega) a (by omega)
      simp only [Function.iterate_zero, id_eq] at h0
      linarith
    · simp only [Function.iterate_one]
      have h1 := ha1_age_abs_le g hx1
      have h1' : U ^ 2 * |partialAge g x| ≤
          U ^ 2 * |(ageOperator^[1] (partialEta^[a] f)) x| +
            U ^ 3 * |(ageOperator^[0] (partialEta^[1 + a] f)) x| := by
        calc U ^ 2 * |partialAge g x|
            ≤ U ^ 2 * (|ageOperator g x| + U * |partialEta g x|) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = U ^ 2 * |(ageOperator^[1] g) x| +
                U ^ 3 * |(ageOperator^[0] (partialEta^[1] g)) x| := by
              simp only [Function.iterate_one, Function.iterate_zero, id_eq]; ring
          _ = U ^ 2 * |(ageOperator^[1] (partialEta^[a] f)) x| +
                U ^ 3 * |(ageOperator^[0] (partialEta^[1 + a] f)) x| := by
              rw [h_eta_g 1]
      have hb1 := hK 2 (by omega) 1 (by omega) a (by omega)
      have hb2 := hK 3 (by omega) 0 (by omega) (1 + a) (by omega)
      linarith
    · rw [show (partialAge^[2] g) x = partialAge (partialAge g) x from rfl]
      have h_step1 := ha1_age_abs_le (partialAge g) hx1
      have h_comm := profileCommutators g x hg_at
      have h_K_age : ageOperator (partialAge g) x =
          partialAge (ageOperator g) x - 2 * partialAge g x := by
        linarith [h_comm.2.2]
      have h_eta_K : partialEta (ageOperator g) x =
          ageOperator (partialEta g) x + partialEta g x := by
        linarith [h_comm.1]
      have h_eta_age : partialEta (partialAge g) x = partialAge (partialEta g) x :=
        commut_partialEta_partialAge hg_at
      have h_abs_K_age : |ageOperator (partialAge g) x| ≤
          |partialAge (ageOperator g) x| + 2 * |partialAge g x| := by
        rw [h_K_age]
        calc |partialAge (ageOperator g) x - 2 * partialAge g x|
            ≤ |partialAge (ageOperator g) x| + |2 * partialAge g x| := abs_sub _ _
          _ = |partialAge (ageOperator g) x| + 2 * |partialAge g x| := by
              rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h_abs_eta_K : |partialEta (ageOperator g) x| ≤
          |ageOperator (partialEta g) x| + |partialEta g x| := by
        rw [h_eta_K]
        exact abs_add_le _ _
      have h_age_Kg := ha1_age_abs_le (ageOperator g) hx1
      have h_age_g := ha1_age_abs_le g hx1
      have h_age_etag := ha1_age_abs_le (partialEta g) hx1
      have h_comb : |partialAge (partialAge g) x| ≤
          |(ageOperator^[2] g) x| + 2 * |(ageOperator^[1] g) x| +
            2 * U * |(ageOperator^[1] (partialEta^[1] g)) x| +
            3 * U * |(ageOperator^[0] (partialEta^[1] g)) x| +
            U ^ 2 * |(ageOperator^[0] (partialEta^[2] g)) x| := by
        simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
        rw [h_eta_age] at h_step1
        have hU_abs_etaK : U * |partialEta (ageOperator g) x| ≤
            U * |ageOperator (partialEta g) x| + U * |partialEta g x| := by
          linarith [mul_le_mul_of_nonneg_left h_abs_eta_K hU0]
        have hU_age_etag : U * |partialAge (partialEta g) x| ≤
            U * |ageOperator (partialEta g) x| + U ^ 2 * |partialEta (partialEta g) x| := by
          calc U * |partialAge (partialEta g) x|
              ≤ U * (|ageOperator (partialEta g) x| + U * |partialEta (partialEta g) x|) :=
                mul_le_mul_of_nonneg_left h_age_etag hU0
            _ = U * |ageOperator (partialEta g) x| + U ^ 2 * |partialEta (partialEta g) x| := by
                ring
        linarith
      have h_wtd : U ^ 2 * |partialAge (partialAge g) x| ≤
          U ^ 2 * |(ageOperator^[2] (partialEta^[a] f)) x| +
            2 * (U ^ 2 * |(ageOperator^[1] (partialEta^[a] f)) x|) +
            2 * (U ^ 3 * |(ageOperator^[1] (partialEta^[1 + a] f)) x|) +
            3 * (U ^ 3 * |(ageOperator^[0] (partialEta^[1 + a] f)) x|) +
            U ^ 4 * |(ageOperator^[0] (partialEta^[2 + a] f)) x| := by
        calc U ^ 2 * |partialAge (partialAge g) x|
            ≤ U ^ 2 * (|(ageOperator^[2] g) x| + 2 * |(ageOperator^[1] g) x| +
                2 * U * |(ageOperator^[1] (partialEta^[1] g)) x| +
                3 * U * |(ageOperator^[0] (partialEta^[1] g)) x| +
                U ^ 2 * |(ageOperator^[0] (partialEta^[2] g)) x|) :=
              mul_le_mul_of_nonneg_left h_comb (by positivity)
          _ = U ^ 2 * |(ageOperator^[2] (partialEta^[a] f)) x| +
                2 * (U ^ 2 * |(ageOperator^[1] (partialEta^[a] f)) x|) +
                2 * (U ^ 3 * |(ageOperator^[1] (partialEta^[1 + a] f)) x|) +
                3 * (U ^ 3 * |(ageOperator^[0] (partialEta^[1 + a] f)) x|) +
                U ^ 4 * |(ageOperator^[0] (partialEta^[2 + a] f)) x| := by
              rw [h_eta_g 1, h_eta_g 2]; ring
      have hb1 := hK 2 (by omega) 2 (by omega) a (by omega)
      have hb2 := hK 2 (by omega) 1 (by omega) a (by omega)
      have hb3 := hK 3 (by omega) 1 (by omega) (1 + a) (by omega)
      have hb4 := hK 3 (by omega) 0 (by omega) (1 + a) (by omega)
      have hb5 := hK 4 (by omega) 0 (by omega) (2 + a) (by omega)
      linarith
  · rw [partialAge_eta_q_eq_zero_of_q_zero hq ℓ a hb_pos hx0, abs_zero, mul_zero]
    linarith

/-! ### Step 5: Fluctuation, pressure, and `A₂` jets (`Jet.JE`) -/

/-- Pure mean part of `coeffB₁`: `B₁[S] = -ν K(K+2)(-∂_η S)`. -/
def meanB1 : Jet.Fam := fun ν c tr => coeffB₁ ν (Jet.meanFam ν c tr)

/-- Full `coeffB₁` as a `Jet.Fam`. -/
def coefB1 : Jet.Fam := Jet.coefFam fun ν ψ _ => coeffB₁ ν ψ

/-- Fluctuation part of `coeffB₁`. -/
def fluctB1 : Jet.Fam := coefB1 - meanB1

theorem coefB1_eq_add_fluctB1 (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (x : ProfilePoint) :
    coeffB₁ ν (trainProfile tr.ψ) x = meanB1 ν c tr x + fluctB1 ν c tr x := by
  simp [fluctB1, coefB1, Jet.coefFam]

theorem fluctB1_late (hT : Jet.JetToolkit) (hF : Jet.FluctWords)
    (hM : Jet.WordsW (1 / 2) Jet.meanFam) :
    Jet.LateEq fluctB1 (-(Jet.famNu (Jet.famK (Jet.famShift 2 Jet.B2.v1t)))) := by
  have hs1 := (Jet.B2.shift_congr hT (Jet.B2.v1P_split hT hF hM) 2).trans
    (Jet.B2.shift_add hT (Jet.B2.v1bar_JQ hT hM 0).smooth (Jet.B2.v1t_JE hT hF 0).smooth 2)
  have hs2 := (hT.eqOps _ _ hs1).1.trans
    (hT.linOps _ _ (hT.jc.qshift 2 (Jet.B2.v1bar_JQ hT hM 1)).smooth
      (hT.jc.eshift 2 (Jet.B2.v1t_JE hT hF 1)).smooth 0).1
  intro ν c hν hc tr htr x hx
  have e := hs2 ν c hν hc tr htr hx
  show coeffB₁ ν (trainProfile tr.ψ) x - coeffB₁ ν (Jet.meanFam ν c tr) x =
    -(ν * ageOperator (ageShift 2 (Jet.B2.v1t ν c tr)) x)
  have e' : ageOperator (ageShift 2 (Jet.B2.v1P ν c tr)) x =
      ageOperator (ageShift 2 (Jet.B2.v1bar ν c tr)) x +
        ageOperator (ageShift 2 (Jet.B2.v1t ν c tr)) x := e
  have hv1 : streamV1 (Jet.meanFam ν c tr) = Jet.B2.v1bar ν c tr := rfl
  simp only [coeffB₁, Jet.B2.v1P, hv1] at e' ⊢
  linear_combination -ν * e'

theorem fluctB1_JE (hT : Jet.JetToolkit) (hF : Jet.FluctWords)
    (hM : Jet.WordsW (1 / 2) Jet.meanFam) (n : ℕ) :
    Jet.JE n fluctB1 :=
  hT.jc.econgr (fluctB1_late hT hF hM).symm
    (hT.jc.eneg (hT.jc.enu (hT.jc.eshift 2 (Jet.B2.v1t_JE hT hF (n + 2))).k))

/-- Pure mean part of `coeffB₃`: `B₃[S] = -ν (K+1)² (1-K) S`. -/
def meanB3 : Jet.Fam := fun ν c tr => coeffB₃ ν (Jet.meanFam ν c tr)

/-- Full `coeffB₃` as a `Jet.Fam`. -/
def coefB3 : Jet.Fam := Jet.coefFam fun ν ψ _ => coeffB₃ ν ψ

/-- Fluctuation part of `coeffB₃`. -/
def fluctB3 : Jet.Fam := coefB3 - meanB3

theorem coefB3_eq_add_fluctB3 (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (x : ProfilePoint) :
    coeffB₃ ν (trainProfile tr.ψ) x = meanB3 ν c tr x + fluctB3 ν c tr x := by
  simp [fluctB3, coefB3, Jet.coefFam]

theorem fluctB3_late (hT : Jet.JetToolkit) (hF : Jet.FluctWords)
    (hM : Jet.WordsW (1 / 2) Jet.meanFam) :
    Jet.LateEq fluctB3 (-(Jet.famNu (Jet.famShift 1 (Jet.famShift 1 Jet.B2.ht)))) := by
  have hs := (Jet.B2.shift_congr hT (Jet.B2.hP_shift_split hT hF hM) 1).trans
    (Jet.B2.shift_add hT (hT.jc.qshift 1 (Jet.B2.hbar_JQ hT hM 1)).smooth
      (hT.jc.eshift 1 (Jet.B2.ht_JE hT hF 1)).smooth 1)
  intro ν c hν hc tr htr x hx
  have e : ageShift 1 (ageShift 1 (Jet.B2.hP ν c tr)) x =
      ageShift 1 (ageShift 1 (Jet.B2.hbar ν c tr)) x +
        ageShift 1 (ageShift 1 (Jet.B2.ht ν c tr)) x :=
    hs ν c hν hc tr htr hx
  show coeffB₃ ν (trainProfile tr.ψ) x - coeffB₃ ν (Jet.meanFam ν c tr) x =
    -(ν * ageShift 1 (ageShift 1 (Jet.B2.ht ν c tr)) x)
  have hhb : ageDefect (Jet.meanFam ν c tr) = Jet.B2.hbar ν c tr := rfl
  simp only [coeffB₃, Jet.B2.hP, hhb] at e ⊢
  linear_combination -ν * e

theorem fluctB3_JE (hT : Jet.JetToolkit) (hF : Jet.FluctWords)
    (hM : Jet.WordsW (1 / 2) Jet.meanFam) (n : ℕ) :
    Jet.JE n fluctB3 :=
  hT.jc.econgr (fluctB3_late hT hF hM).symm
    (hT.jc.eneg (hT.jc.enu (hT.jc.eshift 1 (hT.jc.eshift 1 (Jet.B2.ht_JE hT hF (n + 2))))))

/-- Pure mean part of `coeffA₁`: `M₁ = -\bar v₁ K \bar v₁ + \bar H ∂_η \bar v₁ - \bar v₁²`. -/
def meanA1 : Jet.Fam :=
  -(Jet.B2.v1bar * Jet.famK Jet.B2.v1bar) + Jet.B2.hbar * Jet.famEta Jet.B2.v1bar -
    Jet.B2.v1bar * Jet.B2.v1bar

/-- Full `coeffA₁` as a `Jet.Fam`. -/
def coefA1 : Jet.Fam := Jet.coefFam coeffA₁

/-- Fluctuation and pressure part of `coeffA₁`. -/
def fluctA1 : Jet.Fam := coefA1 - meanA1

theorem coefA1_eq_add_fluctA1 (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (x : ProfilePoint) :
    coeffA₁ ν (trainProfile tr.ψ) (trainProfile tr.p) x = meanA1 ν c tr x + fluctA1 ν c tr x := by
  simp [fluctA1, coefA1, Jet.coefFam]

/-- Explicit fluctuation/pressure sum for `fluctA1`. -/
def fsumA1 : Jet.Fam :=
  -(Jet.B2.v1t * Jet.famK Jet.B2.v1P) - Jet.B2.v1bar * Jet.famK Jet.B2.v1t +
    Jet.B2.ht * Jet.famEta Jet.B2.v1P + Jet.B2.hbar * Jet.famEta Jet.B2.v1t -
    Jet.B2.v1t * Jet.B2.v1P - Jet.B2.v1bar * Jet.B2.v1t +
    (2 : ℝ) • Jet.famNu (Jet.famShift 1 (Jet.famQ Jet.B2.v1P)) - Jet.famShift 2 Jet.presFam

theorem fluctA1_late (hT : Jet.JetToolkit) (hF : Jet.FluctWords)
    (hM : Jet.WordsW (1 / 2) Jet.meanFam) :
    Jet.LateEq fluctA1 fsumA1 := by
  have hk := (hT.eqOps _ _ (Jet.B2.v1P_split hT hF hM)).1.trans
    (hT.linOps _ _ (Jet.B2.v1bar_JQ hT hM 0).smooth (Jet.B2.v1t_JE hT hF 0).smooth 0).1
  have heta := (hT.eqOps _ _ (Jet.B2.v1P_split hT hF hM)).2.1.trans
    (hT.linOps _ _ (Jet.B2.v1bar_JQ hT hM 0).smooth (Jet.B2.v1t_JE hT hF 0).smooth 0).2.1
  intro ν c hν hc tr htr x hx
  have e0 : coefA1 ν c tr x =
      -(Jet.B2.v1P ν c tr x * Jet.famK Jet.B2.v1P ν c tr x) +
        Jet.B2.hP ν c tr x * Jet.famEta Jet.B2.v1P ν c tr x -
        Jet.B2.v1P ν c tr x * Jet.B2.v1P ν c tr x +
        2 * Jet.famNu (Jet.famShift 1 (Jet.famQ Jet.B2.v1P)) ν c tr x -
        Jet.famShift 2 Jet.presFam ν c tr x :=
    (Jet.coeffA1_late ν c hν hc tr htr hx).symm
  have e1 : Jet.B2.v1P ν c tr x = Jet.B2.v1bar ν c tr x + Jet.B2.v1t ν c tr x :=
    Jet.B2.v1P_split hT hF hM ν c hν hc tr htr hx
  have e2 : Jet.B2.hP ν c tr x = Jet.B2.hbar ν c tr x + Jet.B2.ht ν c tr x :=
    Jet.B2.hP_split hT hF hM ν c hν hc tr htr hx
  have e3 : Jet.famK Jet.B2.v1P ν c tr x =
      Jet.famK Jet.B2.v1bar ν c tr x + Jet.famK Jet.B2.v1t ν c tr x :=
    hk ν c hν hc tr htr hx
  have e4 : Jet.famEta Jet.B2.v1P ν c tr x =
      Jet.famEta Jet.B2.v1bar ν c tr x + Jet.famEta Jet.B2.v1t ν c tr x :=
    heta ν c hν hc tr htr hx
  show coefA1 ν c tr x - (-(Jet.B2.v1bar ν c tr x * Jet.famK Jet.B2.v1bar ν c tr x) +
      Jet.B2.hbar ν c tr x * Jet.famEta Jet.B2.v1bar ν c tr x -
      Jet.B2.v1bar ν c tr x * Jet.B2.v1bar ν c tr x) =
    -(Jet.B2.v1t ν c tr x * Jet.famK Jet.B2.v1P ν c tr x) -
      Jet.B2.v1bar ν c tr x * Jet.famK Jet.B2.v1t ν c tr x +
      Jet.B2.ht ν c tr x * Jet.famEta Jet.B2.v1P ν c tr x +
      Jet.B2.hbar ν c tr x * Jet.famEta Jet.B2.v1t ν c tr x -
      Jet.B2.v1t ν c tr x * Jet.B2.v1P ν c tr x -
      Jet.B2.v1bar ν c tr x * Jet.B2.v1t ν c tr x +
      2 * Jet.famNu (Jet.famShift 1 (Jet.famQ Jet.B2.v1P)) ν c tr x -
      Jet.famShift 2 Jet.presFam ν c tr x
  rw [e0]
  linear_combination (-(Jet.famK Jet.B2.v1P ν c tr x) - Jet.B2.v1P ν c tr x -
      Jet.B2.v1bar ν c tr x) * e1 +
    (Jet.famEta Jet.B2.v1P ν c tr x) * e2 -
    (Jet.B2.v1bar ν c tr x) * e3 +
    (Jet.B2.hbar ν c tr x) * e4

theorem fluctA1_JE (hT : Jet.JetToolkit) (hF : Jet.FluctWords)
    (hM : Jet.WordsW (1 / 2) Jet.meanFam) (n : ℕ) :
    Jet.JE n fluctA1 := by
  have hP : ∀ m, Jet.JE m Jet.presFam := fun m => Jet.JE_of_words hT.wordE m _ hF.2
  have s1 : Jet.JE n (Jet.B2.v1t * Jet.famK Jet.B2.v1P) :=
    hT.jc.emulQ (Jet.B2.v1t_JE hT hF n)
      (hT.jc.qmono (by norm_num) (Jet.B2.v1P_JQ hT hF hM (n + 1)).k)
  have s2 : Jet.JE n (Jet.B2.v1bar * Jet.famK Jet.B2.v1t) :=
    hT.jc.qmulE (hT.jc.qmono (by norm_num) (Jet.B2.v1bar_JQ hT hM n))
      (Jet.B2.v1t_JE hT hF (n + 1)).k
  have s3 : Jet.JE n (Jet.B2.ht * Jet.famEta Jet.B2.v1P) :=
    hT.jc.emulQ (Jet.B2.ht_JE hT hF n)
      (hT.jc.qmono (by norm_num) (Jet.B2.v1P_JQ hT hF hM (n + 1)).eta)
  have s4 : Jet.JE n (Jet.B2.hbar * Jet.famEta Jet.B2.v1t) :=
    hT.jc.qmulE (hT.jc.qmono (by norm_num) (Jet.B2.hbar_JQ hT hM n))
      (Jet.B2.v1t_JE hT hF (n + 1)).eta
  have s5 : Jet.JE n (Jet.B2.v1t * Jet.B2.v1P) :=
    hT.jc.emulQ (Jet.B2.v1t_JE hT hF n) (hT.jc.qmono (by norm_num) (Jet.B2.v1P_JQ hT hF hM n))
  have s6 : Jet.JE n (Jet.B2.v1bar * Jet.B2.v1t) :=
    hT.jc.qmulE (hT.jc.qmono (by norm_num) (Jet.B2.v1bar_JQ hT hM n)) (Jet.B2.v1t_JE hT hF n)
  have s7 : Jet.JE n ((2 : ℝ) • Jet.famNu (Jet.famShift 1 (Jet.famQ Jet.B2.v1P))) :=
    hT.jc.esmul 2 (hT.jc.enu (hT.jc.eshift 1 (Jet.B2.v1P_JQ hT hF hM (n + 2)).q))
  have s8 : Jet.JE n (Jet.famShift 2 Jet.presFam) :=
    hT.jc.eshift 2 (hP (n + 1))
  exact hT.jc.econgr (fluctA1_late hT hF hM).symm
    (hT.jc.esub (hT.jc.eadd (hT.jc.esub (hT.jc.esub (hT.jc.eadd (hT.jc.eadd
      (hT.jc.esub (hT.jc.eneg s1) s2) s3) s4) s5) s6) s7) s8)

/-- Unconditional `FluctWords` and `WordsW (1 / 2) meanFam` from `lateIngredients`. -/
theorem fluctWords_uncond : Jet.FluctWords :=
  Jet.fluctWords_of lateIngredients

theorem meanWords_uncond : Jet.WordsW (1 / 2) Jet.meanFam :=
  Jet.meanWords_of (Jet.meanSmoothQ_of lateIngredients)
    (Jet.heatWords_of lateIngredients.heat Jet.jetToolkit.iterLin)
    Jet.jetToolkit.iterLin (Jet.meanHeatPart_of lateIngredients)
    (Jet.meanRemPart_of lateIngredients)

/-- Unconditional `JE n` for all five fluctuation/pressure/`A₂` families. -/
theorem coefA2_je (n : ℕ) : Jet.JE n (Jet.coefFam Jet.A2.coefA2) := by
  have hT := Jet.jetToolkit
  have hF := fluctWords_uncond
  have hM := meanWords_uncond
  have hB := Jet.baseJets_of hT.jc hT.wordE hT.wordW hF hM
  exact Jet.A2.a2Jets_of hT.jc Jet.A2.ageSmoothLocal (Jet.A2.ageComm_of lateIngredients.comm)
    Jet.A2.ageWE (fun m => (hB m).2.2.2) (fun m => (hB m).2.1)
    (fun m => Jet.JE_of_words hT.wordE m Jet.A2.stressFam (Jet.A2.stressWords_of lateIngredients))
    (Jet.A2.meanStressCancel_of hT Jet.A2.heatOpLin
      (Jet.A2.heatOpK_of lateIngredients.comm hT.comm)
      (Jet.A2.meanHeatEq_of trainMeanEquations_proof) hM.1)
    (Jet.A2.heat_defect_split hT Jet.A2.ageSmoothLocal Jet.A2.heatOpLin hM.1 hF.1.1) n

theorem fluctB2_je (n : ℕ) : Jet.JE n Jet.B2.fluctB2 :=
  Jet.B2.fluct_JE Jet.jetToolkit fluctWords_uncond meanWords_uncond n

theorem fluctB1_je (n : ℕ) : Jet.JE n fluctB1 :=
  fluctB1_JE Jet.jetToolkit fluctWords_uncond meanWords_uncond n

theorem fluctB3_je (n : ℕ) : Jet.JE n fluctB3 :=
  fluctB3_JE Jet.jetToolkit fluctWords_uncond meanWords_uncond n

theorem fluctA1_je (n : ℕ) : Jet.JE n fluctA1 :=
  fluctA1_JE Jet.jetToolkit fluctWords_uncond meanWords_uncond n

/-! ### Step 6: Mixed directional partials and `iteratedFDeriv` bounds for `Jet.JE` families -/

theorem je_famQ_iter : ∀ (b n : ℕ) (F : Jet.Fam),
    Jet.JE (n + b) F → Jet.JE n (fun ν c tr => partialQ^[b] (F ν c tr))
  | 0, n, F, h => by simpa using h
  | b + 1, n, F, h => by
    have h' : Jet.JE ((n + 1) + b) F := by rw [Nat.add_right_comm]; exact h
    have ih := (je_famQ_iter b (n + 1) F h').q
    have heq : Jet.famQ (fun ν c tr => partialQ^[b] (F ν c tr)) =
        fun ν c tr => partialQ^[b + 1] (F ν c tr) := by
      funext ν c tr
      exact (Function.iterate_succ_apply' partialQ b (F ν c tr)).symm
    rwa [heq] at ih

theorem je_famEta_iter : ∀ (a n : ℕ) (F : Jet.Fam),
    Jet.JE (n + a) F → Jet.JE n (fun ν c tr => partialEta^[a] (F ν c tr))
  | 0, n, F, h => by simpa using h
  | a + 1, n, F, h => by
    have h' : Jet.JE ((n + 1) + a) F := by rw [Nat.add_right_comm]; exact h
    have ih := (je_famEta_iter a (n + 1) F h').eta
    have heq : Jet.famEta (fun ν c tr => partialEta^[a] (F ν c tr)) =
        fun ν c tr => partialEta^[a + 1] (F ν c tr) := by
      funext ν c tr
      exact (Function.iterate_succ_apply' partialEta a (F ν c tr)).symm
    rwa [heq] at ih

theorem je_famAge_iter : ∀ (ℓ n : ℕ) (F : Jet.Fam),
    Jet.JE (n + ℓ) F → Jet.JE n (fun ν c tr => partialAge^[ℓ] (F ν c tr))
  | 0, n, F, h => by simpa using h
  | ℓ + 1, n, F, h => by
    have h' : Jet.JE ((n + 1) + ℓ) F := by rw [Nat.add_right_comm]; exact h
    have ih := Jet.A2.ageJE_of Jet.jetToolkit.jc Jet.A2.ageSmoothLocal
      (Jet.A2.ageComm_of lateIngredients.comm) Jet.A2.ageWE n _ (je_famAge_iter ℓ (n + 1) F h')
    have heq : Jet.A2.famAge (fun ν c tr => partialAge^[ℓ] (F ν c tr)) =
        fun ν c tr => partialAge^[ℓ + 1] (F ν c tr) := by
      funext ν c tr
      exact (Function.iterate_succ_apply' partialAge ℓ (F ν c tr)).symm
    rwa [heq] at ih

/-- For any `F : Jet.Fam` with `∀ n, Jet.JE n F` and any `ℓ, a, b : ℕ`, the mixed directional
partial `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] F))` belongs to `Jet.JE 0`. -/
theorem je_mixed_partials_zero {F : Jet.Fam} (hF : ∀ n, Jet.JE n F) (ℓ a b : ℕ) :
    Jet.JE 0 (fun ν c tr => partialAge^[ℓ] (partialEta^[a] (partialQ^[b] (F ν c tr)))) :=
  je_famAge_iter ℓ 0 _ (je_famEta_iter a (0 + ℓ) _ (je_famQ_iter b (0 + ℓ + a) F (hF _)))

/-- From `Jet.JE 0 G`, there is a viscosity threshold `ν₀ > 0` (independent of `N`) such that at
fixed parameters `p` with `p.ν < ν₀` and `p.c = (p.ν ^ 2)⁻¹`, `G p.ν p.c p.train` has rapid
inverse-power age decay `B_N s^{-N}` on `1 ≤ s` for every `N : ℕ`. -/
theorem je_zero_late_bound {G : Jet.Fam} (hG : Jet.JE 0 G) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → ∀ N : ℕ,
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 →
          (1 + x.2.1 ^ 2 / x.2.2) ^ 2 * |G p.ν p.c p.train x| ≤ B * x.2.2 ^ (-(N : ℝ)) := by
  obtain ⟨C₀, d₀, κ, ν₀, hκ, hν₀, H⟩ := hG.we 2 2 (by norm_num)
  refine ⟨ν₀, hν₀, fun p htr hν hc N => ?_⟩
  have hc_rpow : p.c = p.ν ^ (-(2 : ℝ)) := by
    rw [hc, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg p.ν_pos.le, Real.rpow_natCast]
  have hExp_gen : ∀ (c : ℝ) (tr : UnforcedLeray.B0140.TrainSol p.ν c),
      c = p.ν ^ (-(2 : ℝ)) → IsBUCTrain tr →
      ExpBound κ p.ν c 2 (G p.ν c tr) (polyConst C₀ d₀ p.ν c) := by
    rintro _ tr rfl htr'
    exact H p.ν p.ν_pos hν.le tr htr'
  have hExp : ExpBound κ p.ν p.c 2 (G p.ν p.c p.train) (polyConst C₀ d₀ p.ν p.c) :=
    hExp_gen p.c p.train hc_rpow htr
  set P₀ : ℝ := max (polyConst C₀ d₀ p.ν p.c) 0
  have hP₀ : 0 ≤ P₀ := le_max_right _ _
  have hPL : polyConst C₀ d₀ p.ν p.c ≤ P₀ := le_max_left _ _
  have hExp' : ExpBound κ p.ν p.c 2 (G p.ν p.c p.train) P₀ :=
    ExpBound.mono' p.ν_pos p.c_pos le_rfl hPL hExp
  set a : ℝ := κ * p.ν / p.c ^ 2
  have ha : 0 < a := by
    unfold a
    have := p.ν_pos
    have := p.c_pos
    positivity
  set C_exp : ℝ := (N.factorial : ℝ) / a ^ N
  have hCexp0 : 0 ≤ C_exp := by unfold C_exp; positivity
  refine ⟨P₀ * C_exp, mul_nonneg hP₀ hCexp0, fun x hx1 => ?_⟩
  have hexp_eq : -(κ * p.ν * x.2.2 / p.c ^ 2) = -(a * x.2.2) := by
    unfold a; ring
  have hexp_le : Real.exp (-(κ * p.ν * x.2.2 / p.c ^ 2)) ≤ C_exp * x.2.2 ^ (-(N : ℝ)) := by
    rw [hexp_eq]
    exact exp_neg_le_rpow_neg ha hx1 N
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ 2 * |G p.ν p.c p.train x|
      ≤ P₀ * Real.exp (-(κ * p.ν * x.2.2 / p.c ^ 2)) := hExp' x hx1
    _ ≤ P₀ * (C_exp * x.2.2 ^ (-(N : ℝ))) := mul_le_mul_of_nonneg_left hexp_le hP₀
    _ = P₀ * C_exp * x.2.2 ^ (-(N : ℝ)) := by ring

/-- For any `F : Jet.Fam` with `∀ n, Jet.JE n F`, there is a single viscosity threshold `ν₀ > 0`
(independent of `N`) such that for `p.ν < ν₀` and `p.c = (p.ν ^ 2)⁻¹`, `F p.ν p.c p.train` is `C^∞`
on `ageDomain` and for every `N : ℕ` its order-`≤ 2` Fréchet jets on `1 ≤ x.2.2` satisfy
`(1 + η² / s)² ‖D^l(F p.ν p.c p.train)(x)‖ ≤ B s^{-N}`. -/
theorem je_late_iteratedFDeriv_bound {F : Jet.Fam} (hF : ∀ n, Jet.JE n F) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ →
        ContDiffOn ℝ ∞ (F p.ν p.c p.train) ageDomain ∧
        ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ l ≤ 2,
          (1 + x.2.1 ^ 2 / x.2.2) ^ 2 * ‖iteratedFDeriv ℝ l (F p.ν p.c p.train) x‖ ≤
            B * x.2.2 ^ (-(N : ℝ)) := by
  choose ν_f hν_f H_f using fun q : Fin 3 × Fin 3 × Fin 3 =>
    je_zero_late_bound (je_mixed_partials_zero hF q.1.val q.2.1.val q.2.2.val)
  obtain ⟨ν₀, hν₀, hle⟩ : ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ q : Fin 3 × Fin 3 × Fin 3, ν₀ ≤ ν_f q := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty ν_f, ?_, fun q =>
      Finset.inf'_le ν_f (Finset.mem_univ q)⟩
    rw [Finset.lt_inf'_iff]
    intro q _
    exact hν_f q
  refine ⟨ν₀, hν₀, fun p htr hν hc => ?_⟩
  have hsm : ContDiffOn ℝ ∞ (F p.ν p.c p.train) ageDomain :=
    (hF 0).smooth p.ν p.c p.ν_pos p.c_pos p.train htr
  refine ⟨hsm, fun N => ?_⟩
  choose B_f hB0 hB using fun q : Fin 3 × Fin 3 × Fin 3 =>
    H_f q p htr (lt_of_lt_of_le hν (hle q)) hc N
  set Bsum : ℝ := ∑ q : Fin 3 × Fin 3 × Fin 3, B_f q
  have hBsum0 : 0 ≤ Bsum := Finset.sum_nonneg fun q _ => hB0 q
  refine ⟨9 * Bsum, mul_nonneg (by norm_num) hBsum0, fun x hx1 l hl => ?_⟩
  have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
  have hW : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ 2 := by positivity
  have hBN0 : 0 ≤ Bsum * x.2.2 ^ (-(N : ℝ)) :=
    mul_nonneg hBsum0 (Real.rpow_nonneg hx0.le _)
  have hjet := wtd_norm_iteratedFDeriv_le_of_partials hsm hx0 hW hBN0 (fun ℓ hℓ a ha b hb => by
    let q : Fin 3 × Fin 3 × Fin 3 := (⟨ℓ, by omega⟩, ⟨a, by omega⟩, ⟨b, by omega⟩)
    have hq_le : B_f q ≤ Bsum :=
      Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_univ q)
    exact (hB q x hx1).trans
      (mul_le_mul_of_nonneg_right hq_le (Real.rpow_nonneg hx0.le _))) hl
  linarith

/-- Full `coeffA₂` as a `Jet.Fam`. -/
def coefA2Fam : Jet.Fam := Jet.coefFam Jet.A2.coefA2

/-- Fluctuation/pressure/`A₂` meridional profile on `ProfilePoint`. -/
def fluctPolyMerid (p : Params) (x : ProfilePoint) : Axi.Merid :=
  (ringEps p.R * fluctA1 p.ν p.c p.train x + ringEps p.R ^ 2 * fluctB1 p.ν p.c p.train x) •
      meridE0 +
    (ringEps p.R * coefA2Fam p.ν p.c p.train x +
        ringEps p.R ^ 2 * Jet.B2.fluctB2 p.ν p.c p.train x +
        ringEps p.R ^ 3 * fluctB3 p.ν p.c p.train x) •
      meridE1

/-- Combined order-`≤ 2` late jet bound for the entire fluctuation/pressure/`A₂` meridional
profile `fun m => fluctPolyMerid p (chartSwap m)`. -/
theorem fluctPolyMerid_late_jet2 :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R →
        ContDiffOn ℝ ∞ (fun m => fluctPolyMerid p (chartSwap m)) {m : ℝ × (ℝ × ℝ) | 0 < m.1} ∧
        ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℝ × (ℝ × ℝ), 1 ≤ m.1 → ∀ l ≤ 2,
          (1 + m.2.2 ^ 2 / m.1) ^ 2 *
            ‖iteratedFDeriv ℝ l (fun w => fluctPolyMerid p (chartSwap w)) m‖ ≤
              B * m.1 ^ (-(N : ℝ)) := by
  obtain ⟨ν1, hν1, H1⟩ := je_late_iteratedFDeriv_bound fluctA1_je
  obtain ⟨ν2, hν2, H2⟩ := je_late_iteratedFDeriv_bound fluctB1_je
  obtain ⟨ν3, hν3, H3⟩ := je_late_iteratedFDeriv_bound coefA2_je
  obtain ⟨ν4, hν4, H4⟩ := je_late_iteratedFDeriv_bound fluctB2_je
  obtain ⟨ν5, hν5, H5⟩ := je_late_iteratedFDeriv_bound fluctB3_je
  refine ⟨min (min (min (min ν1 ν2) ν3) ν4) ν5,
    lt_min (lt_min (lt_min (lt_min hν1 hν2) hν3) hν4) hν5,
    fun p htr hν hc hR => ?_⟩
  obtain ⟨hsm1, HB1⟩ := H1 p htr (lt_of_lt_of_le hν (by simp)) hc
  obtain ⟨hsm2, HB2⟩ := H2 p htr (lt_of_lt_of_le hν (by simp)) hc
  obtain ⟨hsm3, HB3⟩ := H3 p htr (lt_of_lt_of_le hν (by simp)) hc
  obtain ⟨hsm4, HB4⟩ := H4 p htr (lt_of_lt_of_le hν (by simp)) hc
  obtain ⟨hsm5, HB5⟩ := H5 p htr (lt_of_lt_of_le hν (by simp)) hc
  have hsm_fluct : ContDiffOn ℝ ∞ (fluctPolyMerid p) ageDomain := by
    unfold fluctPolyMerid
    exact (((contDiffOn_const.mul hsm1).add (contDiffOn_const.mul hsm2)).smul contDiffOn_const).add
      ((((contDiffOn_const.mul hsm3).add (contDiffOn_const.mul hsm4)).add
        (contDiffOn_const.mul hsm5)).smul contDiffOn_const)
  have hsm_comp :
      ContDiffOn ℝ ∞ (fun m => fluctPolyMerid p (chartSwap m)) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hsm_fluct.comp chartSwapLIE.contDiff.contDiffOn (fun m hm => hm)
  refine ⟨hsm_comp, fun N => ?_⟩
  obtain ⟨B1, hB1, hbd1⟩ := HB1 N
  obtain ⟨B2, hB2, hbd2⟩ := HB2 N
  obtain ⟨B3, hB3, hbd3⟩ := HB3 N
  obtain ⟨B4, hB4, hbd4⟩ := HB4 N
  obtain ⟨B5, hB5, hbd5⟩ := HB5 N
  refine ⟨B1 + B2 + B3 + B4 + B5, by positivity, fun m hm1 l hl => ?_⟩
  rw [norm_iteratedFDeriv_comp_chartSwap (fluctPolyMerid p) m l]
  set x : ProfilePoint := chartSwap m
  have hx1 : 1 ≤ x.2.2 := hm1
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  obtain ⟨hε0, hε1⟩ := ringEps_nonneg_and_le_one hR
  have hε20 : 0 ≤ ringEps p.R ^ 2 := sq_nonneg _
  have hε21 : ringEps p.R ^ 2 ≤ 1 := by nlinarith
  have hε30 : 0 ≤ ringEps p.R ^ 3 := pow_nonneg hε0 3
  have hε31 : ringEps p.R ^ 3 ≤ 1 := by
    calc ringEps p.R ^ 3 = ringEps p.R ^ 2 * ringEps p.R := by ring
      _ ≤ 1 * 1 := mul_le_mul hε21 hε1 hε0 zero_le_one
      _ = 1 := mul_one 1
  have hnhds : ageDomain ∈ 𝓝 x := FarDecaySub.isOpen_ageDomain.mem_nhds hx0
  have c1 : ContDiffAt ℝ ∞ (fluctA1 p.ν p.c p.train) x := hsm1.contDiffAt hnhds
  have c2 : ContDiffAt ℝ ∞ (fluctB1 p.ν p.c p.train) x := hsm2.contDiffAt hnhds
  have c3 : ContDiffAt ℝ ∞ (coefA2Fam p.ν p.c p.train) x := hsm3.contDiffAt hnhds
  have c4 : ContDiffAt ℝ ∞ (Jet.B2.fluctB2 p.ν p.c p.train) x := hsm4.contDiffAt hnhds
  have c5 : ContDiffAt ℝ ∞ (fluctB3 p.ν p.c p.train) x := hsm5.contDiffAt hnhds
  let f1 : ProfilePoint → ℝ := fun y => ringEps p.R * fluctA1 p.ν p.c p.train y
  let f2 : ProfilePoint → ℝ := fun y => ringEps p.R ^ 2 * fluctB1 p.ν p.c p.train y
  let g1 : ProfilePoint → ℝ := fun y => ringEps p.R * coefA2Fam p.ν p.c p.train y
  let g2 : ProfilePoint → ℝ := fun y => ringEps p.R ^ 2 * Jet.B2.fluctB2 p.ν p.c p.train y
  let g3 : ProfilePoint → ℝ := fun y => ringEps p.R ^ 3 * fluctB3 p.ν p.c p.train y
  have cf1 : ContDiffAt ℝ ∞ f1 x := contDiffAt_const.mul c1
  have cf2 : ContDiffAt ℝ ∞ f2 x := contDiffAt_const.mul c2
  have cg1 : ContDiffAt ℝ ∞ g1 x := contDiffAt_const.mul c3
  have cg2 : ContDiffAt ℝ ∞ g2 x := contDiffAt_const.mul c4
  have cg3 : ContDiffAt ℝ ∞ g3 x := contDiffAt_const.mul c5
  let F0 : ProfilePoint → Axi.Merid := fun y => (f1 y + f2 y) • meridE0
  let F1 : ProfilePoint → Axi.Merid := fun y => (g1 y + g2 y + g3 y) • meridE1
  have cF0 : ContDiffAt ℝ l F0 x :=
    ((cf1.add cf2).smul contDiffAt_const).of_le (by exact_mod_cast le_top)
  have cF1 : ContDiffAt ℝ l F1 x :=
    (((cg1.add cg2).add cg3).smul contDiffAt_const).of_le (by exact_mod_cast le_top)
  have hsumF : iteratedFDeriv ℝ l (fluctPolyMerid p) x =
      iteratedFDeriv ℝ l F0 x + iteratedFDeriv ℝ l F1 x :=
    iteratedFDeriv_add_apply cF0 cF1
  have hF0 : ‖iteratedFDeriv ℝ l F0 x‖ ≤
      ‖iteratedFDeriv ℝ l (fluctA1 p.ν p.c p.train) x‖ +
        ‖iteratedFDeriv ℝ l (fluctB1 p.ν p.c p.train) x‖ := by
    have hsm : ‖iteratedFDeriv ℝ l F0 x‖ ≤ ‖iteratedFDeriv ℝ l (fun y => f1 y + f2 y) x‖ :=
      norm_iteratedFDeriv_smul_merid_le (cf1.add cf2) _ norm_merid_e0.le l
    have hadd : iteratedFDeriv ℝ l (fun y => f1 y + f2 y) x =
        iteratedFDeriv ℝ l f1 x + iteratedFDeriv ℝ l f2 x :=
      iteratedFDeriv_add_apply (cf1.of_le (by exact_mod_cast le_top))
        (cf2.of_le (by exact_mod_cast le_top))
    calc ‖iteratedFDeriv ℝ l F0 x‖
        ≤ ‖iteratedFDeriv ℝ l f1 x + iteratedFDeriv ℝ l f2 x‖ := by rw [← hadd]; exact hsm
      _ ≤ ‖iteratedFDeriv ℝ l f1 x‖ + ‖iteratedFDeriv ℝ l f2 x‖ := norm_add_le _ _
      _ ≤ ‖iteratedFDeriv ℝ l (fluctA1 p.ν p.c p.train) x‖ +
            ‖iteratedFDeriv ℝ l (fluctB1 p.ν p.c p.train) x‖ :=
          add_le_add (norm_iteratedFDeriv_const_mul_le c1 hε0 hε1 l)
            (norm_iteratedFDeriv_const_mul_le c2 hε20 hε21 l)
  have hF1 : ‖iteratedFDeriv ℝ l F1 x‖ ≤
      ‖iteratedFDeriv ℝ l (coefA2Fam p.ν p.c p.train) x‖ +
        ‖iteratedFDeriv ℝ l (Jet.B2.fluctB2 p.ν p.c p.train) x‖ +
        ‖iteratedFDeriv ℝ l (fluctB3 p.ν p.c p.train) x‖ := by
    have hsm : ‖iteratedFDeriv ℝ l F1 x‖ ≤
        ‖iteratedFDeriv ℝ l (fun y => g1 y + g2 y + g3 y) x‖ :=
      norm_iteratedFDeriv_smul_merid_le ((cg1.add cg2).add cg3) _ norm_merid_e1.le l
    have hadd1 : iteratedFDeriv ℝ l (fun y => g1 y + g2 y + g3 y) x =
        iteratedFDeriv ℝ l (fun y => g1 y + g2 y) x + iteratedFDeriv ℝ l g3 x :=
      iteratedFDeriv_add_apply ((cg1.add cg2).of_le (by exact_mod_cast le_top))
        (cg3.of_le (by exact_mod_cast le_top))
    have hadd2 : iteratedFDeriv ℝ l (fun y => g1 y + g2 y) x =
        iteratedFDeriv ℝ l g1 x + iteratedFDeriv ℝ l g2 x :=
      iteratedFDeriv_add_apply (cg1.of_le (by exact_mod_cast le_top))
        (cg2.of_le (by exact_mod_cast le_top))
    calc ‖iteratedFDeriv ℝ l F1 x‖
        ≤ ‖iteratedFDeriv ℝ l g1 x + iteratedFDeriv ℝ l g2 x + iteratedFDeriv ℝ l g3 x‖ := by
          rw [← hadd2, ← hadd1]; exact hsm
      _ ≤ ‖iteratedFDeriv ℝ l g1 x + iteratedFDeriv ℝ l g2 x‖ + ‖iteratedFDeriv ℝ l g3 x‖ :=
          norm_add_le _ _
      _ ≤ ‖iteratedFDeriv ℝ l g1 x‖ + ‖iteratedFDeriv ℝ l g2 x‖ + ‖iteratedFDeriv ℝ l g3 x‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖iteratedFDeriv ℝ l (coefA2Fam p.ν p.c p.train) x‖ +
            ‖iteratedFDeriv ℝ l (Jet.B2.fluctB2 p.ν p.c p.train) x‖ +
            ‖iteratedFDeriv ℝ l (fluctB3 p.ν p.c p.train) x‖ :=
          add_le_add
            (add_le_add (norm_iteratedFDeriv_const_mul_le c3 hε0 hε1 l)
              (norm_iteratedFDeriv_const_mul_le c4 hε20 hε21 l))
            (norm_iteratedFDeriv_const_mul_le c5 hε30 hε31 l)
  have htot : ‖iteratedFDeriv ℝ l (fluctPolyMerid p) x‖ ≤
      ‖iteratedFDeriv ℝ l (fluctA1 p.ν p.c p.train) x‖ +
        ‖iteratedFDeriv ℝ l (fluctB1 p.ν p.c p.train) x‖ +
        ‖iteratedFDeriv ℝ l (coefA2Fam p.ν p.c p.train) x‖ +
        ‖iteratedFDeriv ℝ l (Jet.B2.fluctB2 p.ν p.c p.train) x‖ +
        ‖iteratedFDeriv ℝ l (fluctB3 p.ν p.c p.train) x‖ := by
    have h01 : ‖iteratedFDeriv ℝ l (fluctPolyMerid p) x‖ ≤
        ‖iteratedFDeriv ℝ l F0 x‖ + ‖iteratedFDeriv ℝ l F1 x‖ := by
      rw [hsumF]; exact norm_add_le _ _
    linarith
  have hW0 : 0 ≤ (1 + m.2.2 ^ 2 / m.1) ^ 2 := by positivity
  have hb1 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l (fluctA1 p.ν p.c p.train) x‖ ≤
      B1 * m.1 ^ (-(N : ℝ)) := hbd1 x hx1 l hl
  have hb2 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l (fluctB1 p.ν p.c p.train) x‖ ≤
      B2 * m.1 ^ (-(N : ℝ)) := hbd2 x hx1 l hl
  have hb3 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l (coefA2Fam p.ν p.c p.train) x‖ ≤
      B3 * m.1 ^ (-(N : ℝ)) := hbd3 x hx1 l hl
  have hb4 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l (Jet.B2.fluctB2 p.ν p.c p.train) x‖ ≤
      B4 * m.1 ^ (-(N : ℝ)) := hbd4 x hx1 l hl
  have hb5 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l (fluctB3 p.ν p.c p.train) x‖ ≤
      B5 * m.1 ^ (-(N : ℝ)) := hbd5 x hx1 l hl
  have hWtot := mul_le_mul_of_nonneg_left htot hW0
  linarith

end LateHeatDecomp2Sub

/-! ### Step 7: Directional-partial interface and four mean-block heat-split leaves -/

/-- Directional-partial formulation of the late-age finite-order heat decomposition:
the remainder chart profile `r_rem` is given by smooth `ProfilePoint → ℝ` radial and axial
components `f₀, f₁` whose mixed directional partials `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] ·))`
(`ℓ, a, b ≤ 2`) satisfy the normalized-weight late decay `B s^{-N}` on `1 ≤ s`. -/
def ResMeridLateHeatSplit2 : Prop :=
  ∀ N : ℕ, ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
      ∃ (F_heat : UnforcedLeray.Space → UnforcedLeray.Space)
        (r_rem : ℝ × (ℝ × ℝ) → Axi.Merid) (f₀ f₁ : ProfilePoint → ℝ) (C_heat B : ℝ),
        0 ≤ B ∧
        ContDiff ℝ ∞ F_heat ∧
        ContDiffOn ℝ ∞ f₀ ageDomain ∧
        ContDiffOn ℝ ∞ f₁ ageDomain ∧
        (∀ m : ℝ × (ℝ × ℝ), 0 < m.1 →
          r_rem m =
            f₀ (chartSwap m) • LateHeatDecomp2Sub.meridE0 +
              f₁ (chartSwap m) • LateHeatDecomp2Sub.meridE1) ∧
        (∀ (τ : ℝ) (z : UnforcedLeray.Space), z ∉ Axi.axis →
          Axi.age p.R z • Axi.Nv p.R (resChartProfile p) τ z =
            F_heat z + Axi.age p.R z • Axi.Nv p.R r_rem τ z) ∧
        (∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ p.R →
          (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 F_heat y‖ ≤ C_heat) ∧
        (∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
          (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
            |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f₀))) x| ≤ B * x.2.2 ^ (-(N : ℝ))) ∧
        (∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
          (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
            |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f₁))) x| ≤ B * x.2.2 ^ (-(N : ℝ)))

/-- **Target `resProfileLateHeatDecomp2` conditional on `ResMeridLateHeatSplit2`.** -/
theorem resProfileLateHeatDecomp2_of (h : ResMeridLateHeatSplit2) : ResProfileLateHeatDecomp2 := by
  intro N
  obtain ⟨ν₀, hν₀, H⟩ := h N
  refine ⟨ν₀, hν₀, fun p htr hν hc hR hP => ?_⟩
  obtain ⟨F_heat, r_rem, f₀, f₁, C_heat, B, hB0, hF_sm, hf₀, hf₁, h_eq, hdecomp, hF_bd,
    hpart₀, hpart₁⟩ := H p htr hν hc hR hP
  obtain ⟨hrem_sm, hrem_bd⟩ :=
    LateHeatDecomp2Sub.wtd_late_jet2_of_merid_partials hf₀ hf₁ h_eq hB0 hpart₀ hpart₁
  exact ⟨F_heat, r_rem, C_heat, 18 * B, hF_sm, hrem_sm, hdecomp, hF_bd, hrem_bd⟩

/-- Combined reduction of `RawResidualD2AxialTail` to `TrainFluctuationDecay`,
`TrainMeanExpansion`, and `ResMeridLateHeatSplit2`. -/
theorem rawResidualD2AxialTail_of_partI_and_lateSplit
    (hF : TrainFluctuationDecay) (hM : TrainMeanExpansion)
    (hLate : ResMeridLateHeatSplit2) :
    RawResidualD2AxialTail :=
  rawResidualD2AxialTail_of_early_and_late
    (resProfileEarlyJet2_of_partI hF hM)
    (resProfileLateHeatDecomp2_of hLate)

/-- Fixed-order `N` late heat decomposition for a scalar block profile `M p : ProfilePoint → ℝ`
along a unit meridional vector `v : Axi.Merid` (`∀ N : ℕ` outside `∃ ν₀ : ℝ`, matching
`TrainMeanExpansion` and `LateMeanRemainder` per `the November 2 reference manuscript`, lines 247-258,
447-459). -/
def ScalarMeridLateHeatSplit2At (M : Params → ProfilePoint → ℝ) (v : Axi.Merid) (N : ℕ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
      ∃ (F_heat : UnforcedLeray.Space → UnforcedLeray.Space)
        (f_rem : ProfilePoint → ℝ) (C_heat B : ℝ),
        0 ≤ B ∧
        ContDiff ℝ ∞ F_heat ∧
        ContDiffOn ℝ ∞ f_rem ageDomain ∧
        (∀ (τ : ℝ) (z : UnforcedLeray.Space), z ∉ Axi.axis →
          Axi.age p.R z • Axi.Nv p.R (fun m => M p (chartSwap m) • v) τ z =
            F_heat z + Axi.age p.R z • Axi.Nv p.R (fun m => f_rem (chartSwap m) • v) τ z) ∧
        (∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ p.R →
          (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 F_heat y‖ ≤ C_heat) ∧
        (∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
          (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
            |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f_rem))) x| ≤ B * x.2.2 ^ (-(N : ℝ)))

/-- Generic late heat decomposition for a scalar block profile `M p : ProfilePoint → ℝ` along a
unit meridional vector `v : Axi.Merid`. -/
def ScalarMeridLateHeatSplit2 (M : Params → ProfilePoint → ℝ) (v : Axi.Merid) : Prop :=
  ∀ N : ℕ, ScalarMeridLateHeatSplit2At M v N

/-- **Leaf 1 (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/1`)**: late-age finite-order heat decomposition
for the linear radial mean block `ringEps p.R ^ 2 * meanB1` along `meridE0`
(`the November 2 reference manuscript`, lines 1255, 1310-1325, 2548-2551). -/
def MeanBlockB1LateHeatSplit2 : Prop :=
  ScalarMeridLateHeatSplit2
    (fun p x => ringEps p.R ^ 2 * LateHeatDecomp2Sub.meanB1 p.ν p.c p.train x)
    LateHeatDecomp2Sub.meridE0

/-- **Leaf 2 (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/2`)**: late-age finite-order heat decomposition
for the linear axial mean block `ringEps p.R ^ 3 * meanB3` along `meridE1`
(`the November 2 reference manuscript`, lines 1258, 1310-1325, 2548-2551). -/
def MeanBlockB3LateHeatSplit2 : Prop :=
  ScalarMeridLateHeatSplit2
    (fun p x => ringEps p.R ^ 3 * LateHeatDecomp2Sub.meanB3 p.ν p.c p.train x)
    LateHeatDecomp2Sub.meridE1

/-- **Leaf 3 (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/3`)**: late-age finite-order heat decomposition
for the quadratic radial mean block `ringEps p.R * meanA1` along `meridE0`
(`the November 2 reference manuscript`, lines 1251, 1310-1325, 2548-2551). -/
def MeanBlockA1LateHeatSplit2 : Prop :=
  ScalarMeridLateHeatSplit2
    (fun p x => ringEps p.R * LateHeatDecomp2Sub.meanA1 p.ν p.c p.train x)
    LateHeatDecomp2Sub.meridE0

/-- **Leaf 4 (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/4`)**: late-age finite-order heat decomposition
for the quadratic axial mean block `ringEps p.R ^ 2 * Jet.B2.meanB2` along `meridE1`
(`the November 2 reference manuscript`, lines 1256, 1310-1325, 2548-2551). -/
def MeanBlockB2LateHeatSplit2 : Prop :=
  ScalarMeridLateHeatSplit2
    (fun p x => ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train x)
    LateHeatDecomp2Sub.meridE1

namespace LateHeatDecomp2Sub

/-- Converts the directional-partial remainder bound of `ScalarMeridLateHeatSplit2` into the
chart-profile `iteratedFDeriv` bound on `{m | 0 < m.1}`. -/
theorem scalar_rem_jet2 {f_rem : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f_rem ageDomain)
    {v : Axi.Merid} (hv : ‖v‖ ≤ 1) {B : ℝ} (hB0 : 0 ≤ B) {N : ℕ}
    (hpart : ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
      (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
        |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f_rem))) x| ≤ B * x.2.2 ^ (-(N : ℝ))) :
    ContDiffOn ℝ ∞ (fun m => f_rem (chartSwap m) • v) {m : ℝ × (ℝ × ℝ) | 0 < m.1} ∧
      ∀ m : ℝ × (ℝ × ℝ), 1 ≤ m.1 → ∀ l ≤ 2,
        (1 + m.2.2 ^ 2 / m.1) ^ 2 *
          ‖iteratedFDeriv ℝ l (fun w => f_rem (chartSwap w) • v) m‖ ≤
            9 * B * m.1 ^ (-(N : ℝ)) := by
  have hsm : ContDiffOn ℝ ∞ (fun x : ProfilePoint => f_rem x • v) ageDomain :=
    hf.smul contDiffOn_const
  refine ⟨hsm.comp chartSwapLIE.contDiff.contDiffOn (fun m hm => hm), fun m hm l hl => ?_⟩
  rw [norm_iteratedFDeriv_comp_chartSwap (fun x : ProfilePoint => f_rem x • v) m l]
  set x : ProfilePoint := chartSwap m
  have hx1 : 1 ≤ x.2.2 := hm
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  set W : ℝ := (1 + m.2.2 ^ 2 / m.1) ^ 2
  have hW0 : 0 ≤ W := by unfold W; positivity
  have hBN0 : 0 ≤ B * m.1 ^ (-(N : ℝ)) := mul_nonneg hB0 (Real.rpow_nonneg hx0.le _)
  have hjet := wtd_norm_iteratedFDeriv_le_of_partials hf hx0 hW0 hBN0 (hpart x hx1) hl
  have cf : ContDiffAt ℝ ∞ f_rem x :=
    hf.contDiffAt (FarDecaySub.isOpen_ageDomain.mem_nhds hx0)
  have hsmul := norm_iteratedFDeriv_smul_merid_le cf v hv l
  calc W * ‖iteratedFDeriv ℝ l (fun y : ProfilePoint => f_rem y • v) x‖
      ≤ W * ‖iteratedFDeriv ℝ l f_rem x‖ := mul_le_mul_of_nonneg_left hsmul hW0
    _ ≤ 9 * (B * m.1 ^ (-(N : ℝ))) := hjet
    _ = 9 * B * m.1 ^ (-(N : ℝ)) := by ring

/-- Pointwise decomposition of `resChartProfile p m` into the four mean blocks plus the
fluctuation/pressure/`A₂` profile on `{m | 0 < m.1}`. -/
theorem resChartProfile_eq_blocks_add_fluct (p : Params) (htr : IsBUCTrain p.train)
    {m : ℝ × (ℝ × ℝ)} (hm : 0 < m.1) :
    resChartProfile p m =
      (ringEps p.R ^ 2 * meanB1 p.ν p.c p.train (chartSwap m)) • meridE0 +
        (ringEps p.R ^ 3 * meanB3 p.ν p.c p.train (chartSwap m)) • meridE1 +
        (ringEps p.R * meanA1 p.ν p.c p.train (chartSwap m)) • meridE0 +
        (ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train (chartSwap m)) • meridE1 +
        fluctPolyMerid p (chartSwap m) := by
  rw [resChartProfile_eq_resPolyMerid p htr hm]
  set x : ProfilePoint := chartSwap m
  have hA1 := coefA1_eq_add_fluctA1 p.ν p.c p.train x
  have hB1 := coefB1_eq_add_fluctB1 p.ν p.c p.train x
  have hB2 : coeffB₂ p.ν (trainProfile p.train.ψ) x =
      Jet.B2.meanB2 p.ν p.c p.train x + Jet.B2.fluctB2 p.ν p.c p.train x := by
    simp [Jet.B2.fluctB2, Jet.B2.coefB2, Jet.coefFam]
  have hB3 := coefB3_eq_add_fluctB3 p.ν p.c p.train x
  have hA2 : coeffA₂ p.ν (trainProfile p.train.ψ) x = coefA2Fam p.ν p.c p.train x := rfl
  ext i
  fin_cases i <;>
    simp [resPolyMerid, fluctPolyMerid, meridE0, meridE1, trainStream, trainPressure,
      hA1, hB1, hB2, hB3, hA2] <;> ring

end LateHeatDecomp2Sub

/-- **Assembly of `ResProfileLateHeatDecomp2` from the four mean-block heat-split leaves.** -/
theorem resProfileLateHeatDecomp2_of_blocks
    (hB1 : MeanBlockB1LateHeatSplit2)
    (hB3 : MeanBlockB3LateHeatSplit2)
    (hA1 : MeanBlockA1LateHeatSplit2)
    (hB2 : MeanBlockB2LateHeatSplit2) :
    ResProfileLateHeatDecomp2 := by
  intro N
  obtain ⟨ν1, hν1, HB1⟩ := hB1 N
  obtain ⟨ν2, hν2, HB3⟩ := hB3 N
  obtain ⟨ν3, hν3, HA1⟩ := hA1 N
  obtain ⟨ν4, hν4, HB2⟩ := hB2 N
  obtain ⟨ν5, hν5, HFl⟩ := LateHeatDecomp2Sub.fluctPolyMerid_late_jet2
  refine ⟨min (min (min (min ν1 ν2) ν3) ν4) ν5,
    lt_min (lt_min (lt_min (lt_min hν1 hν2) hν3) hν4) hν5,
    fun p htr hν hc hR hP => ?_⟩
  obtain ⟨F1, f1, C1, B1, hB1_0, hF1_sm, hf1_sm, hdec1, hF1_bd, hpart1⟩ :=
    HB1 p htr (lt_of_lt_of_le hν (by simp)) hc hR hP
  obtain ⟨F2, f2, C2, B2, hB2_0, hF2_sm, hf2_sm, hdec2, hF2_bd, hpart2⟩ :=
    HB3 p htr (lt_of_lt_of_le hν (by simp)) hc hR hP
  obtain ⟨F3, f3, C3, B3, hB3_0, hF3_sm, hf3_sm, hdec3, hF3_bd, hpart3⟩ :=
    HA1 p htr (lt_of_lt_of_le hν (by simp)) hc hR hP
  obtain ⟨F4, f4, C4, B4, hB4_0, hF4_sm, hf4_sm, hdec4, hF4_bd, hpart4⟩ :=
    HB2 p htr (lt_of_lt_of_le hν (by simp)) hc hR hP
  obtain ⟨hr5_sm, HFl_N⟩ := HFl p htr (lt_of_lt_of_le hν (by simp)) hc hR
  obtain ⟨B5, hB5_0, hr5_bd⟩ := HFl_N N
  let r1 : ℝ × (ℝ × ℝ) → Axi.Merid := fun m => f1 (chartSwap m) • LateHeatDecomp2Sub.meridE0
  let r2 : ℝ × (ℝ × ℝ) → Axi.Merid := fun m => f2 (chartSwap m) • LateHeatDecomp2Sub.meridE1
  let r3 : ℝ × (ℝ × ℝ) → Axi.Merid := fun m => f3 (chartSwap m) • LateHeatDecomp2Sub.meridE0
  let r4 : ℝ × (ℝ × ℝ) → Axi.Merid := fun m => f4 (chartSwap m) • LateHeatDecomp2Sub.meridE1
  let r5 : ℝ × (ℝ × ℝ) → Axi.Merid := fun m => LateHeatDecomp2Sub.fluctPolyMerid p (chartSwap m)
  obtain ⟨hr1_sm, hr1_bd⟩ :=
    LateHeatDecomp2Sub.scalar_rem_jet2 hf1_sm norm_merid_e0.le hB1_0 hpart1
  obtain ⟨hr2_sm, hr2_bd⟩ :=
    LateHeatDecomp2Sub.scalar_rem_jet2 hf2_sm norm_merid_e1.le hB2_0 hpart2
  obtain ⟨hr3_sm, hr3_bd⟩ :=
    LateHeatDecomp2Sub.scalar_rem_jet2 hf3_sm norm_merid_e0.le hB3_0 hpart3
  obtain ⟨hr4_sm, hr4_bd⟩ :=
    LateHeatDecomp2Sub.scalar_rem_jet2 hf4_sm norm_merid_e1.le hB4_0 hpart4
  let F_heat : UnforcedLeray.Space → UnforcedLeray.Space :=
    fun y => F1 y + F2 y + F3 y + F4 y
  let r_rem : ℝ × (ℝ × ℝ) → Axi.Merid :=
    fun m => r1 m + r2 m + r3 m + r4 m + r5 m
  have hF_sm : ContDiff ℝ ∞ F_heat :=
    (((hF1_sm.add hF2_sm).add hF3_sm).add hF4_sm)
  have hr_sm : ContDiffOn ℝ ∞ r_rem {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    ((((hr1_sm.add hr2_sm).add hr3_sm).add hr4_sm).add hr5_sm)
  refine ⟨F_heat, r_rem, C1 + C2 + C3 + C4,
    9 * B1 + 9 * B2 + 9 * B3 + 9 * B4 + B5, hF_sm, hr_sm, ?_, ?_, ?_⟩
  · intro τ z hz
    have hR0 : 0 < p.R := by linarith
    have hchart_pos : 0 < (Axi.chart p.R τ z).1 := by
      show 0 < Axi.age p.R z
      unfold Axi.age
      exact div_pos (pow_pos hR0 2) (pow_pos (Axi.ϱ_pos hz) 2)
    have hpt := LateHeatDecomp2Sub.resChartProfile_eq_blocks_add_fluct p htr hchart_pos
    have hNv_eq :
        Axi.Nv p.R (resChartProfile p) τ z =
          Axi.Nv p.R (fun m =>
            (ringEps p.R ^ 2 * LateHeatDecomp2Sub.meanB1 p.ν p.c p.train (chartSwap m)) •
              LateHeatDecomp2Sub.meridE0) τ z +
          Axi.Nv p.R (fun m =>
            (ringEps p.R ^ 3 * LateHeatDecomp2Sub.meanB3 p.ν p.c p.train (chartSwap m)) •
              LateHeatDecomp2Sub.meridE1) τ z +
          Axi.Nv p.R (fun m =>
            (ringEps p.R * LateHeatDecomp2Sub.meanA1 p.ν p.c p.train (chartSwap m)) •
              LateHeatDecomp2Sub.meridE0) τ z +
          Axi.Nv p.R (fun m =>
            (ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train (chartSwap m)) •
              LateHeatDecomp2Sub.meridE1) τ z +
          Axi.Nv p.R r5 τ z := by
      simp only [Axi.Nv, r5, hpt, map_add, smul_add]
    have hNv_rem :
        Axi.Nv p.R r_rem τ z =
          Axi.Nv p.R r1 τ z + Axi.Nv p.R r2 τ z + Axi.Nv p.R r3 τ z +
            Axi.Nv p.R r4 τ z + Axi.Nv p.R r5 τ z := by
      simp only [Axi.Nv, r_rem, map_add, smul_add]
    have hd1 := hdec1 τ z hz
    have hd2 := hdec2 τ z hz
    have hd3 := hdec3 τ z hz
    have hd4 := hdec4 τ z hz
    rw [hNv_eq, hNv_rem]
    simp only [F_heat, r1, r2, r3, r4, smul_add]
    rw [hd1, hd2, hd3, hd4]
    abel
  · intro y hy
    have c1 : ContDiffAt ℝ 2 F1 y := hF1_sm.contDiffAt.of_le (by norm_num)
    have c2 : ContDiffAt ℝ 2 F2 y := hF2_sm.contDiffAt.of_le (by norm_num)
    have c3 : ContDiffAt ℝ 2 F3 y := hF3_sm.contDiffAt.of_le (by norm_num)
    have c4 : ContDiffAt ℝ 2 F4 y := hF4_sm.contDiffAt.of_le (by norm_num)
    have hadd1 : iteratedFDeriv ℝ 2 F_heat y =
        iteratedFDeriv ℝ 2 (fun z => F1 z + F2 z + F3 z) y + iteratedFDeriv ℝ 2 F4 y :=
      iteratedFDeriv_add_apply ((c1.add c2).add c3) c4
    have hadd2 : iteratedFDeriv ℝ 2 (fun z => F1 z + F2 z + F3 z) y =
        iteratedFDeriv ℝ 2 (fun z => F1 z + F2 z) y + iteratedFDeriv ℝ 2 F3 y :=
      iteratedFDeriv_add_apply (c1.add c2) c3
    have hadd3 : iteratedFDeriv ℝ 2 (fun z => F1 z + F2 z) y =
        iteratedFDeriv ℝ 2 F1 y + iteratedFDeriv ℝ 2 F2 y :=
      iteratedFDeriv_add_apply c1 c2
    have hnorm : ‖iteratedFDeriv ℝ 2 F_heat y‖ ≤
        ‖iteratedFDeriv ℝ 2 F1 y‖ + ‖iteratedFDeriv ℝ 2 F2 y‖ +
          ‖iteratedFDeriv ℝ 2 F3 y‖ + ‖iteratedFDeriv ℝ 2 F4 y‖ := by
      rw [hadd1, hadd2, hadd3]
      calc ‖iteratedFDeriv ℝ 2 F1 y + iteratedFDeriv ℝ 2 F2 y +
              iteratedFDeriv ℝ 2 F3 y + iteratedFDeriv ℝ 2 F4 y‖
          ≤ ‖iteratedFDeriv ℝ 2 F1 y + iteratedFDeriv ℝ 2 F2 y +
              iteratedFDeriv ℝ 2 F3 y‖ + ‖iteratedFDeriv ℝ 2 F4 y‖ := norm_add_le _ _
        _ ≤ ‖iteratedFDeriv ℝ 2 F1 y + iteratedFDeriv ℝ 2 F2 y‖ +
              ‖iteratedFDeriv ℝ 2 F3 y‖ + ‖iteratedFDeriv ℝ 2 F4 y‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ‖iteratedFDeriv ℝ 2 F1 y‖ + ‖iteratedFDeriv ℝ 2 F2 y‖ +
              ‖iteratedFDeriv ℝ 2 F3 y‖ + ‖iteratedFDeriv ℝ 2 F4 y‖ :=
            add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    have hW : 0 ≤ 1 + y 2 ^ 2 := by positivity
    have hWnorm := mul_le_mul_of_nonneg_left hnorm hW
    linarith [hF1_bd y hy, hF2_bd y hy, hF3_bd y hy, hF4_bd y hy]
  · intro m hm1 l hl
    have hm0 : 0 < m.1 := lt_of_lt_of_le one_pos hm1
    have hopen : IsOpen {w : ℝ × (ℝ × ℝ) | 0 < w.1} := isOpen_lt continuous_const continuous_fst
    have hnhds : {w : ℝ × (ℝ × ℝ) | 0 < w.1} ∈ 𝓝 m := hopen.mem_nhds hm0
    have c1 : ContDiffAt ℝ l r1 m :=
      (hr1_sm.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
    have c2 : ContDiffAt ℝ l r2 m :=
      (hr2_sm.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
    have c3 : ContDiffAt ℝ l r3 m :=
      (hr3_sm.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
    have c4 : ContDiffAt ℝ l r4 m :=
      (hr4_sm.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
    have c5 : ContDiffAt ℝ l r5 m :=
      (hr5_sm.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
    have hadd1 : iteratedFDeriv ℝ l r_rem m =
        iteratedFDeriv ℝ l (fun w => r1 w + r2 w + r3 w + r4 w) m + iteratedFDeriv ℝ l r5 m :=
      iteratedFDeriv_add_apply (((c1.add c2).add c3).add c4) c5
    have hadd2 : iteratedFDeriv ℝ l (fun w => r1 w + r2 w + r3 w + r4 w) m =
        iteratedFDeriv ℝ l (fun w => r1 w + r2 w + r3 w) m + iteratedFDeriv ℝ l r4 m :=
      iteratedFDeriv_add_apply ((c1.add c2).add c3) c4
    have hadd3 : iteratedFDeriv ℝ l (fun w => r1 w + r2 w + r3 w) m =
        iteratedFDeriv ℝ l (fun w => r1 w + r2 w) m + iteratedFDeriv ℝ l r3 m :=
      iteratedFDeriv_add_apply (c1.add c2) c3
    have hadd4 : iteratedFDeriv ℝ l (fun w => r1 w + r2 w) m =
        iteratedFDeriv ℝ l r1 m + iteratedFDeriv ℝ l r2 m :=
      iteratedFDeriv_add_apply c1 c2
    have hnorm : ‖iteratedFDeriv ℝ l r_rem m‖ ≤
        ‖iteratedFDeriv ℝ l r1 m‖ + ‖iteratedFDeriv ℝ l r2 m‖ +
          ‖iteratedFDeriv ℝ l r3 m‖ + ‖iteratedFDeriv ℝ l r4 m‖ +
          ‖iteratedFDeriv ℝ l r5 m‖ := by
      rw [hadd1, hadd2, hadd3, hadd4]
      calc ‖iteratedFDeriv ℝ l r1 m + iteratedFDeriv ℝ l r2 m +
              iteratedFDeriv ℝ l r3 m + iteratedFDeriv ℝ l r4 m +
              iteratedFDeriv ℝ l r5 m‖
          ≤ ‖iteratedFDeriv ℝ l r1 m + iteratedFDeriv ℝ l r2 m +
              iteratedFDeriv ℝ l r3 m + iteratedFDeriv ℝ l r4 m‖ +
              ‖iteratedFDeriv ℝ l r5 m‖ := norm_add_le _ _
        _ ≤ ‖iteratedFDeriv ℝ l r1 m + iteratedFDeriv ℝ l r2 m +
              iteratedFDeriv ℝ l r3 m‖ + ‖iteratedFDeriv ℝ l r4 m‖ +
              ‖iteratedFDeriv ℝ l r5 m‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ‖iteratedFDeriv ℝ l r1 m + iteratedFDeriv ℝ l r2 m‖ +
              ‖iteratedFDeriv ℝ l r3 m‖ + ‖iteratedFDeriv ℝ l r4 m‖ +
              ‖iteratedFDeriv ℝ l r5 m‖ :=
            add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
        _ ≤ ‖iteratedFDeriv ℝ l r1 m‖ + ‖iteratedFDeriv ℝ l r2 m‖ +
              ‖iteratedFDeriv ℝ l r3 m‖ + ‖iteratedFDeriv ℝ l r4 m‖ +
              ‖iteratedFDeriv ℝ l r5 m‖ :=
            add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl
    have hW0 : 0 ≤ (1 + m.2.2 ^ 2 / m.1) ^ 2 := by positivity
    have hWnorm := mul_le_mul_of_nonneg_left hnorm hW0
    have hb1 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l r1 m‖ ≤ 9 * B1 * m.1 ^ (-(N : ℝ)) :=
      hr1_bd m hm1 l hl
    have hb2 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l r2 m‖ ≤ 9 * B2 * m.1 ^ (-(N : ℝ)) :=
      hr2_bd m hm1 l hl
    have hb3 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l r3 m‖ ≤ 9 * B3 * m.1 ^ (-(N : ℝ)) :=
      hr3_bd m hm1 l hl
    have hb4 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l r4 m‖ ≤ 9 * B4 * m.1 ^ (-(N : ℝ)) :=
      hr4_bd m hm1 l hl
    have hb5 : (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l r5 m‖ ≤ B5 * m.1 ^ (-(N : ℝ)) :=
      hr5_bd m hm1 l hl
    linarith

/-- Combined reduction of `RawResidualD2AxialTail` to the four mean-block heat-split leaves
(using the unconditionally proved `resProfileEarlyJet2` from `EarlyJet2.lean`). -/
theorem rawResidualD2AxialTail_of_blocks
    (hB1 : MeanBlockB1LateHeatSplit2)
    (hB3 : MeanBlockB3LateHeatSplit2)
    (hA1 : MeanBlockA1LateHeatSplit2)
    (hB2 : MeanBlockB2LateHeatSplit2) :
    RawResidualD2AxialTail :=
  rawResidualD2AxialTail_of_early_and_late
    resProfileEarlyJet2
    (resProfileLateHeatDecomp2_of_blocks hB1 hB3 hA1 hB2)

end UnforcedLeray.Short.PartIIIb.Concrete
