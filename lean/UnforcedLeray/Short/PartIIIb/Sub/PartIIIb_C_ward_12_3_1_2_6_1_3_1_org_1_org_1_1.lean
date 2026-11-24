import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_1_1_org

/-!
# `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/1`: `TrainHeatRemWtd`, decomposed

Source `the November 2 reference manuscript`
439-458 (`sct:fluctuation` with weights `<eta>^m`, `sct:expansion` remainder with weights
`eta^m`, `p = infinity`) at fixed parameters 427-435.

The weighted fixed-parameter Part I facts `TrainFluctWtdFixed`, `TrainMeanRemWtdFixed` are the two
source leaves; `trainHeatRemWtd_of` is the calculus reduction (same split as
`IIb.trainHeatExpansion_of`: `heatRemainder = R_N o L + (psi - S o L)`, `L(s,q,eta) = (s,eta)`;
the weight `(1+|eta|)^m` is unchanged by `L`, and `e^{-kappa s} <= K s^{-N-3/2} <= K s^{m/2-N-3/2}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI UnforcedLeray.Short.IIb

/-- **Weighted fluctuation at fixed parameters** (SP 440-445, weight `<eta>^m`, 427-435): one
`nu0` for `rho > 1/2`; for every BUC train with `nu <= nu0`, all `m, i`: there are `C`, `kappa > 0`
with `(1+|eta|)^m ||D^i (psi - S)(s,q,eta)|| <= C e^{-kappa s}` for `s >= 1`.  Weighted form of
`PartI.TrainFluctFixed`. -/
def TrainFluctWtdFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ m i : ℕ, ∃ C κ : ℝ, 0 < κ ∧
      ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
        (1 + |y.2.2|) ^ m * ‖iteratedFDeriv ℝ i
            (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ ≤
          C * Real.exp (-(κ * y.1))

/-- **Weighted mean remainder at fixed parameters** (SP 455-458, weights `eta^m`, `p = infinity`,
proof 527-551, fixed parameters 429-435): for every BUC train with `nu <= nu0` and all `N, m, i`
there is `C` with `(1+|eta|)^m ||D^i R_N(s,eta)|| <= C s^{m/2-N-3/2}` for `s >= 1`.  Weighted form
of `PartI.TrainMeanRemFixed`. -/
def TrainMeanRemWtdFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ N m i : ℕ, ∃ C : ℝ,
      ∀ y : ℝ × ℝ, 1 ≤ y.1 →
        (1 + |y.2|) ^ m * ‖iteratedFDeriv ℝ i
            (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) y‖ ≤
          C * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2)

theorem trainHeatRemWtd_of (hS : TrainStreamSmooth) (hM : TrainMeanEquations)
    (hH : HeatTermSmooth) (hA : TrainFluctWtdFixed) (hB : TrainMeanRemWtdFixed) :
    TrainHeatRemWtd := by
  intro ρ hρ
  obtain ⟨νA, hνA, hA'⟩ := hA ρ hρ
  obtain ⟨νB, hνB, hB'⟩ := hB ρ hρ
  refine ⟨min νA νB, lt_min hνA hνB, fun ν c hν hle hc tr htr N m i => ?_⟩
  subst hc
  obtain ⟨C1, κ, hκ, hC1⟩ := hA' ν hν (hle.trans (min_le_left _ _)) tr htr m i
  obtain ⟨C2, hC2⟩ := hB' ν hν (hle.trans (min_le_right _ _)) tr htr N m i
  obtain ⟨K, hK, hKe⟩ := exp_neg_le_rpow κ hκ N
  have hc0 : 0 < trainPeriod ρ ν := Real.rpow_pos_of_pos hν _
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hU2o : IsOpen U2 := isOpen_Ioi.prod isOpen_univ
  let L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  let ι : ℝ × ℝ →L[ℝ] ℝ × (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hL : ∀ x, L x = (x.1, x.2.2) := fun x => rfl
  have hι : ∀ x, ι x = (x.1, (0, x.2)) := fun x => rfl
  have hLnorm : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [hL, one_mul, Prod.norm_def, Prod.norm_def]
    simp only [Prod.norm_def]
    exact max_le (le_max_left _ _) ((le_max_right _ _).trans' (le_max_right _ _))
  have hLmaps : MapsTo L U U2 := fun x hx => by
    simp only [hL, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hιmaps : MapsTo ι U2 U := fun x hx => by
    simp only [hι, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hpre : L ⁻¹' U2 = U := by
    ext x
    simp only [hL, hUdef, hU2def, mem_preimage, mem_prod, mem_Ioi, mem_univ, and_true]
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) U := hS ν _ hν hc0 tr htr
  have hmean : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) U2 :=
    (hM ν _ hν hc0 tr htr).1
  have hmeanL : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => meanStream tr x.1 x.2.2) U :=
    hmean.comp L.contDiff.contDiffOn hLmaps
  have hheat : ∀ j : ℕ, ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => heatTerm ν j (ι x)) U2 := fun j =>
    (hH ν hν j).comp ι.contDiff.contDiffOn hιmaps
  have hΦ1eq : (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) =
      fun x => meanStream tr x.1 x.2 -
        ∑ j ∈ Finset.range (N + 1), meanCoeff tr j * heatTerm ν j (ι x) := by
    funext x
    simp [meanRemainder, heatTerm, hι]
  have hΦ1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) U2 := by
    rw [hΦ1eq]
    refine hmean.sub (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hheat j))
  have hf1 : ContDiffOn ℝ ∞ ((fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) ∘ L) U := by
    have := hΦ1.comp L.contDiff.contDiffOn (hpre ▸ subset_rfl : U ⊆ L ⁻¹' U2)
    exact this
  have hf2 : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) U := hψ.sub hmeanL
  have hsplit : heatRemainder ν (meanCoeff tr) N (fun y => tr.ψ y.1 y.2) =
      ((fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) ∘ L) +
        (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) := by
    funext y
    simp only [heatRemainder, meanRemainder, heatTerm, Pi.add_apply, Function.comp_apply, hL]
    ring
  refine ⟨C2 + C1 * K, fun y hy => ?_⟩
  have hyU : y ∈ U := by
    simp only [hUdef, mem_prod, mem_Ioi, mem_univ, and_true]; linarith
  have hyU2 : L y ∈ U2 := hLmaps hyU
  have hy0 : 0 < y.1 := by linarith
  have hw0 : 0 ≤ (1 + |y.2.2|) ^ m := by positivity
  rw [hsplit, ← iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_add_apply
      ((hf1.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top))
      ((hf2.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)) hUo.uniqueDiffOn hyU]
  have hcomp := L.iteratedFDerivWithin_comp_right hΦ1 hU2o.uniqueDiffOn
    (hpre ▸ hUo.uniqueDiffOn) hyU2 (i := i) (by exact_mod_cast le_top)
  rw [hpre] at hcomp
  rw [hcomp, iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_of_isOpen i hU2o hyU2]
  have hA : (1 + |y.2.2|) ^ m * ‖(iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)).compContinuousLinearMap
      fun _ => L‖ ≤ C2 * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
    have h1 : ∏ _i : Fin i, ‖L‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) hLnorm
    have h2 := hC2 (L y) (by simpa [hL] using hy)
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)‖ :=
      norm_nonneg _
    have h4 := (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y))
      (fun _ => L))
    calc _ ≤ (1 + |y.2.2|) ^ m *
          ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)‖ := by
          refine (mul_le_mul_of_nonneg_left h4 hw0).trans ?_
          have := mul_le_mul_of_nonneg_left h1 h3
          rw [mul_one] at this
          exact mul_le_mul_of_nonneg_left this hw0
      _ ≤ _ := by simpa [hL] using h2
  have hB : (1 + |y.2.2|) ^ m * ‖iteratedFDeriv ℝ i
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ ≤
        C1 * K * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
    have hpow : y.1 ^ (-(N : ℝ) - 3 / 2) ≤ y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) :=
      Real.rpow_le_rpow_of_exponent_le hy (by
        have : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
        linarith)
    have hC1nn : 0 ≤ C1 := by
      have h0 : 0 ≤ (1 + |y.2.2|) ^ m * ‖iteratedFDeriv ℝ i
          (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ := by positivity
      have h := hC1 y hy
      have hpos := Real.exp_pos (-(κ * y.1))
      by_contra hneg
      push_neg at hneg
      nlinarith
    calc _ ≤ C1 * Real.exp (-(κ * y.1)) := hC1 y hy
      _ ≤ C1 * (K * y.1 ^ (-(N : ℝ) - 3 / 2)) := by
        gcongr
        exact hKe y.1 hy
      _ ≤ C1 * (K * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2)) := by gcongr
      _ = _ := by ring
  calc _ ≤ (1 + |y.2.2|) ^ m * (‖(iteratedFDeriv ℝ i
        (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)).compContinuousLinearMap
        fun _ => L‖ + ‖iteratedFDeriv ℝ i
        (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw0
    _ = _ + _ := mul_add _ _ _
    _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
