import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_org
import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed

/-!
# Part II-b, organizer `PartII-b:G4/4/1/1/2/1/1/org`: `TrainHeatExpansion` from the fixed-parameter Part I fact

Source of record: `the November 2 reference manuscript` (SP).

`TrainHeatExpansion` (`Sub/PartII-b_G4_4_1_1_2_org.lean`, SP 438-459 with 429-435) is the
all-order heat expansion of the train stream at fixed parameters.  Its non-analytic content is the
Part I fact `PartI.TrainHeatFixed` (`Short/PartI/Sub/PartI_TrainHeatFixed.lean`): one threshold
`ν₀` before the orders; for each train and order, `D^i ψ̃ = O(e^{-κ s})` (SP 440-445, fluctuation)
and `D^i R_N = O(s^{-N-3/2})` (SP 455-458 at `m = 0`, `p = ∞`, mean remainder).

The reduction proved here is calculus.  With `L(s, q, η) = (s, η)`:
`heatRemainder ν a N Ψ = R_N ∘ L + (ψ − S ∘ L)` where `Ψ = ψ`, `a = meanCoeff`, `S = meanStream`
and `R_N = meanRemainder` (the heat terms depend only on `(s, η)`), both summands are `C^∞` for
`s > 0` (`TrainStreamSmooth`, `TrainMeanEquations`, `HeatTermSmooth`), the derivative of `R_N ∘ L`
has norm `≤ ‖D^i R_N‖ ‖L‖^i` (`ContinuousLinearMap.iteratedFDerivWithin_comp_right`), and
`e^{-κ s} ≤ K s^{-N-2} ≤ K s^{-N-3/2}` for `s ≥ 1`.

The same fixed-parameter fact (`PartI.TrainHeatFixed`) is what PartII-a:R06 (`RingAxisSmooth`, all
`ρ > 1/2`), PartII-b:R1/6 and PartII-b:G1/4 need for `C^∞` through the axis (they can reuse
`ParityOfExpansion` of `Sub/PartII-b_G4_4_1_1_2_org.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartI

/-- `e^{-κ s} ≤ K s^{-N-3/2}` for `s ≥ 1`, with `K` depending only on `κ > 0` and `N`. -/
theorem exp_neg_le_rpow (κ : ℝ) (hκ : 0 < κ) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 1 ≤ s →
      Real.exp (-(κ * s)) ≤ K * s ^ (-(N : ℝ) - 3 / 2) := by
  refine ⟨((N + 2).factorial : ℝ) / κ ^ (N + 2), by positivity, fun s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have h1 := Real.pow_div_factorial_le_exp (x := κ * s) (by positivity) (N + 2)
  have hfac : (0 : ℝ) < ((N + 2).factorial : ℝ) := by positivity
  have hκp : 0 < κ ^ (N + 2) := by positivity
  have h2 : s ^ (N + 2) ≤ ((N + 2).factorial : ℝ) / κ ^ (N + 2) * Real.exp (κ * s) := by
    rw [mul_pow, div_le_iff₀ hfac] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hκp]
    nlinarith [h1]
  have h3 : s ^ (N + 3 / 2 : ℝ) ≤ s ^ (N + 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hs (by push_cast; linarith)
  have h4 : 0 < s ^ (-(N : ℝ) - 3 / 2) := Real.rpow_pos_of_pos hs0 _
  have h5 : s ^ (-(N : ℝ) - 3 / 2) * s ^ ((N : ℝ) + 3 / 2) = 1 := by
    rw [← Real.rpow_add hs0]; simp
  have h6 : Real.exp (-(κ * s)) = (Real.exp (κ * s))⁻¹ := by rw [Real.exp_neg]
  rw [h6]
  have hex : 0 < Real.exp (κ * s) := Real.exp_pos _
  rw [inv_le_iff_one_le_mul₀ hex]
  have : (1 : ℝ) ≤ ((N + 2).factorial : ℝ) / κ ^ (N + 2) * s ^ (-(N : ℝ) - 3 / 2) *
      Real.exp (κ * s) := by
    calc (1 : ℝ) = s ^ (-(N : ℝ) - 3 / 2) * s ^ ((N : ℝ) + 3 / 2) := h5.symm
      _ ≤ s ^ (-(N : ℝ) - 3 / 2) * s ^ (N + 2) := by
        gcongr
      _ ≤ s ^ (-(N : ℝ) - 3 / 2) * (((N + 2).factorial : ℝ) / κ ^ (N + 2) *
            Real.exp (κ * s)) := by gcongr
      _ = _ := by ring
  linarith

/-- **`TrainHeatExpansion` from the fixed-parameter Part I fact** (SP 438-459 with 429-435). -/
theorem trainHeatExpansion_of (hS : TrainStreamSmooth) (hM : TrainMeanEquations)
    (hH : HeatTermSmooth) (h : TrainHeatFixed) : TrainHeatExpansion := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, h'⟩ := h ρ hρ
  refine ⟨ν₀, hν₀, fun ν c hν hle hc tr htr N i => ?_⟩
  subst hc
  obtain ⟨hF, hR⟩ := h' ν hν hle tr htr
  obtain ⟨C1, κ, hκ, hC1⟩ := hF i
  obtain ⟨C2, hC2⟩ := hR N i
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
  rw [hsplit, ← iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_add_apply
      ((hf1.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top))
      ((hf2.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)) hUo.uniqueDiffOn hyU]
  have hcomp := L.iteratedFDerivWithin_comp_right hΦ1 hU2o.uniqueDiffOn
    (hpre ▸ hUo.uniqueDiffOn) hyU2 (i := i) (by exact_mod_cast le_top)
  rw [hpre] at hcomp
  rw [hcomp, iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_of_isOpen i hU2o hyU2]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖(iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)).compContinuousLinearMap
      fun _ => L‖ ≤ C2 * y.1 ^ (-(N : ℝ) - 3 / 2) := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ _i : Fin i, ‖L‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) hLnorm
    have h2 := hC2 (L y) (by simpa [hL] using hy)
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)‖ :=
      norm_nonneg _
    calc _ ≤ ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ _ := by simpa [hL] using h2
  have hB : ‖iteratedFDeriv ℝ i
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ ≤
        C1 * K * y.1 ^ (-(N : ℝ) - 3 / 2) := by
    calc _ ≤ C1 * Real.exp (-(κ * y.1)) := hC1 y hy
      _ ≤ C1 * (K * y.1 ^ (-(N : ℝ) - 3 / 2)) := by
        gcongr
        · have := (norm_nonneg (iteratedFDeriv ℝ i
            (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y))
          have h := hC1 y hy
          have hpos := Real.exp_pos (-(κ * y.1))
          by_contra hneg
          push_neg at hneg
          nlinarith
        · exact hKe y.1 hy
      _ = _ := by ring
  calc _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

end UnforcedLeray.Short.IIb
