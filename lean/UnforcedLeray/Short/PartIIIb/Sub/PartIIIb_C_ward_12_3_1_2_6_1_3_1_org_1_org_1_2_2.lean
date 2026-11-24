import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.TrainStreamWtdBdd_Sub
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromMixed1D

/-!
# Decomposition of `TrainMeanWtdBdd` (SP 456-457, fixed parameters SP 427-435)

Source: `the November 2 reference manuscript`.

`TrainMeanWtdBdd` (one threshold `ν₀` for all orders `m, i` and ages `S`) is a statement at fixed
parameters: its consumer `RingLiftOffAxisDerivBdd` needs all Cartesian orders `k` of the lift at the
same train (SP 1322-1325; SP 427-435: "All higher-order versions of the argument therefore hold at
fixed parameters, without requiring a new smallness condition for each order").  The quantitative
weighted bounds (`TrainMeanWtdMixed`, from `sct:transverse`, SP 460-467) carry a threshold fixed
after the derivative orders (SP 247-258: "fix a finite collection of derivative orders ... All the
smallness conditions below are satisfied by first fixing that collection and then decreasing
`e_c`").  The passage is the source's unit-patch interpolation (SP 494-496: "Unit-patch
interpolation with the fixed higher smooth bounds from Lemma sct:train gives the same tail, with
reduced exponent, for every required ... derivative"): the weighted order-`0` bound (threshold of
order `0`) and the unweighted bounds of every order at fixed parameters (`MeanJetsFixed`, SP 397-404
with SP 427-435) give every weighted order (`WtdJetInterp`, calculus).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff

/-- **Weighted mixed derivatives of the mean stream, bounded ages** (SP 456-457:
`‖η^m ∂_η^b ∂_s^ℓ S(s)‖_∞ ≤ P (1+s)^{(m-b-1)/2-ℓ}`, `s ≥ 0`; equivalently, at bounded ages, the
transverse tails `sct:transverse`, SP 460-467, averaged in `q`, SP 509-511).  The threshold `ν₀` is
fixed after the derivative orders `b, ℓ` (SP 247-258; as `PartI.TrainTransverseTails`,
`StatementsTrain.lean:284`, whose `ν₀` depends on `ρ, ℓ, j` and is fixed before the age bound):
for `ρ > 1/2` and orders `b, ℓ` there is `ν₀` such that for every BUC train with `ν ≤ ν₀`, every
weight `m` and age bound `S`: `(1+|η|)^m |∂_η^b ∂_s^ℓ S(s, η)| ≤ C` on `0 < s ≤ S`
(`∂_s^ℓ` first, as in `PartI.TrainMeanRemMixedFixed`). -/
def TrainMeanWtdMixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ b ℓ : ℕ, ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = Short.PartI.trainPeriod ρ ν →
    ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
      ∀ (m : ℕ) (S : ℝ), ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ S → ∀ η : ℝ,
        (1 + |η|) ^ m *
          ‖iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => Short.PartI.meanStream tr r e) s) η‖
            ≤ C

/-- **Unweighted jets of the mean stream of every order, at fixed parameters** (SP 397-404:
`S_η = -\bar v₁`, `S_s - ν S_ηη = g = \overline{v₁ v₂}`; SP 427-435: every mixed age/spatial jet of
`v` is bounded at fixed parameters, one threshold for all orders, `PartI.TrainJetsBoundedFixed`).
For `ρ > 1/2` there is one `ν₀` such that for every BUC train with `ν ≤ ν₀` and every order
`i ≥ 1` the full derivative `D^i` in `(s, η)` of `S` is bounded on `s > 0`.  (Order `0` is not
claimed: it is the weighted order-`0` bound with `m = 0`.  This is the all-order form of
`MeanStreamGradJets`, `Sub/PartIII-b_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.lean:41`.) -/
def MeanJetsFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = Short.PartI.trainPeriod ρ ν →
    ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
      ∀ i : ℕ, 1 ≤ i → ∃ M : ℝ, ∀ y : ℝ × ℝ, 0 < y.1 →
        ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) y‖ ≤ M

/-- **Unit-patch interpolation of weighted bounds** (calculus; SP 494-496: "Unit-patch
interpolation with the fixed higher smooth bounds ... gives the same tail, with reduced exponent,
for every required ... derivative").  Let `π : E → ℝ` be a continuous linear functional with
`‖π‖ ≤ 1` (the transverse coordinate) and `f : ℝ × E → ℝ` be `C^∞` on `s > 0`.  If on
`0 < s ≤ S + 1` every derivative `D^i f`, `i ≥ 1`, is bounded and `(1+|π x|)^m |f|` is bounded for
every `m`, then on `0 < s ≤ S` every `(1+|π x|)^m ‖D^i f‖` is bounded.  (One step: on the forward
segment `y + t w`, `0 ≤ t ≤ h ≤ 1`, `w.1 ≥ 0`, `‖w‖ ≤ 1`, which stays in `0 < s ≤ S + 1`, the mean
value theorem gives `‖D g(y) w‖ ≤ 2 sup ‖g‖ / h + h sup ‖D² g‖` for `g = D^{i-1} f`; take
`h = (1+|π y.2|)^{-m}` and use the weight `2m` for `g`, `1+|π y.2| ≤ 2 (1+|π (y + t w).2|)`.) -/
def WtdJetInterp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (π : E →L[ℝ] ℝ), ‖π‖ ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (S : ℝ), ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ) →
      (∀ i : ℕ, 1 ≤ i → ∃ M : ℝ, ∀ y : ℝ × E, 0 < y.1 → y.1 ≤ S + 1 →
        ‖iteratedFDeriv ℝ i f y‖ ≤ M) →
      (∀ m : ℕ, ∃ C : ℝ, ∀ y : ℝ × E, 0 < y.1 → y.1 ≤ S + 1 →
        (1 + |π y.2|) ^ m * |f y| ≤ C) →
      ∀ m i : ℕ, ∃ C : ℝ, ∀ y : ℝ × E, 0 < y.1 → y.1 ≤ S →
        (1 + |π y.2|) ^ m * ‖iteratedFDeriv ℝ i f y‖ ≤ C

/-- `TrainMeanWtdBdd` (one threshold for all orders) from the order-`0` weighted bound (threshold of
`TrainMeanWtdMixed` at `b = ℓ = 0`), the fixed-parameter unweighted jets and the interpolation. -/
theorem trainMeanWtdBdd_of (h : TrainMeanWtdMixed) (hJ : MeanJetsFixed) (hI : WtdJetInterp) :
    TrainMeanWtdBdd := by
  intro ρ hρ
  obtain ⟨ν₁, hν₁, h1⟩ := h ρ hρ 0 0
  obtain ⟨ν₂, hν₂, h2⟩ := hJ ρ hρ
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν c hν hle hc tr htr m i S => ?_⟩
  have hle1 : ν ≤ ν₁ := hle.trans (min_le_left _ _)
  have hle2 : ν ≤ ν₂ := hle.trans (min_le_right _ _)
  have hc0 : 0 < c := by subst hc; exact Real.rpow_pos_of_pos hν _
  have hmean : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2)
      (Ioi 0 ×ˢ univ) :=
    (Short.PartI.trainMeanEquations_proof ν _ hν hc0 tr htr).1
  have hB : ∀ k : ℕ, 1 ≤ k → ∃ M : ℝ, ∀ y : ℝ × ℝ, 0 < y.1 → y.1 ≤ S + 1 →
      ‖iteratedFDeriv ℝ k (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) y‖ ≤ M := by
    intro k hk
    obtain ⟨M, hM⟩ := h2 ν c hν hle2 hc tr htr k hk
    exact ⟨M, fun y hy _ => hM y hy⟩
  have hA : ∀ m' : ℕ, ∃ C : ℝ, ∀ y : ℝ × ℝ, 0 < y.1 → y.1 ≤ S + 1 →
      (1 + |(ContinuousLinearMap.id ℝ ℝ) y.2|) ^ m' *
        |(fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) y| ≤ C := by
    intro m'
    obtain ⟨C, hC⟩ := h1 ν c hν hle1 hc tr htr m' (S + 1)
    refine ⟨C, fun y hy hyS => ?_⟩
    have := hC y.1 hy hyS y.2
    simpa only [iteratedDeriv_zero, Real.norm_eq_abs, ContinuousLinearMap.id_apply] using this
  obtain ⟨C, hC⟩ := hI ℝ (ContinuousLinearMap.id ℝ ℝ) ContinuousLinearMap.norm_id_le _ S hmean
    hB hA m i
  refine ⟨C, fun y hy hyS => ?_⟩
  simpa only [ContinuousLinearMap.id_apply] using hC y hy hyS

end UnforcedLeray.Short.PartIIIb.Concrete
