import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1/2`: `MeanStreamJetPoly`, decomposed

Source `the November 2 reference manuscript`
397-404 (`S_s - ν S_ηη = g`, `\bar v₁ = -S_η`, `\bar v₂ = 0`, so `S_η = -\bar v₁`,
`S_s = g - ν ∂_η \bar v₁`), 427-446 (all mixed jets of `v` bounded at fixed parameters).

The smoothness conjunct is `PartI.bucMeanStreamSmooth` composed with `(s,q,η) ↦ (s,η)`.  The jets:
`S_η, S_s` are horizontal averages of `v₁`, `v₁v₂` and `∂_η v₁`, so all joint jets of `S` of order
`1..3` are bounded by joint jets of `v` of order `≤ 3` (`MeanStreamGradJets`); the order-`0` bound
is the mean value theorem from the order-`1` bound (`ZeroFromGrad`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- **Joint jets of `v` of order `≤ 3` are bounded at fixed parameters** (SP 427-435; from
`PartI.TrainJetsBoundedFixed` and `PartI.JointFromAgeJets`, as `VelJointJetsFixed` with order `3`). -/
def VelJointJetsFixed3 : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∃ C : ℝ, ∀ l : ℕ, l ≤ 3 → ∀ y : ℝ × Plane, 0 < y.1 →
        ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.v x.1 x.2) y‖ ≤ C

/-- **Higher jets of the mean stream from jets of `v`** (SP 397-404): for a BUC train, if the joint
jets of `v` of order `≤ 3` are bounded on `s > 0`, so are the joint jets of `(s,q,η) ↦ S(s,η)` of
orders `1, 2, 3`.  (`S_η = -\bar v₁`, `S_s = g - ν ∂_η \bar v₁` with `g = \overline{v₁v₂}`; horizontal
averaging does not increase a sup bound on jets; Leibniz for `v₁v₂`; `D^{l} S` is a combination of
`D^{l-1}` of these two coefficients.) -/
def MeanStreamGradJets : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ C : ℝ,
    (∀ l : ℕ, l ≤ 3 → ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.v x.1 x.2) y‖ ≤ C) →
    ∃ C' : ℝ, ∀ l : ℕ, 1 ≤ l → l ≤ 3 → ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ l
        (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ C'

/-- **Zero order from first order** (mean value theorem on the convex set `s > 0`): if `f` is `C^∞`
on `(0,∞) × ℝ` and the derivative of `(s,q,η) ↦ f(s,η)` is bounded by `C₁` on `s > 0`, then for
every `s₀ > 0` and `0 < s ≤ s₀`, `|f(s,η)| ≤ |f(s₀,0)| + C₁ (s₀ + |η|)` (compare with the point
`(s₀, q, 0)`, where `f(s₀,0)` is the value). -/
def ZeroFromGrad : Prop :=
  ∀ (f : ℝ → ℝ → ℝ) (C₁ : ℝ),
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    (∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ 1 (fun x : ℝ × Plane => f x.1 x.2.2) y‖ ≤ C₁) →
    ∀ s₀ : ℝ, 0 < s₀ → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ s₀ →
      |f y.1 y.2.2| ≤ |f s₀ 0| + C₁ * (s₀ + |y.2.2|)

theorem meanStreamJetPoly_of (hA : VelJointJetsFixed3) (hB : MeanStreamGradJets)
    (hC : ZeroFromGrad) : MeanStreamJetPoly := by
  obtain ⟨ν₀, hν₀, hA⟩ := hA
  refine ⟨ν₀, hν₀, fun ν c hν hνν₀ hc tr hbuc => ?_⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
      (Ioi 0 ×ˢ univ) := UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν c hν hc0 tr hbuc
  refine ⟨?_, ?_⟩
  · have hcomp : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) :=
      contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
    have hmaps : MapsTo (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) (Ioi 0 ×ˢ univ)
        (Ioi 0 ×ˢ univ) := fun x hx => ⟨hx.1, mem_univ _⟩
    exact hsm.comp hcomp.contDiffOn hmaps
  · obtain ⟨C, hC1⟩ := hA ν c hν hνν₀ hc tr hbuc
    obtain ⟨C', hC'⟩ := hB ν c hν hc0 tr hbuc C hC1
    have h1 : ∀ y : ℝ × Plane, 0 < y.1 →
        ‖iteratedFDeriv ℝ 1 (fun x : ℝ × Plane =>
          UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ max C' 0 :=
      fun y hy => (hC' 1 le_rfl (by norm_num) y hy).trans (le_max_left _ _)
    have h0 := hC _ (max C' 0) hsm h1 1 one_pos
    set K : ℝ := |UnforcedLeray.Short.PartI.meanStream tr 1 0| + max C' 0 with hK
    have hKnn : 0 ≤ K := by positivity
    refine ⟨K, 1, 1, one_pos, fun l hl y hy hy1 => ?_⟩
    have hη : 0 ≤ |y.2.2| := abs_nonneg _
    rcases Nat.eq_zero_or_pos l with rfl | hlpos
    · rw [norm_iteratedFDeriv_zero, pow_one, Real.norm_eq_abs]
      refine (h0 y hy hy1).trans ?_
      have hm : 0 ≤ max C' 0 := le_max_right _ _
      have hy1' : 0 < y.1 := hy
      nlinarith [abs_nonneg (UnforcedLeray.Short.PartI.meanStream tr 1 0), mul_nonneg hm hη]
    · rw [pow_one]
      refine (hC' l hlpos hl y hy).trans ?_
      have : max C' 0 ≤ K := by rw [hK]; linarith [abs_nonneg (UnforcedLeray.Short.PartI.meanStream tr 1 0)]
      nlinarith [le_max_left C' 0, mul_nonneg hKnn hη]

end UnforcedLeray.Short.PartIIIb.Concrete
