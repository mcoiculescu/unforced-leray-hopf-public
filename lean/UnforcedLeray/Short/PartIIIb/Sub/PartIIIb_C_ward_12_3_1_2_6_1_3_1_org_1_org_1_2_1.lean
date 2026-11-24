import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.TrainStreamWtdBdd_Sub
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets

/-!
# Decomposition of `TrainFluctWtdBdd` (SP 440-445 with proof SP 516-526, fixed parameters SP 427-435)

Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff

/-- **Weighted mixed age jets of the stream fluctuation, bounded ages** (SP 440-445,
`sct:fluctuation` with weights `⟨η⟩^m`; proof SP 516-526: interpolate the doubled polynomial weight
with the unweighted exponential bounds for `s ≥ s_c` and the pre-overlap bounds for `s ≤ s_c`; age
derivatives by finite induction).  At fixed parameters (SP 427-435): for `ρ > 1/2` one `ν₀`, and for
every BUC train with `ν ≤ ν₀` and all `m, ℓ, j, S`:
`(1+|η|)^m ‖∂_s^ℓ D^j ψ̃(s, q, η)‖ ≤ C` on `0 < s ≤ S`.  This is the weighted form of
`PartI.TrainFluctAgeJetFixed` (`Short/PartI/Sub/PartI_TrainHeatFixed.lean`). -/
def TrainFluctWtdAgeJet : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = Short.PartI.trainPeriod ρ ν →
    ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
      ∀ (m ℓ j : ℕ) (S : ℝ), ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ S → ∀ z : UnforcedLeray.Cyl.Plane,
        (1 + |z.2|) ^ m *
          ‖Short.PartI.ageJet ℓ j
            (fun r w => tr.ψ r w - Short.PartI.hmean c (tr.ψ r) w.2) s z‖ ≤ C

theorem trainFluctWtdBdd_of (h : TrainFluctWtdAgeJet) : TrainFluctWtdBdd := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, h'⟩ := h ρ hρ
  refine ⟨ν₀, hν₀, fun ν c hν hle hc tr htr m i S => ?_⟩
  have hc0 : 0 < c := by subst hc; exact Real.rpow_pos_of_pos hν _
  obtain ⟨K, hK0, hK⟩ := Short.PartI.jointFromAgeJets i
  have hb : ∀ ℓ : ℕ, ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ S → ∀ z : UnforcedLeray.Cyl.Plane,
      (1 + |z.2|) ^ m * ‖Short.PartI.ageJet ℓ (i - ℓ)
            (fun r w => tr.ψ r w - Short.PartI.hmean c (tr.ψ r) w.2) s z‖ ≤ C :=
    fun ℓ => h' ν c hν hle hc tr htr m ℓ (i - ℓ) S
  choose Cf hCf using hb
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  let L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  have hL : ∀ x, L x = (x.1, x.2.2) := fun x => rfl
  have hLmaps : MapsTo L U U2 := fun x hx => by
    simp only [hL, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) U :=
    Short.PartI.trainStreamSmooth ν _ hν hc0 tr htr
  have hmean : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) U2 :=
    (Short.PartI.trainMeanEquations_proof ν _ hν hc0 tr htr).1
  have hf1 : ContDiffOn ℝ ∞
      ((fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) ∘ L) U :=
    hmean.comp L.contDiff.contDiffOn hLmaps
  have hf2 : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - Short.PartI.meanStream tr x.1 x.2.2) U :=
    hψ.sub hf1
  refine ⟨K * ∑ ℓ ∈ Finset.range (i + 1), Cf ℓ, fun y hy0 hyS => ?_⟩
  have hmain := hK (fun r w => tr.ψ r w - Short.PartI.hmean c (tr.ψ r) w.2) hf2 y hy0
  have hw : 0 ≤ (1 + |y.2.2|) ^ m := by positivity
  calc (1 + |y.2.2|) ^ m * ‖iteratedFDeriv ℝ i
          (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - Short.PartI.meanStream tr x.1 x.2.2) y‖
      ≤ (1 + |y.2.2|) ^ m * (K * ∑ ℓ ∈ Finset.range (i + 1), ‖Short.PartI.ageJet ℓ (i - ℓ)
            (fun r w => tr.ψ r w - Short.PartI.hmean c (tr.ψ r) w.2) y.1 y.2‖) :=
        mul_le_mul_of_nonneg_left hmain hw
    _ = K * ∑ ℓ ∈ Finset.range (i + 1), (1 + |y.2.2|) ^ m * ‖Short.PartI.ageJet ℓ (i - ℓ)
            (fun r w => tr.ψ r w - Short.PartI.hmean c (tr.ψ r) w.2) y.1 y.2‖ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ K * ∑ ℓ ∈ Finset.range (i + 1), Cf ℓ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun ℓ _ => hCf ℓ y.1 hy0 hyS y.2)) hK0

end UnforcedLeray.Short.PartIIIb.Concrete
