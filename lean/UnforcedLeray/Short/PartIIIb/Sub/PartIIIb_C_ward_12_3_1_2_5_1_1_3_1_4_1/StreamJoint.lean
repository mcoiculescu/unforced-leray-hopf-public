import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.MeanStream
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainFluctAgeJetFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1/3`: `streamJointJetsPoly`

Source `the November 2 reference manuscript`
427-446: joint `(s, q, η)` jets of `ψ = ψ̃ + ψ̄` of order `≤ 3` have polynomial growth in `η` on
`0 < s ≤ s₀`, from `trainFluctAgeJetFixed`, `jointFromAgeJets`, `trainStreamSmooth`, and
`meanStreamJetPoly`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- **Joint jets of the stream** `ψ = ψ̃ + ψ̄` (SP 427-446): order `≤ 3` joint derivatives in
`(s, q, η)` are `≤ C (1+|η|)^M` for `0 < s ≤ s₀`. -/
theorem streamJointJetsPoly : StreamJointJetsPoly := by
  obtain ⟨ν1, hν1, H1⟩ := meanStreamJetPoly
  obtain ⟨ν2, hν2, HF⟩ :=
    UnforcedLeray.Short.PartI.trainFluctAgeJetFixed 2 (by norm_num)
  refine ⟨min ν1 ν2, lt_min hν1 hν2, fun ν c hν hν₀ hc tr hbuc => ?_⟩
  obtain ⟨hsm, C1, s0, M, hs0, h1b⟩ :=
    H1 ν c hν (hν₀.trans (min_le_left _ _)) hc tr hbuc
  have hν2' : ν ≤ ν2 := hν₀.trans (min_le_right _ _)
  have hcp : UnforcedLeray.Short.PartI.trainPeriod 2 ν = c := by
    rw [hc, UnforcedLeray.Short.PartI.trainPeriod, Real.rpow_neg hν.le, Real.rpow_two]
  subst hcp
  have hc0 : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hc]; positivity
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν hc0 tr hbuc
  set F : ℝ → Plane → ℝ :=
    fun r w => tr.ψ r w -
      UnforcedLeray.Short.PartI.hmean (UnforcedLeray.Short.PartI.trainPeriod 2 ν) (tr.ψ r) w.2
  have hFeq :
      (fun x : ℝ × Plane => tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) =
        (fun x : ℝ × Plane => F x.1 x.2) := rfl
  have hfl : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) := by
    rw [← hFeq]
    exact hψ.sub hsm
  have hage : ∀ ℓ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ j F s z‖ ≤ B := by
    intro ℓ j
    obtain ⟨C, κ, hκ, hC⟩ := HF ν hν hν2' tr hbuc ℓ j
    refine ⟨|C|, abs_nonneg C, fun s hs z => ?_⟩
    have he0 : 0 ≤ Real.exp (-(κ * s)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(κ * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hκ.le hs.le))
    calc ‖UnforcedLeray.Short.PartI.ageJet ℓ j F s z‖
        ≤ C * Real.exp (-(κ * s)) := hC s hs z
      _ ≤ |C| * Real.exp (-(κ * s)) := mul_le_mul_of_nonneg_right (le_abs_self C) he0
      _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) he1
  choose B hB0 hB using hage
  have hJ : UnforcedLeray.Short.PartI.JointFromAgeJets :=
    UnforcedLeray.Short.PartI.jointFromAgeJets
  choose K hK0 hK using hJ
  set C2 : ℝ := ∑ l ∈ Finset.range 4, K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ)
  have hC2 : 0 ≤ C2 :=
    Finset.sum_nonneg fun l _ =>
      mul_nonneg (hK0 l) (Finset.sum_nonneg fun ℓ _ => hB0 ℓ (l - ℓ))
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  refine ⟨|C1| + C2, s0, M, hs0, fun l hl y hy hys0 => ?_⟩
  have hyU : y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hy, mem_univ _⟩
  have hsmAt : ContDiffAt ℝ l
      (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y :=
    (hsm.contDiffAt (hUo.mem_nhds hyU)).of_le (by exact_mod_cast le_top)
  have hflAt : ContDiffAt ℝ l (fun x : ℝ × Plane => F x.1 x.2) y :=
    (hfl.contDiffAt (hUo.mem_nhds hyU)).of_le (by exact_mod_cast le_top)
  have hsplit : (fun x : ℝ × Plane => tr.ψ x.1 x.2) =
      (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) +
        (fun x : ℝ × Plane => F x.1 x.2) := by
    funext x
    simp [F, UnforcedLeray.Short.PartI.meanStream]
  rw [hsplit, iteratedFDeriv_add_apply hsmAt hflAt]
  have hl4 : l ∈ Finset.range 4 := Finset.mem_range.2 (by omega)
  have b2 : ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => F x.1 x.2) y‖ ≤ C2 := by
    calc ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => F x.1 x.2) y‖
        ≤ K l * ∑ ℓ ∈ Finset.range (l + 1),
            ‖UnforcedLeray.Short.PartI.ageJet ℓ (l - ℓ) F y.1 y.2‖ :=
          hK l F hfl y hy
      _ ≤ K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ => hB ℓ (l - ℓ) y.1 hy y.2) (hK0 l)
      _ ≤ C2 :=
          Finset.single_le_sum
            (f := fun l => K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ))
            (fun l' _ => mul_nonneg (hK0 l') (Finset.sum_nonneg fun ℓ _ => hB0 ℓ (l' - ℓ))) hl4
  have hη1 : 1 ≤ 1 + |y.2.2| := by linarith [abs_nonneg y.2.2]
  have hpow1 : 1 ≤ (1 + |y.2.2|) ^ M := one_le_pow₀ hη1
  have hpow0 : 0 ≤ (1 + |y.2.2|) ^ M := by positivity
  have b1' : ‖iteratedFDeriv ℝ l
      (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤
        |C1| * (1 + |y.2.2|) ^ M :=
    (h1b l hl y hy hys0).trans (mul_le_mul_of_nonneg_right (le_abs_self C1) hpow0)
  have b2' : ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => F x.1 x.2) y‖ ≤
      C2 * (1 + |y.2.2|) ^ M :=
    b2.trans (le_mul_of_one_le_right hC2 hpow1)
  calc ‖iteratedFDeriv ℝ l
        (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y +
      iteratedFDeriv ℝ l (fun x : ℝ × Plane => F x.1 x.2) y‖
      ≤ _ := norm_add_le _ _
    _ ≤ |C1| * (1 + |y.2.2|) ^ M + C2 * (1 + |y.2.2|) ^ M := add_le_add b1' b2'
    _ = (|C1| + C2) * (1 + |y.2.2|) ^ M := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
