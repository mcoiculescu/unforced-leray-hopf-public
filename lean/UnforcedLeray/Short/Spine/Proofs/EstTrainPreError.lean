import UnforcedLeray.Short.Spine.Sub.SP_EST
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof

/-!
# Spine: the pre-overlap train error (task `Spine:SP-EST/2`)

Source of record: `the November 2 reference manuscript`, lines 291-303
(`sct:comparison`, sup-norm display). The statement is `Spine.TrainPreError`; the proof is the
Part I comparison `PartI.trainComparison_proof` at `ρ = 2` (so `Train.per ν = trainPeriod 2 ν`),
read off in its sup-norm half.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.Short.PartI
open UnforcedLeray.Cyl (Plane)

theorem trainPreError_proof : UnforcedLeray.Short.Spine.TrainPreError := by
  have H := UnforcedLeray.Short.PartI.trainComparison_proof 2 (by norm_num)
  choose C b ν₀ hC hb hν₀ h using H
  refine ⟨C, b, min (min (ν₀ 0) (ν₀ 1)) (min (ν₀ 2) (ν₀ 3)), ?_, hb, ?_⟩
  · exact lt_min (lt_min (hν₀ 0) (hν₀ 1)) (lt_min (hν₀ 2) (hν₀ 3))
  intro ν hν T hT s hs hsle j hj x
  have hν0 : 0 < ν := hν.1
  have hνle : ν ≤ min (min (ν₀ 0) (ν₀ 1)) (min (ν₀ 2) (ν₀ 3)) := hν.2
  have key : ∀ k : ℕ, k ≤ 3 → ν ≤ ν₀ k := by
    intro k hk
    interval_cases k
    · exact hνle.trans ((min_le_left _ _).trans (min_le_left _ _))
    · exact hνle.trans ((min_le_left _ _).trans (min_le_right _ _))
    · exact hνle.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact hνle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνj : ν ≤ ν₀ j := key j hj
  have gen : ∀ c : ℝ, c = trainPeriod 2 ν → ∀ T : B0140.TrainSol ν c, IsBUCTrain T →
      ∀ s : ℝ, 0 ≤ s → s ≤ B0146.overlapAge ν c → ∀ x : Plane,
        ‖iteratedFDeriv ℝ j (T.v s - Train.Vc ν c s) x‖ ≤
          C j * ν⁻¹ * B0113.heatWidth ν s ^ (-((5 + j : ℝ) / 2)) *
            Real.exp (-b j * c ^ 2 / B0113.heatWidth ν s) := by
    intro c hc T hT s hs hsle x
    subst hc
    have hsle'' : s ≤ (trainPeriod 2 ν ^ 2 - 1) / ν := hsle
    have hsle' : s * ν ≤ trainPeriod 2 ν ^ 2 - 1 := (le_div_iff₀ hν0).1 hsle''
    have hw : Train.width ν s ≤ trainPeriod 2 ν ^ 2 := by
      unfold Train.width
      nlinarith [mul_comm s ν]
    have hsup := (h j ν hν0 hνj T hT s hs hw).2
    have hw1 : 0 < B0113.heatWidth ν s := by
      unfold B0113.heatWidth
      nlinarith [mul_nonneg hν0.le hs]
    rw [show -b j * trainPeriod 2 ν ^ 2 / B0113.heatWidth ν s
        = -(b j * trainPeriod 2 ν ^ 2 / B0113.heatWidth ν s) by ring]
    have hR0 : 0 ≤ C j * ν⁻¹ * B0113.heatWidth ν s ^ (-((5 + j : ℝ) / 2)) *
        Real.exp (-(b j * trainPeriod 2 ν ^ 2 / B0113.heatWidth ν s)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (hC j).le (inv_nonneg.2 hν0.le))
        (Real.rpow_nonneg hw1.le _)) (Real.exp_pos _).le
    have h1 : ‖iteratedFDeriv ℝ j (T.v s - Train.Vc ν (trainPeriod 2 ν) s) x‖ₑ ≤
        B0277.supNormD j (fun z => T.v s z - Train.Vc ν (trainPeriod 2 ν) s z) :=
      le_iSup (fun y => ‖iteratedFDeriv ℝ j (fun z => T.v s z - Train.Vc ν (trainPeriod 2 ν) s z) y‖ₑ) x
    have h2 := h1.trans hsup
    rw [← ofReal_norm] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hR0).1 h2
  exact gen (Train.per ν) (Train.per_eq_rpow hν0) T hT s hs hsle x

end UnforcedLeray.Short.Spine
