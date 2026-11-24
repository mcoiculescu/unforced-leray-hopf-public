import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.TrainGrowth
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Uniform train energy from the `L²` decay of the train (source 314-322, `sct:integrated`)

`TrainEnergyUnif` follows from `PartI.TrainL2Decay` at `ρ = 2`, since `cOf ν = ν^{-2}` and
`trainPeriod 2 ν = ν^{-2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

theorem trainEnergyUnif_of (hL : UnforcedLeray.Short.PartI.TrainL2Decay) : TrainEnergyUnif := by
  obtain ⟨C, ν₁, hC, hν₁, h⟩ := hL 2 (by norm_num)
  unfold TrainEnergyUnif
  refine ⟨min ν₁ (1 / 2), lt_min hν₁ (by norm_num), C, ?_⟩
  intro ν hν hνle tr htr s hs
  have hν₁' : ν ≤ ν₁ := hνle.trans (min_le_left _ _)
  have hν2 : ν ≤ 1 / 2 := hνle.trans (min_le_right _ _)
  have hcν : cOf ν = UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    unfold cOf UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν.le, Real.rpow_two]
  have key : ∀ c : ℝ, c = UnforcedLeray.Short.PartI.trainPeriod 2 ν →
      ∀ tr' : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr' →
        ∀ s : ℝ, 0 ≤ s →
          UnforcedLeray.Train.cellL2 c (tr'.v s) ≤ ENNReal.ofReal C := by
    intro c hc tr' htr' s hs
    subst hc
    have hP1 : 1 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
      unfold UnforcedLeray.Short.PartI.trainPeriod
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by norm_num)
    have hP0 : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by linarith
    obtain ⟨h1, h2⟩ := h ν hν hν₁' tr' htr' s hs
    rcases le_total s (UnforcedLeray.B0146.overlapAge ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν))
      with hsle | hsge
    · refine (h1 hsle).trans (ENNReal.ofReal_le_ofReal ?_)
      have hw : 1 ≤ UnforcedLeray.Train.width ν s := by
        unfold UnforcedLeray.Train.width
        nlinarith
      have hinv : (UnforcedLeray.Train.width ν s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hw
      exact mul_le_of_le_one_right hC.le hinv
    · refine (h2 hsge).trans (ENNReal.ofReal_le_ofReal ?_)
      have hoA : 0 < UnforcedLeray.B0146.overlapAge ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) := by
        unfold UnforcedLeray.B0146.overlapAge
        exact div_pos (by nlinarith) hν
      have hq : 1 ≤ s / UnforcedLeray.B0146.overlapAge ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
        (one_le_div hoA).2 hsge
      have hs0 : 0 ≤ s / UnforcedLeray.B0146.overlapAge ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) := by
        linarith
      have hX : (s / UnforcedLeray.B0146.overlapAge ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν))
          ^ (-(3 / 4 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hq (by norm_num)
      have hX0 : 0 ≤ (s / UnforcedLeray.B0146.overlapAge ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν))
          ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hs0 _
      have hA : (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ (-2 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hP1.le (by norm_num)
      have hA0 : 0 ≤ (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ (-2 : ℝ) :=
        Real.rpow_nonneg hP0.le _
      have hAX : (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ (-2 : ℝ) *
          (s / UnforcedLeray.B0146.overlapAge ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν))
            ^ (-(3 / 4 : ℝ)) ≤ 1 := by
        nlinarith [mul_le_mul hA hX hX0 zero_le_one]
      nlinarith [mul_le_mul_of_nonneg_left hAX hC.le]
  exact key (cOf ν) hcν tr htr s hs

end UnforcedLeray.Short.PartIIIb.Concrete
