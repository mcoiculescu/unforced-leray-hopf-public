import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.Spine.Sub.SP_EST
import UnforcedLeray.Lib.Train.VortexBounds
import UnforcedLeray.Short.Spine.Proofs.EstDerivWordBridge
import UnforcedLeray.Short.Spine.Proofs.EstEuclidBridge
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem vcWeightedJet_power (a : ℝ) (ha : 0 < a) (j : ℕ) :
    a ^ (-(3 + (j : ℝ)) / 2) = (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ j)⁻¹ := by
  have h1 : Real.sqrt a ^ j = a ^ ((j : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    ring
  rw [h1, ← Real.rpow_add ha, ← Real.rpow_neg ha.le]
  congr 1
  ring

theorem vcWeightedJet : VcWeightedJet := by
  intro k j
  obtain ⟨C, b, hC, hb, h⟩ := UnforcedLeray.Train.Vc_bounds j k
  refine ⟨2 ^ (j + 1) * C, fun ν c s hν hc hs hac x => ?_⟩
  have hw1 : 1 ≤ UnforcedLeray.Train.width ν s := by
    have := mul_nonneg hν.le hs
    unfold UnforcedLeray.Train.width
    linarith
  have hwpos : (0 : ℝ) < UnforcedLeray.Train.width ν s := lt_of_lt_of_le one_pos hw1
  have hac' : UnforcedLeray.Train.width ν s ≤ c ^ 2 := hac
  have hsm : ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν c s) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc hwpos
  obtain ⟨h1, -, -⟩ := h ν c s hc hw1 hac'
  have hW : (0 : ℝ) < (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k := by
    have : (0 : ℝ) ≤ x.2 ^ 2 / UnforcedLeray.Train.width ν s :=
      div_nonneg (sq_nonneg _) hwpos.le
    positivity
  have hcomp : ∀ k' : Fin 2,
      ‖iteratedFDeriv ℝ j (fun y => UnforcedLeray.Train.Vc ν c s y k') x‖ ≤
        2 ^ j * (C * UnforcedLeray.Train.width ν s ^ (-(3 + (j : ℝ)) / 2) /
          (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k) := by
    intro k'
    have hfk : ContDiff ℝ ∞ (fun y => UnforcedLeray.Train.Vc ν c s y k') :=
      (EuclideanSpace.proj k' : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm
    refine UnforcedLeray.Short.Spine.norm_iteratedFDeriv_le_of_derivWord hfk j x ?_
    intro w hw
    rw [le_div_iff₀ hW, mul_comm]
    exact h1 w hw k' x
  have hsum : ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν c s) x‖ ≤
      2 ^ j * (C * UnforcedLeray.Train.width ν s ^ (-(3 + (j : ℝ)) / 2) /
          (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k) +
      2 ^ j * (C * UnforcedLeray.Train.width ν s ^ (-(3 + (j : ℝ)) / 2) /
          (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k) :=
    le_trans (UnforcedLeray.Short.Spine.norm_iteratedFDeriv_euclid2_le hsm j x)
      (add_le_add (hcomp 0) (hcomp 1))
  have hWne : (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k ≠ 0 := hW.ne'
  have hfin : (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k *
      ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν c s) x‖ ≤
        2 ^ (j + 1) * C * UnforcedLeray.Train.width ν s ^ (-(3 + (j : ℝ)) / 2) := by
    calc (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k *
          ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν c s) x‖
        ≤ (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k *
          (2 ^ j * (C * UnforcedLeray.Train.width ν s ^ (-(3 + (j : ℝ)) / 2) /
          (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k) +
          2 ^ j * (C * UnforcedLeray.Train.width ν s ^ (-(3 + (j : ℝ)) / 2) /
          (1 + x.2 ^ 2 / UnforcedLeray.Train.width ν s) ^ k)) :=
          mul_le_mul_of_nonneg_left hsum hW.le
      _ = 2 ^ (j + 1) * C * UnforcedLeray.Train.width ν s ^ (-(3 + (j : ℝ)) / 2) := by
          field_simp
          ring
  have hcl : clockA ν s = UnforcedLeray.Train.width ν s := rfl
  rw [hcl]
  have e := vcWeightedJet_power (UnforcedLeray.Train.width ν s) hwpos j
  have e2 : (2 : ℝ) ^ (j + 1) * C * (UnforcedLeray.Train.width ν s ^ (3 / 2 : ℝ) *
      Real.sqrt (UnforcedLeray.Train.width ν s) ^ j)⁻¹ =
      2 ^ (j + 1) * C * UnforcedLeray.Train.width ν s ^ (-(3 + (j : ℝ)) / 2) := by
    rw [e]
  rw [e2]
  exact hfin

end UnforcedLeray.Short.IIIa
