import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets.FrameJets

/-!
# Transverse jets, task `PartII-b:G4/5/2/1/2/3`

Source of record: `the November 2 reference manuscript` lines 2346-2366
(transverse chart coordinate `η = R y₃/ϱ`).  `Axi.trans R = R • (y ↦ y 2 · ϱ⁻¹)`; the Leibniz
rule on `axisᶜ` for `y 2 · ϱ⁻¹`, with the jets of `y ↦ y 2` (order 0: `|y 2|`, order 1: bounded,
order `≥ 2`: zero) and of `ϱ⁻¹` (`SqrtFrameJetsAux.varrho_inv_jet`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

namespace TransJetsAux

open UnforcedLeray

/-- The coordinate projection `y ↦ y 2` as a continuous linear map. -/
def proj2 : Space →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)

theorem proj2_apply (z : Space) : proj2 z = z 2 := rfl

theorem trans_eq (R : ℝ) :
    Axi.trans R = R • (fun z : Space => (proj2 : Space → ℝ) z * (Axi.ϱ z)⁻¹) := by
  funext z
  simp only [Axi.trans, Pi.smul_apply, smul_eq_mul, proj2_apply]
  ring

end TransJetsAux

theorem transJets : UnforcedLeray.Short.IIb.TransJets := by
  intro j hj
  choose C hC0 hC using SqrtFrameJetsAux.varrho_inv_jet
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ, Cs = ∑ i ∈ Finset.range (j + 1), C i := ⟨_, rfl⟩
  have hCs0 : 0 < Cs := by
    rw [hCsdef]; exact Finset.sum_pos (fun i _ => hC0 i) ⟨0, by simp⟩
  have hCle : ∀ i ∈ Finset.range (j + 1), C i ≤ Cs := fun i hi => by
    rw [hCsdef]; exact Finset.single_le_sum (f := C) (fun k _ => (hC0 k).le) hi
  refine ⟨((j + 1 : ℕ) : ℝ) * Cs * (1 + (j : ℝ) * ‖TransJetsAux.proj2‖),
    mul_pos (mul_pos (by positivity) hCs0) (by positivity), ?_⟩
  intro R y hR hy
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hzc : y ∈ Axi.axisᶜ := hy
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hg : ContDiffOn ℝ ∞ (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ :=
    Axi.contDiffOn_ϱ.inv fun _ hw => Axi.ϱ_ne_zero hw
  have hp : ContDiffOn ℝ ∞ (TransJetsAux.proj2 : Space → ℝ) Axi.axisᶜ :=
    TransJetsAux.proj2.contDiff.contDiffOn
  have hF : ContDiffOn ℝ ∞ (fun z : Space => (TransJetsAux.proj2 : Space → ℝ) z * (Axi.ϱ z)⁻¹)
      Axi.axisᶜ := hp.mul hg
  have hU : Axi.axisᶜ ∈ 𝓝 y := hopen.mem_nhds hzc
  have hdiff : ContDiffAt ℝ j
      (fun z : Space => (TransJetsAux.proj2 : Space → ℝ) z * (Axi.ϱ z)⁻¹) y :=
    (hF.contDiffAt hU).of_le (by exact_mod_cast le_top)
  have hD : iteratedFDeriv ℝ j (Axi.trans R) y = R •
      iteratedFDerivWithin ℝ j
        (fun z : Space => (TransJetsAux.proj2 : Space → ℝ) z * (Axi.ϱ z)⁻¹) Axi.axisᶜ y := by
    rw [TransJetsAux.trans_eq R, iteratedFDeriv_const_smul_apply hdiff,
      ← iteratedFDerivWithin_of_isOpen j hopen hzc]
  have hL := norm_iteratedFDerivWithin_mul_le hp hg hopen.uniqueDiffOn hzc
    (n := j) (by exact_mod_cast le_top)
  set t : ℝ := (Axi.ϱ y)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hϱ
  have hnn : ∀ n : ℕ, 0 ≤ Cs * t ^ n := fun n => mul_nonneg hCs0.le (pow_nonneg ht0.le n)
  have hfj : ∀ i : ℕ, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹)
      Axi.axisᶜ y‖ ≤ Cs * t ^ (i + 1) := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hopen hzc]
    exact (hC i y hy).trans (mul_le_mul_of_nonneg_right
      (hCle i (Finset.mem_range.2 (by omega))) (pow_nonneg ht0.le _))
  have hB1 : ∀ n : ℕ, 0 ≤ ‖TransJetsAux.proj2 y‖ * (Cs * t ^ n) := fun n =>
    mul_nonneg (norm_nonneg _) (hnn n)
  have hB2 : 0 ≤ (j : ℝ) * ‖TransJetsAux.proj2‖ * (Cs * t ^ j) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (hnn _)
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (⇑(TransJetsAux.proj2 : Space →L[ℝ] ℝ))
          Axi.axisᶜ y‖ * ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => (Axi.ϱ w)⁻¹)
          Axi.axisᶜ y‖ ≤
        ‖TransJetsAux.proj2 y‖ * (Cs * t ^ (j + 1)) +
          (j : ℝ) * ‖TransJetsAux.proj2‖ * (Cs * t ^ j) := by
    intro i hi
    have hij : i ≤ j := by have := Finset.mem_range.1 hi; omega
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      · have hD0 : ‖iteratedFDerivWithin ℝ 0 (⇑(TransJetsAux.proj2 : Space →L[ℝ] ℝ))
            Axi.axisᶜ y‖ = ‖TransJetsAux.proj2 y‖ := by
          rw [iteratedFDerivWithin_of_isOpen 0 hopen hzc, norm_iteratedFDeriv_zero]
        have hg3 := hfj j le_rfl
        simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, hD0]
        linarith [mul_le_mul_of_nonneg_left hg3 (norm_nonneg (TransJetsAux.proj2 y)), hB2,
          hB1 j]
      · have hD1 : ‖iteratedFDerivWithin ℝ 1 (⇑(TransJetsAux.proj2 : Space →L[ℝ] ℝ))
            Axi.axisᶜ y‖ ≤ ‖TransJetsAux.proj2‖ := by
          rw [iteratedFDerivWithin_of_isOpen 1 hopen hzc]
          exact SqrtFrameJetsAux.clm_jet_one _ y
        have hg4 := hfj (j - 1) (by omega)
        rw [show j - 1 + 1 = j by omega] at hg4
        have hjn : (0 : ℝ) ≤ j := Nat.cast_nonneg _
        have hch : (j.choose 1 : ℝ) = j := by simp
        rw [hch]
        have hA : (j : ℝ) * ‖iteratedFDerivWithin ℝ 1 (⇑(TransJetsAux.proj2 : Space →L[ℝ] ℝ))
            Axi.axisᶜ y‖ * ‖iteratedFDerivWithin ℝ (j - 1) (fun w : Space => (Axi.ϱ w)⁻¹)
            Axi.axisᶜ y‖ ≤ (j : ℝ) * ‖TransJetsAux.proj2‖ * (Cs * t ^ j) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hD1 hjn) hg4 (norm_nonneg _)
            (mul_nonneg hjn (norm_nonneg _))
        linarith [hA, hB1 (j + 1)]
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
      have hD0 : iteratedFDerivWithin ℝ (m + 2) (⇑(TransJetsAux.proj2 : Space →L[ℝ] ℝ))
          Axi.axisᶜ y = 0 := by
        rw [iteratedFDerivWithin_of_isOpen (m + 2) hopen hzc]
        exact SqrtFrameJetsAux.clm_jet_ge_two _ m y
      simp only [hD0, norm_zero, mul_zero, zero_mul]
      linarith [hB1 (j + 1)]
  have hL' := hL.trans (Finset.sum_le_card_nsmul _ _ _ hterm)
  rw [Finset.card_range, nsmul_eq_mul] at hL'
  have habs : |Axi.trans R y| = R * ‖TransJetsAux.proj2 y‖ * t := by
    have hP : ‖TransJetsAux.proj2 y‖ = |y 2| := by
      rw [Real.norm_eq_abs, TransJetsAux.proj2_apply]
    rw [hP, ht]
    unfold Axi.trans
    rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hϱ]
    ring
  have hN : 0 ≤ ((j + 1 : ℕ) : ℝ) * Cs := mul_nonneg (by positivity) hCs0.le
  have hs : 0 ≤ t ^ j := pow_nonneg ht0.le j
  have hm : 0 ≤ (j : ℝ) * ‖TransJetsAux.proj2‖ := by positivity
  have ha : 0 ≤ |Axi.trans R y| := abs_nonneg _
  rw [hD, norm_smul, Real.norm_of_nonneg hR.le]
  calc R * ‖iteratedFDerivWithin ℝ j
        (fun z : Space => (TransJetsAux.proj2 : Space → ℝ) z * (Axi.ϱ z)⁻¹) Axi.axisᶜ y‖
      ≤ R * (((j + 1 : ℕ) : ℝ) * (‖TransJetsAux.proj2 y‖ * (Cs * t ^ (j + 1)) +
          (j : ℝ) * ‖TransJetsAux.proj2‖ * (Cs * t ^ j))) :=
        mul_le_mul_of_nonneg_left hL' hR.le
    _ = ((j + 1 : ℕ) : ℝ) * Cs * (R * ‖TransJetsAux.proj2 y‖ * t) * t ^ j +
          ((j + 1 : ℕ) : ℝ) * ((j : ℝ) * ‖TransJetsAux.proj2‖) * Cs * R * t ^ j := by ring
    _ = ((j + 1 : ℕ) : ℝ) * Cs * |Axi.trans R y| * t ^ j +
          ((j + 1 : ℕ) : ℝ) * ((j : ℝ) * ‖TransJetsAux.proj2‖) * Cs * R * t ^ j := by
        rw [habs]
    _ ≤ ((j + 1 : ℕ) : ℝ) * Cs * (1 + (j : ℝ) * ‖TransJetsAux.proj2‖) *
          (|Axi.trans R y| + R) * t ^ j := by
        nlinarith [mul_nonneg (mul_nonneg hN hs) (add_nonneg hR.le (mul_nonneg hm ha))]

end UnforcedLeray.Short.IIb
