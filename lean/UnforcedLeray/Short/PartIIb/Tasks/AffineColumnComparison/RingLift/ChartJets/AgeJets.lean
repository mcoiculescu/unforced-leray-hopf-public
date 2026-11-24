import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets.InvRho

/-!
# Age jets, task `PartII-b:G4/5/2/1/2/1`

Source of record: `the November 2 reference manuscript` lines 2346-2366
(chart `s = R²/ϱ²`).  `AgeJets` follows from the Leibniz rule on `axisᶜ` for the product
`ϱ⁻¹ · ϱ⁻¹`, using the jets of `ϱ⁻¹` (`SqrtFrameJetsAux.varrho_inv_jet`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

namespace AgeJetsAux

open UnforcedLeray

theorem age_eq (R : ℝ) :
    Axi.age R = R ^ 2 • (fun w : Space => (Axi.ϱ w)⁻¹ * (Axi.ϱ w)⁻¹) := by
  funext y
  simp only [Axi.age, Pi.smul_apply, smul_eq_mul]
  ring

end AgeJetsAux

theorem ageJets : UnforcedLeray.Short.IIb.AgeJets := by
  intro j
  choose C hC0 hC using SqrtFrameJetsAux.varrho_inv_jet
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ, Cs = ∑ i ∈ Finset.range (j + 1), C i := ⟨_, rfl⟩
  have hCs0 : 0 < Cs := by
    rw [hCsdef]; exact Finset.sum_pos (fun i _ => hC0 i) ⟨0, by simp⟩
  have hCle : ∀ i ∈ Finset.range (j + 1), C i ≤ Cs := fun i hi => by
    rw [hCsdef]; exact Finset.single_le_sum (f := C) (fun k _ => (hC0 k).le) hi
  refine ⟨((j + 1 : ℕ) : ℝ) * 2 ^ j * Cs ^ 2,
    mul_pos (mul_pos (by positivity) (by positivity)) (pow_pos hCs0 2), ?_⟩
  intro R y hy
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hzc : y ∈ Axi.axisᶜ := hy
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hg : ContDiffOn ℝ ∞ (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ :=
    Axi.contDiffOn_ϱ.inv fun _ hw => Axi.ϱ_ne_zero hw
  have hU : Axi.axisᶜ ∈ 𝓝 y := hopen.mem_nhds hzc
  have hGc : ContDiffOn ℝ ∞ (fun w : Space => (Axi.ϱ w)⁻¹ * (Axi.ϱ w)⁻¹) Axi.axisᶜ :=
    hg.mul hg
  have hdiff : ContDiffAt ℝ j (fun w : Space => (Axi.ϱ w)⁻¹ * (Axi.ϱ w)⁻¹) y :=
    (hGc.contDiffAt hU).of_le (by exact_mod_cast le_top)
  have hage : ‖iteratedFDeriv ℝ j (Axi.age R) y‖ =
      R ^ 2 * ‖iteratedFDerivWithin ℝ j
        (fun w : Space => (Axi.ϱ w)⁻¹ * (Axi.ϱ w)⁻¹) Axi.axisᶜ y‖ := by
    rw [AgeJetsAux.age_eq, iteratedFDeriv_const_smul_apply hdiff,
      ← iteratedFDerivWithin_of_isOpen j hopen hzc, norm_smul,
      Real.norm_of_nonneg (sq_nonneg R)]
  have hL := norm_iteratedFDerivWithin_mul_le hg hg hopen.uniqueDiffOn hzc
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
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹)
          Axi.axisᶜ y‖ * ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => (Axi.ϱ w)⁻¹)
          Axi.axisᶜ y‖ ≤ 2 ^ j * (Cs ^ 2 * t ^ (j + 2)) := by
    intro i hi
    have hij : i ≤ j := by have := Finset.mem_range.1 hi; omega
    have hch : (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
    have h1 := hfj i hij
    have h2 := hfj (j - i) (by omega)
    have hexp : t ^ (i + 1) * t ^ (j - i + 1) = t ^ (j + 2) := by
      rw [← pow_add]; congr 1; omega
    have hab : ‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ y‖ ≤
        (Cs * t ^ (i + 1)) * (Cs * t ^ (j - i + 1)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (hnn _)
    rw [mul_assoc]
    calc (j.choose i : ℝ) * (‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹)
            Axi.axisᶜ y‖ * ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => (Axi.ϱ w)⁻¹)
            Axi.axisᶜ y‖)
        ≤ 2 ^ j * ((Cs * t ^ (i + 1)) * (Cs * t ^ (j - i + 1))) :=
          mul_le_mul hch hab (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = 2 ^ j * (Cs ^ 2 * t ^ (j + 2)) := by rw [← hexp]; ring
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  rw [hage]
  calc R ^ 2 * ‖iteratedFDerivWithin ℝ j (fun w : Space => (Axi.ϱ w)⁻¹ * (Axi.ϱ w)⁻¹)
        Axi.axisᶜ y‖
      ≤ R ^ 2 * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ y‖ :=
        mul_le_mul_of_nonneg_left hL (sq_nonneg R)
    _ ≤ R ^ 2 * (((j + 1 : ℕ) : ℝ) * (2 ^ j * (Cs ^ 2 * t ^ (j + 2)))) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg R)
    _ = ((j + 1 : ℕ) : ℝ) * 2 ^ j * Cs ^ 2 * R ^ 2 * t ^ (j + 2) := by ring

end UnforcedLeray.Short.IIb
