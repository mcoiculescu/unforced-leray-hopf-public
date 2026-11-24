import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Comp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Leibniz
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Arith

/-!
# Off-axis jets of the ring lift `Nv`, orders `1, 2`, with the `ϱ⁻¹` scaling

Source `the November 2 reference manuscript`
lines 2360-2366, 2385-2387: `Nv R b τ = √s • frameL (b ∘ chart)`, with `t = ϱ⁻¹`,
`W = 1 + s + |η|`: `‖D Nv‖ ≲ Cm t² W`, `‖D² Nv‖ ≲ Cm t³ W²` where `Cm` bounds the jets of `b` of
order `≤ 2` at the chart point.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem nv_jets {R : ℝ} (hR : 0 < R) : ∃ K : ℝ, 0 < K ∧
    ∀ (τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), ContDiff ℝ ∞ b → ∀ y : Space, y ∉ Axi.axis →
    ∀ Cm : ℝ, (∀ i ≤ 2, ‖iteratedFDeriv ℝ i b (Axi.chart R τ y)‖ ≤ Cm) →
      ‖iteratedFDeriv ℝ 1 (Axi.Nv R b τ) y‖ ≤
        K * Cm * ((Axi.ϱ y)⁻¹) ^ 2 * (1 + Axi.age R y + |Axi.trans R y|) ∧
      ‖iteratedFDeriv ℝ 2 (Axi.Nv R b τ) y‖ ≤
        K * Cm * ((Axi.ϱ y)⁻¹) ^ 3 * (1 + Axi.age R y + |Axi.trans R y|) ^ 2 := by
  obtain ⟨α0, hα0, hA0⟩ := amp_jet hR 0
  obtain ⟨α1, hα1, hA1⟩ := amp_jet hR 1
  obtain ⟨α2, hα2, hA2⟩ := amp_jet hR 2
  obtain ⟨π0, hπ0, hP0⟩ := frame_jet 0
  obtain ⟨π1, hπ1, hP1⟩ := frame_jet 1
  obtain ⟨π2, hπ2, hP2⟩ := frame_jet 2
  obtain ⟨a, ha, hcomp⟩ := comp_jet hR
  refine ⟨10 * (α0 + α1 + α2) * (π0 + π1 + π2) * a ^ 2 * R, by positivity, ?_⟩
  intro τ b hb y hy Cm hCm
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hx : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hCm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm 0 (by norm_num))
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact inv_nonneg.2 (Axi.ϱ_nonneg y)
  have hs : Axi.age R y = R ^ 2 * t ^ 2 := by rw [age_eq_sq, ht]
  have hs0 : 0 ≤ Axi.age R y := by rw [hs]; positivity
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 1 + Axi.age R y + |Axi.trans R y| := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by rw [hW]; linarith [abs_nonneg (Axi.trans R y)]
  rw [← ht, ← hW]
  have hAc : ContDiffOn ℝ ∞ (fun z : Space => √(Axi.age R z)) Axi.axisᶜ :=
    IIb.ChartJetsAux.contDiffOn_sqrt_age hR.ne'
  have hPc : ContDiffOn ℝ ∞ Axi.frameL Axi.axisᶜ := IIb.ChartJetsAux.contDiffOn_frameL
  have hBc : ContDiffOn ℝ ∞ (fun z : Space => b (Axi.chart R τ z)) Axi.axisᶜ :=
    IIb.ChartJetsAux.contDiffOn_comp_chart hb hR.ne' τ
  obtain ⟨hG0, hG1, hG2⟩ := clm_apply_le hopen hx hPc hBc
  have hGc : ContDiffOn ℝ ∞ (fun z : Space => Axi.frameL z (b (Axi.chart R τ z))) Axi.axisᶜ :=
    hPc.clm_apply hBc
  obtain ⟨hN1, hN2⟩ := smul_le hopen hx hAc hGc
  have hNv : Axi.Nv R b τ = fun z => √(Axi.age R z) • Axi.frameL z (b (Axi.chart R τ z)) := rfl
  rw [hNv]
  -- the bounds on the three factors
  have bA0 := hA0 y hy
  have bA1 := hA1 y hy
  have bA2 := hA2 y hy
  have bP0 := hP0 y hy
  have bP1 := hP1 y hy
  have bP2 := hP2 y hy
  rw [← ht] at bA0 bA1 bA2 bP0 bP1 bP2
  simp only [zero_add, pow_zero, mul_one, Nat.reduceAdd, pow_one] at bA0 bA1 bA2 bP0 bP1 bP2
  have bB0 : ‖iteratedFDeriv ℝ 0 (fun z => b (Axi.chart R τ z)) y‖ ≤ Cm := by
    rw [norm_iteratedFDeriv_zero]
    simpa using hCm 0 (by norm_num)
  have bB1 := hcomp τ b hb y hy Cm hCm 1 le_rfl (by norm_num)
  have bB2 := hcomp τ b hb y hy Cm hCm 2 (by norm_num) le_rfl
  rw [← ht, ← hW] at bB1 bB2
  have hαs : 0 ≤ α0 + α1 + α2 := by positivity
  have hπs : 0 ≤ π0 + π1 + π2 := by positivity
  have tn : ∀ n : ℕ, 0 ≤ t ^ n := fun n => pow_nonneg ht0 n
  refine arith_jets (α0 + α1 + α2) (π0 + π1 + π2) a R Cm t W _ _ _ _ _ _ _ _ _ _ _ _ _ _ hαs hπs ha hR
    hCm0 ht0 hW1 ?_ ?_ ?_ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) ?_ ?_ ?_
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) bB0 ?_ ?_ (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hG0 hG1 hG2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hN1 hN2
  · refine bA0.trans ?_; gcongr; linarith
  · refine bA1.trans ?_; gcongr; linarith
  · refine bA2.trans ?_; gcongr; linarith
  · refine bP0.trans ?_; linarith
  · refine bP1.trans ?_; gcongr; linarith
  · refine bP2.trans ?_; gcongr; linarith
  · simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at bB1; exact bB1
  · simp only [Nat.factorial_two, Nat.cast_ofNat] at bB2; exact bB2

end UnforcedLeray.Short.PartIIIb.Concrete
