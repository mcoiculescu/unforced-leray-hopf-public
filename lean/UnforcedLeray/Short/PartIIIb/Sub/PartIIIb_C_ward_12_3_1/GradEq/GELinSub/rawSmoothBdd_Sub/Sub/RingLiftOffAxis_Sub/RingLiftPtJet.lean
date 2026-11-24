import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.OffAxis
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.CompChartPtJet

/-!
# Organizer task `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/4`: `ringLiftPtJet`

Source of record: `the November 2 reference manuscript`, SP 2360-2366, 2386-2387.
Pointwise version of `IIb.ringLiftOffAxis`: off the axis `Nv R b τ = √(age R ·) • frameL · (b ∘ chart R τ ·)`
(`ChartJetsAux.Nv_eq_fun`); Leibniz (`RingLiftOffAxisAux.smul_bound`, `RingLiftOffAxisAux.clm_bound`)
on the open set `axisᶜ` with the amplitude/frame jets (`sqrtFrameJets`, at level `L = age + 1`) and
the composite jets (`compChartPtJet`, pointwise in `age` and `|trans|`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ringLiftPtJet : UnforcedLeray.Short.PartIIIb.Concrete.RingLiftPtJet := by
  have hSFall : ∀ i : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ (S R : ℝ), 0 < S → 1 ≤ R →
      ∀ y : Space, y ∉ Axi.axis → Axi.age R y < S →
        ‖iteratedFDeriv ℝ i (fun z => √(Axi.age R z)) y‖ ≤ C * (1 + S) ^ k ∧
        ‖iteratedFDeriv ℝ i Axi.frameL y‖ ≤ C * (1 + S) ^ k :=
    fun i => sqrtFrameJets i
  choose Cs ks hCs hSF using hSFall
  intro j
  obtain ⟨C2, k2, hC2, hcc⟩ := compChartPtJet j
  obtain ⟨Cq, hCq⟩ : ∃ x : ℝ, x = ∑ i ∈ Finset.range (j + 1), Cs i := ⟨_, rfl⟩
  obtain ⟨Kq, hKq⟩ : ∃ K : ℕ, K = ∑ i ∈ Finset.range (j + 1), ks i := ⟨_, rfl⟩
  have hCs_le : ∀ i, i ≤ j → Cs i ≤ Cq := fun i hi => by
    rw [hCq]
    exact Finset.single_le_sum (f := Cs) (fun l _ => (hCs l).le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hks_le : ∀ i, i ≤ j → ks i ≤ Kq := fun i hi => by
    rw [hKq]
    exact Finset.single_le_sum (f := ks) (fun l _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hCq0 : 0 < Cq := by
    rw [hCq]
    exact Finset.sum_pos (fun l _ => hCs l) ⟨0, by simp⟩
  refine ⟨(((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2 * 2 ^ (2 * Kq), 2 * Kq + k2, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (pow_pos (by positivity) 2) (pow_pos hCq0 2)) hC2)
      (pow_pos two_pos _)
  intro R τ b hR hb
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hR0 : R ≠ 0 := hRpos.ne'
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hmaps : MapsTo (Axi.chart R τ) Axi.axisᶜ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro z hz
    exact ⟨age_pos_of hRpos hz, mem_univ _⟩
  have hbc : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
    hb.comp (ChartJetsAux.contDiffOn_chart hR0 τ) hmaps
  have hNvC : ContDiffOn ℝ ∞ (Axi.Nv R b τ) Axi.axisᶜ := by
    rw [ChartJetsAux.Nv_eq_fun]
    exact (ChartJetsAux.contDiffOn_sqrt_age hR0).smul
      (ChartJetsAux.contDiffOn_frameL.clm_apply hbc)
  refine ⟨hNvC, fun y hy => ?_⟩
  have hage : 0 < Axi.age R y := age_pos_of hRpos hy
  have hyc : y ∈ (Axi.axisᶜ : Set Space) := hy
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Axi.age R y + 1 := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; linarith
  have hageL : Axi.age R y < L := by rw [hL]; linarith
  have hpos : 0 ≤ 1 + L := by linarith
  have hS1 : (1 : ℝ) ≤ 1 + L := by linarith
  have hsub : 1 + L ≤ 2 * (1 + Axi.age R y) := by rw [hL]; linarith
  have hP0 : (0 : ℝ) ≤ 1 + Axi.age R y := by linarith
  have hT0 : (0 : ℝ) ≤ 1 + |Axi.trans R y| := by linarith [abs_nonneg (Axi.trans R y)]
  obtain ⟨Bc, hBc⟩ : ∃ B : ℝ, B = C2 * (1 + Axi.age R y) ^ k2 * (1 + |Axi.trans R y|) ^ j *
      ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := by
    rw [hBc]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC2.le (pow_nonneg hP0 _)) (pow_nonneg hT0 _))
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  -- amplitude and frame jets, order `≤ j`, at the level `L = age + 1`
  have hA : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => √(Axi.age R z)) Axi.axisᶜ y‖
      ≤ Cq * (1 + L) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => √(Axi.age R z)) i hopen hyc]
    refine ((hSF i L R hL0 hR y hy hageL).1).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  have hB : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i Axi.frameL Axi.axisᶜ y‖
      ≤ Cq * (1 + L) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.frameL) i hopen hyc]
    refine ((hSF i L R hL0 hR y hy hageL).2).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  -- composite jets, order `≤ j`
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
      ≤ Bc := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => b (Axi.chart R τ z)) i hopen hyc,
      hBc]
    exact hcc R τ b hR hb y hy i hi
  have hX : 0 ≤ Cq * (1 + L) ^ Kq := mul_nonneg hCq0.le (pow_nonneg hpos _)
  -- the frame times the composite
  have hGc : ∀ m, m ≤ j → ‖iteratedFDerivWithin ℝ m
      (fun z => Axi.frameL z (b (Axi.chart R τ z))) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) * Bc := by
    intro m hm
    have h := RingLiftOffAxisAux.clm_bound (f := Axi.frameL) (g := fun z => b (Axi.chart R τ z))
      (n := m) (A := Cq * (1 + L) ^ Kq) (B := Bc)
      ChartJetsAux.contDiffOn_frameL hbc hopen.uniqueDiffOn hyc
      (fun i hi => hB i (hi.trans hm)) (fun i hi => hC i (hi.trans hm))
    refine h.trans ?_
    have hmono : ((m : ℝ) + 1) * 2 ^ m ≤ ((j : ℝ) + 1) * 2 ^ j := by
      have h1 : (m : ℝ) ≤ j := by exact_mod_cast hm
      have h2 : (2 : ℝ) ^ m ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hm
      exact mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hX) hBc0
  -- Leibniz for the amplitude times the frame-composite
  have hSmul : ‖iteratedFDerivWithin ℝ j (fun z => √(Axi.age R z) • Axi.frameL z
      (b (Axi.chart R τ z))) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) * Bc) :=
    RingLiftOffAxisAux.smul_bound (f := fun z => √(Axi.age R z))
      (g := fun z => Axi.frameL z (b (Axi.chart R τ z))) (n := j)
      (A := Cq * (1 + L) ^ Kq)
      (B := ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) * Bc)
      (ChartJetsAux.contDiffOn_sqrt_age hR0)
      (ChartJetsAux.contDiffOn_frameL.clm_apply hbc)
      hopen.uniqueDiffOn hyc hA (fun i hi => hGc i hi)
  -- conversion to the global derivative
  have e := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.Nv R b τ) j hopen hyc
  have hNv : ‖iteratedFDerivWithin ℝ j (Axi.Nv R b τ) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) * Bc) := by
    rw [ChartJetsAux.Nv_eq_fun]
    exact hSmul
  rw [← e]
  refine hNv.trans ?_
  have hL2 : (1 + L) ^ Kq * (1 + L) ^ Kq ≤ 2 ^ (2 * Kq) * (1 + Axi.age R y) ^ (2 * Kq) := by
    calc (1 + L) ^ Kq * (1 + L) ^ Kq = (1 + L) ^ (2 * Kq) := by rw [← pow_add, two_mul]
      _ ≤ (2 * (1 + Axi.age R y)) ^ (2 * Kq) := pow_le_pow_left₀ hpos hsub _
      _ = 2 ^ (2 * Kq) * (1 + Axi.age R y) ^ (2 * Kq) := mul_pow _ _ _
  calc _ = (((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * ((1 + L) ^ Kq * (1 + L) ^ Kq) * Bc := by ring
    _ ≤ (((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * (2 ^ (2 * Kq) * (1 + Axi.age R y) ^ (2 * Kq)) * Bc := by
        refine mul_le_mul_of_nonneg_right ?_ hBc0
        exact mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ = ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2 * 2 ^ (2 * Kq)) * (1 + Axi.age R y) ^ (2 * Kq + k2)
        * (1 + |Axi.trans R y|) ^ j
        * (∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖) := by
        rw [hBc, pow_add]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
