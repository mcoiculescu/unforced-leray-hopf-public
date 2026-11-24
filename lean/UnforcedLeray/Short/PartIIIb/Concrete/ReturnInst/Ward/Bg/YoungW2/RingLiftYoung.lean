import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.CompChartJetsYoung

/-!
# Jets of the ring lift of a profile smooth on `s > 0` (source 2360-2366, 2386-2387, 5461-5464)

Source of record: `the November 2 reference manuscript` (73 pages).

Leaf of `PartIII-b:C/ward/12` (`BgRingLiftYoung`, `Ward/Bg/YoungW2/Defs.lean`).  The proof of
`IIb.ringLiftOffAxis` (`PartII-b/Tasks/AffineColumnComparison/RingLift/OffAxis.lean`): off the axis
`N_v b = √(age R ·) • frameL · (b ∘ chart R τ ·)`; Leibniz on the open set `axisᶜ` with the
amplitude/frame jets (`IIb.sqrtFrameJets`, at the level `S + 1 > age R y`) and the composite jets
(`bgCompChartJetsYoung`, with the profile bound at the chart point, whose age is in `(0, S]`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIb.RingLiftOffAxisAux in
/-- **`BgRingLiftYoung`** (source 2360-2366, 2386-2387, 5461-5464). -/
theorem bgRingLiftYoung : BgRingLiftYoung := by
  have hSFall : ∀ i : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ (S R : ℝ), 0 < S → 1 ≤ R →
      ∀ y : Space, y ∉ axis → age R y < S →
        ‖iteratedFDeriv ℝ i (fun z => √(age R z)) y‖ ≤ C * (1 + S) ^ k ∧
        ‖iteratedFDeriv ℝ i frameL y‖ ≤ C * (1 + S) ^ k :=
    fun i => UnforcedLeray.Short.IIb.sqrtFrameJets i
  choose Cs ks hCs hSF using hSFall
  intro j
  obtain ⟨C2, k2, hC2, hcc⟩ := bgCompChartJetsYoung j
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
  refine ⟨(((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2 * 2 ^ (2 * Kq + k2), 2 * Kq + k2, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (pow_pos (by positivity) 2) (pow_pos hCq0 2)) hC2)
      (by positivity)
  intro S R τ M b hS hR hM hb hder y hy hage
  have hR0 : R ≠ 0 := (lt_of_lt_of_le one_pos hR).ne'
  have hopen : IsOpen (axisᶜ : Set Space) := isOpen_compl_axis
  have hyc : y ∈ (axisᶜ : Set Space) := hy
  have hS' : 0 < S + 1 := by linarith
  have hage' : age R y < S + 1 := by linarith
  have hpos : 0 ≤ 1 + (S + 1) := by linarith
  have hS1 : (1 : ℝ) ≤ 1 + (S + 1) := by linarith
  have hbc : ContDiffOn ℝ ∞ (fun z => b (chart R τ z)) axisᶜ :=
    hb.comp (UnforcedLeray.Short.IIb.ChartJetsAux.contDiffOn_chart hR0 τ)
      (fun z hz => ⟨age_pos hR0 hz, mem_univ _⟩)
  -- amplitude and frame jets, order `≤ j`, at the level `S + 1`
  have hA : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => √(age R z)) axisᶜ y‖
      ≤ Cq * (1 + (S + 1)) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => √(age R z)) i hopen hyc]
    refine ((hSF i (S + 1) R hS' hR y hy hage').1).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  have hB : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i frameL axisᶜ y‖
      ≤ Cq * (1 + (S + 1)) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := frameL) i hopen hyc]
    refine ((hSF i (S + 1) R hS' hR y hy hage').2).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  -- composite jets, order `≤ j`, from the profile bound at the chart point
  have hpt : ∀ l ≤ j, (1 + |trans R y|) ^ j * ‖iteratedFDeriv ℝ l b (chart R τ y)‖ ≤ M :=
    fun l hl => hder l hl (chart R τ y) (age_pos hR0 hy) hage
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => b (chart R τ z)) axisᶜ y‖
      ≤ C2 * (1 + (S + 1)) ^ k2 * M := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => b (chart R τ z)) i hopen hyc]
    exact hcc (S + 1) R τ M b hS' hR hM hb y hy hage' hpt i hi
  have hX : 0 ≤ Cq * (1 + (S + 1)) ^ Kq := mul_nonneg hCq0.le (pow_nonneg hpos _)
  have hY : 0 ≤ C2 * (1 + (S + 1)) ^ k2 * M :=
    mul_nonneg (mul_nonneg hC2.le (pow_nonneg hpos _)) hM
  -- the frame times the composite
  have hGc : ∀ m, m ≤ j → ‖iteratedFDerivWithin ℝ m
      (fun z => frameL z (b (chart R τ z))) axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M) := by
    intro m hm
    have h := clm_bound (f := frameL) (g := fun z => b (chart R τ z)) (n := m)
      (A := Cq * (1 + (S + 1)) ^ Kq) (B := C2 * (1 + (S + 1)) ^ k2 * M)
      UnforcedLeray.Short.IIb.ChartJetsAux.contDiffOn_frameL hbc
      hopen.uniqueDiffOn hyc (fun i hi => hB i (hi.trans hm)) (fun i hi => hC i (hi.trans hm))
    refine h.trans ?_
    have hmono : ((m : ℝ) + 1) * 2 ^ m ≤ ((j : ℝ) + 1) * 2 ^ j := by
      have h1 : (m : ℝ) ≤ j := by exact_mod_cast hm
      have h2 : (2 : ℝ) ^ m ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hm
      exact mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hX) hY
  -- Leibniz for the amplitude times the frame-composite
  have hSmul : ‖iteratedFDerivWithin ℝ j (fun z => √(age R z) • frameL z
      (b (chart R τ z))) axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M)) :=
    smul_bound (f := fun z => √(age R z))
      (g := fun z => frameL z (b (chart R τ z))) (n := j)
      (A := Cq * (1 + (S + 1)) ^ Kq)
      (B := ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M))
      (UnforcedLeray.Short.IIb.ChartJetsAux.contDiffOn_sqrt_age hR0)
      (UnforcedLeray.Short.IIb.ChartJetsAux.contDiffOn_frameL.clm_apply hbc)
      hopen.uniqueDiffOn hyc hA (fun i hi => hGc i hi)
  -- conversion to the global derivative and the algebra
  have e := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Nv R b τ) j hopen hyc
  rw [← e]
  have hNv : ‖iteratedFDerivWithin ℝ j (Nv R b τ) axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M)) := by
    rw [UnforcedLeray.Short.IIb.ChartJetsAux.Nv_eq_fun]
    exact hSmul
  have hsub : (1 + (S + 1) : ℝ) ≤ 2 * (1 + S) := by linarith
  have hpowK : (1 + (S + 1) : ℝ) ^ (2 * Kq + k2) ≤ 2 ^ (2 * Kq + k2) * (1 + S) ^ (2 * Kq + k2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hpos hsub _
  have hK : 0 ≤ ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) hC2.le
  calc _ ≤ _ := hNv
    _ = ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2) * (1 + (S + 1)) ^ (2 * Kq + k2) * M := by
      ring
    _ ≤ ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2) * (2 ^ (2 * Kq + k2) * (1 + S) ^ (2 * Kq + k2))
        * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_left hpowK hK
    _ = ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2 * 2 ^ (2 * Kq + k2)) * (1 + S) ^ (2 * Kq + k2)
        * M := by ring

#print axioms bgRingLiftYoung

end UnforcedLeray.Short.PartIIIb.Concrete
