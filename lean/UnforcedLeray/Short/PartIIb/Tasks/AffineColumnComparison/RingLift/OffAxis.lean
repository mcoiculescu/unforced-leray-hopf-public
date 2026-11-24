import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.CompChartJets

/-!
# Part II-b, task `PartII-b:G4/5/2/1/4` (`RingLiftOffAxis`)

Source of record: `the November 2 reference manuscript` lines 2360-2366, 2386-2387.
Off the axis, `N_v b = √(age R ·) • (frameL · (b ∘ chart R τ ·))` (`ChartJetsAux.Nv_eq_fun`).
Leibniz for the scalar factor and for the Clifford-valued `clm_apply` product, applied on the open
set `axisᶜ`, with the amplitude/frame jets (`sqrtFrameJets`, at the level `S + 1 > age R y`) and the
composite jets (`compChartJets`).  The constants are sums over the orders `≤ j`, and
`1 + (S+1) ≤ 2 (1 + S)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray

namespace RingLiftOffAxisAux

/-- Leibniz bound for a scalar times a vector, on an open set at a point, from order-wise bounds. -/
theorem smul_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → ℝ} {g : E → F} {x : E} {n : ℕ}
    {A B : ℝ} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) (hs : UniqueDiffOn ℝ s)
    (hx : x ∈ s) (hA : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ A)
    (hB : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i g s x‖ ≤ B) :
    ‖iteratedFDerivWithin ℝ n (fun y => f y • g y) s x‖ ≤ ((n : ℝ) + 1) * 2 ^ n * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g s x‖ ≤ 2 ^ n * A * B := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.1 hi)
    have hc : (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
    exact mul_le_mul (mul_le_mul hc (hA i hi') (norm_nonneg _) (by positivity))
      (hB (n - i) (Nat.sub_le n i)) (norm_nonneg _) (mul_nonneg (by positivity) hA0)
  refine (norm_iteratedFDerivWithin_smul_le hf hg hs hx (by exact_mod_cast le_top)).trans ?_
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (2 ^ n * A * B : ℝ) := Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * 2 ^ n * A * B := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

/-- Leibniz bound for a Clifford-type product `f y (g y)`, on an open set at a point. -/
theorem clm_bound {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} {f : E → F →L[ℝ] G} {g : E → F} {x : E} {n : ℕ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) (hs : UniqueDiffOn ℝ s)
    (hx : x ∈ s) (hA : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ A)
    (hB : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i g s x‖ ≤ B) :
    ‖iteratedFDerivWithin ℝ n (fun y => f y (g y)) s x‖ ≤ ((n : ℝ) + 1) * 2 ^ n * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g s x‖ ≤ 2 ^ n * A * B := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.1 hi)
    have hc : (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
    exact mul_le_mul (mul_le_mul hc (hA i hi') (norm_nonneg _) (by positivity))
      (hB (n - i) (Nat.sub_le n i)) (norm_nonneg _) (mul_nonneg (by positivity) hA0)
  refine (norm_iteratedFDerivWithin_clm_apply hf hg hs hx (by exact_mod_cast le_top)).trans ?_
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (2 ^ n * A * B : ℝ) := Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * 2 ^ n * A * B := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

end RingLiftOffAxisAux

open RingLiftOffAxisAux in
/-- **`RingLiftOffAxis`** (SP 2360-2366, 2386-2387): the off-axis jet bound of the ring lift. -/
theorem ringLiftOffAxis : UnforcedLeray.Short.IIb.RingLiftOffAxis := by
  have hSFall : ∀ i : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ (S R : ℝ), 0 < S → 1 ≤ R →
      ∀ y : Space, y ∉ Axi.axis → Axi.age R y < S →
        ‖iteratedFDeriv ℝ i (fun z => √(Axi.age R z)) y‖ ≤ C * (1 + S) ^ k ∧
        ‖iteratedFDeriv ℝ i Axi.frameL y‖ ≤ C * (1 + S) ^ k :=
    fun i => sqrtFrameJets i
  choose Cs ks hCs hSF using hSFall
  intro j
  obtain ⟨C2, k2, hC2, hcc⟩ := compChartJets j
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
  intro S R τ M b hS hR hM hb _hsupp hder y hy hage
  have hR0 : R ≠ 0 := (lt_of_lt_of_le one_pos hR).ne'
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hyc : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hS' : 0 < S + 1 := by linarith
  have hage' : Axi.age R y < S + 1 := by linarith
  have hpos : 0 ≤ 1 + (S + 1) := by linarith
  have hS1 : (1 : ℝ) ≤ 1 + (S + 1) := by linarith
  -- amplitude and frame jets, order `≤ j`, at the level `S + 1`
  have hA : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => √(Axi.age R z)) Axi.axisᶜ y‖
      ≤ Cq * (1 + (S + 1)) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => √(Axi.age R z)) i hopen hyc]
    refine ((hSF i (S + 1) R hS' hR y hy hage').1).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  have hB : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i Axi.frameL Axi.axisᶜ y‖
      ≤ Cq * (1 + (S + 1)) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.frameL) i hopen hyc]
    refine ((hSF i (S + 1) R hS' hR y hy hage').2).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  -- composite jets, order `≤ j`
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
      ≤ C2 * (1 + (S + 1)) ^ k2 * M := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => b (Axi.chart R τ z)) i hopen hyc]
    exact hcc (S + 1) R τ M b hS' hR hM hb hder y hy hage' i hi
  have hX : 0 ≤ Cq * (1 + (S + 1)) ^ Kq := mul_nonneg hCq0.le (pow_nonneg hpos _)
  have hY : 0 ≤ C2 * (1 + (S + 1)) ^ k2 * M :=
    mul_nonneg (mul_nonneg hC2.le (pow_nonneg hpos _)) hM
  -- the frame times the composite
  have hGc : ∀ m, m ≤ j → ‖iteratedFDerivWithin ℝ m
      (fun z => Axi.frameL z (b (Axi.chart R τ z))) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M) := by
    intro m hm
    have h := clm_bound (f := Axi.frameL) (g := fun z => b (Axi.chart R τ z)) (n := m)
      (A := Cq * (1 + (S + 1)) ^ Kq) (B := C2 * (1 + (S + 1)) ^ k2 * M)
      ChartJetsAux.contDiffOn_frameL (ChartJetsAux.contDiffOn_comp_chart hb hR0 τ)
      hopen.uniqueDiffOn hyc (fun i hi => hB i (hi.trans hm)) (fun i hi => hC i (hi.trans hm))
    refine h.trans ?_
    have hmono : ((m : ℝ) + 1) * 2 ^ m ≤ ((j : ℝ) + 1) * 2 ^ j := by
      have h1 : (m : ℝ) ≤ j := by exact_mod_cast hm
      have h2 : (2 : ℝ) ^ m ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hm
      exact mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hX) hY
  -- Leibniz for the amplitude times the frame-composite
  have hSmul : ‖iteratedFDerivWithin ℝ j (fun z => √(Axi.age R z) • Axi.frameL z
      (b (Axi.chart R τ z))) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M)) :=
    smul_bound (f := fun z => √(Axi.age R z))
      (g := fun z => Axi.frameL z (b (Axi.chart R τ z))) (n := j)
      (A := Cq * (1 + (S + 1)) ^ Kq)
      (B := ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M))
      (ChartJetsAux.contDiffOn_sqrt_age hR0)
      (ChartJetsAux.contDiffOn_frameL.clm_apply (ChartJetsAux.contDiffOn_comp_chart hb hR0 τ))
      hopen.uniqueDiffOn hyc hA (fun i hi => hGc i hi)
  -- conversion to the global derivative and the algebra
  have e := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.Nv R b τ) j hopen hyc
  rw [← e]
  have hNv : ‖iteratedFDerivWithin ℝ j (Axi.Nv R b τ) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M)) := by
    rw [ChartJetsAux.Nv_eq_fun]
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

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.ringLiftOffAxis
