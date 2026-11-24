import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PartIIIb_IIIb_D2_4_2_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound.LeibnizMul

/-!
# Polynomial-growth class on the chart strip (helper of `PsiProfileGaussBound`)

Source of record: `the November 2 reference manuscript` lines 4963-4991.
`PB s0 f`: `f` is `C²` on `s > 0` and its derivatives of order `≤ 2` grow at most polynomially in
`‖y‖`, uniformly for `s ∈ [s₀/2, 2s₀]`.  The class is closed under sums and products
(Leibniz, `leibnizMulBound_proof`), contains functions of `s` that are `C²` on `(0,∞)` and the
coordinates `y₁, y₂`.  Also the order-`≤ 2` bound for `exp ∘ q`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Polynomial-growth class. -/
def PB (s0 : ℝ) (f : Chart → ℝ) : Prop :=
  ContDiffOn ℝ 2 f (Ioi 0 ×ˢ univ) ∧ ∃ (N : ℕ) (C : ℝ), ∀ p : Chart,
    p.1 ∈ Icc (s0 / 2) (2 * s0) → ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k f p‖ ≤ C * (1 + ‖p.2‖) ^ N

theorem strip_open : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioi.prod isOpen_univ

theorem strip_mem {s0 : ℝ} (hs0 : 0 < s0) {p : Chart} (hp : p.1 ∈ Icc (s0 / 2) (2 * s0)) :
    p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  ⟨lt_of_lt_of_le (by positivity) hp.1, mem_univ _⟩

theorem PB.congr {s0 : ℝ} {f g : Chart → ℝ} (h : ∀ p, f p = g p) (hf : PB s0 f) : PB s0 g := by
  have : f = g := funext h
  subst this
  exact hf

theorem PB.mul {s0 : ℝ} (hs0 : 0 < s0) {f g : Chart → ℝ} (hf : PB s0 f) (hg : PB s0 g) :
    PB s0 (fun p => f p * g p) := by
  obtain ⟨hf1, N₁, C₁, hf2⟩ := hf
  obtain ⟨hg1, N₂, C₂, hg2⟩ := hg
  refine ⟨hf1.mul hg1, N₁ + N₂, ?_⟩
  obtain ⟨C, hC⟩ := leibnizMulBound_proof f g (fun _ => 1) s0 N₁ N₂ C₁ C₂ hs0
    (fun _ => zero_le_one) hf1 hg1 (fun p hp k hk => by simpa using hf2 p hp k hk) hg2
  exact ⟨C, fun p hp k hk => by simpa using hC p hp k hk⟩

theorem PB.add {s0 : ℝ} (hs0 : 0 < s0) {f g : Chart → ℝ} (hf : PB s0 f) (hg : PB s0 g) :
    PB s0 (fun p => f p + g p) := by
  obtain ⟨hf1, N₁, C₁, hf2⟩ := hf
  obtain ⟨hg1, N₂, C₂, hg2⟩ := hg
  refine ⟨hf1.add hg1, max N₁ N₂, |C₁| + |C₂|, fun p hp k hk => ?_⟩
  have hpU := strip_mem hs0 hp
  have hnh := strip_open.mem_nhds hpU
  have hkk : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  have h1 := hf1.contDiffAt hnh |>.of_le hkk
  have h2 := hg1.contDiffAt hnh |>.of_le hkk
  have e : iteratedFDeriv ℝ k (fun p => f p + g p) p =
      iteratedFDeriv ℝ k f p + iteratedFDeriv ℝ k g p := iteratedFDeriv_add_apply h1 h2
  rw [e]
  have hr : (1 : ℝ) ≤ 1 + ‖p.2‖ := by linarith [norm_nonneg p.2]
  have a1 : C₁ * (1 + ‖p.2‖) ^ N₁ ≤ |C₁| * (1 + ‖p.2‖) ^ (max N₁ N₂) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_left _ _)) (abs_nonneg _))
  have a2 : C₂ * (1 + ‖p.2‖) ^ N₂ ≤ |C₂| * (1 + ‖p.2‖) ^ (max N₁ N₂) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_right _ _)) (abs_nonneg _))
  calc _ ≤ ‖iteratedFDeriv ℝ k f p‖ + ‖iteratedFDeriv ℝ k g p‖ := norm_add_le _ _
    _ ≤ _ := by
      have := hf2 p hp k hk
      have := hg2 p hp k hk
      nlinarith

theorem PB.const {s0 : ℝ} (c : ℝ) : PB s0 (fun _ => c) := by
  refine ⟨contDiffOn_const, 0, |c|, fun p _ k hk => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]
    simp [abs_nonneg]

theorem PB.neg {s0 : ℝ} (hs0 : 0 < s0) {f : Chart → ℝ} (hf : PB s0 f) :
    PB s0 (fun p => -f p) :=
  ((PB.const (s0 := s0) (-1)).mul hs0 hf).congr (fun p => by ring)

theorem PB.sub {s0 : ℝ} (hs0 : 0 < s0) {f g : Chart → ℝ} (hf : PB s0 f) (hg : PB s0 g) :
    PB s0 (fun p => f p - g p) :=
  (hf.add hs0 (hg.neg hs0)).congr (fun p => by ring)

/-- A continuous linear functional of the `y`-variables. -/
theorem PB.clm {s0 : ℝ} (ℓ : Chart →L[ℝ] ℝ) (h0 : ∀ p : Chart, |ℓ p| ≤ ‖p.2‖)
    (h1 : ‖ℓ‖ ≤ 1) : PB s0 (fun p => ℓ p) := by
  refine ⟨ℓ.contDiff.contDiffOn, 1, 1, fun p _ k hk => ?_⟩
  have hr : (0 : ℝ) ≤ ‖p.2‖ := norm_nonneg _
  interval_cases k
  · simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    linarith [h0 p]
  · rw [norm_iteratedFDeriv_one, ℓ.fderiv]
    linarith
  · have : ‖iteratedFDeriv ℝ 2 (fun p => ℓ p) p‖ = 0 := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1)]
      have : fderiv ℝ (fun p => ℓ p) = fun _ => ℓ := by
        funext x; exact ℓ.fderiv
      rw [this]
      rw [iteratedFDeriv_succ_const]
      simp
    rw [this]
    positivity

theorem PB.y1 {s0 : ℝ} : PB s0 (fun p : Chart => p.2.1) := by
  have := PB.clm (s0 := s0) ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
    (fun p => by simpa using (norm_fst_le p.2 : ‖p.2.1‖ ≤ ‖p.2‖))
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ, ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ),
        norm_nonneg (ContinuousLinearMap.fst ℝ ℝ ℝ), norm_nonneg (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]))
  exact this.congr (fun p => rfl)

theorem PB.y2 {s0 : ℝ} : PB s0 (fun p : Chart => p.2.2) := by
  have := PB.clm (s0 := s0) ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
    (fun p => by simpa using (norm_snd_le p.2 : ‖p.2.2‖ ≤ ‖p.2‖))
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ, ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ),
        norm_nonneg (ContinuousLinearMap.snd ℝ ℝ ℝ), norm_nonneg (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]))
  exact this.congr (fun p => rfl)

/-- Functions of `s` alone that are `C²` on `(0,∞)`. -/
theorem PB.sfun {s0 : ℝ} (hs0 : 0 < s0) {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioi 0)) :
    PB s0 (fun p : Chart => φ p.1) := by
  have hU0 : IsOpen (Prod.fst ⁻¹' Ioi (0 : ℝ) : Set Chart) := isOpen_Ioi.preimage continuous_fst
  have hcd : ContDiffOn ℝ 2 (fun p : Chart => φ p.1) (Ioi 0 ×ˢ univ) :=
    hφ.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  refine ⟨hcd, 0, ?_⟩
  have hcont : ∀ i : ℕ, i ≤ 2 → ContinuousOn (fun s => iteratedFDeriv ℝ i φ s) (Ioi 0) := by
    intro i hi
    have := hφ.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast hi)
      isOpen_Ioi.uniqueDiffOn
    exact this.congr (fun s hs => (iteratedFDerivWithin_of_isOpen i isOpen_Ioi hs).symm)
  have hK : IsCompact (Icc (s0 / 2) (2 * s0)) := isCompact_Icc
  have hsub : Icc (s0 / 2) (2 * s0) ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le (by positivity) hs.1
  have hb : ∀ i : ℕ, i ≤ 2 → ∃ C : ℝ, ∀ s ∈ Icc (s0 / 2) (2 * s0),
      ‖iteratedFDeriv ℝ i φ s‖ ≤ C := fun i hi =>
    hK.exists_bound_of_continuousOn ((hcont i hi).mono hsub)
  obtain ⟨C0, h0⟩ := hb 0 (by norm_num)
  obtain ⟨C1, h1⟩ := hb 1 (by norm_num)
  obtain ⟨C2, h2⟩ := hb 2 (by norm_num)
  refine ⟨max C0 (max C1 C2), fun p hp k hk => ?_⟩
  have hpU : p.1 ∈ Ioi (0 : ℝ) := hsub hp
  have heq : iteratedFDeriv ℝ k (fun q : Chart => φ q.1) p =
      (iteratedFDeriv ℝ k φ p.1).compContinuousLinearMap fun _ => ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) := by
    have e1 := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).iteratedFDerivWithin_comp_right hφ
      isOpen_Ioi.uniqueDiffOn hU0.uniqueDiffOn (x := p) hpU (i := k) (by exact_mod_cast hk)
    have hU1 : IsOpen ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) :=
      isOpen_Ioi.preimage (ContinuousLinearMap.continuous _)
    have hp1 : p ∈ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ) := hpU
    rw [iteratedFDerivWithin_of_isOpen k hU1 hp1,
      iteratedFDerivWithin_of_isOpen k isOpen_Ioi (show (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p ∈ Ioi (0 : ℝ) from hpU)] at e1
    exact e1
  rw [heq, pow_zero, mul_one]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn : ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le _ _ _
  have hprod : ∏ _i : Fin k, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hn)
  have hbd : ‖iteratedFDeriv ℝ k φ p.1‖ ≤ max C0 (max C1 C2) := by
    interval_cases k
    · exact (h0 _ hp).trans (le_max_left _ _)
    · exact (h1 _ hp).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 _ hp).trans ((le_max_right _ _).trans (le_max_right _ _))
  calc _ ≤ ‖iteratedFDeriv ℝ k φ p.1‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ _ := by linarith

end UnforcedLeray.Short.PartIIIb.Concrete
