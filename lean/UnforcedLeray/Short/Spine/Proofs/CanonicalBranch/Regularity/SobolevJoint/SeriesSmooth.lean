import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4
import Mathlib.Analysis.PSeries

/-!
# Spine leaf 2: joint smoothness of the series (`SeriesJointSmooth`)

Target `UnforcedLeray.Short.Spine.SeriesJointSmooth` (`Short/Spine/Sub/SP_CAN4_4.lean`), proved
unconditionally, with no hypotheses added. Source of record:
`the November 2 reference manuscript` (lines 1086 and 1134-1140).

Route. Fix `z0` with positive coordinates, `δ > 0` with `closedBall z0 δ ⊆ (0,∞)²`, and a smooth
bump `χ` (from `ContDiffBump`) equal to `1` near `z0` with support in `closedBall z0 δ`.
Each term `χ(z) · (c n z.1 · φ n z.2)` is globally `C^∞`. On the open set `(0,∞)²`, the bilinear
Leibniz rule gives `‖D^k (term n)‖ ≤ M_k / (1+n)²`, using the coefficient bound
`‖c_n^{(l)}(θ)‖ (1+n)^p ≤ 1 + S` and the polynomial bound on `φ_n^{(m)}`. `contDiff_tsum` makes
the sum of class `C^N`, and it agrees with the series near `z0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

lemma sjs_nat_le_top (i : ℕ) : (i : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

lemma sjs_fst_cdo {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => g y.1) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  hg.comp contDiff_fst.contDiffOn (fun _ hy => hy.1)

lemma sjs_snd_cdo {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => g y.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  hg.comp contDiff_snd.contDiffOn (fun _ hy => hy.2)

/-- Derivatives of `g ∘ L` on `(0,∞)²`, for a linear functional `L` of norm at most `1` that maps
`(0,∞)²` into `(0,∞)`, are bounded by the derivatives of `g` at `L z`. -/
lemma sjs_comp_le {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (L : ℝ × ℝ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (hmaps : ∀ y ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), L y ∈ Ioi (0 : ℝ))
    {z : ℝ × ℝ} (hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (l : ℕ) :
    ‖iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => g (L y))
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ ≤ ‖iteratedDeriv l g (L z)‖ := by
  have hO : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hT : IsOpen (L ⁻¹' Ioi (0 : ℝ)) := isOpen_Ioi.preimage L.continuous
  have hzT : z ∈ L ⁻¹' Ioi (0 : ℝ) := hmaps z hz
  have h1 : iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => g (L y)) (L ⁻¹' Ioi (0 : ℝ)) z
      = (iteratedFDerivWithin ℝ l g (Ioi (0 : ℝ)) (L z)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDerivWithin_comp_right hg isOpen_Ioi.uniqueDiffOn hT.uniqueDiffOn (hmaps z hz)
      (sjs_nat_le_top l)
  have hprod : ∏ _i : Fin l, ‖L‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  have hnorm : ‖iteratedFDerivWithin ℝ l g (Ioi (0 : ℝ)) (L z)‖ ≤ ‖iteratedDeriv l g (L z)‖ :=
    le_of_eq (by
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_of_isOpen isOpen_Ioi (hmaps z hz)])
  have hB : ‖iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => g (L y)) (L ⁻¹' Ioi (0 : ℝ)) z‖
      ≤ ‖iteratedDeriv l g (L z)‖ := by
    rw [h1]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc ‖iteratedFDerivWithin ℝ l g (Ioi (0 : ℝ)) (L z)‖ * ∏ _i : Fin l, ‖L‖
        ≤ ‖iteratedFDerivWithin ℝ l g (Ioi (0 : ℝ)) (L z)‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = ‖iteratedFDerivWithin ℝ l g (Ioi (0 : ℝ)) (L z)‖ := mul_one _
      _ ≤ ‖iteratedDeriv l g (L z)‖ := hnorm
  have hA : ‖iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => g (L y))
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖
      = ‖iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => g (L y)) (L ⁻¹' Ioi (0 : ℝ)) z‖ := by
    rw [(iteratedFDerivWithin_of_isOpen l hO) hz, (iteratedFDerivWithin_of_isOpen l hT) hzT]
  rw [hA]
  exact hB

lemma sjs_fst_bound {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) {z : ℝ × ℝ}
    (hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (l : ℕ) :
    ‖iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => g y.1) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖
      ≤ ‖iteratedDeriv l g z.1‖ :=
  sjs_comp_le hg (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ..)
    (fun _ hy => hy.1) hz l

lemma sjs_snd_bound {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) {z : ℝ × ℝ}
    (hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (l : ℕ) :
    ‖iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => g y.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖
      ≤ ‖iteratedDeriv l g z.2‖ :=
  sjs_comp_le hg (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ..)
    (fun _ hy => hy.2) hz l

/-- A `C^∞` cutoff supported in the open set `O` times a function that is `C^∞` on `O` is
globally `C^∞`. -/
lemma sjs_cut_contDiff {χ : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hsupp : tsupport χ ⊆ O) {g : ℝ × ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g O) :
    ContDiff ℝ ∞ (fun z => χ z * g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ O
  · exact hχ.contDiffAt.mul ((hg z hz).contDiffAt (hO.mem_nhds hz))
  · have hev : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hz (hsupp h))
    have hev2 : (fun y => χ y * g y) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [hev] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev2

lemma sjs_mem_box {z z0 : ℝ × ℝ} {δ : ℝ} (h : z ∈ Metric.closedBall z0 δ) :
    z.1 ∈ Icc (z0.1 - δ) (z0.1 + δ) ∧ z.2 ∈ Icc (z0.2 - δ) (z0.2 + δ) := by
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le,
    abs_le] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma sjs_bump (z0 : ℝ × ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.closedBall z0 δ ∧ χ =ᶠ[𝓝 z0] fun _ => (1 : ℂ) := by
  let B : ContDiffBump z0 :=
    { rIn := δ / 2
      rOut := δ
      rIn_pos := half_pos hδ
      rIn_lt_rOut := by linarith }
  refine ⟨fun z => ((B z : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp B.contDiff
  · exact B.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  · have h1 := tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) (B : ℝ × ℝ → ℝ)
    exact h1.trans B.tsupport_eq.subset
  · filter_upwards [B.eventuallyEq_one] with z hz
    simp [hz]

/-- The bilinear Leibniz bound for one term, for fixed `n`, at order `k`, on `(0,∞)²` over the
box `[a,b] × [a',b']`. The constant does not depend on `n`. -/
lemma sjs_F2_order {c φ : ℕ → ℝ → ℂ} (hc : ∀ n, ContDiffOn ℝ ∞ (c n) (Ioi 0))
    (hφ : ∀ n, ContDiffOn ℝ ∞ (φ n) (Ioi 0))
    (hφb : ∀ (m : ℕ) (a b : ℝ), 0 < a → a < b → ∃ C : ℝ, ∃ q : ℕ, ∀ n : ℕ, ∀ r ∈ Icc a b,
      ‖iteratedDeriv m (φ n) r‖ ≤ C * (1 + (n : ℝ)) ^ q)
    (hcb : ∀ (k j : ℕ) (a b : ℝ), 0 < a → a < b → ∃ C : ℝ, ∀ θ ∈ Icc a b,
      Summable (fun n : ℕ => (1 + (n : ℝ)) ^ j * ‖iteratedDeriv k (c n) θ‖ ^ 2) ∧
      ∑' n : ℕ, (1 + (n : ℝ)) ^ j * ‖iteratedDeriv k (c n) θ‖ ^ 2 ≤ C)
    {a b a' b' : ℝ} (ha : 0 < a) (hab : a < b) (ha' : 0 < a') (hab' : a' < b') (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (z : ℝ × ℝ), z.1 ∈ Icc a b → z.2 ∈ Icc a' b' →
      ‖iteratedFDerivWithin ℝ k (fun y : ℝ × ℝ => c n y.1 * φ n y.2)
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ * (1 + (n : ℝ)) ^ 2 ≤ M := by
  choose S hS using fun l j => hcb l j a b ha hab
  choose C q hCq using fun m => hφb m a' b' ha' hab'
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = (∑ m ∈ Finset.range (k + 1), q m) + 2 := ⟨_, rfl⟩
  have hcbd : ∀ (l n : ℕ) (θ : ℝ), θ ∈ Icc a b →
      ‖iteratedDeriv l (c n) θ‖ * (1 + (n : ℝ)) ^ p ≤ 1 + S l (2 * p) := by
    intro l n θ hθ
    obtain ⟨hsum, htsum⟩ := hS l (2 * p) θ hθ
    have hterm : (1 + (n : ℝ)) ^ (2 * p) * ‖iteratedDeriv l (c n) θ‖ ^ 2 ≤ S l (2 * p) :=
      (le_hasSum hsum.hasSum n (fun j _ => by positivity)).trans htsum
    have hy0 : 0 ≤ ‖iteratedDeriv l (c n) θ‖ * (1 + (n : ℝ)) ^ p := by positivity
    have hy2 : (‖iteratedDeriv l (c n) θ‖ * (1 + (n : ℝ)) ^ p) ^ 2 ≤ S l (2 * p) := by
      have e : (‖iteratedDeriv l (c n) θ‖ * (1 + (n : ℝ)) ^ p) ^ 2
          = (1 + (n : ℝ)) ^ (2 * p) * ‖iteratedDeriv l (c n) θ‖ ^ 2 := by ring
      rw [e]
      exact hterm
    generalize ‖iteratedDeriv l (c n) θ‖ * (1 + (n : ℝ)) ^ p = y at hy0 hy2 ⊢
    nlinarith [sq_nonneg (y - 1), sq_nonneg y]
  have hF2 : ∀ (n : ℕ) (z : ℝ × ℝ), z.1 ∈ Icc a b → z.2 ∈ Icc a' b' →
      ‖iteratedFDerivWithin ℝ k (fun y : ℝ × ℝ => c n y.1 * φ n y.2)
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ * (1 + (n : ℝ)) ^ 2 ≤
        ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ((1 + S l (2 * p)) * |C (k - l)|) := by
    intro n z hz1 hz2
    have hzO : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) :=
      ⟨lt_of_lt_of_le ha hz1.1, lt_of_lt_of_le ha' hz2.1⟩
    have hOopen : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (N := ∞)
      (sjs_fst_cdo (hc n)) (sjs_snd_cdo (hφ n)) hOopen.uniqueDiffOn hzO (sjs_nat_le_top k)
    refine (mul_le_mul_of_nonneg_right hleib (by positivity)).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    have hlk : l ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have hmem : k - l ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
    have hf_l := sjs_fst_bound (hc n) hzO l
    have hg_l := sjs_snd_bound (hφ n) hzO (k - l)
    have h2 : ‖iteratedDeriv (k - l) (φ n) z.2‖ ≤ |C (k - l)| * (1 + (n : ℝ)) ^ q (k - l) :=
      (hCq (k - l) n z.2 hz2).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hqle : q (k - l) ≤ ∑ m ∈ Finset.range (k + 1), q m :=
      Finset.single_le_sum (f := q) (fun _ _ => Nat.zero_le _) hmem
    have h3 : (1 + (n : ℝ)) ^ (q (k - l) + 2) ≤ (1 + (n : ℝ)) ^ p :=
      pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by omega)
    have hg' := hg_l.trans h2
    have hstep1 : ‖iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => c n y.1)
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ *
        ‖iteratedFDerivWithin ℝ (k - l) (fun y : ℝ × ℝ => φ n y.2)
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ * (1 + (n : ℝ)) ^ 2 ≤
        ‖iteratedDeriv l (c n) z.1‖ * (|C (k - l)| * (1 + (n : ℝ)) ^ q (k - l)) *
          (1 + (n : ℝ)) ^ 2 :=
      mul_le_mul (mul_le_mul hf_l hg' (norm_nonneg _) (norm_nonneg _)) le_rfl (by positivity)
        (by positivity)
    have hA : ‖iteratedFDerivWithin ℝ l (fun y : ℝ × ℝ => c n y.1)
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ *
        ‖iteratedFDerivWithin ℝ (k - l) (fun y : ℝ × ℝ => φ n y.2)
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ * (1 + (n : ℝ)) ^ 2 ≤
        (1 + S l (2 * p)) * |C (k - l)| := by
      refine hstep1.trans ?_
      calc ‖iteratedDeriv l (c n) z.1‖ * (|C (k - l)| * (1 + (n : ℝ)) ^ q (k - l)) *
            (1 + (n : ℝ)) ^ 2
          = |C (k - l)| * (‖iteratedDeriv l (c n) z.1‖ * (1 + (n : ℝ)) ^ (q (k - l) + 2)) := by
            ring
        _ ≤ |C (k - l)| * (‖iteratedDeriv l (c n) z.1‖ * (1 + (n : ℝ)) ^ p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (abs_nonneg _)
        _ ≤ |C (k - l)| * (1 + S l (2 * p)) := mul_le_mul_of_nonneg_left (hcbd l n z.1 hz1)
          (abs_nonneg _)
        _ = (1 + S l (2 * p)) * |C (k - l)| := by ring
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _))
    ring
  refine ⟨max 0 (∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ((1 + S l (2 * p)) * |C (k - l)|)),
    le_max_left _ _, fun n z h1 h2 => (hF2 n z h1 h2).trans (le_max_right _ _)⟩

/-- The `k`-th derivative of each term `χ · (c n z.1 · φ n z.2)` is bounded by `M / (1+n)²`
with `M` independent of `n`. -/
lemma sjs_order_bound {c φ : ℕ → ℝ → ℂ} (hc : ∀ n, ContDiffOn ℝ ∞ (c n) (Ioi 0))
    (hφ : ∀ n, ContDiffOn ℝ ∞ (φ n) (Ioi 0))
    (hφb : ∀ (m : ℕ) (a b : ℝ), 0 < a → a < b → ∃ C : ℝ, ∃ q : ℕ, ∀ n : ℕ, ∀ r ∈ Icc a b,
      ‖iteratedDeriv m (φ n) r‖ ≤ C * (1 + (n : ℝ)) ^ q)
    (hcb : ∀ (k j : ℕ) (a b : ℝ), 0 < a → a < b → ∃ C : ℝ, ∀ θ ∈ Icc a b,
      Summable (fun n : ℕ => (1 + (n : ℝ)) ^ j * ‖iteratedDeriv k (c n) θ‖ ^ 2) ∧
      ∑' n : ℕ, (1 + (n : ℝ)) ^ j * ‖iteratedDeriv k (c n) θ‖ ^ 2 ≤ C)
    {a b a' b' : ℝ} (ha : 0 < a) (hab : a < b) (ha' : 0 < a') (hab' : a' < b')
    {χ : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχsupp : ∀ z ∈ tsupport χ, z.1 ∈ Icc a b ∧ z.2 ∈ Icc a' b') (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ k (fun y : ℝ × ℝ => χ y * (c n y.1 * φ n y.2)) z‖
        ≤ M / (1 + (n : ℝ)) ^ 2 := by
  choose MF hMF0 hMF using fun i => sjs_F2_order hc hφ hφb hcb ha hab ha' hab' i
  have hKex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ i χ z‖ ≤ K := by
    intro i
    obtain ⟨C0, hC0⟩ :=
      (hχ.continuous_iteratedFDeriv (sjs_nat_le_top i)).bounded_above_of_compact_support
        (hχc.iteratedFDeriv i)
    exact ⟨max C0 0, le_max_right _ _, fun z => (hC0 z).trans (le_max_left _ _)⟩
  choose K hK0 hK using hKex
  refine ⟨max 0 (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i * MF (k - i)),
    le_max_left _ _, fun n z => ?_⟩
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + (n : ℝ)) ^ 2)]
  by_cases hz : z ∈ tsupport χ
  · obtain ⟨hz1, hz2⟩ := hχsupp z hz
    have hzO : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) :=
      ⟨lt_of_lt_of_le ha hz1.1, lt_of_lt_of_le ha' hz2.1⟩
    have hOopen : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
    have hgO : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => c n y.1 * φ n y.2)
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      (sjs_fst_cdo (hc n)).mul (sjs_snd_cdo (hφ n))
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (N := ∞) hχ.contDiffOn hgO
      hOopen.uniqueDiffOn hzO (sjs_nat_le_top k)
    have hEq : iteratedFDeriv ℝ k (fun y : ℝ × ℝ => χ y * (c n y.1 * φ n y.2)) z
        = iteratedFDerivWithin ℝ k (fun y : ℝ × ℝ => χ y * (c n y.1 * φ n y.2))
            (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z :=
      ((iteratedFDerivWithin_of_isOpen k hOopen) hzO).symm
    have hχD : ∀ i : ℕ, ‖iteratedFDerivWithin ℝ i χ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ ≤ K i := by
      intro i
      rw [(iteratedFDerivWithin_of_isOpen i hOopen) hzO]
      exact hK i z
    rw [hEq]
    calc ‖iteratedFDerivWithin ℝ k (fun y : ℝ × ℝ => χ y * (c n y.1 * φ n y.2))
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ * (1 + (n : ℝ)) ^ 2
        ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i χ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ *
            ‖iteratedFDerivWithin ℝ (k - i) (fun y : ℝ × ℝ => c n y.1 * φ n y.2)
              (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖) * (1 + (n : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hleib (by positivity)
      _ = ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i χ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ *
            ‖iteratedFDerivWithin ℝ (k - i) (fun y : ℝ × ℝ => c n y.1 * φ n y.2)
              (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖) * (1 + (n : ℝ)) ^ 2 := Finset.sum_mul _ _ _
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i * MF (k - i) := by
          apply Finset.sum_le_sum
          intro i _
          have hY := hMF (k - i) n z hz1 hz2
          have hX := hχD i
          calc ((k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i χ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ *
                ‖iteratedFDerivWithin ℝ (k - i) (fun y : ℝ × ℝ => c n y.1 * φ n y.2)
                  (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖) * (1 + (n : ℝ)) ^ 2
              = ((k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i χ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖) *
                (‖iteratedFDerivWithin ℝ (k - i) (fun y : ℝ × ℝ => c n y.1 * φ n y.2)
                  (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) z‖ * (1 + (n : ℝ)) ^ 2) := by
                ring
            _ ≤ ((k.choose i : ℝ) * K i) * MF (k - i) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg _)) hY
                (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hK0 i))
      _ ≤ max 0 (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i * MF (k - i)) :=
          le_max_right _ _
  · have hev : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz
    have hev2 : (fun y : ℝ × ℝ => χ y * (c n y.1 * φ n y.2)) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [hev] with y hy
      simp [hy]
    have h0 : iteratedFDeriv ℝ k (fun y : ℝ × ℝ => χ y * (c n y.1 * φ n y.2)) z = 0 := by
      rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev2 k).eq_of_nhds]
      simp [iteratedFDeriv_fun_zero]
    rw [h0, norm_zero, zero_mul]
    exact le_max_left _ _

theorem seriesJointSmooth_proof : UnforcedLeray.Short.Spine.SeriesJointSmooth := by
  intro φ c hφ hφb hc hcb z0 hz0
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_infty]
  intro N
  have hz1 : 0 < z0.1 := hz0.1
  have hz2 : 0 < z0.2 := hz0.2
  obtain ⟨δ, hδ, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < z0.1 ∧ δ < z0.2 :=
    ⟨min z0.1 z0.2 / 2, half_pos (lt_min hz1 hz2), by linarith [min_le_left z0.1 z0.2],
      by linarith [min_le_right z0.1 z0.2]⟩
  obtain ⟨χ, hχ, hχc, hχsub, hχev⟩ := sjs_bump z0 hδ
  have ha : 0 < z0.1 - δ := by linarith
  have hab : z0.1 - δ < z0.1 + δ := by linarith
  have ha' : 0 < z0.2 - δ := by linarith
  have hab' : z0.2 - δ < z0.2 + δ := by linarith
  have hχsupp : ∀ z ∈ tsupport χ, z.1 ∈ Icc (z0.1 - δ) (z0.1 + δ) ∧
      z.2 ∈ Icc (z0.2 - δ) (z0.2 + δ) := fun z hz => sjs_mem_box (hχsub hz)
  have hOopen : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hsuppO : tsupport χ ⊆ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := fun z hz =>
    ⟨lt_of_lt_of_le ha (hχsupp z hz).1.1, lt_of_lt_of_le ha' (hχsupp z hz).2.1⟩
  have hfsm : ∀ n : ℕ, ContDiff ℝ ∞ (fun z : ℝ × ℝ => χ z * (c n z.1 * φ n z.2)) := fun n =>
    sjs_cut_contDiff hχ hOopen hsuppO ((sjs_fst_cdo (hc n)).mul (sjs_snd_cdo (hφ n)))
  choose M _hM0 hM using fun k =>
    sjs_order_bound hc hφ hφb hcb ha hab ha' hab' hχ hχc hχsupp k
  have hsum1 : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    refine ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).congr
      (fun n => ?_)
    push_cast
    ring
  have hT : ContDiff ℝ (N : ℕ∞) (fun x : ℝ × ℝ => ∑' n : ℕ, χ x * (c n x.1 * φ n x.2)) :=
    contDiff_tsum (N := (N : ℕ∞)) (f := fun n x => χ x * (c n x.1 * φ n x.2))
      (v := fun k n => M k * (1 / (1 + (n : ℝ)) ^ 2))
      (fun n => (hfsm n).of_le (sjs_nat_le_top N))
      (fun k _ => hsum1.mul_left (M k))
      (fun k n x _ => (hM k n x).trans_eq (div_eq_mul_one_div _ _))
  have hevχ : ∀ᶠ z in 𝓝 z0, χ z = 1 := by
    filter_upwards [hχev] with z hz
    simpa using hz
  have hevF : (fun x : ℝ × ℝ => ∑' n : ℕ, χ x * (c n x.1 * φ n x.2)) =ᶠ[𝓝 z0]
      (fun z : ℝ × ℝ => ∑' n : ℕ, c n z.1 * φ n z.2) := by
    filter_upwards [hevχ] with z hz
    simp only [hz, one_mul]
  exact hT.contDiffAt.congr_of_eventuallyEq hevF.symm
