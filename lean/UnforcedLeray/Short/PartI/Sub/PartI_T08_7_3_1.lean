import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2_3

/-!
# Part I, task `PartI:T08/7/3/1` (`JTBoundQ`): decomposition

Source: `the November 2 reference manuscript` lines 352-358 (`‖[D^j, e·∇]e‖₂ ≤
C_j ‖∇e‖_∞ ‖D^j e‖₂`, constants independent of the period, via the period-independent
Gagliardo-Nirenberg inequality applied to `f = ∇e`).

With the integrated Leibniz expansion `JTExpand` (`Sub/PartI_T08_7_2_3.lean`) the terms of
`⟨D^j f, D^j (f·∇)f⟩` are indexed by `(w, k, (a,b) ∈ wacSplits w, m)`. The split `a = []` is the top
term (`JTQTop`, zero by `div f = 0`). For `a ≠ []`, `|a| = i ∈ [1,j]`: the ends `i = 1`, `i = j` are
direct (`JTQEnds`, a sup-bound `G` and Cauchy-Schwarz) and the middle `2 ≤ i ≤ j-1` uses Hölder and
`CylGN` (`JTQMid`). `jtBoundQ_of` assembles `JTBoundQ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)

/-- **Leaf (top term vanishes)** (lines 352-358): for `JTHyp` data and any word `w`,
`∑_k ∑_m ∫_cell ∂_w f_k · f_m · ∂_{w m} f_k = 0` (the splitting `a = []`, `b = w`;
`(f·∇)D^j f` pairs to zero since `div f = 0`). Route: `∑_m f_m ∂_{w m} f_k = f·∇(∂_w f_k)`
(`derivWord_comm`, `ForcingIBP.lean`), so the sum is `½ ∫_cell f·∇ ∑_k (∂_w f_k)²`; integrate by
parts on the periodic cell (`word_ibp`, `ViscousIBP.lean`, or `Cyl` periodic IBP) to get
`-½ ∫ (div f) ∑_k (∂_w f_k)² = 0`. -/
def JTQTop : Prop :=
  ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ), JTHyp c V f G M →
    ∀ w : List Bool, ∑ k : Fin 2, ∑ m : Fin 2, ∫ z in Cyl.cell c,
      wordComp w f k z * (wordComp [] f m z * wordComp (w ++ [dirOf m]) f k z) = 0

/-- **Leaf (commutator terms at the ends)** (lines 352-358): for `a ≠ []` a splitting of a word `w`
of length `j` with `|a| = 1` or `|a| = j` (then `|b| = j - 1`, resp. `b = []`), every term satisfies
`|∫_cell ∂_w f_k · ∂_a f_m · ∂_{b m} f_k| ≤ C G ‖D^j f‖²`: in the first case `|∂_a f_m| ≤ G`
(`JTHyp`, word of length one) and `∂_{b m} f_k` has length `j`; in the second `|∂_{[m]} f_k| ≤ G`
and `∂_a f_m = ∂_w f_m` has length `j`. Then `|∫ F · H| ≤ √∫F² √∫H²` (`abs_int_cs`) with
`∫ (∂_u f_l)² ≤ jetEnergy c j f` for `u` of length `j` (a term of the sum `jetEnergy_eq_sum`, all
terms nonnegative), `C = 1`. -/
def JTQEnds : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ), JTHyp c V f G M →
    ∀ w ∈ wordsOfLength j, ∀ p ∈ wacSplits w, p.1 ≠ [] → (p.1.length = 1 ∨ p.1.length = j) →
      ∀ m k : Fin 2, |∫ z in Cyl.cell c,
        wordComp w f k z * (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) f k z)| ≤
          C * (G * jetEnergy c j f)

/-- **Leaf (commutator terms in the middle, Hölder + `CylGN`)** (lines 352-358): same as
`JTQEnds` for `2 ≤ |a| ≤ j - 1` (so `j ≥ 3`). Put `i = |a|`, `m' = j - 1`, `g = ` a component of
`∇f` (`|g| ≤ G`, `JTHyp`). The three factors are `∂_w f_k = D^{m'} g` (up to a component),
`∂_a f_m = D^{i-1} g` and `∂_{b m} f_k = D^{j-i} g`; Hölder with exponents `2m'/(i-1)`, `2m'/(j-i)`, `2`
(sum of reciprocals `= 1`) and the period-independent Gagliardo-Nirenberg
`‖D^l g‖_{2m'/l} ≤ C ‖g‖_∞^{1-l/m'} ‖D^{m'} g‖₂^{l/m'}` (`cylinder_interpolation_uniform`, second
conjunct `CylGN`, `Tasks/CylinderInterpolation.lean`; `cylJetWord_proof`, `cylDerivFinite_proof` to pass
between jets and words) give `≤ C G ‖D^{m'} g‖₂² ≤ C G jetEnergy c j f`; the powers of `G` add
to `1`. `C` depends only on `j`, not on `c ≥ 1`. -/
def JTQMid : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ), JTHyp c V f G M →
    ∀ w ∈ wordsOfLength j, ∀ p ∈ wacSplits w, 2 ≤ p.1.length → p.1.length + 1 ≤ j →
      ∀ m k : Fin 2, |∫ z in Cyl.cell c,
        wordComp w f k z * (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) f k z)| ≤
          C * (G * jetEnergy c j f)

theorem mem_wordsOfLength_length {j : ℕ} {w : List Bool} (h : w ∈ wordsOfLength j) :
    w.length = j := by
  unfold wordsOfLength at h
  rw [Finset.mem_image] at h
  obtain ⟨v, _, rfl⟩ := h
  simp

theorem card_wordsOfLength_le (j : ℕ) : (wordsOfLength j).card ≤ 2 ^ j := by
  unfold wordsOfLength
  refine Finset.card_image_le.trans ?_
  simp

theorem jtBoundQ_of (h1 : JTExpand) (h2 : JTQTop) (h3 : JTQEnds) (h4 : JTQMid) : JTBoundQ := by
  intro j
  obtain ⟨C₁, hC₁, hE⟩ := h3 j
  obtain ⟨C₂, hC₂, hM⟩ := h4 j
  set C : ℝ := C₁ + C₂ with hCdef
  have hC : 0 ≤ C := add_nonneg hC₁ hC₂
  refine ⟨4 * 4 ^ j * C, by positivity, ?_⟩
  intro c V f G M H
  have H' := H
  obtain ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hG, hMb⟩ := H'
  have hfs : ContDiff ℝ ∞ f := hf.1
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hG true 0 (0, 0))
  have hJ0 : 0 ≤ jetEnergy c j f := jetEnergy_nonneg c j f
  set J := jetEnergy c j f with hJ
  rw [h1 j c f f f hfs hfs hf (Or.inl hf) hfb hfb]
  set T : List Bool → Fin 2 → (List Bool × List Bool) → ℝ := fun w k p =>
    ∑ m : Fin 2, ∫ z in Cyl.cell c,
      wordComp w f k z * (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) f k z) with hT
  -- top term
  have hsplit : ∀ w k, ((wacSplits w).map (T w k)).sum =
      T w k ([], w) + ((wacSplits w).map (fun p => if p.1 = [] then 0 else T w k p)).sum := by
    intro w k
    rw [wac_split_sum]
    congr 1
    have := wac_filter_sum (fun v => T w k ([], v)) w
    rw [← this]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    by_cases hp : p.1 = []
    · obtain ⟨a, b⟩ := p
      simp only at hp
      subst hp
      simp
    · simp [hp]
  have hrest : ∀ w ∈ wordsOfLength j, ∀ k,
      |((wacSplits w).map (fun p => if p.1 = [] then 0 else T w k p)).sum| ≤
        2 ^ j * (2 * (C * (G * J))) := by
    intro w hw k
    have hwl := mem_wordsOfLength_length hw
    have hb : 0 ≤ 2 * (C * (G * J)) := by positivity
    have := wac_sum_bound (fun p => if p.1 = [] then 0 else T w k p) (2 * (C * (G * J))) hb (wacSplits w)
      (by
        intro p hp
        by_cases h0 : p.1 = []
        · simp [h0, hb]
        · simp only [h0, if_false]
          have hlen := wac_splits_len_sum w p hp
          have hpos : 1 ≤ p.1.length := List.length_pos_iff.mpr h0
          have hper : ∀ m : Fin 2, |∫ z in Cyl.cell c,
              wordComp w f k z * (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) f k z)| ≤
                C * (G * J) := by
            intro m
            by_cases hcase : p.1.length = 1 ∨ p.1.length = j
            · exact (hE c V f G M H w hw p hp h0 hcase m k).trans
                (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hG0 hJ0))
            · have h2' : 2 ≤ p.1.length := by omega
              have h3' : p.1.length + 1 ≤ j := by omega
              exact (hM c V f G M H w hw p hp h2' h3' m k).trans
                (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hG0 hJ0))
          simp only [hT, Fin.sum_univ_two]
          calc _ ≤ _ := abs_add_le _ _
            _ ≤ C * (G * J) + C * (G * J) := add_le_add (hper 0) (hper 1)
            _ = _ := by ring)
    refine this.trans ?_
    rw [wac_splits_length, hwl]
    push_cast
    exact le_refl _
  have htop : ∀ w : List Bool, ∑ k : Fin 2, T w k ([], w) = 0 := fun w => by
    have := h2 c V f G M H w
    simp only [hT]
    exact this
  have hsum : ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ((wacSplits w).map (T w k)).sum =
      ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        ((wacSplits w).map (fun p => if p.1 = [] then 0 else T w k p)).sum := by
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [hsplit, Finset.sum_add_distrib, htop, zero_add]
  show |∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ((wacSplits w).map (T w k)).sum| ≤ _
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ w ∈ wordsOfLength j, |∑ k : Fin 2,
          ((wacSplits w).map (fun p => if p.1 = [] then 0 else T w k p)).sum|
      ≤ ∑ w ∈ wordsOfLength j, (2 * (2 ^ j * (2 * (C * (G * J))))) := by
        refine Finset.sum_le_sum fun w hw => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc _ ≤ ∑ k : Fin 2, (2 ^ j * (2 * (C * (G * J))) : ℝ) :=
              Finset.sum_le_sum fun k _ => hrest w hw k
          _ = _ := by simp
    _ = ((wordsOfLength j).card : ℝ) * (2 * (2 ^ j * (2 * (C * (G * J))))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ j : ℝ) * (2 * (2 ^ j * (2 * (C * (G * J))))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_wordsOfLength_le j
    _ = 4 * 4 ^ j * C * (G * J) := by
        have : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
        rw [this]; ring

end UnforcedLeray.Short.PartI
