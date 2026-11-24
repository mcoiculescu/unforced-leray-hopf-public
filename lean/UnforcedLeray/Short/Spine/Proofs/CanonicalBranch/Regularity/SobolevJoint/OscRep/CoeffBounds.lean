import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1

/-!
# Leaf B8 (`OscCoeffBounds`): bounds for the coefficient derivatives on `[a, b]`

Source of record: `the November 2 reference manuscript`, lines 1134-1140 (the
Hermite decomposition passage), and the docstring of `OscCoeffBounds` in
`Short/Spine/Sub/SP_CAN4_4_1.lean`, which fixes the statement proved here exactly.

Method: `oscC1` and `oscC0 0` are `C^∞` on `(0, ∞)`, so every iterated derivative is continuous
on the compact `[a, b]` and hence bounded there. `oscC0 n = oscC0 0 - n` differs only by a
constant, which changes the order-zero term and leaves the derivatives of order at least one
unchanged.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace
open UnforcedLeray.Short.Spine

/-- A complex-valued function that is `C^∞` on `(0, ∞)` has every iterated derivative bounded
on `[a, b]` when `0 < a`. -/
lemma coeffBounds_iter_bound (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ioi 0)) (a b : ℝ) (ha : 0 < a)
    (i : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Icc a b, ‖iteratedDeriv i f r‖ ≤ K := by
  have step : ∀ g : ℝ → ℂ, ContDiffOn ℝ ∞ g (Ioi 0) → ContDiffOn ℝ ∞ (deriv g) (Ioi 0) :=
    fun g hg => ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hg).2
  have key : ∀ j : ℕ, ContDiffOn ℝ ∞ (iteratedDeriv j f) (Ioi 0) := by
    intro j
    induction j with
    | zero => rw [iteratedDeriv_zero]; exact hf
    | succ k ih => rw [iteratedDeriv_succ]; exact step _ ih
  have hcont : ContinuousOn (iteratedDeriv i f) (Icc a b) :=
    (key i).continuousOn.mono (fun x hx => lt_of_lt_of_le ha hx.1)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨max K 0, le_max_right _ _, fun r hr => (hK r hr).trans (le_max_left _ _)⟩

/-- `oscC1` is `C^∞` on `(0, ∞)`. -/
lemma coeffBounds_contDiff_C1 : ContDiffOn ℝ ∞ oscC1 (Ioi 0) := by
  have hne : ∀ x ∈ Ioi (0 : ℝ), x ≠ 0 := fun x hx => (Set.mem_Ioi.mp hx).ne'
  have g1 : ContDiffOn ℝ ∞ (fun r : ℝ => -(1 / r + r / 2)) (Ioi 0) :=
    ((contDiffOn_const (c := (1 : ℝ))).div contDiffOn_id hne
      |>.add (contDiffOn_id.div_const (2 : ℝ))).neg
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn g1).congr (fun r _ => by simp [oscC1])

/-- `oscC0 0` is `C^∞` on `(0, ∞)`. -/
lemma coeffBounds_contDiff_C0 : ContDiffOn ℝ ∞ (oscC0 0) (Ioi 0) := by
  have hne : ∀ x ∈ Ioi (0 : ℝ), x ^ 2 ≠ 0 := fun x hx => pow_ne_zero 2 (Set.mem_Ioi.mp hx).ne'
  have g0 : ContDiffOn ℝ ∞ (fun r : ℝ => 4 / r ^ 2 - 2 - ((0 : ℕ) : ℝ)) (Ioi 0) :=
    (((contDiffOn_const (c := (4 : ℝ))).div (contDiffOn_id.pow 2) hne).sub
      (contDiffOn_const (c := (2 : ℝ)))).sub (contDiffOn_const (c := ((0 : ℕ) : ℝ)))
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn g0).congr (fun r _ => by simp [oscC0])

/-- Removing a constant from a function leaves its iterated derivatives of positive order
unchanged. -/
lemma coeffBounds_sub_const (g : ℝ → ℂ) (c : ℂ) (k : ℕ) :
    iteratedDeriv (k + 1) (fun z => g z - c) = iteratedDeriv (k + 1) g := by
  induction k with
  | zero =>
    show iteratedDeriv 1 (fun z => g z - c) = iteratedDeriv 1 g
    rw [iteratedDeriv_one, iteratedDeriv_one]
    exact deriv_sub_const_fun c
  | succ k ih =>
    have e1 : iteratedDeriv (k + 1 + 1) (fun z => g z - c)
        = deriv (iteratedDeriv (k + 1) (fun z => g z - c)) := iteratedDeriv_succ
    have e2 : iteratedDeriv (k + 1 + 1) g = deriv (iteratedDeriv (k + 1) g) := iteratedDeriv_succ
    rw [e1, e2, ih]

/-- The uniform-in-`n` comparison: `|∂^i c₀ⁿ(r)| ≤ |∂^i c₀⁰(r)| + n`. -/
lemma coeffBounds_oscC0_iter (n i : ℕ) (r : ℝ) :
    ‖iteratedDeriv i (oscC0 n) r‖ ≤ ‖iteratedDeriv i (oscC0 0) r‖ + (n : ℝ) := by
  have hfun : oscC0 n = fun z => oscC0 0 z - (n : ℂ) := by
    funext z
    unfold oscC0
    push_cast
    try ring
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [iteratedDeriv_zero, iteratedDeriv_zero]
    have h : oscC0 n r = oscC0 0 r - (n : ℂ) := congrFun hfun r
    rw [h]
    calc ‖oscC0 0 r - (n : ℂ)‖ ≤ ‖oscC0 0 r‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
      _ = ‖oscC0 0 r‖ + (n : ℝ) := by rw [Complex.norm_natCast]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [hfun, coeffBounds_sub_const (oscC0 0) (n : ℂ) k]
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)

/-- **Leaf B8.** For `0 < a < b` and each order `i`, `|c₁^{(i)}| ≤ C` and
`|c₀^{(i)}| ≤ C (1 + n)` on `[a, b]`, with `C` uniform in `n`. -/
theorem oscCoeffBounds_proof : UnforcedLeray.Short.Spine.OscCoeffBounds := by
  intro a b ha _hab i
  obtain ⟨K1, hK1nn, hK1⟩ := coeffBounds_iter_bound oscC1 coeffBounds_contDiff_C1 a b ha i
  obtain ⟨K0, hK0nn, hK0⟩ :=
    coeffBounds_iter_bound (oscC0 0) coeffBounds_contDiff_C0 a b ha i
  refine ⟨max K1 (K0 + 1), fun n r hr => ⟨?_, ?_⟩⟩
  · exact (hK1 r hr).trans (le_max_left _ _)
  · have h2 := coeffBounds_oscC0_iter n i r
    have h3 := hK0 r hr
    have hM : K0 + 1 ≤ max K1 (K0 + 1) := le_max_right _ _
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h4 : (K0 + 1) * (1 + (n : ℝ)) ≤ max K1 (K0 + 1) * (1 + (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hM (by linarith)
    nlinarith [mul_nonneg hK0nn hn]
