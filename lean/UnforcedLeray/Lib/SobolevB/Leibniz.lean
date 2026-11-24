import UnforcedLeray.Lib.Sobolev

/-!
# Leibniz rule with a smooth coefficient (INF11 target S5)


§5.1 (S5, `W.mulCoeff`). Manuscript uses: Leibniz with smooth bounded coefficients in the
weighted and unweighted `H^k` norms (tex 1215–1220, B0060; tex 1867–1871, B0122;
tex 13901–13941, B0660), and Leibniz for cutoffs (tex 7550–7576, B0433).

For a word `w` (a list of coordinate letters) the weak derivative of `a · f` is
`∂^w (a f) = ∑_{|u| ≤ K} lcoef a w u · ∂^u f` (`hasWeakDeriv_smul_word`), where the
coefficients `lcoef a w u` are defined by the recursion of the first-order Leibniz rule
`HasWeakDeriv.smul_left`. They are smooth, vanish for `|u| > |w|`, equal `a` on the diagonal
(`lcoef_diag`), have bounded derivatives when `a` does (`bddDerivs_lcoef`), and scale under
dilations (`lcoef_dilate`). The construction of `W.mulCoeff` follows `W.compDiffeo`
(`Lib/Sobolev/CompDiffeo.lean`, Wave 1) with the chain-rule coefficients replaced by the
Leibniz ones; it reuses `mulL`, `derivL`, `wordSet`, `BddDerivs` from there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology

namespace UnforcedLeray.Sob

section Coeff

variable {n : ℕ}

/-- The new part of the Leibniz rule: `(l :: u) ↦ [l = j] c u`. -/
def ltail (j : Fin n) (c : List (Fin n) → Eucl n → ℝ) : List (Fin n) → Eucl n → ℝ
  | [] => fun _ => 0
  | l :: u => fun x => if l = j then c u x else 0

/-- `lcoef a w u`: the coefficient of `∂^u f` in `∂^w (a f)`. -/
def lcoef (a : Eucl n → ℝ) : List (Fin n) → List (Fin n) → Eucl n → ℝ
  | [] => fun u x => if u = [] then a x else 0
  | j :: w => fun u x => fderiv ℝ (lcoef a w u) x (e j) + ltail j (lcoef a w) u x

theorem lcoef_nil (a : Eucl n → ℝ) (u : List (Fin n)) (x : Eucl n) :
    lcoef a [] u x = if u = [] then a x else 0 := rfl

theorem lcoef_cons (a : Eucl n → ℝ) (j : Fin n) (w u : List (Fin n)) (x : Eucl n) :
    lcoef a (j :: w) u x = fderiv ℝ (lcoef a w u) x (e j) + ltail j (lcoef a w) u x := rfl

theorem contDiff_lcoef {a : Eucl n → ℝ} (ha : ContDiff ℝ ∞ a) (w u : List (Fin n)) :
    ContDiff ℝ ∞ (lcoef a w u) := by
  induction w generalizing u with
  | nil =>
    by_cases hu : u = []
    · simpa [lcoef, hu] using ha
    · have : lcoef a [] u = fun _ => 0 := by funext x; simp [lcoef, hu]
      rw [this]; exact contDiff_const
  | cons j w ih =>
    refine (contDiff_dirDeriv (ih u) (e j)).add ?_
    cases u with
    | nil => exact contDiff_const
    | cons l u =>
      by_cases hl : l = j
      · simpa [ltail, hl] using ih u
      · have : ltail j (lcoef a w) (l :: u) = fun _ => 0 := by funext x; simp [ltail, hl]
        rw [this]; exact contDiff_const

theorem lcoef_eq_zero (a : Eucl n → ℝ) {w u : List (Fin n)} (h : w.length < u.length) :
    lcoef a w u = 0 := by
  induction w generalizing u with
  | nil =>
    funext x
    rw [lcoef_nil, if_neg]
    · rfl
    · rintro rfl; simp at h
  | cons j w ih =>
    funext x
    cases u with
    | nil => simp at h
    | cons l u =>
      simp only [List.length_cons, add_lt_add_iff_right] at h
      rw [lcoef_cons, ih (u := l :: u) (by simp only [List.length_cons]; omega)]
      simp [ltail, ih h, Pi.zero_def]

/-- On the diagonal `|u| = |w|` the coefficient is `a` for `u = w` and `0` otherwise. -/
theorem lcoef_diag (a : Eucl n → ℝ) {w u : List (Fin n)} (h : u.length = w.length) :
    lcoef a w u = if u = w then a else 0 := by
  induction w generalizing u with
  | nil =>
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst hu
    funext x; simp [lcoef]
  | cons j w ih =>
    funext x
    cases u with
    | nil => simp at h
    | cons l u =>
      simp only [List.length_cons, add_left_inj] at h
      rw [lcoef_cons, lcoef_eq_zero a (u := l :: u) (by simp [h])]
      simp only [Pi.zero_apply, fderiv_const, ContinuousLinearMap.zero_apply, zero_add, ltail,
        ih h, List.cons.injEq]
      by_cases hl : l = j <;> by_cases hu : u = w <;> simp [hl, hu]

theorem lcoef_self (a : Eucl n → ℝ) (w : List (Fin n)) : lcoef a w w = a := by
  rw [lcoef_diag a rfl, if_pos rfl]

theorem bddDerivs_lcoef {K : ℕ} {a : Eucl n → ℝ} (ha : BddDerivs K a) (w : List (Fin n))
    (hw : w.length ≤ K) (u : List (Fin n)) : BddDerivs (K - w.length) (lcoef a w u) := by
  induction w generalizing u with
  | nil =>
    by_cases hu : u = []
    · simpa [lcoef, hu] using ha
    · have : lcoef a [] u = fun _ => (0 : ℝ) := by funext x; simp [lcoef, hu]
      rw [this]; exact bddDerivs_const _ _
  | cons j w ih =>
    have hw' : w.length ≤ K := by simp only [List.length_cons] at hw; omega
    have hlen : K - (j :: w).length + 1 = K - w.length := by
      simp only [List.length_cons] at hw ⊢; omega
    have h1 : BddDerivs (K - (j :: w).length) (fun x => fderiv ℝ (lcoef a w u) x (e j)) := by
      have := ih hw' u
      rw [← hlen] at this
      exact this.dirDeriv (e j)
    have h2 : BddDerivs (K - (j :: w).length) (ltail j (lcoef a w) u) := by
      cases u with
      | nil => exact bddDerivs_const _ _
      | cons l u =>
        by_cases hl : l = j
        · have e1 : ltail j (lcoef a w) (l :: u) = lcoef a w u := by
            funext x; simp [ltail, hl]
          rw [e1]
          exact (ih hw' u).mono (by simp only [List.length_cons]; omega)
        · have e1 : ltail j (lcoef a w) (l :: u) = fun _ => (0 : ℝ) := by
            funext x; simp [ltail, hl]
          rw [e1]; exact bddDerivs_const _ _
    exact h1.add h2

/-- **Dilations**: the coefficients of `a(s ·)` are `s^{|w| - |u|}` times those of `a`,
evaluated at `s x`. -/
theorem lcoef_dilate {a : Eucl n → ℝ} (ha : ContDiff ℝ ∞ a) (s : ℝ) (w u : List (Fin n))
    (x : Eucl n) :
    lcoef (fun y => a (s • y)) w u x = s ^ (w.length - u.length) * lcoef a w u (s • x) := by
  induction w generalizing u x with
  | nil => by_cases hu : u = [] <;> simp [lcoef, hu]
  | cons j w ih =>
    rw [lcoef_cons, lcoef_cons]
    have hfun : lcoef (fun y => a (s • y)) w u =
        fun y => s ^ (w.length - u.length) * lcoef a w u (s • y) := funext (ih u)
    have hd : HasFDerivAt (fun y => s ^ (w.length - u.length) * lcoef a w u (s • y))
        (s ^ (w.length - u.length) • (fderiv ℝ (lcoef a w u) (s • x)).comp
          (s • ContinuousLinearMap.id ℝ (Eucl n))) x := by
      have h1 : HasFDerivAt (fun y : Eucl n => s • y) (s • ContinuousLinearMap.id ℝ (Eucl n)) x :=
        (hasFDerivAt_id x).const_smul s
      have h2 := (((contDiff_lcoef ha w u).differentiable (by simp)) (s • x)).hasFDerivAt
      exact (h2.comp x h1).const_mul _
    rw [hfun, hd.fderiv]
    have htail : ltail j (lcoef (fun y => a (s • y)) w) u x =
        s ^ ((j :: w).length - u.length) * ltail j (lcoef a w) u (s • x) := by
      cases u with
      | nil => simp [ltail]
      | cons l u =>
        by_cases hl : l = j
        · simp [ltail, hl, ih u x]
        · simp [ltail, hl]
    rw [htail]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
      map_smul, smul_eq_mul, List.length_cons]
    by_cases hle : u.length ≤ w.length
    · have : w.length + 1 - u.length = w.length - u.length + 1 := by omega
      rw [this, pow_succ]
      ring
    · have hz : lcoef a w u = 0 := lcoef_eq_zero a (by omega)
      simp [hz]

end Coeff

/-! ### The weak Leibniz rule for every word -/

section Rule

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sum_lcoef_nil_smul (a : Eucl n → ℝ) (K : ℕ) (g : List (Fin n) → Eucl n → F)
    (x : Eucl n) : ∑ u ∈ wordSet K, lcoef a [] u x • g u x = a x • g [] x := by
  rw [Finset.sum_eq_single_of_mem [] (mem_wordSet.mpr (Nat.zero_le _))]
  · simp [lcoef_nil]
  · intro u _ hu
    simp [lcoef_nil, hu]

/-- **Weak Leibniz rule for words** (S5): if `g u = ∂^u f` weakly for every word `|u| ≤ K`
(locally integrable) and `a` is smooth, then for every word `|w| ≤ K`,
`∂^w (a f) = ∑_{|u| ≤ K} lcoef a w u · g u` weakly. -/
theorem hasWeakDeriv_smul_word {a : Eucl n → ℝ} (ha : ContDiff ℝ ∞ a) {K : ℕ}
    (g : List (Fin n) → Eucl n → F)
    (hgl : ∀ u, u.length ≤ K → LocallyIntegrable (g u) volume)
    (hgw : ∀ u, u.length ≤ K → HasWeakDeriv (wholeSpace n) (u.map e) (g []) (g u))
    (w : List (Fin n)) (hw : w.length ≤ K) :
    HasWeakDeriv (wholeSpace n) (w.map e) (fun x => a x • g [] x)
      (fun x => ∑ u ∈ wordSet K, lcoef a w u x • g u x) := by
  induction w with
  | nil =>
    have e1 : (fun x => ∑ u ∈ wordSet K, lcoef a [] u x • g u x) = fun x => a x • g [] x :=
      funext (sum_lcoef_nil_smul a K g)
    rw [e1]
    exact HasWeakDeriv.nil fun φ hφ =>
      integrable_smul_of_adm hφ ((hgl [] (Nat.zero_le _)).continuous_smul ha.continuous)
  | cons j w ih =>
    have hwK : w.length < K := by simp only [List.length_cons] at hw; omega
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have ih' := ih (Nat.le_of_lt hwK)
    have hterm : ∀ u ∈ wordSet (K' + 1), HasWeakDeriv (wholeSpace n) [e j]
        (fun x => lcoef a w u x • g u x)
        (fun x => fderiv ℝ (lcoef a w u) x (e j) • g u x +
          lcoef a w u x • (if u.length ≤ K' then g (j :: u) x else 0)) := by
      intro u hu
      have huK := mem_wordSet.mp hu
      by_cases hlt : u.length ≤ K'
      · have hGl : HasWeakDeriv (wholeSpace n) [e j] (g u) (g (j :: u)) := by
          have h2 := (hgw (j :: u) (by simpa using hlt)).perm
            (show (e j :: u.map e).Perm (u.map e ++ [e j]) from List.perm_append_singleton _ _
              |>.symm)
          exact (hgw u huK).of_append h2
        simp only [hlt, if_true]
        exact hGl.smul_left (contDiff_lcoef ha w u) (hgl u huK)
          (hgl (j :: u) (by simpa using hlt))
      · have hz : lcoef a w u = 0 := lcoef_eq_zero a (by omega)
        have e1 : (fun x => lcoef a w u x • g u x) = 0 := by
          funext x; simp [hz]
        have e2 : (fun x => fderiv ℝ (lcoef a w u) x (e j) • g u x +
            lcoef a w u x • (if u.length ≤ K' then g (j :: u) x else 0)) = 0 := by
          funext x; simp [hz, Pi.zero_def]
        rw [e1, e2]
        exact HasWeakDeriv.zero
    have hsum := HasWeakDeriv.sum _ hterm
    refine ih'.cons (hsum.congr_ae (Eventually.of_forall fun x => rfl)
      (Eventually.of_forall fun x => ?_))
    simp only [lcoef_cons, add_smul, Finset.sum_add_distrib, smul_add]
    congr 1
    rw [sum_wordSet_succ K' (fun u => ltail j (lcoef a w) u x • g u x), Finset.sum_comm]
    simp only [ltail, zero_smul, zero_add, ite_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [← Finset.sum_subset (wordSet_mono (K := K'))]
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [if_pos (mem_wordSet.mp hu)]
    · intro u hu hnot
      have hlen : K' < u.length := by
        by_contra h
        exact hnot (mem_wordSet.mpr (by omega))
      have hz : lcoef a w u = 0 := lcoef_eq_zero a (by omega)
      simp [hz]

end Rule

/-! ### Multiplication by a smooth coefficient on `W` -/

section MulCoeff

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (ρ : Weight (Eucl n))

theorem lcoef_bounded {a : Eucl n → ℝ} (ha : BddDerivs k a) (w u : List (Fin n))
    (hw : w.length ≤ k) : ∃ B, ∀ x, |lcoef a w u x| ≤ B :=
  (bddDerivs_lcoef ha w hw u).bounded

/-- The `L^p` coefficient operator `f ↦ lcoef a w u · f` (zero if `|w| > k`). -/
def lcoefL {a : Eucl n → ℝ} (ha : BddDerivs k a) (w u : List (Fin n)) {μ : Measure (Eucl n)} :
    Lp F p μ →L[𝕜] Lp F p μ :=
  if hw : w.length ≤ k then
    mulL (lcoef a w u) (contDiff_lcoef ha.1 w u).continuous
      (Classical.choose_spec (lcoef_bounded ha w u hw))
  else 0

/-- The components `∑_u lcoef a α u · ∂^u x` of `a · x`. -/
def mulComponent {a : Eucl n → ℝ} (ha : BddDerivs k a) (α : Idx n k) :
    W (wholeSpace n) ρ 𝕜 F k p →L[𝕜] Lp F p (wμ volume ρ) :=
  ∑ u ∈ wordSet k, (lcoefL ha (Idx.toList α) u).comp (derivL ρ u)

variable {ρ}

theorem coeFn_mulComponent {a : Eucl n → ℝ} (ha : BddDerivs k a) (α : Idx n k)
    (x : W (wholeSpace n) ρ 𝕜 F k p) :
    ⇑(mulComponent ρ ha α x) =ᵐ[wμ volume ρ] fun y =>
      ∑ u ∈ wordSet k, lcoef a (Idx.toList α) u y • (derivL ρ u x) y := by
  have hα : (Idx.toList α).length ≤ k := by
    rw [Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.2
  rw [mulComponent, ContinuousLinearMap.sum_apply]
  have hterm : ∀ u ∈ wordSet k,
      ⇑(((lcoefL (𝕜 := 𝕜) ha (Idx.toList α) u).comp (derivL ρ u)) x) =ᵐ[wμ volume ρ]
        fun y => lcoef a (Idx.toList α) u y • (derivL ρ u x) y := by
    intro u _
    simp only [ContinuousLinearMap.comp_apply, lcoefL, dif_pos hα]
    exact coeFn_mulL _ _ _ _
  filter_upwards [Lp.coeFn_finsetSum (wordSet k) (fun u =>
      ((lcoefL (𝕜 := 𝕜) ha (Idx.toList α) u).comp (derivL ρ u)) x),
    (Filter.eventually_all_finset (wordSet k)).mpr hterm] with y h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun u hu => h2 u hu

theorem coeFn_mulComponent_zero {a : Eucl n → ℝ} (ha : BddDerivs k a)
    (x : W (wholeSpace n) ρ 𝕜 F k p) :
    ⇑(mulComponent ρ ha Idx.zero x) =ᵐ[wμ volume ρ] fun y => a y • (derivL ρ [] x) y := by
  filter_upwards [coeFn_mulComponent ha Idx.zero x] with y hy
  rw [hy, Idx.toList_zero]
  exact sum_lcoef_nil_smul a k (fun u => ⇑(derivL ρ u x)) y

theorem mem_SobSub_mulCoeff {a : Eucl n → ℝ} (ha : BddDerivs k a)
    (x : W (wholeSpace n) ρ 𝕜 F k p) :
    (WithLp.toLp p (fun α => mulComponent ρ ha α x) : SobTuple (wholeSpace n) ρ F k p) ∈
      SobSub (wholeSpace n) ρ 𝕜 F k p := by
  rw [mem_SobSub_iff]
  intro α
  have hα : (Idx.toList α).length ≤ k := by
    rw [Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.2
  have hgl : ∀ u : List (Fin n), u.length ≤ k →
      LocallyIntegrable (⇑(derivL ρ u x) : Eucl n → F) volume :=
    fun u _ => locallyIntegrable_of_memLp (Lp.memLp _)
  have main := hasWeakDeriv_smul_word ha.1 (fun u => ⇑(derivL ρ u x)) hgl
    (fun u hu => hasWeakDeriv_derivL x u hu) (Idx.toList α) hα
  rw [TestDomain.word_eq_map, wholeSpace_dir]
  refine main.congr_ae ?_ ?_
  · exact ((ae_eq_wμ_iff volume ρ).mp (coeFn_mulComponent_zero ha x)).symm
  · exact ((ae_eq_wμ_iff volume ρ).mp (coeFn_mulComponent ha α x)).symm

/-- **Multiplication by a smooth coefficient with bounded derivatives** (S5, `W.mulCoeff`):
`x ↦ a x` on `W^{k,p}(ρ)` over `ℝⁿ`, for `a` smooth with `D^j a` bounded, `j ≤ k`. -/
def W.mulCoeff {a : Eucl n → ℝ} (ha : BddDerivs k a) :
    W (wholeSpace n) ρ 𝕜 F k p →L[𝕜] W (wholeSpace n) ρ 𝕜 F k p :=
  (((PiLp.continuousLinearEquiv p 𝕜 (fun _ : Idx n k =>
      Lp F p (wμ (wholeSpace n).μ ρ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun α => mulComponent ρ ha α))).codRestrict _
    (mem_SobSub_mulCoeff ha)

theorem W.deriv_mulCoeff {a : Eucl n → ℝ} (ha : BddDerivs k a)
    (x : W (wholeSpace n) ρ 𝕜 F k p) (α : Idx n k) :
    W.deriv (wholeSpace n) ρ 𝕜 F k p α (W.mulCoeff ha x) = mulComponent ρ ha α x := rfl

/-- The value of `a · x` is `a · x` a.e. -/
theorem W.coeFn_value_mulCoeff {a : Eucl n → ℝ} (ha : BddDerivs k a)
    (x : W (wholeSpace n) ρ 𝕜 F k p) :
    ⇑(W.value (wholeSpace n) ρ 𝕜 F k p (W.mulCoeff ha x)) =ᵐ[wμ volume ρ]
      fun y => a y • W.value (wholeSpace n) ρ 𝕜 F k p x y := by
  have h := coeFn_mulComponent_zero ha x
  rw [derivL_nil] at h
  exact h

/-- The components of `a · x`: `∂^α (a x) = ∑_{|u| ≤ k} lcoef a α u · ∂^u x` a.e. -/
theorem W.coeFn_deriv_mulCoeff {a : Eucl n → ℝ} (ha : BddDerivs k a)
    (x : W (wholeSpace n) ρ 𝕜 F k p) (α : Idx n k) :
    ⇑(W.deriv (wholeSpace n) ρ 𝕜 F k p α (W.mulCoeff ha x)) =ᵐ[wμ volume ρ]
      fun y => ∑ u ∈ wordSet k, lcoef a (Idx.toList α) u y • (derivL ρ u x) y :=
  coeFn_mulComponent ha α x

end MulCoeff

end UnforcedLeray.Sob
