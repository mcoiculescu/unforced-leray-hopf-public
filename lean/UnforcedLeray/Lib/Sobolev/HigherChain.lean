import UnforcedLeray.Lib.Sobolev.ChainRule
import UnforcedLeray.Lib.Sobolev.Space
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Higher-order weak chain rule under a smooth diffeomorphism (helper for INF11 target S6)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S6, `W.compDiffeo`). Manuscript use: the chain
rule for weak derivatives of every order `j` under the area-preserving flow (tex 1228–1237,
B0062) and under dilations (tex 1569–1580, B0102).

Words are lists of coordinate letters; `wordSet K` is the finite set of words of length
`≤ K`. For `Ψ = Φ⁻¹` the derivative `∂^w (f ∘ Ψ)` of a word `w` is the finite combination
`∑_{u, |u| ≤ K} coef Φ w u · (∂^u f) ∘ Ψ` (`hasWeakDeriv_comp_symm_word`), where the
coefficients are defined by the recursion of the first-order chain rule and the Leibniz rule
(`coefStep`). The coefficients are smooth, vanish for `|u| > |w|`, and are bounded when the
derivatives of `Ψ` of orders `1, …, K` are bounded (`coef_bounded`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

/-! ### Words as lists -/

section Words

variable {n : ℕ}

/-- The letters of a word. -/
def Idx.toList {k : ℕ} (α : Idx n k) : List (Fin n) := List.ofFn α.2

@[simp] theorem Idx.length_toList {k : ℕ} (α : Idx n k) : (Idx.toList α).length = α.1 :=
  List.length_ofFn

/-- A list of length `≤ k` as a word. -/
def Idx.ofList {k : ℕ} (u : List (Fin n)) (h : u.length ≤ k) : Idx n k :=
  ⟨⟨u.length, Nat.lt_succ_of_le h⟩, u.get⟩

@[simp] theorem Idx.toList_ofList {k : ℕ} (u : List (Fin n)) (h : u.length ≤ k) :
    Idx.toList (Idx.ofList u h : Idx n k) = u :=
  List.ofFn_get u

theorem Idx.ofList_nil {k : ℕ} (h : ([] : List (Fin n)).length ≤ k) :
    (Idx.ofList [] h : Idx n k) = Idx.zero :=
  Sigma.ext rfl (heq_of_eq (funext fun i => i.elim0))

@[simp] theorem Idx.toList_zero {k : ℕ} : Idx.toList (Idx.zero : Idx n k) = [] := rfl

theorem TestDomain.word_eq_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (D : TestDomain E n) {k : ℕ} (α : Idx n k) :
    D.word α = (Idx.toList α).map D.dir := by
  rw [TestDomain.word, Idx.toList, List.map_ofFn]
  rfl

/-- Words of length `≤ K`. -/
def wordSet : ℕ → Finset (List (Fin n))
  | 0 => {[]}
  | K + 1 => insert [] ((Finset.univ ×ˢ wordSet K).image fun p => p.1 :: p.2)

theorem mem_wordSet {K : ℕ} {u : List (Fin n)} : u ∈ wordSet K ↔ u.length ≤ K := by
  induction K generalizing u with
  | zero => simp [wordSet]
  | succ K ih => cases u <;> simp [wordSet, ih]

theorem wordSet_mono {K : ℕ} : wordSet (n := n) K ⊆ wordSet (K + 1) := fun u hu =>
  mem_wordSet.mpr ((mem_wordSet.mp hu).trans (Nat.le_succ K))

theorem sum_wordSet_succ {G : Type*} [AddCommMonoid G] (K : ℕ) (F : List (Fin n) → G) :
    ∑ u ∈ wordSet (K + 1), F u = F [] + ∑ l : Fin n, ∑ u ∈ wordSet K, F (l :: u) := by
  have hnot : ([] : List (Fin n)) ∉ (Finset.univ ×ˢ wordSet K).image
      (fun p : Fin n × List (Fin n) => p.1 :: p.2) := by simp
  have hinj : Set.InjOn (fun p : Fin n × List (Fin n) => p.1 :: p.2)
      (((Finset.univ : Finset (Fin n)) ×ˢ wordSet (n := n) K :
        Finset (Fin n × List (Fin n))) : Set (Fin n × List (Fin n))) := by
    rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
    simp only [List.cons.injEq] at h
    rw [h.1, h.2]
  rw [wordSet, Finset.sum_insert hnot, Finset.sum_image hinj, Finset.sum_product]

end Words

/-! ### Bounded derivatives -/

section Bdd

variable {n : ℕ}

theorem natCast_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)

/-- Smooth with bounded derivatives of orders `0, …, r`. -/
def BddDerivs (r : ℕ) (a : Eucl n → ℝ) : Prop :=
  ContDiff ℝ ∞ a ∧ ∀ k ≤ r, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ C

theorem BddDerivs.mono {r s : ℕ} {a : Eucl n → ℝ} (h : BddDerivs r a) (hs : s ≤ r) :
    BddDerivs s a := ⟨h.1, fun k hk => h.2 k (hk.trans hs)⟩

theorem BddDerivs.bounded {r : ℕ} {a : Eucl n → ℝ} (h : BddDerivs r a) :
    ∃ C, ∀ x, |a x| ≤ C := by
  obtain ⟨C, hC⟩ := h.2 0 (Nat.zero_le _)
  exact ⟨C, fun x => by
    have := hC x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this⟩

theorem bddDerivs_const (r : ℕ) (c : ℝ) : BddDerivs r (fun _ : Eucl n => c) := by
  refine ⟨contDiff_const, fun k _ => ⟨|c|, fun x => ?_⟩⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  · rw [iteratedFDeriv_const_of_ne hk.ne' c]
    simp

theorem BddDerivs.add {r : ℕ} {a b : Eucl n → ℝ} (ha : BddDerivs r a) (hb : BddDerivs r b) :
    BddDerivs r (fun x => a x + b x) := by
  refine ⟨ha.1.add hb.1, fun k hk => ?_⟩
  obtain ⟨C, hC⟩ := ha.2 k hk
  obtain ⟨C', hC'⟩ := hb.2 k hk
  refine ⟨C + C', fun x => ?_⟩
  have e : iteratedFDeriv ℝ k (fun x => a x + b x) x =
      iteratedFDeriv ℝ k a x + iteratedFDeriv ℝ k b x :=
    iteratedFDeriv_add_apply (ha.1.contDiffAt.of_le (natCast_le_infty _))
      (hb.1.contDiffAt.of_le (natCast_le_infty _))
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))

theorem BddDerivs.mul {r : ℕ} {a b : Eucl n → ℝ} (ha : BddDerivs r a) (hb : BddDerivs r b) :
    BddDerivs r (fun x => a x * b x) := by
  refine ⟨ha.1.mul hb.1, fun k hk => ?_⟩
  choose C hC using fun i (hi : i ≤ r) => ha.2 i hi
  choose C' hC' using fun i (hi : i ≤ r) => hb.2 i hi
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      (if hi : i ≤ r then C i hi else 0) * (if hi : k - i ≤ r then C' (k - i) hi else 0),
    fun x => ?_⟩
  refine (norm_iteratedFDeriv_mul_le ha.1 hb.1 x (natCast_le_infty _)).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hir : i ≤ r := hik.trans hk
  have hkir : k - i ≤ r := (Nat.sub_le k i).trans hk
  rw [dif_pos hir, dif_pos hkir]
  have h0 : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hC i hir x) h0) (hC' (k - i) hkir x)
    (norm_nonneg _) (mul_nonneg h0 ((norm_nonneg _).trans (hC i hir x)))

theorem norm_iteratedFDeriv_clm_comp_le {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G →L[ℝ] H) {f : Eucl n → G}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : Eucl n) :
    ‖iteratedFDeriv ℝ k (fun y => L (f y)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k f x‖ :=
  L.norm_iteratedFDeriv_comp_left hf.contDiffAt (natCast_le_infty _)

theorem BddDerivs.dirDeriv {r : ℕ} {a : Eucl n → ℝ} (ha : BddDerivs (r + 1) a) (v : Eucl n) :
    BddDerivs r (fun x => fderiv ℝ a x v) := by
  refine ⟨contDiff_dirDeriv ha.1 v, fun k hk => ?_⟩
  obtain ⟨C, hC⟩ := ha.2 (k + 1) (Nat.succ_le_succ hk)
  refine ⟨‖ContinuousLinearMap.apply ℝ ℝ v‖ * C, fun x => ?_⟩
  have hfd : ContDiff ℝ ∞ (fderiv ℝ a) := ha.1.fderiv_right (m := ∞) (by simp)
  have := norm_iteratedFDeriv_clm_comp_le (ContinuousLinearMap.apply ℝ ℝ v) hfd k x
  rw [norm_iteratedFDeriv_fderiv] at this
  exact this.trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))

end Bdd

/-! ### The coefficients -/

section Coeff

variable {n : ℕ} (Φ : Eucl n ≃ₜ Eucl n)

/-- The new part of the chain rule: `(l :: u) ↦ A l j · c u`. -/
def tailTerm (j : Fin n) (c : List (Fin n) → Eucl n → ℝ) : List (Fin n) → Eucl n → ℝ
  | [] => fun _ => 0
  | l :: u => fun x => dsymm Φ l j x * c u x

/-- One step of the recursion: `(∂ⱼ c) u + tailTerm`. -/
def coefStep (j : Fin n) (c : List (Fin n) → Eucl n → ℝ) (u : List (Fin n)) :
    Eucl n → ℝ :=
  fun x => fderiv ℝ (c u) x (e j) + tailTerm Φ j c u x

/-- `coef Φ w u`: the coefficient of `(∂^u f) ∘ Ψ` in `∂^w (f ∘ Ψ)`. -/
def coef : List (Fin n) → List (Fin n) → Eucl n → ℝ
  | [] => fun u _ => if u = [] then 1 else 0
  | j :: w => coefStep Φ j (coef w)

theorem coef_nil (u : List (Fin n)) (x : Eucl n) :
    coef Φ [] u x = if u = [] then 1 else 0 := rfl

theorem coef_cons (j : Fin n) (w u : List (Fin n)) (x : Eucl n) :
    coef Φ (j :: w) u x = fderiv ℝ (coef Φ w u) x (e j) + tailTerm Φ j (coef Φ w) u x := rfl

variable (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)

include hΨ in
theorem contDiff_coef (w u : List (Fin n)) : ContDiff ℝ ∞ (coef Φ w u) := by
  induction w generalizing u with
  | nil =>
    show ContDiff ℝ ∞ (fun _ => if u = [] then (1 : ℝ) else 0)
    exact contDiff_const
  | cons j w ih =>
    refine (contDiff_dirDeriv (ih u) (e j)).add ?_
    cases u with
    | nil => exact contDiff_const
    | cons l u => exact (contDiff_dsymm Φ hΨ l j).mul (ih u)

theorem coef_eq_zero {w u : List (Fin n)} (h : w.length < u.length) : coef Φ w u = 0 := by
  induction w generalizing u with
  | nil =>
    funext x
    rw [coef_nil, if_neg]
    · rfl
    · rintro rfl; simp at h
  | cons j w ih =>
    funext x
    cases u with
    | nil => simp at h
    | cons l u =>
      simp only [List.length_cons, add_lt_add_iff_right] at h
      rw [coef_cons, ih (u := l :: u) (by simp only [List.length_cons]; omega)]
      simp [tailTerm, ih h, Pi.zero_def]

include hΨ in
/-- **Bounded coefficients**: if the derivatives of `Φ⁻¹` of orders `1, …, K` are bounded,
then every coefficient `coef Φ w u` with `|w| ≤ K` has bounded derivatives of orders
`≤ K - |w|`. -/
theorem bddDerivs_coef {K : ℕ}
    (hbd : ∀ k, 1 ≤ k → k ≤ K → ∃ C, ∀ x, ‖iteratedFDeriv ℝ k Φ.symm x‖ ≤ C)
    (w : List (Fin n)) (hw : w.length ≤ K) (u : List (Fin n)) :
    BddDerivs (K - w.length) (coef Φ w u) := by
  have hds : ∀ l j : Fin n, 1 ≤ K → BddDerivs (K - 1) (dsymm Φ l j) := by
    intro l j hK
    refine ⟨contDiff_dsymm Φ hΨ l j, fun k hk => ?_⟩
    obtain ⟨C, hC⟩ := hbd (k + 1) (by omega) (by omega)
    let L : (Eucl n →L[ℝ] Eucl n) →L[ℝ] ℝ :=
      (EuclideanSpace.proj l : Eucl n →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ (Eucl n) (e j))
    refine ⟨‖L‖ * C, fun x => ?_⟩
    have hfd : ContDiff ℝ ∞ (fderiv ℝ Φ.symm) := hΨ.fderiv_right (m := ∞) (by simp)
    have h1 := norm_iteratedFDeriv_clm_comp_le L hfd k x
    rw [norm_iteratedFDeriv_fderiv] at h1
    have e1 : (fun y => L (fderiv ℝ Φ.symm y)) = dsymm Φ l j := by
      funext y; simp [L, dsymm]
    rw [e1] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))
  induction w generalizing u with
  | nil =>
    show BddDerivs (K - 0) (fun _ : Eucl n => if u = [] then (1 : ℝ) else 0)
    exact bddDerivs_const _ _
  | cons j w ih =>
    have hw' : w.length ≤ K := by simp only [List.length_cons] at hw; omega
    have hlen : K - (j :: w).length + 1 = K - w.length := by
      simp only [List.length_cons] at hw ⊢; omega
    have h1 : BddDerivs (K - (j :: w).length) (fun x => fderiv ℝ (coef Φ w u) x (e j)) := by
      have := ih hw' u
      rw [← hlen] at this
      exact this.dirDeriv (e j)
    have h2 : BddDerivs (K - (j :: w).length) (tailTerm Φ j (coef Φ w) u) := by
      cases u with
      | nil => exact bddDerivs_const _ _
      | cons l u =>
        refine ((hds l j (by simp only [List.length_cons] at hw; omega)).mono ?_).mul
          ((ih hw' u).mono ?_)
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega
    exact h1.add h2

end Coeff

/-! ### The weak chain rule for every word -/

section Chain

variable {n : ℕ} (Φ : Eucl n ≃ₜ Eucl n) (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sum_coef_nil_smul (K : ℕ) (g : List (Fin n) → Eucl n → F) (x : Eucl n) :
    ∑ u ∈ wordSet K, coef Φ [] u x • g u (Φ.symm x) = g [] (Φ.symm x) := by
  rw [Finset.sum_eq_single_of_mem [] (mem_wordSet.mpr (Nat.zero_le _))]
  · simp [coef_nil]
  · intro u _ hu
    simp [coef_nil, hu]

include hΦ hΨ in
/-- **Weak chain rule for words** (S6): if `g u = ∂^u f` weakly for every word `|u| ≤ K`
(locally integrable), then for every word `|w| ≤ K`,
`∂^w (f ∘ Φ⁻¹) = ∑_{|u| ≤ K} coef Φ w u · (g u) ∘ Φ⁻¹` weakly. -/
theorem hasWeakDeriv_comp_symm_word {K : ℕ} (g : List (Fin n) → Eucl n → F)
    (hgl : ∀ u, u.length ≤ K → LocallyIntegrable (g u) volume)
    (hgw : ∀ u, u.length ≤ K → HasWeakDeriv (wholeSpace n) (u.map e) (g []) (g u))
    (w : List (Fin n)) (hw : w.length ≤ K) :
    HasWeakDeriv (wholeSpace n) (w.map e) (fun x => g [] (Φ.symm x))
      (fun x => ∑ u ∈ wordSet K, coef Φ w u x • g u (Φ.symm x)) := by
  have hloc : ∀ u, u.length ≤ K → LocallyIntegrable (fun x => g u (Φ.symm x)) volume :=
    fun u hu => locallyIntegrable_comp_symm Φ hΦ hΨ (hgl u hu)
  induction w with
  | nil =>
    have e1 : (fun x => ∑ u ∈ wordSet K, coef Φ [] u x • g u (Φ.symm x)) =
        fun x => g [] (Φ.symm x) := funext (sum_coef_nil_smul Φ K g)
    rw [e1]
    exact HasWeakDeriv.nil fun φ hφ => integrable_smul_of_adm hφ (hloc [] (Nat.zero_le _))
  | cons j w ih =>
    have hwK : w.length < K := by simp only [List.length_cons] at hw; omega
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have ih' := ih (Nat.le_of_lt hwK)
    -- the derivative of each term
    have hterm : ∀ u ∈ wordSet (K' + 1), HasWeakDeriv (wholeSpace n) [e j]
        (fun x => coef Φ w u x • g u (Φ.symm x))
        (fun x => fderiv ℝ (coef Φ w u) x (e j) • g u (Φ.symm x) +
          coef Φ w u x • ∑ l, dsymm Φ l j x • g (l :: u) (Φ.symm x)) := by
      intro u hu
      have huK := mem_wordSet.mp hu
      by_cases hlt : u.length ≤ K'
      · -- `∂ₗ (g u) = g (l :: u)`
        have hGl : ∀ l : Fin n, HasWeakDeriv (wholeSpace n) [e l] (g u) (g (l :: u)) := by
          intro l
          have h2 := (hgw (l :: u) (by simpa using hlt)).perm
            (show (e l :: u.map e).Perm (u.map e ++ [e l]) from List.perm_append_singleton _ _
              |>.symm)
          exact (hgw u huK).of_append h2
        have hc := hasWeakDeriv_comp_symm Φ hΦ hΨ (hgl u huK)
          (fun l => hgl (l :: u) (by simpa using hlt)) hGl j
        exact hc.smul_left (contDiff_coef Φ hΨ w u) (hloc u huK)
          (locallyIntegrable_finsetSum _ fun l _ =>
            (hloc (l :: u) (by simpa using hlt)).continuous_smul
              (contDiff_dsymm Φ hΨ l j).continuous)
      · have hz : coef Φ w u = 0 := coef_eq_zero Φ (by omega)
        have e1 : (fun x => coef Φ w u x • g u (Φ.symm x)) = 0 := by
          funext x; simp [hz]
        have e2 : (fun x => fderiv ℝ (coef Φ w u) x (e j) • g u (Φ.symm x) +
            coef Φ w u x • ∑ l, dsymm Φ l j x • g (l :: u) (Φ.symm x)) = 0 := by
          funext x; simp [hz, Pi.zero_def]
        rw [e1, e2]
        exact HasWeakDeriv.zero
    have hsum := HasWeakDeriv.sum _ hterm
    refine ih'.cons (hsum.congr_ae (Eventually.of_forall fun x => rfl)
      (Eventually.of_forall fun x => ?_))
    -- reindex the sum
    simp only [coef_cons, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum,
      smul_smul]
    congr 1
    rw [sum_wordSet_succ K' (fun u => tailTerm Φ j (coef Φ w) u x • g u (Φ.symm x))]
    simp only [tailTerm, zero_smul, zero_add]
    rw [← Finset.sum_subset (wordSet_mono (K := K'))]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun u _ => ?_
      rw [mul_comm]
    · intro u hu hnot
      have hlen : K' < u.length := by
        by_contra h
        exact hnot (mem_wordSet.mpr (by omega))
      have hz : coef Φ w u = 0 := coef_eq_zero Φ (by omega)
      simp [hz]

end Chain

end UnforcedLeray.Sob
