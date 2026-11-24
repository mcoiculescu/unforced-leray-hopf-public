import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs

/-!
# `wordW_smul_bound` (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1/8`)

Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4963-4985.

Leibniz for the conormal operators: `s∂_s` (= `opW 0`) is a derivation, and `∂_q`, `∂_η`
(= `opW 1`, `opW 2`) kill functions of `s` alone. Hence every word `w` applied to `a(s)·G` is a
finite list of terms `(s∂_s)^k a(s) · wordW u G` with `k ≤ |w|`, `|u| ≤ |w|`, at most `2^|w|` terms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The open chart region `s > 0` is open. -/
lemma wsb_open : IsOpen UChart := isOpen_Ioi.prod isOpen_univ

lemma wsb_mem_budget_iff {w : List (Fin 3)} : w ∈ budgetWords ↔ w.length ≤ 4 := by
  constructor
  · intro h
    unfold budgetWords at h
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and] at h
    obtain ⟨n, hn, f, rfl⟩ := h
    simp only [List.length_ofFn]
    omega
  · intro h
    unfold budgetWords
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨w.length, by omega, w.get, List.ofFn_get w⟩

/-- Smoothness of `(s∂_s)^k a` on `s > 0`, losing one order per application. -/
lemma wsb_sDerivIterR_cdo (a : ℝ → ℝ) (ha : ContDiffOn ℝ 4 a (Ioi 0)) :
    ∀ (k n : ℕ), k + n ≤ 4 → ContDiffOn ℝ (n : WithTop ℕ∞) (sDerivIterR k a) (Ioi 0) := by
  intro k
  induction k with
  | zero =>
    intro n hn
    exact ha.of_le (by exact_mod_cast (show n ≤ 4 by omega))
  | succ k ih =>
    intro n hn
    have h1 := ih (n + 1) (by omega)
    have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (deriv (sDerivIterR k a)) (Ioi 0) :=
      h1.deriv_of_isOpen isOpen_Ioi (by norm_cast)
    exact contDiffOn_id.mul h2

/-- Smoothness of a conormal operator, losing one order. -/
lemma wsb_opW_cdo (x : Fin 3) (F : Chart → Merid) (n : ℕ)
    (hF : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F UChart) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (opW x F) UChart := by
  have hfd : ContDiffOn ℝ (n : WithTop ℕ∞) (fun y => fderiv ℝ F y) UChart :=
    hF.fderiv_of_isOpen wsb_open (by norm_cast)
  fin_cases x
  · show ContDiffOn ℝ _ (fun p : Chart => p.1 • fderiv ℝ F p (1, (0, 0))) UChart
    exact contDiffOn_fst.smul (hfd.clm_apply contDiffOn_const)
  · show ContDiffOn ℝ _ (fun p : Chart => fderiv ℝ F p (0, (1, 0))) UChart
    exact hfd.clm_apply contDiffOn_const
  · show ContDiffOn ℝ _ (fun p : Chart => fderiv ℝ F p (0, (0, 1))) UChart
    exact hfd.clm_apply contDiffOn_const

/-- Smoothness of every conormal word of length `≤ 4 - n` on `UChart`. -/
lemma wsb_wordW_cdo (G : Chart → Merid) (hG : ContDiffOn ℝ 4 G UChart) :
    ∀ (u : List (Fin 3)) (n : ℕ), u.length + n ≤ 4 →
      ContDiffOn ℝ (n : WithTop ℕ∞) (wordW u G) UChart := by
  intro u
  induction u with
  | nil =>
    intro n hn
    simp only [List.length_nil, zero_add] at hn
    exact hG.of_le (by exact_mod_cast (show n ≤ 4 by omega))
  | cons x u ih =>
    intro n hn
    simp only [List.length_cons] at hn
    exact wsb_opW_cdo x (wordW u G) n (ih (n + 1) (by omega))

lemma wsb_wordW_diffAt (G : Chart → Merid) (hG : ContDiffOn ℝ 4 G UChart) (u : List (Fin 3))
    (hu : u.length ≤ 3) (q : Chart) (hq : q ∈ UChart) :
    DifferentiableAt ℝ (wordW u G) q :=
  ((wsb_wordW_cdo G hG u 1 (by omega)).differentiableOn (by norm_num)).differentiableAt
    (wsb_open.mem_nhds hq)

lemma wsb_sDerivIterR_diffAt (a : ℝ → ℝ) (ha : ContDiffOn ℝ 4 a (Ioi 0)) (k : ℕ) (hk : k ≤ 3)
    (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ (sDerivIterR k a) t :=
  ((wsb_sDerivIterR_cdo a ha k 1 (by omega)).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ht))

lemma wsb_term_diffAt (a : ℝ → ℝ) (ha : ContDiffOn ℝ 4 a (Ioi 0)) (G : Chart → Merid)
    (hG : ContDiffOn ℝ 4 G UChart) (k : ℕ) (u : List (Fin 3)) (hk : k ≤ 3) (hu : u.length ≤ 3)
    (q : Chart) (hq : q ∈ UChart) :
    DifferentiableAt ℝ (fun p : Chart => sDerivIterR k a p.1 • wordW u G p) q := by
  have hφ : DifferentiableAt ℝ (fun p : Chart => sDerivIterR k a p.1) q :=
    (wsb_sDerivIterR_diffAt a ha k hk q.1 hq.1).comp q differentiableAt_fst
  exact hφ.smul (wsb_wordW_diffAt G hG u hu q hq)

/-- `∂_s` of a product with a function of `s` alone. -/
lemma wsb_fderiv_fst (φ : ℝ → ℝ) (q : Chart) (hφ : DifferentiableAt ℝ φ q.1) (v : Chart) :
    fderiv ℝ (fun p : Chart => φ p.1) q v = deriv φ q.1 * v.1 := by
  have h1 : HasFDerivAt φ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv φ q.1)) q.1 :=
    hφ.hasDerivAt.hasFDerivAt
  have h2 := h1.comp q hasFDerivAt_fst
  rw [show (fun p : Chart => φ p.1) = φ ∘ Prod.fst from rfl, h2.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, mul_comm]

lemma wsb_fderiv_smul (φ : ℝ → ℝ) (H : Chart → Merid) (q : Chart)
    (hφ : DifferentiableAt ℝ φ q.1) (hH : DifferentiableAt ℝ H q) (v : Chart) :
    fderiv ℝ (fun p : Chart => φ p.1 • H p) q v
      = φ q.1 • fderiv ℝ H q v + (deriv φ q.1 * v.1) • H q := by
  have hc : DifferentiableAt ℝ (fun p : Chart => φ p.1) q := hφ.comp q differentiableAt_fst
  have h : fderiv ℝ (fun p : Chart => φ p.1 • H p) q
      = φ q.1 • fderiv ℝ H q + (fderiv ℝ (fun p : Chart => φ p.1) q).smulRight (H q) :=
    (hc.hasFDerivAt.smul hH.hasFDerivAt).fderiv
  rw [h, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, wsb_fderiv_fst φ q hφ v]

/-- Leibniz for `s∂_s`: a derivation hitting the `s`-factor. -/
lemma wsb_opW0_mul (φ : ℝ → ℝ) (H : Chart → Merid) (q : Chart)
    (hφ : DifferentiableAt ℝ φ q.1) (hH : DifferentiableAt ℝ H q) :
    opW 0 (fun p : Chart => φ p.1 • H p) q
      = (q.1 * deriv φ q.1) • H q + φ q.1 • opW 0 H q := by
  simp only [opW, UnforcedLeray.Axi.dS]
  rw [wsb_fderiv_smul φ H q hφ hH]
  simp only [smul_add, smul_smul, mul_one]
  module

/-- `∂_q`, `∂_η` do not differentiate the `s`-factor. -/
lemma wsb_opW_ne0_mul (x : Fin 3) (hx : x ≠ 0) (φ : ℝ → ℝ) (H : Chart → Merid) (q : Chart)
    (hφ : DifferentiableAt ℝ φ q.1) (hH : DifferentiableAt ℝ H q) :
    opW x (fun p : Chart => φ p.1 • H p) q = φ q.1 • opW x H q := by
  fin_cases x
  · exact absurd rfl hx
  · simp only [opW, UnforcedLeray.Axi.dQ]
    rw [wsb_fderiv_smul φ H q hφ hH]
    simp
  · simp only [opW, UnforcedLeray.Axi.dEta]
    rw [wsb_fderiv_smul φ H q hφ hH]
    simp

/-- Congruence of a conormal operator at a point (only the germ at the point matters). -/
lemma wsb_opW_congr (x : Fin 3) {F F' : Chart → Merid} {q : Chart}
    (h : F =ᶠ[𝓝 q] F') : opW x F q = opW x F' q := by
  have e1 : fderiv ℝ F q = fderiv ℝ F' q := h.fderiv_eq
  fin_cases x
  · simp [opW, UnforcedLeray.Axi.dS, e1]
  · simp [opW, UnforcedLeray.Axi.dQ, e1]
  · simp [opW, UnforcedLeray.Axi.dEta, e1]

/-- Derivatives of a finite list sum of differentiable terms. -/
lemma wsb_list_hasFDeriv {ι : Type} (f : ι → Chart → Merid) (q : Chart) :
    ∀ (l : List ι), (∀ i ∈ l, DifferentiableAt ℝ (f i) q) →
      DifferentiableAt ℝ (fun p => (l.map fun i => f i p).sum) q ∧
      ∀ v : Chart, fderiv ℝ (fun p => (l.map fun i => f i p).sum) q v
        = (l.map fun i => fderiv ℝ (f i) q v).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨by simp, fun v => by simp⟩
  | cons i l ih =>
    intro hd
    obtain ⟨h1, h2⟩ := ih (fun j hj => hd j (List.mem_cons_of_mem _ hj))
    have hi : DifferentiableAt ℝ (f i) q := hd i (by simp)
    have hsum : DifferentiableAt ℝ (fun p => f i p + (l.map fun j => f j p).sum) q :=
      hi.add h1
    refine ⟨?_, fun v => ?_⟩
    · show DifferentiableAt ℝ (fun p => f i p + (l.map fun j => f j p).sum) q
      exact hsum
    · have h : fderiv ℝ (fun p => f i p + (l.map fun j => f j p).sum) q
          = fderiv ℝ (f i) q + fderiv ℝ (fun p => (l.map fun j => f j p).sum) q :=
        (hi.hasFDerivAt.add h1.hasFDerivAt).fderiv
      show fderiv ℝ (fun p => f i p + (l.map fun j => f j p).sum) q v
        = fderiv ℝ (f i) q v + (l.map fun j => fderiv ℝ (f j) q v).sum
      rw [h, add_apply, h2 v]

/-- A conormal operator on a finite list sum. -/
lemma wsb_opW_list {ι : Type} (x : Fin 3) (f : ι → Chart → Merid) (q : Chart) (l : List ι)
    (hd : ∀ i ∈ l, DifferentiableAt ℝ (f i) q) :
    opW x (fun p => (l.map fun i => f i p).sum) q = (l.map fun i => opW x (f i) q).sum := by
  obtain ⟨-, h2⟩ := wsb_list_hasFDeriv f q l hd
  fin_cases x
  · simp only [opW, UnforcedLeray.Axi.dS]
    rw [h2, List.smul_sum, List.map_map]
    rfl
  · simp only [opW, UnforcedLeray.Axi.dQ]
    rw [h2]
  · simp only [opW, UnforcedLeray.Axi.dEta]
    rw [h2]

lemma wsb_sum_map_add {ι : Type} (l : List ι) (A B : ι → Merid) :
    (l.map fun i => A i + B i).sum = (l.map A).sum + (l.map B).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, ih]; abel

lemma wsb_norm_list_sum_le {ι : Type} (l : List ι) (f : ι → Merid) (B : ℝ)
    (h : ∀ i ∈ l, ‖f i‖ ≤ B) : ‖(l.map f).sum‖ ≤ (l.length : ℝ) * B := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi := h i (by simp)
    have hl := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc ‖f i + (l.map f).sum‖ ≤ ‖f i‖ + ‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ B + (l.length : ℝ) * B := add_le_add hi hl
      _ = ((l.length + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- The Leibniz representation of a word applied to `a·G`. -/
def WsbRep (a : ℝ → ℝ) (G : Chart → Merid) (w : List (Fin 3)) : Prop :=
  ∃ L : List (ℕ × List (Fin 3)), L.length ≤ 2 ^ w.length ∧
    (∀ kv ∈ L, kv.1 ≤ w.length ∧ kv.2.length ≤ w.length) ∧
    ∀ q ∈ UChart, wordW w (fun p => a p.1 • G p) q
      = (L.map fun kv => sDerivIterR kv.1 a q.1 • wordW kv.2 G q).sum

lemma wsb_rep (a : ℝ → ℝ) (ha : ContDiffOn ℝ 4 a (Ioi 0)) (G : Chart → Merid)
    (hG : ContDiffOn ℝ 4 G UChart) :
    ∀ w : List (Fin 3), w.length ≤ 4 → WsbRep a G w := by
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨[(0, [])], by simp, by simp, fun q _ => ?_⟩
    simp [wordW, sDerivIterR]
  | cons x w ih =>
    intro hlen
    simp only [List.length_cons] at hlen
    obtain ⟨L, hL1, hL2, hL3⟩ := ih (by omega)
    have hEq : ∀ q ∈ UChart, wordW (x :: w) (fun p => a p.1 • G p) q
        = opW x (fun p : Chart => (L.map fun kv => sDerivIterR kv.1 a p.1 • wordW kv.2 G p).sum) q := by
      intro q hq
      apply wsb_opW_congr x
      exact Filter.eventually_of_mem (wsb_open.mem_nhds hq) (fun p hp => hL3 p hp)
    have hdiff : ∀ q ∈ UChart, ∀ kv ∈ L,
        DifferentiableAt ℝ (fun p : Chart => sDerivIterR kv.1 a p.1 • wordW kv.2 G p) q :=
      fun q hq kv hkv => wsb_term_diffAt a ha G hG kv.1 kv.2
        (by have := (hL2 kv hkv).1; omega) (by have := (hL2 kv hkv).2; omega) q hq
    by_cases hx : x = 0
    · subst hx
      refine ⟨L.map (fun kv => (kv.1 + 1, kv.2)) ++ L.map (fun kv => (kv.1, (0 : Fin 3) :: kv.2)),
        ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_map, List.length_cons]
        calc L.length + L.length ≤ 2 ^ w.length + 2 ^ w.length := Nat.add_le_add hL1 hL1
          _ = 2 ^ (w.length + 1) := by ring
      · intro kv hkv
        simp only [List.mem_append, List.mem_map] at hkv
        rcases hkv with ⟨kv', hkv', rfl⟩ | ⟨kv', hkv', rfl⟩
        · have := hL2 kv' hkv'
          dsimp only
          simp only [List.length_cons]
          constructor <;> omega
        · have := hL2 kv' hkv'
          dsimp only
          simp only [List.length_cons]
          constructor <;> omega
      · intro q hq
        rw [hEq q hq, wsb_opW_list 0 (fun kv p => sDerivIterR kv.1 a p.1 • wordW kv.2 G p) q L
          (fun kv hkv => hdiff q hq kv hkv)]
        have hterm : ∀ kv ∈ L,
            opW 0 (fun p : Chart => sDerivIterR kv.1 a p.1 • wordW kv.2 G p) q
              = sDerivIterR (kv.1 + 1) a q.1 • wordW kv.2 G q
                + sDerivIterR kv.1 a q.1 • wordW (0 :: kv.2) G q := by
          intro kv hkv
          rw [wsb_opW0_mul (sDerivIterR kv.1 a) (wordW kv.2 G) q
            (wsb_sDerivIterR_diffAt a ha kv.1 (by have := (hL2 kv hkv).1; omega) q.1 hq.1)
            (wsb_wordW_diffAt G hG kv.2 (by have := (hL2 kv hkv).2; omega) q hq)]
          rfl
        rw [List.map_congr_left hterm, wsb_sum_map_add]
        simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
    · refine ⟨L.map (fun kv => (kv.1, x :: kv.2)), ?_, ?_, ?_⟩
      · simp only [List.length_map, List.length_cons]
        calc L.length ≤ 2 ^ w.length := hL1
          _ ≤ 2 ^ (w.length + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      · intro kv hkv
        simp only [List.mem_map] at hkv
        obtain ⟨kv', hkv', rfl⟩ := hkv
        have := hL2 kv' hkv'
        dsimp only
        simp only [List.length_cons]
        constructor <;> omega
      · intro q hq
        rw [hEq q hq, wsb_opW_list x (fun kv p => sDerivIterR kv.1 a p.1 • wordW kv.2 G p) q L
          (fun kv hkv => hdiff q hq kv hkv)]
        have hterm : ∀ kv ∈ L,
            opW x (fun p : Chart => sDerivIterR kv.1 a p.1 • wordW kv.2 G p) q
              = sDerivIterR kv.1 a q.1 • wordW (x :: kv.2) G q := by
          intro kv hkv
          rw [wsb_opW_ne0_mul x hx (sDerivIterR kv.1 a) (wordW kv.2 G) q
            (wsb_sDerivIterR_diffAt a ha kv.1 (by have := (hL2 kv hkv).1; omega) q.1 hq.1)
            (wsb_wordW_diffAt G hG kv.2 (by have := (hL2 kv hkv).2; omega) q hq)]
          rfl
        rw [List.map_congr_left hterm]
        simp only [List.map_map, Function.comp_def]

/-- **Word bound (source 5063-5071, 5076-5079).** -/
theorem wordW_smul_bound (a : ℝ → ℝ) (G : Chart → Merid) (ha : ContDiffOn ℝ 4 a (Set.Ioi 0))
    (hG : ContDiffOn ℝ 4 G UChart) (w : List (Fin 3)) (hw : w ∈ budgetWords) (q : Chart)
    (hq : q ∈ UChart) :
    ‖wordW w (fun p => a p.1 • G p) q‖ ≤ 16 * (∑ i ∈ Finset.range 5, |sDerivIterR i a q.1|) *
      ∑ w' ∈ budgetWords, ‖wordW w' G q‖ := by
  have hwlen : w.length ≤ 4 := wsb_mem_budget_iff.mp hw
  obtain ⟨L, hL1, hL2, hL3⟩ := wsb_rep a ha G hG w hwlen
  rw [hL3 q hq]
  set C1 : ℝ := ∑ i ∈ Finset.range 5, |sDerivIterR i a q.1| with hC1def
  set S : ℝ := ∑ w' ∈ budgetWords, ‖wordW w' G q‖ with hSdef
  have hC1 : 0 ≤ C1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hterm : ∀ kv ∈ L,
      ‖sDerivIterR kv.1 a q.1 • wordW kv.2 G q‖ ≤ C1 * S := by
    intro kv hkv
    have hk5 : kv.1 ∈ Finset.range 5 := Finset.mem_range.mpr (by have := (hL2 kv hkv).1; omega)
    have hu : kv.2 ∈ budgetWords := wsb_mem_budget_iff.mpr (by have := (hL2 kv hkv).2; omega)
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul
    · exact Finset.single_le_sum (f := fun i => |sDerivIterR i a q.1|)
        (fun i _ => abs_nonneg _) hk5
    · exact Finset.single_le_sum (f := fun w' => ‖wordW w' G q‖)
        (fun i _ => norm_nonneg _) hu
    · exact norm_nonneg _
    · exact hC1
  have hsum := wsb_norm_list_sum_le L _ (C1 * S) hterm
  have hLlen : (L.length : ℝ) ≤ 16 := by
    have h16 : L.length ≤ 16 := by
      calc L.length ≤ 2 ^ w.length := hL1
        _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hwlen
        _ = 16 := by norm_num
    exact_mod_cast h16
  calc ‖(L.map fun kv => sDerivIterR kv.1 a q.1 • wordW kv.2 G q).sum‖
      ≤ (L.length : ℝ) * (C1 * S) := hsum
    _ ≤ 16 * (C1 * S) := mul_le_mul_of_nonneg_right hLlen (mul_nonneg hC1 hS)
    _ = 16 * C1 * S := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
