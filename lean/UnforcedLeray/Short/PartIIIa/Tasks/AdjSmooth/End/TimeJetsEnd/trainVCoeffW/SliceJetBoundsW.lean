import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PdEcCont

/-!
# `SliceJetBoundsW`: one-sided age jets of a function smooth on `[0, ∞) × ℝ²`

Source: `the November 2 reference manuscript` lines 270-288, 2866-2870, 3060-3061.
One-sided (within `[0, ∞) × ℝ²`) transcription of `SliceJetBounds` (`Tasks/AdjSmooth/Interior/
TimeJets/SliceJetBounds.lean`), valid down to the age `0`: the age jets are
`iteratedDerivWithin … (Ici 0)`, and the claims are on `Ico a b` with `a ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa
namespace SliceJBW

abbrev E : Type := ℝ × (ℝ × ℝ)

/-- The closed half-space `[0, ∞) × ℝ²`. -/
def U : Set E := Ici 0 ×ˢ univ

lemma uU : UniqueDiffOn ℝ U := PdEc.strip_uniqueDiff

def e0 : E := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))

lemma norm_e0 : ‖e0‖ ≤ 1 := by simp [e0, Prod.norm_def]

/-- `g` is, on `U`, the `n`-th derivative of `V` within `U` applied to fixed vectors of norm `≤ 1`. -/
def Dk (V : E → ℝ) (n : ℕ) (g : E → ℝ) : Prop :=
  ∃ m : Fin n → E, (∀ k, ‖m k‖ ≤ 1) ∧ ∀ p ∈ U, g p = iteratedFDerivWithin ℝ n V U p m

lemma Dk.congr {V : E → ℝ} {n : ℕ} {g g' : E → ℝ} (h : Dk V n g) (heq : ∀ p ∈ U, g' p = g p) :
    Dk V n g' := by
  obtain ⟨m, hm, h⟩ := h
  exact ⟨m, hm, fun p hp => by rw [heq p hp, h p hp]⟩

lemma cdIter {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedFDerivWithin ℝ n V U) U := by
  intro p hp
  exact (hV p hp).iteratedFDerivWithin_right uU (by exact_mod_cast le_top) hp

lemma Dk.contDiffOn {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {n : ℕ} {g : E → ℝ} (h : Dk V n g) :
    ContDiffOn ℝ ∞ g U := by
  obtain ⟨m, -, hm⟩ := h
  have h2 : ContDiffOn ℝ ∞ (fun y => iteratedFDerivWithin ℝ n V U y m) U :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ m).contDiff.comp_contDiffOn
      (cdIter hV n)
  exact h2.congr hm

lemma Dk.abs_le {V : E → ℝ} {n : ℕ} {g : E → ℝ} (h : Dk V n g) {p : E} (hp : p ∈ U) :
    |g p| ≤ ‖iteratedFDerivWithin ℝ n V U p‖ := by
  obtain ⟨m, hm, h⟩ := h
  rw [h p hp, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ m).trans ?_
  have : ∏ i, ‖m i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hm i)
  nlinarith [norm_nonneg (iteratedFDerivWithin ℝ n V U p)]

lemma Dk.fderivWithin {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {n : ℕ} {g : E → ℝ} (h : Dk V n g)
    {v : E} (hv : ‖v‖ ≤ 1) : Dk V (n + 1) (fun p => _root_.fderivWithin ℝ g U p v) := by
  obtain ⟨m, hm, hg⟩ := h
  refine ⟨Fin.cons v m, ?_, ?_⟩
  · intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hv
    · simpa using hm i
  · intro p hp
    have hd : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ n V U) U p :=
      ((cdIter hV n) p hp).differentiableWithinAt (by simp)
    have e1 : _root_.fderivWithin ℝ g U p =
        _root_.fderivWithin ℝ (fun y => iteratedFDerivWithin ℝ n V U y m) U p :=
      fderivWithin_congr hg (hg p hp)
    show _root_.fderivWithin ℝ g U p v = _
    rw [e1, iteratedFDerivWithin_succ_apply_left,
      fderivWithin_continuousMultilinear_apply_const (uU p hp) hd]
    simp

/-- The age derivative of a derivative-type function along a slice. -/
lemma deriv_slice {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {n : ℕ} {g : E → ℝ} (h : Dk V n g)
    {s : ℝ} {x : ℝ × ℝ} (hp : (s, x) ∈ U) :
    HasDerivWithinAt (fun s => g (s, x)) (_root_.fderivWithin ℝ g U (s, x) e0) (Ici 0) s := by
  have hd : DifferentiableWithinAt ℝ g U (s, x) :=
    ((h.contDiffOn hV) _ hp).differentiableWithinAt (by simp)
  have hγ : HasDerivWithinAt (fun s : ℝ => (s, x)) e0 (Ici 0) s :=
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x)).hasDerivWithinAt
  exact hd.hasFDerivWithinAt.comp_hasDerivWithinAt s hγ (fun s' (hs' : s' ∈ Ici (0 : ℝ)) => show (s', x) ∈ U from ⟨hs', trivial⟩)

/-- The age jet `∂_r^i V(p.1, p.2)` within `[0, ∞)`. -/
def Fj (V : E → ℝ) (i : ℕ) (p : E) : ℝ :=
  iteratedDerivWithin i (fun s => V (s, p.2)) (Ici 0) p.1

lemma slice_Dk {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) : Dk V i (Fj V i) := by
  induction i with
  | zero =>
    refine ⟨Fin.elim0, fun k => k.elim0, fun p hp => ?_⟩
    simp [Fj, iteratedFDerivWithin_zero_apply]
  | succ i ih =>
    refine (ih.fderivWithin hV norm_e0).congr ?_
    intro p hp
    have := ((deriv_slice hV ih (s := p.1) (x := p.2) hp).derivWithin
      ((uniqueDiffOn_Ici (0 : ℝ)) _ hp.1))
    simp only [Fj, iteratedDerivWithin_succ]
    exact this

lemma fj_succ {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) {p : E} (hp : p ∈ U) :
    Fj V (i + 1) p = _root_.fderivWithin ℝ (Fj V i) U p e0 := by
  have := ((deriv_slice hV (slice_Dk hV i) (s := p.1) (x := p.2) hp).derivWithin
    ((uniqueDiffOn_Ici (0 : ℝ)) _ hp.1))
  simp only [Fj, iteratedDerivWithin_succ]
  exact this

lemma hasDeriv_Fj {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) {s : ℝ} {x : ℝ × ℝ}
    (hp : (s, x) ∈ U) :
    HasDerivWithinAt (fun s => Fj V i (s, x)) (Fj V (i + 1) (s, x)) (Ici 0) s := by
  rw [fj_succ hV i hp]
  exact deriv_slice hV (slice_Dk hV i) hp

/-- The word derivative `∂^w` of the slice, as a function of `(r, x)`. -/
def Gw (V : E → ℝ) (i : ℕ) (w : List (Fin 2)) (p : E) : ℝ :=
  rSpatial w (fun y => Fj V i (p.1, y)) p.2

lemma norm_dir (j : Fin 2) : ‖((0 : ℝ), B0579.dir j)‖ ≤ 1 := by
  fin_cases j <;> simp [B0579.dir, Prod.norm_def]

lemma spatial_Dk {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) (w : List (Fin 2)) :
    Dk V (i + w.length) (Gw V i w) := by
  induction w with
  | nil => exact (slice_Dk hV i).congr (fun p _ => rfl)
  | cons j w ih =>
    have h1 := ih.fderivWithin hV (norm_dir j)
    refine h1.congr ?_
    intro p hp
    have := PdEc.fderiv_slice_apply (ih.contDiffOn hV) hp.1 p.2 (B0579.dir j)
    simp only [Gw, rSpatial, B0579.pd]
    exact this

/-- Mean value inequality in the age. -/
lemma mvt {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {n : ℕ} {g : E → ℝ} (h : Dk V n g) {S K : ℝ}
    (x : ℝ × ℝ)
    (hK : ∀ ρ ∈ Icc (0 : ℝ) S, ‖iteratedFDerivWithin ℝ (n + 1) V U (ρ, x)‖ ≤ K)
    {r r' : ℝ} (hr : r ∈ Icc (0 : ℝ) S) (hr' : r' ∈ Icc (0 : ℝ) S) :
    |g (r', x) - g (r, x)| ≤ K * |r' - r| := by
  have hU : ∀ s ∈ Icc (0 : ℝ) S, (s, x) ∈ U := fun s hs => ⟨hs.1, trivial⟩
  have := (convex_Icc (0 : ℝ) S).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => g (s, x)) (f' := fun s => _root_.fderivWithin ℝ g U (s, x) e0) (C := K)
    (fun s hs => (deriv_slice hV h (hU s hs)).mono Icc_subset_Ici_self)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact ((h.fderivWithin hV norm_e0).abs_le (hU s hs)).trans (hK s hs)) hr hr'
  simpa [Real.norm_eq_abs] using this

/-- First-order Taylor bound in the age. -/
lemma taylor {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) {S K : ℝ} (x : ℝ × ℝ)
    (hK : ∀ ρ ∈ Icc (0 : ℝ) S, ‖iteratedFDerivWithin ℝ (i + 1 + 1) V U (ρ, x)‖ ≤ K)
    {r r' : ℝ} (hr : r ∈ Icc (0 : ℝ) S) (hr' : r' ∈ Icc (0 : ℝ) S) (hne : r' ≠ r) :
    |(r' - r)⁻¹ * (Fj V i (r', x) - Fj V i (r, x)) - Fj V (i + 1) (r, x)| ≤ K * |r' - r| := by
  have hU : ∀ s ∈ Icc (0 : ℝ) S, (s, x) ∈ U := fun s hs => ⟨hs.1, trivial⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK r hr)
  have hsub : uIcc r r' ⊆ Icc (0 : ℝ) S := (ordConnected_Icc).uIcc_subset hr hr'
  set A' := Fj V (i + 1) (r, x) with hA'
  have key := (convex_uIcc r r').norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => Fj V i (s, x) - Fj V i (r, x) - (s - r) * A')
    (f' := fun s => Fj V (i + 1) (s, x) - A') (C := K * |r' - r|)
    (fun s hs => by
      have h1 := (hasDeriv_Fj hV i (hU s (hsub hs)))
      have h2 : HasDerivWithinAt (fun s : ℝ => (s - r) * A') A' (Ici 0) s := by
        simpa using (((hasDerivAt_id s).sub_const r).mul_const A').hasDerivWithinAt
      have := (h1.sub_const (Fj V i (r, x))).sub h2
      exact this.mono (fun y hy => (hsub hy).1))
    (fun s hs => by
      rw [Real.norm_eq_abs]
      have := mvt hV (slice_Dk hV (i + 1)) x hK hr (hsub hs)
      have h3 : |s - r| ≤ |r' - r| := Set.abs_sub_left_of_mem_uIcc hs
      calc |Fj V (i + 1) (s, x) - A'| ≤ K * |s - r| := this
        _ ≤ K * |r' - r| := mul_le_mul_of_nonneg_left h3 hK0)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [sub_self, zero_mul, sub_zero, Real.norm_eq_abs] at key
  have hpos : 0 < |r' - r| := abs_pos.2 (sub_ne_zero.2 hne)
  have hr0 : r' - r ≠ 0 := sub_ne_zero.2 hne
  have : (r' - r)⁻¹ * (Fj V i (r', x) - Fj V i (r, x)) - A' =
      (r' - r)⁻¹ * (Fj V i (r', x) - Fj V i (r, x) - (r' - r) * A') := by
    field_simp
  rw [this, abs_mul, abs_inv]
  rw [inv_mul_le_iff₀ hpos]
  calc _ ≤ K * |r' - r| * |r' - r| := key
    _ = _ := by ring

end SliceJBW

open SliceJBW in
/-- **One-sided age jets of a function smooth on `[0, ∞) × ℝ²`** (SP 270-288, 2866-2870). -/
theorem sliceJetBoundsW (V : ℝ × (ℝ × ℝ) → ℝ) (wt : ℝ × ℝ → ℝ) (hwt : ∀ x : ℝ × ℝ, 0 < wt x)
    (hV : ContDiffOn ℝ ∞ V (Ici 0 ×ˢ univ))
    (hC : ∀ (n : ℕ) (S : ℝ), ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      wt x * ‖iteratedFDerivWithin ℝ n V (Ici 0 ×ˢ univ) (ρ, x)‖ ≤ C)
    (a b : ℝ) (ha : 0 ≤ a) (i : ℕ) :
    (∀ r ∈ Ico a b, ContDiff ℝ ∞
        (fun x => iteratedDerivWithin i (fun ρ => V (ρ, x)) (Ici 0) r)) ∧
      (∀ (w : List (Fin 2)), ∀ r ∈ Ico a b,
        (∃ C : ℝ, ∀ x : ℝ × ℝ,
          wt x * |rSpatial w
            (fun y => iteratedDerivWithin i (fun ρ => V (ρ, y)) (Ici 0) r) x| ≤ C) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ r' in 𝓝[Ico a b] r, ∀ x : ℝ × ℝ,
          wt x * |rSpatial w (fun y => iteratedDerivWithin i (fun ρ => V (ρ, y)) (Ici 0) r') x -
            rSpatial w (fun y => iteratedDerivWithin i (fun ρ => V (ρ, y)) (Ici 0) r) x| ≤ ε) ∧
      HasCoeffDeriv (Ico a b) wt
        (fun r x => iteratedDerivWithin i (fun ρ => V (ρ, x)) (Ici 0) r)
        (fun r x => iteratedDerivWithin (i + 1) (fun ρ => V (ρ, x)) (Ici 0) r) := by
  have hV' : ContDiffOn ℝ ∞ V U := hV
  have hrU : ∀ r ∈ Ico a b, ∀ x : ℝ × ℝ, (r, x) ∈ U := fun r hr x => ⟨ha.trans hr.1, trivial⟩
  have hsub : ∀ r ∈ Ico a b, r ∈ Icc (0 : ℝ) (b + 1) :=
    fun r hr => ⟨ha.trans hr.1, by linarith [hr.2]⟩
  have hdiv : ∀ (n : ℕ) (C : ℝ), (∀ ρ ∈ Icc (0 : ℝ) (b + 1), ∀ x : ℝ × ℝ,
      wt x * ‖iteratedFDerivWithin ℝ n V U (ρ, x)‖ ≤ C) → ∀ x : ℝ × ℝ,
      ∀ ρ ∈ Icc (0 : ℝ) (b + 1), ‖iteratedFDerivWithin ℝ n V U (ρ, x)‖ ≤ C / wt x := by
    intro n C hC' x ρ hρ
    rw [le_div_iff₀ (hwt x), mul_comm]
    exact hC' ρ hρ x
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have hr0 : 0 ≤ r := ha.trans hr.1
    have h1 := ((slice_Dk hV' i).contDiffOn hV').comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ fun y : ℝ × ℝ => ((r, y) : E)).contDiffOn
        (s := univ)
      (fun y _ => (⟨hr0, trivial⟩ : ((r, y) : E) ∈ U))
    exact contDiffOn_univ.1 h1
  · intro w r hr
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC'⟩ := hC (i + w.length) (b + 1)
      refine ⟨C, fun x => ?_⟩
      have h1 := (spatial_Dk hV' i w).abs_le (hrU r hr x)
      have h2 : wt x * |Gw V i w (r, x)| ≤
          wt x * ‖iteratedFDerivWithin ℝ (i + w.length) V U (r, x)‖ :=
        mul_le_mul_of_nonneg_left h1 (hwt x).le
      exact h2.trans (hC' r (hsub r hr) x)
    · intro ε hε
      obtain ⟨C, hC'⟩ := hC (i + w.length + 1) (b + 1)
      have hδ : 0 < ε / (|C| + 1) := div_pos hε (by positivity)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds r hδ)] with r' hr' hball x
      have hm := mvt hV' (spatial_Dk hV' i w) x (hdiv _ C hC' x) (hsub r hr) (hsub r' hr')
      have hd : |r' - r| < ε / (|C| + 1) := by simpa [Real.dist_eq] using hball
      rw [lt_div_iff₀ (by positivity)] at hd
      change wt x * |Gw V i w (r', x) - Gw V i w (r, x)| ≤ ε
      calc wt x * |Gw V i w (r', x) - Gw V i w (r, x)|
          ≤ wt x * (C / wt x * |r' - r|) := mul_le_mul_of_nonneg_left hm (hwt x).le
        _ = C * |r' - r| := by field_simp [(hwt x).ne']
        _ ≤ |C| * |r' - r| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
        _ ≤ (|C| + 1) * |r' - r| := by nlinarith [abs_nonneg (r' - r)]
        _ ≤ ε := by nlinarith [abs_nonneg (r' - r)]
  · intro r hr ε hε
    obtain ⟨C, hC'⟩ := hC (i + 1 + 1) (b + 1)
    have hδ : 0 < ε / (|C| + 1) := div_pos hε (by positivity)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds r hδ)] with r' hr' hball x
    have hr'1 : r' ∈ Ico a b := hr'.1
    have hm := taylor hV' i x (hdiv _ C hC' x) (hsub r hr) (hsub r' hr'1) hr'.2
    have hd : |r' - r| < ε / (|C| + 1) := by simpa [Real.dist_eq] using hball
    rw [lt_div_iff₀ (by positivity)] at hd
    change wt x * |(r' - r)⁻¹ * (Fj V i (r', x) - Fj V i (r, x)) - Fj V (i + 1) (r, x)| ≤ ε
    calc wt x * |(r' - r)⁻¹ * (Fj V i (r', x) - Fj V i (r, x)) - Fj V (i + 1) (r, x)|
        ≤ wt x * (C / wt x * |r' - r|) := mul_le_mul_of_nonneg_left hm (hwt x).le
      _ = C * |r' - r| := by field_simp [(hwt x).ne']
      _ ≤ |C| * |r' - r| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
      _ ≤ (|C| + 1) * |r' - r| := by nlinarith [abs_nonneg (r' - r)]
      _ ≤ ε := by nlinarith [abs_nonneg (r' - r)]

end UnforcedLeray.Short.IIIa
