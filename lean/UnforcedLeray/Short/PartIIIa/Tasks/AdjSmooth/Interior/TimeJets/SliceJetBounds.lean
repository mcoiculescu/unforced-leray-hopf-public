import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs

/-!
# `SliceJetBounds`: age jets of a jointly smooth function (pure calculus)

Source: `the November 2 reference manuscript` lines 270-288, 2866-2870.

A function is *derivative-type of order `n`* (`Dk V n g`) if on `U = (0, ∞) × ℝ²` it equals
`D^n V` applied to fixed vectors of norm `≤ 1`.  The age jet `∂_r^i V`, its spatial derivatives
`∂^w ∂_r^i V`, and the derivative of a derivative-type function along a unit vector are
derivative-type; hence bounded by `‖D^n V‖`, and the mean value inequality in `r` applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa
namespace SliceJB

abbrev E : Type := ℝ × (ℝ × ℝ)

/-- The open half-space `(0, ∞) × ℝ²`. -/
def U : Set E := Ioi 0 ×ˢ univ

lemma isOpen_U : IsOpen U := isOpen_Ioi.prod isOpen_univ

/-- The unit age direction. -/
def e0 : E := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))

lemma norm_e0 : ‖e0‖ ≤ 1 := by simp [e0, Prod.norm_def]

/-- `g` is, on `U`, the `n`-th derivative of `V` applied to fixed vectors of norm `≤ 1`. -/
def Dk (V : E → ℝ) (n : ℕ) (g : E → ℝ) : Prop :=
  ∃ m : Fin n → E, (∀ k, ‖m k‖ ≤ 1) ∧ ∀ p ∈ U, g p = iteratedFDeriv ℝ n V p m

lemma Dk.congr {V : E → ℝ} {n : ℕ} {g g' : E → ℝ} (h : Dk V n g) (heq : ∀ p ∈ U, g' p = g p) :
    Dk V n g' := by
  obtain ⟨m, hm, h⟩ := h
  exact ⟨m, hm, fun p hp => by rw [heq p hp, h p hp]⟩

lemma cdAt {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {p : E} (hp : p ∈ U) : ContDiffAt ℝ ∞ V p :=
  hV.contDiffAt (isOpen_U.mem_nhds hp)

lemma cdAt_iter {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (n : ℕ) {p : E} (hp : p ∈ U) :
    ContDiffAt ℝ ∞ (iteratedFDeriv ℝ n V) p :=
  (cdAt hV hp).iteratedFDeriv_right (by norm_cast)

lemma Dk.contDiffAt {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {n : ℕ} {g : E → ℝ} (h : Dk V n g)
    {p : E} (hp : p ∈ U) : ContDiffAt ℝ ∞ g p := by
  obtain ⟨m, -, hm⟩ := h
  have h2 : ContDiffAt ℝ ∞ (fun y => iteratedFDeriv ℝ n V y m) p :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ m).contDiff.contDiffAt.comp p
      (cdAt_iter hV n hp)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_U.mem_nhds hp] with y hy using hm y hy

lemma Dk.abs_le {V : E → ℝ} {n : ℕ} {g : E → ℝ} (h : Dk V n g) {p : E} (hp : p ∈ U) :
    |g p| ≤ ‖iteratedFDeriv ℝ n V p‖ := by
  obtain ⟨m, hm, h⟩ := h
  rw [h p hp, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ m).trans ?_
  have : ∏ i, ‖m i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hm i)
  nlinarith [norm_nonneg (iteratedFDeriv ℝ n V p)]

lemma Dk.fderiv {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {n : ℕ} {g : E → ℝ} (h : Dk V n g)
    {v : E} (hv : ‖v‖ ≤ 1) : Dk V (n + 1) (fun p => fderiv ℝ g p v) := by
  obtain ⟨m, hm, hg⟩ := h
  refine ⟨Fin.cons v m, ?_, ?_⟩
  · intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hv
    · simpa using hm i
  · intro p hp
    have hev : g =ᶠ[𝓝 p] fun y => iteratedFDeriv ℝ n V y m := by
      filter_upwards [isOpen_U.mem_nhds hp] with y hy using hg y hy
    show _root_.fderiv ℝ g p v = _
    rw [hev.fderiv_eq, iteratedFDeriv_succ_apply_left]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n V) p :=
      (cdAt_iter hV n hp).differentiableAt (by simp)
    have := (hd.hasFDerivAt.continuousMultilinear_apply_const m).fderiv
    rw [this]
    simp

/-- The age derivative of a derivative-type function along a slice. -/
lemma deriv_slice {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {n : ℕ} {g : E → ℝ} (h : Dk V n g)
    {s : ℝ} {x : ℝ × ℝ} (hp : (s, x) ∈ U) :
    HasDerivAt (fun s => g (s, x)) (fderiv ℝ g (s, x) e0) s := by
  have hd : DifferentiableAt ℝ g (s, x) := (h.contDiffAt hV hp).differentiableAt (by simp)
  have hγ : HasDerivAt (fun s : ℝ => (s, x)) e0 s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hd.hasFDerivAt.comp_hasDerivAt s hγ

/-- The age jet `∂_r^i V(p.1, p.2)`. -/
def Fj (V : E → ℝ) (i : ℕ) (p : E) : ℝ := iteratedDeriv i (fun s => V (s, p.2)) p.1

lemma slice_Dk {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) : Dk V i (Fj V i) := by
  induction i with
  | zero =>
    refine ⟨Fin.elim0, fun k => k.elim0, fun p hp => ?_⟩
    simp [Fj, iteratedFDeriv_zero_apply]
  | succ i ih =>
    refine (ih.fderiv hV norm_e0).congr ?_
    intro p hp
    have := (deriv_slice hV ih (s := p.1) (x := p.2) hp).deriv
    simp only [Fj, iteratedDeriv_succ]
    exact this

lemma fj_succ {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) {p : E} (hp : p ∈ U) :
    Fj V (i + 1) p = fderiv ℝ (Fj V i) p e0 := by
  have := (deriv_slice hV (slice_Dk hV i) (s := p.1) (x := p.2) hp).deriv
  simp only [Fj, iteratedDeriv_succ]
  exact this

lemma hasDeriv_Fj {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) {s : ℝ} {x : ℝ × ℝ}
    (hp : (s, x) ∈ U) : HasDerivAt (fun s => Fj V i (s, x)) (Fj V (i + 1) (s, x)) s := by
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
    have h1 := ih.fderiv hV (norm_dir j)
    refine h1.congr ?_
    intro p hp
    have hd : DifferentiableAt ℝ (Gw V i w) p := (ih.contDiffAt hV hp).differentiableAt (by simp)
    have hγ : HasFDerivAt (fun y : ℝ × ℝ => (p.1, y))
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
      (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
    have := (hd.hasFDerivAt.comp p.2 hγ).fderiv
    simp only [Gw, rSpatial, B0579.pd]
    have h2 : fderiv ℝ (fun y => rSpatial w (fun y' => Fj V i (p.1, y')) y) p.2 (B0579.dir j) =
        fderiv ℝ (Gw V i w) p (0, B0579.dir j) := by
      have e := (hd.hasFDerivAt.comp p.2 hγ).fderiv
      change fderiv ℝ (Gw V i w ∘ fun y => (p.1, y)) p.2 (B0579.dir j) = _
      rw [e]
      simp
    exact h2

/-- Mean value inequality in the age. -/
lemma mvt {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) {n : ℕ} {g : E → ℝ} (h : Dk V n g) {S K : ℝ}
    (x : ℝ × ℝ) (hK : ∀ ρ ∈ Ioo (0 : ℝ) S, ‖iteratedFDeriv ℝ (n + 1) V (ρ, x)‖ ≤ K)
    {r r' : ℝ} (hr : r ∈ Ioo (0 : ℝ) S) (hr' : r' ∈ Ioo (0 : ℝ) S) :
    |g (r', x) - g (r, x)| ≤ K * |r' - r| := by
  have hU : ∀ s ∈ Ioo (0 : ℝ) S, (s, x) ∈ U := fun s hs => ⟨hs.1, trivial⟩
  have := (convex_Ioo (0 : ℝ) S).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => g (s, x)) (f' := fun s => fderiv ℝ g (s, x) e0) (C := K)
    (fun s hs => (deriv_slice hV h (hU s hs)).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact ((h.fderiv hV norm_e0).abs_le (hU s hs)).trans (hK s hs)) hr hr'
  simpa [Real.norm_eq_abs] using this

/-- First-order Taylor bound in the age. -/
lemma taylor {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (i : ℕ) {S K : ℝ} (x : ℝ × ℝ)
    (hK : ∀ ρ ∈ Ioo (0 : ℝ) S, ‖iteratedFDeriv ℝ (i + 1 + 1) V (ρ, x)‖ ≤ K)
    {r r' : ℝ} (hr : r ∈ Ioo (0 : ℝ) S) (hr' : r' ∈ Ioo (0 : ℝ) S) (hne : r' ≠ r) :
    |(r' - r)⁻¹ * (Fj V i (r', x) - Fj V i (r, x)) - Fj V (i + 1) (r, x)| ≤ K * |r' - r| := by
  have hU : ∀ s ∈ Ioo (0 : ℝ) S, (s, x) ∈ U := fun s hs => ⟨hs.1, trivial⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK r hr)
  have hsub : uIcc r r' ⊆ Ioo (0 : ℝ) S := (ordConnected_Ioo).uIcc_subset hr hr'
  set A' := Fj V (i + 1) (r, x) with hA'
  have key := (convex_uIcc r r').norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => Fj V i (s, x) - Fj V i (r, x) - (s - r) * A')
    (f' := fun s => Fj V (i + 1) (s, x) - A') (C := K * |r' - r|)
    (fun s hs => by
      have h1 := (hasDeriv_Fj hV i (hU s (hsub hs)))
      have h2 : HasDerivAt (fun s : ℝ => (s - r) * A') A' s := by
        simpa using ((hasDerivAt_id s).sub_const r).mul_const A'
      have := (h1.sub_const (Fj V i (r, x))).sub h2
      exact this.hasDerivWithinAt)
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

end SliceJB

open SliceJB in
theorem sliceJetBounds : SliceJetBounds := by
  intro V wt hwt hV hC a b ha i
  have hrU : ∀ r ∈ Ioo a b, ∀ x : ℝ × ℝ, (r, x) ∈ U := fun r hr x => ⟨ha.trans_lt hr.1, trivial⟩
  have hsub : ∀ r ∈ Ioo a b, r ∈ Ioo (0 : ℝ) (b + 1) :=
    fun r hr => ⟨ha.trans_lt hr.1, by linarith [hr.2]⟩
  -- the pointwise bound `wt * ‖D^n V‖ ≤ C` as an `x`-dependent bound
  have hdiv : ∀ (n : ℕ) (C : ℝ), (∀ ρ ∈ Ioo (0 : ℝ) (b + 1), ∀ x : ℝ × ℝ,
      wt x * ‖iteratedFDeriv ℝ n V (ρ, x)‖ ≤ C) → ∀ x : ℝ × ℝ,
      ∀ ρ ∈ Ioo (0 : ℝ) (b + 1), ‖iteratedFDeriv ℝ n V (ρ, x)‖ ≤ C / wt x := by
    intro n C hC' x ρ hρ
    rw [le_div_iff₀ (hwt x), mul_comm]
    exact hC' ρ hρ x
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    exact ((slice_Dk hV i).contDiffAt hV (hrU r hr x)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  · intro w r hr
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC'⟩ := hC (i + w.length) (b + 1)
      refine ⟨C, fun x => ?_⟩
      have h1 := (spatial_Dk hV i w).abs_le (hrU r hr x)
      have h2 : wt x * |Gw V i w (r, x)| ≤ wt x * ‖iteratedFDeriv ℝ (i + w.length) V (r, x)‖ :=
        mul_le_mul_of_nonneg_left h1 (hwt x).le
      exact h2.trans (hC' r (hsub r hr) x)
    · intro ε hε
      obtain ⟨C, hC'⟩ := hC (i + w.length + 1) (b + 1)
      have hδ : 0 < ε / (|C| + 1) := div_pos hε (by positivity)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds r hδ)] with r' hr' hball x
      have hm := mvt hV (spatial_Dk hV i w) x (hdiv _ C hC' x) (hsub r hr) (hsub r' hr')
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
    have hr'1 : r' ∈ Ioo a b := hr'.1
    have hm := taylor hV i x (hdiv _ C hC' x) (hsub r hr) (hsub r' hr'1) hr'.2
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
