import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.CoeffWeakDeriv

/-!
# `PartIII-a:T21/2/7/2/1/1/6/9`: Leibniz cell jets (`leibCellJet`)

Source of record: `the November 2 reference manuscript` (SP), line 3060 (the
adjoint equation and its weighted energies of every order).  The statement is `LeibCellJet`
(`Sub/AdjInterior/TimeJets/Defs.lean`): a smooth `c`-periodic coefficient `A` with every spatial
derivative bounded, times a cell jet of every order `f` with fields `D`, is a cell jet of every
order with the Leibniz fields `leib A D`.

Proof outline.  `leib A D w = Σ_{(α, β) ∈ wordSplits w} ∂^α A · D β`.
* base: `wordSplits [] = [([], [])]`;
* periodicity: each `∂^α A` is periodic (`ll_rs_smooth_per`), each `D β` periodic by length;
* `X_{-m,c}`-membership: each term is a bounded coefficient times an `X_{-m,c}` field
  (`ll_memLp_coeff_mul`), and finite sums keep membership (`ll_memLp_sum`);
* derivative: `wordSplits (j :: w)` is the flat map of the two splittings of each `p ∈ wordSplits w`,
  so `leib A D (j :: w)` is the sum over `p` of `∂_j(∂^α A) · D β + ∂^α A · D (j :: β)`
  (`ll_leib_cons`); each summand is the `CoeffWeakDeriv` derivative of `∂^α A · D β`
  (`coeffWeakDeriv`), and the sum over `p` is closed under weak derivatives (`ll_hwcd_sum`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Weak cell derivatives: linear closure -/

/-- Zero is a weak cell derivative of zero. -/
theorem ll_hwcd_zero {c : ℝ} {j : Fin 2} :
    HasWeakCellDerivC c j (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun ψ _ => ⟨?_, ?_⟩, fun ψ _ => ?_⟩ <;> simp

/-- Weak cell derivatives are closed under sums. -/
theorem ll_hwcd_add {c : ℝ} {j : Fin 2} {φ φ' g g' : ℝ × ℝ → ℂ}
    (h1 : HasWeakCellDerivC c j φ g) (h2 : HasWeakCellDerivC c j φ' g') :
    HasWeakCellDerivC c j (fun x => φ x + φ' x) (fun x => g x + g' x) := by
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · exact ((a1 ψ hψ).1.add (a2 ψ hψ).1).congr_fun (fun x _ => by simp [add_mul])
      (UnforcedLeray.B0579.measurableSet_cell c)
  · exact ((a1 ψ hψ).2.add (a2 ψ hψ).2).congr_fun (fun x _ => by simp [add_mul])
      (UnforcedLeray.B0579.measurableSet_cell c)
  · beta_reduce
    have i1 := (a1 ψ hψ).1
    have i2 := (a2 ψ hψ).1
    have j1 := (a1 ψ hψ).2
    have j2 := (a2 ψ hψ).2
    have e1 : ∫ x in B0579.cell c, (φ x + φ' x) * (B0579.pd j ψ x : ℂ) =
        (∫ x in B0579.cell c, φ x * (B0579.pd j ψ x : ℂ)) +
          ∫ x in B0579.cell c, φ' x * (B0579.pd j ψ x : ℂ) := by
      rw [← integral_add i1 i2]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [add_mul])
    have e2 : ∫ x in B0579.cell c, (g x + g' x) * (ψ x : ℂ) =
        (∫ x in B0579.cell c, g x * (ψ x : ℂ)) + ∫ x in B0579.cell c, g' x * (ψ x : ℂ) := by
      rw [← integral_add j1 j2]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [add_mul])
    rw [e1, e2, b1 ψ hψ, b2 ψ hψ]
    ring

/-- Finite sums of weak cell derivatives (over a list of indices). -/
theorem ll_hwcd_sum {c : ℝ} {j : Fin 2} {ι : Type} (L : List ι) (F G : ι → ℝ × ℝ → ℂ)
    (h : ∀ p ∈ L, HasWeakCellDerivC c j (F p) (G p)) :
    HasWeakCellDerivC c j (fun x => (L.map fun p => F p x).sum)
      (fun x => (L.map fun p => G p x).sum) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ll_hwcd_zero
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ll_hwcd_add (h p (by simp)) (ih fun q hq => h q (by simp [hq]))

/-! ## Membership in `X_{-m,c}` -/

/-- A bounded continuous real coefficient times an `L²` field is `L²`. -/
theorem ll_memLp_coeff_mul {μ : Measure (ℝ × ℝ)} {g : ℝ × ℝ → ℂ} {a : ℝ × ℝ → ℝ}
    (hg : MemLp g 2 μ) (ha : Continuous a) {C : ℝ} (hC : ∀ x, |a x| ≤ C) :
    MemLp (fun x => ((a x : ℝ) : ℂ) * g x) 2 μ := by
  refine MemLp.of_le (hg.const_mul ((max C 0 : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp ha).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have h1 : |a x| ≤ max C 0 := (hC x).trans (le_max_left _ _)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (le_max_right C 0)]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- A finite sum of `L²` fields is `L²`. -/
theorem ll_memLp_sum {μ : Measure (ℝ × ℝ)} {ι : Type} (L : List ι) (F : ι → ℝ × ℝ → ℂ)
    (h : ∀ p ∈ L, MemLp (F p) 2 μ) :
    MemLp (fun x => (L.map fun p => F p x).sum) 2 μ := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact MemLp.zero
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h p (by simp)).add (ih fun q hq => h q (by simp [hq]))

/-! ## Splittings of words -/

/-- Flat-map sums: the two splittings of each pair. -/
theorem ll_sum_flatMap (j : Fin 2) (h : List (Fin 2) × List (Fin 2) → ℂ) :
    ∀ L : List (List (Fin 2) × List (Fin 2)),
      ((L.flatMap fun p => [(j :: p.1, p.2), (p.1, j :: p.2)]).map h).sum =
        (L.map fun p => h (j :: p.1, p.2) + h (p.1, j :: p.2)).sum
  | [] => rfl
  | q :: L => by
    simp [List.flatMap_cons, ll_sum_flatMap j h L, add_assoc]

/-- The two parts of every splitting of a word have total length `|w|`. -/
theorem ll_wordSplits_length : ∀ (w : List (Fin 2)) (p : List (Fin 2) × List (Fin 2)),
    p ∈ wordSplits w → p.1.length + p.2.length = w.length
  | [], p, hp => by
    simp only [wordSplits, List.mem_singleton] at hp
    subst hp
    rfl
  | j :: w, p, hp => by
    rw [show wordSplits (j :: w) = (wordSplits w).flatMap
      (fun q => [(j :: q.1, q.2), (q.1, j :: q.2)]) from rfl] at hp
    obtain ⟨q, hq, hp⟩ := List.mem_flatMap.1 hp
    have ih := ll_wordSplits_length w q hq
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [List.length_cons] <;> omega

/-- The leading letter of a word splits off either factor. -/
theorem ll_leib_cons (A : ℝ × ℝ → ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (j : Fin 2)
    (w : List (Fin 2)) (x : ℝ × ℝ) :
    leib A D (j :: w) x =
      ((wordSplits w).map fun p =>
        ((B0579.pd j (rSpatial p.1 A) x : ℝ) : ℂ) * D p.2 x +
          ((rSpatial p.1 A x : ℝ) : ℂ) * D (j :: p.2) x).sum := by
  unfold leib
  rw [show wordSplits (j :: w) = (wordSplits w).flatMap
    (fun q => [(j :: q.1, q.2), (q.1, j :: q.2)]) from rfl]
  exact ll_sum_flatMap j (fun q => ((rSpatial q.1 A x : ℝ) : ℂ) * D q.2 x) (wordSplits w)

/-! ## Spatial derivatives of a smooth periodic coefficient -/

/-- Every spatial derivative of a smooth periodic coefficient is smooth and periodic. -/
theorem ll_rs_smooth_per {c : ℝ} {A : ℝ × ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hAp : ∀ x : ℝ × ℝ, A (x.1 + c, x.2) = A x) :
    ∀ w : List (Fin 2), ContDiff ℝ ∞ (rSpatial w A) ∧
      ∀ x : ℝ × ℝ, rSpatial w A (x.1 + c, x.2) = rSpatial w A x
  | [] => ⟨hA, hAp⟩
  | j :: w => by
    obtain ⟨h1, h2⟩ := ll_rs_smooth_per hA hAp w
    exact cw_pd_smooth_periodic h1 h2 j

/-! ## The main statement -/

/-- **(9) Leibniz fields**: a smooth `c`-periodic coefficient with every derivative bounded, times
a cell jet of every order, is a cell jet of every order with the fields `leib A D`. -/
theorem leibCellJet : LeibCellJet := by
  intro c m A f D hc hA hAp hb hk k
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- base
    funext x
    simp [leib, wordSplits, rSpatial, (hk k).base]
  · -- periodicity
    intro w hw x
    unfold leib
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    have hl := ll_wordSplits_length w p hp
    rw [(ll_rs_smooth_per hA hAp p.1).2 x, (hk k).periodic p.2 (by omega) x]
  · -- membership in X_{-m,c}
    intro w hw
    refine ll_memLp_sum (wordSplits w) (fun p x => ((rSpatial p.1 A x : ℝ) : ℂ) * D p.2 x)
      (fun p hp => ?_)
    have hl := ll_wordSplits_length w p hp
    obtain ⟨C, hC⟩ := hb p.1
    exact ll_memLp_coeff_mul ((hk k).memX p.2 (by omega))
      (ll_rs_smooth_per hA hAp p.1).1.continuous hC
  · -- derivatives
    intro j w hw
    have hterm : ∀ p ∈ wordSplits w,
        HasWeakCellDerivC c j (fun x => ((rSpatial p.1 A x : ℝ) : ℂ) * D p.2 x)
          (fun x => ((B0579.pd j (rSpatial p.1 A) x : ℝ) : ℂ) * D p.2 x +
            ((rSpatial p.1 A x : ℝ) : ℂ) * D (j :: p.2) x) := by
      intro p hp
      have hl := ll_wordSplits_length w p hp
      obtain ⟨C, hC⟩ := hb p.1
      obtain ⟨C', hC'⟩ := hb (j :: p.1)
      exact coeffWeakDeriv c m j (rSpatial p.1 A) (D p.2) (D (j :: p.2)) hc
        (ll_rs_smooth_per hA hAp p.1).1 (ll_rs_smooth_per hA hAp p.1).2 ⟨C, hC⟩ ⟨C', hC'⟩
        ((hk k).memX p.2 (by omega))
        ((hk k).memX (j :: p.2) (by simp only [List.length_cons]; omega))
        ((hk k).deriv j p.2 (by omega))
    have hsum := ll_hwcd_sum (wordSplits w)
      (fun p x => ((rSpatial p.1 A x : ℝ) : ℂ) * D p.2 x)
      (fun p x => ((B0579.pd j (rSpatial p.1 A) x : ℝ) : ℂ) * D p.2 x +
        ((rSpatial p.1 A x : ℝ) : ℂ) * D (j :: p.2) x) hterm
    have hL : leib A D (j :: w) = fun x => ((wordSplits w).map fun p =>
        ((B0579.pd j (rSpatial p.1 A) x : ℝ) : ℂ) * D p.2 x +
          ((rSpatial p.1 A x : ℝ) : ℂ) * D (j :: p.2) x).sum := by
      funext x
      exact ll_leib_cons A D j w x
    rw [hL]
    exact hsum

end UnforcedLeray.Short.IIIa
