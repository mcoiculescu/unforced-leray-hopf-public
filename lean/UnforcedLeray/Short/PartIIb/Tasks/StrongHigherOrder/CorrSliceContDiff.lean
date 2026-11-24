import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.ContRepFDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice

/-!
# `PartII-b:S2/2`: Classical slice regularity of `contRep u τ` for iterated maximal-graph states

Source of record: `the November 2 reference manuscript`
(SP), lines 2557-2559 and 1515-1531.

Proves `theorem corrSliceIteratedContDiff_proof : UnforcedLeray.Short.IIb.CorrSliceIteratedContDiff`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- Coordinate basis tuple associated with a multi-index `α : Fin k → Fin 3`, ordered from
outermost derivative (`Fin.last`) to innermost derivative (`0`) to match `iteratedFDeriv`. -/
def coordTuple : ∀ {k : ℕ}, (Fin k → Fin 3) → (Fin k → Space)
  | 0, _ => Fin.elim0
  | k + 1, β =>
      Fin.cons (UnforcedLeray.coordinateVector (β (Fin.last k))) (coordTuple (Fin.init β))

@[simp]
theorem coordTuple_snoc {k : ℕ} (α : Fin k → Fin 3) (j : Fin 3) :
    coordTuple (Fin.snoc α j) =
      Fin.cons (UnforcedLeray.coordinateVector j) (coordTuple α) := by
  simp [coordTuple]

/-- Operator norm bound for a continuous multilinear map on `(Fin k → Space)` by the sum of its
values on coordinate basis tuples `coordTuple α`. -/
theorem norm_continuousMultilinear_le_sum_coordTuple {k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) F) :
    ‖M‖ ≤ ∑ α : Fin k → Fin 3, ‖M (coordTuple α)‖ := by
  induction k generalizing F with
  | zero =>
      have h0 : ‖M‖ = ‖M Fin.elim0‖ := by simp
      have huniv : (Finset.univ : Finset (Fin 0 → Fin 3)) = {Fin.elim0} := by
        ext α
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subsingleton.elim α Fin.elim0
      rw [h0, huniv, Finset.sum_singleton]
      rfl
  | succ k ih =>
      let L : Space →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) F :=
        continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) F M
      have hML : ‖M‖ = ‖L‖ :=
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) F).norm_map M).symm
      have hL : ‖L‖ ≤ ∑ j : Fin 3, ‖L (UnforcedLeray.coordinateVector j)‖ :=
        UnforcedLeray.Short.PartIIIb.Concrete.bgCorr_norm_clm_le_sum L
      have hstep : ∑ j : Fin 3, ‖L (UnforcedLeray.coordinateVector j)‖ ≤
          ∑ j : Fin 3, ∑ α : Fin k → Fin 3,
            ‖M (coordTuple (Fin.snoc α j))‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (ih (L (UnforcedLeray.coordinateVector j))).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [coordTuple_snoc]
        rfl
      have hsum_eq : (∑ j : Fin 3, ∑ α : Fin k → Fin 3, ‖M (coordTuple (Fin.snoc α j))‖) =
          ∑ β : Fin (k + 1) → Fin 3, ‖M (coordTuple β)‖ := by
        rw [← Fintype.sum_prod_type']
        exact Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin 3))
          (fun β => ‖M (coordTuple β)‖)
      exact (hML.trans_le (hL.trans hstep)).trans_eq hsum_eq

/-- Any two families `g₁, g₂` satisfying `IsIteratedPhaseGrad P q k u` have identical phase pairings
against every phase test `Φ`. -/
theorem isIteratedPhaseGrad_phasePair_eq {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {u : Yq P q} :
    ∀ {k : ℕ} {g₁ g₂ : (Fin k → Fin 3) → Yq P q},
      IsIteratedPhaseGrad P q k u g₁ →
      IsIteratedPhaseGrad P q k u g₂ →
      ∀ (α : Fin k → Fin 3) (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ →
        phasePair P q Φ (g₁ α) = phasePair P q Φ (g₂ α)
  | 0, g₁, g₂, hg₁, hg₂, α, Φ, _ => by
      have hα : α = Fin.elim0 := Subsingleton.elim α Fin.elim0
      rw [hα, hg₁, hg₂]
  | k + 1, g₁, g₂, ⟨g₁₀, hg₁₀, hop₁⟩, ⟨g₂₀, hg₂₀, hop₂⟩, β, Φ, hΦ => by
      have hβ : β = Fin.snoc (Fin.init β) (β (Fin.last k)) := (Fin.snoc_init_self β).symm
      rw [hβ, ← hop₁ (Fin.init β) (β (Fin.last k)) Φ hΦ,
        ← hop₂ (Fin.init β) (β (Fin.last k)) Φ hΦ]
      exact isIteratedPhaseGrad_phasePair_eq hg₁₀ hg₂₀ (Fin.init β)
        (-dy (β (Fin.last k)) Φ) (hΦ.dy (β (Fin.last k))).neg

/-- If `g₀` satisfies `IsIteratedPhaseGrad P q k u` and `g` satisfies
`IsIteratedPhaseGrad P q (k + 1) u`, then `g (Fin.snoc α j)` is the `j`-th distributional spatial
derivative of `g₀ α`. -/
theorem isIteratedPhaseGrad_hasPhaseOp_snoc {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {u : Yq P q} {k : ℕ} {g₀ : (Fin k → Fin 3) → Yq P q}
    {g : (Fin (k + 1) → Fin 3) → Yq P q}
    (hg₀ : IsIteratedPhaseGrad P q k u g₀) (hg : IsIteratedPhaseGrad P q (k + 1) u g)
    (α : Fin k → Fin 3) (j : Fin 3) :
    HasPhaseOp (fun Φ => -dy j Φ) (g₀ α) (g (Fin.snoc α j)) := by
  obtain ⟨g₀', hg₀', hop⟩ := hg
  intro Φ hΦ
  rw [← isIteratedPhaseGrad_phasePair_eq hg₀' hg₀ α (-dy j Φ) (hΦ.dy j).neg]
  exact hop α j Φ hΦ

theorem contDiff_clmOfGrad {k : ℕ} {gj : Fin 3 → Space → Space}
    (hgj : ∀ j : Fin 3, ContDiff ℝ k (gj j)) :
    ContDiff ℝ k (clmOfGrad gj) := by
  unfold clmOfGrad
  refine ContDiff.sum fun j _ => ?_
  exact ((ContinuousLinearMap.smulRightL ℝ Space Space
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ)).contDiff).comp (hgj j)

/-- **`PartII-b:S2/2` (`corrSliceIteratedContDiff_proof`)**
(`the November 2 reference manuscript`,
lines 2557-2559 and 1515-1531). -/
theorem corrSliceIteratedContDiff_proof : UnforcedLeray.Short.IIb.CorrSliceIteratedContDiff := by
  intro P _ hP1 ν hν u hall
  choose G hG using hall
  have hstep_op : ∀ (m : ℕ) (α : Fin m → Fin 3) (j : Fin 3),
      HasPhaseOp (fun Φ => -dy j Φ) (G m α : Yq P q0E) (G (m + 1) (Fin.snoc α j) : Yq P q0E) :=
    fun m α j => isIteratedPhaseGrad_hasPhaseOp_snoc (hG m) (hG (m + 1)) α j
  have hslice_cont : ∀ (m : ℕ) (α : Fin m → Fin 3) (τ : ℝ),
      Continuous (contRep (G m α : Yq P q0E) τ) :=
    fun m α τ => contRep_slice_continuous hP1 hν (G m α) τ
  have hslice_weak : ∀ (m : ℕ) (α : Fin m → Fin 3) (j : Fin 3) (τ : ℝ),
      UnforcedLeray.HasWeakSpatialDerivative j
        (contRep (G m α : Yq P q0E) τ)
        (contRep (G (m + 1) (Fin.snoc α j) : Yq P q0E) τ) :=
    fun m α j τ =>
      UnforcedLeray.Short.PartIIIb.Concrete.bgContRepWeakSlice P hP1 ν hν
        (G m α) (G (m + 1) (Fin.snoc α j)) j (hstep_op m α j) τ
  have hG_smooth : ∀ (n : ℕ) (m : ℕ) (α : Fin m → Fin 3) (τ : ℝ),
      ContDiff ℝ n (contRep (G m α : Yq P q0E) τ) := by
    intro n
    induction n with
    | zero =>
        intro m α τ
        exact contDiff_zero.2 (hslice_cont m α τ)
    | succ n ih =>
        intro m α τ
        rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
        have hf : Continuous (contRep (G m α : Yq P q0E) τ) := hslice_cont m α τ
        have hgj : ∀ j : Fin 3, Continuous (contRep (G (m + 1) (Fin.snoc α j) : Yq P q0E) τ) :=
          fun j => hslice_cont (m + 1) (Fin.snoc α j) τ
        have hw : ∀ j : Fin 3, UnforcedLeray.HasWeakSpatialDerivative j
            (contRep (G m α : Yq P q0E) τ)
            (contRep (G (m + 1) (Fin.snoc α j) : Yq P q0E) τ) :=
          fun j => hslice_weak m α j τ
        refine ⟨fun x => (hasFDerivAt_of_continuous_weakGrad hf hgj hw x).differentiableAt,
          by simp, ?_⟩
        have heq : fderiv ℝ (contRep (G m α : Yq P q0E) τ) =
            clmOfGrad (fun j => contRep (G (m + 1) (Fin.snoc α j) : Yq P q0E) τ) :=
          funext fun y => fderiv_eq_clmOfGrad_of_continuous_weakGrad hf hgj hw y
        rw [heq]
        exact contDiff_clmOfGrad fun j => ih (m + 1) (Fin.snoc α j) τ
  have hu_eq : (G 0 Fin.elim0 : Yq P q0E) = u := hG 0
  have hu_smooth : ∀ (n : ℕ) (τ : ℝ), ContDiff ℝ n (contRep u τ) := by
    intro n τ
    rw [← hu_eq]
    exact hG_smooth n 0 Fin.elim0 τ
  have hiter_eval : ∀ (k : ℕ) (g : (Fin k → Fin 3) → B0411.D P ν q0E),
      IsIteratedPhaseGrad P q0E k u (fun α => (g α : Yq P q0E)) →
      ∀ (τ : ℝ) (α : Fin k → Fin 3) (y : Space),
        iteratedFDeriv ℝ k (contRep u τ) y (coordTuple α) =
          contRep (g α : Yq P q0E) τ y := by
    intro k
    induction k with
    | zero =>
        intro g hg τ α y
        have hα : α = Fin.elim0 := Subsingleton.elim α Fin.elim0
        have hg0 : (g Fin.elim0 : Yq P q0E) = u := hg
        rw [hα, iteratedFDeriv_zero_apply, hg0]
    | succ k ih =>
        intro g hg τ β y
        have hβ : β = Fin.snoc (Fin.init β) (β (Fin.last k)) := (Fin.snoc_init_self β).symm
        set α : Fin k → Fin 3 := Fin.init β
        set j : Fin 3 := β (Fin.last k)
        rw [hβ, coordTuple_snoc]
        have hdiff_iter : DifferentiableAt ℝ (iteratedFDeriv ℝ k (contRep u τ)) y :=
          ((hu_smooth (k + 1) τ).differentiable_iteratedFDeriv
            (by exact_mod_cast Nat.lt_succ_self k)) y
        have hleft := hdiff_iter.iteratedFDeriv_succ_apply_left'
          (m := Fin.cons (UnforcedLeray.coordinateVector j) (coordTuple α))
        simp only [Fin.cons_zero, Fin.tail_cons] at hleft
        rw [hleft]
        have hfun_eq : (fun y' : Space => iteratedFDeriv ℝ k (contRep u τ) y' (coordTuple α)) =
            contRep (G k α : Yq P q0E) τ :=
          funext fun y' => ih (G k) (hG k) τ α y'
        rw [hfun_eq]
        have hop_g : ∀ l : Fin 3,
            HasPhaseOp (fun Φ => -dy l Φ) (G k α : Yq P q0E) (g (Fin.snoc α l) : Yq P q0E) :=
          fun l => isIteratedPhaseGrad_hasPhaseOp_snoc (hG k) hg α l
        have hf : Continuous (contRep (G k α : Yq P q0E) τ) := hslice_cont k α τ
        have hgj : ∀ l : Fin 3, Continuous (contRep (g (Fin.snoc α l) : Yq P q0E) τ) :=
          fun l => contRep_slice_continuous hP1 hν (g (Fin.snoc α l)) τ
        have hw : ∀ l : Fin 3, UnforcedLeray.HasWeakSpatialDerivative l
            (contRep (G k α : Yq P q0E) τ)
            (contRep (g (Fin.snoc α l) : Yq P q0E) τ) :=
          fun l =>
            UnforcedLeray.Short.PartIIIb.Concrete.bgContRepWeakSlice P hP1 ν hν
              (G k α) (g (Fin.snoc α l)) l (hop_g l) τ
        exact fderiv_apply_coordinateVector_of_continuous_weakGrad hf hgj hw y j
  intro k g hg τ
  refine ⟨hu_smooth k τ, fun y => ?_⟩
  refine (norm_continuousMultilinear_le_sum_coordTuple
    (iteratedFDeriv ℝ k (contRep u τ) y)).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hiter_eval k g hg τ α y]

end UnforcedLeray.Short.IIb

end
