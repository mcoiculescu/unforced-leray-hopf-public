import UnforcedLeray.Short.PartI.Sub.T02_1_4
import UnforcedLeray.Short.PartI.Sub.T02_1_3

/-!
# Part I, task `PartI:T02/1/4/5`: joint smoothness of the representative (conditional
decomposition)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1: the mild solution is smooth for positive time, here in the
`BUC ∩ H^k` form: the Sobolev embedding `H^{k+3}(cell) ⊂ C^{k+1}_b` applied to the lifts
`u_k ∈ C^∞([0,T], H^{k+3})`).

Target: `JointSmoothOfHk` (`Short/PartI/Sub/T02_1_4.lean`).

## The cut

* `CylSobolevRep` and `AePeriodicEq` (`Short/PartI/Sub/T02_1_3.lean`, tasks `PartI:T02/1/3/1`
  and `PartI:T02/1/3/5`): the Sobolev embedding as a linear choice `g_k` of representatives with
  derivative bounds, and uniqueness of continuous periodic representatives;
* `EvalHasFDerivAt` (the only new leaf): the evaluation map `(x, z) ↦ g x z` of such a linear map
  `g : E →ₗ (Plane → F)` (each `g x` is `C¹`, with `‖g x z‖` and `‖D(g x) z‖` bounded by
  `C ‖x‖`) is Fréchet differentiable on `E × Plane`, with derivative `(h, v) ↦ g h z + D(g x) z v`;
* `evalFamilySmooth_of` (proved here): from `EvalHasFDerivAt`, if `g x` is `C^{n+1}` with the
  derivative bounds `‖D^j (g x) z‖ ≤ C ‖x‖`, `j ≤ n+1`, and `V : ℝ → E` is `C^∞` on `[0,T]`, then
  `(s, z) ↦ g (V s) z` is `C^n` on `[0,T] × ℝ²` (induction on `n`, the derivative being
  `(a, v) ↦ a g(V' s) z + D(g (V s)) z v`, a sum of two functions of the same form for `g` and for
  `x ↦ D(g x)` with one derivative less);
* `jointSmoothOfHk_of` (proved here): the glue.  For each `k` the level-`k` representative
  `g_k (uk k s)` of the lift equals `w s` (`AePeriodicEq`: both are continuous, periodic, and equal
  to the class of `u s` a.e.), so `w` is `C^k` jointly for all `k`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-! ### The leaf statement -/

/-- **Leaf (evaluation is Fréchet differentiable; source lines 261-288, Sobolev embedding on the
cell).**  Let `g : E →ₗ[ℝ] (Plane → F)` be a linear map from a normed space such that every `g x`
is `C¹` and `‖g x z‖ ≤ C ‖x‖`, `‖D(g x) z‖ ≤ C ‖x‖` for all `z` (i.e. `‖iteratedFDeriv ℝ j (g x) z‖
≤ C ‖x‖` for `j ≤ 1`).  Then the evaluation map `q ↦ g q.1 q.2` on `E × Plane` has a Fréchet
derivative at every `(x, z)`, the continuous linear map `(h, v) ↦ g h z + D(g x) z v`.

Proof idea: `L (h, v) := g h z + fderiv ℝ (g x) z v` is a continuous linear map on `E × Plane`
(`LinearMap.mkContinuous`, using `‖g h z‖ ≤ C ‖h‖`; `fderiv ℝ (g x) z` is continuous linear).  The
remainder is
`g (x + h) (z + v) - g x z - L (h, v)
   = (g h (z + v) - g h z) + (g x (z + v) - g x z - D(g x) z v)`:
the second bracket is `o(‖v‖)` because `g x` is differentiable at `z`, the first has norm at most
`C ‖h‖ ‖v‖` by the mean value inequality on the convex set `Plane`
(`Convex.norm_image_sub_le_of_norm_fderiv_le` with the bound `‖D(g h) y‖ ≤ C ‖h‖`), hence is
`o(‖(h, v)‖)`.  Use `HasFDerivAt` via `isLittleO` (`hasFDerivAt_iff_isLittleO_nhds_zero`). -/
def EvalHasFDerivAt : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : E →ₗ[ℝ] (Plane → F)) (C : ℝ),
    (∀ x, ContDiff ℝ 1 (g x)) →
    (∀ x (j : ℕ), j ≤ 1 → ∀ z, ‖iteratedFDeriv ℝ j (g x) z‖ ≤ C * ‖x‖) →
    ∀ (x : E) (z : Plane), ∃ L : E × Plane →L[ℝ] F,
      HasFDerivAt (fun q : E × Plane => g q.1 q.2) L (x, z) ∧
      ∀ (h : E) (v : Plane), L (h, v) = g h z + fderiv ℝ (g x) z v

/-- **Smoothness of a smooth family of evaluations** (the statement proved by
`evalFamilySmooth_of`). -/
def EvalFamilySmooth : Prop :=
  ∀ (n : ℕ) (T : ℝ), 0 < T →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Type) [NormedAddCommGroup F]
      [NormedSpace ℝ F] (g : E →ₗ[ℝ] (Plane → F)) (C : ℝ),
      (∀ x, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (g x)) →
      (∀ x (j : ℕ), j ≤ n + 1 → ∀ z, ‖iteratedFDeriv ℝ j (g x) z‖ ≤ C * ‖x‖) →
      ∀ V : ℝ → E, ContDiffOn ℝ ∞ V (Icc 0 T) →
        ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × Plane => g (V p.1) p.2)
          (Icc 0 T ×ˢ (univ : Set Plane))

/-! ### `EvalFamilySmooth` from `EvalHasFDerivAt` -/

/-- The derivative family `x ↦ D(g x)` of a linear family of `C¹` functions is again linear. -/
def derivFamily {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : E →ₗ[ℝ] (Plane → F)) (hd : ∀ x, ContDiff ℝ 1 (g x)) :
    E →ₗ[ℝ] (Plane → (Plane →L[ℝ] F)) where
  toFun x := fderiv ℝ (g x)
  map_add' x y := by
    funext z
    have h1 : DifferentiableAt ℝ (g x) z := ((hd x).differentiable (by simp)) z
    have h2 : DifferentiableAt ℝ (g y) z := ((hd y).differentiable (by simp)) z
    rw [map_add]
    exact fderiv_add h1 h2
  map_smul' a x := by
    funext z
    have h1 : DifferentiableAt ℝ (g x) z := ((hd x).differentiable (by simp)) z
    rw [map_smul]
    exact fderiv_const_smul h1 a

theorem derivFamily_apply {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E →ₗ[ℝ] (Plane → F))
    (hd : ∀ x, ContDiff ℝ 1 (g x)) (x : E) (z : Plane) :
    derivFamily g hd x z = fderiv ℝ (g x) z := rfl

theorem evalFamilySmooth_aux (h2 : EvalHasFDerivAt) (n : ℕ) :
    ∀ (T : ℝ), 0 < T →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Type) [NormedAddCommGroup F]
      [NormedSpace ℝ F] (g : E →ₗ[ℝ] (Plane → F)) (C : ℝ),
      (∀ x, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (g x)) →
      (∀ x (j : ℕ), j ≤ n + 1 → ∀ z, ‖iteratedFDeriv ℝ j (g x) z‖ ≤ C * ‖x‖) →
      ∀ V : ℝ → E, ContDiffOn ℝ ∞ V (Icc 0 T) →
        ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × Plane => g (V p.1) p.2)
          (Icc 0 T ×ˢ (univ : Set Plane)) := by
  induction n with
  | zero =>
    intro T hT E _ _ F _ _ g C hd hb V hV
    have hd1 : ∀ x, ContDiff ℝ 1 (g x) := fun x => by exact_mod_cast hd x
    have hb1 : ∀ x (j : ℕ), j ≤ 1 → ∀ z, ‖iteratedFDeriv ℝ j (g x) z‖ ≤ C * ‖x‖ :=
      fun x j hj z => hb x j (by omega) z
    have hev : Continuous (fun q : E × Plane => g q.1 q.2) := by
      rw [continuous_iff_continuousAt]
      intro q
      obtain ⟨L, hL, -⟩ := h2 E F g C hd1 hb1 q.1 q.2
      exact hL.continuousAt
    have hVc : ContinuousOn V (Icc 0 T) := hV.continuousOn
    have hφ : ContinuousOn (fun p : ℝ × Plane => (V p.1, p.2)) (Icc 0 T ×ˢ (univ : Set Plane)) := by
      refine ContinuousOn.prodMk ?_ continuousOn_snd
      exact hVc.comp continuousOn_fst (fun p hp => hp.1)
    have := hev.comp_continuousOn hφ
    rw [Nat.cast_zero, contDiffOn_zero]
    exact this
  | succ n ih =>
    intro T hT E _ _ F _ _ g C hd hb V hV
    have hUD : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set Plane)) :=
      (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
    have hd1 : ∀ x, ContDiff ℝ 1 (g x) := fun x =>
      (hd x).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1 + 1))
    have hb1 : ∀ x (j : ℕ), j ≤ 1 → ∀ z, ‖iteratedFDeriv ℝ j (g x) z‖ ≤ C * ‖x‖ :=
      fun x j hj z => hb x j (by omega) z
    have hVdiff : DifferentiableOn ℝ V (Icc 0 T) := hV.differentiableOn (by simp)
    have hV'sm : ContDiffOn ℝ ∞ (derivWithin V (Icc 0 T)) (Icc 0 T) :=
      hV.derivWithin (uniqueDiffOn_Icc hT) (le_of_eq rfl)
    -- the derivative family `x ↦ D (g x)`
    have hd₁ : ∀ x, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (derivFamily g hd1 x) := fun x => by
      show ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (g x))
      exact (hd x).fderiv_right (by push_cast; exact le_rfl)
    have hb₁ : ∀ x (j : ℕ), j ≤ n + 1 → ∀ z,
        ‖iteratedFDeriv ℝ j (derivFamily g hd1 x) z‖ ≤ C * ‖x‖ := by
      intro x j hj z
      show ‖iteratedFDeriv ℝ j (fderiv ℝ (g x)) z‖ ≤ C * ‖x‖
      rw [norm_iteratedFDeriv_fderiv]
      exact hb x (j + 1) (by omega) z
    have hA : ContDiffOn ℝ (n : WithTop ℕ∞)
        (fun p : ℝ × Plane => g (derivWithin V (Icc 0 T) p.1) p.2) (Icc 0 T ×ˢ (univ : Set Plane)) :=
      ih T hT E F g C (fun x => (hd x).of_le (by exact_mod_cast Nat.le_succ (n + 1)))
        (fun x j hj z => hb x j (by omega) z) _ hV'sm
    have hB : ContDiffOn ℝ (n : WithTop ℕ∞)
        (fun p : ℝ × Plane => derivFamily g hd1 (V p.1) p.2) (Icc 0 T ×ˢ (univ : Set Plane)) :=
      ih T hT E (Plane →L[ℝ] F) (derivFamily g hd1) C hd₁ hb₁ V hV
    -- the candidate derivative
    let Lp : ℝ × Plane → (ℝ × Plane →L[ℝ] F) := fun p =>
      (ContinuousLinearMap.smulRightL ℝ (ℝ × Plane) F (ContinuousLinearMap.fst ℝ ℝ Plane))
          (g (derivWithin V (Icc 0 T) p.1) p.2) +
        ((ContinuousLinearMap.compL ℝ (ℝ × Plane) Plane F).flip
          (ContinuousLinearMap.snd ℝ ℝ Plane)) (derivFamily g hd1 (V p.1) p.2)
    have hL : ContDiffOn ℝ (n : WithTop ℕ∞) Lp (Icc 0 T ×ˢ (univ : Set Plane)) :=
      ((ContinuousLinearMap.smulRightL ℝ (ℝ × Plane) F
        (ContinuousLinearMap.fst ℝ ℝ Plane)).contDiff.comp_contDiffOn hA).add
      (((ContinuousLinearMap.compL ℝ (ℝ × Plane) Plane F).flip
        (ContinuousLinearMap.snd ℝ ℝ Plane)).contDiff.comp_contDiffOn hB)
    have hderiv : ∀ p ∈ Icc 0 T ×ˢ (univ : Set Plane),
        HasFDerivWithinAt (fun q : ℝ × Plane => g (V q.1) q.2) (Lp p)
          (Icc 0 T ×ˢ (univ : Set Plane)) p := by
      intro p hp
      obtain ⟨Lev, hLev, hLevapp⟩ := h2 E F g C hd1 hb1 (V p.1) p.2
      have hVs : HasDerivWithinAt V (derivWithin V (Icc 0 T) p.1) (Icc 0 T) p.1 :=
        (hVdiff p.1 hp.1).hasDerivWithinAt
      have hfst : HasFDerivWithinAt (fun q : ℝ × Plane => q.1)
          (ContinuousLinearMap.fst ℝ ℝ Plane) (Icc 0 T ×ˢ (univ : Set Plane)) p :=
        (ContinuousLinearMap.fst ℝ ℝ Plane).hasFDerivAt.hasFDerivWithinAt
      have hVf := (hVs.hasFDerivWithinAt).comp p hfst (fun q hq => hq.1)
      have hφ := hVf.prodMk
        (ContinuousLinearMap.snd ℝ ℝ Plane).hasFDerivAt.hasFDerivWithinAt
      have hcomp := hLev.comp_hasFDerivWithinAt p hφ
      have hEq : Lev.comp ((((ContinuousLinearMap.toSpanSingleton ℝ
          (derivWithin V (Icc 0 T) p.1)).comp (ContinuousLinearMap.fst ℝ ℝ Plane)).prod
            (ContinuousLinearMap.snd ℝ ℝ Plane))) = Lp p := by
        refine ContinuousLinearMap.ext fun q => ?_
        obtain ⟨a, v⟩ := q
        simp [Lp, hLevapp, derivFamily_apply]
      exact hcomp.congr_fderiv hEq
    have hfd : ∀ p ∈ Icc 0 T ×ˢ (univ : Set Plane),
        fderivWithin ℝ (fun q : ℝ × Plane => g (V q.1) q.2) (Icc 0 T ×ˢ (univ : Set Plane)) p =
          Lp p := fun p hp => (hderiv p hp).fderivWithin (hUD p hp)
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderivWithin hUD]
    refine ⟨fun p hp => (hderiv p hp).differentiableWithinAt, by intro h; simp at h, ?_⟩
    exact hL.congr (fun p hp => hfd p hp)

/-- **`EvalFamilySmooth` from `EvalHasFDerivAt`** (induction on `n`).  The derivative of
`F(s, z) = g (V s) z` within `[0,T] × ℝ²` is the sum of the two functions of the same form
`g (V' s) z` and `(D ∘ g) (V s) z`, each with one derivative less. -/
theorem evalFamilySmooth_of (h2 : EvalHasFDerivAt) : EvalFamilySmooth :=
  fun n => evalFamilySmooth_aux h2 n

/-! ### The conditional theorem -/

/-- **`JointSmoothOfHk` from the Sobolev embedding, uniqueness of continuous periodic
representatives, and joint smoothness of an evaluation family.**  For each `k` the representative
`g_k (uk k s)` of the lift equals `w s` (`AePeriodicEq`), and `(s, z) ↦ g_k (uk k s) z` is `C^k` by
`EvalFamilySmooth` (with `V = extendCompactPath hT.le (uk k)`, which is `C^∞` on `[0,T]`). -/
theorem jointSmoothOfHk_of (h1 : CylSobolevRep) (h2 : AePeriodicEq) (h3 : EvalFamilySmooth) :
    JointSmoothOfHk := by
  intro ν c T hν hc hc1 hT u hu w hw hP
  rw [contDiffOn_infty]
  intro n
  obtain ⟨uk, huk, hsm⟩ := hP n
  obtain ⟨g, C, hgsm, hgrep, hgb⟩ := h1 c hc hc1 n
  have hcont : ∀ x, Continuous (g x) := fun x => (hgsm x).1.continuous
  have hwg : ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T), w s = g (uk ⟨s, hs⟩) := by
    intro s hs
    refine h2 c hc _ _ (hw.smooth s hs).continuous (hcont _) (hw.periodic s hs) (hgsm _).2 ?_
    have e1 := hgrep (uk ⟨s, hs⟩) Sob.Idx.zero
    have e0 := hw.represents ⟨s, hs⟩ Sob.Idx.zero
    simp only [Sob.Idx.castLE_zero, Sob.TestDomain.word_zero, Sob.iterD_nil] at e1 e0
    have hval : (vecH3CellDerivCLM Sob.Idx.zero (u ⟨s, hs⟩) : Plane → Vec) =
        cellDeriv c (Sob.Idx.zero : Sob.Idx 2 (n + 3)) (uk ⟨s, hs⟩) := by
      rw [← huk ⟨s, hs⟩]
      rfl
    rw [← hval] at e1
    exact e0.symm.trans e1
  have hmain := h3 n T hT (Cyl.H ℝ Cyl.Vec2 c 0 (n + 3)) Vec g C (fun x => (hgsm x).1) hgb
    (extendCompactPath hT.le uk) hsm
  refine hmain.congr (fun p hp => ?_)
  rw [extendCompactPath_apply_of_mem hT.le uk hp.1]
  exact congrFun (hwg p.1 hp.1) p.2

end UnforcedLeray.Short.PartI
