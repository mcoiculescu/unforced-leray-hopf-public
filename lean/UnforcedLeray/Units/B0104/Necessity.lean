import UnforcedLeray.Units.B0104.Evolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# B0104, helper: the interaction convergence must be uniform in the auxiliary parameters

Helper for blueprint unit `B0104` (`lem:compact-duhamel`, `paper/main.tex` lines 1586-1621).

Line 1594 writes the interaction hypothesis as `sup_t ‖A_n(t) - A_0(t)‖ → 0`, while line 1601
asserts that "all these conclusions have the same parameter uniformity", i.e. hold uniformly in
the auxiliary parameters. `B0104.lean` reads the supremum as taken over the time *and* the
auxiliary parameters. This file shows that this reading is forced: with the convergence only for
each fixed parameter, and every other hypothesis of the lemma in force, both the strong
convergence of `U_n` and the norm convergence of the Duhamel remainders fail to be uniform in
the parameter.

The example lives on `ℂ²` with `B = 1`: free evolutions `F_n = F_0 = 1`, interactions
`A_n(p) = N` if `p = n` and `0` otherwise, `A_0 = 0`, where `N x = x₁ e₀` satisfies `N² = 0`; the
Duhamel evolutions are `U_n(p,t,s) = 1 + (t - s) A_n(p)` and `U_0 = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace UnforcedLeray.B0104

section SquareZero

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a time-independent square-zero interaction `a(p)` (`a(p)² = 0`) and the identity free
evolution, `U(t,s) = 1 + (t - s) a(p)` is the Duhamel evolution on blocks of any length `B`
(`paper/main.tex` line 1617; unit `B0104`). -/
theorem isDuhamelEvolution_squareZero (B : ℝ) (a : ι → H →L[ℂ] H)
    (ha : ∀ p x, a p (a p x) = 0) :
    IsDuhamelEvolution B (fun _ _ _ => ContinuousLinearMap.id ℂ H) (fun p _ => a p)
      (fun p t s => ContinuousLinearMap.id ℂ H + ((t - s : ℝ) : ℂ) • a p) := by
  have hint : ∀ p (s : ℝ) (x : H),
      (fun r : ℝ => ContinuousLinearMap.id ℂ H
        (a p ((ContinuousLinearMap.id ℂ H + ((r - s : ℝ) : ℂ) • a p) x))) = fun _ => a p x := by
    intro p s x
    funext r
    simp [ha]
  refine ⟨fun p s t _ _ x => ?_, fun p s t _ _ x => ?_, fun p s => ⟨1 + B * ‖a p‖, ?_⟩⟩
  · show IntervalIntegrable (fun r : ℝ => ContinuousLinearMap.id ℂ H
        (a p ((ContinuousLinearMap.id ℂ H + ((r - s : ℝ) : ℂ) • a p) x))) volume s t
    rw [hint]
    exact intervalIntegrable_const
  · show (ContinuousLinearMap.id ℂ H + ((t - s : ℝ) : ℂ) • a p) x =
      ContinuousLinearMap.id ℂ H x + ∫ r in s..t, ContinuousLinearMap.id ℂ H
        (a p ((ContinuousLinearMap.id ℂ H + ((r - s : ℝ) : ℂ) • a p) x))
    rw [hint, intervalIntegral.integral_const, _root_.add_apply,
      _root_.smul_apply, Complex.coe_smul]
  · intro t h1 h2
    calc ‖ContinuousLinearMap.id ℂ H + ((t - s : ℝ) : ℂ) • a p‖
        ≤ ‖ContinuousLinearMap.id ℂ H‖ + ‖((t - s : ℝ) : ℂ) • a p‖ := norm_add_le _ _
      _ = ‖ContinuousLinearMap.id ℂ H‖ + (t - s) * ‖a p‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      _ ≤ 1 + B * ‖a p‖ :=
          add_le_add ContinuousLinearMap.norm_id_le
            (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end SquareZero

/-- The square-zero operator `N x = ⟪e₁, x⟫ e₀` on `ℂ²`. -/
def nilp : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (innerSL ℂ (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))).smulRight
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

theorem nilp_apply (x : EuclideanSpace ℂ (Fin 2)) :
    nilp x = ⟪EuclideanSpace.single (1 : Fin 2) (1 : ℂ), x⟫_ℂ •
      EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := rfl

theorem inner_single_one_single_zero :
    ⟪EuclideanSpace.single (1 : Fin 2) (1 : ℂ), EuclideanSpace.single (0 : Fin 2) (1 : ℂ)⟫_ℂ =
      0 := by
  rw [EuclideanSpace.inner_single_left]
  simp

theorem nilp_nilp (x : EuclideanSpace ℂ (Fin 2)) : nilp (nilp x) = 0 := by
  rw [nilp_apply (nilp x), nilp_apply x, inner_smul_right, inner_single_one_single_zero]
  simp

theorem nilp_single_one :
    nilp (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := by
  rw [nilp_apply, EuclideanSpace.inner_single_left]
  simp

/-- The interactions of the example: `A_n(p) = N` if `p = n`, `0` otherwise. -/
def bumpInteraction (n p : ℕ) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  if p = n then nilp else 0

theorem bumpInteraction_sq (n p : ℕ) (x : EuclideanSpace ℂ (Fin 2)) :
    bumpInteraction n p (bumpInteraction n p x) = 0 := by
  unfold bumpInteraction
  split_ifs
  · exact nilp_nilp x
  · simp

/-- **The parameter-uniform reading of `sup_t ‖A_n(t) - A_0(t)‖ → 0` is necessary**
(`paper/main.tex` lines 1593-1601; unit `B0104`). There are families on `ℂ²`, with parameters
`p : ℕ` and block length `B = 1`, satisfying every hypothesis of `compact_duhamel` except that
`A_n → A_0` holds uniformly in time only for each fixed parameter, for which neither
`U_n → U_0` strongly uniformly in the parameter nor
`sup ‖(U_n - F_n) - (U_0 - F_0)‖ → 0` holds. -/
theorem exists_counterexample_pointwise_interaction :
    ∃ (F : ℕ → ℕ → ℝ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
      (F₀ : ℕ → ℝ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
      (A : ℕ → ℕ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
      (A₀ : ℕ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
      (U : ℕ → ℕ → ℝ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
      (U₀ : ℕ → ℝ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
      (∃ M, ∀ n p t s, s ≤ t → t ≤ s + 1 → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M) ∧
      (∀ x, ∀ ε > 0, ∀ᶠ n in atTop, ∀ p t s, s ≤ t → t ≤ s + 1 →
        ‖F n p t s x - F₀ p t s x‖ < ε) ∧
      (∀ x, ∀ ε > 0, ∀ᶠ n in atTop, ∀ p t s, s ≤ t → t ≤ s + 1 →
        ‖((F n p t s)†) x - ((F₀ p t s)†) x‖ < ε) ∧
      (∃ K, ∀ n p r, ‖A n p r‖ ≤ K) ∧
      (∀ p, ∀ ε > 0, ∀ᶠ n in atTop, ∀ r, ‖A n p r - A₀ p r‖ < ε) ∧
      (∀ p r, IsCompactOperator (A₀ p r)) ∧
      TotallyBounded (range fun q : ℕ × ℝ => A₀ q.1 q.2) ∧
      (∀ n, IsDuhamelEvolution 1 (F n) (A n) (U n)) ∧ IsDuhamelEvolution 1 F₀ A₀ U₀ ∧
      ¬ (∀ x, ∀ ε > 0, ∀ᶠ n in atTop, ∀ p t s, s ≤ t → t ≤ s + 1 →
        ‖U n p t s x - U₀ p t s x‖ < ε) ∧
      ¬ (∀ ε > 0, ∀ᶠ n in atTop, ∀ p t s, s ≤ t → t ≤ s + 1 →
        ‖(U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)‖ < ε) := by
  set e₀ := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℂ)
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have he₁ : ‖e₁‖ = 1 := by simp [e₁]
  refine ⟨fun _ _ _ _ => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)), fun _ _ _ => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)),
    fun n p _ => bumpInteraction n p, fun _ _ => 0,
    fun n p t s => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) + ((t - s : ℝ) : ℂ) • bumpInteraction n p,
    fun _ t s => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) + ((t - s : ℝ) : ℂ) • (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
    ⟨1, fun _ _ _ _ _ _ => ⟨ContinuousLinearMap.norm_id_le, ContinuousLinearMap.norm_id_le⟩⟩,
    fun x ε hε => Eventually.of_forall fun _ _ _ _ _ _ => by simpa using hε,
    fun x ε hε => Eventually.of_forall fun _ _ _ _ _ _ => by simpa using hε,
    ⟨‖nilp‖, fun n p _ => ?_⟩, fun p ε hε => ?_, fun _ _ => isCompactOperator_zero,
    isCompact_singleton.totallyBounded.subset (range_subset_iff.2 fun _ => mem_singleton _),
    fun n => isDuhamelEvolution_squareZero 1 (bumpInteraction n) (bumpInteraction_sq n),
    isDuhamelEvolution_squareZero 1 (fun _ => 0) (fun _ _ => by simp), ?_, ?_⟩
  · show ‖bumpInteraction n p‖ ≤ ‖nilp‖
    unfold bumpInteraction
    split_ifs <;> simp
  · filter_upwards [eventually_gt_atTop p] with n hn r
    have hpn : p ≠ n := hn.ne
    simpa [bumpInteraction, hpn] using hε
  · intro h
    obtain ⟨n, hn⟩ := (h e₁ (1 / 2) (by norm_num)).exists
    have h1 : ‖(ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) + (((1 : ℝ) - 0 : ℝ) : ℂ) • bumpInteraction n n) e₁ -
        (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) + (((1 : ℝ) - 0 : ℝ) : ℂ) •
          (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) e₁‖ < 1 / 2 :=
      hn n 1 0 (by norm_num) (by norm_num)
    have h2 : (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) + (((1 : ℝ) - 0 : ℝ) : ℂ) • bumpInteraction n n) e₁ -
        (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) + (((1 : ℝ) - 0 : ℝ) : ℂ) •
          (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) e₁ = e₀ := by
      simp [bumpInteraction, e₁, e₀, nilp_single_one]
    rw [h2, he₀] at h1
    norm_num at h1
  · intro h
    obtain ⟨n, hn⟩ := (h (1 / 2) (by norm_num)).exists
    let T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
      (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) + (((1 : ℝ) - 0 : ℝ) : ℂ) • bumpInteraction n n -
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2))) -
        (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) + (((1 : ℝ) - 0 : ℝ) : ℂ) •
          (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) -
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)))
    have h1 : ‖T‖ < 1 / 2 := hn n 1 0 (by norm_num) (by norm_num)
    have h2 : T e₁ = e₀ := by
      simp [T, bumpInteraction, e₁, e₀, nilp_single_one]
    have h3 := T.le_opNorm e₁
    rw [h2, he₀, he₁, mul_one] at h3
    linarith

end UnforcedLeray.B0104
