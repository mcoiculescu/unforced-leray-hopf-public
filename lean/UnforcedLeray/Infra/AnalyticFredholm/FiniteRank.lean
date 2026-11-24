import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Finite-rank and approximable operators; the determinant criterion

General infrastructure for the analytic Fredholm theorem
(`UnforcedLeray.Infra.AnalyticFredholm`).  Over an `RCLike` field `𝕜`:

* `IsFiniteRank T`: the range of the bounded operator `T` is finite-dimensional;
* `IsApproximable T`: `T` lies in the norm closure of the finite-rank operators;
* `sumRankOne ψ v = ∑ i, (ψ i).smulRight (v i)`, the operator `x ↦ ∑ i, ψ i x • v i`; every
  finite-rank operator has this form (`IsFiniteRank.exists_eq_sumRankOne`);
* finite-rank and approximable operators are compact, and both classes are stable under
  composition with bounded operators on either side;
* the **determinant criterion** `isUnit_one_sub_sumRankOne_iff`: on a Banach space,
  `1 - ∑ i, (ψ i).smulRight (v i)` is invertible iff `det (1 - M) ≠ 0`, where
  `M i j = ψ i (v j)` (`gramMatrix`).  The proof uses Mathlib's Fredholm alternative
  `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` and the finite-dimensional fact
  `Matrix.exists_mulVec_eq_zero_iff`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Infra.AnalyticFredholm

section Defs

variable {𝕜 W X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A bounded operator has *finite rank* if its range is finite-dimensional. -/
def IsFiniteRank (T : X →L[𝕜] Y) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.range (T : X →ₗ[𝕜] Y))

/-- A bounded operator is *approximable* if it is a norm limit of finite-rank operators, i.e. it
lies in the closure of the set of finite-rank operators. -/
def IsApproximable (T : X →L[𝕜] Y) : Prop :=
  T ∈ closure {S : X →L[𝕜] Y | IsFiniteRank S}

/-- The finite-rank operator `x ↦ ∑ i, ψ i x • v i`. -/
def sumRankOne {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y) : X →L[𝕜] Y :=
  ∑ i, (ψ i).smulRight (v i)

theorem sumRankOne_apply {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y) (x : X) :
    sumRankOne ψ v x = ∑ i, ψ i x • v i := by
  simp [sumRankOne]

/-- The range of `sumRankOne ψ v` lies in the span of the vectors `v i`. -/
theorem range_sumRankOne_le {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y) :
    LinearMap.range (sumRankOne ψ v : X →ₗ[𝕜] Y) ≤ Submodule.span 𝕜 (Set.range v) := by
  rintro _ ⟨x, rfl⟩
  change sumRankOne ψ v x ∈ _
  rw [sumRankOne_apply]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isFiniteRank_sumRankOne {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y) :
    IsFiniteRank (sumRankOne ψ v) := by
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range v)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  exact Submodule.finiteDimensional_of_le (range_sumRankOne_le ψ v)

/-- Every finite-rank operator is a finite sum of rank-one operators `(ψ i).smulRight (v i)`. -/
theorem IsFiniteRank.exists_eq_sumRankOne {T : X →L[𝕜] Y} (hT : IsFiniteRank T) :
    ∃ (n : ℕ) (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y), T = sumRankOne ψ v := by
  classical
  have : FiniteDimensional 𝕜 (LinearMap.range (T : X →ₗ[𝕜] Y)) := hT
  set V := LinearMap.range (T : X →ₗ[𝕜] Y)
  let b := Module.finBasis 𝕜 V
  let T' : X →L[𝕜] V := T.codRestrict V (fun x => LinearMap.mem_range_self (T : X →ₗ[𝕜] Y) x)
  refine ⟨Module.finrank 𝕜 V, fun i => (LinearMap.toContinuousLinearMap (b.coord i)).comp T',
    fun i => (b i : Y), ?_⟩
  ext x
  rw [sumRankOne_apply]
  have h2 : ((∑ i, b.repr (T' x) i • b i : V) : Y) = ∑ i, b.repr (T' x) i • (b i : Y) := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [b.sum_repr] at h2
  exact h2

theorem isFiniteRank_iff_exists_eq_sumRankOne {T : X →L[𝕜] Y} :
    IsFiniteRank T ↔ ∃ (n : ℕ) (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y), T = sumRankOne ψ v :=
  ⟨IsFiniteRank.exists_eq_sumRankOne, by
    rintro ⟨n, ψ, v, rfl⟩
    exact isFiniteRank_sumRankOne ψ v⟩

theorem isFiniteRank_zero : IsFiniteRank (0 : X →L[𝕜] Y) := by
  have : (0 : X →L[𝕜] Y) = sumRankOne (n := 0) Fin.elim0 Fin.elim0 := by
    ext x; simp [sumRankOne_apply]
  rw [this]
  exact isFiniteRank_sumRankOne _ _

theorem IsFiniteRank.isApproximable {T : X →L[𝕜] Y} (hT : IsFiniteRank T) : IsApproximable T :=
  subset_closure hT

/-- `T` is approximable iff for every `ε > 0` some finite-rank `S` has `‖T - S‖ < ε`. -/
theorem isApproximable_iff {T : X →L[𝕜] Y} :
    IsApproximable T ↔ ∀ ε > 0, ∃ S : X →L[𝕜] Y, IsFiniteRank S ∧ ‖T - S‖ < ε := by
  rw [IsApproximable, Metric.mem_closure_iff]
  simp only [dist_eq_norm]
  rfl

/-- A norm limit of finite-rank operators is approximable. -/
theorem isApproximable_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {S : ι → X →L[𝕜] Y}
    {T : X →L[𝕜] Y} (hS : Tendsto S l (𝓝 T)) (hfin : ∀ᶠ i in l, IsFiniteRank (S i)) :
    IsApproximable T :=
  mem_closure_of_tendsto hS hfin

/-- Rank-one operators are compact. -/
theorem isCompactOperator_smulRight (ψ : X →L[𝕜] 𝕜) (v : Y) :
    IsCompactOperator (ψ.smulRight v) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have h1 : IsCompactOperator ((ContinuousLinearMap.id 𝕜 𝕜).smulRight v) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have h2 := h1.comp_clm ψ
  have he : (ψ.smulRight v : X → Y) = ((ContinuousLinearMap.id 𝕜 𝕜).smulRight v) ∘ ψ := by
    funext x; simp
  rw [he]
  exact h2

theorem isCompactOperator_sumRankOne {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y) :
    IsCompactOperator (sumRankOne ψ v) := by
  unfold sumRankOne
  refine Finset.sum_induction _ (fun T : X →L[𝕜] Y => IsCompactOperator T) ?_ ?_ ?_
  · intro a b ha hb
    rw [FunLike.coe_add]
    exact ha.add hb
  · rw [FunLike.coe_zero]
    exact isCompactOperator_zero
  · intro i _
    exact isCompactOperator_smulRight _ _

/-- Finite-rank operators are compact. -/
theorem IsFiniteRank.isCompactOperator {T : X →L[𝕜] Y} (hT : IsFiniteRank T) :
    IsCompactOperator T := by
  obtain ⟨n, ψ, v, rfl⟩ := hT.exists_eq_sumRankOne
  exact isCompactOperator_sumRankOne ψ v

/-- Approximable operators into a Banach space are compact. -/
theorem IsApproximable.isCompactOperator [CompleteSpace Y] {T : X →L[𝕜] Y}
    (hT : IsApproximable T) : IsCompactOperator T := by
  have hsub : {S : X →L[𝕜] Y | IsFiniteRank S} ⊆ {S : X →L[𝕜] Y | IsCompactOperator S} :=
    fun S hS => IsFiniteRank.isCompactOperator hS
  exact (isClosed_setOfPred_isCompactOperator.closure_subset_iff.mpr hsub) hT

theorem comp_sumRankOne {n : ℕ} (B : Y →L[𝕜] Z) (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y) :
    B.comp (sumRankOne ψ v) = sumRankOne ψ (fun i => B (v i)) := by
  ext x
  simp [sumRankOne_apply]

theorem sumRankOne_comp {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → Y) (B : W →L[𝕜] X) :
    (sumRankOne ψ v).comp B = sumRankOne (fun i => (ψ i).comp B) v := by
  ext x
  simp [sumRankOne_apply]

theorem IsFiniteRank.comp_left {T : X →L[𝕜] Y} (hT : IsFiniteRank T) (B : Y →L[𝕜] Z) :
    IsFiniteRank (B.comp T) := by
  obtain ⟨n, ψ, v, rfl⟩ := hT.exists_eq_sumRankOne
  rw [comp_sumRankOne]
  exact isFiniteRank_sumRankOne _ _

theorem IsFiniteRank.comp_right {T : X →L[𝕜] Y} (hT : IsFiniteRank T) (B : W →L[𝕜] X) :
    IsFiniteRank (T.comp B) := by
  obtain ⟨n, ψ, v, rfl⟩ := hT.exists_eq_sumRankOne
  rw [sumRankOne_comp]
  exact isFiniteRank_sumRankOne _ _

/-- Approximable operators are stable under composition with a bounded operator on the left. -/
theorem IsApproximable.comp_left {T : X →L[𝕜] Y} (hT : IsApproximable T) (B : Y →L[𝕜] Z) :
    IsApproximable (B.comp T) := by
  have hc : Continuous fun S : X →L[𝕜] Y => B.comp S :=
    (ContinuousLinearMap.compL 𝕜 X Y Z B).continuous
  exact map_mem_closure (f := fun S : X →L[𝕜] Y => B.comp S) hc hT
    fun S hS => IsFiniteRank.comp_left hS B

/-- Approximable operators are stable under composition with a bounded operator on the right. -/
theorem IsApproximable.comp_right {T : X →L[𝕜] Y} (hT : IsApproximable T) (B : W →L[𝕜] X) :
    IsApproximable (T.comp B) := by
  have hc : Continuous fun S : X →L[𝕜] Y => S.comp B :=
    ((ContinuousLinearMap.compL 𝕜 W X Y).flip B).continuous
  exact map_mem_closure (f := fun S : X →L[𝕜] Y => S.comp B) hc hT
    fun S hS => IsFiniteRank.comp_right hS B

end Defs

section Determinant

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The matrix `M i j = ψ i (v j)` of the finite-rank operator `sumRankOne ψ v`. -/
def gramMatrix {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → X) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => ψ i (v j)

/-- `sumRankOne ψ v` has a nonzero fixed vector iff `det (1 - M) = 0`, `M = gramMatrix ψ v`. -/
theorem exists_fixed_sumRankOne_iff {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜) (v : Fin n → X) :
    (∃ y : X, y ≠ 0 ∧ sumRankOne ψ v y = y) ↔ (1 - gramMatrix ψ v).det = 0 := by
  classical
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨y, hy0, hy⟩
    refine ⟨fun i => ψ i y, ?_, ?_⟩
    · intro hc
      apply hy0
      rw [← hy, sumRankOne_apply]
      have hc' : ∀ i, ψ i y = 0 := fun i => congrFun hc i
      simp [hc']
    · funext j
      have hj : ψ j (sumRankOne ψ v y) = ψ j y := by rw [hy]
      rw [sumRankOne_apply, map_sum] at hj
      simp only [map_smul, smul_eq_mul] at hj
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
      simp only [Matrix.mulVec, dotProduct, gramMatrix, Matrix.of_apply]
      rw [← hj]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · rintro ⟨c, hc0, hc⟩
    have hfix : ∀ i, ψ i (∑ j, c j • v j) = c i := by
      intro i
      have hi := congrFun hc i
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hi
      simp only [Matrix.mulVec, dotProduct, gramMatrix, Matrix.of_apply] at hi
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [hi]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    refine ⟨∑ j, c j • v j, ?_, ?_⟩
    · intro h0
      apply hc0
      funext i
      rw [← hfix i, h0, map_zero, Pi.zero_apply]
    · rw [sumRankOne_apply]
      simp only [hfix]

/-- **Determinant criterion.** On a Banach space, `1 - ∑ i, (ψ i).smulRight (v i)` is
invertible iff `det (1 - M) ≠ 0`, where `M i j = ψ i (v j)`. -/
theorem isUnit_one_sub_sumRankOne_iff [CompleteSpace X] {n : ℕ} (ψ : Fin n → X →L[𝕜] 𝕜)
    (v : Fin n → X) :
    IsUnit (1 - sumRankOne ψ v) ↔ (1 - gramMatrix ψ v).det ≠ 0 := by
  rw [Ne, ← exists_fixed_sumRankOne_iff, not_exists]
  constructor
  · rintro hu y ⟨hy0, hy⟩
    obtain ⟨b, hb⟩ := hu.exists_left_inv
    apply hy0
    have h1 : (1 - sumRankOne ψ v) y = 0 := by
      simp [hy]
    have h2 : (b * (1 - sumRankOne ψ v)) y = y := by rw [hb]; rfl
    have h3 : (b * (1 - sumRankOne ψ v)) y = b ((1 - sumRankOne ψ v) y) := rfl
    rw [h3, h1, map_zero] at h2
    exact h2.symm
  · intro h
    rcases (isCompactOperator_sumRankOne ψ v).hasEigenvalue_or_mem_resolventSet
      (μ := (1 : 𝕜)) one_ne_zero with he | hr
    · obtain ⟨y, hy⟩ := he.exists_hasEigenvector
      exact absurd ⟨hy.2, by simpa using hy.apply_eq_smul⟩ (h y)
    · rw [spectrum.mem_resolventSet_iff, map_one] at hr
      exact hr

end Determinant

end UnforcedLeray.Infra.AnalyticFredholm
