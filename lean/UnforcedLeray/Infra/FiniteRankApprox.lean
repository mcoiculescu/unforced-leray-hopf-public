import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite-rank approximation of compact operators

This file proves that a compact operator into an inner product space is an operator-norm limit
of continuous linear maps with finite-dimensional range, and sets up the closed subspace of
such limits.

## Main definitions

* `finiteRank 𝕜 E F`: the submodule of `E →L[𝕜] F` of continuous linear maps whose
  `LinearMap.range` is finite-dimensional.
* `approximable 𝕜 E F`: its operator-norm closure, i.e. the operators which are norm limits of
  finite-rank operators.

## Main results

* `exists_finiteRank_norm_sub_le`: if `F` is an inner product space over `RCLike 𝕜` and
  `K : E →L[𝕜] F` is compact, then for every `ε > 0` there is a continuous linear `K'` with
  finite-dimensional range and `‖K - K'‖ ≤ ε`. The approximant is `P ∘ K` with `P` the
  orthogonal projection onto the span of a finite `ε`-net of `K` (closed unit ball)
  (`exists_starProjection_comp_norm_sub_le`).
* `exists_tendsto_finiteRank`: the same, as a sequence converging in operator norm.
* `isClosed_approximable`, `comp_mem_approximable`, `mem_approximable_comp`: the set of limits of
  finite-rank operators is closed, and stable under composition with bounded operators on either
  side.
* `isCompactOperator_of_mem_finiteRank`, `isCompactOperator_of_mem_approximable`: finite-rank
  operators, and (for a complete target) their norm limits, are compact.
* `mem_approximable_iff_isCompactOperator`, `approximable_eq_compactOperator`: for a Hilbert space
  target, the approximable operators are exactly the compact operators.

The domain `E` is an arbitrary (semi)normed space throughout; only the target needs an inner
product, and completeness of the target is used only to show that limits of compact operators
are compact.
-/

set_option autoImplicit false

noncomputable section

open Metric Set Filter Topology

namespace UnforcedLeray.Infra.FiniteRankApprox

/-! ### Finite-rank operators and their norm closure over a general field -/

section General

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E F G : Type*)
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The continuous linear maps `E →L[𝕜] F` whose range `LinearMap.range T` is
finite-dimensional (the *finite-rank* operators), as a submodule of `E →L[𝕜] F`. -/
def finiteRank : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {T | FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F))}
  zero_mem' := by
    show FiniteDimensional 𝕜 (LinearMap.range ((0 : E →L[𝕜] F) : E →ₗ[𝕜] F))
    have h : LinearMap.range ((0 : E →L[𝕜] F) : E →ₗ[𝕜] F) ≤ ⊥ := by
      rintro _ ⟨x, rfl⟩
      simp
    exact Submodule.finiteDimensional_of_le h
  add_mem' := by
    intro S T hS hT
    simp only [Set.mem_ofPred_eq] at hS hT ⊢
    have h : LinearMap.range ((S + T : E →L[𝕜] F) : E →ₗ[𝕜] F) ≤
        LinearMap.range (S : E →ₗ[𝕜] F) ⊔ LinearMap.range (T : E →ₗ[𝕜] F) := by
      rintro _ ⟨x, rfl⟩
      exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
    exact Submodule.finiteDimensional_of_le h
  smul_mem' := by
    intro c T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    have h : LinearMap.range ((c • T : E →L[𝕜] F) : E →ₗ[𝕜] F) ≤
        LinearMap.range (T : E →ₗ[𝕜] F) := by
      rintro _ ⟨x, rfl⟩
      exact Submodule.smul_mem _ c ⟨x, rfl⟩
    exact Submodule.finiteDimensional_of_le h

variable {𝕜 E F G}

theorem mem_finiteRank {T : E →L[𝕜] F} :
    T ∈ finiteRank 𝕜 E F ↔ FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F)) :=
  Iff.rfl

/-- A finite-rank operator composed on the right with a bounded operator has finite rank. -/
theorem comp_mem_finiteRank {T : F →L[𝕜] G} (hT : T ∈ finiteRank 𝕜 F G) (A : E →L[𝕜] F) :
    T.comp A ∈ finiteRank 𝕜 E G := by
  rw [mem_finiteRank] at hT ⊢
  have h : LinearMap.range ((T.comp A : E →L[𝕜] G) : E →ₗ[𝕜] G) ≤
      LinearMap.range (T : F →ₗ[𝕜] G) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨A x, rfl⟩
  exact Submodule.finiteDimensional_of_le h

/-- A bounded operator composed on the left with a finite-rank operator has finite rank. -/
theorem mem_finiteRank_comp (B : F →L[𝕜] G) {T : E →L[𝕜] F} (hT : T ∈ finiteRank 𝕜 E F) :
    B.comp T ∈ finiteRank 𝕜 E G := by
  rw [mem_finiteRank] at hT ⊢
  have h : LinearMap.range ((B.comp T : E →L[𝕜] G) : E →ₗ[𝕜] G) ≤
      (LinearMap.range (T : E →ₗ[𝕜] F)).map (B : F →ₗ[𝕜] G) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T x, ⟨x, rfl⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le h

variable (𝕜 E F)

/-- The operators `E →L[𝕜] F` which are operator-norm limits of finite-rank operators: the
topological closure of `finiteRank 𝕜 E F`. -/
def approximable : Submodule 𝕜 (E →L[𝕜] F) :=
  (finiteRank 𝕜 E F).topologicalClosure

/-- The set of operator-norm limits of finite-rank operators is closed. -/
theorem isClosed_approximable : IsClosed (approximable 𝕜 E F : Set (E →L[𝕜] F)) :=
  Submodule.isClosed_topologicalClosure _

theorem finiteRank_le_approximable : finiteRank 𝕜 E F ≤ approximable 𝕜 E F :=
  Submodule.le_topologicalClosure _

variable {𝕜 E F}

theorem coe_approximable :
    (approximable 𝕜 E F : Set (E →L[𝕜] F)) = closure (finiteRank 𝕜 E F : Set (E →L[𝕜] F)) :=
  Submodule.topologicalClosure_coe _

/-- `T` is a norm limit of finite-rank operators iff it is approximated by finite-rank operators to
within every `ε > 0`. -/
theorem mem_approximable_iff {T : E →L[𝕜] F} :
    T ∈ approximable 𝕜 E F ↔
      ∀ ε > 0, ∃ T' : E →L[𝕜] F,
        FiniteDimensional 𝕜 (LinearMap.range (T' : E →ₗ[𝕜] F)) ∧ ‖T - T'‖ < ε := by
  rw [← SetLike.mem_coe, coe_approximable, Metric.mem_closure_iff]
  refine forall₂_congr fun ε _ => ?_
  refine exists_congr fun T' => ?_
  rw [dist_eq_norm]
  rfl

/-- Variant of `mem_approximable_iff` with a non-strict inequality. -/
theorem mem_approximable_iff_le {T : E →L[𝕜] F} :
    T ∈ approximable 𝕜 E F ↔
      ∀ ε > 0, ∃ T' : E →L[𝕜] F,
        FiniteDimensional 𝕜 (LinearMap.range (T' : E →ₗ[𝕜] F)) ∧ ‖T - T'‖ ≤ ε := by
  rw [mem_approximable_iff]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · obtain ⟨T', hT', h'⟩ := h ε hε
    exact ⟨T', hT', h'.le⟩
  · obtain ⟨T', hT', h'⟩ := h (ε / 2) (half_pos hε)
    exact ⟨T', hT', h'.trans_lt (half_lt_self hε)⟩

/-- An operator-norm limit of finite-rank operators, composed on the right with a bounded
operator, is again such a limit. -/
theorem comp_mem_approximable {T : F →L[𝕜] G} (hT : T ∈ approximable 𝕜 F G) (A : E →L[𝕜] F) :
    T.comp A ∈ approximable 𝕜 E G := by
  rw [← SetLike.mem_coe, coe_approximable] at hT ⊢
  exact map_mem_closure (f := fun S : F →L[𝕜] G => S.comp A)
    (continuous_id.clm_comp continuous_const) hT fun S hS => comp_mem_finiteRank hS A

/-- A bounded operator composed with an operator-norm limit of finite-rank operators is again
such a limit. -/
theorem mem_approximable_comp (B : F →L[𝕜] G) {T : E →L[𝕜] F} (hT : T ∈ approximable 𝕜 E F) :
    B.comp T ∈ approximable 𝕜 E G := by
  rw [← SetLike.mem_coe, coe_approximable] at hT ⊢
  exact map_mem_closure (f := fun S : E →L[𝕜] F => B.comp S)
    (continuous_const.clm_comp continuous_id) hT fun S hS => mem_finiteRank_comp B hS

/-- If a sequence (or net) of finite-rank operators converges in operator norm, its limit is an
operator-norm limit of finite-rank operators. -/
theorem mem_approximable_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → E →L[𝕜] F} {T₀ : E →L[𝕜] F} (hlim : Tendsto T l (𝓝 T₀))
    (hT : ∀ᶠ i in l, T i ∈ finiteRank 𝕜 E F) : T₀ ∈ approximable 𝕜 E F :=
  (isClosed_approximable 𝕜 E F).mem_of_tendsto hlim
    (hT.mono fun _ hi => finiteRank_le_approximable 𝕜 E F hi)

end General

/-! ### Finite-rank operators and their limits are compact -/

section Compact

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
variable {E F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A finite-rank operator is compact (over a locally compact field, e.g. `ℝ` or `ℂ`). -/
theorem isCompactOperator_of_mem_finiteRank {T : E →L[𝕜] F}
    (hT : T ∈ finiteRank 𝕜 E F) : IsCompactOperator T := by
  rw [mem_finiteRank] at hT
  have : ProperSpace (LinearMap.range (T : E →ₗ[𝕜] F)) := FiniteDimensional.proper 𝕜 _
  have hmem : ∀ x, T x ∈ LinearMap.range (T : E →ₗ[𝕜] F) := fun x => ⟨x, rfl⟩
  have h := (isCompactOperator_of_locallyCompactSpace_dom
    (T.codRestrict (LinearMap.range (T : E →ₗ[𝕜] F)) hmem)).clm_comp
      (LinearMap.range (T : E →ₗ[𝕜] F)).subtypeL
  exact h

/-- An operator-norm limit of finite-rank operators into a complete space is compact. -/
theorem isCompactOperator_of_mem_approximable [CompleteSpace F]
    {T : E →L[𝕜] F} (hT : T ∈ approximable 𝕜 E F) : IsCompactOperator T := by
  rw [← SetLike.mem_coe, coe_approximable] at hT
  have hsub : closure (finiteRank 𝕜 E F : Set (E →L[𝕜] F)) ⊆
      {f : E →L[𝕜] F | IsCompactOperator f} :=
    closure_minimal (fun S hS => isCompactOperator_of_mem_finiteRank hS)
      isClosed_setOfPred_isCompactOperator
  exact hsub hT

end Compact

/-! ### Compact operators into an inner product space -/

section Hilbert

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Finite-rank approximation, projection form.** A compact operator `K : E →L[𝕜] F` into an
inner product space is approximated within `ε` in operator norm by `P ∘ K`, where `P` is the
orthogonal projection onto a finite-dimensional subspace `V` of `F` (the span of a finite
`ε`-net of the image of the closed unit ball). -/
theorem exists_starProjection_comp_norm_sub_le {K : E →L[𝕜] F} (hK : IsCompactOperator K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (V : Submodule 𝕜 F) (_ : FiniteDimensional 𝕜 V),
      ‖K - V.starProjection.comp K‖ ≤ ε := by
  have hK' : IsCompactOperator (K : E →ₗ[𝕜] F) := hK
  obtain ⟨t, -, htfin, hcover⟩ :=
    finite_cover_balls_of_compact (hK'.isCompact_closure_image_closedBall 1) hε
  let V : Submodule 𝕜 F := Submodule.span 𝕜 t
  have hV : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 htfin
  refine ⟨V, hV, ?_⟩
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hε.le fun x hx => ?_
  have hKx : K x ∈ closure ((K : E →ₗ[𝕜] F) '' closedBall 0 1) :=
    subset_closure ⟨x, by simp [hx], rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (hcover hKx)
  have hyV : y ∈ V := Submodule.subset_span hyt
  rw [sub_apply, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_minimal]
  calc ⨅ v : V, ‖K x - (v : F)‖ ≤ ‖K x - ((⟨y, hyV⟩ : V) : F)‖ :=
        ciInf_le ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩ _
    _ = dist (K x) y := (dist_eq_norm _ _).symm
    _ ≤ ε := (mem_ball.1 hy).le

/-- **Compact operators are norm limits of finite-rank operators.** Let `F` be an inner product
space over `RCLike 𝕜` (e.g. a Hilbert space) and `K : E →L[𝕜] F` compact. For every `ε > 0`
there is a continuous linear `K'` with finite-dimensional range and `‖K - K'‖ ≤ ε`. -/
theorem exists_finiteRank_norm_sub_le {K : E →L[𝕜] F} (hK : IsCompactOperator K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : E →L[𝕜] F, FiniteDimensional 𝕜 (LinearMap.range (K' : E →ₗ[𝕜] F)) ∧ ‖K - K'‖ ≤ ε := by
  obtain ⟨V, hV, hnorm⟩ := exists_starProjection_comp_norm_sub_le hK hε
  refine ⟨V.starProjection.comp K, ?_, hnorm⟩
  have h : LinearMap.range ((V.starProjection.comp K : E →L[𝕜] F) : E →ₗ[𝕜] F) ≤ V := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.starProjection_apply_mem V (K x)
  exact Submodule.finiteDimensional_of_le h

/-- Strict-inequality form of `exists_finiteRank_norm_sub_le`. -/
theorem exists_finiteRank_norm_sub_lt {K : E →L[𝕜] F} (hK : IsCompactOperator K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : E →L[𝕜] F, FiniteDimensional 𝕜 (LinearMap.range (K' : E →ₗ[𝕜] F)) ∧ ‖K - K'‖ < ε := by
  obtain ⟨K', hK', h⟩ := exists_finiteRank_norm_sub_le hK (half_pos hε)
  exact ⟨K', hK', h.trans_lt (half_lt_self hε)⟩

/-- **Sequential form.** A compact operator into an inner product space is the operator-norm
limit of a sequence of finite-rank operators, with `‖K - Kₙ‖ ≤ 1 / (n + 1)`. -/
theorem exists_tendsto_finiteRank {K : E →L[𝕜] F} (hK : IsCompactOperator K) :
    ∃ T : ℕ → E →L[𝕜] F, (∀ n, FiniteDimensional 𝕜 (LinearMap.range (T n : E →ₗ[𝕜] F))) ∧
      (∀ n : ℕ, ‖K - T n‖ ≤ 1 / ((n : ℝ) + 1)) ∧ Tendsto T atTop (𝓝 K) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => Nat.one_div_pos_of_nat
  choose T hTfin hTnorm using fun n : ℕ => exists_finiteRank_norm_sub_le hK (hpos n)
  refine ⟨T, hTfin, hTnorm, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [norm_sub_rev]
  exact hTnorm n

/-- A compact operator into an inner product space is an operator-norm limit of finite-rank
operators. -/
theorem mem_approximable_of_isCompactOperator {K : E →L[𝕜] F} (hK : IsCompactOperator K) :
    K ∈ approximable 𝕜 E F :=
  mem_approximable_iff_le.2 fun _ hε => exists_finiteRank_norm_sub_le hK hε

/-- Into a Hilbert space, an operator is compact iff it is an operator-norm limit of finite-rank
operators. -/
theorem mem_approximable_iff_isCompactOperator [CompleteSpace F] {K : E →L[𝕜] F} :
    K ∈ approximable 𝕜 E F ↔ IsCompactOperator K :=
  ⟨isCompactOperator_of_mem_approximable, mem_approximable_of_isCompactOperator⟩

/-- Into a Hilbert space, the closure of the finite-rank operators is the space of compact
operators. -/
theorem approximable_eq_compactOperator [CompleteSpace F] :
    approximable 𝕜 E F = compactOperator (RingHom.id 𝕜) E F := by
  ext K
  exact mem_approximable_iff_isCompactOperator

/-- **Compact ∘ bounded.** If `K : F →L[𝕜] G` is compact (with `G` an inner product space) and
`A : E →L[𝕜] F` is bounded, then `K ∘ A` is an operator-norm limit of finite-rank operators. -/
theorem comp_mem_approximable_of_isCompactOperator
    {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {K : E →L[𝕜] F} (hK : IsCompactOperator K) (A : E' →L[𝕜] E) :
    K.comp A ∈ approximable 𝕜 E' F :=
  comp_mem_approximable (mem_approximable_of_isCompactOperator hK) A

/-- **Bounded ∘ compact.** If `K : E →L[𝕜] F` is compact (with `F` an inner product space) and
`B : F →L[𝕜] G` is bounded, then `B ∘ K` is an operator-norm limit of finite-rank operators;
here `G` need only be a seminormed space. -/
theorem mem_approximable_comp_of_isCompactOperator
    {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {K : E →L[𝕜] F} (hK : IsCompactOperator K) (B : F →L[𝕜] G) :
    B.comp K ∈ approximable 𝕜 E G :=
  mem_approximable_comp B (mem_approximable_of_isCompactOperator hK)

end Hilbert

end UnforcedLeray.Infra.FiniteRankApprox
