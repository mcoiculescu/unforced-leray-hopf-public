import UnforcedLeray.Infra.WeaklyNullCompact.Extraction
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Compactness through weakly null sequences

`paper/main.tex`, lines 338-340: "Apply the Duhamel formula to a weakly null sequence in `X`:
compactness at each positive `r` and this integrable bound show that `E(t,s) - S_0(t-s)` is
compact." The abstract fact used there is the sequential characterization of compact operators
on a Hilbert space:

* `isCompactOperator_of_forall_weaklyNull` (core): for a Hilbert space `E` over `RCLike 𝕜` and a
  normed space `F`, a continuous linear `T : E →L[𝕜] F` that maps every weakly null sequence
  (`⟪y, x n⟫ → 0` for every `y`) to a norm null sequence (`‖T (x n)‖ → 0`) is compact.
* `tendsto_norm_of_isCompactOperator_of_weaklyNull` (converse): a compact `T` maps weakly null
  sequences to norm null sequences.
* `isCompactOperator_iff_forall_weaklyNull`: the equivalence.
* `isCompactOperator_of_forall_weaklyNull_of_norm_le_one`: it suffices to test weakly null
  sequences in the closed unit ball.
* Versions for sequences converging weakly to `x₀`: `isCompactOperator_of_forall_weakTendsto`,
  `tendsto_of_isCompactOperator_of_weakTendsto`, `isCompactOperator_iff_forall_weakTendsto`.

Ingredients: weakly null sequences are bounded (`exists_norm_le_of_weaklyNull`, Banach–Steinhaus)
and bounded sequences have weakly convergent subsequences (`exists_subseq_weakTendsto`), both in
`UnforcedLeray/Infra/WeaklyNullCompact/{Basic,Extraction}.lean`. The codomain `F` need not be
complete: the image of the closed unit ball is shown to be sequentially compact itself.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open scoped InnerProductSpace

namespace UnforcedLeray.Infra.WeaklyNullCompact

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `T` maps weakly null sequences to norm null sequences, then the image of the closed ball
of radius `r` is sequentially compact. -/
theorem isSeqCompact_image_closedBall_of_forall_weaklyNull [CompleteSpace E] (T : E →L[𝕜] F)
    (hT : ∀ x : ℕ → E, (∀ y : E, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) →
      Tendsto (fun n => ‖T (x n)‖) atTop (𝓝 0)) (r : ℝ) :
    IsSeqCompact (T '' Metric.closedBall (0 : E) r) := by
  intro z hz
  choose x hx hxz using hz
  have hb : ∀ n, ‖x n‖ ≤ r := fun n => by simpa using hx n
  obtain ⟨φ, hφ, x₀, hx₀, hw⟩ := exists_subseq_weakTendsto (𝕜 := 𝕜) hb
  refine ⟨T x₀, ⟨x₀, by simpa using hx₀, rfl⟩, φ, hφ, ?_⟩
  have hnull := hT _ (weakTendsto_zero_iff.mp hw.sub_const)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine hnull.congr fun n => ?_
  simp only [Function.comp_apply, map_sub, hxz]

/-- **Compactness through weakly null sequences** (`paper/main.tex`, lines 338-340). Let `E` be
a Hilbert space over `𝕜` (`RCLike`) and `F` a normed space. A continuous linear map
`T : E →L[𝕜] F` such that `‖T (x n)‖ → 0` for every weakly null sequence `x` (that is,
`⟪y, x n⟫ → 0` for every `y : E`) is a compact operator. -/
theorem isCompactOperator_of_forall_weaklyNull [CompleteSpace E] (T : E →L[𝕜] F)
    (hT : ∀ x : ℕ → E, (∀ y : E, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) →
      Tendsto (fun n => ‖T (x n)‖) atTop (𝓝 0)) :
    IsCompactOperator T :=
  (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ one_pos, _,
      (isSeqCompact_image_closedBall_of_forall_weaklyNull T hT 1).isCompact, subset_rfl⟩

/-- **Compactness through bounded weakly null sequences.** It suffices to test the sequences in
the closed unit ball: if `‖T (x n)‖ → 0` for every weakly null `x` with `‖x n‖ ≤ 1`, then `T` is
compact. (General weakly null sequences are bounded, by uniform boundedness, and are rescaled.) -/
theorem isCompactOperator_of_forall_weaklyNull_of_norm_le_one [CompleteSpace E] (T : E →L[𝕜] F)
    (hT : ∀ x : ℕ → E, (∀ n, ‖x n‖ ≤ 1) →
      (∀ y : E, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) →
      Tendsto (fun n => ‖T (x n)‖) atTop (𝓝 0)) :
    IsCompactOperator T := by
  refine isCompactOperator_of_forall_weaklyNull T fun x hx => ?_
  obtain ⟨M, hM⟩ := exists_norm_le_of_weaklyNull (𝕜 := 𝕜) hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM1 : 0 < M + 1 := by linarith
  set c : 𝕜 := (((M + 1)⁻¹ : ℝ) : 𝕜) with hc
  have hcn : ‖c‖ = (M + 1)⁻¹ := by
    rw [hc, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hM1)]
  have hb : ∀ n, ‖c • x n‖ ≤ 1 := fun n => by
    rw [norm_smul, hcn, inv_mul_le_iff₀ hM1]
    linarith [hM n]
  have hw : ∀ y : E, Tendsto (fun n => ⟪y, c • x n⟫_𝕜) atTop (𝓝 0) := fun y => by
    simpa only [inner_smul_right, mul_zero] using (hx y).const_mul c
  have h1 := (hT (fun n => c • x n) hb hw).const_mul (M + 1)
  rw [mul_zero] at h1
  refine h1.congr fun n => ?_
  rw [map_smul, norm_smul, hcn, ← mul_assoc, mul_inv_cancel₀ hM1.ne', one_mul]

/-- **Compact operators map weakly null sequences to norm null sequences.** -/
theorem tendsto_norm_of_isCompactOperator_of_weaklyNull [CompleteSpace E] {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) {x : ℕ → E}
    (hx : ∀ y : E, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) :
    Tendsto (fun n => ‖T (x n)‖) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_norm_le_of_weaklyNull (𝕜 := 𝕜) hx
  have hK := hT.isCompact_closure_image_closedBall M
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hmem : ∀ n, T (x (ns n)) ∈ closure (T '' Metric.closedBall 0 M) := fun n =>
    subset_closure ⟨x (ns n), by simpa using hM (ns n), rfl⟩
  obtain ⟨z, -, ms, hms, hz⟩ := hK.tendsto_subseq hmem
  -- the strong limit `z` vanishes: every continuous linear functional kills it
  have hz0 : z = 0 := by
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun f => ?_
    have hw : WeakTendsto 𝕜 (x ∘ (ns ∘ ms)) atTop 0 :=
      (weakTendsto_zero_iff.mpr hx).comp (hns.comp hms.tendsto_atTop)
    have h1 := hw.tendsto_dual_map T f
    have h2 : Tendsto (fun n => f (T (x (ns (ms n))))) atTop (𝓝 (f z)) :=
      (f.continuous.tendsto z).comp hz
    rw [map_zero, map_zero] at h1
    exact tendsto_nhds_unique h2 h1
  refine ⟨ms, ?_⟩
  have := hz.norm
  rw [hz0, norm_zero] at this
  exact this

/-- **Compactness through weakly null sequences, as an equivalence.** On a Hilbert space, a
continuous linear map is compact iff it maps weakly null sequences to norm null sequences. -/
theorem isCompactOperator_iff_forall_weaklyNull [CompleteSpace E] (T : E →L[𝕜] F) :
    IsCompactOperator T ↔ ∀ x : ℕ → E, (∀ y : E, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) →
      Tendsto (fun n => ‖T (x n)‖) atTop (𝓝 0) :=
  ⟨fun hT _ hx => tendsto_norm_of_isCompactOperator_of_weaklyNull hT hx,
    isCompactOperator_of_forall_weaklyNull T⟩

/-- **Compact operators map weakly convergent sequences to norm convergent ones**: if `T` is
compact and `x n ⇀ x₀`, then `T (x n) → T x₀`. -/
theorem tendsto_of_isCompactOperator_of_weakTendsto [CompleteSpace E] {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) {x : ℕ → E} {x₀ : E} (hx : WeakTendsto 𝕜 x atTop x₀) :
    Tendsto (fun n => T (x n)) atTop (𝓝 (T x₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine (tendsto_norm_of_isCompactOperator_of_weaklyNull hT
    (weakTendsto_zero_iff.mp hx.sub_const)).congr fun n => ?_
  rw [map_sub]

/-- Explicit form of `tendsto_of_isCompactOperator_of_weakTendsto`: if `T` is compact and
`⟪y, x n⟫ → ⟪y, x₀⟫` for every `y`, then `‖T (x n) - T x₀‖ → 0`. -/
theorem tendsto_norm_sub_of_isCompactOperator_of_forall_inner [CompleteSpace E] {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) {x : ℕ → E} {x₀ : E}
    (hx : ∀ y : E, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 ⟪y, x₀⟫_𝕜)) :
    Tendsto (fun n => ‖T (x n) - T x₀‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_of_isCompactOperator_of_weakTendsto hT hx)

/-- **Compactness through weakly convergent sequences.** A continuous linear map `T` on a
Hilbert space such that `T (x n) → T x₀` whenever `x n ⇀ x₀` is compact. -/
theorem isCompactOperator_of_forall_weakTendsto [CompleteSpace E] (T : E →L[𝕜] F)
    (hT : ∀ (x : ℕ → E) (x₀ : E), WeakTendsto 𝕜 x atTop x₀ →
      Tendsto (fun n => T (x n)) atTop (𝓝 (T x₀))) :
    IsCompactOperator T := by
  refine isCompactOperator_of_forall_weaklyNull T fun x hx => ?_
  have := (hT x 0 (weakTendsto_zero_iff.mpr hx)).norm
  rwa [map_zero, norm_zero] at this

/-- **Compactness through weakly convergent sequences, as an equivalence.** -/
theorem isCompactOperator_iff_forall_weakTendsto [CompleteSpace E] (T : E →L[𝕜] F) :
    IsCompactOperator T ↔ ∀ (x : ℕ → E) (x₀ : E), WeakTendsto 𝕜 x atTop x₀ →
      Tendsto (fun n => T (x n)) atTop (𝓝 (T x₀)) :=
  ⟨fun hT _ _ hx => tendsto_of_isCompactOperator_of_weakTendsto hT hx,
    isCompactOperator_of_forall_weakTendsto T⟩

end UnforcedLeray.Infra.WeaklyNullCompact
