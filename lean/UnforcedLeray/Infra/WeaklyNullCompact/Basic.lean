import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Weak convergence of sequences in a Hilbert space over `RCLike`

General infrastructure for the compactness criterion of `paper/main.tex` (lines 338-340:
"Apply the Duhamel formula to a weakly null sequence in `X` ..."). The space `E` is an inner
product space over an `RCLike` field `𝕜` (so `ℝ` or `ℂ`); the inner product `⟪x, y⟫_𝕜` is
conjugate-linear in `x` and linear in `y` (Mathlib convention).

* `WeakTendsto 𝕜 u l x`: `u i ⇀ x` along the filter `l`, i.e. `⟪y, u i⟫ → ⟪y, x⟫` for every `y`.
  By the Riesz representation theorem this is weak convergence (`weakTendsto_iff_forall_dual`).
* `weakTendsto_zero_iff`: `u i ⇀ 0` iff `⟪y, u i⟫ → 0` for every `y` (weakly null).
* `exists_norm_le_of_forall_norm_inner_le`, `WeakTendsto.exists_norm_le`: weakly bounded and
  weakly convergent sequences are norm bounded (uniform boundedness, Mathlib `banach_steinhaus`).
* `WeakTendsto.norm_le`: a weak limit of vectors of norm `≤ M` has norm `≤ M`.
* `WeakTendsto.map`: bounded linear maps preserve weak convergence.

The real-scalar version of part of this file is in the reference formalization
`NonUniqueEuler/Defs/Infra/WeakL2.lean` and `NonUniqueEuler/P/Infra/WeakL2/Norm.lean`
(`NonUniqueEuler/lean/NonUniqueEuler/`); the statements here are adapted to `RCLike 𝕜` and
to the orientation `⟪y, u i⟫` (linear in `u i`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Infra.WeaklyNullCompact

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- Weak convergence `u i ⇀ x` along the filter `l`: `⟪y, u i⟫ → ⟪y, x⟫` for every `y : E`. -/
def WeakTendsto {ι : Type*} (u : ι → E) (l : Filter ι) (x : E) : Prop :=
  ∀ y : E, Tendsto (fun i => ⟪y, u i⟫_𝕜) l (𝓝 ⟪y, x⟫_𝕜)

section Basic

variable {ι : Type*} {u v : ι → E} {l : Filter ι} {x z : E}

theorem weakTendsto_iff :
    WeakTendsto 𝕜 u l x ↔ ∀ y : E, Tendsto (fun i => ⟪y, u i⟫_𝕜) l (𝓝 ⟪y, x⟫_𝕜) :=
  Iff.rfl

/-- The other orientation of the inner product: `⟪u i, y⟫ → ⟪x, y⟫` for every `y`. -/
theorem weakTendsto_iff_inner_left :
    WeakTendsto 𝕜 u l x ↔ ∀ y : E, Tendsto (fun i => ⟪u i, y⟫_𝕜) l (𝓝 ⟪x, y⟫_𝕜) := by
  constructor
  · intro h y
    have := ((RCLike.continuous_conj (K := 𝕜)).tendsto _).comp (h y)
    simpa only [Function.comp_def, inner_conj_symm] using this
  · intro h y
    have := ((RCLike.continuous_conj (K := 𝕜)).tendsto _).comp (h y)
    simpa only [Function.comp_def, inner_conj_symm] using this

/-- Weakly null: `u i ⇀ 0` iff `⟪y, u i⟫ → 0` for every `y`. -/
theorem weakTendsto_zero_iff :
    WeakTendsto 𝕜 u l 0 ↔ ∀ y : E, Tendsto (fun i => ⟪y, u i⟫_𝕜) l (𝓝 0) := by
  simp only [WeakTendsto, inner_zero_right]

/-- `u i ⇀ x` iff `u i - x ⇀ 0`. -/
theorem weakTendsto_iff_sub :
    WeakTendsto 𝕜 u l x ↔ WeakTendsto 𝕜 (fun i => u i - x) l 0 := by
  rw [weakTendsto_zero_iff]
  refine forall_congr' fun y => ?_
  simp only [inner_sub_right]
  rw [← tendsto_sub_const_iff ⟪y, x⟫_𝕜, sub_self]

namespace WeakTendsto

theorem tendsto_inner (h : WeakTendsto 𝕜 u l x) (y : E) :
    Tendsto (fun i => ⟪y, u i⟫_𝕜) l (𝓝 ⟪y, x⟫_𝕜) :=
  h y

theorem tendsto_inner_left (h : WeakTendsto 𝕜 u l x) (y : E) :
    Tendsto (fun i => ⟪u i, y⟫_𝕜) l (𝓝 ⟪x, y⟫_𝕜) :=
  weakTendsto_iff_inner_left.mp h y

/-- Weak limits are unique. -/
theorem unique [l.NeBot] {x' : E} (h : WeakTendsto 𝕜 u l x) (h' : WeakTendsto 𝕜 u l x') :
    x = x' := by
  have key : ⟪x - x', x - x'⟫_𝕜 = 0 := by
    rw [inner_sub_right, tendsto_nhds_unique (h (x - x')) (h' (x - x')), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)

/-- Composition with a map of filters (in particular, passing to a subsequence). -/
theorem comp {κ : Type*} {l' : Filter κ} {φ : κ → ι} (h : WeakTendsto 𝕜 u l x)
    (hφ : Tendsto φ l' l) : WeakTendsto 𝕜 (u ∘ φ) l' x :=
  fun y => (h y).comp hφ

/-- Passing to a subsequence. -/
theorem subseq {u : ℕ → E} (h : WeakTendsto 𝕜 u atTop x) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakTendsto 𝕜 (u ∘ φ) atTop x :=
  h.comp hφ.tendsto_atTop

theorem mono_left {l' : Filter ι} (h : WeakTendsto 𝕜 u l x) (hl : l' ≤ l) :
    WeakTendsto 𝕜 u l' x :=
  fun y => (h y).mono_left hl

theorem congr' (h : WeakTendsto 𝕜 u l x) (huv : u =ᶠ[l] v) : WeakTendsto 𝕜 v l x := by
  intro y
  refine (h y).congr' ?_
  filter_upwards [huv] with i hi
  rw [hi]

theorem add (h : WeakTendsto 𝕜 u l x) (h' : WeakTendsto 𝕜 v l z) :
    WeakTendsto 𝕜 (fun i => u i + v i) l (x + z) := by
  intro y
  simp only [inner_add_right]
  exact (h y).add (h' y)

theorem sub (h : WeakTendsto 𝕜 u l x) (h' : WeakTendsto 𝕜 v l z) :
    WeakTendsto 𝕜 (fun i => u i - v i) l (x - z) := by
  intro y
  simp only [inner_sub_right]
  exact (h y).sub (h' y)

theorem const_smul (h : WeakTendsto 𝕜 u l x) (c : 𝕜) :
    WeakTendsto 𝕜 (fun i => c • u i) l (c • x) := by
  intro y
  simp only [inner_smul_right]
  exact (h y).const_mul c

theorem neg (h : WeakTendsto 𝕜 u l x) : WeakTendsto 𝕜 (fun i => -u i) l (-x) := by
  intro y
  simp only [inner_neg_right]
  exact (h y).neg

/-- `u i ⇀ x` gives the weakly null family `u i - x`. -/
theorem sub_const (h : WeakTendsto 𝕜 u l x) : WeakTendsto 𝕜 (fun i => u i - x) l 0 :=
  weakTendsto_iff_sub.mp h

end WeakTendsto

/-- Strong convergence implies weak convergence. -/
theorem WeakTendsto.of_tendsto (h : Tendsto u l (𝓝 x)) : WeakTendsto 𝕜 u l x :=
  fun y => ((continuous_const (y := y)).inner continuous_id |>.tendsto x).comp h

theorem weakTendsto_const : WeakTendsto 𝕜 (fun _ : ι => x) l x :=
  fun _ => tendsto_const_nhds

end Basic

/-! ### Boundedness (uniform boundedness principle) -/

/-- **Weakly bounded families are bounded.** If `‖⟪y, u i⟫‖ ≤ C y` for every `y`, then the family
`u` is norm bounded. This is Banach–Steinhaus applied to the functionals `⟪u i, ·⟫`. -/
theorem exists_norm_le_of_forall_norm_inner_le [CompleteSpace E] {ι : Type*} {u : ι → E}
    (h : ∀ y : E, ∃ C, ∀ i, ‖⟪y, u i⟫_𝕜‖ ≤ C) : ∃ M, ∀ i, ‖u i‖ ≤ M := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun i => innerSL 𝕜 (u i)) fun y => by
    obtain ⟨C, hC⟩ := h y
    exact ⟨C, fun i => by rw [innerSL_apply_apply, norm_inner_symm]; exact hC i⟩
  exact ⟨C, fun i => by rw [← innerSL_apply_norm (𝕜 := 𝕜)]; exact hC i⟩

/-- **Weakly convergent sequences are bounded** (uniform boundedness). -/
theorem WeakTendsto.exists_norm_le [CompleteSpace E] {u : ℕ → E} {x : E}
    (h : WeakTendsto 𝕜 u atTop x) : ∃ M : ℝ, ∀ n, ‖u n‖ ≤ M := by
  refine exists_norm_le_of_forall_norm_inner_le (𝕜 := 𝕜) fun y => ?_
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ (h y))
  exact ⟨C, fun n => hC _ (mem_range_self n)⟩

/-- Weakly null sequences are bounded (uniform boundedness). -/
theorem exists_norm_le_of_weaklyNull [CompleteSpace E] {u : ℕ → E}
    (h : ∀ y : E, Tendsto (fun n => ⟪y, u n⟫_𝕜) atTop (𝓝 0)) : ∃ M : ℝ, ∀ n, ‖u n‖ ≤ M :=
  WeakTendsto.exists_norm_le (𝕜 := 𝕜) (x := 0) (weakTendsto_zero_iff.mpr h)

/-- A weak limit of vectors of norm `≤ M` has norm `≤ M`. -/
theorem WeakTendsto.norm_le {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → E} {x : E}
    (h : WeakTendsto 𝕜 u l x) {M : ℝ} (hM : ∀ᶠ i in l, ‖u i‖ ≤ M) : ‖x‖ ≤ M := by
  have hM0 : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hM.exists
    exact (norm_nonneg _).trans hi
  -- `‖x‖² = lim ‖⟪x, u i⟫‖ ≤ M ‖x‖`
  have hle : ‖x‖ * ‖x‖ ≤ M * ‖x‖ := by
    have hlim := (h x).norm
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [hM] with i hi
    calc ‖⟪x, u i⟫_𝕜‖ ≤ ‖x‖ * ‖u i‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * M := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ = M * ‖x‖ := mul_comm _ _
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]; exact hM0
  · exact le_of_mul_le_mul_right hle hpos

/-! ### Duality -/

/-- Weak convergence is convergence against every continuous linear functional
(Riesz representation). -/
theorem weakTendsto_iff_forall_dual [CompleteSpace E] {ι : Type*} {l : Filter ι} {u : ι → E}
    {x : E} :
    WeakTendsto 𝕜 u l x ↔ ∀ f : StrongDual 𝕜 E, Tendsto (fun i => f (u i)) l (𝓝 (f x)) := by
  constructor
  · intro h f
    set y : E := (InnerProductSpace.toDual 𝕜 E).symm f
    have hf : ∀ z, f z = ⟪y, z⟫_𝕜 := fun z => by
      rw [InnerProductSpace.toDual_symm_apply]
    simp only [hf]
    exact h y
  · intro h y
    have := h (innerSL 𝕜 y)
    simpa only [innerSL_apply_apply] using this

/-- Bounded linear maps preserve weak convergence. -/
theorem WeakTendsto.map [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] {ι : Type*} {l : Filter ι} {u : ι → E} {x : E} (T : E →L[𝕜] F)
    (h : WeakTendsto 𝕜 u l x) : WeakTendsto 𝕜 (fun i => T (u i)) l (T x) := by
  intro y
  have := (weakTendsto_iff_forall_dual.mp h) ((innerSL 𝕜 y).comp T)
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using this

/-- A weakly convergent family is mapped by a continuous linear map into a normed space to a
family converging against every continuous linear functional. -/
theorem WeakTendsto.tendsto_dual_map [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {ι : Type*} {l : Filter ι} {u : ι → E} {x : E} (T : E →L[𝕜] F)
    (h : WeakTendsto 𝕜 u l x) (f : StrongDual 𝕜 F) :
    Tendsto (fun i => f (T (u i))) l (𝓝 (f (T x))) :=
  (weakTendsto_iff_forall_dual.mp h) (f.comp T)

end UnforcedLeray.Infra.WeaklyNullCompact
