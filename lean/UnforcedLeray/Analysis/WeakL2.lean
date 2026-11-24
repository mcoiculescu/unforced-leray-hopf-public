import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Tactic

/-
Adapted from Matei P. Coiculescu's NonUniqueEuler repository, Apache-2.0.
Source commit: d81c3f456505f8a3e8211f2a9f63313d0599ed5a.
Only the general real Hilbert-space portion is retained; no Euler theorem is imported.
See THIRD_PARTY_NOTICES.md and LICENSE-NonUniqueEuler.
-/
noncomputable section

open Filter Topology Set
open scoped InnerProductSpace

namespace UnforcedLeray.WeakL2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weak convergence `u i ⇀ x` along the filter `l`: `⟪u i, y⟫ → ⟪x, y⟫` for every `y`. -/
def WeakTendsto {ι : Type*} (u : ι → E) (l : Filter ι) (x : E) : Prop :=
  ∀ y : E, Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 ⟪x, y⟫_ℝ)

/-- Weak continuity on a set: `t ↦ ⟪u t, y⟫` is continuous on `s` for every `y`. -/
def WeakContinuousOn {τ : Type*} [TopologicalSpace τ] (u : τ → E) (s : Set τ) : Prop :=
  ∀ y : E, ContinuousOn (fun t => ⟪u t, y⟫_ℝ) s

/-- Uniform weak convergence on `s`: for every `y`, `⟪u i t, y⟫ → ⟪U t, y⟫` uniformly in
`t ∈ s` (`prop:compact`(i), `03_compactness.tex:262-263`). -/
def WeakTendstoUniformlyOn {ι τ : Type*} (u : ι → τ → E) (U : τ → E) (l : Filter ι)
    (s : Set τ) : Prop :=
  ∀ y : E, TendstoUniformlyOn (fun i t => ⟪u i t, y⟫_ℝ) (fun t => ⟪U t, y⟫_ℝ) l s

namespace WeakTendsto

variable {ι : Type*} {u v : ι → E} {l : Filter ι} {x x' z : E}

theorem tendsto_inner (h : WeakTendsto u l x) (y : E) :
    Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 ⟪x, y⟫_ℝ) :=
  h y

/-- Weak limits are unique. -/
theorem unique [l.NeBot] (h : WeakTendsto u l x) (h' : WeakTendsto u l x') : x = x' := by
  have key : ⟪x - x', x - x'⟫_ℝ = 0 := by
    rw [inner_sub_left, tendsto_nhds_unique (h (x - x')) (h' (x - x')), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)

/-- Composition with a map of filters (in particular, passing to a subsequence). -/
theorem comp {κ : Type*} {l' : Filter κ} {φ : κ → ι} (h : WeakTendsto u l x)
    (hφ : Tendsto φ l' l) : WeakTendsto (u ∘ φ) l' x :=
  fun y => (h y).comp hφ

/-- Passing to a subsequence. -/
theorem subseq {u : ℕ → E} (h : WeakTendsto u atTop x) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakTendsto (u ∘ φ) atTop x :=
  h.comp hφ.tendsto_atTop

theorem mono_left {l' : Filter ι} (h : WeakTendsto u l x) (hl : l' ≤ l) :
    WeakTendsto u l' x :=
  fun y => (h y).mono_left hl

theorem add (h : WeakTendsto u l x) (h' : WeakTendsto v l z) :
    WeakTendsto (fun i => u i + v i) l (x + z) := by
  intro y
  simp only [inner_add_left]
  exact (h y).add (h' y)

theorem sub (h : WeakTendsto u l x) (h' : WeakTendsto v l z) :
    WeakTendsto (fun i => u i - v i) l (x - z) := by
  intro y
  simp only [inner_sub_left]
  exact (h y).sub (h' y)

theorem const_smul (h : WeakTendsto u l x) (c : ℝ) :
    WeakTendsto (fun i => c • u i) l (c • x) := by
  intro y
  simp only [real_inner_smul_left]
  exact (h y).const_mul c

theorem neg (h : WeakTendsto u l x) : WeakTendsto (fun i => -u i) l (-x) := by
  intro y
  simp only [inner_neg_left]
  exact (h y).neg

end WeakTendsto

/-- Strong convergence implies weak convergence. -/
theorem _root_.Filter.Tendsto.weakTendsto {ι : Type*} {u : ι → E} {l : Filter ι} {x : E}
    (h : Tendsto u l (𝓝 x)) : WeakTendsto u l x :=
  fun _ => h.inner tendsto_const_nhds

theorem weakTendsto_const {ι : Type*} (l : Filter ι) (x : E) :
    WeakTendsto (fun _ : ι => x) l x :=
  fun _ => tendsto_const_nhds

namespace WeakContinuousOn

variable {τ : Type*} [TopologicalSpace τ] {u : τ → E} {s t : Set τ}

theorem continuousOn_inner (h : WeakContinuousOn u s) (y : E) :
    ContinuousOn (fun t => ⟪u t, y⟫_ℝ) s :=
  h y

theorem mono (h : WeakContinuousOn u s) (hts : t ⊆ s) : WeakContinuousOn u t :=
  fun y => (h y).mono hts

/-- A weakly continuous path is weakly continuous at each point within `s`. -/
theorem weakTendsto (h : WeakContinuousOn u s) {t₀ : τ} (ht₀ : t₀ ∈ s) :
    WeakTendsto u (𝓝[s] t₀) (u t₀) :=
  fun y => h y t₀ ht₀

end WeakContinuousOn

/-- Strongly continuous paths are weakly continuous. -/
theorem _root_.ContinuousOn.weakContinuousOn {τ : Type*} [TopologicalSpace τ] {u : τ → E}
    {s : Set τ} (h : ContinuousOn u s) : WeakContinuousOn u s :=
  fun _ => h.inner continuousOn_const

/-- A uniform weak limit of weakly continuous paths is weakly continuous. -/
theorem WeakTendstoUniformlyOn.weakContinuousOn {ι τ : Type*} [TopologicalSpace τ]
    {u : ι → τ → E} {U : τ → E} {l : Filter ι} [l.NeBot] {s : Set τ}
    (h : WeakTendstoUniformlyOn u U l s) (hu : ∀ᶠ i in l, WeakContinuousOn (u i) s) :
    WeakContinuousOn U s :=
  fun y => (h y).continuousOn (hu.mono fun _ hi => hi y).frequently

/-- Uniform weak convergence on `s` gives weak convergence at every point of `s`. -/
theorem WeakTendstoUniformlyOn.weakTendsto {ι τ : Type*} {u : ι → τ → E} {U : τ → E}
    {l : Filter ι} {s : Set τ} (h : WeakTendstoUniformlyOn u U l s) {t : τ} (ht : t ∈ s) :
    WeakTendsto (fun i => u i t) l (U t) :=
  fun y => (h y).tendsto_at ht


end UnforcedLeray.WeakL2
