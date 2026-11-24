import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Sequences

/-!
# Actual local-uniform compactness for annular-mode extensions

The square-root modulus supplied by the one-dimensional energy estimate gives
uniform equicontinuity. Pointwise compactness follows from the actual bounded
complex range. Arzelà--Ascoli in the compact-open topology on C(ℝ,ℂ), followed
by sequential compactness, produces a single subsequence on all compact sets.
No compactness assumption or finite-dimensional model of the function space is
introduced. Application to the annular modes requires their actual zero-extension
bounds, supplied separately.
-/

noncomputable section
open Set Filter Topology
open scoped UniformConvergence
namespace UnforcedLeray.Rayleigh

/-- A common square-root modulus is an actual uniform equicontinuity estimate. -/
theorem uniformEquicontinuous_of_sqrt_bound {ι : Type*} (F : ι → ℝ → ℂ) (K : ℝ)
    (hmod : ∀ n x y, ‖F n x - F n y‖ ≤ K * Real.sqrt |x - y|) :
    UniformEquicontinuous F := by
  refine Metric.uniformEquicontinuous_of_continuity_modulus
    (fun r : ℝ => K * Real.sqrt r) ?_ F ?_
  · simpa only [Pi.mul_apply, Real.sqrt_zero, mul_zero] using
      ((continuous_const : Continuous (fun _ : ℝ => K)).fun_mul Real.continuous_sqrt).tendsto (0 : ℝ)
  · intro x y n
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hmod n x y

/-- The actual compact-open closure of a bounded, uniformly Hölder family is compact. -/
theorem isCompact_closure_of_sup_sqrt_bound (F : ℕ → C(ℝ, ℂ)) (M K : ℝ)
    (hsup : ∀ n x, ‖F n x‖ ≤ M)
    (hmod : ∀ n x y, ‖F n x - F n y‖ ≤ K * Real.sqrt |x - y|) :
    IsCompact (closure (range F)) := by
  let 𝔖 : Set (Set ℝ) := {S | IsCompact S}
  have hcover : ⋃₀ 𝔖 = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton
  let : T2Space (ℝ →ᵤ[𝔖] ℂ) := UniformOnFun.t2Space_of_covering hcover
  have hemb : Topology.IsClosedEmbedding
      (UniformOnFun.ofFun 𝔖 ∘ (fun f : C(ℝ, ℂ) => (f : ℝ → ℂ))) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have heq : Equicontinuous (fun f : range F => (f.1 : ℝ → ℂ)) := by
    apply (uniformEquicontinuous_of_sqrt_bound _ K ?_).equicontinuous
    rintro ⟨f, ⟨n, rfl⟩⟩ x y
    exact hmod n x y
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun f : C(ℝ, ℂ) => (f : ℝ → ℂ)) (𝔖 := 𝔖)
    (fun _ hS => hS) hemb
  · intro S _
    exact heq.equicontinuousOn S
  · intro S _ x _
    refine ⟨Metric.closedBall (0 : ℂ) M, isCompact_closedBall _ _, ?_⟩
    rintro f ⟨n, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsup n x

/-- One increasing subsequence converges uniformly on every compact subset of ℝ.
The limit retains the common supremum and Hölder bounds. -/
theorem exists_uniformOnCompacts_subsequence_of_sup_sqrt_bound
    (F : ℕ → ℝ → ℂ) (hF : ∀ n, Continuous (F n)) (M K : ℝ)
    (hsup : ∀ n x, ‖F n x‖ ≤ M)
    (hmod : ∀ n x y, ‖F n x - F n y‖ ≤ K * Real.sqrt |x - y|) :
    ∃ (f : ℝ → ℂ) (φ : ℕ → ℕ), Continuous f ∧ StrictMono φ ∧
      (∀ S : Set ℝ, IsCompact S → TendstoUniformlyOn (fun n => F (φ n)) f atTop S) ∧
      (∀ x, ‖f x‖ ≤ M) ∧
      (∀ x y, ‖f x - f y‖ ≤ K * Real.sqrt |x - y|) := by
  let G : ℕ → C(ℝ, ℂ) := fun n => ⟨F n, hF n⟩
  have hc := isCompact_closure_of_sup_sqrt_bound G M K hsup hmod
  obtain ⟨f, _, φ, hφ, hconv⟩ := hc.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hunif : ∀ S : Set ℝ, IsCompact S →
      TendstoUniformlyOn (fun n => F (φ n)) f atTop S :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv
  have hp : ∀ x, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)) := by
    intro x
    exact (hunif {x} isCompact_singleton).tendsto_at (mem_singleton x)
  refine ⟨f, φ, f.continuous, hφ, hunif, ?_, ?_⟩
  · intro x
    exact le_of_tendsto (hp x).norm (Eventually.of_forall (fun n => hsup (φ n) x))
  · intro x y
    exact le_of_tendsto ((hp x).sub (hp y)).norm
      (Eventually.of_forall (fun n => hmod (φ n) x y))

/-- The same actual extraction expressed in the ordinary locally uniform topology. -/
theorem exists_locallyUniform_subsequence_of_sup_sqrt_bound
    (F : ℕ → ℝ → ℂ) (hF : ∀ n, Continuous (F n)) (M K : ℝ)
    (hsup : ∀ n x, ‖F n x‖ ≤ M)
    (hmod : ∀ n x y, ‖F n x - F n y‖ ≤ K * Real.sqrt |x - y|) :
    ∃ (f : ℝ → ℂ) (φ : ℕ → ℕ), Continuous f ∧ StrictMono φ ∧
      TendstoLocallyUniformly (fun n => F (φ n)) f atTop ∧
      (∀ x, ‖f x‖ ≤ M) ∧
      (∀ x y, ‖f x - f y‖ ≤ K * Real.sqrt |x - y|) := by
  obtain ⟨f, φ, hf, hφ, hu, hb, hm⟩ :=
    exists_uniformOnCompacts_subsequence_of_sup_sqrt_bound F hF M K hsup hmod
  exact ⟨f, φ, hf, hφ, tendstoLocallyUniformly_iff_forall_isCompact.mpr hu, hb, hm⟩

end UnforcedLeray.Rayleigh
