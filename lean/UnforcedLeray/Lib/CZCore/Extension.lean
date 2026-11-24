import UnforcedLeray.Lib.CZCore.Density
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Extension from `L² ∩ L^p` to `L^p`, and consistency in `p` (INF01 T12, generic part)


target T12 (`extendLp`, `extendLp_consistent`). The Calderón–Zygmund bound is proved on
`L² ∩ L^p`; this file turns any such bound into a bounded operator on `L^p` (blueprint unit
B0414, `paper/main.tex` lines 7336–7344: "bounded on `L^q` for `1 < q < ∞`").

On a finite-dimensional space with an additive Haar measure, for `1 ≤ p < ∞` and an operator
`T` on `L²` with `‖T f‖_p ≤ C ‖f‖_p` on `L² ∩ L^p`:

* `lpTwo p`: the subspace `L^p ∩ L²` of `L^p`, dense (`dense_lpTwo`);
* `extendOfBound T p C hC : Lp ℝ p μ →L[ℝ] Lp ℝ p μ`: the extension by continuity
  (`ContinuousLinearMap.extend` along the inclusion of `lpTwo p`);
* `extendOfBound_toLp`: on `f ∈ L² ∩ L^p` it agrees a.e. with `T f`;
* `extendOfBound_consistent`: for `f ∈ L^p ∩ L^q` the `L^p` and `L^q` extensions agree a.e.
  (simultaneous approximation by continuous compactly supported functions, and uniqueness of
  limits in measure).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.CZ

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Operator bound in `eLpNorm` form, for a bounded operator on `L^p`. -/
theorem eLpNorm_apply_le_of_Lp {p : ℝ≥0∞} [Fact (1 ≤ p)] (A : Lp ℝ p μ →L[ℝ] Lp ℝ p μ)
    (u : Lp ℝ p μ) : eLpNorm (A u) p μ ≤ ‖A‖₊ * eLpNorm u p μ := by
  rw [← Lp.enorm_def, ← Lp.enorm_def, enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact_mod_cast A.le_opNNNorm u

variable (μ) in
/-- `L^p ∩ L²` as a subspace of `L^p`. -/
def lpTwo (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (Lp ℝ p μ) where
  carrier := {u | MemLp u 2 μ}
  add_mem' {u v} hu hv := (MemLp.add hu hv).ae_eq (Lp.coeFn_add u v).symm
  zero_mem' := (MemLp.zero : MemLp (0 : E → ℝ) 2 μ).ae_eq (Lp.coeFn_zero ℝ p μ).symm
  smul_mem' c u hu := (MemLp.const_smul hu c).ae_eq (Lp.coeFn_smul c u).symm

/-- `L^p ∩ L²` is dense in `L^p` for `p < ∞`. -/
theorem dense_lpTwo {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense (lpTwo μ p : Set (Lp ℝ p μ)) := by
  refine Metric.dense_iff.2 fun u r hr => ?_
  obtain ⟨g, hgs, hgu, hgc, hgp⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ENNReal.ofReal_pos.2 (half_pos hr)).ne'
  refine ⟨hgp.toLp g, ?_, (hgc.memLp_of_hasCompactSupport hgs).ae_eq hgp.coeFn_toLp.symm⟩
  rw [Metric.mem_ball, dist_comm, Lp.dist_def]
  have h1 : (u : E → ℝ) - ⇑(hgp.toLp g) =ᵐ[μ] (u : E → ℝ) - g := by
    filter_upwards [hgp.coeFn_toLp] with x hx
    simp [hx]
  rw [eLpNorm_congr_ae h1]
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgu
  rw [ENNReal.toReal_ofReal (half_pos hr).le] at h2
  linarith

section Restrict

variable (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (C : ℝ≥0)
  (hC : ∀ f : Lp ℝ 2 μ, MemLp f p μ → eLpNorm (T f) p μ ≤ C * eLpNorm f p μ)

/-- The `L²` element of `u ∈ L^p ∩ L²`. -/
def lpTwoToL2 (u : lpTwo μ p) : Lp ℝ 2 μ :=
  (show MemLp ((u : Lp ℝ p μ) : E → ℝ) 2 μ from u.2).toLp _

theorem coeFn_lpTwoToL2 (u : lpTwo μ p) :
    (lpTwoToL2 p u : E → ℝ) =ᵐ[μ] ((u : Lp ℝ p μ) : E → ℝ) :=
  MemLp.coeFn_toLp _

theorem memLp_lpTwoToL2 (u : lpTwo μ p) : MemLp (lpTwoToL2 p u) p μ :=
  (Lp.memLp (u : Lp ℝ p μ)).ae_eq (coeFn_lpTwoToL2 p u).symm

theorem lpTwoToL2_add (u v : lpTwo μ p) :
    lpTwoToL2 p (u + v) = lpTwoToL2 p u + lpTwoToL2 p v := by
  unfold lpTwoToL2
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Lp.coeFn_add (u : Lp ℝ p μ) v)

theorem lpTwoToL2_smul (c : ℝ) (u : lpTwo μ p) : lpTwoToL2 p (c • u) = c • lpTwoToL2 p u := by
  unfold lpTwoToL2
  rw [← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _ (Lp.coeFn_smul c (u : Lp ℝ p μ))

include hC in
theorem memLp_apply_lpTwoToL2 (u : lpTwo μ p) : MemLp (T (lpTwoToL2 p u)) p μ :=
  ⟨Lp.aestronglyMeasurable _, (hC _ (memLp_lpTwoToL2 p u)).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (memLp_lpTwoToL2 p u).2)⟩

/-- `T` as a linear map `L^p ∩ L² → L^p`. -/
def restrictLin : lpTwo μ p →ₗ[ℝ] Lp ℝ p μ where
  toFun u := (memLp_apply_lpTwoToL2 T p C hC u).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    rw [lpTwoToL2_add, map_add]
    exact Lp.coeFn_add _ _
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    rw [lpTwoToL2_smul, map_smul]
    exact Lp.coeFn_smul _ _

theorem norm_restrictLin_le (u : lpTwo μ p) : ‖restrictLin T p C hC u‖ ≤ C * ‖u‖ := by
  change ‖(memLp_apply_lpTwoToL2 T p C hC u).toLp _‖ ≤ C * ‖(u : Lp ℝ p μ)‖
  rw [Lp.norm_toLp, Lp.norm_def]
  have h1 : eLpNorm (lpTwoToL2 p u) p μ = eLpNorm (u : Lp ℝ p μ) p μ :=
    eLpNorm_congr_ae (coeFn_lpTwoToL2 p u)
  have h2 := hC _ (memLp_lpTwoToL2 p u)
  rw [h1] at h2
  calc (eLpNorm (T (lpTwoToL2 p u)) p μ).toReal
      ≤ ((C : ℝ≥0∞) * eLpNorm (u : Lp ℝ p μ) p μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top _)) h2
    _ = C * (eLpNorm (u : Lp ℝ p μ) p μ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal]

/-- `T` as a bounded operator `L^p ∩ L² → L^p`. -/
def restrictCLM : lpTwo μ p →L[ℝ] Lp ℝ p μ :=
  (restrictLin T p C hC).mkContinuous C (norm_restrictLin_le T p C hC)

/-- **Extension by continuity** of an operator bounded in the `L^p` norm on `L² ∩ L^p`. -/
def extendOfBound : Lp ℝ p μ →L[ℝ] Lp ℝ p μ :=
  (restrictCLM T p C hC).extend (lpTwo μ p).subtypeL

theorem extendOfBound_coe (hp : p ≠ ⊤) (u : lpTwo μ p) :
    extendOfBound T p C hC (u : Lp ℝ p μ) = restrictCLM T p C hC u := by
  have hdense : DenseRange (lpTwo μ p).subtypeL := by
    rw [DenseRange, Submodule.coe_subtypeL, Submodule.coe_subtype, Subtype.range_coe]
    exact dense_lpTwo hp
  have hunif : IsUniformInducing (lpTwo μ p).subtypeL := by
    rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
    exact isUniformEmbedding_subtype_val.isUniformInducing
  exact ContinuousLinearMap.extend_eq _ hdense hunif u

/-- On `L² ∩ L^p` the extension agrees a.e. with `T`. -/
theorem extendOfBound_toLp (hp : p ≠ ⊤) {f : E → ℝ} (hf2 : MemLp f 2 μ) (hfp : MemLp f p μ) :
    ⇑(extendOfBound T p C hC (hfp.toLp f)) =ᵐ[μ] ⇑(T (hf2.toLp f)) := by
  set u : lpTwo μ p := ⟨hfp.toLp f, hf2.ae_eq hfp.coeFn_toLp.symm⟩
  have h1 : extendOfBound T p C hC (hfp.toLp f) = restrictCLM T p C hC u :=
    extendOfBound_coe T p C hC hp u
  have h2 : lpTwoToL2 p u = hf2.toLp f := MemLp.toLp_congr _ _ hfp.coeFn_toLp
  rw [h1]
  change ⇑((memLp_apply_lpTwoToL2 T p C hC u).toLp _) =ᵐ[μ] _
  rw [← h2]
  exact MemLp.coeFn_toLp _

/-- The same, for `f` given as an element of `L²`. -/
theorem extendOfBound_apply (hp : p ≠ ⊤) (f : Lp ℝ 2 μ) (hfp : MemLp f p μ) :
    ⇑(extendOfBound T p C hC (hfp.toLp f)) =ᵐ[μ] ⇑(T f) := by
  have := extendOfBound_toLp T p C hC hp (Lp.memLp f) hfp
  rwa [Lp.toLp_coeFn] at this

end Restrict

/-- **Consistency in the exponent.** For `f ∈ L^p ∩ L^q` the extensions at `p` and `q` agree
almost everywhere. -/
theorem extendOfBound_consistent (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hq : q ≠ ⊤) {Cp Cq : ℝ≥0}
    (hCp : ∀ f : Lp ℝ 2 μ, MemLp f p μ → eLpNorm (T f) p μ ≤ Cp * eLpNorm f p μ)
    (hCq : ∀ f : Lp ℝ 2 μ, MemLp f q μ → eLpNorm (T f) q μ ≤ Cq * eLpNorm f q μ)
    {f : E → ℝ} (hfp : MemLp f p μ) (hfq : MemLp f q μ) :
    ⇑(extendOfBound T p Cp hCp (hfp.toLp f)) =ᵐ[μ] ⇑(extendOfBound T q Cq hCq (hfq.toLp f)) := by
  have hp1 : 1 ≤ p := Fact.out
  have hq1 : 1 ≤ q := Fact.out
  set Ep := extendOfBound T p Cp hCp
  set Eq := extendOfBound T q Cq hCq
  have hex : ∀ n : ℕ, ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) p μ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
      eLpNorm (f - g) q μ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    exists_continuous_eLpNorm_sub_le_two hp1 hq1 hp hq hfp hfq
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
  choose g hgc hgs hgp hgq using hex
  have hgP : ∀ n, MemLp (g n) p μ := fun n => (hgc n).memLp_of_hasCompactSupport (hgs n)
  have hgQ : ∀ n, MemLp (g n) q μ := fun n => (hgc n).memLp_of_hasCompactSupport (hgs n)
  have hg2 : ∀ n, MemLp (g n) 2 μ := fun n => (hgc n).memLp_of_hasCompactSupport (hgs n)
  have hbound : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [ENNReal.ofReal_zero] at this
  -- convergence of the images, in each exponent
  have hconv : ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (A : Lp ℝ r μ →L[ℝ] Lp ℝ r μ) (hfr : MemLp f r μ)
      (hgr : ∀ n, MemLp (g n) r μ),
      (∀ n, eLpNorm (f - g n) r μ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))) →
      TendstoInMeasure μ (fun n => ⇑(A ((hgr n).toLp (g n)))) atTop ⇑(A (hfr.toLp f)) := by
    intro r _ A hfr hgr hgn
    have hr0 : r ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ r)).ne'
    refine tendstoInMeasure_of_tendsto_eLpNorm hr0 (fun n => Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _) ?_
    have hle : ∀ n, eLpNorm (⇑(A ((hgr n).toLp (g n))) - ⇑(A (hfr.toLp f))) r μ ≤
        ‖A‖₊ * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      intro n
      have h1 : ⇑(A ((hgr n).toLp (g n))) - ⇑(A (hfr.toLp f)) =ᵐ[μ]
          ⇑(A ((hgr n).toLp (g n) - hfr.toLp f)) := by
        rw [map_sub]; exact (Lp.coeFn_sub _ _).symm
      rw [eLpNorm_congr_ae h1]
      refine (eLpNorm_apply_le_of_Lp A _).trans ?_
      gcongr
      have h2 : ⇑((hgr n).toLp (g n) - hfr.toLp f) =ᵐ[μ] g n - f := by
        filter_upwards [Lp.coeFn_sub ((hgr n).toLp (g n)) (hfr.toLp f), (hgr n).coeFn_toLp,
          hfr.coeFn_toLp] with x h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
      rw [eLpNorm_congr_ae h2, eLpNorm_sub_comm]
      exact hgn n
    have hlim : Tendsto (fun n : ℕ => (‖A‖₊ : ℝ≥0∞) * ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop
        (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hbound (Or.inr ENNReal.coe_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hle
  have hP := hconv p Ep hfp hgP hgp
  have hQ := hconv q Eq hfq hgQ hgq
  have hPQ : ∀ n, ⇑(Ep ((hgP n).toLp (g n))) =ᵐ[μ] ⇑(Eq ((hgQ n).toLp (g n))) := fun n =>
    (extendOfBound_toLp T p Cp hCp hp (hg2 n) (hgP n)).trans
      (extendOfBound_toLp T q Cq hCq hq (hg2 n) (hgQ n)).symm
  exact tendstoInMeasure_ae_unique hP (hQ.congr_left fun n => (hPQ n).symm)

end UnforcedLeray.CZ
