import UnforcedLeray.Lib.SobolevB.Mollify
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Smooth fields in `Sob.W` and mollified Sobolev fields (INF11 target S4, helpers)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S4). Manuscript use: smooth approximation of
Sobolev fields (tex 13970–13985, B0892; tex 1238–1243, B0063).

* `hasWeakDeriv_of_contDiff`: classical derivatives of a smooth field are weak derivatives
  (integration by parts, Mathlib `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`);
* `W.ofSmooth`: a smooth field whose derivatives of order `≤ k` lie in `L^p(ρ)` as an element
  of `W`;
* `W.mollify`: the componentwise mollification `x ↦ (x_α ⋆ b̃)_α` of `x ∈ W^{k,p}(ℝⁿ)`
  (weight `1`, `p < ∞`), whose value is smooth (`W.contDiff_mollify`), compactly supported
  when the value of `x` is (`W.hasCompactSupport_mollify`), and which tends to `x` in `W` as the
  bump radius tends to `0` (`W.tendsto_mollify`);
* `W.tendsto_of_deriv`: convergence in `W` is convergence of every component.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiff_iterDD {u : E → F} (hu : ContDiff ℝ ∞ u) (vs : List E) :
    ContDiff ℝ ∞ (iterDD vs u) := by
  induction vs with
  | nil => simpa using hu
  | cons v vs ih => exact (ContDiff.fderiv_right (m := ∞) ih (by simp)).clm_apply contDiff_const

theorem integrable_adm_smul {n : ℕ} {dir : Fin n → E} {φ : E → ℝ}
    (hφ : (wholeSpaceOf E μ dir).Adm φ) {u : E → F} (hu : Continuous u) :
    Integrable (fun x => φ x • u x) μ :=
  (hφ.1.continuous.smul hu).integrable_of_hasCompactSupport (hφ.2.smul_right)

/-- A smooth field has its classical directional derivative as weak derivative. -/
theorem hasWeakDeriv_dir_of_contDiff {n : ℕ} {dir : Fin n → E} {u : E → F}
    (hu : ContDiff ℝ ∞ u) (v : E) :
    HasWeakDeriv (wholeSpaceOf E μ dir) [v] u (fun x => fderiv ℝ u x v) := by
  have hdu : Continuous fun x => fderiv ℝ u x v :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨fun φ hφ => ?_, fun φ hφ => integrable_adm_smul hφ hdu, fun φ hφ => ?_⟩
  · exact integrable_adm_smul ((wholeSpaceOf E μ dir).adm_iterDirDeriv hφ [v]) hu.continuous
  · have h1 : Integrable (fun x => fderiv ℝ φ x v • u x) μ :=
      integrable_adm_smul ((wholeSpaceOf E μ dir).deriv_mem hφ v) hu.continuous
    have h2 : Integrable (fun x => φ x • fderiv ℝ u x v) μ := integrable_adm_smul hφ hdu
    have h3 : Integrable (fun x => φ x • u x) μ := integrable_adm_smul hφ hu.continuous
    have ibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ) (v := v) h1 h2 h3
      (fun x _ => (hφ.1.differentiable (by simp)) x) (fun x _ => (hu.differentiable (by simp)) x)
    simp only [iterDirDeriv_singleton, wholeSpaceOf_μ, List.length_singleton, pow_one, neg_smul,
      one_smul]
    rw [ibp, neg_neg]

/-- **Smooth fields are weakly differentiable**: `∂_{vs} u` (classical) is the weak derivative
of a smooth `u` for every word. -/
theorem hasWeakDeriv_of_contDiff {n : ℕ} {dir : Fin n → E} {u : E → F} (hu : ContDiff ℝ ∞ u)
    (vs : List E) : HasWeakDeriv (wholeSpaceOf E μ dir) vs u (iterDD vs u) := by
  induction vs with
  | nil => exact HasWeakDeriv.nil fun φ hφ => integrable_adm_smul hφ hu.continuous
  | cons v vs ih => exact ih.cons (hasWeakDeriv_dir_of_contDiff (contDiff_iterDD hu vs) v)

end Smooth

section WSmooth

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

instance : CompleteSpace F := completeSpace_of_finiteDimensional 𝕜 F

/-- A smooth field whose derivatives of order `≤ k` lie in `L^p(ρ)`, as an element of `W`. -/
def W.ofSmooth (ρ : Weight (Eucl n)) (u : Eucl n → F) (hu : ContDiff ℝ ∞ u)
    (hmem : ∀ α : Idx n k, MemLp (iterDD ((wholeSpace n).word α) u) p (wμ volume ρ)) :
    W (wholeSpace n) ρ 𝕜 F k p :=
  W.ofFields (fun α => iterDD ((wholeSpace n).word α) u) hmem
    (fun α => hasWeakDeriv_of_contDiff (μ := volume) (dir := e) hu _)

theorem W.coeFn_value_ofSmooth (ρ : Weight (Eucl n)) (u : Eucl n → F) (hu : ContDiff ℝ ∞ u)
    (hmem : ∀ α : Idx n k, MemLp (iterDD ((wholeSpace n).word α) u) p (wμ volume ρ)) :
    ⇑(W.value (wholeSpace n) ρ 𝕜 F k p (W.ofSmooth ρ u hu hmem)) =ᵐ[wμ volume ρ] u :=
  (hmem Idx.zero).coeFn_toLp

/-- **Convergence in `W` is convergence of the components.** -/
theorem W.tendsto_of_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {D : TestDomain E n} {ρ : Weight E}
    {ι : Type*} {l : Filter ι} {y : ι → W D ρ 𝕜 F k p} {x : W D ρ 𝕜 F k p}
    (h : ∀ α, Tendsto (fun i => W.deriv D ρ 𝕜 F k p α (y i)) l
      (𝓝 (W.deriv D ρ 𝕜 F k p α x))) : Tendsto y l (𝓝 x) := by
  rw [tendsto_subtype_rng]
  have h1 : Tendsto (fun i => WithLp.ofLp (y i : SobTuple D ρ F k p)) l
      (𝓝 (WithLp.ofLp (x : SobTuple D ρ F k p))) := tendsto_pi_nhds.mpr h
  have h2 := ((PiLp.continuous_toLp p _).tendsto _).comp h1
  simp only [WithLp.toLp_ofLp] at h2
  exact h2.congr fun i => by simp

/-! ### Mollification on `W` (weight `1`) -/

variable (hp : p ≠ ⊤) (b : ContDiffBump (0 : Eucl n))

theorem memLp_wμ_one_iff {f : Eucl n → F} :
    MemLp f p (wμ volume (1 : Weight (Eucl n))) ↔ MemLp f p volume := by
  rw [wμ_one]

theorem eLpNorm_wμ_one (f : Eucl n → F) (q : ℝ≥0∞) :
    eLpNorm f q (wμ volume (1 : Weight (Eucl n))) = eLpNorm f q volume := by
  rw [wμ_one]

theorem W.memLp_deriv_one (x : W (wholeSpace n) 1 𝕜 F k p) (α : Idx n k) :
    MemLp (W.deriv (wholeSpace n) 1 𝕜 F k p α x) p volume :=
  memLp_wμ_one_iff.mp (Lp.memLp _)

theorem W.locallyIntegrable_deriv (x : W (wholeSpace n) 1 𝕜 F k p) (α : Idx n k) :
    LocallyIntegrable (W.deriv (wholeSpace n) 1 𝕜 F k p α x) volume :=
  (W.memLp_deriv_one x α).locallyIntegrable Fact.out

include hp in
theorem W.memLp_moll_deriv (x : W (wholeSpace n) 1 𝕜 F k p) (α : Idx n k) :
    MemLp (moll b volume (W.deriv (wholeSpace n) 1 𝕜 F k p α x)) p
      (wμ volume (1 : Weight (Eucl n))) := by
  rw [memLp_wμ_one_iff]
  exact memLp_moll b Fact.out hp (W.memLp_deriv_one x α)
    (contDiff_moll b (W.locallyIntegrable_deriv x α)).continuous.aestronglyMeasurable

theorem W.iterDD_moll_value (x : W (wholeSpace n) 1 𝕜 F k p) (α : Idx n k) :
    iterDD ((wholeSpace n).word α)
        (moll b volume (W.deriv (wholeSpace n) 1 𝕜 F k p Idx.zero x)) =
      moll b volume (W.deriv (wholeSpace n) 1 𝕜 F k p α x) :=
  iterDD_cv_of_hasWeakDeriv (W.hasWeakDeriv x α) (b.contDiff_normed)
    (b.hasCompactSupport_normed) (W.locallyIntegrable_deriv x Idx.zero)

/-- The componentwise mollification of `x ∈ W^{k,p}(ℝⁿ)`. -/
def W.mollify (x : W (wholeSpace n) 1 𝕜 F k p) : W (wholeSpace n) 1 𝕜 F k p :=
  W.ofFields (fun α => moll b volume (W.deriv (wholeSpace n) 1 𝕜 F k p α x))
    (W.memLp_moll_deriv hp b x) (fun α => by
      have h := hasWeakDeriv_of_contDiff (μ := volume) (dir := e)
        (contDiff_moll b (W.locallyIntegrable_deriv x Idx.zero)) ((wholeSpace n).word α)
      rw [W.iterDD_moll_value b x α] at h
      exact h)

theorem W.deriv_mollify (x : W (wholeSpace n) 1 𝕜 F k p) (α : Idx n k) :
    W.deriv (wholeSpace n) 1 𝕜 F k p α (W.mollify hp b x) =
      (W.memLp_moll_deriv hp b x α).toLp _ := rfl

theorem W.coeFn_value_mollify (x : W (wholeSpace n) 1 𝕜 F k p) :
    ⇑(W.value (wholeSpace n) 1 𝕜 F k p (W.mollify hp b x)) =ᵐ[volume]
      moll b volume (W.value (wholeSpace n) 1 𝕜 F k p x) :=
  (ae_eq_wμ_iff volume 1).mp (W.memLp_moll_deriv hp b x Idx.zero).coeFn_toLp

theorem W.contDiff_mollify (x : W (wholeSpace n) 1 𝕜 F k p) :
    ContDiff ℝ ∞ (moll b volume (W.value (wholeSpace n) 1 𝕜 F k p x)) :=
  contDiff_moll b (W.locallyIntegrable_deriv x Idx.zero)

theorem W.hasCompactSupport_mollify (x : W (wholeSpace n) 1 𝕜 F k p) {K : Set (Eucl n)}
    (hK : IsCompact K)
    (hxK : ∀ᵐ y ∂volume, y ∉ K → W.value (wholeSpace n) 1 𝕜 F k p x y = 0) :
    HasCompactSupport (moll b volume (W.value (wholeSpace n) 1 𝕜 F k p x)) :=
  hasCompactSupport_cv b.hasCompactSupport_normed hK hxK

omit hp in
/-- **Mollification converges in `W^{k,p}`**, `p < ∞`. -/
theorem W.tendsto_mollify (hp : p ≠ ⊤) {ι : Type*} {l : Filter ι}
    {b : ι → ContDiffBump (0 : Eucl n)} (hb : Tendsto (fun i => (b i).rOut) l (𝓝 0))
    (x : W (wholeSpace n) 1 𝕜 F k p) : Tendsto (fun i => W.mollify hp (b i) x) l (𝓝 x) := by
  refine W.tendsto_of_deriv fun α => ?_
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have h := tendsto_eLpNorm_moll_sub (μ := volume) hp (W.memLp_deriv_one x α) hb
  refine h.congr fun i => ?_
  rw [W.deriv_mollify, ← eLpNorm_wμ_one, eLpNorm_sub_comm]
  refine eLpNorm_congr_ae ?_
  filter_upwards [(W.memLp_moll_deriv hp (b i) x α).coeFn_toLp] with y hy
  exact congrArg (· - _) hy.symm

end WSmooth

end UnforcedLeray.Sob
