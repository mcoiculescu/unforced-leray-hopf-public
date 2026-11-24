import UnforcedLeray.Lib.PhaseSpace.Graph
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Phase tests separate the points of `Y_q` (helper for B0411)

Blueprint unit B0411 (`eq:free-stress-1`, `paper/main.tex` lines 7304–7337). The manuscript
writes `D_(ν,q) = {w ∈ Y_q : νΔw ∈ Y_q, T₀w ∈ Y_q}` with norm
`‖w‖ + ‖νΔw‖ + ‖T₀w‖` (tex 7322–7327). This presupposes that the distributions `νΔw` and
`T₀w`, when they lie in `Y_q`, are *determined* by `w`: an element of `Y_q` is determined by
its pairings with the phase tests. This file proves that fact (planned as
`eq_of_phasePair` in INF25 T25.1 of the scoping note

yet in `Lib/PhaseSpace`):

* `eq_zero_of_forall_phasePair`: if `⟪Φ, f⟫ = 0` for every phase test `Φ`, then `f = 0`.

Proof, valid for every `1 ≤ q ≤ ∞`:
1. Product tests `Φ(τ, y) = e_n(τ) ψ(y) eᵢ`, with `e_n` the Fourier characters of the phase
   circle and `ψ ∈ C_c^∞(ℝ³)`, are phase tests; their pairing with `f` is the spatial pairing
   of `ψ eᵢ` with the `L^q(ℝ³)`-valued Fourier coefficient `∫ e_n(τ) f(τ) dhaar`.
2. Smooth compactly supported functions separate `L^q(ℝ³)` (Mathlib's
   `ae_eq_zero_of_integral_contDiff_smul_eq_zero`), so all Fourier coefficients of `f` vanish.
3. Hence `c ∘ f` has vanishing Fourier coefficients for every `c ∈ L^q(ℝ³)*`. Trigonometric
   polynomials are uniformly dense in `C(ℝ/Pℤ)` (`span_fourier_closure_eq_top`), so
   `∫ φ (c ∘ f) = 0` for continuous `φ`, hence on closed sets, hence `c ∘ f = 0` a.e.
4. `f` is a.e. separably valued, so `f = 0` a.e. (`ae_eq_zero_of_forall_dual_of_isSeparable`).

Status: helper infrastructure for B0411; Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Real

namespace UnforcedLeray.B0411

open UnforcedLeray.PhaseSpace

/-! ### Fourier uniqueness for integrable functions on the phase circle -/

section Circle

variable {P : ℝ} [hP : Fact (0 < P)]

/-- The pairing `φ ↦ ∫ φ h dhaar` of continuous functions on `ℝ/Pℤ` with an integrable `h`. -/
def circlePairing {h : AddCircle P → ℂ} (hh : Integrable h AddCircle.haarAddCircle) :
    C(AddCircle P, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => ∫ τ, φ τ * h τ ∂AddCircle.haarAddCircle
      map_add' := fun φ ψ => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add
          (hh.bdd_mul φ.continuous.aestronglyMeasurable
            (Eventually.of_forall fun τ => φ.norm_coe_le_norm τ))
          (hh.bdd_mul ψ.continuous.aestronglyMeasurable
            (Eventually.of_forall fun τ => ψ.norm_coe_le_norm τ))
      map_smul' := fun c φ => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
    (∫ τ, ‖h τ‖ ∂AddCircle.haarAddCircle) (fun φ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ τ, φ τ * h τ ∂AddCircle.haarAddCircle‖
          ≤ ∫ τ, ‖φ‖ * ‖h τ‖ ∂AddCircle.haarAddCircle :=
            norm_integral_le_of_norm_le (hh.norm.const_mul _)
              (Eventually.of_forall fun τ => by
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm τ) (norm_nonneg _))
        _ = (∫ τ, ‖h τ‖ ∂AddCircle.haarAddCircle) * ‖φ‖ := by
            rw [integral_const_mul]; ring)

theorem circlePairing_apply {h : AddCircle P → ℂ} (hh : Integrable h AddCircle.haarAddCircle)
    (φ : C(AddCircle P, ℂ)) :
    circlePairing hh φ = ∫ τ, φ τ * h τ ∂AddCircle.haarAddCircle := rfl

/-- Vanishing Fourier coefficients give vanishing pairings with all continuous functions. -/
theorem integral_continuous_mul_eq_zero {h : AddCircle P → ℂ}
    (hh : Integrable h AddCircle.haarAddCircle)
    (hf : ∀ n : ℤ, ∫ τ, fourier n τ * h τ ∂AddCircle.haarAddCircle = 0)
    (φ : C(AddCircle P, ℂ)) : ∫ τ, φ τ * h τ ∂AddCircle.haarAddCircle = 0 := by
  have hker : Submodule.span ℂ (range (@fourier P)) ≤
      LinearMap.ker (circlePairing hh : C(AddCircle P, ℂ) →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact hf n
  have hcl : (Submodule.span ℂ (range (@fourier P))).topologicalClosure ≤
      LinearMap.ker (circlePairing hh : C(AddCircle P, ℂ) →ₗ[ℂ] ℂ) :=
    Submodule.topologicalClosure_minimal _ hker (ContinuousLinearMap.isClosed_ker _)
  rw [span_fourier_closure_eq_top] at hcl
  have := hcl (Submodule.mem_top (x := φ))
  rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, circlePairing_apply] at this

/-- **Fourier uniqueness on `L¹(ℝ/Pℤ)`.** An integrable function on the phase circle whose
Fourier coefficients all vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_fourier {h : AddCircle P → ℂ} (hh : Integrable h AddCircle.haarAddCircle)
    (hf : ∀ n : ℤ, ∫ τ, fourier n τ * h τ ∂AddCircle.haarAddCircle = 0) :
    h =ᵐ[AddCircle.haarAddCircle] 0 := by
  refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hh fun s hs => ?_
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  let g : ℕ → C(AddCircle P, ℂ) := fun k =>
    ⟨fun x => ((max 0 (1 - ((k : ℝ) + 1) * infDist x s) : ℝ) : ℂ),
      Complex.continuous_ofReal.comp
        (continuous_const.max (continuous_const.sub
          (continuous_const.mul (continuous_infDist_pt s))))⟩
  have hg : ∀ k x, g k x = ((max 0 (1 - ((k : ℝ) + 1) * infDist x s) : ℝ) : ℂ) :=
    fun _ _ => rfl
  have hlim : Tendsto (fun k => ∫ τ, g k τ * h τ ∂AddCircle.haarAddCircle) atTop
      (𝓝 (∫ τ in s, h τ ∂AddCircle.haarAddCircle)) := by
    rw [← integral_indicator hs.measurableSet]
    refine tendsto_integral_of_dominated_convergence (fun τ => ‖h τ‖)
      (fun k => (g k).continuous.aestronglyMeasurable.mul hh.aestronglyMeasurable) hh.norm
      (fun k => ?_) ?_
    · filter_upwards with τ
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [hg, Complex.norm_real, Real.norm_of_nonneg (le_max_left _ _)]
      refine max_le zero_le_one ?_
      have : 0 ≤ ((k : ℝ) + 1) * infDist τ s := mul_nonneg (by positivity) infDist_nonneg
      linarith
    · filter_upwards with τ
      by_cases hτ : τ ∈ s
      · have h1 : ∀ k, g k τ = 1 := fun k => by
          rw [hg, infDist_zero_of_mem hτ]; simp
        simp only [h1, one_mul, indicator_of_mem hτ]
        exact tendsto_const_nhds
      · rw [indicator_of_notMem hτ]
        have hpos : 0 < infDist τ s := (hs.notMem_iff_infDist_pos hne).1 hτ
        obtain ⟨K, hK⟩ := exists_nat_gt (1 / infDist τ s)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop K] with k hk
        have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
        have h1 : 1 ≤ ((k : ℝ) + 1) * infDist τ s := by
          rw [div_lt_iff₀ hpos] at hK
          nlinarith
        have h2 : g k τ = 0 := by
          rw [hg, max_eq_left (by linarith)]; simp
        rw [h2, zero_mul]
  have h0 : ∀ k, ∫ τ, g k τ * h τ ∂AddCircle.haarAddCircle = 0 := fun k =>
    integral_continuous_mul_eq_zero hh hf (g k)
  simp only [h0] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end Circle

/-! ### Smooth compactly supported functions separate `L^q(ℝ³; ℂ³)` -/

/-- If `∫ ψ(y) gᵢ(y) dy = 0` for all `ψ ∈ C_c^∞(ℝ³; ℝ)` and all components `i`, then
`g = 0` in `L^q(ℝ³; ℂ³)`. -/
theorem lp_eq_zero_of_test {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]
    (g : Lp CVec3 q (volume : Measure Space))
    (h : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ i : Fin 3,
      ∫ y, (ψ y : ℂ) * (g y) i = 0) : g = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hi : ∀ i : Fin 3, ∀ᵐ y ∂(volume : Measure Space), (g y) i = 0 := fun i => by
    have hloc : LocallyIntegrable (fun y => (g y) i) volume :=
      ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).comp_memLp g).locallyIntegrable hq.out
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun ψ hψ hψc => ?_
    simpa [Complex.real_smul] using h ψ hψ hψc i
  filter_upwards [ae_all_iff.2 hi] with y hy
  ext i
  simpa using hy i

/-! ### Product tests -/

/-- The spatial factor `ψ(y) eᵢ`. -/
def spatialTest (ψ : Space → ℝ) (i : Fin 3) : Space → CVec3 :=
  fun y => (ψ y : ℂ) • EuclideanSpace.single i (1 : ℂ)

theorem memLp_spatialTest {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (i : Fin 3) (r : ℝ≥0∞) : MemLp (spatialTest ψ i) r volume := by
  have hc : Continuous (spatialTest ψ i) :=
    (Complex.continuous_ofReal.comp hψ.continuous).smul continuous_const
  have hs : HasCompactSupport (spatialTest ψ i) := by
    have h1 : HasCompactSupport (fun y => (ψ y : ℂ)) := hψc.comp_left Complex.ofReal_zero
    exact h1.smul_right (f' := fun _ => (EuclideanSpace.single i (1 : ℂ) : CVec3))
  exact hc.memLp_of_hasCompactSupport hs

/-- The product test `Φ(τ, y) = e_n(τ) ψ(y) eᵢ`, with `e_n` the `n`-th Fourier character of
`ℝ/Pℤ`. -/
def prodTest (P : ℝ) (n : ℤ) (ψ : Space → ℝ) (i : Fin 3) : ℝ × Space → CVec3 :=
  fun p => (fourier n (p.1 : AddCircle P) * (ψ p.2 : ℂ)) • EuclideanSpace.single i (1 : ℂ)

section Prod

variable {P : ℝ} [hP : Fact (0 < P)]

omit hP in
theorem isPhaseTest_prodTest (n : ℤ) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (i : Fin 3) : IsPhaseTest P (prodTest P n ψ i) where
  smooth := by
    have h1 : (fun p : ℝ × Space => fourier n (p.1 : AddCircle P)) =
        fun p => Complex.exp (2 * π * Complex.I * n * (p.1 : ℂ) / P) := by
      funext p; exact fourier_coe_apply
    have hre : ContDiff ℝ ∞ (fun p : ℝ × Space => ((p.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun p : ℝ × Space => fourier n (p.1 : AddCircle P)) := by
      rw [h1]
      exact Complex.contDiff_exp.comp ((contDiff_const.mul hre).div_const _)
    have h3 : ContDiff ℝ ∞ (fun p : ℝ × Space => (ψ p.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_snd)
    exact (h2.mul h3).smul contDiff_const
  periodic := fun τ y => by simp [prodTest]
  bounded_support := by
    obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun τ y hy => ?_⟩
    have : ψ y = 0 := image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hR hmem
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    simp [prodTest, this]

variable {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

theorem norm_fourier_le (n : ℤ) (τ : AddCircle P) : ‖fourier n τ‖ ≤ 1 := by
  have := (fourier n).norm_coe_le_norm τ
  rwa [fourier_norm] at this

/-- Elements of `Y_q` are Bochner integrable (the phase circle has mass one, `q ≥ 1`). -/
theorem integrable_Yq (f : Yq P q) :
    Integrable (fun τ => f τ) (AddCircle.haarAddCircle (T := P)) :=
  (Lp.memLp f).integrable hq.out

theorem integrable_fourier_smul (f : Yq P q) (n : ℤ) :
    Integrable (fun τ => fourier n τ • f τ) (AddCircle.haarAddCircle (T := P)) := by
  have h := (integrable_Yq f).bdd_smul (φ := fun τ => fourier n τ) 1
    (fourier n).continuous.aestronglyMeasurable
    (Eventually.of_forall fun τ => norm_fourier_le n τ)
  exact h

/-- The spatial pairing with `ψ eᵢ` is the integral of `ψ` against the `i`-th component. -/
theorem innerPair_spatialTest {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (i : Fin 3) (g : Lp CVec3 q (volume : Measure Space)) :
    innerPair q ((memLp_spatialTest hψ hψc i (conjExp q)).toLp _) g =
      ∫ y, (ψ y : ℂ) * (g y) i := by
  rw [innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_spatialTest hψ hψc i (conjExp q))] with y hy
  rw [hy, dotL_apply]
  simp [spatialTest]

omit hP hq in
theorem circleSlice_prodTest (n : ℤ) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (i : Fin 3)
    (hs : IsSliceTest P (conjExp q) (prodTest P n ψ i)) (τ : AddCircle P) :
    circleSlice hs τ = fourier n τ • (memLp_spatialTest hψ hψc i (conjExp q)).toLp _ := by
  induction τ using QuotientAddGroup.induction_on with
  | H t =>
    rw [circleSlice_coe, sliceMap, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Eventually.of_forall fun y => by
      simp only [prodTest, spatialTest, Pi.smul_apply, mul_smul]

/-- The pairing of a product test with `f ∈ Y_q` is the spatial pairing of `ψ eᵢ` with the
`L^q(ℝ³)`-valued Fourier coefficient `∫ e_n(τ) f(τ) dhaar(τ)`. -/
theorem phasePair_prodTest (f : Yq P q) (n : ℤ) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (i : Fin 3) :
    phasePair P q (prodTest P n ψ i) f =
      innerPair q ((memLp_spatialTest hψ hψc i (conjExp q)).toLp _)
        (∫ τ, fourier n τ • f τ ∂AddCircle.haarAddCircle) := by
  have hs := (isPhaseTest_prodTest (P := P) n hψ hψc i).isSliceTest (conjExp q)
  have hint := integrable_fourier_smul f n
  set φL := (memLp_spatialTest hψ hψc i (conjExp q)).toLp _ with hφL
  have h1 : phasePair P q (prodTest P n ψ i) f =
      ∫ τ, innerPair q (testElem P (conjExp q) (prodTest P n ψ i) τ) (f τ)
        ∂AddCircle.haarAddCircle := phasePairing_apply _ _
  have h2 : innerPair q φL (∫ τ, fourier n τ • f τ ∂AddCircle.haarAddCircle) =
      ∫ τ, innerPair q φL (fourier n τ • f τ) ∂AddCircle.haarAddCircle :=
    (ContinuousLinearMap.integral_comp_comm _ hint).symm
  rw [h1, h2]
  refine integral_congr_ae ?_
  have h3 := ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp q) (volume : Measure Space))
    (p := conjExp q) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := P)) (circleSlice hs)
  rw [← testElem_of hs] at h3
  filter_upwards [h3] with τ hτ
  rw [hτ, circleSlice_prodTest n hψ hψc i hs τ, map_smul, map_smul, smul_apply]

/-! ### Separation -/

/-- **Phase tests separate the points of `Y_q`** (INF25 T25.1 `eq_of_phasePair`), for every
`1 ≤ q ≤ ∞`: if `⟪Φ, f⟫ = 0` for all phase tests `Φ`, then `f = 0`. -/
theorem eq_zero_of_forall_phasePair {f : Yq P q}
    (h : ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → phasePair P q Φ f = 0) : f = 0 := by
  have hfi := integrable_Yq f
  have hint := integrable_fourier_smul f
  have hF : ∀ n : ℤ, ∫ τ, fourier n τ • f τ ∂AddCircle.haarAddCircle = 0 := fun n =>
    lp_eq_zero_of_test _ fun ψ hψ hψc i => by
      rw [← innerPair_spatialTest hψ hψc i, ← phasePair_prodTest f n hψ hψc i]
      exact h _ (isPhaseTest_prodTest n hψ hψc i)
  have hdual : ∀ c : StrongDual ℂ (Lp CVec3 q (volume : Measure Space)),
      (fun τ => c (f τ)) =ᵐ[AddCircle.haarAddCircle (T := P)] 0 := by
    intro c
    refine ae_eq_zero_of_fourier (c.integrable_comp hfi) fun n => ?_
    have := c.integral_comp_comm (hint n)
    simp only [map_smul, smul_eq_mul] at this
    rw [this, hF n, map_zero]
  obtain ⟨t, ht, htt⟩ := (Lp.aestronglyMeasurable f).isSeparable_ae_range
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact ae_eq_zero_of_forall_dual_of_isSeparable ℂ ht hdual htt

/-- Two elements of `Y_q` with the same pairings against all phase tests are equal. -/
theorem eq_of_forall_phasePair {f g : Yq P q}
    (h : ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → phasePair P q Φ f = phasePair P q Φ g) :
    f = g :=
  sub_eq_zero.1 (eq_zero_of_forall_phasePair fun Φ hΦ => by rw [map_sub, h Φ hΦ, sub_self])

/-- A distribution in `Y_q` is determined: if `L f = g` and `L f = g'` in distributions, then
`g = g'`. -/
theorem hasPhaseOp_unique {Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3} {f g g' : Yq P q}
    (h : HasPhaseOp Lt f g) (h' : HasPhaseOp Lt f g') : g = g' :=
  eq_of_forall_phasePair fun Φ hΦ => by rw [← h Φ hΦ, ← h' Φ hΦ]

end Prod

end UnforcedLeray.B0411
