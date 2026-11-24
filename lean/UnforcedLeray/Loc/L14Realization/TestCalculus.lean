import UnforcedLeray.Loc.L10Nonlinear.Pairing
import UnforcedLeray.Analysis.Heat.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Step L14, helpers: calculus of spacetime tests

Support for `Loc/L14Realization.lean` (step L14 `RealizationStep`, `paper/main.tex`
line 561 and `eq:initial-weak-form`, blueprint unit B1032, infrastructure "time cutoff and
passage to the initial time" and "integrability of each pairing on the slab").

For a spacetime test `φ` (`UnforcedLeray.IsSpacetimeTest`):

* the derivative fields `Dt φ = ∂ₜφ`, `Ds φ i = ∂ᵢφ` and `Lap φ = Δₓφ` are smooth with compact
  support and are the literal `timeDerivative`, `spatialDerivative`, `spatialLaplacian` of the
  statement (`timeDerivative_eq_Dt`, `spatialDerivative_coord_eq_Ds`,
  `spatialLaplacian_eq_Lap`);
* every time slice `φ(t,·)` is a vector test (`isVectorTest_slice`);
* the slices are differentiable in `L²`: `d/dt φ(t,·) = ∂ₜφ(t,·)`
  (`hasDerivAt_toL2_slice`), by the mean value inequality and the uniform continuity of
  `∂ₜφ`;
* the weak `H²` Laplacian pairs with tests as `⟨Δ F, φ⟩ = ⟨F, Δφ⟩`
  (`inner_laplace_toL2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L14

open SobolevGraph

/-! ## Derivative fields of a spacetime test -/

/-- `∂ₜφ`. -/
def Dt (φ : SpaceTime → Space) (z : SpaceTime) : Space := fderiv ℝ φ z ((1 : ℝ), (0 : Space))

/-- `∂ᵢφ` (spatial). -/
def Ds (φ : SpaceTime → Space) (i : Fin 3) (z : SpaceTime) : Space :=
  fderiv ℝ φ z ((0 : ℝ), coordinateVector i)

/-- `Δₓφ`. -/
def Lap (φ : SpaceTime → Space) (z : SpaceTime) : Space :=
  ∑ i : Fin 3, fderiv ℝ (Ds φ i) z ((0 : ℝ), coordinateVector i)

theorem contDiff_fderiv_apply' {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) (w : SpaceTime) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ φ z w) :=
  (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_Dt {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Dt φ) :=
  contDiff_fderiv_apply' hφ _

theorem contDiff_Ds {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    ContDiff ℝ ∞ (Ds φ i) :=
  contDiff_fderiv_apply' hφ _

theorem contDiff_Lap {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Lap φ) := by
  unfold Lap
  have h : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z => fderiv ℝ (Ds φ i) z ((0 : ℝ), coordinateVector i)) :=
    fun i => contDiff_fderiv_apply' (contDiff_Ds hφ i) _
  convert ContDiff.sum (s := Finset.univ) (fun i _ => h i) using 1

theorem hasCompactSupport_Dt {φ : SpaceTime → Space} (hφ : HasCompactSupport φ) :
    HasCompactSupport (Dt φ) := hφ.fderiv_apply (𝕜 := ℝ) _

theorem hasCompactSupport_Ds {φ : SpaceTime → Space} (hφ : HasCompactSupport φ) (i : Fin 3) :
    HasCompactSupport (Ds φ i) := hφ.fderiv_apply (𝕜 := ℝ) _

theorem hasCompactSupport_Lap {φ : SpaceTime → Space} (hφ : HasCompactSupport φ) :
    HasCompactSupport (Lap φ) := by
  unfold Lap
  have h : ∀ i : Fin 3, HasCompactSupport
      (fun z => fderiv ℝ (Ds φ i) z ((0 : ℝ), coordinateVector i)) :=
    fun i => (hasCompactSupport_Ds hφ i).fderiv_apply (𝕜 := ℝ) _
  have he : (fun z => ∑ i : Fin 3, fderiv ℝ (Ds φ i) z ((0 : ℝ), coordinateVector i)) =
      ∑ i : Fin 3, fun z => fderiv ℝ (Ds φ i) z ((0 : ℝ), coordinateVector i) := by
    funext z
    simp [Finset.sum_apply]
  rw [he]
  exact HasCompactSupport.finset_sum fun i _ => h i

/-- The time derivative of the statement is `Dt`. -/
theorem timeDerivative_eq_Dt {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (x : Space) :
    timeDerivative φ t x = Dt φ (t, x) := by
  have hf : HasFDerivAt φ (fderiv ℝ φ (t, x)) (t, x) :=
    (hφ.differentiable (by simp) _).hasFDerivAt
  have hc := hf.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  unfold timeDerivative Dt
  rw [show (fun s : ℝ => φ (s, x)) = φ ∘ fun s : ℝ => (s, x) from rfl, hc.fderiv]
  simp

/-- The spatial derivative of the statement is the restriction of `fderiv φ`. -/
theorem spatialDerivative_eq {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (x v : Space) :
    spatialDerivative φ t x v = fderiv ℝ φ (t, x) ((0 : ℝ), v) := by
  have hf : HasFDerivAt φ (fderiv ℝ φ (t, x)) (t, x) :=
    (hφ.differentiable (by simp) _).hasFDerivAt
  have hc := hf.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  unfold spatialDerivative
  rw [show (fun y : Space => φ (t, y)) = φ ∘ fun y : Space => (t, y) from rfl, hc.fderiv]
  simp

theorem spatialDerivative_coord_eq_Ds {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) (t : ℝ)
    (x : Space) (i : Fin 3) :
    spatialDerivative φ t x (coordinateVector i) = Ds φ i (t, x) :=
  spatialDerivative_eq hφ t x _

theorem spatialLaplacian_eq_Lap {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) (t : ℝ)
    (x : Space) : spatialLaplacian φ t x = Lap φ (t, x) := by
  unfold spatialLaplacian Lap
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => spatialDerivative φ t y (coordinateVector i)) = fun y => Ds φ i (t, y) :=
    funext fun y => spatialDerivative_coord_eq_Ds hφ t y i
  rw [h1]
  exact spatialDerivative_eq (contDiff_Ds hφ i) t x _

/-! ## Slices -/

theorem isVectorTest_slice {φ : SpaceTime → Space} (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (t : ℝ) : IsVectorTest (slice φ t) := by
  constructor
  · exact hs.comp (contDiff_const.prodMk contDiff_id)
  · exact hc.comp_isClosedEmbedding
      ⟨isEmbedding_prodMkRight t, (isClosedMap_prodMk_left t).isClosed_range⟩

theorem memLp_slice {φ : SpaceTime → Space} (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (t : ℝ) (p : ℝ≥0∞) : MemLp (slice φ t) p volume :=
  L10.vectorTest_memLp (isVectorTest_slice hs hc t) p

theorem isVectorTest_testPartial {ψ : Space → Space} (hψ : IsVectorTest ψ) (j : Fin 3) :
    IsVectorTest (testPartial ψ j) :=
  ⟨(hψ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    hψ.compact.fderiv_apply (𝕜 := ℝ) _⟩

/-- `toL2` is linear on `L²` functions. -/
theorem toL2_sub_sub_smul {a b d : SpatialField} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume)
    (hd : MemLp d 2 volume) (c : ℝ) :
    toL2 (a - b - c • d) = toL2 a - toL2 b - c • toL2 d := by
  rw [toL2_of_memLp ((ha.sub hb).sub (hd.const_smul c)), toL2_of_memLp ha, toL2_of_memLp hb,
    toL2_of_memLp hd, MemLp.toLp_sub (ha.sub hb) (hd.const_smul c), MemLp.toLp_sub ha hb,
    MemLp.toLp_const_smul c hd]

/-- **`L²` differentiability of test slices**: `d/dt φ(t,·) = ∂ₜφ(t,·)` in `L²`. -/
theorem hasDerivAt_toL2_slice {φ : SpaceTime → Space} (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun s => toL2 (slice φ s)) (toL2 (slice (Dt φ) t)) t := by
  set K : Set Space := Prod.snd '' tsupport φ with hKdef
  have hK : IsCompact K := hc.image continuous_snd
  have hzero : ∀ r x, x ∉ K → φ (r, x) = 0 := fun r x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(r, x), h, rfl⟩)
  have hDzero : ∀ x, x ∉ K → Dt φ (t, x) = 0 := by
    intro x hx
    rw [← timeDerivative_eq_Dt hs]
    unfold timeDerivative
    have : (fun s : ℝ => φ (s, x)) = fun _ => 0 := funext fun s => hzero s x hx
    rw [this]
    simp
  have hderiv : ∀ x r, HasDerivAt (fun s : ℝ => φ (s, x)) (Dt φ (r, x)) r := by
    intro x r
    have hd : DifferentiableAt ℝ (fun s : ℝ => φ (s, x)) r :=
      ((hs.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) r
    have := hd.hasDerivAt
    rwa [show deriv (fun s : ℝ => φ (s, x)) r = timeDerivative φ r x from rfl,
      timeDerivative_eq_Dt hs] at this
  have hUC : UniformContinuous (Dt φ) :=
    (hasCompactSupport_Dt hc).uniformContinuous_of_continuous (contDiff_Dt hs).continuous
  have hDs : ContDiff ℝ ∞ (Dt φ) := contDiff_Dt hs
  have hDc : HasCompactSupport (Dt φ) := hasCompactSupport_Dt hc
  set V : ℝ := ((volume K) ^ (1 / (2 : ℝ≥0∞).toReal)).toReal with hVdef
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsLittleO.of_bound fun c hc0 => ?_
  set ε : ℝ := c / (V + 1) with hεdef
  have hε : 0 < ε := div_pos hc0 (by linarith)
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp hUC ε hε
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs'
  have hst : |s - t| < δ := by rw [← Real.dist_eq]; exact hs'
  set F : SpatialField := slice φ s - slice φ t - (s - t) • slice (Dt φ) t with hFdef
  have hconv : toL2 (slice φ s) - toL2 (slice φ t) - (s - t) • toL2 (slice (Dt φ) t) = toL2 F :=
    (toL2_sub_sub_smul (memLp_slice hs hc s 2) (memLp_slice hs hc t 2)
      (memLp_slice hDs hDc t 2) (s - t)).symm
  have hFm : MemLp F 2 volume :=
    ((memLp_slice hs hc s 2).sub (memLp_slice hs hc t 2)).sub
      ((memLp_slice hDs hDc t 2).const_smul (s - t))
  -- pointwise bound
  have hpt : ∀ x, ‖F x‖ ≤ ‖K.indicator (fun _ => ε * |s - t|) x‖ := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun r => φ (r, x) - (r - t) • Dt φ (t, x))
        (f' := fun r => Dt φ (r, x) - Dt φ (t, x)) (s := uIcc t s) (C := ε)
        (fun r _ => by
          have h1 := hderiv x r
          have h2 : HasDerivAt (fun r : ℝ => (r - t) • Dt φ (t, x)) (Dt φ (t, x)) r := by
            simpa using ((hasDerivAt_id r).sub_const t).smul_const (Dt φ (t, x))
          exact (h1.sub h2).hasDerivWithinAt)
        (fun r hr => by
          have hrt : dist ((r, x) : SpaceTime) (t, x) < δ := by
            rw [Prod.dist_eq, dist_self, Real.dist_eq]
            exact lt_of_le_of_lt (max_le (Set.abs_sub_left_of_mem_uIcc hr) (abs_nonneg _)) hst
          exact (le_of_lt (by rw [← dist_eq_norm]; exact hδε hrt)))
        (convex_uIcc t s) left_mem_uIcc right_mem_uIcc
      have hFx : F x = (φ (s, x) - (s - t) • Dt φ (t, x)) - (φ (t, x) - (t - t) • Dt φ (t, x)) := by
        simp only [hFdef, Pi.sub_apply, Pi.smul_apply, slice, sub_self, zero_smul, sub_zero]
        abel
      rw [hFx, Real.norm_eq_abs] at *
      calc _ ≤ ε * ‖s - t‖ := hmv
        _ = ε * |s - t| := by rw [Real.norm_eq_abs]
    · rw [indicator_of_notMem hx, norm_zero]
      have : F x = 0 := by
        simp only [hFdef, Pi.sub_apply, Pi.smul_apply, slice, hzero s x hx, hzero t x hx,
          hDzero x hx, smul_zero, sub_zero]
      rw [this, norm_zero]
  have hle : eLpNorm F 2 volume ≤ eLpNorm (K.indicator (fun _ => ε * |s - t|)) 2 volume :=
    eLpNorm_mono hpt
  rw [eLpNorm_indicator_const hK.measurableSet (by norm_num) (by norm_num)] at hle
  rw [hconv, norm_toL2 hFm, l2Norm, Real.norm_eq_abs]
  have hfin : (volume K) ^ (1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.measure_lt_top.ne
  have h2 : (eLpNorm F 2 volume).toReal ≤ ε * |s - t| * V := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hfin) hle
    rwa [ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ε * |s - t|)] at this
  calc (eLpNorm F 2 volume).toReal ≤ ε * |s - t| * V := h2
    _ ≤ c * |s - t| := by
      have : ε * V ≤ c := by
        rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      nlinarith [abs_nonneg (s - t)]

/-! ## The weak Laplacian against tests -/

/-- `⟨Δ F, φ⟩ = ⟨F, Δφ⟩` for `F ∈ H²` and a vector test `φ`. -/
theorem inner_laplace_toL2 (F : H2) {ψ : Space → Space} (hψ : IsVectorTest ψ) :
    inner ℝ (H2.laplace F) (toL2 ψ) =
      inner ℝ F.value (toL2 (fun x => ∑ i : Fin 3, testPartial (testPartial ψ i) i x)) := by
  have hmem : ∀ i, MemLp (testPartial (testPartial ψ i) i) 2 volume := fun i =>
    L10.vectorTest_memLp (isVectorTest_testPartial (isVectorTest_testPartial hψ i) i) 2
  have hsum : toL2 (fun x => ∑ i : Fin 3, testPartial (testPartial ψ i) i x) =
      ∑ i : Fin 3, toL2 (testPartial (testPartial ψ i) i) := by
    have he : (fun x => ∑ i : Fin 3, testPartial (testPartial ψ i) i x) =
        testPartial (testPartial ψ 0) 0 + testPartial (testPartial ψ 1) 1 +
          testPartial (testPartial ψ 2) 2 := by
      funext x
      simp [Fin.sum_univ_three]
    rw [he, L10.toL2_add' ((hmem 0).add (hmem 1)) (hmem 2),
      L10.toL2_add' (hmem 0) (hmem 1), Fin.sum_univ_three]
  rw [hsum, inner_sum, H2.laplace_eq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- `⟨∂ᵢ∂ᵢF, ψ⟩ = -⟨∂ᵢF, ∂ᵢψ⟩ = ⟨F, ∂ᵢ∂ᵢψ⟩`
  have h1 := L10.H1_inner_testPartial (L10.h2PartialH1 F i) hψ i
  have h2 := L10.H1_inner_testPartial
    (H1.ofWeakDerivatives F.value (fun j => F.first j) (fun j => F.hasWeakFirst j))
    (isVectorTest_testPartial hψ i) i
  simp only [L10.h2PartialH1, H1.value_ofWeakDerivatives, H1.derivative_ofWeakDerivatives] at h1 h2
  rw [h2, h1, neg_neg]

end UnforcedLeray.Blueprint.L14
