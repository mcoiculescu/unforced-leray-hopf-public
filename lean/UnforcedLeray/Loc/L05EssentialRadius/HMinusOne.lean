import UnforcedLeray.Blueprint.Localization.Spaces
import UnforcedLeray.Analysis.LerayProjection.Mollifier.Representative
import UnforcedLeray.Analysis.SobolevEmbedding.H1
import UnforcedLeray.Analysis.Heat.SmoothingBounds
import UnforcedLeray.Analysis.Heat.SelfAdjoint
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# L5: `-𝔓 div 𝕋` is an `H⁻¹` functional, and its heat smoothing

`paper/main.tex` lines 333–336 (blueprint B0714 (b), (c)): "Hence `𝓑_* : X → H^{-1}` is compact,
and `S_0(r)𝓑_* : X → X` is compact for `r > 0`." The blueprint encodes `F = -𝔓 div 𝕋` by
`IsMinusLerayDiv col F` (`Blueprint/Localization/Spaces.lean`): `⟨F, φ⟩ = -⟨𝔓 div 𝕋, φ⟩` for
every smooth compactly supported vector test `φ`. This file extends that bound beyond tests:

* `tendsto_toL2_zero_of_dominated`: dominated convergence in `L²(ℝ³;ℝ³)`;
* `exists_test_approx` (cutoff): a smooth `g` with `g, ∂_j g ∈ L²` is the limit of the tests
  `χ(x/(n+1)) g(x)` in the sense `φₙ → g`, `∂_j φₙ → ∂_j g` in `L²`;
* `abs_inner_H1_le`: `|⟨F, G⟩| ≤ ∑_j ‖𝕋_{·j}‖₂ ‖∂_j G‖₂` for every `G ∈ H¹` (cutoff, then
  mollification of `G`, `SobolevEmbedding.mollification_derivative`);
* `norm_heat_sq_le`: `‖e^{aΔ}F‖₂² ≤ (∑_j ‖𝕋_{·j}‖₂) · C(a) ‖F‖₂` for `a > 0`, from
  `‖e^{aΔ}F‖² = ⟨F, e^{aΔ}e^{aΔ}F⟩` and the `L² → H¹` heat smoothing.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Loc.L05

open UnforcedLeray.Blueprint

/-! ## `L²` norms and dominated convergence -/

theorem norm_sq_eq_integral (F : L2Space) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem norm_toL2_sq {f : SpatialField} (hf : MemLp f 2 volume) :
    ‖toL2 f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae ((coeFn_toL2 hf).mono fun x hx => by simp only [hx])

/-- Dominated convergence in `L²(ℝ³;ℝ³)`. -/
theorem tendsto_toL2_zero_of_dominated {u : ℕ → SpatialField} {G : Space → ℝ}
    (hG : MemLp G 2 volume) (hu : ∀ n, AEStronglyMeasurable (u n) volume)
    (hb : ∀ n, ∀ x, ‖u n x‖ ≤ G x) (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 0)) :
    Tendsto (fun n => toL2 (u n)) atTop (𝓝 0) := by
  have hb' : ∀ n, ∀ᵐ x ∂volume, ‖u n x‖ ≤ ‖G x‖ := fun n =>
    Eventually.of_forall fun x => (hb n x).trans (Real.le_norm_self _)
  have hmem : ∀ n, MemLp (u n) 2 volume := fun n => hG.of_le (hu n) (hb' n)
  have hGint : Integrable (fun x => ‖G x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hG.1).mp hG
  have hint : Tendsto (fun n => ∫ x, ‖u n x‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun x => ‖G x‖ ^ 2)
      (fun n => ((hu n).norm.pow 2 : AEStronglyMeasurable (fun x => ‖u n x‖ ^ 2) volume)) hGint
      (fun n => (hb' n).mono fun x hx => by
        rw [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2)
      (Eventually.of_forall fun x => by simpa using ((hlim x).norm.pow 2))
    simpa using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun n => ‖toL2 (u n)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_toL2_sq (hmem _)] using hint
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt

/-! ## The cutoff -/

/-- A fixed smooth cutoff: `1` on the unit ball, supported in the ball of radius `2`. -/
def cutoffBump : ContDiffBump (0 : Space) where
  rIn := 1
  rOut := 2
  rIn_pos := one_pos
  rIn_lt_rOut := one_lt_two

/-- The scale `1/(n+1)`. -/
def cutoffScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  unfold cutoffScale; positivity

theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  unfold cutoffScale
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_cutoffScale : Tendsto cutoffScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- `χₙ(x) = χ(x/(n+1))`. -/
def cutoffN (n : ℕ) (x : Space) : ℝ := cutoffBump (cutoffScale n • x)

theorem contDiff_cutoffN (n : ℕ) : ContDiff ℝ ∞ (cutoffN n) :=
  cutoffBump.contDiff.comp (contDiff_const_smul _)

theorem hasCompactSupport_cutoffN (n : ℕ) : HasCompactSupport (cutoffN n) :=
  cutoffBump.hasCompactSupport.comp_smul (cutoffScale_pos n).ne'

theorem cutoffN_nonneg (n : ℕ) (x : Space) : 0 ≤ cutoffN n x := cutoffBump.nonneg

theorem cutoffN_le_one (n : ℕ) (x : Space) : cutoffN n x ≤ 1 := cutoffBump.le_one

theorem eventually_cutoffN_eq_one (x : Space) : ∀ᶠ n in atTop, cutoffN n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  apply cutoffBump.one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (cutoffScale_pos n).le]
  change cutoffScale n * ‖x‖ ≤ 1
  unfold cutoffScale
  rw [one_div, inv_mul_le_iff₀ (by positivity), mul_one]
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- A bound for the derivative of the fixed cutoff. -/
theorem exists_fderiv_cutoffBump_le : ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ y, ‖fderiv ℝ cutoffBump y‖ ≤ Cd := by
  obtain ⟨C, hC⟩ := (cutoffBump.contDiff (n := 1).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (cutoffBump.hasCompactSupport.fderiv (𝕜 := ℝ))
  exact ⟨max C 0, le_max_right _ _, fun y => (hC y).trans (le_max_left _ _)⟩

theorem hasFDerivAt_cutoffN (n : ℕ) (x : Space) :
    HasFDerivAt (cutoffN n)
      ((fderiv ℝ cutoffBump (cutoffScale n • x)).comp
        (cutoffScale n • ContinuousLinearMap.id ℝ Space)) x := by
  have hd : DifferentiableAt ℝ cutoffBump (cutoffScale n • x) :=
    (cutoffBump.contDiff (n := 1)).differentiable (by norm_num) _
  have hl : HasFDerivAt (fun y : Space => cutoffScale n • y)
      (cutoffScale n • ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (cutoffScale n)
  exact hd.hasFDerivAt.comp x hl

theorem norm_fderiv_cutoffN_le {Cd : ℝ} (hCd : ∀ y, ‖fderiv ℝ cutoffBump y‖ ≤ Cd) (n : ℕ)
    (x : Space) : ‖fderiv ℝ (cutoffN n) x‖ ≤ Cd * cutoffScale n := by
  rw [(hasFDerivAt_cutoffN n x).fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd 0)
  refine mul_le_mul (hCd _) ?_ (norm_nonneg _) h0
  refine (norm_smul_le (cutoffScale n) (ContinuousLinearMap.id ℝ Space)).trans ?_
  rw [Real.norm_of_nonneg (cutoffScale_pos n).le]
  calc cutoffScale n * ‖ContinuousLinearMap.id ℝ Space‖ ≤ cutoffScale n * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (cutoffScale_pos n).le
    _ = cutoffScale n := mul_one _

theorem norm_coordinateVector (j : Fin 3) : ‖coordinateVector j‖ = 1 := by
  simp [coordinateVector]

/-- The partial derivative of `χₙ g`. -/
theorem testPartial_cutoff {g : Space → Space} (hg : ContDiff ℝ ∞ g) (n : ℕ) (j : Fin 3)
    (x : Space) :
    testPartial (fun y => cutoffN n y • g y) j x =
      cutoffN n x • testPartial g j x + (fderiv ℝ (cutoffN n) x (coordinateVector j)) • g x := by
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  have hcd : DifferentiableAt ℝ (cutoffN n) x := (hasFDerivAt_cutoffN n x).differentiableAt
  have h := hcd.hasFDerivAt.smul hgd.hasFDerivAt
  unfold testPartial
  rw [show (fun y => cutoffN n y • g y) = cutoffN n • g from rfl, h.fderiv]
  simp

/-- **Cutoff approximation.** A smooth field `g` with `g, ∂_j g ∈ L²` is approximated by the
tests `χₙ g`: `χₙ g → g` and `∂_j(χₙ g) → ∂_j g` in `L²`. -/
theorem exists_test_approx {g : Space → Space} (hg : ContDiff ℝ ∞ g) (hg2 : MemLp g 2 volume)
    (hdg : ∀ j, MemLp (testPartial g j) 2 volume) :
    ∃ φ : ℕ → Space → Space, (∀ n, IsVectorTest (φ n)) ∧
      Tendsto (fun n => toL2 (φ n)) atTop (𝓝 (toL2 g)) ∧
      ∀ j, Tendsto (fun n => toL2 (testPartial (φ n) j)) atTop (𝓝 (toL2 (testPartial g j))) := by
  obtain ⟨Cd, hCd0, hCd⟩ := exists_fderiv_cutoffBump_le
  have hgc : Continuous g := hg.continuous
  have hdgc : ∀ j, Continuous (testPartial g j) := fun j =>
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcc : ∀ n, Continuous (cutoffN n) := fun n => (contDiff_cutoffN n).continuous
  have hdcc : ∀ n, Continuous (fun x => fderiv ℝ (cutoffN n) x) := fun n =>
    (contDiff_cutoffN n).continuous_fderiv (by simp)
  refine ⟨fun n y => cutoffN n y • g y, fun n => ⟨(contDiff_cutoffN n).smul hg,
    (hasCompactSupport_cutoffN n).smul_right⟩, ?_, ?_⟩
  · -- the values
    set u : ℕ → SpatialField := fun n x => (cutoffN n x - 1) • g x with hu
    have hconv : Tendsto (fun n => toL2 (u n)) atTop (𝓝 0) := by
      refine tendsto_toL2_zero_of_dominated hg2.norm (fun n => ?_) (fun n x => ?_) (fun x => ?_)
      · exact (((hcc n).sub continuous_const).smul hgc).aestronglyMeasurable
      · simp only [hu, norm_smul, Real.norm_eq_abs]
        have : |cutoffN n x - 1| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [cutoffN_nonneg n x, cutoffN_le_one n x]
        calc |cutoffN n x - 1| * ‖g x‖ ≤ 1 * ‖g x‖ :=
              mul_le_mul_of_nonneg_right this (norm_nonneg _)
          _ = ‖g x‖ := one_mul _
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_cutoffN_eq_one x] with n hn
        simp [hu, hn]
    have hmemu : ∀ n, MemLp (u n) 2 volume := fun n =>
      hg2.norm.of_le (((hcc n).sub continuous_const).smul hgc).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          simp only [hu, norm_smul, Real.norm_eq_abs, abs_norm]
          have : |cutoffN n x - 1| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith [cutoffN_nonneg n x, cutoffN_le_one n x]
          calc |cutoffN n x - 1| * ‖g x‖ ≤ 1 * ‖g x‖ :=
                mul_le_mul_of_nonneg_right this (norm_nonneg _)
            _ = ‖g x‖ := one_mul _)
    have heq : ∀ n, (fun y => cutoffN n y • g y) = u n + g := fun n => by
      funext y
      simp only [hu, Pi.add_apply, sub_smul, one_smul, sub_add_cancel]
    have h2 : Tendsto (fun n => toL2 (u n) + toL2 g) atTop (𝓝 (0 + toL2 g)) :=
      hconv.add tendsto_const_nhds
    rw [zero_add] at h2
    refine h2.congr fun n => ?_
    beta_reduce
    rw [heq n, toL2_of_memLp ((hmemu n).add hg2), toL2_of_memLp (hmemu n), toL2_of_memLp hg2]
    exact ((hmemu n).toLp_add hg2).symm
  · -- the derivatives
    intro j
    set u : ℕ → SpatialField := fun n x => (cutoffN n x - 1) • testPartial g j x +
      (fderiv ℝ (cutoffN n) x (coordinateVector j)) • g x with hu
    have hum : ∀ n, AEStronglyMeasurable (u n) volume := fun n =>
      ((((hcc n).sub continuous_const).smul (hdgc j)).add
        (((hdcc n).clm_apply continuous_const).smul hgc)).aestronglyMeasurable
    have hbd : ∀ n x, ‖u n x‖ ≤ ‖testPartial g j x‖ + Cd * ‖g x‖ := by
      intro n x
      have h1 : |cutoffN n x - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [cutoffN_nonneg n x, cutoffN_le_one n x]
      have h2 : ‖fderiv ℝ (cutoffN n) x (coordinateVector j)‖ ≤ Cd := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_coordinateVector, mul_one]
        refine (norm_fderiv_cutoffN_le hCd n x).trans ?_
        calc Cd * cutoffScale n ≤ Cd * 1 :=
              mul_le_mul_of_nonneg_left (cutoffScale_le_one n) hCd0
          _ = Cd := mul_one _
      simp only [hu]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        calc |cutoffN n x - 1| * ‖testPartial g j x‖ ≤ 1 * ‖testPartial g j x‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = _ := one_mul _
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have hG : MemLp (fun x => ‖testPartial g j x‖ + Cd * ‖g x‖) 2 volume :=
      (hdg j).norm.add (hg2.norm.const_mul Cd)
    have hconv : Tendsto (fun n => toL2 (u n)) atTop (𝓝 0) := by
      refine tendsto_toL2_zero_of_dominated hG hum hbd (fun x => ?_)
      have hA : Tendsto (fun n => (cutoffN n x - 1) • testPartial g j x) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_cutoffN_eq_one x] with n hn
        simp [hn]
      have hB : Tendsto (fun n => (fderiv ℝ (cutoffN n) x (coordinateVector j)) • g x)
          atTop (𝓝 0) := by
        have hs : Tendsto (fun n => fderiv ℝ (cutoffN n) x (coordinateVector j)) atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
            ((tendsto_cutoffScale.const_mul Cd).trans (by rw [mul_zero]))
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          rw [norm_coordinateVector, mul_one]
          exact norm_fderiv_cutoffN_le hCd n x
        simpa using hs.smul_const (g x)
      simpa using hA.add hB
    have hmemu : ∀ n, MemLp (u n) 2 volume := fun n =>
      hG.of_le (hum n) (Eventually.of_forall fun x => (hbd n x).trans (Real.le_norm_self _))
    have heq : ∀ n, testPartial (fun y => cutoffN n y • g y) j = u n + testPartial g j := by
      intro n
      funext x
      rw [testPartial_cutoff hg n j x]
      simp only [hu, Pi.add_apply, sub_smul, one_smul]
      abel
    have h2 : Tendsto (fun n => toL2 (u n) + toL2 (testPartial g j)) atTop
        (𝓝 (0 + toL2 (testPartial g j))) := hconv.add tendsto_const_nhds
    rw [zero_add] at h2
    refine h2.congr fun n => ?_
    beta_reduce
    rw [heq n, toL2_of_memLp ((hmemu n).add (hdg j)), toL2_of_memLp (hmemu n),
      toL2_of_memLp (hdg j)]
    exact ((hmemu n).toLp_add (hdg j)).symm

/-! ## The `H⁻¹` bound -/

/-- On tests: `|⟨F, φ⟩| ≤ ∑_j ‖𝕋_{·j}‖ ‖∂_j φ‖` (the literal pairing, `‖𝔓‖ ≤ 1`). -/
theorem abs_inner_test_le {col : Fin 3 → SpatialField} {F : L2Space}
    (hF : IsMinusLerayDiv col F) {φ : Space → Space} (hφ : IsVectorTest φ) :
    |inner ℝ F (toL2 φ)| ≤ ∑ j, ‖toL2 (col j)‖ * ‖toL2 (testPartial φ j)‖ := by
  rw [hF.2 φ hφ, lerayDivPairing, neg_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (Leray.norm_projection_apply_le _) (norm_nonneg _)

/-- On smooth fields with `g, ∂_j g ∈ L²`, by the cutoff approximation. -/
theorem abs_inner_smooth_le {col : Fin 3 → SpatialField} {F : L2Space}
    (hF : IsMinusLerayDiv col F) {g : Space → Space} (hg : ContDiff ℝ ∞ g)
    (hg2 : MemLp g 2 volume) (hdg : ∀ j, MemLp (testPartial g j) 2 volume) :
    |inner ℝ F (toL2 g)| ≤ ∑ j, ‖toL2 (col j)‖ * ‖toL2 (testPartial g j)‖ := by
  obtain ⟨φ, hφ, h0, h1⟩ := exists_test_approx hg hg2 hdg
  have hl : Tendsto (fun n => |inner ℝ F (toL2 (φ n))|) atTop (𝓝 |inner ℝ F (toL2 g)|) :=
    (tendsto_const_nhds.inner h0).abs
  have hr : Tendsto (fun n => ∑ j, ‖toL2 (col j)‖ * ‖toL2 (testPartial (φ n) j)‖) atTop
      (𝓝 (∑ j, ‖toL2 (col j)‖ * ‖toL2 (testPartial g j)‖)) :=
    tendsto_finsetSum _ fun j _ => (h1 j).norm.const_mul _
  exact le_of_tendsto_of_tendsto' hl hr fun n => abs_inner_test_le hF (hφ n)

/-- **`-𝔓 div 𝕋 ∈ H⁻¹`** (line 334): `|⟨F, G⟩| ≤ ∑_j ‖𝕋_{·j}‖₂ ‖∂_j G‖₂` for every `G ∈ H¹`. -/
theorem abs_inner_H1_le {col : Fin 3 → SpatialField} {F : L2Space}
    (hF : IsMinusLerayDiv col F) (G : SobolevGraph.H1) :
    |inner ℝ F G.value| ≤ ∑ j, ‖toL2 (col j)‖ * ‖G.derivative j‖ := by
  have hval : MemLp (G.value : SpatialField) 2 volume := Lp.memLp _
  have hder : ∀ j, MemLp (G.derivative j : SpatialField) 2 volume := fun j => Lp.memLp _
  have hpart : ∀ (n : ℕ) (j : Fin 3),
      testPartial (SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n)
        (G.value : SpatialField)) j =
      SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n)
        (G.derivative j : SpatialField) := fun n j => funext fun x =>
    SobolevEmbedding.mollification_derivative (G.hasWeakDerivative j) hval _ x
  have hbound : ∀ n : ℕ, |inner ℝ F (toL2 (SobolevEmbedding.mollification
      (SobolevEmbedding.shrinkingMollifier n) (G.value : SpatialField)))| ≤
      ∑ j, ‖toL2 (col j)‖ * ‖G.derivative j‖ := by
    intro n
    refine (abs_inner_smooth_le hF (SobolevEmbedding.mollification_smooth _ _ hval)
      (SobolevEmbedding.mollification_memLp _ _ hval) (fun j => by
        rw [hpart]; exact SobolevEmbedding.mollification_memLp _ _ (hder j))).trans ?_
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [hpart, norm_toL2 (SobolevEmbedding.mollification_memLp _ _ (hder j))]
    refine (SobolevEmbedding.mollification_l2Norm_le _ _ (hder j)).trans_eq ?_
    rw [l2Norm, Lp.norm_def]
  have hlim := Leray.mollification_toL2_tendsto hval
  rw [ViscosityTransport.toL2_coe] at hlim
  exact le_of_tendsto' (tendsto_const_nhds.inner hlim).abs hbound

/-- **Heat smoothing of `-𝔓 div 𝕋`** (lines 334–335): for `a > 0`,
`‖e^{aΔ}F‖₂² ≤ (∑_j ‖𝕋_{·j}‖₂) · h1SmoothingBound(a) · ‖F‖₂`. -/
theorem norm_heat_sq_le {col : Fin 3 → SpatialField} {F : L2Space}
    (hF : IsMinusLerayDiv col F) {a : ℝ} (ha : 0 < a) :
    ‖Heat.heatOperator a F‖ ^ 2 ≤
      (∑ j, ‖toL2 (col j)‖) * (Heat.h1SmoothingBound a * ‖F‖) := by
  have hGval : (Heat.heatToH1 ha (Heat.heatOperator a F)).value =
      Heat.heatOperator a (Heat.heatOperator a F) := by
    show Heat.convolutionOperator (Heat.kernel a) (Heat.kernel_integrable ha)
      (Heat.heatOperator a F) = _
    rw [Heat.heatOperator_pos ha]
  have h1 : ‖Heat.heatOperator a F‖ ^ 2 =
      inner ℝ F (Heat.heatToH1 ha (Heat.heatOperator a F)).value := by
    rw [hGval, ← Heat.heatOperator_inner, real_inner_self_eq_norm_sq]
  rw [h1]
  refine (le_abs_self _).trans ((abs_inner_H1_le hF _).trans ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (SobolevEmbedding.h1_derivative_norm_le _ j).trans ?_
  refine (Heat.norm_heatToH1_apply_le ha _).trans ?_
  exact mul_le_mul_of_nonneg_left (Heat.heatOperator_apply_norm_le a F) (Real.sqrt_nonneg _)

end UnforcedLeray.Loc.L05
