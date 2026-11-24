import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice
import UnforcedLeray.Lib.SobolevB.Mollify
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# `PartII-b:S1/2`: `ContRepFDerivLeSumGrad` (`ContRepFDeriv.lean`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2537-2541 and 1515-1531.

For `0 < P ≤ 1`, `ν > 0`, `u : B0411.D P ν q0E` and `g : Fin 3 → B0411.D P ν q0E` with
`HasPhaseOp (fun Φ => -dy j Φ) (u : Yq P q0E) (g j : Yq P q0E)` for all `j : Fin 3`,
`PartIIIb.Concrete.bgContRepGraph` gives continuity of `f := contRep (u : Yq P q0E) τ` and
`gj j := contRep (g j : Yq P q0E) τ`, and `PartIIIb.Concrete.bgContRepWeakSlice` gives
`HasWeakSpatialDerivative j f (gj j)` for each `j : Fin 3`. Using mollification
(`Sob.hasWeakSpatialDerivative_iff`, `Sob.iterDD_cv_of_hasWeakDeriv` in
`UnforcedLeray.Lib.SobolevB.Mollify`) and locally uniform convergence of the mollified derivatives
(`hasFDerivAt_of_tendstoUniformlyOnFilter`), we identify the classical Fréchet derivative of `f`
with `∑ j, (proj j).smulRight (gj j y)` everywhere on `Space`, concluding both `ContDiff ℝ 1 f` and
`‖fderiv ℝ f y‖ ≤ ∑ j : Fin 3, ‖gj j y‖` via `PartIIIb.Concrete.bgCorr_norm_clm_le_sum`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- Normalized bump sequence on `Space = ℝ³` with outer radius `1 / (n + 1)`. -/
def spaceBump (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact (one_div_lt_one_div (by positivity) (by positivity)).2 (by linarith)

theorem tendsto_spaceBump_rOut : Tendsto (fun n : ℕ => (spaceBump n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem moll_eq_normed_conv (n : ℕ) (h : Space → Space) (y : Space) :
    Sob.moll (spaceBump n) volume h y =
      (((spaceBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h : Space → Space) y) := by
  rw [Sob.moll_apply_swap, MeasureTheory.convolution_def]
  rfl

/-- For a continuous field `h : Space → Space`, the mollifications `Sob.moll (spaceBump n) volume h`
converge to `h x₀` along `atTop ×ˢ 𝓝 x₀`. -/
theorem tendsto_moll_prod_nhds {h : Space → Space} (hh : Continuous h) (x₀ : Space) :
    Tendsto (fun p : ℕ × Space => Sob.moll (spaceBump p.1) volume h p.2)
      (atTop ×ˢ 𝓝 x₀) (𝓝 (h x₀)) := by
  have heq : (fun p : ℕ × Space => Sob.moll (spaceBump p.1) volume h p.2) =
      fun p : ℕ × Space =>
        (((spaceBump p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h :
          Space → Space) p.2) := by
    funext p
    exact moll_eq_normed_conv p.1 h p.2
  rw [heq]
  exact ContDiffBump.convolution_tendsto_right
    (φ := fun p : ℕ × Space => spaceBump p.1)
    (g := fun _ : ℕ × Space => h)
    (k := Prod.snd)
    (tendsto_spaceBump_rOut.comp tendsto_fst)
    (Eventually.of_forall fun _ => hh.aestronglyMeasurable)
    ((hh.tendsto x₀).comp tendsto_snd)
    tendsto_snd

/-- Pointwise convergence of `Sob.moll (spaceBump n) volume h y` to `h y` for continuous `h`. -/
theorem tendsto_moll_pointwise {h : Space → Space} (hh : Continuous h) (y : Space) :
    Tendsto (fun n : ℕ => Sob.moll (spaceBump n) volume h y) atTop (𝓝 (h y)) := by
  have heq : (fun n : ℕ => Sob.moll (spaceBump n) volume h y) =
      fun n : ℕ =>
        (((spaceBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h :
          Space → Space) y) := by
    funext n
    exact moll_eq_normed_conv n h y
  rw [heq]
  exact ContDiffBump.convolution_tendsto_right_of_continuous tendsto_spaceBump_rOut hh y

/-- Candidate Fréchet derivative assembled from partial derivative fields `gj : Fin 3 → Space → Space`. -/
def clmOfGrad (gj : Fin 3 → Space → Space) (y : Space) : Space →L[ℝ] Space :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (gj j y)

@[simp]
theorem clmOfGrad_apply_coordinateVector (gj : Fin 3 → Space → Space) (y : Space) (i : Fin 3) :
    clmOfGrad gj y (UnforcedLeray.coordinateVector i) = gj i y := by
  simp only [clmOfGrad, sum_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.proj, PiLp.proj_apply, UnforcedLeray.coordinateVector,
    EuclideanSpace.single, PiLp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem continuous_clmOfGrad {gj : Fin 3 → Space → Space} (hgj : ∀ j : Fin 3, Continuous (gj j)) :
    Continuous (clmOfGrad gj) := by
  unfold clmOfGrad
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((ContinuousLinearMap.smulRightL ℝ Space Space
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ)).continuous).comp (hgj j)

/-- If `f : Space → Space` is continuous and has continuous weak partial derivatives
`gj j : Space → Space` for all `j : Fin 3`, then `f` has classical Fréchet derivative
`clmOfGrad gj x` at every `x : Space`. -/
theorem hasFDerivAt_of_continuous_weakGrad {f : Space → Space} {gj : Fin 3 → Space → Space}
    (hf : Continuous f) (hgj : ∀ j : Fin 3, Continuous (gj j))
    (hw : ∀ j : Fin 3, UnforcedLeray.HasWeakSpatialDerivative j f (gj j)) (x : Space) :
    HasFDerivAt f (clmOfGrad gj x) x := by
  have hfloc : LocallyIntegrable f volume := hf.locallyIntegrable
  let fn : ℕ → Space → Space := fun n => Sob.moll (spaceBump n) volume f
  let fn' : ℕ → Space → Space →L[ℝ] Space := fun n y => fderiv ℝ (fn n) y
  have hfn_smooth : ∀ n : ℕ, ContDiff ℝ ∞ (fn n) := fun n =>
    Sob.contDiff_moll (spaceBump n) hfloc
  have hfn_fderiv : ∀ (n : ℕ) (y : Space) (j : Fin 3),
      fn' n y (UnforcedLeray.coordinateVector j) = Sob.moll (spaceBump n) volume (gj j) y := by
    intro n y j
    have hw' : Sob.HasWeakDeriv (Sob.wholeSpace 3) [Sob.e j] f (gj j) :=
      Sob.hasWeakSpatialDerivative_iff.mp (hw j)
    have hid := Sob.iterDD_cv_of_hasWeakDeriv hw'
      ((spaceBump n).contDiff_normed (μ := volume))
      ((spaceBump n).hasCompactSupport_normed (μ := volume)) hfloc
    exact congrFun hid y
  have hunif : TendstoUniformlyOnFilter fn' (clmOfGrad gj) atTop (𝓝 x) := by
    rw [Metric.tendstoUniformlyOnFilter_iff]
    intro ε hε
    have hdiff_tendsto : ∀ j : Fin 3,
        Tendsto (fun p : ℕ × Space => ‖gj j p.2 - Sob.moll (spaceBump p.1) volume (gj j) p.2‖)
          (atTop ×ˢ 𝓝 x) (𝓝 0) := by
      intro j
      have h1 : Tendsto (fun p : ℕ × Space => gj j p.2) (atTop ×ˢ 𝓝 x) (𝓝 (gj j x)) :=
        ((hgj j).tendsto x).comp tendsto_snd
      have h2 : Tendsto (fun p : ℕ × Space => Sob.moll (spaceBump p.1) volume (gj j) p.2)
          (atTop ×ˢ 𝓝 x) (𝓝 (gj j x)) :=
        tendsto_moll_prod_nhds (hgj j) x
      simpa [sub_self] using (h1.sub h2).norm
    have hsum_tendsto :
        Tendsto (fun p : ℕ × Space =>
          ∑ j : Fin 3, ‖gj j p.2 - Sob.moll (spaceBump p.1) volume (gj j) p.2‖)
          (atTop ×ˢ 𝓝 x) (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun j _ => hdiff_tendsto j
    have hev := hsum_tendsto.eventually (gt_mem_nhds hε)
    filter_upwards [hev] with p hp
    rw [dist_eq_norm]
    have hle : ‖clmOfGrad gj p.2 - fn' p.1 p.2‖ ≤
        ∑ j : Fin 3, ‖gj j p.2 - Sob.moll (spaceBump p.1) volume (gj j) p.2‖ := by
      refine (UnforcedLeray.Short.PartIIIb.Concrete.bgCorr_norm_clm_le_sum
        (clmOfGrad gj p.2 - fn' p.1 p.2)).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_apply, clmOfGrad_apply_coordinateVector, hfn_fderiv]
    exact hle.trans_lt hp
  have hfn_has : ∀ᶠ p : ℕ × Space in atTop ×ˢ 𝓝 x, HasFDerivAt (fn p.1) (fn' p.1 p.2) p.2 :=
    Eventually.of_forall fun p => ((hfn_smooth p.1).differentiable (by simp) p.2).hasFDerivAt
  have hfn_pt : ∀ᶠ y : Space in 𝓝 x, Tendsto (fun n : ℕ => fn n y) atTop (𝓝 (f y)) :=
    Eventually.of_forall fun y => tendsto_moll_pointwise hf y
  exact hasFDerivAt_of_tendstoUniformlyOnFilter hunif hfn_has hfn_pt

theorem fderiv_eq_clmOfGrad_of_continuous_weakGrad {f : Space → Space}
    {gj : Fin 3 → Space → Space} (hf : Continuous f) (hgj : ∀ j : Fin 3, Continuous (gj j))
    (hw : ∀ j : Fin 3, UnforcedLeray.HasWeakSpatialDerivative j f (gj j)) (y : Space) :
    fderiv ℝ f y = clmOfGrad gj y :=
  (hasFDerivAt_of_continuous_weakGrad hf hgj hw y).fderiv

theorem fderiv_apply_coordinateVector_of_continuous_weakGrad {f : Space → Space}
    {gj : Fin 3 → Space → Space} (hf : Continuous f) (hgj : ∀ j : Fin 3, Continuous (gj j))
    (hw : ∀ j : Fin 3, UnforcedLeray.HasWeakSpatialDerivative j f (gj j)) (y : Space) (j : Fin 3) :
    fderiv ℝ f y (UnforcedLeray.coordinateVector j) = gj j y := by
  rw [fderiv_eq_clmOfGrad_of_continuous_weakGrad hf hgj hw y, clmOfGrad_apply_coordinateVector]

theorem contDiff_one_of_continuous_weakGrad {f : Space → Space} {gj : Fin 3 → Space → Space}
    (hf : Continuous f) (hgj : ∀ j : Fin 3, Continuous (gj j))
    (hw : ∀ j : Fin 3, UnforcedLeray.HasWeakSpatialDerivative j f (gj j)) :
    ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_of_continuous_weakGrad hf hgj hw x).differentiableAt, ?_⟩
  have heq : fderiv ℝ f = clmOfGrad gj :=
    funext fun y => fderiv_eq_clmOfGrad_of_continuous_weakGrad hf hgj hw y
  rw [heq]
  exact continuous_clmOfGrad hgj

theorem norm_fderiv_le_sum_of_continuous_weakGrad {f : Space → Space} {gj : Fin 3 → Space → Space}
    (hf : Continuous f) (hgj : ∀ j : Fin 3, Continuous (gj j))
    (hw : ∀ j : Fin 3, UnforcedLeray.HasWeakSpatialDerivative j f (gj j)) (y : Space) :
    ‖fderiv ℝ f y‖ ≤ ∑ j : Fin 3, ‖gj j y‖ := by
  refine (UnforcedLeray.Short.PartIIIb.Concrete.bgCorr_norm_clm_le_sum (fderiv ℝ f y)).trans
    (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_apply_coordinateVector_of_continuous_weakGrad hf hgj hw y j]

/-- **`PartII-b:S1/2` (`contRepFDerivLeSumGrad_proof`)**
(`the November 2 reference manuscript`,
lines 2537-2541 and 1515-1531). -/
theorem contRepFDerivLeSumGrad_proof : UnforcedLeray.Short.IIb.ContRepFDerivLeSumGrad := by
  intro P _ hP1 ν hν u g hop τ y
  let f : Space → Space := contRep (u : Yq P q0E) τ
  let gj : Fin 3 → Space → Space := fun j => contRep (g j : Yq P q0E) τ
  have hf : Continuous f :=
    (UnforcedLeray.Short.PartIIIb.Concrete.bgContRepGraph P hP1 ν hν u).1.comp
      (Continuous.prodMk_right τ)
  have hgj : ∀ j : Fin 3, Continuous (gj j) := fun j =>
    (UnforcedLeray.Short.PartIIIb.Concrete.bgContRepGraph P hP1 ν hν (g j)).1.comp
      (Continuous.prodMk_right τ)
  have hw : ∀ j : Fin 3, UnforcedLeray.HasWeakSpatialDerivative j f (gj j) := fun j =>
    UnforcedLeray.Short.PartIIIb.Concrete.bgContRepWeakSlice P hP1 ν hν u (g j) j (hop j) τ
  exact norm_fderiv_le_sum_of_continuous_weakGrad hf hgj hw y

end UnforcedLeray.Short.IIb

end
