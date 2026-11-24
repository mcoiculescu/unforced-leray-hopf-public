import UnforcedLeray.Short.PartI.Sub.T02_3_8
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Part I, task `PartI:T02/3/8/ModeC2`: the `q`-modes of a `C²` function are `C²` (leaf O1 of `CylinderPoissonBound`)

Source of record: `the November 2 reference manuscript`, lines 276-288 (Fourier modes
in `q` of the pressure).

Target: `CylPoisModeC2` (`Short/PartI/Sub/T02_3_8.lean`): for `c > 0`, `n : ℤ` and a complex `C²`
function `f` on the plane, the `n`-th `q`-mode `η ↦ Cyl.qMode c hc n f η` is `C²`, and its second
`η`-derivative is the mode of `∂_η² f`.

Proof.  By `Cyl.qMode_eq_integral` the mode is the constant `1/c` times the integral over the cell of
the bounded continuous weight `q ↦ fourier (-n) q` (of modulus one) times `f (q, η)`.  Differentiation
under the integral over the compact interval `[-c/2, c/2]` (dominated by the sup of the continuous
function `∂_η f` on a compact box) gives `(qMode f)' = qMode (∂_η f)`.  Applying this to `f` and to
`∂_η f` (which is `C¹` because `f` is `C²`) gives the second derivative.  Continuity of the mode of a
continuous function is the parametric interval integral, and `C²` follows from `contDiff_succ_iff_deriv`
and `contDiff_one_iff_deriv`, as in `Tasks/ClassicalOdd/CylinderPoissonBound/HmeanC2.lean`.

All auxiliary names start with `cpM2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The weight `q ↦ fourier (-n) q` on the centred cell has modulus one. -/
theorem cpM2_norm_weight (c : ℝ) (n : ℤ) (q : ℝ) :
    ‖fourier (-n) (q : AddCircle (c / 2 - -c / 2))‖ = 1 :=
  Circle.norm_coe _

/-- The weight `q ↦ fourier (-n) q` is continuous. -/
theorem cpM2_continuous_weight (c : ℝ) (n : ℤ) :
    Continuous (fun q : ℝ => fourier (-n) (q : AddCircle (c / 2 - -c / 2))) :=
  (fourier (-n)).continuous.comp (AddCircle.continuous_mk' (c / 2 - -c / 2))

/-- Differentiation under the `q`-integral: for a `C¹` function `g` on the plane, the weighted
integral over the centred cell is differentiable in `η`, with derivative the weighted integral of
`∂_η g`. -/
theorem cpM2_hasDerivAt_integral {c : ℝ} (hc : 0 < c) (n : ℤ) {g : Plane → ℂ}
    (hg : ContDiff ℝ 1 g) (e : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ q in (-c / 2)..(c / 2),
        fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • g (q, x))
      (∫ q in (-c / 2)..(c / 2),
        fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • Cyl.partialEta g (q, e)) e := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hGc : Continuous g := hg.continuous
  have h01 : ContDiff ℝ (0 + 1) g := by simpa using hg
  have hpc : Continuous (Cyl.partialEta g) := (Cyl.contDiff_partialEta h01).continuous
  have hw : Continuous (fun q : ℝ => fourier (-n) (q : AddCircle (c / 2 - -c / 2))) :=
    cpM2_continuous_weight c n
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (e - 1) (e + 1) : Set Plane) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hpc.continuousOn
  have hle : -c / 2 ≤ c / 2 := by linarith
  have hnhds : Ioo (e - 1) (e + 1) ∈ 𝓝 e := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeasF : ∀ x : ℝ, Continuous
      (fun q : ℝ => fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • g (q, x)) := fun x =>
    hw.smul (hGc.comp (continuous_id.prodMk continuous_const))
  have hmeasD : Continuous
      (fun q : ℝ => fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • Cyl.partialEta g (q, e)) :=
    hw.smul (hpc.comp (continuous_id.prodMk continuous_const))
  have hbound : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ∈ Set.uIoc (-c / 2) (c / 2) →
      ∀ x ∈ Ioo (e - 1) (e + 1),
        ‖fourier (-n) (t : AddCircle (c / 2 - -c / 2)) • Cyl.partialEta g (t, x)‖ ≤ (fun _ : ℝ => C) t := by
    refine ae_of_all _ fun t ht x hx => ?_
    rw [Set.uIoc_of_le hle] at ht
    rw [norm_smul, cpM2_norm_weight, one_mul]
    exact hC (t, x) ⟨⟨ht.1.le, ht.2⟩, ⟨hx.1.le, hx.2.le⟩⟩
  have hdiff : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ∈ Set.uIoc (-c / 2) (c / 2) →
      ∀ x ∈ Ioo (e - 1) (e + 1),
        HasDerivAt (fun x => fourier (-n) (t : AddCircle (c / 2 - -c / 2)) • g (t, x))
          (fourier (-n) (t : AddCircle (c / 2 - -c / 2)) • Cyl.partialEta g (t, x)) x := by
    refine ae_of_all _ fun t _ x _ => ?_
    exact (Cyl.hasDerivAt_sliceEta hd t x).const_smul
      (fourier (-n) (t : AddCircle (c / 2 - -c / 2)))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun x q => fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • g (q, x))
    (F' := fun x q => fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • Cyl.partialEta g (q, x))
    (x₀ := e) (a := -c / 2) (b := c / 2) (bound := fun _ : ℝ => C) hnhds
    (Filter.Eventually.of_forall fun x => (hmeasF x).aestronglyMeasurable)
    ((hmeasF e).intervalIntegrable _ _)
    hmeasD.aestronglyMeasurable
    hbound
    (continuous_const.intervalIntegrable _ _)
    hdiff
  exact key.2

/-- The `n`-th `q`-mode of a continuous function is continuous in `η`. -/
theorem cpM2_continuous_mode {c : ℝ} (hc : 0 < c) (n : ℤ) {g : Plane → ℂ} (hg : Continuous g) :
    Continuous (fun e : ℝ => Cyl.qMode c hc n g e) := by
  have hw2 : Continuous (fun p : ℝ × ℝ => fourier (-n) (p.2 : AddCircle (c / 2 - -c / 2))) :=
    (cpM2_continuous_weight c n).comp continuous_snd
  have hg2 : Continuous (fun p : ℝ × ℝ => g (p.2, p.1)) :=
    hg.comp (continuous_snd.prodMk continuous_fst)
  have hf : Continuous (fun p : ℝ × ℝ =>
      fourier (-n) (p.2 : AddCircle (c / 2 - -c / 2)) • g (p.2, p.1)) := hw2.smul hg2
  have hint : Continuous (fun e : ℝ => ∫ q in (-c / 2)..(c / 2),
      fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • g (q, e)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun e q => fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • g (q, e)) hf _ _
  have heq : (fun e : ℝ => Cyl.qMode c hc n g e) = fun e =>
      (1 / (c / 2 - -c / 2)) • ∫ q in (-c / 2)..(c / 2),
        fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • g (q, e) :=
    funext fun e => Cyl.qMode_eq_integral hc n g e
  rw [heq]
  exact hint.const_smul (1 / (c / 2 - -c / 2) : ℝ)

/-- The `η`-derivative of the `n`-th `q`-mode of a `C¹` function is the mode of `∂_η`. -/
theorem cpM2_hasDerivAt_mode {c : ℝ} (hc : 0 < c) (n : ℤ) {g : Plane → ℂ}
    (hg : ContDiff ℝ 1 g) (e : ℝ) :
    HasDerivAt (Cyl.qMode c hc n g) (Cyl.qMode c hc n (Cyl.partialEta g) e) e := by
  have heq : Cyl.qMode c hc n g = fun x =>
      (1 / (c / 2 - -c / 2)) • ∫ q in (-c / 2)..(c / 2),
        fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • g (q, x) :=
    funext fun x => Cyl.qMode_eq_integral hc n g x
  have hval : Cyl.qMode c hc n (Cyl.partialEta g) e =
      (1 / (c / 2 - -c / 2)) • ∫ q in (-c / 2)..(c / 2),
        fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • Cyl.partialEta g (q, e) :=
    Cyl.qMode_eq_integral hc n (Cyl.partialEta g) e
  rw [heq, hval]
  exact (cpM2_hasDerivAt_integral hc n hg e).const_smul (1 / (c / 2 - -c / 2) : ℝ)

/-- **Target** `CylPoisModeC2`: the `q`-modes of a `C²` function are `C²` in `η`, and their second
`η`-derivative is the mode of `∂_η² f`. -/
theorem cylPoisModeC2 : CylPoisModeC2 := by
  unfold CylPoisModeC2
  intro c hc n f hf
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have h11 : ContDiff ℝ (1 + 1) f := by rwa [one_add_one_eq_two]
  have hY1 : ContDiff ℝ 1 (Cyl.partialEta f) := Cyl.contDiff_partialEta h11
  have hY0 : ContDiff ℝ (0 + 1) (Cyl.partialEta f) := by simpa using hY1
  have hYY0 : Continuous (Cyl.partialEta (Cyl.partialEta f)) :=
    (Cyl.contDiff_partialEta hY0).continuous
  have hdiffH : Differentiable ℝ (Cyl.qMode c hc n f) := fun e =>
    (cpM2_hasDerivAt_mode hc n hf1 e).differentiableAt
  have hderiv : deriv (Cyl.qMode c hc n f) = Cyl.qMode c hc n (Cyl.partialEta f) :=
    funext fun e => (cpM2_hasDerivAt_mode hc n hf1 e).deriv
  have hdiffY : Differentiable ℝ (Cyl.qMode c hc n (Cyl.partialEta f)) := fun e =>
    (cpM2_hasDerivAt_mode hc n hY1 e).differentiableAt
  have hderivY : deriv (Cyl.qMode c hc n (Cyl.partialEta f)) =
      Cyl.qMode c hc n (Cyl.partialEta (Cyl.partialEta f)) :=
    funext fun e => (cpM2_hasDerivAt_mode hc n hY1 e).deriv
  have hcontY : Continuous (Cyl.qMode c hc n (Cyl.partialEta (Cyl.partialEta f))) :=
    cpM2_continuous_mode hc n hYY0
  have hC1Y : ContDiff ℝ 1 (Cyl.qMode c hc n (Cyl.partialEta f)) :=
    contDiff_one_iff_deriv.2 ⟨hdiffY, by rw [hderivY]; exact hcontY⟩
  have hC2 : ContDiff ℝ (1 + 1) (Cyl.qMode c hc n f) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨hdiffH, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [hderiv]; exact hC1Y
  rw [one_add_one_eq_two] at hC2
  have hsecond : deriv (deriv (Cyl.qMode c hc n f)) =
      Cyl.qMode c hc n (Cyl.partialEta (Cyl.partialEta f)) := by
    rw [hderiv, hderivY]
  exact ⟨hC2, fun η => congrFun hsecond η⟩

end UnforcedLeray.Short.PartI
