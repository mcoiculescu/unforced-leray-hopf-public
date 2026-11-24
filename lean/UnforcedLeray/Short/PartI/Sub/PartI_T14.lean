import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.OverlapRescaling

/-!
# Part I, task `PartI:T14`: the overlap-rescaled mean primitive `𝖲` (decomposition)

Source of record: `the November 2 reference manuscript`, lines 395-425.

With `S = meanStream tr` (`\bar ψ`) and overlap variables `s = s_c + c² T / ν`, `η = c Y`,
the rescaled primitive `𝖲(T, Y) = c² S(s_c + c² T / ν, c Y)` (`overlapMeanStream`) satisfies:
1. `ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => overlapMeanStream tr x.1 x.2) (Ici 0 ×ˢ univ)` for `c > 1`;
2. `(hmean 1 (overlapField ν c tr.v T) Y) 1 = 0` (`\bar U₂ = 0`);
3. `b(T, Y) := (hmean 1 (overlapField ν c tr.v T) Y) 0 = -∂_Y 𝖲(T, Y)` (`b = -𝖲_Y`);
4. `∂_T 𝖲(T, Y) - ∂_Y² 𝖲(T, Y) = e_c hmean 1 (fun y => W(T, y)₀ * W(T, y)₁) Y`
   where `W(T) = hfluct 1 (overlapField ν c tr.v T)` (`𝖲_T - 𝖲_{YY} = e_c \overline{W₁ W₂}`);
5. `hmean c (fun z => Vc ν c s z 0 * Vc ν c s z 1) η = 0` (`\overline{(V_c^p)₁ (V_c^p)₂} = 0`,
   from horizontal reflection symmetry `q ↦ -q`);
6. `eLpNorm (overlapMeanStream tr 0) 1 volume = ENNReal.ofReal c * eLpNorm (meanStream tr s_c) 1 volume`,
   reducing `‖𝖲(0)‖_{L¹_Y} ≤ C` (`overlap_mean_primitive_of`) to the pre-overlap `L¹_η` bound
   `MeanStreamAtOverlapL1Bound` (`‖S(s_c)‖_{L¹_η} ≤ C c⁻¹`).
7. The isolated-vortex mean stream `vortexMeanStream ν c s η = -(8π c⁻¹) G_{1 + νs}(η)` has
   `‖vortexMeanStream ν c s‖_{L¹_η} = 8π c⁻¹` (`eLpNorm_vortexMeanStream_le`), so
   `MeanStreamAtOverlapL1Bound` follows (`meanStreamAtOverlapL1Bound_of`) from the two leaves:
   * `MeanStreamDiffDuhamelL1` (`PartI:T14/1`): 1D heat Duhamel `L¹_η` contraction
     `‖S(s) - vortexMeanStream ν c s‖_{L¹_η} ≤ ∫_0^s ‖g(r)‖_{L¹_η} dr`;
   * `MeanStressPreOverlapL1Integral` (`PartI:T14/2`): pre-overlap mean stress integral bound
     `∫_0^{s_c} ‖g(r)‖_{L¹_η} dr ≤ C (ν⁻² c⁻⁵ + ν⁻³ c⁻⁷)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc isoV isoV_apply width toVec)

/-! ### 1. Definition and smoothness of the overlap mean stream primitive `𝖲` -/

/-- The overlap-rescaled mean stream primitive
`𝖲(T, Y) = c² S(s_c + c² T / ν, c Y)` (source line 415). -/
def overlapMeanStream {ν c : ℝ} (tr : B0140.TrainSol ν c) (T Y : ℝ) : ℝ :=
  c ^ 2 * meanStream tr (B0146.overlapAge ν c + c ^ 2 * T / ν) (c * Y)

/-- For `ν > 0`, `c > 1`, and `T ≥ 0`, the overlap age `s_c + c² T / ν` is strictly positive. -/
theorem overlapAge_add_pos {ν c T : ℝ} (hν : 0 < ν) (hc : 1 < c) (hT : 0 ≤ T) :
    0 < B0146.overlapAge ν c + c ^ 2 * T / ν := by
  have hs0 : 0 < B0146.overlapAge ν c := by
    unfold B0146.overlapAge
    exact div_pos (by nlinarith) hν
  have hT0 : 0 ≤ c ^ 2 * T / ν := div_nonneg (mul_nonneg (sq_nonneg c) hT) hν.le
  linarith

/-- Joint smoothness of `𝖲(T, Y) = overlapMeanStream tr T Y` on `[0, ∞) × ℝ` for `c > 1`. -/
theorem overlapMeanStream_contDiffOn {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => overlapMeanStream tr x.1 x.2) (Ici 0 ×ˢ univ) := by
  have hc0 : 0 < c := by linarith
  have hS := (trainMeanEquations_proof ν c hν hc0 tr htr).1
  have hΦ : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      (B0146.overlapAge ν c + c ^ 2 * x.1 / ν, c * x.2)) := by
    refine ContDiff.prodMk ?_ ?_
    · exact contDiff_const.add ((contDiff_const.mul contDiff_fst).div_const ν)
    · exact contDiff_const.mul contDiff_snd
  have hmaps : MapsTo (fun x : ℝ × ℝ => (B0146.overlapAge ν c + c ^ 2 * x.1 / ν, c * x.2))
      (Ici 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := by
    intro x hx
    exact ⟨overlapAge_add_pos hν hc hx.1, mem_univ _⟩
  have hcomp := hS.comp hΦ.contDiffOn hmaps
  exact hcomp.const_smul (c ^ 2)

/-- First `Y`-derivative of `overlapMeanStream`:
`∂_Y 𝖲(T, Y) = c³ ∂_η S(s_c + c² T / ν, c Y)`. -/
theorem deriv_overlapMeanStream_Y {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ}
    (hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν) (Y : ℝ) :
    deriv (fun Y' => overlapMeanStream tr T Y') Y =
      c ^ 3 * deriv (fun e => meanStream tr (B0146.overlapAge ν c + c ^ 2 * T / ν) e) (c * Y) := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hS := (trainMeanEquations_proof ν c hν hc tr htr).1
  have hslice : ContDiff ℝ ∞ (fun e : ℝ => meanStream tr s e) :=
    t01_contDiff_slice (f := fun x : ℝ × ℝ => meanStream tr x.1 x.2) hS hs
  have hd1 : DifferentiableAt ℝ (fun e : ℝ => meanStream tr s e) (c * Y) :=
    (hslice.differentiable (by simp)).differentiableAt
  have hd_inner : HasDerivAt (fun Y' : ℝ => c * Y') c Y := by
    simpa using (hasDerivAt_id Y).const_mul c
  have hd_comp : HasDerivAt (fun Y' : ℝ => meanStream tr s (c * Y'))
      (deriv (fun e : ℝ => meanStream tr s e) (c * Y) * c) Y :=
    hd1.hasDerivAt.comp Y hd_inner
  have hd_full : HasDerivAt (fun Y' : ℝ => overlapMeanStream tr T Y')
      (c ^ 2 * (deriv (fun e : ℝ => meanStream tr s e) (c * Y) * c)) Y := by
    simpa [overlapMeanStream, s] using hd_comp.const_mul (c ^ 2)
  rw [hd_full.deriv]
  ring

/-- Second `Y`-derivative of `overlapMeanStream`:
`∂_Y² 𝖲(T, Y) = c⁴ ∂_η² S(s_c + c² T / ν, c Y)`. -/
theorem deriv_deriv_overlapMeanStream_Y {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ}
    (hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν) (Y : ℝ) :
    deriv (deriv (fun Y' => overlapMeanStream tr T Y')) Y =
      c ^ 4 * deriv (deriv (fun e => meanStream tr (B0146.overlapAge ν c + c ^ 2 * T / ν) e))
        (c * Y) := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hfun : deriv (fun Y' => overlapMeanStream tr T Y') =
      fun Y' => c ^ 3 * deriv (fun e => meanStream tr s e) (c * Y') := by
    funext Y'
    exact deriv_overlapMeanStream_Y hν hc tr htr hs Y'
  rw [hfun]
  have hS := (trainMeanEquations_proof ν c hν hc tr htr).1
  have hslice : ContDiff ℝ ∞ (fun e : ℝ => meanStream tr s e) :=
    t01_contDiff_slice (f := fun x : ℝ × ℝ => meanStream tr x.1 x.2) hS hs
  have hdslice : ContDiff ℝ ∞ (deriv (fun e : ℝ => meanStream tr s e)) :=
    hslice.deriv'
  have hd1 : DifferentiableAt ℝ (deriv (fun e : ℝ => meanStream tr s e)) (c * Y) :=
    (hdslice.differentiable (by simp)).differentiableAt
  have hd_inner : HasDerivAt (fun Y' : ℝ => c * Y') c Y := by
    simpa using (hasDerivAt_id Y).const_mul c
  have hd_comp : HasDerivAt (fun Y' : ℝ => deriv (fun e : ℝ => meanStream tr s e) (c * Y'))
      (deriv (deriv (fun e : ℝ => meanStream tr s e)) (c * Y) * c) Y :=
    hd1.hasDerivAt.comp Y hd_inner
  have hd_full : HasDerivAt (fun Y' : ℝ => c ^ 3 * deriv (fun e : ℝ => meanStream tr s e) (c * Y'))
      (c ^ 3 * (deriv (deriv (fun e : ℝ => meanStream tr s e)) (c * Y) * c)) Y :=
    hd_comp.const_mul (c ^ 3)
  rw [hd_full.deriv]
  ring

/-- `T`-derivative of `overlapMeanStream`:
`∂_T 𝖲(T, Y) = (c⁴ / ν) ∂_s S(s_c + c² T / ν, c Y)`. -/
theorem deriv_overlapMeanStream_T {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ}
    (hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν) (Y : ℝ) :
    deriv (fun T' => overlapMeanStream tr T' Y) T =
      (c ^ 4 / ν) * deriv (fun r => meanStream tr r (c * Y))
        (B0146.overlapAge ν c + c ^ 2 * T / ν) := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hS := (trainMeanEquations_proof ν c hν hc tr htr).1
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmem : (s, c * Y) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ _⟩
  have hcdAt : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (s, c * Y) :=
    hS.contDiffAt (hopen.mem_nhds hmem)
  have hemb : ContDiffAt ℝ ∞ (fun r : ℝ => (r, c * Y)) s :=
    contDiffAt_id.prodMk contDiffAt_const
  have hslice : ContDiffAt ℝ ∞ (fun r : ℝ => meanStream tr r (c * Y)) s :=
    ContDiffAt.comp s (g := fun x : ℝ × ℝ => meanStream tr x.1 x.2) hcdAt hemb
  have hd1 : DifferentiableAt ℝ (fun r : ℝ => meanStream tr r (c * Y)) s :=
    hslice.differentiableAt (by simp)
  have hd_inner : HasDerivAt (fun T' : ℝ => B0146.overlapAge ν c + c ^ 2 * T' / ν)
      (c ^ 2 / ν) T := by
    have hmul : HasDerivAt (fun T' : ℝ => c ^ 2 * T') (c ^ 2) T := by
      simpa using (hasDerivAt_id T).const_mul (c ^ 2)
    have hdiv : HasDerivAt (fun T' : ℝ => c ^ 2 * T' / ν) (c ^ 2 / ν) T :=
      hmul.div_const ν
    simpa using hdiv.const_add (B0146.overlapAge ν c)
  have hd_comp : HasDerivAt
      (fun T' : ℝ => meanStream tr (B0146.overlapAge ν c + c ^ 2 * T' / ν) (c * Y))
      (deriv (fun r : ℝ => meanStream tr r (c * Y)) s * (c ^ 2 / ν)) T :=
    HasDerivAt.comp T (h₂ := fun r : ℝ => meanStream tr r (c * Y)) hd1.hasDerivAt hd_inner
  have hd_full : HasDerivAt (fun T' : ℝ => overlapMeanStream tr T' Y)
      (c ^ 2 * (deriv (fun r : ℝ => meanStream tr r (c * Y)) s * (c ^ 2 / ν))) T := by
    simpa [overlapMeanStream] using hd_comp.const_mul (c ^ 2)
  rw [hd_full.deriv]
  ring

/-! ### 2. Horizontal mean and fluctuation scaling on the unit cylinder -/

/-- Horizontal average on the unit cell of a `c`-dilated function equals the `c`-cell average
at `c * Y`: `hmean 1 (fun y => F (c • y)) Y = hmean c F (c * Y)`. -/
theorem hmean_scale_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) (F : Plane → E) (Y : ℝ) :
    hmean 1 (fun y : Plane => F (c • y)) Y = hmean c F (c * Y) := by
  unfold hmean
  have hle1 : (-1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hlec : -c / 2 ≤ c / 2 := by linarith
  rw [inv_one, one_smul, ← intervalIntegral.integral_of_le hle1,
    ← intervalIntegral.integral_of_le hlec]
  have hcomp := intervalIntegral.integral_comp_mul_left (fun q : ℝ => F (q, c * Y)) hc.ne'
    (a := -1 / 2) (b := 1 / 2)
  have ha : c * (-1 / 2) = -c / 2 := by ring
  have hb : c * (1 / 2) = c / 2 := by ring
  rw [ha, hb] at hcomp
  simpa [Prod.smul_mk, smul_eq_mul] using hcomp

private theorem hmean_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c a : ℝ) (F : Plane → E) (Y : ℝ) :
    hmean c (fun y : Plane => a • F y) Y = a • hmean c F Y := by
  unfold hmean
  rw [integral_smul, smul_comm]

private theorem hmean_apply_vec {c : ℝ} {a : Plane → Vec} (ha : Continuous a) (η : ℝ) (j : Fin 2) :
    (hmean c a η) j = hmean c (fun z => a z j) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).integral_comp_comm hint
  unfold hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

private theorem hfluct_apply_vec {c : ℝ} {a : Plane → Vec} (ha : Continuous a) (z : Plane) (j : Fin 2) :
    (hfluct c a z) j = hfluct c (fun w => a w j) z := by
  unfold hfluct
  rw [PiLp.sub_apply, hmean_apply_vec ha z.2 j]

private theorem continuous_overlapField_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {T : ℝ}
    (hs : 0 ≤ B0146.overlapAge ν c + c ^ 2 * T / ν) :
    Continuous (overlapField ν c tr.v T) := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hmap : Continuous (fun y : Plane => ((s, c • y) : ℝ × Plane)) :=
    continuous_const.prodMk (continuous_id.const_smul c)
  have hv : Continuous (fun y : Plane => tr.v s (c • y)) :=
    hcont.comp_continuous hmap (fun y => ⟨hs, mem_univ _⟩)
  exact hv.const_smul (c ^ 3)

/-- The horizontal average of the vertical component of `overlapField` vanishes (`\bar U₂ = 0`). -/
theorem overlapField_hmean_snd_eq_zero {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ}
    (hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν) (Y : ℝ) :
    hmean 1 (fun y : Plane => overlapField ν c tr.v T y 1) Y = 0 ∧
      (hmean 1 (overlapField ν c tr.v T) Y) 1 = 0 := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hv2 := ((trainMeanEquations_proof ν c hν hc tr htr).2 s hs (c * Y)).2.2
  have h1 : hmean 1 (fun y : Plane => overlapField ν c tr.v T y 1) Y = 0 := by
    have hfun : (fun y : Plane => overlapField ν c tr.v T y 1) =
        fun y : Plane => c ^ 3 • (fun z : Plane => tr.v s z 1) (c • y) := by
      funext y
      simp [overlapField, s, smul_eq_mul]
    rw [hfun, hmean_const_smul, hmean_scale_unit hc (fun z : Plane => tr.v s z 1) Y, hv2,
      smul_zero]
  refine ⟨h1, ?_⟩
  rw [hmean_apply_vec (continuous_overlapField_slice tr hs.le) Y 1, h1]

/-- **`b = -𝖲_Y`** (source line 419): the horizontal mean drift
`b(T, Y) = (hmean 1 (overlapField ν c tr.v T) Y) 0` equals `-∂_Y 𝖲(T, Y)`. -/
theorem overlapMean_b_eq_neg_deriv {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ}
    (hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν) (Y : ℝ) :
    (hmean 1 (overlapField ν c tr.v T) Y) 0 =
      -deriv (fun Y' => overlapMeanStream tr T Y') Y := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hv1 := ((trainMeanEquations_proof ν c hν hc tr htr).2 s hs (c * Y)).2.1
  rw [hmean_apply_vec (continuous_overlapField_slice tr hs.le) Y 0]
  have hfun : (fun y : Plane => overlapField ν c tr.v T y 0) =
      fun y : Plane => c ^ 3 • (fun z : Plane => tr.v s z 0) (c • y) := by
    funext y
    simp [overlapField, s, smul_eq_mul]
  rw [hfun, hmean_const_smul, hmean_scale_unit hc (fun z : Plane => tr.v s z 0) Y,
    smul_eq_mul, hv1, deriv_overlapMeanStream_Y hν hc tr htr hs Y]
  ring

private theorem hmean_unit_mul_fluct_eq {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g)
    (Y : ℝ) (hgmean : hmean 1 g Y = 0) :
    hmean 1 (fun y => f y * g y) Y =
      hmean 1 (fun y => hfluct 1 f y * hfluct 1 g y) Y := by
  have hgint : ∫ X in Ioc (-1 / 2 : ℝ) (1 / 2), g (X, Y) = 0 := by
    have h : (1 : ℝ)⁻¹ • ∫ X in Ioc (-1 / 2 : ℝ) (1 / 2), g (X, Y) = 0 := hgmean
    simpa using h
  have hpt : ∀ X : ℝ, hfluct 1 f (X, Y) * hfluct 1 g (X, Y) =
      f (X, Y) * g (X, Y) - hmean 1 f Y * g (X, Y) := by
    intro X
    unfold hfluct
    rw [hgmean, sub_zero]
    ring
  have hpair : Continuous (fun X : ℝ => ((X, Y) : Plane)) :=
    continuous_id.prodMk continuous_const
  have hfY : Continuous (fun X : ℝ => f (X, Y)) := hf.comp hpair
  have hgY : Continuous (fun X : ℝ => g (X, Y)) := hg.comp hpair
  have hFi : IntegrableOn (fun X : ℝ => f (X, Y) * g (X, Y)) (Ioc (-1 / 2 : ℝ) (1 / 2)) :=
    (hfY.mul hgY).integrableOn_Ioc
  have hGi : IntegrableOn (fun X : ℝ => hmean 1 f Y * g (X, Y)) (Ioc (-1 / 2 : ℝ) (1 / 2)) :=
    (continuous_const.mul hgY).integrableOn_Ioc
  unfold hmean
  congr 1
  symm
  simp only [hpt]
  rw [integral_sub hFi hGi, integral_const_mul, hgint, mul_zero, sub_zero]

/-- The rescaled mean stress `c⁶ g(s_c + c² T / ν, c Y)` equals `\overline{W₁ W₂}(T, Y)`
where `W(T) = hfluct 1 (overlapField ν c tr.v T)`. -/
theorem overlapMeanStress_eq_fluct {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ}
    (hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν) (Y : ℝ) :
    c ^ 6 * meanStress tr (B0146.overlapAge ν c + c ^ 2 * T / ν) (c * Y) =
      hmean 1 (fun y : Plane =>
        hfluct 1 (overlapField ν c tr.v T) y 0 *
          hfluct 1 (overlapField ν c tr.v T) y 1) Y := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  set U := overlapField ν c tr.v T
  have hUc : Continuous U := continuous_overlapField_slice tr hs.le
  have hU0c : Continuous (fun y : Plane => U y 0) := (PiLp.continuous_apply _ _ 0).comp hUc
  have hU1c : Continuous (fun y : Plane => U y 1) := (PiLp.continuous_apply _ _ 1).comp hUc
  have hU1_zero : hmean 1 (fun y : Plane => U y 1) Y = 0 :=
    (overlapField_hmean_snd_eq_zero hν hc tr htr hs Y).1
  have hfluct_prod : (fun y : Plane => hfluct 1 U y 0 * hfluct 1 U y 1) =
      fun y : Plane => hfluct 1 (fun w => U w 0) y * hfluct 1 (fun w => U w 1) y := by
    funext y
    rw [hfluct_apply_vec hUc y 0, hfluct_apply_vec hUc y 1]
  rw [hfluct_prod, ← hmean_unit_mul_fluct_eq hU0c hU1c Y hU1_zero]
  have hU_prod : (fun y : Plane => U y 0 * U y 1) =
      fun y : Plane => (c ^ 6 : ℝ) • (fun z : Plane => tr.v s z 0 * tr.v s z 1) (c • y) := by
    funext y
    simp only [U, overlapField, s, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hU_prod, hmean_const_smul,
    hmean_scale_unit hc (fun z : Plane => tr.v s z 0 * tr.v s z 1) Y]
  rfl

/-- **`𝖲_T - 𝖲_{YY} = e_c \overline{W₁ W₂}`** (source line 418): the overlap-rescaled mean stream
primitive solves the 1D forced heat equation with forcing `e_c \overline{W₁ W₂}`. -/
theorem overlapMeanStream_eq {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ}
    (hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν) (Y : ℝ) :
    deriv (fun T' => overlapMeanStream tr T' Y) T -
        deriv (deriv (fun Y' => overlapMeanStream tr T Y')) Y =
      eC ν c * hmean 1 (fun y : Plane =>
        hfluct 1 (overlapField ν c tr.v T) y 0 *
          hfluct 1 (overlapField ν c tr.v T) y 1) Y := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hmeanEq := ((trainMeanEquations_proof ν c hν hc tr htr).2 s hs (c * Y)).1
  rw [deriv_overlapMeanStream_T hν hc tr htr hs Y,
    deriv_deriv_overlapMeanStream_Y hν hc tr htr hs Y,
    ← overlapMeanStress_eq_fluct hν hc tr htr hs Y]
  have hν0 : ν ≠ 0 := hν.ne'
  have hc0 : c ≠ 0 := hc.ne'
  unfold eC
  calc (c ^ 4 / ν) * deriv (fun r => meanStream tr r (c * Y)) s -
        c ^ 4 * deriv (deriv (fun e => meanStream tr s e)) (c * Y)
      = (c ^ 4 / ν) * (deriv (fun r => meanStream tr r (c * Y)) s -
          ν * deriv (deriv (fun e => meanStream tr s e)) (c * Y)) := by
        field_simp
    _ = (c ^ 4 / ν) * meanStress tr s (c * Y) := by rw [hmeanEq]
    _ = (ν * c ^ 2)⁻¹ * (c ^ 6 * meanStress tr s (c * Y)) := by
        field_simp

/-! ### 3. `L¹` norm scaling at overlap `T = 0` -/

/-- At `T = 0`, `overlapMeanStream tr 0 Y = c² S(s_c, c Y)`. -/
theorem overlapMeanStream_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) (Y : ℝ) :
    overlapMeanStream tr 0 Y = c ^ 2 * meanStream tr (B0146.overlapAge ν c) (c * Y) := by
  simp [overlapMeanStream]

/-- `L¹` scaling identity at `T = 0`:
`‖𝖲(0)‖_{L¹_Y} = c ‖S(s_c)‖_{L¹_η}` for `0 < ν` and `1 < c`. -/
theorem eLpNorm_overlapMeanStream_zero {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) :
    eLpNorm (overlapMeanStream tr 0) 1 volume =
      ENNReal.ofReal c * eLpNorm (meanStream tr (B0146.overlapAge ν c)) 1 volume := by
  have hc0 : 0 < c := by linarith
  set s_c := B0146.overlapAge ν c
  have hs_c : 0 < s_c := by
    simpa [s_c] using overlapAge_add_pos hν hc (le_refl 0)
  have hS := (trainMeanEquations_proof ν c hν hc0 tr htr).1
  have hslice : ContDiff ℝ ∞ (meanStream tr s_c) :=
    t01_contDiff_slice (f := fun x : ℝ × ℝ => meanStream tr x.1 x.2) hS hs_c
  have hmeas : AEStronglyMeasurable (meanStream tr s_c)
      (Measure.map (fun Y : ℝ => c * Y) volume) :=
    hslice.continuous.measurable.aestronglyMeasurable
  have hfun : overlapMeanStream tr 0 = (c ^ 2 : ℝ) • (fun Y : ℝ => meanStream tr s_c (c * Y)) := by
    funext Y
    simp [overlapMeanStream_zero, s_c, smul_eq_mul]
  have hmap : Measure.map (fun Y : ℝ => c * Y) (volume : Measure ℝ) =
      ENNReal.ofReal c⁻¹ • (volume : Measure ℝ) := by
    rw [Real.map_volume_mul_left hc0.ne', abs_of_pos (inv_pos.2 hc0)]
  have hcomp : eLpNorm (fun Y : ℝ => meanStream tr s_c (c * Y)) 1 volume =
      ENNReal.ofReal c⁻¹ * eLpNorm (meanStream tr s_c) 1 volume := by
    change eLpNorm ((meanStream tr s_c) ∘ (fun Y : ℝ => c * Y)) 1 volume = _
    rw [← eLpNorm_map_measure hmeas (measurable_const_mul c).aemeasurable, hmap,
      eLpNorm_smul_measure_of_ne_top ENNReal.one_ne_top]
    simp
  rw [hfun, eLpNorm_const_smul, hcomp, ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal (sq_nonneg c), ← ENNReal.ofReal_mul (sq_nonneg c)]
  congr 1
  field_simp [hc0.ne']

/-! ### 4. Reflection symmetry of `V_c^p` (`\overline{(V_c^p)₁ (V_c^p)₂} = 0`, lines 406-407) -/

/-- Horizontal reflection symmetry of the isolated vortex `isoV`:
the first component is even in `q` and the second component is odd in `q`. -/
theorem isoV_reflect_fst (ν s q η : ℝ) :
    isoV ν s (-q, η) 0 = isoV ν s (q, η) 0 ∧
      isoV ν s (-q, η) 1 = -isoV ν s (q, η) 1 := by
  rw [isoV_apply, isoV_apply]
  simp [UnforcedLeray.Train.toVec_zero, UnforcedLeray.Train.toVec_one]

/-- Horizontal reflection symmetry of the periodized heat vortex `Vc`:
`Vc ν c s (-q, η) 0 = Vc ν c s (q, η) 0` and `Vc ν c s (-q, η) 1 = -Vc ν c s (q, η) 1`. -/
theorem Vc_reflect_fst {ν c s : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (q η : ℝ) :
    Vc ν c s (-q, η) 0 = Vc ν c s (q, η) 0 ∧
      Vc ν c s (-q, η) 1 = -Vc ν c s (q, η) 1 := by
  have hsum_pos := UnforcedLeray.Train.summable_isoV hν hc hs (q, η)
  have hsum_neg := UnforcedLeray.Train.summable_isoV hν hc hs (-q, η)
  have heval0_pos : (∑' n : ℤ, isoV ν s (q - ↑n * c, η)) 0 =
      ∑' n : ℤ, isoV ν s (q - ↑n * c, η) 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).map_tsum hsum_pos
  have heval0_neg : (∑' n : ℤ, isoV ν s (-q - ↑n * c, η)) 0 =
      ∑' n : ℤ, isoV ν s (-q - ↑n * c, η) 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).map_tsum hsum_neg
  have heval1_pos : (∑' n : ℤ, isoV ν s (q - ↑n * c, η)) 1 =
      ∑' n : ℤ, isoV ν s (q - ↑n * c, η) 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).map_tsum hsum_pos
  have heval1_neg : (∑' n : ℤ, isoV ν s (-q - ↑n * c, η)) 1 =
      ∑' n : ℤ, isoV ν s (-q - ↑n * c, η) 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).map_tsum hsum_neg
  change (∑' n : ℤ, isoV ν s (-q - ↑n * c, η)) 0 = (∑' n : ℤ, isoV ν s (q - ↑n * c, η)) 0 ∧
    (∑' n : ℤ, isoV ν s (-q - ↑n * c, η)) 1 = -(∑' n : ℤ, isoV ν s (q - ↑n * c, η)) 1
  rw [heval0_neg, heval0_pos, heval1_neg, heval1_pos, ← tsum_neg]
  refine ⟨?_, ?_⟩
  · rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; ext n
    simp only [Equiv.neg_apply]
    have hq : -q - ↑(-n) * c = -(q - ↑n * c) := by push_cast; ring
    rw [hq, (isoV_reflect_fst ν s (q - ↑n * c) η).1]
  · rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; ext n
    simp only [Equiv.neg_apply]
    have hq : -q - ↑(-n) * c = -(q - ↑n * c) := by push_cast; ring
    rw [hq, (isoV_reflect_fst ν s (q - ↑n * c) η).2]

/-- **Separate reflection symmetries of `V_c^p` imply `\overline{(V_c^p)₁ (V_c^p)₂} = 0`**
(source lines 406-407). -/
theorem hmean_Vc_prod_eq_zero {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) (η : ℝ) :
    hmean c (fun z : Plane => Vc ν c s z 0 * Vc ν c s z 1) η = 0 := by
  unfold hmean
  have hlec : -c / 2 ≤ c / 2 := by linarith
  rw [← intervalIntegral.integral_of_le hlec]
  set f : ℝ → ℝ := fun q => Vc ν c s (q, η) 0 * Vc ν c s (q, η) 1
  have hodd : ∀ q : ℝ, f (-q) = -f q := by
    intro q
    obtain ⟨h0, h1⟩ := Vc_reflect_fst hν hc.ne' hs q η
    simp only [f, h0, h1, mul_neg]
  have h1 : ∫ q in (-c / 2)..(c / 2), f (-q) = ∫ q in (-c / 2)..(c / 2), f q := by
    have h := intervalIntegral.integral_comp_neg f (a := -c / 2) (b := c / 2)
    have hb1 : -(c / 2) = -c / 2 := by ring
    have hb2 : -(-c / 2) = c / 2 := by ring
    rwa [hb1, hb2] at h
  have h2 : ∫ q in (-c / 2)..(c / 2), f (-q) = -∫ q in (-c / 2)..(c / 2), f q := by
    simp only [hodd, intervalIntegral.integral_neg]
  have hint0 : ∫ q in (-c / 2)..(c / 2), f q = 0 := by linarith
  change c⁻¹ • ∫ q in (-c / 2)..(c / 2), f q = 0
  rw [hint0, smul_zero]

/-- By `hmean_Vc_prod_eq_zero`, the mean Reynolds stress `g = \overline{v₁ v₂}` equals the
horizontal average of the error difference `v₁ v₂ - (V_c^p)₁ (V_c^p)₂`. -/
theorem meanStress_eq_hmean_error {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s)
    (tr : B0140.TrainSol ν c) (η : ℝ) :
    meanStress tr s η =
      hmean c (fun z : Plane => tr.v s z 0 * tr.v s z 1 - Vc ν c s z 0 * Vc ν c s z 1) η := by
  have hvc : Continuous (tr.v s) := by
    have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    exact hcont.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hs, mem_univ _⟩)
  have ha_pos : 0 < width ν s := by
    change 0 < 1 + ν * s
    nlinarith
  have hVc : Continuous (Vc ν c s) :=
    (UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc ha_pos).continuous
  have hpair : Continuous (fun q : ℝ => ((q, η) : Plane)) :=
    continuous_id.prodMk continuous_const
  have hv_int : IntegrableOn (fun q : ℝ => tr.v s (q, η) 0 * tr.v s (q, η) 1)
      (Ioc (-c / 2) (c / 2)) :=
    (((PiLp.continuous_apply _ _ 0).comp (hvc.comp hpair)).mul
      ((PiLp.continuous_apply _ _ 1).comp (hvc.comp hpair))).integrableOn_Ioc
  have hV_int : IntegrableOn (fun q : ℝ => Vc ν c s (q, η) 0 * Vc ν c s (q, η) 1)
      (Ioc (-c / 2) (c / 2)) :=
    (((PiLp.continuous_apply _ _ 0).comp (hVc.comp hpair)).mul
      ((PiLp.continuous_apply _ _ 1).comp (hVc.comp hpair))).integrableOn_Ioc
  have hsub : hmean c (fun z : Plane => tr.v s z 0 * tr.v s z 1 - Vc ν c s z 0 * Vc ν c s z 1) η =
      meanStress tr s η - hmean c (fun z : Plane => Vc ν c s z 0 * Vc ν c s z 1) η := by
    unfold meanStress hmean
    rw [integral_sub hv_int hV_int, smul_sub]
  rw [hsub, hmean_Vc_prod_eq_zero hν hc hs η, sub_zero]

/-! ### 5. The isolated-vortex mean stream and its `L¹_η` norm -/

/-- The horizontal average `\overline{\psi_c^p}(s, η) = -(8π c⁻¹) G_{1 + νs}(η)` of the periodized
Gaussian stream `ψ_c^p(q, η, s) = ∑_n -(2/a) e^{-((q-nc)²+η²)/(4a)}`, `a = 1 + νs`
(source lines 408-415). -/
def vortexMeanStream (ν c s η : ℝ) : ℝ :=
  -(8 * Real.pi * c⁻¹) * heatKernel1 (width ν s) η

private theorem heatKernel1_nonneg {a : ℝ} (ha : 0 < a) (η : ℝ) : 0 ≤ heatKernel1 a η := by
  unfold heatKernel1
  positivity

private theorem integrable_heatKernel1 {a : ℝ} (ha : 0 < a) :
    Integrable (heatKernel1 a) volume := by
  have hb : 0 < (4 * a)⁻¹ := by positivity
  have hG : Integrable (fun η : ℝ => Real.exp (-(4 * a)⁻¹ * η ^ 2)) volume :=
    integrable_exp_neg_mul_sq hb
  refine (hG.const_mul (Real.sqrt (4 * Real.pi * a))⁻¹).congr (ae_of_all _ fun η => ?_)
  unfold heatKernel1
  rw [show -(η ^ 2) / (4 * a) = -(4 * a)⁻¹ * η ^ 2 by ring]

private theorem integral_heatKernel1_eq_one {a : ℝ} (ha : 0 < a) :
    ∫ η : ℝ, heatKernel1 a η = 1 := by
  have hfun : heatKernel1 a = fun η : ℝ =>
      (Real.sqrt (4 * Real.pi * a))⁻¹ * Real.exp (-(4 * a)⁻¹ * η ^ 2) := by
    funext η
    unfold heatKernel1
    rw [show -(η ^ 2) / (4 * a) = -(4 * a)⁻¹ * η ^ 2 by ring]
  rw [hfun, integral_const_mul, integral_gaussian,
    show Real.pi / (4 * a)⁻¹ = 4 * Real.pi * a by field_simp,
    inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne']

private theorem eLpNorm_heatKernel1_one {a : ℝ} (ha : 0 < a) :
    eLpNorm (heatKernel1 a) 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (integrable_heatKernel1 ha)]
  have hnorm : (fun η : ℝ => ‖heatKernel1 a η‖) = heatKernel1 a := by
    funext η
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel1_nonneg ha η)]
  rw [hnorm, integral_heatKernel1_eq_one ha, ENNReal.ofReal_one]

/-- Exact `L¹_η` norm of `vortexMeanStream`: `‖\overline{\psi_c^p}(s)‖_{L¹_η} = 8π c⁻¹`. -/
theorem eLpNorm_vortexMeanStream {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) :
    eLpNorm (vortexMeanStream ν c s) 1 volume = ENNReal.ofReal (8 * Real.pi * c⁻¹) := by
  have ha : 0 < width ν s := by
    change 0 < 1 + ν * s
    nlinarith
  have hfun : vortexMeanStream ν c s = (-(8 * Real.pi * c⁻¹) : ℝ) • heatKernel1 (width ν s) := by
    funext η
    simp [vortexMeanStream, smul_eq_mul]
  rw [hfun, eLpNorm_const_smul, eLpNorm_heatKernel1_one ha, mul_one,
    Real.enorm_eq_ofReal_abs, abs_neg, abs_of_pos (by positivity)]

/-! ### 6. Leaves and conditional assembly of `PartI:T14` -/

/-- **Leaf 1 (`PartI:T14/1`)**: 1D heat Duhamel `L¹_η` contraction for the difference between the
mean stream `S(s, η) = meanStream tr s η` and the isolated-vortex mean stream
`vortexMeanStream ν c s η = -(8π c⁻¹) G_{1 + νs}(η)` (source lines 398-410):
`‖S(s) - vortexMeanStream ν c s‖_{L¹_η} ≤ ∫_0^s ‖g(r)‖_{L¹_η} dr`. -/
def MeanStreamDiffDuhamelL1 : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 1 ≤ c →
    ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
      ∀ s : ℝ, 0 < s →
        eLpNorm (fun η => meanStream tr s η - vortexMeanStream ν c s η) 1 volume ≤
          ∫⁻ r in Ioc 0 s, eLpNorm (meanStress tr r) 1 volume

/-- **Leaf 2 (`PartI:T14/2`)**: pre-overlap `L¹_η` time integral bound for the mean stress
`g = meanStress tr` on `(0, s_c]` (source lines 406-414):
`∫_0^{s_c} ‖g(r)‖_{L¹_η} dr ≤ C (ν⁻² c⁻⁵ + ν⁻³ c⁻⁷)`. -/
def MeanStressPreOverlapL1Integral : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        ∫⁻ r in Ioc 0 (B0146.overlapAge ν c), eLpNorm (meanStress tr r) 1 volume ≤
          ENNReal.ofReal (C * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) + ν ^ (-3 : ℝ) * c ^ (-7 : ℝ)))

/-- Pre-overlap `L¹_η` bound on the mean stream at overlap age `s_c = overlapAge ν c`
(source lines 408-415): `‖S(s_c)‖_{L¹_η} ≤ C c⁻¹`. -/
def MeanStreamAtOverlapL1Bound : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        eLpNorm (meanStream tr (B0146.overlapAge ν c)) 1 volume ≤
          ENNReal.ofReal (C * c⁻¹)

/-- Derivation of `MeanStreamAtOverlapL1Bound` from `MeanStreamDiffDuhamelL1` and
`MeanStressPreOverlapL1Integral` (source lines 408-415). -/
theorem meanStreamAtOverlapL1Bound_of (hDuh : MeanStreamDiffDuhamelL1)
    (hInt : MeanStressPreOverlapL1Integral) : MeanStreamAtOverlapL1Bound := by
  intro ρ hρ
  obtain ⟨C, ν₁, hC, hν₁, hI⟩ := hInt ρ hρ
  obtain ⟨ν₂, hν₂, _, hAsym⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
  refine ⟨2 * C + 8 * Real.pi, min (min ν₁ ν₂) (2 ^ (-1 / ρ)), by positivity,
    lt_min (lt_min hν₁ hν₂) (Real.rpow_pos_of_pos two_pos _), ?_⟩
  intro ν hν hν_le tr htr
  dsimp only
  let c := trainPeriod ρ ν
  have hν_12 : ν ≤ min ν₁ ν₂ := hν_le.trans (min_le_left _ _)
  have hν_1 : ν ≤ ν₁ := hν_12.trans (min_le_left _ _)
  have hν_2 : ν ≤ ν₂ := hν_12.trans (min_le_right _ _)
  have hν_3 : ν ≤ 2 ^ (-1 / ρ) := hν_le.trans (min_le_right _ _)
  obtain ⟨hc_ge1, hνc2_ge2⟩ := hAsym ν hν hν_2
  have hρ0 : 0 < ρ := by linarith
  have hc_ge2 : 2 ≤ c := by
    have hpow := Real.rpow_le_rpow_of_nonpos hν hν_3 (neg_nonpos.mpr hρ0.le)
    have hexp : (-1 / ρ) * (-ρ) = 1 := by field_simp [hρ0.ne']
    rw [← Real.rpow_mul two_pos.le, hexp, Real.rpow_one] at hpow
    exact hpow
  have hc1 : 1 < c := by linarith
  have hc0 : 0 < c := by linarith
  have heC_le1 : eC ν c ≤ 1 := by
    unfold eC
    rw [inv_le_one_iff₀]
    right
    linarith
  let s_c := B0146.overlapAge ν c
  have hs_c : 0 < s_c := by
    simpa [s_c] using overlapAge_add_pos hν hc1 (le_refl 0)
  have hS := (trainMeanEquations_proof ν c hν hc0 tr htr).1
  have hslice : ContDiff ℝ ∞ (meanStream tr s_c) :=
    t01_contDiff_slice (f := fun x : ℝ × ℝ => meanStream tr x.1 x.2) hS hs_c
  have hcont_v : Continuous (vortexMeanStream ν c s_c) := by
    unfold vortexMeanStream heatKernel1
    fun_prop
  have hmeas_diff : AEStronglyMeasurable
      (fun η => meanStream tr s_c η - vortexMeanStream ν c s_c η) volume :=
    (hslice.continuous.sub hcont_v).measurable.aestronglyMeasurable
  have hmeas_v : AEStronglyMeasurable (vortexMeanStream ν c s_c) volume :=
    hcont_v.measurable.aestronglyMeasurable
  have hdecomp : meanStream tr s_c =
      (fun η => meanStream tr s_c η - vortexMeanStream ν c s_c η) + vortexMeanStream ν c s_c := by
    funext η
    simp [Pi.add_apply]
  have htri : eLpNorm (meanStream tr s_c) 1 volume ≤
      eLpNorm (fun η => meanStream tr s_c η - vortexMeanStream ν c s_c η) 1 volume +
        eLpNorm (vortexMeanStream ν c s_c) 1 volume := by
    conv_lhs => rw [hdecomp]
    exact eLpNorm_add_le hmeas_diff hmeas_v le_rfl
  have h1 := (hDuh ν c hν hc_ge1 tr htr s_c hs_c).trans (hI ν hν hν_1 tr htr)
  have h2 := eLpNorm_vortexMeanStream hν hc0 hs_c.le
  have heC_pos : 0 ≤ eC ν c := by
    unfold eC
    positivity
  have hterm1 : ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) ≤ c⁻¹ := by
    have heq : ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) = (eC ν c) ^ 2 * c⁻¹ := by
      unfold eC
      rw [Real.rpow_neg hν.le, Real.rpow_two,
        show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc0.le, Real.rpow_natCast]
      field_simp [hν.ne', hc0.ne']
    rw [heq]
    exact mul_le_of_le_one_left (inv_nonneg.2 hc0.le) (pow_le_one₀ heC_pos heC_le1)
  have hterm2 : ν ^ (-3 : ℝ) * c ^ (-7 : ℝ) ≤ c⁻¹ := by
    have heq : ν ^ (-3 : ℝ) * c ^ (-7 : ℝ) = (eC ν c) ^ 3 * c⁻¹ := by
      unfold eC
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν.le, Real.rpow_natCast,
        show (-7 : ℝ) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc0.le, Real.rpow_natCast]
      field_simp [hν.ne', hc0.ne']
    rw [heq]
    exact mul_le_of_le_one_left (inv_nonneg.2 hc0.le) (pow_le_one₀ heC_pos heC_le1)
  have hsum_le : C * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) + ν ^ (-3 : ℝ) * c ^ (-7 : ℝ)) +
      8 * Real.pi * c⁻¹ ≤ (2 * C + 8 * Real.pi) * c⁻¹ := by
    nlinarith
  calc eLpNorm (meanStream tr s_c) 1 volume
      ≤ eLpNorm (fun η => meanStream tr s_c η - vortexMeanStream ν c s_c η) 1 volume +
          eLpNorm (vortexMeanStream ν c s_c) 1 volume := htri
    _ ≤ ENNReal.ofReal (C * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) + ν ^ (-3 : ℝ) * c ^ (-7 : ℝ))) +
          ENNReal.ofReal (8 * Real.pi * c⁻¹) := add_le_add h1 (le_of_eq h2)
    _ = ENNReal.ofReal (C * (ν ^ (-2 : ℝ) * c ^ (-5 : ℝ) + ν ^ (-3 : ℝ) * c ^ (-7 : ℝ)) +
          8 * Real.pi * c⁻¹) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((2 * C + 8 * Real.pi) * c⁻¹) := ENNReal.ofReal_le_ofReal hsum_le

/-- **`PartI:T14` (`overlap_mean_primitive_of`)** (source lines 395-425):
given `MeanStreamDiffDuhamelL1` and `MeanStressPreOverlapL1Integral`, for `c = trainPeriod ρ ν`
(`1 / 2 < ρ`), `tr : B0140.TrainSol ν c` in `IsBUCTrain`, and `𝖲 = overlapMeanStream tr`:
1. `ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => 𝖲 x.1 x.2) (Ici 0 ×ˢ univ)`;
2. for all `T ≥ 0` and `Y : ℝ`,
   `∂_T 𝖲(T, Y) - ∂_Y² 𝖲(T, Y) = e_c \overline{W₁ W₂}(T, Y)`,
   `b(T, Y) = -∂_Y 𝖲(T, Y)`, and `\bar U₂(T, Y) = 0`;
3. `‖𝖲(0)‖_{L¹_Y} ≤ C`. -/
theorem overlap_mean_primitive_of (hDuh : MeanStreamDiffDuhamelL1)
    (hInt : MeanStressPreOverlapL1Integral) (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          let c := trainPeriod ρ ν
          let U := overlapField ν c tr.v
          let W := fun T => hfluct 1 (U T)
          let b := fun T Y => (hmean 1 (U T) Y) 0
          ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => overlapMeanStream tr x.1 x.2) (Ici 0 ×ˢ univ) ∧
          (∀ T : ℝ, 0 ≤ T → ∀ Y : ℝ,
            deriv (fun T' => overlapMeanStream tr T' Y) T -
                deriv (deriv (fun Y' => overlapMeanStream tr T Y')) Y =
              eC ν c * hmean 1 (fun y : Plane => W T y 0 * W T y 1) Y ∧
            b T Y = -deriv (fun Y' => overlapMeanStream tr T Y') Y ∧
            (hmean 1 (U T) Y) 1 = 0) ∧
          eLpNorm (overlapMeanStream tr 0) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨C, ν₁, hC, hν₁, hbound⟩ := meanStreamAtOverlapL1Bound_of hDuh hInt ρ hρ
  refine ⟨C, min ν₁ (2 ^ (-1 / ρ)), hC,
    lt_min hν₁ (Real.rpow_pos_of_pos two_pos _), ?_⟩
  intro ν hν hν_le tr htr
  dsimp only
  let c := trainPeriod ρ ν
  have hν_le1 : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν_le2 : ν ≤ 2 ^ (-1 / ρ) := hν_le.trans (min_le_right _ _)
  have hρ0 : 0 < ρ := by linarith
  have hc_ge2 : 2 ≤ c := by
    have hpow := Real.rpow_le_rpow_of_nonpos hν hν_le2 (neg_nonpos.mpr hρ0.le)
    have hexp : (-1 / ρ) * (-ρ) = 1 := by field_simp [hρ0.ne']
    rw [← Real.rpow_mul two_pos.le, hexp, Real.rpow_one] at hpow
    exact hpow
  have hc1 : 1 < c := by linarith
  have hc0 : 0 < c := by linarith
  refine ⟨overlapMeanStream_contDiffOn hν hc1 tr htr, ?_, ?_⟩
  · intro T hT Y
    have hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν := overlapAge_add_pos hν hc1 hT
    exact ⟨overlapMeanStream_eq hν hc0 tr htr hs Y,
      overlapMean_b_eq_neg_deriv hν hc0 tr htr hs Y,
      (overlapField_hmean_snd_eq_zero hν hc0 tr htr hs Y).2⟩
  · rw [eLpNorm_overlapMeanStream_zero hν hc1 tr htr]
    have hL1_ν := hbound ν hν hν_le1 tr htr
    calc ENNReal.ofReal c * eLpNorm (meanStream tr (B0146.overlapAge ν c)) 1 volume
        ≤ ENNReal.ofReal c * ENNReal.ofReal (C * c⁻¹) := by gcongr
      _ = ENNReal.ofReal (c * (C * c⁻¹)) := by rw [← ENNReal.ofReal_mul hc0.le]
      _ = ENNReal.ofReal C := by
          congr 1
          field_simp [hc0.ne']

end UnforcedLeray.Short.PartI
