import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanStreamDecay
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1

/-!
# Part I, task `PartI:TC/3`: decay of the mean velocity and its derivative (BUC train)

Source of record: `the November 2 reference manuscript`, lines 261-288 and 397-404.
The Prop `BUCMeanVelDecay` is defined in `Short/PartI/Sub/T01Class.lean`; this file proves it.

Notation at a fixed age `s ≥ 0`: `S = meanStream tr s`, `u = meanVel1 tr s = \bar v₁`,
`G1 = ∂_η v₁` and `G2 = ∂_η² v₁` (pointwise, horizontal averages `u' = \bar G1`, `u'' = \bar G2`).

* `S' = -u` (`bucVel_S_deriv`, the proof of `TrainMeanV1` with `s ≥ 0`), `u' = \bar G1`
  and `(\bar G1)' = \bar G2` (`trainMeanV1_hasDerivAt_hmean`), with `|\bar G1| ≤ M₁`, `|\bar G2| ≤ M₂`
  from the orders `1, 2` of `IsBUCTrain`.
* `u → 0`: the one-sided interpolation inequality `bucVel_lk` for `f = S` (with `S'' = -\bar G1`
  bounded by `M₁`) and the tail `S → 0` (`MeanStreamDecay`).
* `u' → 0`: `bucVel_lk` for `f = -u` (with `f'' = -\bar G2` bounded by `M₂`) and the tail `u → 0`.

`bucVel_lk` is the one-sided interpolation inequality of `TrainClass/LkOneSided.lean` in the form
needing only `Differentiable f` and `Differentiable (deriv f)` (no `C²` hypothesis), since the
averages here are only known to be differentiable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec_zero)

/-! ### One-sided interpolation with `Differentiable` hypotheses -/

private theorem bucVel_lipschitz {f : ℝ → ℝ} (hH : Differentiable ℝ (deriv f)) {B : ℝ}
    (hB : ∀ t, |deriv (deriv f) t| ≤ B) (x t : ℝ) :
    |deriv f t - deriv f x| ≤ B * |t - x| := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (C := B)
    (fun y _ => hH y) (fun y _ => by rw [Real.norm_eq_abs]; exact hB y) (mem_univ x) (mem_univ t)
  simpa only [Real.norm_eq_abs] using h

private theorem bucVel_taylor_upper {f : ℝ → ℝ} (hf : Differentiable ℝ f) {x B : ℝ}
    (hlip : ∀ t, x ≤ t → deriv f t - deriv f x ≤ B * (t - x)) (t : ℝ) (ht : x ≤ t) :
    f t - f x - (t - x) * deriv f x ≤ B * (t - x) ^ 2 / 2 := by
  have hG : ∀ s : ℝ,
      HasDerivAt (fun s => f s - f x - (s - x) * deriv f x - B * (s - x) ^ 2 / 2)
        (deriv f s - deriv f x - B * (s - x)) s := by
    intro s
    have h1 : HasDerivAt f (deriv f s) s := (hf s).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => y - x) 1 s := (hasDerivAt_id' (x := s)).sub_const x
    have h3 := ((h1.sub_const (f x)).sub (h2.mul_const (deriv f x))).sub
      (((h2.pow 2).const_mul B).div_const 2)
    refine h3.congr_deriv ?_
    norm_num
    ring
  have hanti : AntitoneOn (fun s => f s - f x - (s - x) * deriv f x - B * (s - x) ^ 2 / 2)
      (Ici x) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici x) ?_ ?_ ?_
    · exact fun s _ => (hG s).continuousAt.continuousWithinAt
    · exact fun s _ => (hG s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hG s).deriv]
      have hs' := hlip s (le_of_lt (Set.mem_Ioi.mp hs))
      linarith
  have key := hanti (Set.mem_Ici.mpr le_rfl) (show t ∈ Ici x from ht) ht
  dsimp only at key
  linarith

/-- One-sided interpolation: `f` differentiable with `f'` differentiable, `|f''| ≤ B`, and
`|f| ≤ m` on `[x, ∞)`; then `|f'(x)| ≤ 2m/h + B h/2` for every `h > 0`. -/
theorem bucVel_lk {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hH : Differentiable ℝ (deriv f))
    {x B m h : ℝ} (hh : 0 < h) (hB2 : ∀ t, |deriv (deriv f) t| ≤ B)
    (hm : ∀ t, x ≤ t → |f t| ≤ m) : |deriv f x| ≤ 2 * m / h + B * h / 2 := by
  have hup_lip : ∀ t, x ≤ t → deriv f t - deriv f x ≤ B * (t - x) := by
    intro t ht
    have h1 := bucVel_lipschitz hH hB2 x t
    rw [abs_of_nonneg (sub_nonneg.2 ht)] at h1
    exact le_trans (le_abs_self _) h1
  have hlo_lip : ∀ t, x ≤ t → deriv (-f) t - deriv (-f) x ≤ B * (t - x) := by
    intro t ht
    rw [deriv.neg, deriv.neg]
    have h1 := bucVel_lipschitz hH hB2 x t
    rw [abs_of_nonneg (sub_nonneg.2 ht)] at h1
    have h3 := (abs_le.mp h1).1
    linarith
  have hup := bucVel_taylor_upper hf hup_lip (x + h) (by linarith)
  have hlow := bucVel_taylor_upper hf.neg hlo_lip (x + h) (by linarith)
  simp only [Pi.neg_apply, deriv.neg] at hlow
  have e : x + h - x = h := by ring
  rw [e] at hup hlow
  have hfx := abs_le.mp (hm x le_rfl)
  have hfxh := abs_le.mp (hm (x + h) (by linarith))
  have key : |h * deriv f x| ≤ 2 * m + B * h ^ 2 / 2 := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hc : |h * deriv f x| = h * |deriv f x| := by
    rw [abs_mul, abs_of_pos hh]
  have hfin : h * |deriv f x| ≤ 2 * m + B * h ^ 2 / 2 := by
    rw [← hc]
    exact key
  have hdiv : |deriv f x| ≤ (2 * m + B * h ^ 2 / 2) / h := by
    rw [le_div_iff₀ hh]
    linarith
  have hh' : h ≠ 0 := ne_of_gt hh
  have hsplit : (2 * m + B * h ^ 2 / 2) / h = 2 * m / h + B * h / 2 := by
    field_simp
  linarith

/-- An explicit choice of `h, m > 0` with `2m/h + M h/2 < ε`. -/
theorem bucVel_arith {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    ∃ h m : ℝ, 0 < h ∧ 0 < m ∧ 2 * m / h + M * h / 2 < ε := by
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = ε / (2 * (M + 1)) := ⟨_, rfl⟩
  have hM1 : 0 < M + 1 := by linarith
  have hh0 : 0 < h := by rw [hh]; exact div_pos hε (by linarith)
  have hhne : h ≠ 0 := hh0.ne'
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ε * h / 8 := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact div_pos (mul_pos hε hh0) (by norm_num)
  have h2 : 2 * m / h = ε / 4 := by
    rw [div_eq_iff hhne, hm]; ring
  have h3 : (M + 1) * h = ε / 2 := by
    rw [hh]; field_simp
  have h4 : M * h ≤ (M + 1) * h := by nlinarith
  exact ⟨h, m, hh0, hm0, by linarith⟩

/-! ### Horizontal averages and derivatives at a fixed age -/

/-- Derivative of a negation, for the lambda form `fun y => -f y`. -/
theorem bucVel_deriv_neg (f : ℝ → ℝ) (x : ℝ) : deriv (fun y => -f y) x = -deriv f x :=
  deriv.neg

/-- The horizontal average of a function bounded by `K` on the line `η` is bounded by `K`. -/
theorem bucVel_hmean_abs_le {c : ℝ} (hc : 0 < c) (F : Plane → ℝ) (η K : ℝ)
    (h : ∀ q : ℝ, |F (q, η)| ≤ K) : |hmean c F η| ≤ K := by
  unfold hmean
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (-c / 2) (c / 2)) (f := fun q : ℝ => F (q, η)) (C := K)
    measure_Ioc_lt_top (fun q _ => by rw [Real.norm_eq_abs]; exact h q)
  rw [Real.volume_real_Ioc_of_le (by linarith), show c / 2 - -c / 2 = c by ring] at hint
  rw [Real.norm_eq_abs] at hint
  rw [smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc]
  have h1 : c⁻¹ * |∫ q in Ioc (-c / 2) (c / 2), F (q, η)| ≤ c⁻¹ * (K * c) :=
    mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hc.le)
  have h2 : c⁻¹ * (K * c) = K := by field_simp
  linarith

/-- The velocity at a fixed age `s ≥ 0` is `C^∞` in the spatial variable. -/
theorem bucVel_vslice_contDiff {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (fun z : Plane => tr.v s z) := by
  have h := tr.isTrain.smooth_v
  have hmap : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    contDiff_const.prodMk contDiff_id
  have h2 : ContDiffOn ℝ ∞ (fun z : Plane => tr.v s z) univ :=
    h.comp hmap.contDiffOn (fun z _ => ⟨hs, mem_univ z⟩)
  exact contDiffOn_univ.1 h2

/-- `S' = -u` at every age `s ≥ 0` (the proof of `TrainMeanV1` for `s ≥ 0`). -/
theorem bucVel_S_deriv {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (η : ℝ) :
    HasDerivAt (fun e : ℝ => meanStream tr s e)
      (-hmean c (fun z : Plane => tr.v s z 0) η) η := by
  have hψd : Differentiable ℝ (tr.ψ s) := tr.isTrain.stream_differentiable s hs
  have hvc : Continuous (fun z : Plane => tr.v s z) := (bucVel_vslice_contDiff tr hs).continuous
  have hv0 : Continuous (fun z : Plane => tr.v s z 0) := (PiLp.continuous_apply _ _ 0).comp hvc
  have hpart : ∀ q e : ℝ,
      HasDerivAt (fun y : ℝ => tr.ψ s (q, y)) (-(tr.v s (q, e) 0)) e := by
    intro q e
    have hpath : HasDerivAt (fun y : ℝ => ((q, y) : Plane)) ((0 : ℝ), (1 : ℝ)) e :=
      (hasDerivAt_const e q).prodMk (hasDerivAt_id e)
    have hdiffAt : DifferentiableAt ℝ (fun y : ℝ => tr.ψ s (q, y)) e :=
      (hψd (q, e)).comp e hpath.differentiableAt
    have hval : tr.v s (q, e) 0 = -deriv (fun y : ℝ => tr.ψ s (q, y)) e := by
      rw [tr.isTrain.stream s hs (q, e), toVec_zero]
      rfl
    rw [hval, neg_neg]
    exact hdiffAt.hasDerivAt
  have key := trainMeanV1_hasDerivAt_hmean (c := c) (f := tr.ψ s)
    (g := fun z : Plane => -(tr.v s z 0)) hψd.continuous hv0.neg hpart η
  have hneg : hmean c (fun z : Plane => -(tr.v s z 0)) η =
      -hmean c (fun z : Plane => tr.v s z 0) η :=
    trainMeanV1_hmean_neg c (fun z : Plane => tr.v s z 0) η
  rw [hneg] at key
  exact key

/-! ### The main theorem -/

/-- **`PartI:TC/3`. Decay of the mean velocity and its derivative** (BUC train, `s ≥ 0`). -/
theorem bucMeanVelDecay : BUCMeanVelDecay := by
  intro ν c hν hc tr hb s hs
  obtain ⟨M1, hM1'⟩ := hb.deriv_bound hs 1
  obtain ⟨M2, hM2'⟩ := hb.deriv_bound hs 2
  have hM1 : ∀ z : Plane, ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ ≤ M1 := fun z => hM1' s ⟨hs, le_rfl⟩ z
  have hM2 : ∀ z : Plane, ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ ≤ M2 := fun z => hM2' s ⟨hs, le_rfl⟩ z
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg _) (hM1 0)
  have hM2nn : 0 ≤ M2 := le_trans (norm_nonneg _) (hM2 0)
  -- smoothness of the velocity at age `s`
  have hV3 : ContDiff ℝ 3 (tr.v s) := (bucVel_vslice_contDiff tr hs).of_le (by simp)
  have hV2 : ContDiff ℝ 2 (fderiv ℝ (tr.v s)) := hV3.fderiv_right (by norm_num)
  have hV1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (tr.v s))) := hV2.fderiv_right (by norm_num)
  have hdiffV : Differentiable ℝ (tr.v s) := hV3.differentiable (by norm_num)
  have hdiffV1 : Differentiable ℝ (fderiv ℝ (tr.v s)) := hV2.differentiable (by norm_num)
  have hcontV0 : Continuous (tr.v s) := hV3.continuous
  have hcontV1 : Continuous (fderiv ℝ (tr.v s)) := hV2.continuous
  have hcontV2 : Continuous (fderiv ℝ (fderiv ℝ (tr.v s))) := hV1.continuous
  have hev1 : Continuous (fun A : Plane →L[ℝ] Vec => A ((0 : ℝ), (1 : ℝ))) :=
    (ContinuousLinearMap.apply ℝ Vec ((0 : ℝ), (1 : ℝ))).continuous
  have hev2 : Continuous
      (fun A : Plane →L[ℝ] (Plane →L[ℝ] Vec) => A ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))) :=
    (ContinuousLinearMap.apply ℝ Vec ((0 : ℝ), (1 : ℝ))).continuous.comp
      (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Vec) ((0 : ℝ), (1 : ℝ))).continuous
  -- the first and second `η`-derivatives of the first velocity component
  obtain ⟨G1, hG1⟩ : ∃ G : Plane → ℝ, ∀ z, G z = fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ)) 0 :=
    ⟨fun z => fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ)) 0, fun z => rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G : Plane → ℝ, ∀ z,
      G z = fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    ⟨fun z => fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ)) 0,
      fun z => rfl⟩
  have hcontG1 : Continuous G1 := by
    have e : G1 = fun z => fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ)) 0 := funext hG1
    rw [e]
    exact (PiLp.continuous_apply _ _ 0).comp (hev1.comp hcontV1)
  have hcontG2 : Continuous G2 := by
    have e : G2 = fun z => fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
      funext hG2
    rw [e]
    exact (PiLp.continuous_apply _ _ 0).comp (hev2.comp hcontV2)
  have hcont0 : Continuous (fun z : Plane => tr.v s z 0) :=
    (PiLp.continuous_apply _ _ 0).comp hcontV0
  have hpartV : ∀ q e : ℝ, HasDerivAt (fun y : ℝ => tr.v s (q, y))
      (fderiv ℝ (tr.v s) (q, e) ((0 : ℝ), (1 : ℝ))) e := by
    intro q e
    have hp : HasDerivAt (fun y : ℝ => ((q, y) : Plane)) ((0 : ℝ), (1 : ℝ)) e :=
      (hasDerivAt_const e q).prodMk (hasDerivAt_id e)
    exact (hdiffV (q, e)).hasFDerivAt.comp_hasDerivAt e hp
  have hpart0 : ∀ q e : ℝ, HasDerivAt (fun y : ℝ => tr.v s (q, y) 0) (G1 (q, e)) e := by
    intro q e
    rw [hG1]
    exact (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt e
      (hpartV q e)
  have hpartV1 : ∀ q e : ℝ, HasDerivAt (fun y : ℝ => fderiv ℝ (tr.v s) (q, y) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ (tr.v s)) (q, e) ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))) e := by
    intro q e
    have hp : HasDerivAt (fun y : ℝ => ((q, y) : Plane)) ((0 : ℝ), (1 : ℝ)) e :=
      (hasDerivAt_const e q).prodMk (hasDerivAt_id e)
    have hA : HasDerivAt (fun y : ℝ => fderiv ℝ (tr.v s) (q, y))
        (fderiv ℝ (fderiv ℝ (tr.v s)) (q, e) ((0 : ℝ), (1 : ℝ))) e :=
      (hdiffV1 (q, e)).hasFDerivAt.comp_hasDerivAt e hp
    exact (ContinuousLinearMap.apply ℝ Vec ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt e hA
  have hpartG1 : ∀ q e : ℝ, HasDerivAt (fun y : ℝ => G1 (q, y)) (G2 (q, e)) e := by
    intro q e
    have h := (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt e
      (hpartV1 q e)
    have e1 : (fun y : ℝ => G1 (q, y)) =
        fun y : ℝ => (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ)
          (fderiv ℝ (tr.v s) (q, y) ((0 : ℝ), (1 : ℝ))) :=
      funext fun y => hG1 _
    rw [e1, hG2 (q, e)]
    exact h
  -- the averaged derivatives
  have hu : ∀ η : ℝ, HasDerivAt (fun e : ℝ => hmean c (fun z : Plane => tr.v s z 0) e)
      (hmean c G1 η) η :=
    fun η => trainMeanV1_hasDerivAt_hmean (c := c) (f := fun z : Plane => tr.v s z 0) (g := G1)
      hcont0 hcontG1 hpart0 η
  have hu2 : ∀ η : ℝ, HasDerivAt (fun e : ℝ => hmean c G1 e) (hmean c G2 η) η :=
    fun η => trainMeanV1_hasDerivAt_hmean (c := c) (f := G1) (g := G2) hcontG1 hcontG2 hpartG1 η
  have hS : ∀ η : ℝ, HasDerivAt (fun e : ℝ => meanStream tr s e)
      (-hmean c (fun z : Plane => tr.v s z 0) η) η :=
    fun η => bucVel_S_deriv tr hs η
  -- pointwise bounds on the derivatives
  have hG1bd : ∀ z : Plane, |G1 z| ≤ M1 := by
    intro z
    rw [hG1 z]
    have h1 : |fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ)) 0| ≤
        ‖fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ))‖ := by
      have := PiLp.norm_apply_le (fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ))) 0
      simpa [Real.norm_eq_abs] using this
    have h2 : ‖fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ))‖ ≤
        ‖fderiv ℝ (tr.v s) z‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
      (fderiv ℝ (tr.v s) z).le_opNorm _
    have h3 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    have h4 : ‖fderiv ℝ (tr.v s) z‖ ≤ M1 := by
      rw [← norm_iteratedFDeriv_one]
      exact hM1 z
    rw [h3, mul_one] at h2
    linarith
  have hG2bd : ∀ z : Plane, |G2 z| ≤ M2 := by
    intro z
    rw [hG2 z]
    have h1 : |fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ)) 0| ≤
        ‖fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))‖ := by
      have := PiLp.norm_apply_le
        (fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))) 0
      simpa [Real.norm_eq_abs] using this
    have h2 : ‖fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))‖ ≤
        ‖fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ))‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
      (fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ))).le_opNorm _
    have h3 : ‖fderiv ℝ (fderiv ℝ (tr.v s)) z ((0 : ℝ), (1 : ℝ))‖ ≤
        ‖fderiv ℝ (fderiv ℝ (tr.v s)) z‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
      (fderiv ℝ (fderiv ℝ (tr.v s)) z).le_opNorm _
    have h4 : ‖fderiv ℝ (fderiv ℝ (tr.v s)) z‖ ≤ M2 := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hM2 z
    have h5 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    rw [h5, mul_one] at h2 h3
    linarith
  have hmeanG1 : ∀ η : ℝ, |hmean c G1 η| ≤ M1 :=
    fun η => bucVel_hmean_abs_le hc G1 η M1 (fun q => hG1bd _)
  -- `S` and its derivatives
  have hSdiff : Differentiable ℝ (fun e : ℝ => meanStream tr s e) := fun η => (hS η).differentiableAt
  have hSderiv : deriv (fun e : ℝ => meanStream tr s e) =
      fun e : ℝ => -hmean c (fun z : Plane => tr.v s z 0) e :=
    funext fun η => (hS η).deriv
  have hudiff : Differentiable ℝ (fun e : ℝ => hmean c (fun z : Plane => tr.v s z 0) e) :=
    fun η => (hu η).differentiableAt
  have hdS : Differentiable ℝ (deriv (fun e : ℝ => meanStream tr s e)) := by
    rw [hSderiv]
    exact hudiff.neg
  have hd2S : ∀ t : ℝ, |deriv (deriv (fun e : ℝ => meanStream tr s e)) t| ≤ M1 := by
    intro t
    rw [hSderiv, bucVel_deriv_neg, (hu t).deriv, abs_neg]
    exact bucVel_hmean_abs_le hc G1 t M1 (fun q => hG1bd _)
  -- Step (c): `u → 0`
  have hstep_c : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ η : ℝ, R ≤ η →
      |meanVel1 tr s η| < ε := by
    intro ε hε
    obtain ⟨h, m, hh, hm, hlt⟩ := bucVel_arith hε hM1nn
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.1
      (Metric.tendsto_nhds.1 (meanStreamDecay ν c hν hc tr s hs) m hm)
    refine ⟨R, fun η hη => ?_⟩
    have htail : ∀ t : ℝ, η ≤ t → |meanStream tr s t| ≤ m := by
      intro t ht
      have := hR t (le_trans hη ht)
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    have hlk := bucVel_lk hSdiff hdS hh hd2S htail
    rw [(hS η).deriv, abs_neg] at hlk
    show |hmean c (fun z : Plane => tr.v s z 0) η| < ε
    linarith
  have hu0 : Tendsto (meanVel1 tr s) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := hstep_c ε hε
    refine Filter.eventually_atTop.2 ⟨R, fun η hη => ?_⟩
    rw [Real.dist_eq, sub_zero]
    exact hR η hη
  -- Step (d): `u' → 0`
  have hfd_eq : ∀ η : ℝ, deriv (fun e : ℝ => -hmean c (fun z : Plane => tr.v s z 0) e) η =
      -hmean c G1 η := fun η => by
    rw [bucVel_deriv_neg, (hu η).deriv]
  have hdf_eq : deriv (fun e : ℝ => -hmean c (fun z : Plane => tr.v s z 0) e) =
      fun e : ℝ => -hmean c G1 e :=
    funext hfd_eq
  have hfdiff : Differentiable ℝ (fun e : ℝ => -hmean c (fun z : Plane => tr.v s z 0) e) :=
    hudiff.neg
  have hdf : Differentiable ℝ (deriv (fun e : ℝ => -hmean c (fun z : Plane => tr.v s z 0) e)) := by
    rw [hdf_eq]
    exact fun e : ℝ => (hu2 e).differentiableAt.neg
  have hd2 : ∀ t : ℝ, |deriv (deriv (fun e : ℝ => -hmean c (fun z : Plane => tr.v s z 0) e)) t|
      ≤ M2 := by
    intro t
    rw [hdf_eq, bucVel_deriv_neg, (hu2 t).deriv, abs_neg]
    exact bucVel_hmean_abs_le hc G2 t M2 (fun q => hG2bd _)
  have hstep_d : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ η : ℝ, R ≤ η → |hmean c G1 η| < ε := by
    intro ε hε
    obtain ⟨h, m, hh, hm, hlt⟩ := bucVel_arith hε hM2nn
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 (Metric.tendsto_nhds.1 hu0 m hm)
    refine ⟨R, fun η hη => ?_⟩
    have htail : ∀ t : ℝ, η ≤ t →
        |(fun e : ℝ => -hmean c (fun z : Plane => tr.v s z 0) e) t| ≤ m := by
      intro t ht
      have := hR t (le_trans hη ht)
      rw [Real.dist_eq, sub_zero] at this
      show |-hmean c (fun z : Plane => tr.v s z 0) t| ≤ m
      rw [abs_neg]
      exact this.le
    have hlk := bucVel_lk hfdiff hdf hh hd2 htail
    rw [hfd_eq, abs_neg] at hlk
    linarith
  have hderivu : ∀ η : ℝ, deriv (meanVel1 tr s) η = hmean c G1 η := fun η => (hu η).deriv
  refine ⟨hu0, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ := hstep_d ε hε
  refine Filter.eventually_atTop.2 ⟨R, fun η hη => ?_⟩
  show dist (deriv (meanVel1 tr s) η) 0 < ε
  rw [Real.dist_eq, sub_zero, hderivu η]
  exact hR η hη

end UnforcedLeray.Short.PartI
