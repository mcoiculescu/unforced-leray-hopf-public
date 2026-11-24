import UnforcedLeray.Lib.HeatR3.Admissible

/-!
# Smoothness of the heat flow of admissible data (INF04 T8, `contDiff_average`)


`contDiff_average`. The heat flow of an admissible field (tex 5205–5216, B0697, B0707) is
`C^∞` in space at every positive time. Mathlib's convolution smoothness lemmas need compact
support (`Analysis/Calculus/ContDiff/Convolution.lean`), so they do not apply to the Gaussian;
this file differentiates under the integral instead (scoping note §3).

The device is a kernel convolution with a bilinear pairing,
`kconv B K g x = ∫ B (K(x - y)) (g y) dy`, for a smooth kernel `K` all of whose derivatives decay
like `(1 + |z|)^{-m}` (`DecayKernel m K`) and a field with `(1 + |y|)^{-m}|g| ∈ L¹`. Its
derivative is again such a convolution, with kernel `DK` and pairing `B.precompL` — so
induction on the order gives `C^n` for every `n`.

Main results:
* `DecayKernel`, `DecayKernel.fderiv`, `decayKernel_gaussKernel`;
* `hasFDerivAt_kconv`, `contDiff_kconv`;
* `average_eq_kconv`, `contDiff_average` (`C^∞`, so in particular the scoping note's `C²`),
  `hasFDerivAt_average'` (`D e^{θΔ}f = ∫ DG_θ(x - y) ⊗ f(y) dy`).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Gaussian (Euc gaussKernel)

universe u v w

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth kernel on `ℝ³` all of whose derivatives decay like `(1 + |z|)^{-m}`. -/
structure DecayKernel {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℝ)
    (K : Space → V) : Prop where
  smooth : ContDiff ℝ ∞ K
  decay : ∀ n : ℕ, ∃ C : ℝ, ∀ z : Space, ‖iteratedFDeriv ℝ n K z‖ ≤ C * (1 + ‖z‖) ^ (-m)

theorem DecayKernel.fderiv {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℝ}
    {K : Space → V} (hK : DecayKernel m K) : DecayKernel m (fderiv ℝ K) where
  smooth := (contDiff_infty_iff_fderiv.mp hK.smooth).2
  decay n := by
    obtain ⟨C, hC⟩ := hK.decay (n + 1)
    exact ⟨C, fun z => by rw [norm_iteratedFDeriv_fderiv]; exact hC z⟩

theorem DecayKernel.norm_le {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℝ}
    {K : Space → V} (hK : DecayKernel m K) : ∃ C : ℝ, ∀ z : Space, ‖K z‖ ≤ C * (1 + ‖z‖) ^ (-m) := by
  obtain ⟨C, hC⟩ := hK.decay 0
  exact ⟨C, fun z => by simpa only [norm_iteratedFDeriv_zero] using hC z⟩

/-- The heat kernel is a `DecayKernel` for every `m ≥ 0` (`θ > 0`). -/
theorem decayKernel_gaussKernel {θ : ℝ} (hθ : 0 < θ) {m : ℝ} (hm : 0 ≤ m) :
    DecayKernel m (kernel θ) := by
  rw [← Gaussian.gaussKernel_three_eq]
  refine ⟨Gaussian.contDiff_gaussKernel θ, fun n => ?_⟩
  obtain ⟨C, _, hC⟩ := norm_iteratedFDeriv_gaussKernel_le_weight 3 n hθ hm
  exact ⟨C, hC⟩

/-- The kernel convolution `x ↦ ∫ B (K(x - y)) (g y) dy`. -/
def kconv {V : Type u} {W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (B : V →L[ℝ] E →L[ℝ] W) (K : Space → V)
    (g : Space → E) (x : Space) : W :=
  ∫ y : Space, B (K (x - y)) (g y)

section Kconv

variable {V : Type u} {W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- The pointwise bound of the kconv integrand. -/
theorem norm_kconv_integrand_le (B : V →L[ℝ] E →L[ℝ] W) {K : Space → V} {m C : ℝ}
    (hm : 0 ≤ m) (hC : ∀ z, ‖K z‖ ≤ C * (1 + ‖z‖) ^ (-m)) (g : Space → E) (x y : Space) :
    ‖B (K (x - y)) (g y)‖ ≤
      ‖B‖ * C * (1 + ‖x‖) ^ m * ((1 + ‖y‖) ^ (-m) * ‖g y‖) := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos (by positivity) _)
  calc ‖B (K (x - y)) (g y)‖ ≤ ‖B‖ * ‖K (x - y)‖ * ‖g y‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * (C * ((1 + ‖x‖) ^ m * (1 + ‖y‖) ^ (-m))) * ‖g y‖ := by
        gcongr
        exact (hC _).trans (mul_le_mul_of_nonneg_left
          (one_add_norm_sub_rpow_neg_le hm x y) hC0)
    _ = ‖B‖ * C * (1 + ‖x‖) ^ m * ((1 + ‖y‖) ^ (-m) * ‖g y‖) := by ring

theorem integrable_kconv_integrand (B : V →L[ℝ] E →L[ℝ] W) {K : Space → V} {m C : ℝ}
    (hm : 0 ≤ m) (hKc : Continuous K) (hC : ∀ z, ‖K z‖ ≤ C * (1 + ‖z‖) ^ (-m)) {g : Space → E}
    (hg : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-m) * ‖g y‖)) (x : Space) :
    Integrable (fun y : Space => B (K (x - y)) (g y)) := by
  refine (hgi.const_mul (‖B‖ * C * (1 + ‖x‖) ^ m)).mono'
    (B.aestronglyMeasurable_comp₂
      (hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable hg)
    (Eventually.of_forall fun y => ?_)
  exact norm_kconv_integrand_le B hm hC g x y

/-- **Differentiation under the integral.** For a `DecayKernel` `K` and `(1+|y|)^{-m}g ∈ L¹`,
`D(kconv B K g)(x) = kconv (B.precompL ℝ³) (DK) g x`. -/
theorem hasFDerivAt_kconv (B : V →L[ℝ] E →L[ℝ] W) {K : Space → V} {m : ℝ} (hm : 0 ≤ m)
    (hK : DecayKernel m K) {g : Space → E} (hg : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-m) * ‖g y‖)) (x : Space) :
    HasFDerivAt (kconv B K g) (kconv (B.precompL Space) (fderiv ℝ K) g x) x := by
  obtain ⟨C₀, hC₀⟩ := hK.norm_le
  obtain ⟨C₁, hC₁⟩ := hK.fderiv.norm_le
  have hKc : Continuous K := hK.smooth.continuous
  have hK'c : Continuous (fderiv ℝ K) := hK.fderiv.smooth.continuous
  have hKd : Differentiable ℝ K := hK.smooth.differentiable (by simp)
  set B' := B.precompL Space with hB'
  have hC₁0 : 0 ≤ C₁ := by
    have := (norm_nonneg _).trans (hC₁ 0)
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos (by positivity) _)
  set c : ℝ := ‖B‖ * C₁ * (2 + ‖x‖) ^ m with hc
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := (volume : Measure Space))
    (F := fun x' y => B (K (x' - y)) (g y))
    (F' := fun x' y => B' (fderiv ℝ K (x' - y)) (g y))
    (bound := fun y => c * ((1 + ‖y‖) ^ (-m) * ‖g y‖))
    (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun x' =>
      (integrable_kconv_integrand B hm hKc hC₀ hg hgi x').1)
    (integrable_kconv_integrand B hm hKc hC₀ hg hgi x)
    (integrable_kconv_integrand B' hm hK'c hC₁ hg hgi x).1
    (Eventually.of_forall fun y x' hx' => ?_)
    (hgi.const_mul _)
    (Eventually.of_forall fun y x' _ => ?_)
  · refine (norm_kconv_integrand_le B' hm hC₁ g x' y).trans ?_
    have hx'x : ‖x'‖ ≤ 1 + ‖x‖ := by
      have := Metric.mem_ball.mp hx'
      rw [dist_eq_norm] at this
      calc ‖x'‖ = ‖(x' - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖x' - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ 1 + ‖x‖ := by linarith
    have h1 : (1 + ‖x'‖) ^ m ≤ (2 + ‖x‖) ^ m :=
      Real.rpow_le_rpow (by positivity) (by linarith) hm
    have h2 : 0 ≤ (1 + ‖y‖) ^ (-m) * ‖g y‖ :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
    rw [hc]
    gcongr
    rw [hB']
    exact ContinuousLinearMap.norm_precompL_le Space B
  · have h1 : HasFDerivAt (fun z : Space => z - y) (ContinuousLinearMap.id ℝ Space) x' :=
      (hasFDerivAt_id x').sub_const y
    have h2 : HasFDerivAt (fun z : Space => K (z - y)) (fderiv ℝ K (x' - y)) x' := by
      have h := (hKd (x' - y)).hasFDerivAt.comp x' h1
      rwa [ContinuousLinearMap.comp_id] at h
    have h3 := (B.flip (g y)).hasFDerivAt.comp x' h2
    have h4 : B' (fderiv ℝ K (x' - y)) (g y) = (B.flip (g y)).comp (fderiv ℝ K (x' - y)) := by
      ext h; simp [hB']
    rw [h4]
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
    simp

/-- **`C^n` regularity of kernel convolutions**, by induction on `n` (the pairing and the
kernel change at each step). -/
theorem contDiff_kconv {m : ℝ} (hm : 0 ≤ m) {g : Space → E} (hg : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-m) * ‖g y‖)) (n : ℕ) :
    ∀ {V : Type u} {W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (B : V →L[ℝ] E →L[ℝ] W) (K : Space → V), DecayKernel m K →
      ContDiff ℝ n (kconv B K g) := by
  induction n with
  | zero =>
    intro V W _ _ _ _ _ B K hK
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasFDerivAt_kconv B hm hK hg hgi x).continuousAt
  | succ n ih =>
    intro V W _ _ _ _ _ B K hK
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
    exact ⟨kconv (B.precompL Space) (fderiv ℝ K) g, ih _ _ hK.fderiv,
      fun x => hasFDerivAt_kconv B hm hK hg hgi x⟩

/-- `fderiv` of a kernel convolution is the kernel convolution of the derivative kernel. -/
theorem fderiv_kconv (B : V →L[ℝ] E →L[ℝ] W) {K : Space → V} {m : ℝ} (hm : 0 ≤ m)
    (hK : DecayKernel m K) {g : Space → E} (hg : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-m) * ‖g y‖)) :
    fderiv ℝ (kconv B K g) = kconv (B.precompL Space) (fderiv ℝ K) g :=
  funext fun x => (hasFDerivAt_kconv B hm hK hg hgi x).fderiv

/-- Directional derivative of a kernel convolution, kernel side:
`D(kconv B K g)(x) w = kconv B (DK(·) w) g x`. -/
theorem fderiv_kconv_apply (B : V →L[ℝ] E →L[ℝ] W) {K : Space → V} {m : ℝ} (hm : 0 ≤ m)
    (hK : DecayKernel m K) {g : Space → E} (hg : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-m) * ‖g y‖)) (x w : Space) :
    fderiv ℝ (kconv B K g) x w = kconv B (fun z => fderiv ℝ K z w) g x := by
  rw [fderiv_kconv B hm hK hg hgi]
  simp only [kconv]
  set B' := B.precompL Space with hB'
  obtain ⟨C₁, hC₁⟩ := hK.fderiv.norm_le
  have hi := integrable_kconv_integrand B' hm hK.fderiv.smooth.continuous hC₁ hg hgi x
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

/-- Directional derivatives of a `DecayKernel` are `DecayKernel`s. -/
theorem DecayKernel.fderiv_apply {K : Space → V} {m : ℝ} (hK : DecayKernel m K) (w : Space) :
    DecayKernel m (fun z => _root_.fderiv ℝ K z w) where
  smooth := (ContinuousLinearMap.apply ℝ V w).contDiff.comp hK.fderiv.smooth
  decay n := by
    obtain ⟨C, hC⟩ := hK.fderiv.decay n
    refine ⟨‖ContinuousLinearMap.apply ℝ V w‖ * C, fun z => ?_⟩
    have h := (ContinuousLinearMap.apply ℝ V w).norm_iteratedFDeriv_comp_left
      (f := _root_.fderiv ℝ K) (x := z) (N := ∞) (n := n) hK.fderiv.smooth.contDiffAt
      (by exact_mod_cast le_top)
    refine h.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)

/-- Second derivatives of a kernel convolution, kernel side:
`D²(kconv B K g)(x)(v, w) = kconv B (D²K(·)(v, w)) g x`. -/
theorem fderiv_fderiv_kconv_apply (B : V →L[ℝ] E →L[ℝ] W) {K : Space → V} {m : ℝ} (hm : 0 ≤ m)
    (hK : DecayKernel m K) {g : Space → E} (hg : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-m) * ‖g y‖)) (x v w : Space) :
    fderiv ℝ (fderiv ℝ (kconv B K g)) x v w =
      kconv B (fun z => fderiv ℝ (fderiv ℝ K) z v w) g x := by
  have hdiff : Differentiable ℝ (fderiv ℝ (kconv B K g)) := by
    rw [fderiv_kconv B hm hK hg hgi]
    exact fun x' => (hasFDerivAt_kconv _ hm hK.fderiv hg hgi x').differentiableAt
  have h1 : fderiv ℝ (fderiv ℝ (kconv B K g)) x v w =
      fderiv ℝ (fun x' => fderiv ℝ (kconv B K g) x' w) x v := by
    rw [fderiv_clm_apply (hdiff x) (differentiableAt_const _)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.flip_apply]
  have h2 : (fun x' => fderiv ℝ (kconv B K g) x' w) = kconv B (fun z => fderiv ℝ K z w) g :=
    funext fun x' => fderiv_kconv_apply B hm hK hg hgi x' w
  rw [h1, h2, fderiv_kconv_apply B hm (hK.fderiv_apply w) hg hgi x v]
  congr 1
  funext z
  have hdK : DifferentiableAt ℝ (fderiv ℝ K) z := hK.fderiv.smooth.differentiable (by simp) z
  rw [fderiv_clm_apply hdK (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.flip_apply]

/-- The integrand bound `‖B (K(x-y)) (g y)‖ ≤ ‖B‖ ‖K(x-y)‖ ‖g y‖` is integrable. -/
theorem integrable_kconv_norm_bound {K : Space → V} {m : ℝ} (hm : 0 ≤ m)
    (hK : DecayKernel m K) {g : Space → E} (hg : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-m) * ‖g y‖)) (x : Space) :
    Integrable (fun y : Space => ‖K (x - y)‖ * ‖g y‖) := by
  obtain ⟨C, hC⟩ := hK.norm_le
  have h := integrable_kconv_integrand (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    hm (hK.smooth.continuous.norm) (C := C) (fun z => by rw [norm_norm]; exact hC z)
    hg.norm (by simpa only [norm_norm] using hgi) x
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- **Kernel-side bound for every derivative of a kernel convolution:**
`‖D^j (kconv B K g)(x)‖ ≤ ‖B‖ ∫ ‖D^j K(x - y)‖ ‖g y‖ dy`. -/
theorem norm_iteratedFDeriv_kconv_le {m : ℝ} (hm : 0 ≤ m) {g : Space → E}
    (hg : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-m) * ‖g y‖)) (j : ℕ) :
    ∀ {V : Type u} {W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (B : V →L[ℝ] E →L[ℝ] W) (K : Space → V), DecayKernel m K → ∀ x : Space,
      ‖iteratedFDeriv ℝ j (kconv B K g) x‖ ≤
        ‖B‖ * ∫ y : Space, ‖iteratedFDeriv ℝ j K (x - y)‖ * ‖g y‖ := by
  induction j with
  | zero =>
    intro V W _ _ _ _ _ B K hK x
    simp only [norm_iteratedFDeriv_zero, kconv]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
      ((integrable_kconv_norm_bound hm hK hg hgi x).const_mul ‖B‖)
      (Eventually.of_forall fun y => ?_)
    calc ‖B (K (x - y)) (g y)‖ ≤ ‖B‖ * ‖K (x - y)‖ * ‖g y‖ := B.le_opNorm₂ _ _
      _ = ‖B‖ * (‖K (x - y)‖ * ‖g y‖) := by ring
  | succ j ih =>
    intro V W _ _ _ _ _ B K hK x
    rw [← norm_iteratedFDeriv_fderiv, fderiv_kconv B hm hK hg hgi]
    refine (ih (B.precompL Space) (fderiv ℝ K) hK.fderiv x).trans ?_
    simp_rw [norm_iteratedFDeriv_fderiv]
    have hI : 0 ≤ ∫ y : Space, ‖iteratedFDeriv ℝ (j + 1) K (x - y)‖ * ‖g y‖ :=
      integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_precompL_le Space B) hI

end Kconv

/-- The heat integral as a kernel convolution: `e^{θΔ}f = kconv (lsmul) G_θ f`. -/
theorem average_eq_kconv (θ : ℝ) (f : Space → E) :
    average θ f = kconv (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) (kernel θ) f := by
  funext x
  simp only [average, kconv, ContinuousLinearMap.lsmul_apply]
  exact (integral_sub_left_eq_self (fun y : Space => kernel θ y • f (x - y)) volume x).symm.trans
    (by simp only [sub_sub_cancel])

theorem HeatAdmissible.integrable_norm {f : Space → E} (hf : HeatAdmissible f) :
    ∃ m : ℕ, Integrable (fun y : Space => (1 + ‖y‖) ^ (-(m : ℝ)) * ‖f y‖) := by
  obtain ⟨_, m, hm⟩ := hf
  refine ⟨m, hm.norm.congr (Eventually.of_forall fun y => ?_)⟩
  simp only [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖) _)]

/-- **INF04 T8 `contDiff_average`.** The heat flow of an admissible field is `C^∞` in space at
every positive time (the scoping note asks for `C²`). -/
theorem contDiff_average {f : Space → E} (hf : HeatAdmissible f) {θ : ℝ} (hθ : 0 < θ) :
    ContDiff ℝ ∞ (average θ f) := by
  obtain ⟨m, hm⟩ := hf.integrable_norm
  rw [average_eq_kconv, contDiff_infty]
  intro n
  exact contDiff_kconv (by positivity) hf.1 hm n _ _ (decayKernel_gaussKernel hθ (by positivity))

/-- First derivative of the heat flow of admissible data, kernel side:
`D(e^{θΔ}f)(x) = ∫ DG_θ(x - y) ⊗ f(y) dy` (as `kconv` with the pairing `lsmul.precompL`). -/
theorem hasFDerivAt_average' {f : Space → E} (hf : HeatAdmissible f) {θ : ℝ} (hθ : 0 < θ)
    (x : Space) :
    HasFDerivAt (average θ f)
      (kconv ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).precompL Space)
        (fderiv ℝ (kernel θ)) f x) x := by
  obtain ⟨m, hm⟩ := hf.integrable_norm
  rw [average_eq_kconv]
  exact hasFDerivAt_kconv _ (by positivity) (decayKernel_gaussKernel hθ (by positivity)) hf.1 hm x

/-- **Kernel-side bound for every derivative of the heat flow of admissible data:**
`‖D^j e^{θΔ}f(x)‖ ≤ ∫ ‖D^j G_θ(x - y)‖ ‖f(y)‖ dy`, every `j`, `θ > 0`. -/
theorem norm_iteratedFDeriv_average_le_kernel {f : Space → E} (hf : HeatAdmissible f) {θ : ℝ}
    (hθ : 0 < θ) (j : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ j (average θ f) x‖ ≤
      ∫ y : Space, ‖iteratedFDeriv ℝ j (kernel θ) (x - y)‖ * ‖f y‖ := by
  obtain ⟨m, hm⟩ := hf.integrable_norm
  rw [average_eq_kconv]
  refine (norm_iteratedFDeriv_kconv_le (by positivity) hf.1 hm j _ _
    (decayKernel_gaussKernel hθ (by positivity)) x).trans ?_
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  have hI : 0 ≤ ∫ y : Space, ‖iteratedFDeriv ℝ j (kernel θ) (x - y)‖ * ‖f y‖ :=
    integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc _ ≤ 1 * ∫ y : Space, ‖iteratedFDeriv ℝ j (kernel θ) (x - y)‖ * ‖f y‖ := by gcongr
    _ = _ := one_mul _

end UnforcedLeray.Heat
