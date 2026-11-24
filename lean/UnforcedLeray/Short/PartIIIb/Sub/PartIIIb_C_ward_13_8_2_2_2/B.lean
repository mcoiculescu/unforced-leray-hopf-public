import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2.L1
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# `PartIII-b:C/ward/13/8/2/2/2/2`: Poincare on the conical pieces (transfer step)

Source `the November 2 reference manuscript`
117-118, 2641-2642. This file proves the generic transfer lemma `bg_transfer`: if a `C^1` map
`Psi` is injective on a compact convex `W` of positive volume, has `|det D Psi|` between `c1` and
`c2` on `W`, and `||D Psi|| <= L` on `W`, then `PoincOn (Psi '' W)` follows from `ConvexPoincare`
on `W`. The concrete maps for the six cones are NOT in this file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain

abbrev BgSp := UnforcedLeray.Space

lemma bg_coord_norm (j : Fin 3) : ‖UnforcedLeray.coordinateVector j‖ = 1 := by
  simp [UnforcedLeray.coordinateVector]

/-- Gradient of a composition: `|grad (p o Psi)|^2 <= 3 L^2 |grad p (Psi z)|^2` when `||D Psi|| <= L`. -/
lemma bg_physGrad_comp_le (Ψ : BgSp → BgSp) (hΨ : ContDiff ℝ 1 Ψ) (p : BgSp → ℝ)
    (hp : ContDiff ℝ 1 p) (z : BgSp) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ v, ‖fderiv ℝ Ψ z v‖ ≤ L * ‖v‖) :
    ‖physGrad (p ∘ Ψ) z‖ ^ 2 ≤
      3 * L ^ 2 * ‖physGrad p (Ψ z)‖ ^ 2 := by
  have hcomp : ∀ j : Fin 3, physGrad (p ∘ Ψ) z j =
      inner ℝ (physGrad p (Ψ z)) (fderiv ℝ Ψ z (UnforcedLeray.coordinateVector j)) := by
    intro j
    unfold physGrad
    rw [fderiv_comp z (hp.differentiable one_ne_zero (Ψ z)) (hΨ.differentiable one_ne_zero z)]
    simp only [ContinuousLinearMap.comp_apply]
    exact UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.CP.fderiv_apply_eq_inner_physGrad p _ _
  have hbound : ∀ j : Fin 3, (physGrad (p ∘ Ψ) z j) ^ 2 ≤
      L ^ 2 * ‖physGrad p (Ψ z)‖ ^ 2 := by
    intro j
    rw [hcomp j]
    have h1 := abs_real_inner_le_norm (physGrad p (Ψ z))
      (fderiv ℝ Ψ z (UnforcedLeray.coordinateVector j))
    have h2 : ‖fderiv ℝ Ψ z (UnforcedLeray.coordinateVector j)‖ ≤ L := by
      have := hL (UnforcedLeray.coordinateVector j)
      rwa [bg_coord_norm j, mul_one] at this
    have h3 : |inner ℝ (physGrad p (Ψ z)) (fderiv ℝ Ψ z (UnforcedLeray.coordinateVector j))| ≤
        L * ‖physGrad p (Ψ z)‖ := by
      calc _ ≤ ‖physGrad p (Ψ z)‖ * ‖fderiv ℝ Ψ z (UnforcedLeray.coordinateVector j)‖ := h1
        _ ≤ ‖physGrad p (Ψ z)‖ * L := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = L * ‖physGrad p (Ψ z)‖ := mul_comm _ _
    calc (inner ℝ (physGrad p (Ψ z)) (fderiv ℝ Ψ z (UnforcedLeray.coordinateVector j))) ^ 2
        = |inner ℝ (physGrad p (Ψ z)) (fderiv ℝ Ψ z (UnforcedLeray.coordinateVector j))| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (L * ‖physGrad p (Ψ z)‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = L ^ 2 * ‖physGrad p (Ψ z)‖ ^ 2 := by ring
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [hbound 0, hbound 1, hbound 2]

/-- Generic transfer: Poincare on `Psi '' W` from Poincare on the convex set `W`. -/
theorem bg_transfer (W S : Set BgSp) (Ψ : BgSp → BgSp) (hWconv : Convex ℝ W)
    (hWc : IsCompact W) (hWv : 0 < (volume W).toReal) (hΨ : ContDiff ℝ 1 Ψ)
    (hinj : Set.InjOn Ψ W) (himg : Ψ '' W = S)
    (L c₁ c₂ : ℝ) (hL0 : 0 ≤ L) (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hL : ∀ z ∈ W, ∀ v, ‖fderiv ℝ Ψ z v‖ ≤ L * ‖v‖)
    (hdet : ∀ z ∈ W, c₁ ≤ |ContinuousLinearMap.det (fderiv ℝ Ψ z)| ∧
      |ContinuousLinearMap.det (fderiv ℝ Ψ z)| ≤ c₂) :
    PoincOn S := by
  obtain ⟨Cw, hCw⟩ := convexPoincare W
    hWconv hWc hWv
  have hfd : ∀ z ∈ W, HasFDerivWithinAt Ψ (fderiv ℝ Ψ z) W z := fun z _ =>
    (hΨ.differentiable one_ne_zero z).hasFDerivAt.hasFDerivWithinAt
  have hdetc : Continuous fun z => |ContinuousLinearMap.det (fderiv ℝ Ψ z)| :=
    (ContinuousLinearMap.continuous_det.comp (hΨ.continuous_fderiv one_ne_zero)).abs
  have hcov : ∀ g : BgSp → ℝ, ∫ y in S, g y =
      ∫ z in W, |ContinuousLinearMap.det (fderiv ℝ Ψ z)| * g (Ψ z) := by
    intro g
    rw [← himg, integral_image_eq_integral_abs_det_fderiv_smul volume hWc.measurableSet hfd hinj g]
    simp only [smul_eq_mul]
  refine ⟨3 * L ^ 2 * c₂ * max Cw 0 / c₁, fun p hp => ?_⟩
  have hpΨ : ContDiff ℝ 1 (p ∘ Ψ) := hp.comp hΨ
  obtain ⟨m, hm⟩ := hCw (p ∘ Ψ) hpΨ
  refine ⟨m, ?_⟩
  have hcontG : ∀ f : BgSp → ℝ, Continuous f → IntegrableOn f W := fun f hf =>
    hf.continuousOn.integrableOn_compact hWc
  have hcontgrad : Continuous fun z => ‖physGrad p z‖ ^ 2 :=
    ((UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.CP.continuous_physGrad hp).norm).pow 2
  have hcontpsi : Continuous fun z => ‖physGrad p (Ψ z)‖ ^ 2 :=
    hcontgrad.comp hΨ.continuous
  have hcontq : Continuous fun z => (p (Ψ z) - m) ^ 2 :=
    ((hp.continuous.comp hΨ.continuous).sub continuous_const).pow 2
  -- Step 1: the left side pulled back, bounded by c2 times the integral over W
  have hS1 : ∫ y in S, (p y - m) ^ 2 = ∫ z in W, |ContinuousLinearMap.det (fderiv ℝ Ψ z)| *
      (p (Ψ z) - m) ^ 2 := hcov (fun y => (p y - m) ^ 2)
  have hA : ∫ z in W, |ContinuousLinearMap.det (fderiv ℝ Ψ z)| * (p (Ψ z) - m) ^ 2 ≤
      c₂ * ∫ z in W, (p (Ψ z) - m) ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on ((hdetc.mul hcontq).continuousOn.integrableOn_compact hWc)
      ((hcontq.continuousOn.integrableOn_compact hWc).const_mul c₂) hWc.measurableSet
    intro z hz
    exact mul_le_mul_of_nonneg_right (hdet z hz).2 (sq_nonneg _)
  -- Step 2: Poincare on W for q = p o Psi
  have hY : ∫ z in W, (p (Ψ z) - m) ^ 2 ≤ max Cw 0 * ∫ z in W, ‖physGrad (p ∘ Ψ) z‖ ^ 2 := by
    have hZ0 : 0 ≤ ∫ z in W, ‖physGrad (p ∘ Ψ) z‖ ^ 2 :=
      setIntegral_nonneg hWc.measurableSet (fun z _ => by positivity)
    exact (hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hZ0))
  -- Step 3: gradient of q against gradient of p on the image
  have hcontLHS : Continuous fun z => ‖physGrad (p ∘ Ψ) z‖ ^ 2 :=
    ((UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.CP.continuous_physGrad hpΨ).norm).pow 2
  have hB : ∫ z in W, ‖physGrad (p ∘ Ψ) z‖ ^ 2 ≤
      3 * L ^ 2 * ∫ z in W, ‖physGrad p (Ψ z)‖ ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hcontLHS.continuousOn.integrableOn_compact hWc)
      ((hcontpsi.continuousOn.integrableOn_compact hWc).const_mul _) hWc.measurableSet
    intro z _
    exact bg_physGrad_comp_le Ψ hΨ p hp z L hL0 (hL z ‹_›)
  -- Step 4: lower bound of the image gradient integral by the integral over S
  have hG : ∫ y in S, ‖physGrad p y‖ ^ 2 =
      ∫ z in W, |ContinuousLinearMap.det (fderiv ℝ Ψ z)| * ‖physGrad p (Ψ z)‖ ^ 2 :=
    hcov (fun y => ‖physGrad p y‖ ^ 2)
  have hC : c₁ * ∫ z in W, ‖physGrad p (Ψ z)‖ ^ 2 ≤ ∫ y in S, ‖physGrad p y‖ ^ 2 := by
    rw [hG, ← integral_const_mul]
    apply setIntegral_mono_on ((hcontpsi.continuousOn.integrableOn_compact hWc).const_mul _)
      ((hdetc.mul hcontpsi).continuousOn.integrableOn_compact hWc) hWc.measurableSet
    intro z hz
    exact mul_le_mul_of_nonneg_right (hdet z hz).1 (by positivity)
  have hX : ∫ z in W, ‖physGrad p (Ψ z)‖ ^ 2 ≤ (∫ y in S, ‖physGrad p y‖ ^ 2) / c₁ := by
    rw [le_div_iff₀ hc₁, mul_comm]
    exact hC
  have hmax0 : 0 ≤ max Cw 0 := le_max_right _ _
  calc ∫ y in S, (p y - m) ^ 2
      = ∫ z in W, |ContinuousLinearMap.det (fderiv ℝ Ψ z)| * (p (Ψ z) - m) ^ 2 := hS1
    _ ≤ c₂ * ∫ z in W, (p (Ψ z) - m) ^ 2 := hA
    _ ≤ c₂ * (max Cw 0 * ∫ z in W, ‖physGrad (p ∘ Ψ) z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hY hc₂
    _ ≤ c₂ * (max Cw 0 * (3 * L ^ 2 * ∫ z in W, ‖physGrad p (Ψ z)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hmax0) hc₂
    _ ≤ c₂ * (max Cw 0 * (3 * L ^ 2 * ((∫ y in S, ‖physGrad p y‖ ^ 2) / c₁))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hX (by positivity)) hmax0) hc₂
    _ = 3 * L ^ 2 * c₂ * max Cw 0 / c₁ * ∫ y in S, ‖physGrad p y‖ ^ 2 := by ring

/-- positive smooth `rho` with `rho x = x` for `x ≥ 1/8`. -/
def cpRho (x : ℝ) : ℝ := 1 / 16 + Real.smoothTransition (16 * x - 1) * (x - 1 / 16)

lemma cpRho_ge (x : ℝ) : 1 / 16 ≤ cpRho x := by
  unfold cpRho
  by_cases hx : x ≤ 1 / 16
  · have : Real.smoothTransition (16 * x - 1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [this]; linarith
  · push Not at hx
    have := Real.smoothTransition.nonneg (16 * x - 1)
    nlinarith

lemma cpRho_eq (x : ℝ) (hx : 1 / 8 ≤ x) : cpRho x = x := by
  unfold cpRho
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring

lemma cpRho_contDiff : ContDiff ℝ 1 cpRho := by
  unfold cpRho
  have h := (Real.smoothTransition.contDiff (n := 1)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const : ContDiff ℝ 1 fun x : ℝ => 16 * x - 1)
  exact contDiff_const.add (h.mul (contDiff_id.sub contDiff_const))

/-- C^1 extension of `sqrt` from `[1/8, ∞)` to `ℝ`. -/
def cpG (x : ℝ) : ℝ := Real.sqrt (cpRho x)

lemma cpG_contDiff : ContDiff ℝ 1 cpG := by
  unfold cpG
  refine ContDiff.sqrt cpRho_contDiff (fun x => ?_)
  have := cpRho_ge x
  linarith

lemma cpG_eq (x : ℝ) (hx : 1 / 8 ≤ x) : cpG x = Real.sqrt x := by
  unfold cpG; rw [cpRho_eq x hx]

lemma cpG_hasDerivAt (x : ℝ) (hx : 1 / 8 < x) :
    HasDerivAt cpG (1 / (2 * Real.sqrt x)) x := by
  have h := Real.hasDerivAt_sqrt (x := x) (by linarith)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact cpG_eq y (le_of_lt hy)

abbrev cpE2 : UnforcedLeray.Space := EuclideanSpace.single 2 1

def cpF (w : UnforcedLeray.Space) : ℝ := w 2 ^ 2 - w 0 ^ 2 - w 1 ^ 2

def cpPsi (s : ℝ) (w : UnforcedLeray.Space) : UnforcedLeray.Space :=
  w + (s * cpG (cpF w) - w 2) • cpE2

lemma cpProj_contDiff (i : Fin 3) : ContDiff ℝ 1 fun w : UnforcedLeray.Space => w i :=
  (EuclideanSpace.proj i : UnforcedLeray.Space →L[ℝ] ℝ).contDiff

lemma cpF_contDiff : ContDiff ℝ 1 cpF := by
  unfold cpF
  exact (((cpProj_contDiff 2).pow 2).sub ((cpProj_contDiff 0).pow 2)).sub
    ((cpProj_contDiff 1).pow 2)

lemma cpPsi_contDiff (s : ℝ) : ContDiff ℝ 1 (cpPsi s) := by
  unfold cpPsi
  exact contDiff_id.add (((contDiff_const.mul (cpG_contDiff.comp cpF_contDiff)).sub
    (cpProj_contDiff 2)).smul contDiff_const)

lemma cpPsi_apply0 (s : ℝ) (w : UnforcedLeray.Space) : cpPsi s w 0 = w 0 := by
  simp [cpPsi, cpE2, PiLp.single_apply]

lemma cpPsi_apply1 (s : ℝ) (w : UnforcedLeray.Space) : cpPsi s w 1 = w 1 := by
  simp [cpPsi, cpE2, PiLp.single_apply]

lemma cpPsi_apply2 (s : ℝ) (w : UnforcedLeray.Space) : cpPsi s w 2 = s * cpG (cpF w) := by
  simp [cpPsi, cpE2, PiLp.single_apply]

/-- The derivative formula, components. -/
lemma cpPsi_fderiv (s : ℝ) (w : UnforcedLeray.Space) (hF : 1 / 8 < cpF w) (v : UnforcedLeray.Space) :
    fderiv ℝ (cpPsi s) w v 0 = v 0 ∧ fderiv ℝ (cpPsi s) w v 1 = v 1 ∧
    fderiv ℝ (cpPsi s) w v 2 =
      s * (1 / Real.sqrt (cpF w)) * (w 2 * v 2 - w 0 * v 0 - w 1 * v 1) := by
  have hP : ∀ i : Fin 3, HasFDerivAt (fun w : UnforcedLeray.Space => w i)
      (EuclideanSpace.proj i : UnforcedLeray.Space →L[ℝ] ℝ) w := fun i =>
    (EuclideanSpace.proj i : UnforcedLeray.Space →L[ℝ] ℝ).hasFDerivAt
  have hFd : HasFDerivAt cpF
      ((2 * w 2) • (EuclideanSpace.proj 2 : UnforcedLeray.Space →L[ℝ] ℝ)
        - (2 * w 0) • (EuclideanSpace.proj 0 : UnforcedLeray.Space →L[ℝ] ℝ)
        - (2 * w 1) • (EuclideanSpace.proj 1 : UnforcedLeray.Space →L[ℝ] ℝ)) w := by
    unfold cpF
    have h2 := (hasDerivAt_pow 2 (w 2)).comp_hasFDerivAt w (hP 2)
    have h0 := (hasDerivAt_pow 2 (w 0)).comp_hasFDerivAt w (hP 0)
    have h1 := (hasDerivAt_pow 2 (w 1)).comp_hasFDerivAt w (hP 1)
    refine ((h2.sub h0).sub h1).congr_fderiv ?_
    ext v
    simp
  have hG := (cpG_hasDerivAt (cpF w) hF).comp_hasFDerivAt w hFd
  have hT := ((hG.const_mul s).sub (hP 2)).smul_const cpE2
  have hΨ : HasFDerivAt (cpPsi s) _ w := (hasFDerivAt_id w).add hT
  rw [hΨ.fderiv]
  have hsq : Real.sqrt (cpF w) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  refine ⟨?_, ?_, ?_⟩
  · simp [cpE2, PiLp.single_apply]
  · simp [cpE2, PiLp.single_apply]
  · simp [cpE2]
    field_simp

def cpW : Set UnforcedLeray.Space :=
  {w | 1 ≤ w 2 ∧ w 2 ≤ 4 ∧ w 0 ^ 2 + w 1 ^ 2 ≤ 3 / 4 * w 2 ^ 2}

lemma cpNormSq (y : UnforcedLeray.Space) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

lemma cpW_convex : Convex ℝ cpW := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  simp only [cpW, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  -- Cauchy-Schwarz cross term
  have hX : u 0 * v 0 + u 1 * v 1 ≤ 3 / 4 * (u 2 * v 2) := by
    have hcs : (u 0 * v 0 + u 1 * v 1) ^ 2 ≤ (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
      nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0)]
    have hAB : (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) ≤ (3 / 4 * u 2 ^ 2) * (3 / 4 * v 2 ^ 2) :=
      mul_le_mul hu3 hv3 (by positivity) (by positivity)
    have h2 : (u 0 * v 0 + u 1 * v 1) ^ 2 ≤ (3 / 4 * (u 2 * v 2)) ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h2 (by nlinarith)).2
  nlinarith [mul_nonneg ha hb, mul_nonneg ha ha, mul_nonneg hb hb,
    mul_nonneg (mul_nonneg ha hb) (sub_nonneg.2 hX)]

lemma cpW_subset_ball : cpW ⊆ Metric.closedBall (0 : UnforcedLeray.Space) 8 := by
  intro w hw
  obtain ⟨h1, h2, h3⟩ := hw
  rw [mem_closedBall_zero_iff]
  have hsq : ‖w‖ ^ 2 ≤ 8 ^ 2 := by
    rw [cpNormSq]; nlinarith
  exact (abs_le_of_sq_le_sq' hsq (by norm_num)).2

lemma cpW_isClosed : IsClosed cpW := by
  have h0 : Continuous fun w : UnforcedLeray.Space => w 0 := by fun_prop
  have h1 : Continuous fun w : UnforcedLeray.Space => w 1 := by fun_prop
  have h2 : Continuous fun w : UnforcedLeray.Space => w 2 := by fun_prop
  refine (isClosed_le continuous_const h2).inter ((isClosed_le h2 continuous_const).inter ?_)
  exact isClosed_le ((h0.pow 2).add (h1.pow 2)) (continuous_const.mul (h2.pow 2))

lemma cpW_compact : IsCompact cpW :=
  IsCompact.of_isClosed_subset (isCompact_closedBall _ _) cpW_isClosed cpW_subset_ball

lemma cpW_volume_pos : 0 < (volume cpW).toReal := by
  have hball : Metric.ball (EuclideanSpace.single 2 2 : UnforcedLeray.Space) (1 / 2) ⊆ cpW := by
    intro w hw
    rw [Metric.mem_ball, EuclideanSpace.dist_eq] at hw
    have hsum : ∑ i, (w i - (EuclideanSpace.single (2 : Fin 3) (2 : ℝ) : UnforcedLeray.Space) i) ^ 2
        < (1 / 2) ^ 2 := by
      have := Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2) |>.1 hw
      simpa [Real.dist_eq, sq_abs] using this
    rw [Fin.sum_univ_three] at hsum
    simp only [PiLp.single_apply] at hsum
    simp at hsum
    have a0 := sq_nonneg (w 0)
    have a1 := sq_nonneg (w 1)
    have a2 := sq_nonneg (w 2 - 2)
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith
  have hpos : 0 < volume cpW :=
    lt_of_lt_of_le (Metric.measure_ball_pos volume _ (by norm_num)) (measure_mono hball)
  exact ENNReal.toReal_pos hpos.ne' cpW_compact.measure_lt_top.ne

def cpS (σ : Bool) : ℝ := if σ then (1 : ℝ) else -1

lemma cpS_sq (σ : Bool) : cpS σ * cpS σ = 1 := by
  cases σ <;> simp [cpS]

lemma cpF_bounds {w : UnforcedLeray.Space} (hw : w ∈ cpW) :
    w 2 ^ 2 / 4 ≤ cpF w ∧ cpF w ≤ w 2 ^ 2 ∧ 1 / 4 ≤ cpF w := by
  obtain ⟨h1, h2, h3⟩ := hw
  unfold cpF
  have := sq_nonneg (w 0)
  have := sq_nonneg (w 1)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma cpG_cpF {w : UnforcedLeray.Space} (hw : w ∈ cpW) : cpG (cpF w) = Real.sqrt (cpF w) :=
  cpG_eq _ (by have := (cpF_bounds hw).2.2; linarith)

lemma cpSqrt_ge {w : UnforcedLeray.Space} (hw : w ∈ cpW) : w 2 / 2 ≤ Real.sqrt (cpF w) := by
  apply Real.le_sqrt_of_sq_le
  have := (cpF_bounds hw).1
  nlinarith

lemma cpSqrt_le {w : UnforcedLeray.Space} (hw : w ∈ cpW) : Real.sqrt (cpF w) ≤ w 2 := by
  apply Real.sqrt_le_iff.2
  refine ⟨by have := hw.1; linarith, (cpF_bounds hw).2.1⟩

lemma cpPsi_injOn (σ : Bool) : Set.InjOn (cpPsi (cpS σ)) cpW := by
  intro w hw w' hw' h
  have e0 := cpPsi_apply0 (cpS σ) w
  have e1 := cpPsi_apply1 (cpS σ) w
  have e2 := cpPsi_apply2 (cpS σ) w
  have e0' := cpPsi_apply0 (cpS σ) w'
  have e1' := cpPsi_apply1 (cpS σ) w'
  have e2' := cpPsi_apply2 (cpS σ) w'
  rw [h] at e0 e1 e2
  have h0 : w 0 = w' 0 := by rw [← e0, e0']
  have h1 : w 1 = w' 1 := by rw [← e1, e1']
  have h2 : cpS σ * cpG (cpF w) = cpS σ * cpG (cpF w') := by rw [← e2, e2']
  have hs := cpS_sq σ
  have h3 : cpG (cpF w) = cpG (cpF w') := by
    have := congrArg (fun t => cpS σ * t) h2
    simp only [← mul_assoc, hs, one_mul] at this
    exact this
  rw [cpG_cpF hw, cpG_cpF hw'] at h3
  have hF : cpF w = cpF w' := by
    have a := Real.sq_sqrt (show 0 ≤ cpF w by have := (cpF_bounds hw).2.2; linarith)
    have b := Real.sq_sqrt (show 0 ≤ cpF w' by have := (cpF_bounds hw').2.2; linarith)
    rw [← a, ← b, h3]
  have h4 : w 2 = w' 2 := by
    unfold cpF at hF
    rw [h0, h1] at hF
    have hpos := hw.1
    have hpos' := hw'.1
    nlinarith
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h4

lemma cpPsi_image (σ : Bool) : cpPsi (cpS σ) '' cpW = cone 2 σ := by
  have hs := cpS_sq σ
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have e0 := cpPsi_apply0 (cpS σ) w
    have e1 := cpPsi_apply1 (cpS σ) w
    have e2 := cpPsi_apply2 (cpS σ) w
    rw [cpG_cpF hw] at e2
    have hF0 : 0 ≤ cpF w := by have := (cpF_bounds hw).2.2; linarith
    have hsq := Real.sq_sqrt hF0
    have hN : ‖cpPsi (cpS σ) w‖ = w 2 := by
      have h : ‖cpPsi (cpS σ) w‖ ^ 2 = w 2 ^ 2 := by
        rw [cpNormSq, e0, e1, e2]
        unfold cpF at hsq ⊢
        nlinarith
      have := hw.1
      exact (sq_eq_sq₀ (norm_nonneg _) (by linarith)).1 h
    refine ⟨?_, ?_, ?_⟩
    · rw [hN]; exact hw.1
    · rw [hN]; exact hw.2.1
    · rw [hN]
      have : 2 * (cpS σ * cpPsi (cpS σ) w 2) = 2 * Real.sqrt (cpF w) := by
        rw [e2]
        linear_combination (2 * Real.sqrt (cpF w)) * hs
      show w 2 ≤ 2 * (cpS σ * cpPsi (cpS σ) w 2)
      rw [this]
      have := cpSqrt_ge hw
      linarith
  · rintro ⟨h1, h2, h3⟩
    change ‖y‖ ≤ 2 * (cpS σ * y 2) at h3
    set N := ‖y‖ with hNdef
    have hN2 : N ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := cpNormSq y
    have ht : N / 2 ≤ cpS σ * y 2 := by linarith
    have ht2 : (cpS σ * y 2) ^ 2 = y 2 ^ 2 := by
      have : (cpS σ * y 2) ^ 2 = (cpS σ * cpS σ) * y 2 ^ 2 := by ring
      rw [this, hs, one_mul]
    have hy2 : N ^ 2 ≤ 4 * y 2 ^ 2 := by nlinarith
    let w : UnforcedLeray.Space := y + (N - y 2) • cpE2
    have w0 : w 0 = y 0 := by simp [w, cpE2]
    have w1 : w 1 = y 1 := by simp [w, cpE2]
    have w2 : w 2 = N := by simp [w, cpE2]
    have hwW : w ∈ cpW := by
      refine ⟨?_, ?_, ?_⟩
      · rw [w2]; exact h1
      · rw [w2]; exact h2
      · rw [w0, w1, w2]; nlinarith
    refine ⟨w, hwW, ?_⟩
    have hF : cpF w = y 2 ^ 2 := by
      unfold cpF; rw [w0, w1, w2]; nlinarith
    have hG : cpG (cpF w) = cpS σ * y 2 := by
      rw [cpG_cpF hwW, hF, ← ht2]
      exact Real.sqrt_sq (by linarith)
    ext i
    fin_cases i
    · show cpPsi (cpS σ) w 0 = y 0
      rw [cpPsi_apply0, w0]
    · show cpPsi (cpS σ) w 1 = y 1
      rw [cpPsi_apply1, w1]
    · show cpPsi (cpS σ) w 2 = y 2
      rw [cpPsi_apply2, hG, ← mul_assoc, hs, one_mul]

lemma cp_det_of_components (f : UnforcedLeray.Space →L[ℝ] UnforcedLeray.Space) (a b c : ℝ)
    (h0 : ∀ v, f v 0 = v 0) (h1 : ∀ v, f v 1 = v 1)
    (h2 : ∀ v, f v 2 = a * v 0 + b * v 1 + c * v 2) :
    ContinuousLinearMap.det f = c := by
  have hdet := LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (f : UnforcedLeray.Space →ₗ[ℝ] UnforcedLeray.Space)
  have : ContinuousLinearMap.det f = LinearMap.det (f : UnforcedLeray.Space →ₗ[ℝ] UnforcedLeray.Space) :=
    rfl
  rw [this, ← hdet, Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply, h0, h1, h2]

lemma cp_abs_s (σ : Bool) : |cpS σ| = 1 := by
  cases σ <;> simp [cpS]

lemma cpPsi_det (σ : Bool) {w : UnforcedLeray.Space} (hw : w ∈ cpW) :
    |ContinuousLinearMap.det (fderiv ℝ (cpPsi (cpS σ)) w)| = w 2 / Real.sqrt (cpF w) := by
  have hF : 1 / 8 < cpF w := by have := (cpF_bounds hw).2.2; linarith
  have hd := cp_det_of_components (fderiv ℝ (cpPsi (cpS σ)) w)
    (-(cpS σ * (1 / Real.sqrt (cpF w))) * w 0) (-(cpS σ * (1 / Real.sqrt (cpF w))) * w 1)
    (cpS σ * (1 / Real.sqrt (cpF w)) * w 2)
    (fun v => (cpPsi_fderiv (cpS σ) w hF v).1) (fun v => (cpPsi_fderiv (cpS σ) w hF v).2.1)
    (fun v => by rw [(cpPsi_fderiv (cpS σ) w hF v).2.2]; ring)
  rw [hd, abs_mul, abs_mul, cp_abs_s, one_mul]
  have hpos : 0 < Real.sqrt (cpF w) := Real.sqrt_pos.2 (by linarith)
  rw [abs_of_pos (by positivity : 0 < 1 / Real.sqrt (cpF w)), abs_of_pos (by have := hw.1; linarith : 0 < w 2)]
  ring

lemma cpPsi_det_bounds (σ : Bool) {w : UnforcedLeray.Space} (hw : w ∈ cpW) :
    1 ≤ |ContinuousLinearMap.det (fderiv ℝ (cpPsi (cpS σ)) w)| ∧
    |ContinuousLinearMap.det (fderiv ℝ (cpPsi (cpS σ)) w)| ≤ 2 := by
  rw [cpPsi_det σ hw]
  have hpos : 0 < Real.sqrt (cpF w) := Real.sqrt_pos.2 (by have := (cpF_bounds hw).2.2; linarith)
  have h1 := cpSqrt_ge hw
  have h2 := cpSqrt_le hw
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

lemma cp_norm_le_sum (x : UnforcedLeray.Space) : ‖x‖ ≤ |x 0| + |x 1| + |x 2| := by
  have h : ‖x‖ ^ 2 ≤ (|x 0| + |x 1| + |x 2|) ^ 2 := by
    rw [cpNormSq]
    have := abs_nonneg (x 0)
    have := abs_nonneg (x 1)
    have := abs_nonneg (x 2)
    nlinarith [sq_abs (x 0), sq_abs (x 1), sq_abs (x 2), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)),
      mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 2)), mul_nonneg (abs_nonneg (x 1)) (abs_nonneg (x 2))]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h

lemma cp_abs_le_norm (x : UnforcedLeray.Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h : x i ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [cpNormSq]
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  exact abs_le_of_sq_le_sq' h (norm_nonneg _) |> fun h' => abs_le.2 h'

lemma cpPsi_L (σ : Bool) {w : UnforcedLeray.Space} (hw : w ∈ cpW) (v : UnforcedLeray.Space) :
    ‖fderiv ℝ (cpPsi (cpS σ)) w v‖ ≤ 8 * ‖v‖ := by
  have hF : 1 / 8 < cpF w := by have := (cpF_bounds hw).2.2; linarith
  obtain ⟨e0, e1, e2⟩ := cpPsi_fderiv (cpS σ) w hF v
  have hpos : 0 < Real.sqrt (cpF w) := Real.sqrt_pos.2 (by linarith)
  have hw2 : 0 < w 2 := by have := hw.1; linarith
  have hr : 0 < 1 / Real.sqrt (cpF w) := by positivity
  have hrw : w 2 * (1 / Real.sqrt (cpF w)) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ hpos]; have := cpSqrt_ge hw; linarith
  have hw0 : |w 0| ≤ w 2 := by
    have := hw.2.2; nlinarith [sq_nonneg (w 1), abs_le.2 (abs_le_of_sq_le_sq' (show w 0 ^ 2 ≤ w 2 ^ 2 by nlinarith [sq_nonneg (w 1)]) hw2.le)]
  have hw1 : |w 1| ≤ w 2 := abs_le.2 (abs_le_of_sq_le_sq' (show w 1 ^ 2 ≤ w 2 ^ 2 by
    have := hw.2.2; nlinarith [sq_nonneg (w 0)]) hw2.le)
  set r := 1 / Real.sqrt (cpF w) with hrdef
  have hv0 := cp_abs_le_norm v 0
  have hv1 := cp_abs_le_norm v 1
  have hv2 := cp_abs_le_norm v 2
  have hsum : |w 2 * v 2 - w 0 * v 0 - w 1 * v 1| ≤ 3 * w 2 * ‖v‖ := by
    calc _ ≤ |w 2 * v 2| + |w 0 * v 0| + |w 1 * v 1| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ = w 2 * |v 2| + |w 0| * |v 0| + |w 1| * |v 1| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hw2]
      _ ≤ w 2 * ‖v‖ + w 2 * ‖v‖ + w 2 * ‖v‖ := by
          gcongr
      _ = 3 * w 2 * ‖v‖ := by ring
  have h3 : |fderiv ℝ (cpPsi (cpS σ)) w v 2| ≤ 6 * ‖v‖ := by
    rw [e2, abs_mul, abs_mul, cp_abs_s, one_mul, abs_of_pos hr]
    calc r * |w 2 * v 2 - w 0 * v 0 - w 1 * v 1| ≤ r * (3 * w 2 * ‖v‖) :=
          mul_le_mul_of_nonneg_left hsum hr.le
      _ = 3 * (w 2 * r) * ‖v‖ := by ring
      _ ≤ 3 * 2 * ‖v‖ := by gcongr
      _ = 6 * ‖v‖ := by ring
  have := cp_norm_le_sum (fderiv ℝ (cpPsi (cpS σ)) w v)
  rw [e0, e1] at this
  linarith

/-- Coordinate permutation swapping `2` and `k`, as a linear isometry. -/
def cpE (k : Fin 3) : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (2 : Fin 3) k)

lemma cpE_apply (k : Fin 3) (x : UnforcedLeray.Space) (j : Fin 3) :
    cpE k x j = x (Equiv.swap (2 : Fin 3) k j) := by
  simp [cpE, Equiv.piCongrLeft'_apply]

lemma cpE_cone (k : Fin 3) (σ : Bool) : cpE k '' cone 2 σ = cone k σ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hx
    have hk : cpE k x k = x 2 := by rw [cpE_apply]; simp
    refine ⟨?_, ?_, ?_⟩
    · rw [(cpE k).norm_map]; exact h1
    · rw [(cpE k).norm_map]; exact h2
    · rw [(cpE k).norm_map, hk]; exact h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(cpE k).symm y, ⟨?_, ?_, ?_⟩, (cpE k).apply_symm_apply y⟩
    · rw [(cpE k).symm.norm_map]; exact h1
    · rw [(cpE k).symm.norm_map]; exact h2
    · have hk : y k = (cpE k).symm y 2 := by
        have := cpE_apply k ((cpE k).symm y) k
        rw [(cpE k).apply_symm_apply] at this
        rw [this]; simp
      rw [(cpE k).symm.norm_map, ← hk]; exact h3

lemma cp_abs_det_comp (k : Fin 3) (f : UnforcedLeray.Space →L[ℝ] UnforcedLeray.Space) :
    |ContinuousLinearMap.det ((cpE k).toContinuousLinearEquiv.toContinuousLinearMap.comp f)| =
      |ContinuousLinearMap.det f| := by
  have h1 : ((cpE k).toContinuousLinearEquiv.toContinuousLinearMap.comp f :
      UnforcedLeray.Space →ₗ[ℝ] UnforcedLeray.Space) =
      (cpE k).toLinearIsometry.toLinearMap ∘ₗ (f : UnforcedLeray.Space →ₗ[ℝ] UnforcedLeray.Space) :=
    rfl
  have h2 := (cpE k).toLinearIsometry.normDet_eq_one
  rw [LinearMap.normDet_eq_abs_det] at h2
  have h3 : ContinuousLinearMap.det ((cpE k).toContinuousLinearEquiv.toContinuousLinearMap.comp f) =
      LinearMap.det (cpE k).toLinearIsometry.toLinearMap * ContinuousLinearMap.det f := by
    show LinearMap.det ((cpE k).toLinearIsometry.toLinearMap ∘ₗ
      (f : UnforcedLeray.Space →ₗ[ℝ] UnforcedLeray.Space)) = _
    exact LinearMap.det_comp _ _
  rw [h3, abs_mul, h2, one_mul]

theorem conePieces : ConePieces := by
  intro k σ
  set Ψ : UnforcedLeray.Space → UnforcedLeray.Space := fun w => cpE k (cpPsi (cpS σ) w) with hΨdef
  have hΨ : ContDiff ℝ 1 Ψ := (cpE k).toContinuousLinearEquiv.contDiff.comp (cpPsi_contDiff (cpS σ))
  have hfd : ∀ w, fderiv ℝ Ψ w = (cpE k).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fderiv ℝ (cpPsi (cpS σ)) w) := by
    intro w
    exact (cpE k).toContinuousLinearEquiv.comp_fderiv
  refine bg_transfer cpW (cone k σ) Ψ cpW_convex cpW_compact cpW_volume_pos hΨ ?_ ?_ 8 1 2
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · exact (cpE k).injective.comp_injOn (cpPsi_injOn σ)
  · rw [hΨdef]
    show (cpE k) ∘ (cpPsi (cpS σ)) '' cpW = _
    rw [Set.image_comp, cpPsi_image, cpE_cone]
  · intro z hz v
    rw [hfd z]
    show ‖(cpE k) (fderiv ℝ (cpPsi (cpS σ)) z v)‖ ≤ _
    rw [(cpE k).norm_map]
    exact cpPsi_L σ hz v
  · intro z hz
    rw [hfd z, cp_abs_det_comp]
    exact cpPsi_det_bounds σ hz

end UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain
