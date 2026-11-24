import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7

/-!
# Part II-b, task `PartII-b:G4/3/7/6` (`VecDiffJet`): second-order chart calculus

Source of record: `the November 2 reference manuscript`, SP 2367-2369.

Pure calculus. Write `N0 = ‖F x‖`, `N1 = ‖fderiv F x‖`, `N2 = ‖fderiv (fderiv F) x‖`, `Q = 2|s| + |η|`,
`Λ = 1 + |s| + |η|`. Each term of `vecDiffEps ε F x` is bounded by `20 Λ² (N0 + N1 + N2)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace VecDiffJetHelp

theorem e1_le : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp

theorem eQ_le : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp

theorem eE_le : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp

/-- The directional derivative `y ↦ ∂_v F(y)` has derivative `w ↦ ∂²F(w, v)`. -/
theorem fderiv_dir {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x : Coord) (v w : Coord) :
    fderiv ℝ (fun y => fderiv ℝ F y v) x w = fderiv ℝ (fderiv ℝ F) x w v := by
  have hc : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have := fderiv_clm_apply (hc x) (differentiableAt_const v)
  have h2 : fderiv ℝ (fun y => fderiv ℝ F y v) x =
      (fderiv ℝ (fderiv ℝ F) x).flip v := by
    rw [show (fun y => fderiv ℝ F y v) = fun y => (fderiv ℝ F y) ((fun _ => v) y) from rfl, this]
    simp
  rw [h2, ContinuousLinearMap.flip_apply]

/-- Norm bound for second derivatives in directions of norm at most one. -/
theorem fderiv_dir_norm_le {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x : Coord)
    (v w : Coord) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ (fun y => fderiv ℝ F y v) x w‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ := by
  rw [fderiv_dir hF x v w]
  have h3 : ‖fderiv ℝ (fderiv ℝ F) x w‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ * ‖w‖ :=
    (fderiv ℝ (fderiv ℝ F) x).le_opNorm w
  have h4 : ‖fderiv ℝ (fderiv ℝ F) x w v‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x w‖ * ‖v‖ :=
    ((fderiv ℝ (fderiv ℝ F) x) w).le_opNorm v
  have hN := norm_nonneg (fderiv ℝ (fderiv ℝ F) x)
  have hV := norm_nonneg v
  have hW := norm_nonneg w
  calc ‖fderiv ℝ (fderiv ℝ F) x w v‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x w‖ * ‖v‖ := h4
    _ ≤ (‖fderiv ℝ (fderiv ℝ F) x‖ * ‖w‖) * ‖v‖ := mul_le_mul_of_nonneg_right h3 hV
    _ ≤ (‖fderiv ℝ (fderiv ℝ F) x‖ * 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw hN) hv hV (by positivity)
    _ = ‖fderiv ℝ (fderiv ℝ F) x‖ := by ring

/-- First-order norm bound in a direction of norm at most one. -/
theorem fderiv_dir1_le {F : Coord → Axi.Merid} (x : Coord) (v : Coord) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ F x v‖ ≤ ‖fderiv ℝ F x‖ :=
  ((fderiv ℝ F x).le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)

/-- `‖kAge G x‖ ≤ 2|s| ‖dS G x‖ + |η| ‖dEta G x‖`. -/
theorem norm_kAge_le (G : Coord → Axi.Merid) (x : Coord) :
    ‖kAge G x‖ ≤ 2 * |x.1| * ‖Axi.dS G x‖ + |x.2.2| * ‖Axi.dEta G x‖ := by
  have e : ‖(2 * x.1) • Axi.dS G x + x.2.2 • Axi.dEta G x‖ ≤
      ‖(2 * x.1) • Axi.dS G x‖ + ‖x.2.2 • Axi.dEta G x‖ := norm_add_le _ _
  have e1 : ‖(2 * x.1) • Axi.dS G x‖ = 2 * |x.1| * ‖Axi.dS G x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    norm_num
  have e2 : ‖x.2.2 • Axi.dEta G x‖ = |x.2.2| * ‖Axi.dEta G x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  unfold kAge
  linarith

theorem norm_add3_le {E : Type*} [NormedAddCommGroup E] (a b c : E) :
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have := norm_add_le (a + b) c
  have := norm_add_le a b
  linarith

theorem norm_add4_le {E : Type*} [NormedAddCommGroup E] (a b c d : E) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have := norm_add_le (a + b + c) d
  have := norm_add3_le a b c
  linarith

theorem diff_dS {F : Coord → Axi.Merid} (hc : Differentiable ℝ (fderiv ℝ F)) (x : Coord)
    (v : Coord) : DifferentiableAt ℝ (fun y => fderiv ℝ F y v) x :=
  (hc x).clm_apply (differentiableAt_const v)

/-- The derivative of `kAge F` in a direction `w` of norm at most one. -/
theorem kAge_fderiv_bound {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x w : Coord)
    (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ (fun y => kAge F y) x w‖ ≤
      3 * ‖fderiv ℝ F x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
  have hc : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hS : DifferentiableAt ℝ (fun y => Axi.dS F y) x := diff_dS hc x _
  have hE : DifferentiableAt ℝ (fun y => Axi.dEta F y) x := diff_dS hc x _
  have hfun : (fun y => kAge F y) = fun y => (2 * y.1) • Axi.dS F y + y.2.2 • Axi.dEta F y := rfl
  have hc1 : DifferentiableAt ℝ (fun y : Coord => 2 * y.1) x := by fun_prop
  have hc2 : DifferentiableAt ℝ (fun y : Coord => y.2.2) x := by fun_prop
  have d1 : fderiv ℝ (fun y : Coord => 2 * y.1) x w = 2 * w.1 := by
    rw [((hasFDerivAt_fst (p := x)).const_mul (2 : ℝ)).fderiv]
    simp
  have d2 : fderiv ℝ (fun y : Coord => y.2.2) x w = w.2.2 := by
    let L : Coord →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    have hL : (fun y : Coord => y.2.2) = ⇑L := rfl
    rw [hL, L.fderiv]
    simp [L]
  have hA : HasFDerivAt (fun y => (2 * y.1) • Axi.dS F y)
      ((2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x +
        (fderiv ℝ (fun y : Coord => 2 * y.1) x).smulRight (Axi.dS F x)) x :=
    hc1.hasFDerivAt.smul hS.hasFDerivAt
  have hB : HasFDerivAt (fun y => y.2.2 • Axi.dEta F y)
      (x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x +
        (fderiv ℝ (fun y : Coord => y.2.2) x).smulRight (Axi.dEta F x)) x :=
    hc2.hasFDerivAt.smul hE.hasFDerivAt
  have hAB : HasFDerivAt (fun y => (2 * y.1) • Axi.dS F y + y.2.2 • Axi.dEta F y)
      (((2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x +
        (fderiv ℝ (fun y : Coord => 2 * y.1) x).smulRight (Axi.dS F x)) +
      (x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x +
        (fderiv ℝ (fun y : Coord => y.2.2) x).smulRight (Axi.dEta F x))) x :=
    hA.add hB
  have eq : fderiv ℝ (fun y => kAge F y) x w =
      (2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x w + (2 * w.1) • Axi.dS F x +
        (w.2.2) • Axi.dEta F x + x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x w := by
    rw [hfun, hAB.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, d1, d2, smul_eq_mul]
    abel
  rw [eq]
  have b1 : ‖fderiv ℝ (fun y => Axi.dS F y) x w‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x _ w e1_le hw
  have b2 : ‖fderiv ℝ (fun y => Axi.dEta F y) x w‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x _ w eE_le hw
  have hw1 : |w.1| ≤ 1 := by
    have h := norm_fst_le w
    rw [Real.norm_eq_abs] at h
    linarith
  have hw2 : |w.2.2| ≤ 1 := by
    have h := (norm_snd_le w.2).trans (norm_snd_le w)
    rw [Real.norm_eq_abs] at h
    linarith
  have hN2 := norm_nonneg (fderiv ℝ (fderiv ℝ F) x)
  have hN1 := norm_nonneg (fderiv ℝ F x)
  have b3 : ‖Axi.dS F x‖ ≤ ‖fderiv ℝ F x‖ := fderiv_dir1_le x _ e1_le
  have b4 : ‖Axi.dEta F x‖ ≤ ‖fderiv ℝ F x‖ := fderiv_dir1_le x _ eE_le
  have n1 : ‖(2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x w‖ ≤
      2 * |x.1| * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have := mul_le_mul_of_nonneg_left b1 (abs_nonneg x.1)
    norm_num
    nlinarith [this]
  have n2 : ‖(2 * w.1) • Axi.dS F x‖ ≤ 2 * ‖fderiv ℝ F x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have := mul_le_mul_of_nonneg_right hw1 (norm_nonneg (Axi.dS F x))
    have h2 := mul_le_mul_of_nonneg_right b3 (by norm_num : (0:ℝ) ≤ 2)
    norm_num
    nlinarith [this, h2, norm_nonneg (Axi.dS F x)]
  have n3 : ‖(w.2.2) • Axi.dEta F x‖ ≤ ‖fderiv ℝ F x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_right hw2 (norm_nonneg (Axi.dEta F x))
    nlinarith [this, b4]
  have n4 : ‖x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x w‖ ≤
      |x.2.2| * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left b2 (abs_nonneg _)
  have t := norm_add4_le ((2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x w)
    ((2 * w.1) • Axi.dS F x) ((w.2.2) • Axi.dEta F x)
    (x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x w)
  nlinarith [t, n1, n2, n3, n4, hN1, hN2, abs_nonneg x.1, abs_nonneg x.2.2]

theorem diff_kAge_at {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x : Coord) :
    DifferentiableAt ℝ (fun y => kAge F y) x := by
  have hc : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hS : DifferentiableAt ℝ (fun y => Axi.dS F y) x := diff_dS hc x _
  have hE : DifferentiableAt ℝ (fun y => Axi.dEta F y) x := diff_dS hc x _
  have hc1 : DifferentiableAt ℝ (fun y : Coord => 2 * y.1) x := by fun_prop
  have hc2 : DifferentiableAt ℝ (fun y : Coord => y.2.2) x := by fun_prop
  have hfun : (fun y => kAge F y) = fun y => (2 * y.1) • Axi.dS F y + y.2.2 • Axi.dEta F y := rfl
  rw [hfun]
  exact (hc1.smul hS).add (hc2.smul hE)

/-- The derivative of `kAge F + F` in a direction of norm at most one. -/
theorem G_fderiv_bound {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x w : Coord)
    (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ (fun y => kAge F y + F y) x w‖ ≤
      4 * ‖fderiv ℝ F x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
  have hK := diff_kAge_at hF x
  have hFd : DifferentiableAt ℝ F x := (hF.differentiable (by simp)) x
  have h : HasFDerivAt (fun y => kAge F y + F y)
      (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x) x :=
    hK.hasFDerivAt.add hFd.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.add_apply]
  have h1 := kAge_fderiv_bound hF x w hw
  have h2 := fderiv_dir1_le (F := F) x w hw
  have h3 := norm_add_le ((fderiv ℝ (fun y => kAge F y) x) w) ((fderiv ℝ F x) w)
  linarith

/-- The second chart operator on `kAge F + F`. -/
theorem norm_kAge_G_le {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x : Coord) :
    ‖kAge (fun y => kAge F y + F y) x‖ ≤
      (2 * |x.1| + |x.2.2|) * (4 * ‖fderiv ℝ F x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖) := by
  have hS' : ‖Axi.dS (fun y => kAge F y + F y) x‖ ≤
      4 * ‖fderiv ℝ F x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    G_fderiv_bound hF x _ e1_le
  have hE' : ‖Axi.dEta (fun y => kAge F y + F y) x‖ ≤
      4 * ‖fderiv ℝ F x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    G_fderiv_bound hF x _ eE_le
  have hN := norm_kAge_le (fun y => kAge F y + F y) x
  have ha : 0 ≤ |x.1| := abs_nonneg _
  have hb : 0 ≤ |x.2.2| := abs_nonneg _
  have hA0 : 0 ≤ 4 * ‖fderiv ℝ F x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    have := norm_nonneg (fderiv ℝ F x)
    have := norm_nonneg (fderiv ℝ (fderiv ℝ F) x)
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hS' ha, mul_le_mul_of_nonneg_left hE' hb]

/-- The final numeric comparison. -/
theorem final_ineq (a b N0 N1 N2 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 ≤ N0) (h1 : 0 ≤ N1)
    (h2 : 0 ≤ N2) :
    2 * N2 + 2 * ((2 * a + b) * N2 + N1) +
        ((2 * a + b) * (4 * N1 + (2 * a + b) * N2) + ((2 * a + b) * N1 + N0) + N0)
      ≤ 20 * (1 + a + b) ^ 2 * (N0 + N1 + N2) := by
  have hQ0 : 0 ≤ 2 * a + b := by linarith
  have hQL : 2 * a + b ≤ 2 * (1 + a + b) := by linarith
  have hΛ : 1 ≤ 1 + a + b := by linarith
  have hΛ2 : 1 ≤ (1 + a + b) ^ 2 := by nlinarith
  have hΛL : (1 + a + b) ≤ (1 + a + b) ^ 2 := by nlinarith
  have hQ2 : (2 * a + b) ^ 2 ≤ 4 * (1 + a + b) ^ 2 := by nlinarith
  have e0 : 2 * N0 ≤ 20 * (1 + a + b) ^ 2 * N0 := by nlinarith
  have e1 : (2 + 5 * (2 * a + b)) * N1 ≤ 20 * (1 + a + b) ^ 2 * N1 :=
    mul_le_mul_of_nonneg_right (by nlinarith) h1
  have e2 : (2 + 2 * (2 * a + b) + (2 * a + b) ^ 2) * N2 ≤ 20 * (1 + a + b) ^ 2 * N2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) h2
  nlinarith [e0, e1, e2]

theorem vecDiffJet_body {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : Coord) :
    ‖vecDiffEps ε F x‖ ≤
      20 * (1 + |x.1| + |x.2.2|) ^ 2 *
        (‖F x‖ + ‖fderiv ℝ F x‖ + ‖fderiv ℝ (fderiv ℝ F) x‖) := by
  have hN0 := norm_nonneg (F x)
  have hN1 := norm_nonneg (fderiv ℝ F x)
  have hN2 := norm_nonneg (fderiv ℝ (fderiv ℝ F) x)
  have ha : 0 ≤ |x.1| := abs_nonneg _
  have hb : 0 ≤ |x.2.2| := abs_nonneg _
  have hQ0 : 0 ≤ 2 * |x.1| + |x.2.2| := by positivity
  -- second-order terms
  have b1 : ‖Axi.dQ (Axi.dQ F) x‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x ((0:ℝ), ((1:ℝ), (0:ℝ))) ((0:ℝ), ((1:ℝ), (0:ℝ))) eQ_le eQ_le
  have b2 : ‖Axi.dEta (Axi.dEta F) x‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x ((0:ℝ), ((0:ℝ), (1:ℝ))) ((0:ℝ), ((0:ℝ), (1:ℝ))) eE_le eE_le
  have c1 : ‖Axi.dS (Axi.dQ F) x‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x ((0:ℝ), ((1:ℝ), (0:ℝ))) ((1:ℝ), ((0:ℝ), (0:ℝ))) eQ_le e1_le
  have c2 : ‖Axi.dEta (Axi.dQ F) x‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x ((0:ℝ), ((1:ℝ), (0:ℝ))) ((0:ℝ), ((0:ℝ), (1:ℝ))) eQ_le eE_le
  have b3 : ‖kAge (Axi.dQ F) x‖ ≤ (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    have hk := norm_kAge_le (Axi.dQ F) x
    linarith [mul_le_mul_of_nonneg_left c1 (by linarith : (0:ℝ) ≤ 2 * |x.1|),
      mul_le_mul_of_nonneg_left c2 hb]
  have b4 : ‖Axi.dQ F x‖ ≤ ‖fderiv ℝ F x‖ := fderiv_dir1_le x ((0:ℝ), ((1:ℝ), (0:ℝ))) eQ_le
  have b5 := norm_kAge_G_le hF x
  have b6 : ‖kAge F x‖ ≤ (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ F x‖ := by
    have hk := norm_kAge_le F x
    have d1 : ‖Axi.dS F x‖ ≤ ‖fderiv ℝ F x‖ := fderiv_dir1_le x ((1:ℝ), ((0:ℝ), (0:ℝ))) e1_le
    have d2 : ‖Axi.dEta F x‖ ≤ ‖fderiv ℝ F x‖ := fderiv_dir1_le x ((0:ℝ), ((0:ℝ), (1:ℝ))) eE_le
    linarith [mul_le_mul_of_nonneg_left d1 (by linarith : (0:ℝ) ≤ 2 * |x.1|),
      mul_le_mul_of_nonneg_left d2 hb]
  have b8 : ‖hoopR (F x)‖ ≤ ‖F x‖ := by
    have hm0 : ‖Axi.m0‖ = 1 := by simp [Axi.m0]
    have hv0 : |F x 0| ≤ ‖F x‖ := by
      have := PiLp.norm_apply_le (F x) 0
      rwa [Real.norm_eq_abs] at this
    unfold hoopR
    rw [norm_smul, hm0, Real.norm_eq_abs, mul_one]
    exact hv0
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hε2' : 0 ≤ ε ^ 2 := by positivity
  -- the term with the factor `2ε`
  have T3 : ‖(2 * ε) • (kAge (Axi.dQ F) x + Axi.dQ F x)‖ ≤
      2 * ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + ‖fderiv ℝ F x‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hZ : ‖kAge (Axi.dQ F) x + Axi.dQ F x‖ ≤
        (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + ‖fderiv ℝ F x‖ :=
      (norm_add_le _ _).trans (add_le_add b3 b4)
    have hZ0 : 0 ≤ (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + ‖fderiv ℝ F x‖ := by
      positivity
    linarith [mul_le_mul_of_nonneg_left hZ (by linarith : (0:ℝ) ≤ 2 * ε),
      mul_le_mul_of_nonneg_right hε1 hZ0]
  -- the term with the factor `ε²`
  have hW : ‖kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x)‖ ≤
      (2 * |x.1| + |x.2.2|) * (4 * ‖fderiv ℝ F x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖)
        + ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ F x‖ + ‖F x‖) + ‖F x‖ := by
    have s1 := norm_sub_le (kAge (fun y => kAge F y + F y) x + (kAge F x + F x)) (hoopR (F x))
    have s2 := norm_add_le (kAge (fun y => kAge F y + F y) x) (kAge F x + F x)
    have s3 := norm_add_le (kAge F x) (F x)
    linarith [b5, b6, b8]
  have T4 : ‖ε ^ 2 • (kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x))‖ ≤
      (2 * |x.1| + |x.2.2|) * (4 * ‖fderiv ℝ F x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖)
        + ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ F x‖ + ‖F x‖) + ‖F x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε2']
    have hW0 := norm_nonneg (kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x))
    linarith [mul_le_mul_of_nonneg_right hε2 hW0, hW]
  -- assemble
  unfold vecDiffEps
  have s1 := norm_add_le (Axi.dQ (Axi.dQ F) x + Axi.dEta (Axi.dEta F) x -
    (2 * ε) • (kAge (Axi.dQ F) x + Axi.dQ F x))
    (ε ^ 2 • (kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x)))
  have s2 := norm_sub_le (Axi.dQ (Axi.dQ F) x + Axi.dEta (Axi.dEta F) x)
    ((2 * ε) • (kAge (Axi.dQ F) x + Axi.dQ F x))
  have s3 := norm_add_le (Axi.dQ (Axi.dQ F) x) (Axi.dEta (Axi.dEta F) x)
  have fin := final_ineq |x.1| |x.2.2| ‖F x‖ ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖
    ha hb hN0 hN1 hN2
  linarith [s1, s2, s3, b1, b2, T3, T4, fin]

end VecDiffJetHelp

open VecDiffJetHelp in
/-- **Second-order chart calculus** (SP 2367-2369): `K = 20` works. -/
theorem vecDiffJet : UnforcedLeray.Short.IIb.VecDiffJet := by
  refine ⟨20, by norm_num, ?_⟩
  intro ε hε0 hε1 F hF x
  have h0 : ‖iteratedFDeriv ℝ 0 F x‖ = ‖F x‖ := norm_iteratedFDeriv_zero
  have h1 : ‖iteratedFDeriv ℝ 1 F x‖ = ‖fderiv ℝ F x‖ := norm_iteratedFDeriv_one F
  have h2 : ‖iteratedFDeriv ℝ 2 F x‖ = ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1, h2]
  exact vecDiffJet_body hF ε hε0 hε1 x

end UnforcedLeray.Short.IIb

end
