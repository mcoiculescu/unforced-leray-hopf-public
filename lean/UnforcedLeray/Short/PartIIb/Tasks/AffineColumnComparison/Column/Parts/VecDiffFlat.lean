import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_8

/-!
# Part II-b, task `PartII-b:G4/3/8/5` (`VecDiffFlat`)

Source of record: `the November 2 reference manuscript` (SP), lines 2367-2369.
Pure chart calculus: `vecDiffEps ε F - (∂_q²F + ∂_η²F)` is the sum of the `ε`-terms
`-(2ε)(K+1)∂_qF` and `ε²(...)`; each is bounded by `ε` times the second-order jet of `F`
with polynomial weight `(1 + |s| + |η|)²`. We use `K = 8`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

namespace VecDiffFlatHelp

theorem fderiv_diff {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) :
    Differentiable ℝ (fderiv ℝ F) :=
  (hF.fderiv_right (m := 1) (by simp)).differentiable (by simp)

theorem dir_diff {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (u : Coord) :
    Differentiable ℝ (fun y => fderiv ℝ F y u) := fun y =>
  (fderiv_diff hF y).clm_apply (differentiableAt_const u)

/-- Directional derivative of the chart derivative `y ↦ ∂_u F(y)` in direction `w`. -/
theorem fderiv_dir {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x v w : Coord) :
    fderiv ℝ (fun y => fderiv ℝ F y v) x w = fderiv ℝ (fderiv ℝ F) x w v := by
  have := fderiv_clm_apply (fderiv_diff hF x) (differentiableAt_const v)
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
  have h1 := ((fderiv ℝ (fderiv ℝ F) x).le_opNorm w)
  have h2 := ((fderiv ℝ (fderiv ℝ F) x) w).le_opNorm v
  have hN := norm_nonneg (fderiv ℝ (fderiv ℝ F) x)
  have hW := norm_nonneg w
  nlinarith [norm_nonneg v, norm_nonneg (fderiv ℝ (fderiv ℝ F) x w), norm_nonneg (fderiv ℝ F x)]

/-- First-order directional bound. -/
theorem fderiv_le_norm {G : Coord → Axi.Merid} (x w : Coord) (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ G x w‖ ≤ ‖fderiv ℝ G x‖ :=
  ((fderiv ℝ G x).le_opNorm w).trans (mul_le_of_le_one_right (norm_nonneg _) hw)

/-- `kAge` is bounded by its two chart derivatives. -/
theorem norm_kAge_le {G : Coord → Axi.Merid} (x : Coord) {M : ℝ} (hM : 0 ≤ M)
    (hS : ‖Axi.dS G x‖ ≤ M) (hE : ‖Axi.dEta G x‖ ≤ M) :
    ‖kAge G x‖ ≤ (2 * |x.1| + |x.2.2|) * M := by
  unfold kAge
  have h2 : |2 * x.1| = 2 * |x.1| := by rw [abs_mul]; norm_num
  calc ‖(2 * x.1) • Axi.dS G x + x.2.2 • Axi.dEta G x‖
      ≤ ‖(2 * x.1) • Axi.dS G x‖ + ‖x.2.2 • Axi.dEta G x‖ := norm_add_le _ _
    _ = |2 * x.1| * ‖Axi.dS G x‖ + |x.2.2| * ‖Axi.dEta G x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |2 * x.1| * M + |x.2.2| * M := by
        gcongr
    _ = (2 * |x.1| + |x.2.2|) * M := by rw [h2]; ring

/-- The product rule for `kAge`. -/
theorem fderiv_kAge {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x w : Coord) :
    fderiv ℝ (fun y => kAge F y) x w =
      (2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x w + (2 * w.1) • Axi.dS F x +
        x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x w + w.2.2 • Axi.dEta F x := by
  have hS : DifferentiableAt ℝ (fun y => Axi.dS F y) x :=
    dir_diff hF (1, (0, 0)) x
  have hE : DifferentiableAt ℝ (fun y => Axi.dEta F y) x :=
    dir_diff hF (0, (0, 1)) x
  have hc1 : DifferentiableAt ℝ (fun y : Coord => 2 * y.1) x := by fun_prop
  have hc2 : DifferentiableAt ℝ (fun y : Coord => y.2.2) x := by fun_prop
  have hL1 : HasFDerivAt (fun y : Coord => 2 * y.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_fst).const_mul 2
  have hL2 : HasFDerivAt (fun y : Coord => y.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp x (hasFDerivAt_snd)
  have hdc1 : fderiv ℝ (fun y : Coord => 2 * y.1) x w = 2 * w.1 := by
    rw [hL1.fderiv]; simp
  have hdc2 : fderiv ℝ (fun y : Coord => y.2.2) x w = w.2.2 := by
    rw [hL2.fderiv]; simp
  unfold kAge
  have hA : DifferentiableAt ℝ (fun y : Coord => (2 * y.1) • Axi.dS F y) x := hc1.smul hS
  have hB : DifferentiableAt ℝ (fun y : Coord => y.2.2 • Axi.dEta F y) x := hc2.smul hE
  have e1 : fderiv ℝ (fun y : Coord => (2 * y.1) • Axi.dS F y) x =
      (2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x +
        (fderiv ℝ (fun y : Coord => 2 * y.1) x).smulRight (Axi.dS F x) :=
    fderiv_smul hc1 hS
  have e2 : fderiv ℝ (fun y : Coord => y.2.2 • Axi.dEta F y) x =
      x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x +
        (fderiv ℝ (fun y : Coord => y.2.2) x).smulRight (Axi.dEta F x) :=
    fderiv_smul hc2 hE
  rw [fderiv_fun_add hA hB, e1, e2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, hdc1, hdc2, smul_eq_mul]
  abel_nf

/-- `‖hoopR v‖ ≤ ‖v‖`. -/
theorem norm_hoopR_le (v : Axi.Merid) : ‖hoopR v‖ ≤ ‖v‖ := by
  unfold hoopR
  have hm0 : ‖Axi.m0‖ = 1 := by
    unfold Axi.m0
    simp [EuclideanSpace.norm_single]
  have hv : ‖v 0‖ ≤ ‖v‖ := PiLp.norm_apply_le v 0
  rw [norm_smul, hm0, mul_one]
  exact hv

/-- Second-order chart bound for `kAge F` in a unit direction. -/
theorem norm_fderiv_kAge_le {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x w : Coord)
    (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ (fun y => kAge F y) x w‖ ≤
      (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + 3 * ‖fderiv ℝ F x‖ := by
  have hes : ‖((1:ℝ), ((0:ℝ), (0:ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hee : ‖((0:ℝ), ((0:ℝ), (1:ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hwf : |w.1| ≤ 1 := by
    rw [← Real.norm_eq_abs]; exact (norm_fst_le w).trans hw
  have hws : |w.2.2| ≤ 1 := by
    rw [← Real.norm_eq_abs]; exact (norm_snd_le w.2).trans ((norm_snd_le w).trans hw)
  have hS1s : ‖Axi.dS F x‖ ≤ ‖fderiv ℝ F x‖ :=
    fderiv_le_norm (G := F) x ((1:ℝ), ((0:ℝ), (0:ℝ))) hes
  have hS1e : ‖Axi.dEta F x‖ ≤ ‖fderiv ℝ F x‖ :=
    fderiv_le_norm (G := F) x ((0:ℝ), ((0:ℝ), (1:ℝ))) hee
  have hX : ‖fderiv ℝ (fun y => Axi.dS F y) x w‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x ((1:ℝ), ((0:ℝ), (0:ℝ))) w hes hw
  have hY : ‖fderiv ℝ (fun y => Axi.dEta F y) x w‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x ((0:ℝ), ((0:ℝ), (1:ℝ))) w hee hw
  rw [fderiv_kAge hF x w]
  have h1 : ‖(2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x w‖ ≤
      (2 * |x.1|) * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  have h2 : ‖(2 * w.1) • Axi.dS F x‖ ≤ 2 * ‖fderiv ℝ F x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    calc 2 * |w.1| * ‖Axi.dS F x‖ ≤ 2 * 1 * ‖Axi.dS F x‖ := by
          gcongr
      _ ≤ 2 * ‖fderiv ℝ F x‖ := by linarith
  have h3 : ‖x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x w‖ ≤
      |x.2.2| * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hY (abs_nonneg _)
  have h4 : ‖w.2.2 • Axi.dEta F x‖ ≤ ‖fderiv ℝ F x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |w.2.2| * ‖Axi.dEta F x‖ ≤ 1 * ‖Axi.dEta F x‖ := by gcongr
      _ ≤ ‖fderiv ℝ F x‖ := by linarith
  have t1 := norm_add_le ((2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x w + (2 * w.1) • Axi.dS F x +
    x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x w) (w.2.2 • Axi.dEta F x)
  have t2 := norm_add_le ((2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x w + (2 * w.1) • Axi.dS F x)
    (x.2.2 • fderiv ℝ (fun y => Axi.dEta F y) x w)
  have t3 := norm_add_le ((2 * x.1) • fderiv ℝ (fun y => Axi.dS F y) x w)
    ((2 * w.1) • Axi.dS F x)
  have hab : (2 * |x.1|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + |x.2.2| * ‖fderiv ℝ (fderiv ℝ F) x‖ =
      (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ := by ring
  linarith [t1, t2, t3, h1, h2, h3, h4, hab]

end VecDiffFlatHelp

/-- The final polynomial inequality (pure arithmetic, `A = 2|s| + |η|`, `P = (1 + |s| + |η|)²`). -/
theorem vec_arith (ε a b S0 S1 S2 : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hS0 : 0 ≤ S0) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) :
    2 * ε * ((2 * a + b) * S2 + S1) +
        ε * ((2 * a + b) * ((2 * a + b) * S2 + 4 * S1) + ((2 * a + b) * S1 + S0) + S0) ≤
      ε * 8 * (1 + a + b) ^ 2 * (S0 + S1 + S2) := by
  have hAP : 2 * a + b ≤ (1 + a + b) ^ 2 := by nlinarith
  have hA2P : (2 * a + b) * (2 * a + b) ≤ 4 * (1 + a + b) ^ 2 := by nlinarith
  have hP1 : 1 ≤ (1 + a + b) ^ 2 := by nlinarith
  have p1 := mul_le_mul_of_nonneg_left hAP (mul_nonneg hε0 hS2)
  have p2 := mul_le_mul_of_nonneg_left hA2P (mul_nonneg hε0 hS2)
  have p3 := mul_le_mul_of_nonneg_left hP1 (mul_nonneg hε0 hS1)
  have p4 := mul_le_mul_of_nonneg_left hAP (mul_nonneg hε0 hS1)
  have p5 := mul_le_mul_of_nonneg_left hP1 (mul_nonneg hε0 hS0)
  have hP0 : 0 ≤ (1 + a + b) ^ 2 := by positivity
  have q0 := mul_nonneg (mul_nonneg hε0 hP0) hS0
  have q1 := mul_nonneg (mul_nonneg hε0 hP0) hS1
  have q2 := mul_nonneg (mul_nonneg hε0 hP0) hS2
  nlinarith [p1, p2, p3, p4, p5, q0, q1, q2]

open VecDiffFlatHelp in
/-- **The vector diffusion error is `O(ε)`** (SP 2367-2369). -/
theorem vecDiffFlat : VecDiffFlat := by
  refine ⟨8, by norm_num, ?_⟩
  intro ε hε0 hε1 F hF x
  have hF' : DifferentiableAt ℝ F x := (hF.differentiable (by simp)) x
  have hes : ‖((1:ℝ), ((0:ℝ), (0:ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hee : ‖((0:ℝ), ((0:ℝ), (1:ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hq : ‖((0:ℝ), ((1:ℝ), (0:ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have h2 : ‖iteratedFDeriv ℝ 2 F x‖ = ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (n := 1) (x := x)
    rw [norm_iteratedFDeriv_one] at h
    exact h.symm
  have hsum : ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l F x‖ =
      ‖F x‖ + ‖fderiv ℝ F x‖ + ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one, h2]
  rw [hsum]
  have hkDiff : DifferentiableAt ℝ (fun y => kAge F y) x := by
    have hc1 : DifferentiableAt ℝ (fun y : Coord => 2 * y.1) x := by fun_prop
    have hc2 : DifferentiableAt ℝ (fun y : Coord => y.2.2) x := by fun_prop
    unfold kAge
    exact (hc1.smul (dir_diff hF ((1:ℝ), ((0:ℝ), (0:ℝ))) x)).add
      (hc2.smul (dir_diff hF ((0:ℝ), ((0:ℝ), (1:ℝ))) x))
  have hdSdQ : ‖Axi.dS (Axi.dQ F) x‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x ((0:ℝ), ((1:ℝ), (0:ℝ))) ((1:ℝ), ((0:ℝ), (0:ℝ))) hq hes
  have hdEdQ : ‖Axi.dEta (Axi.dQ F) x‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    fderiv_dir_norm_le hF x ((0:ℝ), ((1:ℝ), (0:ℝ))) ((0:ℝ), ((0:ℝ), (1:ℝ))) hq hee
  have hdQF : ‖Axi.dQ F x‖ ≤ ‖fderiv ℝ F x‖ := fderiv_le_norm (G := F) x _ hq
  have hS1s : ‖Axi.dS F x‖ ≤ ‖fderiv ℝ F x‖ :=
    fderiv_le_norm (G := F) x ((1:ℝ), ((0:ℝ), (0:ℝ))) hes
  have hS1e : ‖Axi.dEta F x‖ ≤ ‖fderiv ℝ F x‖ :=
    fderiv_le_norm (G := F) x ((0:ℝ), ((0:ℝ), (1:ℝ))) hee
  have hkQ : ‖kAge (Axi.dQ F) x‖ ≤ (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ :=
    norm_kAge_le x (M := ‖fderiv ℝ (fderiv ℝ F) x‖) (by positivity) hdSdQ hdEdQ
  have hGS : Axi.dS (fun y => kAge F y + F y) x =
      fderiv ℝ (fun y => kAge F y) x ((1:ℝ), ((0:ℝ), (0:ℝ))) +
        fderiv ℝ F x ((1:ℝ), ((0:ℝ), (0:ℝ))) := by
    unfold Axi.dS
    rw [fderiv_fun_add hkDiff hF']
    rfl
  have hGE : Axi.dEta (fun y => kAge F y + F y) x =
      fderiv ℝ (fun y => kAge F y) x ((0:ℝ), ((0:ℝ), (1:ℝ))) +
        fderiv ℝ F x ((0:ℝ), ((0:ℝ), (1:ℝ))) := by
    unfold Axi.dEta
    rw [fderiv_fun_add hkDiff hF']
    rfl
  have hGS' : ‖Axi.dS (fun y => kAge F y + F y) x‖ ≤
      (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + 4 * ‖fderiv ℝ F x‖ := by
    rw [hGS]
    have t := norm_add_le (fderiv ℝ (fun y => kAge F y) x ((1:ℝ), ((0:ℝ), (0:ℝ))))
      (fderiv ℝ F x ((1:ℝ), ((0:ℝ), (0:ℝ))))
    have k1 := norm_fderiv_kAge_le hF x ((1:ℝ), ((0:ℝ), (0:ℝ))) hes
    have k2 := fderiv_le_norm (G := F) x ((1:ℝ), ((0:ℝ), (0:ℝ))) hes
    linarith
  have hGE' : ‖Axi.dEta (fun y => kAge F y + F y) x‖ ≤
      (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + 4 * ‖fderiv ℝ F x‖ := by
    rw [hGE]
    have t := norm_add_le (fderiv ℝ (fun y => kAge F y) x ((0:ℝ), ((0:ℝ), (1:ℝ))))
      (fderiv ℝ F x ((0:ℝ), ((0:ℝ), (1:ℝ))))
    have k1 := norm_fderiv_kAge_le hF x ((0:ℝ), ((0:ℝ), (1:ℝ))) hee
    have k2 := fderiv_le_norm (G := F) x ((0:ℝ), ((0:ℝ), (1:ℝ))) hee
    linarith
  have hkG : ‖kAge (fun y => kAge F y + F y) x‖ ≤
      (2 * |x.1| + |x.2.2|) *
        ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + 4 * ‖fderiv ℝ F x‖) :=
    norm_kAge_le x (M := (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + 4 * ‖fderiv ℝ F x‖)
      (by positivity) hGS' hGE'
  have hkF : ‖kAge F x‖ ≤ (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ F x‖ :=
    norm_kAge_le x (M := ‖fderiv ℝ F x‖) (by positivity) hS1s hS1e
  have hhoop : ‖hoopR (F x)‖ ≤ ‖F x‖ := norm_hoopR_le (F x)
  have hid : vecDiffEps ε F x - (Axi.dQ (Axi.dQ F) x + Axi.dEta (Axi.dEta F) x) =
      -((2 * ε) • (kAge (Axi.dQ F) x + Axi.dQ F x)) +
        ε ^ 2 • (kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x)) := by
    unfold vecDiffEps
    module
  have hA : ‖kAge (Axi.dQ F) x + Axi.dQ F x‖ ≤
      (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + ‖fderiv ℝ F x‖ := by
    have t := norm_add_le (kAge (Axi.dQ F) x) (Axi.dQ F x)
    linarith
  have hT : ‖kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x)‖ ≤
      (2 * |x.1| + |x.2.2|) *
          ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + 4 * ‖fderiv ℝ F x‖) +
        ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ F x‖ + ‖F x‖) + ‖F x‖ := by
    have t1 := norm_add_le (kAge (fun y => kAge F y + F y) x) (kAge F x + F x)
    have t2 := norm_add_le (kAge F x) (F x)
    have t3 := norm_sub_le (kAge (fun y => kAge F y + F y) x + (kAge F x + F x)) (hoopR (F x))
    linarith
  rw [hid]
  have hL : ‖-((2 * ε) • (kAge (Axi.dQ F) x + Axi.dQ F x)) +
      ε ^ 2 • (kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x))‖ ≤
      2 * ε * ‖kAge (Axi.dQ F) x + Axi.dQ F x‖ +
        ε ^ 2 * ‖kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x)‖ := by
    have t := norm_add_le (-((2 * ε) • (kAge (Axi.dQ F) x + Axi.dQ F x)))
      (ε ^ 2 • (kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x)))
    rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ε),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ε ^ 2)] at t
    exact t
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hTn0 := norm_nonneg (kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x))
  have hTb2 : ε ^ 2 * ‖kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x)‖ ≤
      ε * ((2 * |x.1| + |x.2.2|) *
          ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + 4 * ‖fderiv ℝ F x‖) +
        ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ F x‖ + ‖F x‖) + ‖F x‖) := by
    have h1 := mul_le_mul_of_nonneg_right hε2 hTn0
    have h2 := mul_le_mul_of_nonneg_left hT hε0
    linarith
  have hkb : 2 * ε * ‖kAge (Axi.dQ F) x + Axi.dQ F x‖ ≤
      2 * ε * ((2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ F) x‖ + ‖fderiv ℝ F x‖) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have key := vec_arith ε |x.1| |x.2.2| ‖F x‖ ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖
    hε0 hε1 (abs_nonneg _) (abs_nonneg _) (by positivity) (by positivity) (by positivity)
  calc _ ≤ 2 * ε * ‖kAge (Axi.dQ F) x + Axi.dQ F x‖ +
        ε ^ 2 * ‖kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x)‖ := hL
    _ ≤ ε * 8 * (1 + |x.1| + |x.2.2|) ^ 2 * (‖F x‖ + ‖fderiv ℝ F x‖ + ‖fderiv ℝ (fderiv ℝ F) x‖) := by
        linarith [key, hkb, hTb2]

end UnforcedLeray.Short.IIb

end
