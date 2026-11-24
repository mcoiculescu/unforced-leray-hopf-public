import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_8

/-!
# Part II-b, task `PartII-b:G4/3/8/6` (`BEpsFlat`): the interaction differs from the flat one by `O(ε)`

Source of record: `the November 2 reference manuscript` (SP), lines 2370-2374.
With `raw = train + ε·raised` (`rawProf_eq`) and `raised 0 = 0` (`m1 0 = 0`), the difference
`B_εF - B_0F` is an explicit sum of four terms, each with a factor `ε`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- Directional derivative of `F + c • G` (both differentiable at `x`). -/
theorem beF_fderiv_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (w : Coord) :
    fderiv ℝ (fun y => F y + c • G y) x w = fderiv ℝ F x w + c • fderiv ℝ G x w := by
  have e : (fun y => F y + c • G y) = F + c • G := rfl
  have e2 : fderiv ℝ (c • G) x = c • fderiv ℝ G x := fderiv_const_smul hG c
  rw [e, fderiv_add hF (hG.const_smul c), e2]
  simp

theorem beF_dQ_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    Axi.dQ (fun y => F y + c • G y) x = Axi.dQ F x + c • Axi.dQ G x := by
  unfold Axi.dQ
  exact beF_fderiv_add_smul hF hG _

theorem beF_dEta_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    Axi.dEta (fun y => F y + c • G y) x = Axi.dEta F x + c • Axi.dEta G x := by
  unfold Axi.dEta
  exact beF_fderiv_add_smul hF hG _

theorem beF_dS_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    Axi.dS (fun y => F y + c • G y) x = Axi.dS F x + c • Axi.dS G x := by
  unfold Axi.dS
  exact beF_fderiv_add_smul hF hG _

theorem beF_kAge_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    kAge (fun y => F y + c • G y) x = kAge F x + c • kAge G x := by
  unfold kAge
  rw [beF_dS_add_smul hF hG, beF_dEta_add_smul hF hG]
  module

/-- `b_raw = v + ε·h` in the chart, with `h = raisedMerid p`, `v = trainProf p`. -/
theorem beF_rawProf_eq (p : Params) :
    rawProf p = fun y => trainProf p y + p.ε • raisedMerid p y :=
  rawProf_eq p

/-- The algebraic identity behind `BEpsFlat`: the four `ε`-terms. -/
theorem beF_bEps_sub_flatB (p : Params) (F : Coord → Axi.Merid) (x : Coord)
    (hv : DifferentiableAt ℝ (trainProf p) x) (hh : DifferentiableAt ℝ (raisedMerid p) x) :
    bEps p F x - flatB p F x =
      (-(p.ε * trainProf p x 0)) • (kAge F x + F x)
      + (p.ε * raisedMerid p x 1) • Axi.dEta F x
      + (F x 0 * p.ε) • (Axi.dQ (raisedMerid p) x - (kAge (rawProf p) x + rawProf p x))
      + (F x 1 * p.ε) • Axi.dEta (raisedMerid p) x := by
  have h0 : raisedMerid p x 0 = 0 := by simp [raisedMerid, Axi.m1_zero]
  have hr0 : rawProf p x 0 = trainProf p x 0 := by
    rw [beF_rawProf_eq p]
    simp [h0]
  unfold bEps flatB qEps
  rw [hr0, beF_rawProf_eq p]
  beta_reduce
  rw [beF_dQ_add_smul hv hh, beF_dEta_add_smul hv hh, beF_kAge_add_smul hv hh]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  module

/-- Norm of a scalar multiple, bounded by a bound on the scalar times a bound on the vector. -/
theorem beF_norm_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (w : E) (C B : ℝ) (ha : |a| ≤ C) (hw : ‖w‖ ≤ B) : ‖a • w‖ ≤ C * B := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul ha hw (norm_nonneg _) ((abs_nonneg _).trans ha)

/-- Norm of `u + ε • w` for `0 ≤ ε ≤ 1`. -/
theorem beF_norm_add_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u w : E) (ε A B : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hu : ‖u‖ ≤ A) (hw : ‖w‖ ≤ B) :
    ‖u + ε • w‖ ≤ A + B := by
  have hB : 0 ≤ B := (norm_nonneg w).trans hw
  have h1 : ‖ε • w‖ ≤ B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0]
    exact (mul_le_of_le_one_left (norm_nonneg w) hε1).trans hw
  exact (norm_add_le u (ε • w)).trans (add_le_add hu h1)

theorem beF_chartJet_nonneg (G : Coord → Axi.Merid) (x : Coord) : 0 ≤ chartJet G x := by
  unfold chartJet
  positivity

theorem beF_cj_norm (G : Coord → Axi.Merid) (x : Coord) : ‖G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (Axi.dQ G x)
  have := norm_nonneg (Axi.dEta G x)
  have := norm_nonneg (kAge G x)
  linarith

theorem beF_cj_dQ (G : Coord → Axi.Merid) (x : Coord) : ‖Axi.dQ G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (G x)
  have := norm_nonneg (Axi.dEta G x)
  have := norm_nonneg (kAge G x)
  linarith

theorem beF_cj_dEta (G : Coord → Axi.Merid) (x : Coord) : ‖Axi.dEta G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (G x)
  have := norm_nonneg (Axi.dQ G x)
  have := norm_nonneg (kAge G x)
  linarith

theorem beF_cj_kAge (G : Coord → Axi.Merid) (x : Coord) : ‖kAge G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (G x)
  have := norm_nonneg (Axi.dQ G x)
  have := norm_nonneg (Axi.dEta G x)
  linarith

theorem beF_cj_sum (G : Coord → Axi.Merid) (x : Coord) :
    ‖kAge G x + G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (Axi.dQ G x)
  have := norm_nonneg (Axi.dEta G x)
  linarith [norm_add_le (kAge G x) (G x)]

theorem beF_comp_le (w : Axi.Merid) (i : Fin 2) (C : ℝ) (h : ‖w‖ ≤ C) : |w i| ≤ C := by
  have := PiLp.norm_apply_le w i
  rw [Real.norm_eq_abs] at this
  exact this.trans h

/-- **The interaction is `O(ε)` from the flat one** (SP 2370-2374): for `0 ≤ ε ≤ 1`,
`‖B_εF - B_0F‖ ≤ 6 ε J(F)(J(v) + J(He_z))`. -/
theorem bEpsFlat : UnforcedLeray.Short.IIb.BEpsFlat := by
  intro p hε0 hε1 F x hv hh
  rw [beF_bEps_sub_flatB p F x hv hh]
  have hv0 : |trainProf p x 0| ≤ chartJet (trainProf p) x :=
    beF_comp_le _ 0 _ (beF_cj_norm _ _)
  have hh1 : |raisedMerid p x 1| ≤ chartJet (raisedMerid p) x :=
    beF_comp_le _ 1 _ (beF_cj_norm _ _)
  have hF0 : |F x 0| ≤ chartJet F x := beF_comp_le _ 0 _ (beF_cj_norm _ _)
  have hF1 : |F x 1| ≤ chartJet F x := beF_comp_le _ 1 _ (beF_cj_norm _ _)
  have hraw : ‖rawProf p x‖ ≤ chartJet (trainProf p) x + chartJet (raisedMerid p) x := by
    rw [beF_rawProf_eq p]
    exact beF_norm_add_smul_le _ _ _ _ _ hε0 hε1 (beF_cj_norm _ _) (beF_cj_norm _ _)
  have hkraw : ‖kAge (rawProf p) x‖ ≤ chartJet (trainProf p) x + chartJet (raisedMerid p) x := by
    rw [beF_rawProf_eq p, beF_kAge_add_smul hv hh]
    exact beF_norm_add_smul_le _ _ _ _ _ hε0 hε1 (beF_cj_kAge _ _) (beF_cj_kAge _ _)
  have hJv0 := beF_chartJet_nonneg (trainProf p) x
  have hJh0 := beF_chartJet_nonneg (raisedMerid p) x
  have hJF0 := beF_chartJet_nonneg F x
  have t1 : ‖(-(p.ε * trainProf p x 0)) • (kAge F x + F x)‖ ≤
      (p.ε * chartJet (trainProf p) x) * chartJet F x := by
    apply beF_norm_smul_le
    · rw [abs_neg, abs_mul, abs_of_nonneg hε0]
      exact mul_le_mul_of_nonneg_left hv0 hε0
    · exact beF_cj_sum F x
  have t2 : ‖(p.ε * raisedMerid p x 1) • Axi.dEta F x‖ ≤
      (p.ε * chartJet (raisedMerid p) x) * chartJet F x := by
    apply beF_norm_smul_le
    · rw [abs_mul, abs_of_nonneg hε0]
      exact mul_le_mul_of_nonneg_left hh1 hε0
    · exact beF_cj_dEta F x
  have hdiff : ‖Axi.dQ (raisedMerid p) x - (kAge (rawProf p) x + rawProf p x)‖ ≤
      chartJet (raisedMerid p) x +
        ((chartJet (trainProf p) x + chartJet (raisedMerid p) x) +
          (chartJet (trainProf p) x + chartJet (raisedMerid p) x)) := by
    refine (norm_sub_le _ _).trans ?_
    have h1 := beF_cj_dQ (raisedMerid p) x
    have h2 : ‖kAge (rawProf p) x + rawProf p x‖ ≤
        (chartJet (trainProf p) x + chartJet (raisedMerid p) x) +
          (chartJet (trainProf p) x + chartJet (raisedMerid p) x) :=
      (norm_add_le _ _).trans (add_le_add hkraw hraw)
    linarith
  have t3 : ‖(F x 0 * p.ε) • (Axi.dQ (raisedMerid p) x - (kAge (rawProf p) x + rawProf p x))‖
      ≤ (chartJet F x * p.ε) *
        (chartJet (raisedMerid p) x +
          ((chartJet (trainProf p) x + chartJet (raisedMerid p) x) +
            (chartJet (trainProf p) x + chartJet (raisedMerid p) x))) := by
    apply beF_norm_smul_le
    · rw [abs_mul, abs_of_nonneg hε0]
      exact mul_le_mul_of_nonneg_right hF0 hε0
    · exact hdiff
  have t4 : ‖(F x 1 * p.ε) • Axi.dEta (raisedMerid p) x‖ ≤
      (chartJet F x * p.ε) * chartJet (raisedMerid p) x := by
    apply beF_norm_smul_le
    · rw [abs_mul, abs_of_nonneg hε0]
      exact mul_le_mul_of_nonneg_right hF1 hε0
    · exact beF_cj_dEta _ _
  have hsum : ∀ a b c d : Axi.Merid, ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have e1 := norm_add_le (a + b + c) d
    have e2 := norm_add_le (a + b) c
    have e3 := norm_add_le a b
    linarith
  refine (hsum _ _ _ _).trans ?_
  nlinarith [mul_nonneg (mul_nonneg hε0 hJF0) hJv0, mul_nonneg (mul_nonneg hε0 hJF0) hJh0]

end UnforcedLeray.Short.IIb
