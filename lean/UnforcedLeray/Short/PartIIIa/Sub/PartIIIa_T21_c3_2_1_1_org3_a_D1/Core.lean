import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Assembly

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: the drift of the pairing

Source: SP 2962-2964 (Duhamel against the transported compact test), SP 2954-2956 (`δ_ν → 0`),
SP 2937-2958 (energy bound).

`drift_bound`: along a regular free cylinder flow with weighted energy `≤ a⁻³ L²`, the pairing
`I(σ) = ∫ ω(σ) cmp(σ)` with the transported profile moves by at most
`2 R L (C_Q/b + ε' C_Y) (z(t) - z(s))`: the residual is `ν Q + √a (v - V_iso)·∇_yΦ`
(`cmpRes_eq`), with `ν ≤ (b a)⁻¹` on `θ ≥ b` and `|v - V_iso| ≤ ε' a^{-3/2}` (`FmrVelGap`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

theorem train_contDiff_comp {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {σ : ℝ}
    (hσ : 0 ≤ σ) (j : Fin 2) : ContDiff ℝ 1 (fun x => tr.v σ x j) :=
  (EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp
    (UnforcedLeray.Short.IIb.TransportIBP.contDiff_one_of_top
      (UnforcedLeray.Short.IIb.TransportIBP.contDiff_slice tr hσ))

theorem train_div {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ)
    (x : ℝ × ℝ) :
    B0579.pd 0 (fun x => tr.v σ x 0) x + B0579.pd 1 (fun x => tr.v σ x 1) x = 0 := by
  have h := tr.isTrain.solenoidal σ hσ x
  unfold UnforcedLeray.Cyl.divergence at h
  rw [UnforcedLeray.Short.IIb.TransportIBP.pd0_eq_partialQ
      ((train_contDiff_comp tr hσ 0).differentiable (by norm_num)),
    UnforcedLeray.Short.IIb.TransportIBP.pd1_eq_partialEta
      ((train_contDiff_comp tr hσ 1).differentiable (by norm_num))]
  exact h

theorem sqrt_mul_rpow {a : ℝ} (ha : 0 < a) :
    Real.sqrt a * a ^ (-(3 / 2) : ℝ) = a⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha]
  norm_num
  exact Real.rpow_neg_one a

theorem one_le_movWeight {m a : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (x : ℝ × ℝ) :
    1 ≤ movWeight m a x := by
  unfold movWeight
  exact Real.one_le_rpow (by have : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / a := by positivity
                             linarith) hm

theorem continuous_movWeight (m : ℝ) {a : ℝ} (ha : 0 < a) : Continuous (movWeight m a) := by
  unfold movWeight
  refine Continuous.rpow_const (by fun_prop) fun x => Or.inl ?_
  have : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / a := by positivity
  linarith

theorem theta_anti' {ν r s : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hrs : r ≤ s) :
    clockTheta ν s ≤ clockTheta ν r := by
  unfold clockTheta
  have h1 := clockA_pos hν.le hr
  exact inv_anti₀ (mul_pos hν h1) (mul_le_mul_of_nonneg_left (clockA_mono hν.le hrs) hν.le)

/-- **The drift of the pairing** along a regular free cylinder flow. -/
theorem drift_bound {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R : ℝ} (hR : 0 < R)
    (hgR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g y = 0)
    {CQ CY Z : ℝ}
    (hCQ : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 → p.1 ≤ Z → |bracketQ (tprof g) p| ≤ CQ)
    (hCY : ∀ j : Fin 2, ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 → p.1 ≤ Z → |dY (tprof g) j p| ≤ CY)
    {m b ν ε' Lb s t T : ℝ} (hm : 0 ≤ m) (hb : 1 ≤ b) (hν : 0 < ν)
    (hνR : ν * (2 * R + 1) ≤ 1) (hε' : 0 ≤ ε') (hLb : 0 < Lb)
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (hθ : b ≤ clockTheta ν t)
    (hZ : movingZ ν t - movingZ ν s ≤ Z)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hgap : ∀ σ ∈ Icc s t, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      |tr.v σ x 0 - (UnforcedLeray.B0146.isoVelocity ν σ x).1| +
        |tr.v σ x 1 - (UnforcedLeray.B0146.isoVelocity ν σ x).2| ≤
          ε' * clockA ν σ ^ (-(3 / 2) : ℝ))
    {M : ℝ} (hM : ∀ σ ∈ Icc s t, ∀ x, |tr.v σ x 0| + |tr.v σ x 1| ≤ M)
    {om : ℝ → ℝ × ℝ → ℝ}
    (hom : UnforcedLeray.Short.IIb.IsRegularCylFlow (ν ^ (-2 : ℝ)) ν tr.v s T om)
    (hEi : ∀ σ ∈ Icc s t, IntegrableOn (fun x => om σ x ^ 2 * movWeight m (clockA ν σ) x)
      (B0579.cell (ν ^ (-2 : ℝ))))
    (hE : ∀ σ ∈ Icc s t, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      om σ x ^ 2 * movWeight m (clockA ν σ) x ≤ (clockA ν σ)⁻¹ ^ 3 * Lb ^ 2) :
    |(∫ x, om t x * cmp (tprof g) ν s t x) - ∫ x, om s x * cmp (tprof g) ν s s x| ≤
      2 * R * Lb * (CQ / b + ε' * CY) * (movingZ ν t - movingZ ν s) := by
  have hν0 : 0 ≤ ν := hν.le
  have hΦ2 : ContDiff ℝ 2 (tprof g) := contDiff_infty.1 (contDiff_tprof hg) 2
  have hsupp : SuppIn R (tprof g) := fun p hp => tprof_eq_zero hgR hp
  obtain ⟨hcont, hder⟩ := pairing_hasDeriv hΦ2 hR.le hsupp hν hs hst htT
    (fun σ hσ j => train_contDiff_comp tr (hs.trans hσ.1) j)
    (fun σ hσ x => train_div tr (hs.trans hσ.1) x) hM hom
  have hCQ0 : 0 ≤ CQ := (abs_nonneg _).trans (hCQ (0, (0, 0)) le_rfl
    (le_trans (sub_nonneg.2 (movingZ_mono hν0 hs hst)) hZ))
  have hCY0 : 0 ≤ CY := (abs_nonneg _).trans (hCY 0 (0, (0, 0)) le_rfl
    (le_trans (sub_nonneg.2 (movingZ_mono hν0 hs hst)) hZ))
  have hb0 : 0 < b := by linarith
  refine abs_sub_le_of_deriv_bound hν0 hs hst hcont hder fun τ hτ => ?_
  have hτ0 : 0 ≤ τ := hs.trans hτ.1
  have hτI : τ ∈ Icc s t := Ico_subset_Icc_self hτ
  set a := clockA ν τ with ha_def
  have ha : 0 < a := clockA_pos hν0 hτ0
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hθτ : b ≤ clockTheta ν τ := hθ.trans (theta_anti' hν hτ0 hτI.2)
  -- `ν ≤ (b a)⁻¹`
  have hνba : ν ≤ (b * a)⁻¹ := by
    have hθτ' : b ≤ (ν * a)⁻¹ := hθτ
    have hp : 0 < ν * a := mul_pos hν ha
    have h1 : b * (ν * a) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hθτ' hp.le
      rwa [inv_mul_cancel₀ hp.ne'] at this
    have h2 : ν * (b * a) ≤ 1 := by nlinarith [h1]
    have hba : 0 < b * a := mul_pos hb0 ha
    calc ν = ν * (b * a) / (b * a) := by field_simp
      _ ≤ 1 / (b * a) := div_le_div_of_nonneg_right h2 hba.le
      _ = (b * a)⁻¹ := one_div _
  set r := R * Real.sqrt a with hr
  have hrc : r < ν ^ (-2 : ℝ) / 2 := radius_lt_half_cell hν hνR hR.le hb hτ0 hθτ
  set Bnd := (CQ / b + ε' * CY) / a with hBnd
  have hBnd0 : 0 ≤ Bnd := by positivity
  have hslab : ∀ x, 0 ≤ (cpt ν s τ x).1 ∧ (cpt ν s τ x).1 ≤ Z := by
    intro x
    simp only [cpt]
    refine ⟨sub_nonneg.2 (movingZ_mono hν0 hs hτ.1), ?_⟩
    linarith [movingZ_mono hν0 hτ0 hτI.2]
  have hin : ∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) r,
      |cmpRes (tprof g) tr.v ν s τ x| ≤ Bnd := by
    intro x hx
    have hxc := mem_cell_of_mem_closedBall hrc hx
    have hgx := hgap τ hτI x hxc
    rw [cmpRes_eq hg hν0 hτ0, ← ha_def]
    have hQ := hCQ _ (hslab x).1 (hslab x).2
    have hY0 := hCY 0 _ (hslab x).1 (hslab x).2
    have hY1 := hCY 1 _ (hslab x).1 (hslab x).2
    set d0 := tr.v τ x 0 - (UnforcedLeray.B0146.isoVelocity ν τ x).1
    set d1 := tr.v τ x 1 - (UnforcedLeray.B0146.isoVelocity ν τ x).2
    have hsr : Real.sqrt a * a ^ (-(3 / 2) : ℝ) = a⁻¹ := sqrt_mul_rpow ha
    have e1 : |d0 * dY (tprof g) 0 (cpt ν s τ x) + d1 * dY (tprof g) 1 (cpt ν s τ x)| ≤
        (|d0| + |d1|) * CY := by
      calc _ ≤ |d0 * dY (tprof g) 0 (cpt ν s τ x)| + |d1 * dY (tprof g) 1 (cpt ν s τ x)| :=
            abs_add_le _ _
        _ ≤ |d0| * CY + |d1| * CY := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left hY0 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hY1 (abs_nonneg _))
        _ = (|d0| + |d1|) * CY := by ring
    calc |ν * bracketQ (tprof g) (cpt ν s τ x) + Real.sqrt a *
          (d0 * dY (tprof g) 0 (cpt ν s τ x) + d1 * dY (tprof g) 1 (cpt ν s τ x))|
        ≤ ν * CQ + Real.sqrt a * ((ε' * a ^ (-(3 / 2) : ℝ)) * CY) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_of_nonneg hν0]
            exact mul_le_mul_of_nonneg_left hQ hν0
          · rw [abs_mul, abs_of_pos hsa]
            exact mul_le_mul_of_nonneg_left (e1.trans
              (mul_le_mul_of_nonneg_right hgx hCY0)) hsa.le
      _ = ν * CQ + ε' * CY / a := by
          rw [show Real.sqrt a * (ε' * a ^ (-(3 / 2) : ℝ) * CY) =
            (Real.sqrt a * a ^ (-(3 / 2) : ℝ)) * (ε' * CY) by ring, hsr]
          field_simp
      _ ≤ Bnd := by
          rw [hBnd, add_div]
          refine add_le_add ?_ le_rfl
          calc ν * CQ ≤ (b * a)⁻¹ * CQ := mul_le_mul_of_nonneg_right hνba hCQ0
            _ = CQ / b / a := by field_simp
  have hout : ∀ x ∉ Metric.closedBall (0 : ℝ × ℝ) r, cmpRes (tprof g) tr.v ν s τ x = 0 := by
    intro x hx
    have hp := cpt_outside (s := s) hν0 hτ0 le_rfl hR.le hx
    rw [cmpRes_eq hg hν0 hτ0, suppIn_bracketQ hsupp _ hp, suppIn_dY hsupp 0 _ hp,
      suppIn_dY hsupp 1 _ hp]
    ring
  have hA : ∫ x in Metric.closedBall (0 : ℝ × ℝ) r, om τ x ^ 2 ≤ a⁻¹ ^ 3 * Lb ^ 2 := by
    have hK := isCompact_closedBall (0 : ℝ × ℝ) r
    have hwc : Continuous (om τ) :=
      ((hom.slice τ ⟨hτ.1, hτI.2.trans htT⟩).smooth).continuous
    have i1 : IntegrableOn (fun x => om τ x ^ 2) (Metric.closedBall (0 : ℝ × ℝ) r) :=
      (hwc.pow 2).continuousOn.integrableOn_compact hK
    have i2 : IntegrableOn (fun x => om τ x ^ 2 * movWeight m a x)
        (Metric.closedBall (0 : ℝ × ℝ) r) :=
      ((hwc.pow 2).mul (continuous_movWeight m ha)).continuousOn.integrableOn_compact hK
    have hsub : Metric.closedBall (0 : ℝ × ℝ) r ⊆ B0579.cell (ν ^ (-2 : ℝ)) :=
      fun x hx => mem_cell_of_mem_closedBall hrc hx
    calc ∫ x in Metric.closedBall (0 : ℝ × ℝ) r, om τ x ^ 2
        ≤ ∫ x in Metric.closedBall (0 : ℝ × ℝ) r, om τ x ^ 2 * movWeight m a x :=
          setIntegral_mono_on i1 i2 measurableSet_closedBall fun x _ =>
            le_mul_of_one_le_right (sq_nonneg _) (one_le_movWeight hm ha x)
      _ ≤ ∫ x in B0579.cell (ν ^ (-2 : ℝ)), om τ x ^ 2 * movWeight m a x :=
          setIntegral_mono_set (hEi τ hτI)
            ((ae_restrict_iff' (B0579.measurableSet_cell _)).2 (Eventually.of_forall fun x _ =>
              mul_nonneg (sq_nonneg _) ((zero_le_one).trans (one_le_movWeight hm ha x))))
            (Eventually.of_forall hsub)
      _ ≤ a⁻¹ ^ 3 * Lb ^ 2 := hE τ hτI
  have hwc : Continuous (om τ) := ((hom.slice τ ⟨hτ.1, hτI.2.trans htT⟩).smooth).continuous
  have hL : 0 < a⁻¹ ^ 2 * Lb / (2 * R) := by positivity
  have key := abs_integral_mul_le hwc hBnd0 hL hin hout hA
  rw [volume_real_closedBall_zero r (by positivity)] at key
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hvol : (2 * r) ^ 2 = 4 * R ^ 2 * a := by rw [hr, mul_pow, mul_pow, hsq]; ring
  rw [hvol] at key
  refine key.trans (le_of_eq ?_)
  rw [hBnd]
  have hR0 : R ≠ 0 := hR.ne'
  have hLb0 : Lb ≠ 0 := hLb.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hb0' : b ≠ 0 := hb0.ne'
  field_simp
  ring

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
