import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdTransDeriv.Taylor

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.NearInst.OdHelp
open UnforcedLeray.PhaseSpace
open scoped ContDiff

section Transp

variable {P : ℝ} [Fact (0 < P)]

theorem toCell_snd_coe (w : UnforcedLeray.B0223.PSpace P) :
    (((UnforcedLeray.B0223.toCell P w).2 : ℝ) : AddCircle P) = w.2 := by
  unfold UnforcedLeray.B0223.toCell
  exact AddCircle.coe_equivIoc

theorem toCell_fst (w : UnforcedLeray.B0223.PSpace P) :
    (UnforcedLeray.B0223.toCell P w).1 = w.1 := rfl

theorem toCell_snd_mem (w : UnforcedLeray.B0223.PSpace P) :
    (UnforcedLeray.B0223.toCell P w).2 ∈ Icc 0 P := by
  unfold UnforcedLeray.B0223.toCell
  have h := (AddCircle.measurableEquivIoc P 0 w.2 : Ioc (0 : ℝ) (0 + P)).2
  rw [Set.mem_Ioc] at h
  exact ⟨h.1.le, by linarith [h.2]⟩

/-- The a.e. representative of `transC (-r) Ψ`: a phase shift of the representative of `Ψ`. -/
theorem transC_ae_repr (ψ : ℝ × Space → CVec3) (hper : ∀ τ y, ψ (τ + P, y) = ψ (τ, y))
    (Ψ : XC P)
    (hΨ : (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
    (r : ℝ) :
    ∀ᵐ z ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      ((UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r) Ψ :
        UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) z) =
        ψ ((UnforcedLeray.B0223.toCell P z).2 + r, (UnforcedLeray.B0223.toCell P z).1) := by
  have h1 := UnforcedLeray.B0223.coeFn_transC (E := UnforcedLeray.B0223.SpaceC) (-r) Ψ
  have h2 := (UnforcedLeray.B0223.mp_shiftT (P := P) (-r)).quasiMeasurePreserving.ae_eq_comp hΨ
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [Function.comp_apply] at hz2
  rw [hz1, hz2]
  have hx : (UnforcedLeray.B0223.toCell P (UnforcedLeray.B0223.shiftT P (-r) z)).1 =
      (UnforcedLeray.B0223.toCell P z).1 := by
    rw [toCell_fst, UnforcedLeray.B0223.shiftT_apply, toCell_fst]
  have hτ : (((UnforcedLeray.B0223.toCell P (UnforcedLeray.B0223.shiftT P (-r) z)).2 : ℝ) :
      AddCircle P) = (((UnforcedLeray.B0223.toCell P z).2 + r : ℝ) : AddCircle P) := by
    rw [toCell_snd_coe, UnforcedLeray.B0223.shiftT_apply, AddCircle.coe_add, toCell_snd_coe,
      AddCircle.coe_neg, sub_neg_eq_add]
  rw [hx]
  exact periodic_lift_coe (f := fun t : ℝ => ψ (t, (UnforcedLeray.B0223.toCell P z).1))
    (fun t => hper t _) hτ

/-- Pointwise Taylor bound for the phase translation on a smooth phase test, with the
`L²`-support set `closedBall 0 R × univ`. -/
theorem transC_pointwise (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest P ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ R : ℝ, ∀ r : ℝ, |r| ≤ 1 → ∀ z : UnforcedLeray.B0223.PSpace P,
      ‖ψ ((UnforcedLeray.B0223.toCell P z).2 + r, (UnforcedLeray.B0223.toCell P z).1)
        - ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)
        - r • dτ ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)‖
        ≤ (Metric.closedBall (0 : Space) R ×ˢ (univ : Set (AddCircle P))).indicator
            (fun _ => M * r ^ 2) z := by
  classical
  obtain ⟨R, hR⟩ := hψ.bounded_support
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hF : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Space) => ((p.2.1 + p.1 : ℝ), p.2.2)) :=
    ((contDiff_snd.fst).add contDiff_fst).prodMk contDiff_snd.snd
  have hGs : ContDiff ℝ 2 (fun p : ℝ × (ℝ × Space) => ψ (p.2.1 + p.1, p.2.2)) :=
    (hψ.smooth.comp hF).of_le (by simp)
  have hGd : Differentiable ℝ (fun p : ℝ × (ℝ × Space) => ψ (p.2.1 + p.1, p.2.2)) :=
    hGs.differentiable (by norm_num)
  obtain ⟨M, hM0, hJ⟩ := joint_taylor hGs (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R)
    (isCompact_Icc.prod (isCompact_closedBall _ _))
  have hderiv : ∀ q : ℝ × Space,
      fderiv ℝ (fun p : ℝ × (ℝ × Space) => ψ (p.2.1 + p.1, p.2.2)) (0, q) (1, 0) = dτ ψ q := by
    intro q
    have h1 := hasDerivAt_slice hGd 0 q
    have h2 := hasDerivAt_tauLine hψd q.1 q.2 0
    rw [add_zero] at h2
    exact h1.unique h2
  refine ⟨M, hM0, R, fun r hr z => ?_⟩
  by_cases hz : z.1 ∈ Metric.closedBall (0 : Space) R
  · have hmem : z ∈ Metric.closedBall (0 : Space) R ×ˢ (univ : Set (AddCircle P)) :=
      ⟨hz, mem_univ _⟩
    rw [Set.indicator_apply, if_pos hmem]
    have hq : ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1) ∈
        Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R :=
      ⟨toCell_snd_mem z, hz⟩
    have key := hJ r hr _ hq
    rw [hderiv] at key
    simp only [add_zero] at key
    exact key
  · have hnot : z ∉ Metric.closedBall (0 : Space) R ×ˢ (univ : Set (AddCircle P)) :=
      fun h => hz h.1
    rw [Set.indicator_apply, if_neg hnot]
    have hx : R < ‖(UnforcedLeray.B0223.toCell P z).1‖ := by
      have : ¬ ‖z.1‖ ≤ R := by
        intro h
        exact hz (by rw [Metric.mem_closedBall, dist_zero_right]; exact h)
      exact not_le.1 this
    have hfun : (fun t : ℝ => ψ ((UnforcedLeray.B0223.toCell P z).2 + t,
        (UnforcedLeray.B0223.toCell P z).1)) = fun _ => 0 :=
      funext fun t => hR _ _ hx
    have hd : dτ ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1) = 0 := by
      have h2 := hasDerivAt_tauLine hψd (UnforcedLeray.B0223.toCell P z).2
        (UnforcedLeray.B0223.toCell P z).1 0
      rw [hfun, add_zero] at h2
      exact ((hasDerivAt_const (0 : ℝ) (0 : CVec3)).unique h2).symm
    rw [hR _ _ hx, hR _ _ hx, hd]
    simp

/-- The `L²` Taylor bound for the phase translation: `‖transC(-r)Ψ - Ψ - rΨτ‖ ≤ C r²`. -/
theorem transC_taylor_L2 (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest P ψ) (Ψ Ψτ : XC P)
    (hΨ : (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
    (hΨτ : (Ψτ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => dτ ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |r| ≤ 1 →
      ‖UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r) Ψ - Ψ - r • Ψτ‖
        ≤ C * r ^ 2 := by
  obtain ⟨M, hM0, R, hpt⟩ := transC_pointwise ψ hψ
  have hS : MeasurableSet (Metric.closedBall (0 : Space) R ×ˢ (univ : Set (AddCircle P))) :=
    measurableSet_closedBall.prod MeasurableSet.univ
  have hfin : (volume : Measure (UnforcedLeray.B0223.PSpace P))
      (Metric.closedBall (0 : Space) R ×ˢ (univ : Set (AddCircle P))) < ⊤ := by
    rw [UnforcedLeray.B0223.volume_pspace, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_closedBall_lt_top (measure_lt_top _ _)
  obtain ⟨A, hA0, hA⟩ := l2_indicator_bound (E := UnforcedLeray.B0223.SpaceC) (μ := volume)
    _ hS hfin
  refine ⟨A * M, mul_nonneg hA0 hM0, fun r hr => ?_⟩
  have hD := hA (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r) Ψ - Ψ
    - r • Ψτ) (M * r ^ 2) (mul_nonneg hM0 (sq_nonneg r)) ?_
  · calc _ ≤ A * (M * r ^ 2) := hD
      _ = A * M * r ^ 2 := by ring
  · have hrep := transC_ae_repr ψ hψ.periodic Ψ hΨ r
    filter_upwards [Lp.coeFn_sub (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC)
        (-r) Ψ - Ψ) (r • Ψτ),
      Lp.coeFn_sub (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r) Ψ) Ψ,
      Lp.coeFn_smul r Ψτ, hrep, hΨ, hΨτ] with z e1 e2 e3 e4 e5 e6
    rw [e1, Pi.sub_apply, e2, e3]
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [e4, e5, e6]
    exact hpt r hr z

end Transp

/-- **Right-hand strong derivative of the phase translation** (`OD_TransDeriv`). -/
theorem odTransDeriv : OD_TransDeriv := by
  intro p ψ hψ Ψ Ψτ hΨ hΨτ
  obtain ⟨C, hC0, hC⟩ := transC_taylor_L2 ψ hψ Ψ Ψτ hΨ hΨτ
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero, neg_zero, UnforcedLeray.B0223.transC_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun x : ℝ => x ^ 2) ?_ ?_
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with r hr
    have hr' : |r| ≤ 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hr
      exact hr.le
    have hn : ‖r ^ 2‖ = r ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    rw [hn]
    exact hC r hr'
  · exact Asymptotics.isLittleO_pow_id (by norm_num)

end UnforcedLeray.Short.PartIIIb.NearInst
