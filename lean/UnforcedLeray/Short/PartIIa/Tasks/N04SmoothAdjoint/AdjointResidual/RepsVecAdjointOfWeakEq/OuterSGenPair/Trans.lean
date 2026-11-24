import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.OuterSGenPair.Defs

/-!
# Strong derivative of the phase translation on `C²` phase tests

Copy of the PartIII-b proof (`OdTransDeriv`) for `C²` phase tests `IsPhaseTest2` (only `C²` is used).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.OuterSGen

open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.OdHelp
open UnforcedLeray.PhaseSpace

section S

variable {P : ℝ} [Fact (0 < P)]

/-- Pointwise Taylor bound for the phase translation on a smooth phase test, with the
`L²`-support set `closedBall 0 R × univ`. -/
theorem transC_pointwise2 (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest2 P ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ R : ℝ, ∀ r : ℝ, |r| ≤ 1 → ∀ z : UnforcedLeray.B0223.PSpace P,
      ‖ψ ((UnforcedLeray.B0223.toCell P z).2 + r, (UnforcedLeray.B0223.toCell P z).1)
        - ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)
        - r • dτ ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)‖
        ≤ (Metric.closedBall (0 : Space) R ×ˢ (univ : Set (AddCircle P))).indicator
            (fun _ => M * r ^ 2) z := by
  classical
  obtain ⟨R, hR⟩ := hψ.bounded_support
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by norm_num)
  have hF : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Space) => ((p.2.1 + p.1 : ℝ), p.2.2)) :=
    ((contDiff_snd.fst).add contDiff_fst).prodMk contDiff_snd.snd
  have hGs : ContDiff ℝ 2 (fun p : ℝ × (ℝ × Space) => ψ (p.2.1 + p.1, p.2.2)) :=
    hψ.smooth.comp (hF.of_le (by simp))
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
theorem transC_taylor_L2' (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest2 P ψ) (Ψ Ψτ : XC P)
    (hΨ : (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
    (hΨτ : (Ψτ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => dτ ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |r| ≤ 1 →
      ‖UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r) Ψ - Ψ - r • Ψτ‖
        ≤ C * r ^ 2 := by
  obtain ⟨M, hM0, R, hpt⟩ := transC_pointwise2 ψ hψ
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

/-- Strong derivative of the phase translation at `0` on a `C²` phase test. -/
theorem transDeriv2 (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest2 P ψ) (Ψ Ψτ : XC P)
    (hΨ : (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
    (hΨτ : (Ψτ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => dτ ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)) :
    HasDerivAt (fun r : ℝ =>
      UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r) Ψ) Ψτ 0 := by
  obtain ⟨C, hC0, hC⟩ := transC_taylor_L2' ψ hψ Ψ Ψτ hΨ hΨτ
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

end S

end UnforcedLeray.Short.PartIIa.OuterSGen
