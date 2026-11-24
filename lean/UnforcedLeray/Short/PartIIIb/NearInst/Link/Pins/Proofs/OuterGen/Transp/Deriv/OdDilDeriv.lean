import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdTransDeriv.Taylor
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdTransDeriv

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.PartIIIb.NearInst.OdHelp

section Dil

variable {P : ℝ} [Fact (0 < P)]

/-- The joint dilation family `(s, (τ, x)) ↦ e^{-3s/4} ψ(τ, e^{-s/2} x)`; its `s`-slice at `s`
is `dilN (e^{-s/2}) ψ` up to the phase representation (`dil_ae_repr`). -/
def dilG (ψ : ℝ × Space → CVec3) : ℝ × (ℝ × Space) → CVec3 :=
  fun p => Real.exp (-(3 * p.1) / 4) • ψ (p.2.1, Real.exp (-p.1 / 2) • p.2.2)

theorem cplx_smul_real (c : ℝ) (v : UnforcedLeray.B0223.SpaceC) :
    ((c : ℝ) : ℂ) • v = c • v :=
  (RCLike.real_smul_eq_coe_smul (K := ℂ) c v).symm

theorem neg_cplx_smul_real (c : ℝ) (v : UnforcedLeray.B0223.SpaceC) :
    (-((c : ℝ) : ℂ)) • v = (-c) • v := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (-c) v]
  congr 1
  simp

theorem dilG_zero (ψ : ℝ × Space → CVec3) (q : ℝ × Space) : dilG ψ (0, q) = ψ q := by
  simp [dilG]

theorem dilG_contDiff {ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ 2 (dilG ψ) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Space) => Real.exp (-(3 * p.1) / 4)) :=
    Real.contDiff_exp.comp (((contDiff_const.mul contDiff_fst).neg).div_const 4)
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Space) => Real.exp (-p.1 / 2) • p.2.2) :=
    (Real.contDiff_exp.comp ((contDiff_fst.neg).div_const 2)).smul contDiff_snd.snd
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Space) =>
      ψ (p.2.1, Real.exp (-p.1 / 2) • p.2.2)) :=
    hψ.comp (contDiff_snd.fst.prodMk h2)
  exact ((h1.smul h3)).of_le (by simp)

theorem dilG_differentiable {ψ : ℝ × Space → CVec3} (hψ : IsPhaseTest P ψ) :
    Differentiable ℝ (dilG ψ) :=
  (dilG_contDiff hψ.smooth).differentiable (by norm_num)

theorem radialT_eq_fderiv (ψ : ℝ × Space → CVec3) (τ : ℝ) (x : Space) :
    fderiv ℝ ψ (τ, x) (0, x) = radialT ψ (τ, x) := by
  have hx : x = ∑ j : Fin 3, x j • coordinateVector j := by
    ext i
    simp [WithLp.ofLp_sum, coordinateVector, EuclideanSpace.single_apply, Finset.sum_apply,
      Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have h : ((0 : ℝ), x) = ∑ j : Fin 3, x j • ((0 : ℝ), coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      exact hx
  rw [h, map_sum]
  simp only [map_smul, radialT, dy]

/-- The `s`-derivative of the joint dilation family at `0`. -/
theorem dilG_deriv (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest P ψ) (q : ℝ × Space) :
    fderiv ℝ (dilG ψ) (0, q) (1, 0) = (-(3 / 4 : ℝ)) • ψ q - (1 / 2 : ℝ) • radialT ψ q := by
  obtain ⟨τ, x⟩ := q
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have h1 := hasDerivAt_slice (dilG_differentiable hψ) 0 (τ, x)
  have hc : HasDerivAt (fun t : ℝ => Real.exp (-(3 * t) / 4)) (-(3 / 4 : ℝ)) 0 := by
    have hfun : (fun t : ℝ => Real.exp (-(3 * t) / 4)) =
        fun t : ℝ => Real.exp ((-(3 / 4) : ℝ) * t) := by
      funext t
      congr 1
      ring
    rw [hfun]
    have := ((hasDerivAt_id' (0 : ℝ)).const_mul (-(3 / 4) : ℝ)).exp
    convert this using 1
    simp
  have hc2 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (-(1 / 2 : ℝ)) 0 := by
    have hfun : (fun t : ℝ => Real.exp (-t / 2)) =
        fun t : ℝ => Real.exp ((-(1 / 2) : ℝ) * t) := by
      funext t
      congr 1
      ring
    rw [hfun]
    have := ((hasDerivAt_id' (0 : ℝ)).const_mul (-(1 / 2) : ℝ)).exp
    convert this using 1
    simp
  have hl : HasDerivAt (fun t : ℝ => ((τ, Real.exp (-t / 2) • x) : ℝ × Space))
      ((0 : ℝ), (-(1 / 2 : ℝ)) • x) 0 :=
    (hasDerivAt_const (0 : ℝ) τ).prodMk (hc2.smul_const x)
  have hf : HasDerivAt (fun t : ℝ => ψ (τ, Real.exp (-t / 2) • x))
      (fderiv ℝ ψ (τ, Real.exp (-0 / 2) • x) ((0 : ℝ), (-(1 / 2 : ℝ)) • x)) 0 :=
    (hψd (τ, Real.exp (-0 / 2) • x)).hasFDerivAt.comp_hasDerivAt 0 hl
  have hprod := hc.smul hf
  have h2 := h1.unique hprod
  have e0 : Real.exp (-0 / 2) = 1 := by simp
  have e1 : Real.exp (-(3 * 0) / 4) = 1 := by simp
  have e2 : ((0 : ℝ), (-(1 / 2 : ℝ)) • x) = (-(1 / 2 : ℝ)) • ((0 : ℝ), x) := by
    ext <;> simp
  rw [h2, e0, e1]
  simp only [one_smul]
  rw [e2, map_smul, radialT_eq_fderiv]
  simp only [one_smul, neg_smul, sub_eq_add_neg]
  abel

/-- Vanishing outside the support: for `|s| ≤ 1` and `‖x‖ > R e^{1/2}` the joint family is zero. -/
theorem dilG_zero_outside (ψ : ℝ × Space → CVec3) {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → ψ (τ, y) = 0) (τ : ℝ) (x : Space)
    (hx : R * Real.exp (1 / 2) < ‖x‖) (s : ℝ) (hs : |s| ≤ 1) :
    dilG ψ (s, (τ, x)) = 0 := by
  have hu : Real.exp (-(1 / 2)) ≤ Real.exp (-s / 2) :=
    Real.exp_le_exp.2 (by linarith [(abs_le.1 hs).2])
  have he : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hpos : 0 < Real.exp (-(1 / 2)) := Real.exp_pos _
  have hy : R < ‖Real.exp (-s / 2) • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : Real.exp (-(1 / 2)) * (R * Real.exp (1 / 2)) < Real.exp (-(1 / 2)) * ‖x‖ :=
      mul_lt_mul_of_pos_left hx hpos
    have h2 : Real.exp (-(1 / 2)) * (R * Real.exp (1 / 2)) = R := by
      linear_combination R * he
    calc R = Real.exp (-(1 / 2)) * (R * Real.exp (1 / 2)) := h2.symm
      _ < Real.exp (-(1 / 2)) * ‖x‖ := h1
      _ ≤ Real.exp (-s / 2) * ‖x‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
  show Real.exp (-(3 * s) / 4) • ψ (τ, Real.exp (-s / 2) • x) = 0
  rw [hR τ _ hy, smul_zero]

/-- Pointwise Taylor bound for the dilation on a smooth phase test, with the `L²`-support
set `closedBall 0 (R e^{1/2}) × univ`. -/
theorem dil_pointwise (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest P ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ R' : ℝ, ∀ r : ℝ, |r| ≤ 1 → ∀ z : UnforcedLeray.B0223.PSpace P,
      ‖dilG ψ (r, ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
        - ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)
        - r • ((-(3 / 4 : ℝ)) • ψ ((UnforcedLeray.B0223.toCell P z).2,
              (UnforcedLeray.B0223.toCell P z).1)
            - (1 / 2 : ℝ) • radialT ψ ((UnforcedLeray.B0223.toCell P z).2,
              (UnforcedLeray.B0223.toCell P z).1))‖
        ≤ (Metric.closedBall (0 : Space) (R' ) ×ˢ (univ : Set (AddCircle P))).indicator
            (fun _ => M * r ^ 2) z := by
  classical
  obtain ⟨R, hR⟩ := hψ.bounded_support
  obtain ⟨M, hM0, hJ⟩ := joint_taylor (dilG_contDiff hψ.smooth)
    (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) (R * Real.exp (1 / 2)))
    (isCompact_Icc.prod (isCompact_closedBall _ _))
  refine ⟨M, hM0, R * Real.exp (1 / 2), fun r hr z => ?_⟩
  by_cases hz : z.1 ∈ Metric.closedBall (0 : Space) (R * Real.exp (1 / 2))
  · have hmem : z ∈ Metric.closedBall (0 : Space) (R * Real.exp (1 / 2)) ×ˢ
        (univ : Set (AddCircle P)) := ⟨hz, mem_univ _⟩
    rw [Set.indicator_apply, if_pos hmem]
    have hq : ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1) ∈
        Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) (R * Real.exp (1 / 2)) :=
      ⟨toCell_snd_mem z, hz⟩
    have key := hJ r hr _ hq
    rw [dilG_deriv ψ hψ, dilG_zero] at key
    exact key
  · have hnot : z ∉ Metric.closedBall (0 : Space) (R * Real.exp (1 / 2)) ×ˢ
        (univ : Set (AddCircle P)) := fun h => hz h.1
    rw [Set.indicator_apply, if_neg hnot]
    have hx : R * Real.exp (1 / 2) < ‖(UnforcedLeray.B0223.toCell P z).1‖ := by
      have h' : ¬ ‖z.1‖ ≤ R * Real.exp (1 / 2) := fun h =>
        hz (by rw [Metric.mem_closedBall, dist_zero_right]; exact h)
      exact not_le.1 h'
    have hz0 : ∀ s : ℝ, |s| ≤ 1 →
        dilG ψ (s, ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)) = 0 :=
      fun s hs => dilG_zero_outside ψ hR _ _ hx s hs
    have hψq : ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1) = 0 := by
      have := hz0 0 (by simp)
      rwa [dilG_zero] at this
    have hrad : radialT ψ ((UnforcedLeray.B0223.toCell P z).2,
        (UnforcedLeray.B0223.toCell P z).1) = 0 := by
      have hd : fderiv ℝ (dilG ψ) (0, ((UnforcedLeray.B0223.toCell P z).2,
          (UnforcedLeray.B0223.toCell P z).1)) (1, 0) = 0 :=
        fderiv_eq_zero_of_zero (dilG_differentiable hψ) _ (fun s hs => hz0 s (abs_le.2 hs))
      rw [dilG_deriv ψ hψ, hψq] at hd
      rw [smul_zero, zero_sub, neg_eq_zero] at hd
      exact (smul_eq_zero.1 hd).resolve_left (by norm_num)
    rw [hz0 r hr, hψq, hrad]
    simp

/-- The phase representation of `dilN (e^{-r/2}) Ψ`. -/
theorem dil_ae_repr (ψ : ℝ × Space → CVec3) (Ψ : XC P)
    (hΨ : (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
    (r : ℝ) :
    ∀ᵐ z ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      ((UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ :
        UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) z) =
        dilG ψ (r, ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)) := by
  have h := UnforcedLeray.B0223.dilN_ae (a := Real.exp (-r / 2)) (Real.exp_pos _) hΨ
  filter_upwards [h] with z hz
  rw [hz]
  have hpow : Real.exp (-r / 2) ^ (3 / 2 : ℝ) = Real.exp (-(3 * r) / 4) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hpow]
  rfl

/-- **`L²` Taylor bound for the dilation**: `‖dilN(e^{-r/2})Ψ - Ψ - r(-(3/4)Ψ - (1/2)Ψx)‖ ≤ C r²`. -/
theorem dil_taylor_L2 (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest P ψ) (Ψ Ψx : XC P)
    (hΨ : (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
    (hΨx : (Ψx : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => radialT ψ ((UnforcedLeray.B0223.toCell P z).2,
        (UnforcedLeray.B0223.toCell P z).1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |r| ≤ 1 →
      ‖UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ - Ψ
        - r • (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx)‖ ≤ C * r ^ 2 := by
  classical
  obtain ⟨M, hM0, R', hpt⟩ := dil_pointwise ψ hψ
  have hS : MeasurableSet (Metric.closedBall (0 : Space) R' ×ˢ (univ : Set (AddCircle P))) :=
    measurableSet_closedBall.prod MeasurableSet.univ
  have hfin : (volume : Measure (UnforcedLeray.B0223.PSpace P))
      (Metric.closedBall (0 : Space) R' ×ˢ (univ : Set (AddCircle P))) < ⊤ := by
    rw [UnforcedLeray.B0223.volume_pspace, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_closedBall_lt_top (measure_lt_top _ _)
  obtain ⟨A, hA0, hA⟩ := l2_indicator_bound (E := UnforcedLeray.B0223.SpaceC) (μ := volume)
    _ hS hfin
  refine ⟨A * M, mul_nonneg hA0 hM0, fun r hr => ?_⟩
  have hD := hA (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
      (Real.exp (-r / 2)) Ψ - Ψ
      - r • (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx)) (M * r ^ 2)
    (mul_nonneg hM0 (sq_nonneg r)) ?_
  · calc _ ≤ A * (M * r ^ 2) := hD
      _ = A * M * r ^ 2 := by ring
  · have hrep := dil_ae_repr ψ Ψ hΨ r
    filter_upwards [
      Lp.coeFn_sub (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
        (Real.exp (-r / 2)) Ψ - Ψ) (r • (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx)),
      Lp.coeFn_sub (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
        (Real.exp (-r / 2)) Ψ) Ψ,
      Lp.coeFn_smul r (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx),
      Lp.coeFn_sub (-(((3 / 4 : ℝ)) : ℂ) • Ψ) (((1 / 2 : ℝ) : ℂ) • Ψx),
      Lp.coeFn_smul (-(((3 / 4 : ℝ)) : ℂ)) Ψ,
      Lp.coeFn_smul (((1 / 2 : ℝ) : ℂ)) Ψx,
      hrep, hΨ, hΨx] with z e1 e2 e3 e4 e5 e6 e7 e8 e9
    simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, Pi.sub_apply, Pi.smul_apply]
    simp only [neg_cplx_smul_real, cplx_smul_real]
    exact hpt r hr z

end Dil

/-- **Right-hand strong derivative of the normalized dilation** (`OD_DilDeriv`). -/
theorem odDilDeriv : OD_DilDeriv := by
  intro p ψ hψ Ψ Ψx hΨ hΨx
  obtain ⟨C, hC0, hC⟩ := dil_taylor_L2 ψ hψ Ψ Ψx hΨ hΨx
  have hf0 : UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
      (Real.exp (-0 / 2)) Ψ = Ψ := by
    rw [show (-0 : ℝ) / 2 = 0 by ring, Real.exp_zero, UnforcedLeray.B0223.dilN_one]
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero, hf0]
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
