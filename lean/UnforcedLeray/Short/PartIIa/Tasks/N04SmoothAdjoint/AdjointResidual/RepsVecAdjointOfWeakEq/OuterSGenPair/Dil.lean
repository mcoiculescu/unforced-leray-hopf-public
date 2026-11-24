import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.OuterSGenPair.Defs

/-!
# Strong derivative of the normalized dilation on `C²` phase tests

Copy of the PartIII-b proof (`OdDilDeriv`) for `C²` phase tests `IsPhaseTest2` (only `C²` is used).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.OuterSGen

open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.OdHelp
open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

section S

variable {P : ℝ} [Fact (0 < P)]

/-- The joint dilation family of a `C²` function is `C²`. -/
theorem dilG_contDiff2 {ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ 2 ψ) :
    ContDiff ℝ 2 (dilG ψ) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Space) => Real.exp (-(3 * p.1) / 4)) :=
    Real.contDiff_exp.comp (((contDiff_const.mul contDiff_fst).neg).div_const 4)
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Space) => Real.exp (-p.1 / 2) • p.2.2) :=
    (Real.contDiff_exp.comp ((contDiff_fst.neg).div_const 2)).smul contDiff_snd.snd
  have h3 : ContDiff ℝ 2 (fun p : ℝ × (ℝ × Space) =>
      ψ (p.2.1, Real.exp (-p.1 / 2) • p.2.2)) :=
    hψ.comp ((contDiff_snd.fst.prodMk h2).of_le (by simp))
  exact (h1.of_le (by simp)).smul h3

theorem dilG_differentiable2 {ψ : ℝ × Space → CVec3} (hψ : IsPhaseTest2 P ψ) :
    Differentiable ℝ (dilG ψ) :=
  (dilG_contDiff2 hψ.smooth).differentiable (by norm_num)

theorem dilG_deriv2 (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest2 P ψ) (q : ℝ × Space) :
    fderiv ℝ (dilG ψ) (0, q) (1, 0) = (-(3 / 4 : ℝ)) • ψ q - (1 / 2 : ℝ) • radialT ψ q := by
  obtain ⟨τ, x⟩ := q
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by norm_num)
  have h1 := hasDerivAt_slice (dilG_differentiable2 hψ) 0 (τ, x)
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

/-- Pointwise Taylor bound for the dilation on a smooth phase test, with the `L²`-support
set `closedBall 0 (R e^{1/2}) × univ`. -/
theorem dil_pointwise2 (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest2 P ψ) :
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
  obtain ⟨M, hM0, hJ⟩ := joint_taylor (dilG_contDiff2 hψ.smooth)
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
    rw [dilG_deriv2 ψ hψ, dilG_zero] at key
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
        fderiv_eq_zero_of_zero (dilG_differentiable2 hψ) _ (fun s hs => hz0 s (abs_le.2 hs))
      rw [dilG_deriv2 ψ hψ, hψq] at hd
      rw [smul_zero, zero_sub, neg_eq_zero] at hd
      exact (smul_eq_zero.1 hd).resolve_left (by norm_num)
    rw [hz0 r hr, hψq, hrad]
    simp

/-- The phase representation of `dilN (e^{-r/2}) Ψ`. -/

theorem dil_taylor_L2' (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest2 P ψ) (Ψ Ψx : XC P)
    (hΨ : (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
    (hΨx : (Ψx : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => radialT ψ ((UnforcedLeray.B0223.toCell P z).2,
        (UnforcedLeray.B0223.toCell P z).1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |r| ≤ 1 →
      ‖UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ - Ψ
        - r • (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx)‖ ≤ C * r ^ 2 := by
  classical
  obtain ⟨M, hM0, R', hpt⟩ := dil_pointwise2 ψ hψ
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


/-- Strong derivative of `r ↦ dilN(e^{-r/2})Ψ` at `0` on a `C²` phase test. -/
theorem dilDeriv2 (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest2 P ψ) (Ψ Ψx : XC P)
    (hΨ : (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ψ ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1))
    (hΨx : (Ψx : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => radialT ψ ((UnforcedLeray.B0223.toCell P z).2,
        (UnforcedLeray.B0223.toCell P z).1)) :
    HasDerivAt (fun r : ℝ =>
        UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ)
      (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx) 0 := by
  obtain ⟨C, hC0, hC⟩ := dil_taylor_L2' ψ hψ Ψ Ψx hΨ hΨx
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

end S

end UnforcedLeray.Short.PartIIa.OuterSGen
