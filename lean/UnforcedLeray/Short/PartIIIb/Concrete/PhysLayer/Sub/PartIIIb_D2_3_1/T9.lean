import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T10
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.D

/-!
# `WardXRegular` from the four Ward facts (`PartIII-b:IIIb-D2/3/1/9`)

The field is `X = wardXr` (`Sub/IIIb-D2_3_2/Dense/Reg.lean`): `wardX` off the axis and `0` on it.
Its regularity, divergence, periodicity and symmetry follow from `h1`-`h4` as follows.
* `C²`: `wardXr τ` is `0` on `{ϱ < R√ν}` and equals `wardStreamCut (wardX0 τ)` on `youngOpen`;
  the `C²` of the outward primitive `(r,z) ↦ outPrim` on the young region is the bootstrap
  `t9_outPrim_c2` (from the partial derivatives, via `t9_hasFDerivAt_of_partials`).
* divergence: `WardStreamCutDivFree` (`h4`) on `youngOpen`, `0` on `{ϱ < R√ν}`.
* periodicity: `wardXr_periodic_of`.  Symmetry: `wardXrAxiOfX0_proved` and `axiNoSwirl_of_pt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Bootstrap estimate**: the outward primitive of a `C²` field on the young
region is `C²` as a function of `y` there, given the two partial derivatives of `OutPrimStream`
(source 4178-4179: `∂_rΨ = r Z_z`, `∂_zΨ = -r Z_r`, whose right-hand sides are `C¹` in `(r,z)`). -/
def OutPrimC2Boot : Prop :=
  ∀ (ν R : ℝ) (Z : ℝ → Space → Space) (τ : ℝ), 0 < ν → 0 < R →
    ContDiffOn ℝ 2 (Z τ) (youngOpen ν R) →
    (∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim Z τ r' z) (r * Z τ !₂[r, 0, z] 2) r ∧
        HasDerivAt (fun z' => outPrim Z τ r z') (-(r * Z τ !₂[r, 0, z] 0)) z) →
    ContDiffOn ℝ 2 (fun y : Space => outPrim Z τ (ϱ y) (y 2)) (youngOpen ν R)

theorem t9_thr_pos {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    0 < R * Real.sqrt (5 * ν / 6) :=
  mul_pos hR (Real.sqrt_pos.2 (by positivity))

theorem t9_not_axis {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {y : Space}
    (hy : y ∈ youngOpen ν R) : y ∉ axis := by
  intro h
  have h0 : ϱ y = 0 := (mem_axis_iff y).1 h
  have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
  have hp := t9_thr_pos hν hR
  linarith

theorem t9_wsc_contDiffOn {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) (hν : 0 < ν)
    (hR : 0 < R) {Z : ℝ → Space → Space} {τ : ℝ}
    (hZ : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R))
    (hO : ContDiffOn ℝ 2 (fun y : Space => outPrim Z τ (ϱ y) (y 2)) (youngOpen ν R)) :
    ContDiffOn ℝ 2 (wardStreamCut ν R χy Z τ) (youngOpen ν R) := by
  have hne : ∀ y ∈ youngOpen ν R, ϱ y ≠ 0 := fun y hy => by
    have hp := t9_thr_pos hν hR
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
    intro h0
    linarith
  have hϱ : ContDiffOn ℝ 2 (fun y : Space => ϱ y) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun y hy => t9_not_axis hν hR hy)
  have hage : ContDiffOn ℝ 2 (fun y : Space => age R y) (youngOpen ν R) :=
    ContDiffOn.div contDiffOn_const (hϱ.pow 2) (fun y hy => pow_ne_zero 2 (hne y hy))
  have hνage : ContDiffOn ℝ 2 (fun y : Space => ν * age R y) (youngOpen ν R) :=
    contDiffOn_const.mul hage
  have hχ2 : ContDiff ℝ 2 χy :=
    hχy.smooth.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hdχ2 : ContDiff ℝ 2 (deriv χy) :=
    ((show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχy.smooth).deriv').of_le
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hχA : ContDiffOn ℝ 2 (fun y : Space => χy (ν * age R y)) (youngOpen ν R) :=
    hχ2.comp_contDiffOn hνage
  have hdA : ContDiffOn ℝ 2 (fun y : Space => deriv χy (ν * age R y)) (youngOpen ν R) :=
    hdχ2.comp_contDiffOn hνage
  have hK : ContDiffOn ℝ 2 (fun y : Space => -2 * ν * R ^ 2 / ϱ y ^ 3) (youngOpen ν R) :=
    ContDiffOn.div contDiffOn_const (hϱ.pow 3) (fun y hy => pow_ne_zero 3 (hne y hy))
  have hterm1 := hχA.smul hZ
  have hterm2 := (((hdA.mul hK).div hϱ hne).mul hO).smul
    (contDiffOn_const (c := (coordinateVector 2 : Space)))
  exact hterm1.add hterm2

theorem t9_wardXr_contDiff {ν μ R c : ℝ} {χy : ℝ → ℝ} (g : Chart → Ten3)
    (hχy : IsYoungCutoff χy) (hν : 0 < ν) (hR : 0 < R) (τ : ℝ)
    (hZ : ContDiffOn ℝ 2 (wardX0 ν μ R c g τ) (youngOpen ν R))
    (hO : ContDiffOn ℝ 2 (fun y : Space => outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2))
      (youngOpen ν R)) :
    ContDiff ℝ 2 (wardXr ν μ R c χy g τ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : R * Real.sqrt (5 * ν / 6) < ϱ y
  · have hWc : ContDiffOn ℝ 2 (wardXr ν μ R c χy g τ) (youngOpen ν R) := by
      refine (t9_wsc_contDiffOn hχy hν hR hZ hO).congr ?_
      intro x hx
      rw [wardXr_of_not_mem ν μ R c χy g τ (t9_not_axis hν hR hx)]
      rfl
    have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
    exact hWc.contDiffAt (hopen.mem_nhds hy)
  · have hlt : ϱ y < R * Real.sqrt ν := by
      have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
        Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have h2' : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := mul_lt_mul_of_pos_left h1 hR
      have h3 : ϱ y ≤ R * Real.sqrt (5 * ν / 6) := not_lt.1 hy
      linarith
    have hO' : IsOpen {z : Space | ϱ z < R * Real.sqrt ν} :=
      isOpen_lt continuous_ϱ continuous_const
    have hev : wardXr ν μ R c χy g τ =ᶠ[𝓝 y] (fun _ : Space => (0 : Space)) := by
      filter_upwards [hO'.mem_nhds (show y ∈ {z : Space | ϱ z < R * Real.sqrt ν} from hlt)]
        with z hz
      have hz' : ϱ z < R * Real.sqrt ν := hz
      have h0 : 0 ≤ ϱ z := ϱ_nonneg z
      have hs2 : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
      have hm := mul_le_mul hz'.le hz'.le h0 (mul_nonneg hR.le (Real.sqrt_nonneg ν))
      have he : (R * Real.sqrt ν) * (R * Real.sqrt ν) = ν * R ^ 2 := by
        rw [show (R * Real.sqrt ν) * (R * Real.sqrt ν) = R ^ 2 * Real.sqrt ν ^ 2 by ring, hs2]
        ring
      have hsq : ϱ z ^ 2 ≤ ν * R ^ 2 := by nlinarith [hm, he]
      exact wardXr_eq_zero_of_sq_le (ν := ν) (μ := μ) (R := R) (c := c) hχy g τ hsq
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- Fréchet derivative of a function with continuous partial derivatives on an open set. -/
theorem t9_hasFDerivAt_of_partials (S : Set (ℝ × ℝ)) (hS : IsOpen S) (F P Q : ℝ × ℝ → ℝ)
    (hP : ContinuousOn P S) (hQ : ContinuousOn Q S)
    (h1 : ∀ p ∈ S, HasDerivAt (fun r => F (r, p.2)) (P p) p.1)
    (h2 : ∀ p ∈ S, HasDerivAt (fun z => F (p.1, z)) (Q p) p.2)
    (p : ℝ × ℝ) (hp : p ∈ S) :
    HasFDerivAt F (P p • ContinuousLinearMap.fst ℝ ℝ ℝ + Q p • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ1, hδ1, hPδ⟩ := Metric.continuousAt_iff.1
    (hP.continuousAt (hS.mem_nhds hp)) (c / 2) (half_pos hc)
  obtain ⟨δ2, hδ2, hQδ⟩ := Metric.continuousAt_iff.1
    (hQ.continuousAt (hS.mem_nhds hp)) (c / 2) (half_pos hc)
  obtain ⟨δ3, hδ3, hball⟩ := Metric.isOpen_iff.1 hS p hp
  have hδpos0 : 0 < min δ1 (min δ2 δ3) := lt_min hδ1 (lt_min hδ2 hδ3)
  set δ := min δ1 (min δ2 δ3) with hδdef
  have hδ1' : δ ≤ δ1 := min_le_left _ _
  have hδ2' : δ ≤ δ2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3' : δ ≤ δ3 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hδpos : 0 < δ := hδpos0
  have hdist : ∀ x t : ℝ, dist x p.1 < δ → dist t p.2 < δ → dist (x, t) p < δ := by
    intro x t hx ht
    rw [Prod.dist_eq]
    exact max_lt hx ht
  have hF : F (p.1, p.2) = F p := rfl
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) hδpos] with h hh
  have hh' : ‖h‖ < δ := by simpa using hh
  have hhd1 : dist (p.1 + h.1) p.1 < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, ← Real.norm_eq_abs]
    exact lt_of_le_of_lt (norm_fst_le h) hh'
  have hhd2 : dist (p.2 + h.2) p.2 < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, ← Real.norm_eq_abs]
    exact lt_of_le_of_lt (norm_snd_le h) hh'
  have hstep1 : ∀ x ∈ Metric.ball p.1 δ,
      HasDerivWithinAt (fun y => F (y, p.2 + h.2) - P p * y)
        (P (x, p.2 + h.2) - P p) (Metric.ball p.1 δ) x := by
    intro x hx
    have hxd : dist x p.1 < δ := Metric.mem_ball.1 hx
    have hxS : (x, p.2 + h.2) ∈ S :=
      hball (Metric.mem_ball.2 (lt_of_lt_of_le (hdist x _ hxd hhd2) hδ3'))
    have H : HasDerivAt (fun y => F (y, p.2 + h.2)) (P (x, p.2 + h.2)) x := h1 (x, p.2 + h.2) hxS
    exact (H.sub ((hasDerivAt_id' x).const_mul (P p))).hasDerivWithinAt.congr_deriv (by ring)
  have hb1 : ∀ x ∈ Metric.ball p.1 δ, ‖P (x, p.2 + h.2) - P p‖ ≤ c / 2 := by
    intro x hx
    have hxd : dist x p.1 < δ := Metric.mem_ball.1 hx
    rw [← dist_eq_norm]
    exact (hPδ (lt_of_lt_of_le (hdist x _ hxd hhd2) hδ1')).le
  have e1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hstep1 hb1 (convex_ball _ _)
    (Metric.mem_ball_self hδpos) (Metric.mem_ball.2 hhd1)
  have hstep2 : ∀ t ∈ Metric.ball p.2 δ,
      HasDerivWithinAt (fun y => F (p.1, y) - Q p * y)
        (Q (p.1, t) - Q p) (Metric.ball p.2 δ) t := by
    intro t ht
    have htd : dist t p.2 < δ := Metric.mem_ball.1 ht
    have hp1 : dist p.1 p.1 < δ := by simpa using hδpos
    have htS : (p.1, t) ∈ S :=
      hball (Metric.mem_ball.2 (lt_of_lt_of_le (hdist p.1 t hp1 htd) hδ3'))
    have H : HasDerivAt (fun y => F (p.1, y)) (Q (p.1, t)) t := h2 (p.1, t) htS
    exact (H.sub ((hasDerivAt_id' t).const_mul (Q p))).hasDerivWithinAt.congr_deriv (by ring)
  have hb2 : ∀ t ∈ Metric.ball p.2 δ, ‖Q (p.1, t) - Q p‖ ≤ c / 2 := by
    intro t ht
    have htd : dist t p.2 < δ := Metric.mem_ball.1 ht
    have hp1 : dist p.1 p.1 < δ := by simpa using hδpos
    rw [← dist_eq_norm]
    exact (hQδ (lt_of_lt_of_le (hdist p.1 t hp1 htd) hδ2')).le
  have e2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hstep2 hb2 (convex_ball _ _)
    (Metric.mem_ball_self hδpos) (Metric.mem_ball.2 hhd2)
  simp only [add_sub_cancel_left] at e1 e2
  rw [hF] at e2
  have hL : (P p • ContinuousLinearMap.fst ℝ ℝ ℝ + Q p • ContinuousLinearMap.snd ℝ ℝ ℝ) h
      = P p * h.1 + Q p * h.2 := by simp
  show ‖F (p.1 + h.1, p.2 + h.2) - F p -
    (P p • ContinuousLinearMap.fst ℝ ℝ ℝ + Q p • ContinuousLinearMap.snd ℝ ℝ ℝ) h‖ ≤ c * ‖h‖
  rw [hL]
  have key : F (p.1 + h.1, p.2 + h.2) - F p - (P p * h.1 + Q p * h.2) =
      (F (p.1 + h.1, p.2 + h.2) - P p * (p.1 + h.1) - (F (p.1, p.2 + h.2) - P p * p.1))
      + (F (p.1, p.2 + h.2) - Q p * (p.2 + h.2) - (F p - Q p * p.2)) := by ring
  rw [key]
  have f1 := mul_le_mul_of_nonneg_left (norm_fst_le h) hc.le
  have f2 := mul_le_mul_of_nonneg_left (norm_snd_le h) hc.le
  calc _ ≤ ‖F (p.1 + h.1, p.2 + h.2) - P p * (p.1 + h.1) - (F (p.1, p.2 + h.2) - P p * p.1)‖
        + ‖F (p.1, p.2 + h.2) - Q p * (p.2 + h.2) - (F p - Q p * p.2)‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖h.1‖ + c / 2 * ‖h.2‖ := add_le_add e1 e2
    _ ≤ c * ‖h‖ := by linarith

/-- The bootstrap: `outPrim` is `C²` on the young region (proved from `t9_hasFDerivAt_of_partials`). -/
theorem t9_outPrim_c2 {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {Z : ℝ → Space → Space} {τ : ℝ}
    (hZ : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R))
    (hdr : ∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim Z τ r' z) (r * Z τ !₂[r, 0, z] 2) r ∧
        HasDerivAt (fun z' => outPrim Z τ r z') (-(r * Z τ !₂[r, 0, z] 0)) z) :
    ContDiffOn ℝ 2 (fun y : Space => outPrim Z τ (ϱ y) (y 2)) (youngOpen ν R) := by
  have hS : IsOpen {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have hm : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
    have hv : ContDiff ℝ 2 (fun p : ℝ × ℝ => (![p.1, 0, p.2] : Fin 3 → ℝ)) :=
      contDiff_pi.2 (fun i => by fin_cases i <;> simp <;> fun_prop)
    have : ContDiff ℝ 2 (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) :=
      PiLp.contDiff_toLp.comp hv
    exact this.contDiffOn
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} (youngOpen ν R) := by
    intro p hp
    have hp' : R * Real.sqrt (5 * ν / 6) < p.1 := hp
    show R * Real.sqrt (5 * ν / 6) < ϱ (!₂[p.1, 0, p.2] : Space)
    have hϱ : ϱ (!₂[p.1, 0, p.2] : Space) = |p.1| := by simp [ϱ, Real.sqrt_sq_eq_abs]
    rw [hϱ]
    exact lt_of_lt_of_le hp' (le_abs_self _)
  have hPc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    contDiffOn_fst.mul ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (hZ.comp hm hmaps))
  have hQc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    (contDiffOn_fst.mul ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (hZ.comp hm hmaps))).neg
  have hD := fun p (hp : p ∈ {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1}) =>
    t9_hasFDerivAt_of_partials _ hS (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
      (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      hPc.continuousOn hQc.continuousOn
      (fun p hp => (hdr p.1 p.2 hp).1) (fun p hp => (hdr p.1 p.2 hp).2) p hp
  have hPc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := hPc.of_le (by norm_num)
  have hQc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := hQc.of_le (by norm_num)
  have hS1 : ContDiffOn ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
    refine ContDiffOn.congr (f := fun p : ℝ × ℝ =>
      (p.1 * Z τ !₂[p.1, 0, p.2] 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(p.1 * Z τ !₂[p.1, 0, p.2] 0)) • ContinuousLinearMap.snd ℝ ℝ ℝ) ?_ ?_
    · exact (hPc1.smul contDiffOn_const).add (hQc1.smul contDiffOn_const)
    · intro p hp
      exact (hD p hp).fderiv
  have hF : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
    have h' : ContDiffOn ℝ (1 + 1) (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
        {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hS]
      refine ⟨fun p hp => (hD p hp).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), hS1⟩
    exact h'
  have hϱ2 : ContDiffOn ℝ 2 (fun y : Space => ϱ y) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun y hy => t9_not_axis hν hR hy)
  have hz2 : ContDiffOn ℝ 2 (fun y : Space => y 2) (youngOpen ν R) :=
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff).contDiffOn
  have hG : ContDiffOn ℝ 2 (fun y : Space => ((ϱ y, y 2) : ℝ × ℝ)) (youngOpen ν R) :=
    hϱ2.prodMk hz2
  have hmapG : Set.MapsTo (fun y : Space => ((ϱ y, y 2) : ℝ × ℝ)) (youngOpen ν R)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := fun y hy => by
    show R * Real.sqrt (5 * ν / 6) < ϱ y
    exact hy
  exact hF.comp hG hmapG

theorem outPrimC2Boot_proved : OutPrimC2Boot :=
  fun ν R Z τ hν hR hZ hdr => t9_outPrim_c2 hν hR hZ hdr

/-- **Conditional assembly**: `WardXRegular` follows from `h1`-`h4` and the bootstrap
`OutPrimC2Boot`. -/
theorem wardXRegular_of_boot (hBoot : OutPrimC2Boot)
    (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ)
    (h1 : WardX0Smooth c mZ ρb γ ν ε μ hχo) (h2 : WardX0Structure c mZ ρb γ ν ε μ hχo)
    (h3 : OutPrimStream c mZ ρb γ ν ε μ hχo) (h4 : WardStreamCutDivFree ν ε⁻¹ χy) :
    WardXRegular c mZ ρb γ ν ε μ hχo χy := by
  unfold WardXRegular
  intro hχy hc hρb hm hν hε hμ T g₁ g₂ hg1 hg2
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hZs := h1 hc hρb hm hν hε hμ T g₁ g₂ hg1 hg2
  have hW2 := h2 hc hρb hm hν hε hμ T g₁ g₂ hg1 hg2
  have hPr := h3 hc hρb hm hν hε hμ T g₁ g₂ hg1 hg2
  have hOs : ∀ τ, ContDiffOn ℝ 2 (fun y : Space => outPrim (wardX0 ν μ ε⁻¹ c (g₁ + g₂)) τ (ϱ y) (y 2))
      (youngOpen ν ε⁻¹) := fun τ =>
    hBoot ν ε⁻¹ (wardX0 ν μ ε⁻¹ c (g₁ + g₂)) τ hν hR (hZs τ) (fun r z hr => hPr τ r z hr)
  have hopen : IsOpen (youngOpen ν ε⁻¹) := isOpen_lt continuous_const continuous_ϱ
  refine ⟨wardXr ν μ ε⁻¹ c χy (g₁ + g₂), fun τ => t9_wardXr_contDiff (g₁ + g₂) hχy hν hR τ
      (hZs τ) (hOs τ), fun τ y hy => wardXr_of_not_mem ν μ ε⁻¹ c χy (g₁ + g₂) τ hy, ?_,
    fun τ y => wardXr_periodic_of ν μ ε⁻¹ c χy (g₁ + g₂) τ y, ?_⟩
  · intro τ y
    by_cases hy : ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y
    · have hev : wardXr ν μ ε⁻¹ c χy (g₁ + g₂) τ =ᶠ[𝓝 y]
          wardStreamCut ν ε⁻¹ χy (wardX0 ν μ ε⁻¹ c (g₁ + g₂)) τ := by
        filter_upwards [hopen.mem_nhds (show y ∈ youngOpen ν ε⁻¹ from hy)] with z hz
        exact wardXr_of_not_mem ν μ ε⁻¹ c χy (g₁ + g₂) τ (t9_not_axis hν hR hz)
      simp only [physPd_congr_nhds hev]
      exact h4 hχy hν hR (wardX0 ν μ ε⁻¹ c (g₁ + g₂)) τ (hZs τ)
        (hW2.1 τ) hW2.2.2 (fun r z hr => hPr τ r z hr) y (t9_not_axis hν hR hy)
    · have hlt : ϱ y < ε⁻¹ * Real.sqrt ν := by
        have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
          Real.sqrt_lt_sqrt (by linarith) (by linarith)
        have h2' : ε⁻¹ * Real.sqrt (5 * ν / 6) < ε⁻¹ * Real.sqrt ν :=
          mul_lt_mul_of_pos_left h1 hR
        have h3 : ϱ y ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := not_lt.1 hy
        linarith
      have hO' : IsOpen {z : Space | ϱ z < ε⁻¹ * Real.sqrt ν} :=
        isOpen_lt continuous_ϱ continuous_const
      have hev : wardXr ν μ ε⁻¹ c χy (g₁ + g₂) τ =ᶠ[𝓝 y] (0 : Space → Space) := by
        filter_upwards [hO'.mem_nhds (show y ∈ {z : Space | ϱ z < ε⁻¹ * Real.sqrt ν} from hlt)]
          with z hz
        have hz' : ϱ z < ε⁻¹ * Real.sqrt ν := hz
        have h0 : 0 ≤ ϱ z := ϱ_nonneg z
        have hs2 : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
        have hm' := mul_le_mul hz'.le hz'.le h0 (mul_nonneg hR.le (Real.sqrt_nonneg ν))
        have he : (ε⁻¹ * Real.sqrt ν) * (ε⁻¹ * Real.sqrt ν) = ν * (ε⁻¹) ^ 2 := by
          rw [show (ε⁻¹ * Real.sqrt ν) * (ε⁻¹ * Real.sqrt ν) = (ε⁻¹) ^ 2 * Real.sqrt ν ^ 2 by ring,
            hs2]
          ring
        have hsq : ϱ z ^ 2 ≤ ν * (ε⁻¹) ^ 2 := by nlinarith [hm', he]
        exact wardXr_eq_zero_of_sq_le (ν := ν) (μ := μ) (R := ε⁻¹) (c := c) hχy (g₁ + g₂) τ hsq
      simp [physPd_congr_nhds hev, physPd_zero_fun]
  · exact axiNoSwirl_of_pt (wardXr ν μ ε⁻¹ c χy (g₁ + g₂))
      (fun τ => wardXrAxiOfX0_proved ν μ ε⁻¹ c χy (g₁ + g₂) hν hR hχy hW2.2.2 τ)


/-- **`WardXRegular` from the four Ward facts** (`PartIII-b:IIIb-D2/3/1/9`). -/
theorem wardXRegular_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (χy : ℝ → ℝ) (h1 : WardX0Smooth c mZ ρb γ ν ε μ hχo)
    (h2 : WardX0Structure c mZ ρb γ ν ε μ hχo) (h3 : OutPrimStream c mZ ρb γ ν ε μ hχo)
    (h4 : WardStreamCutDivFree ν ε⁻¹ χy) : WardXRegular c mZ ρb γ ν ε μ hχo χy :=
  wardXRegular_of_boot outPrimC2Boot_proved c mZ ρb γ ν ε μ hχo χy h1 h2 h3 h4

end UnforcedLeray.Short.PartIIIb.Concrete
