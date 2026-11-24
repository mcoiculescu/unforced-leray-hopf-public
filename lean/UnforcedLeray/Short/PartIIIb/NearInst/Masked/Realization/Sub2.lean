import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub1
import UnforcedLeray.Lib.Semigroups.Adjoint

/-!
# Leaves of `KF2` (source 3613, "In its Laplace integral")

Source of record: `the November 2 reference manuscript`.

`physRes = (outerS hν ε).laplace μ` is the `L²`-valued Bochner integral
`∫_0^∞ e^{-μt} S_ε(t)F dt` (3613, `Infra.ExpSemigroup.laplace`), and `S_ε(t)` acts pointwise by
`e^{t/2}[e^{θ_tΔ}F(·, τ - t)](e^{t/2}x)`, `θ_t = νε²(eᵗ - 1)` (3606-3608, `KF1`).  `KF2` evaluates
the Bochner integral pointwise a.e.:

* `KF2a`: the explicit integrand `kfSgInt` is jointly strongly measurable in `(t, w)`;
* `KF2b1`: for a jointly measurable representative `G` of `t ↦ S(t)x`, the Laplace integrand is
  integrable on `A × (0, ∞)` for every `A` of finite measure (Fubini, as in
  `B0225.integrable_lapRep`);
* `KF2b2`: then `S.laplace μ x = ∫_0^∞ e^{-μt} G(t, ·) dt` a.e. (testing against sets of finite
  measure, as in `B0225.R0_ae_eq`).

## Positivity hypotheses (`KF1pos`, `KF2pos`)

`KF1` and `KF2` of `Realization/Sub1.lean` carry no hypothesis `ε > 0` (and `KF1` none on `ν`).
At `ε = 0` the heat time is `θ = 0`, `heatG 0 = 0` (`(4π·0)^{-3/2} = 0`), so their right-hand sides
vanish while `S_ε(t)`, `physRes` do not: both are false (`not_KF1_body`, `not_KF2_body` below,
stated for the literal bodies of `Sub1.KF1`, `Sub1.KF2`).  The source has `ν > 0`, `ε > 0`
throughout (3586-3613).  `KF1pos` is `KF1` with the hypothesis `0 < ν * ε ^ 2` of `B0223.Sop_rep`
(the restatement planned by the organize task `…/18/1/KF1/org`), `KF2pos` is `KF2` with `0 < ε`;
`kf2pos_of` proves `KF2pos` from `KF1pos` and the three leaves, and `kernelFormulaSmooth_of'` is
`Sub1.kernelFormulaSmooth_of` with `KF2pos` in place of `KF2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked
open UnforcedLeray.B0223 UnforcedLeray.Infra

/-- The explicit outer semigroup in component `i` (3606-3608):
`e^{t/2} ∫ G_{νε²(eᵗ-1)}(y) F(e^{t/2}x - y, s - t)_i dy` at `w = (x, s)`. -/
def kfSgInt (ν ε P : ℝ) [Fact (0 < P)] (F : X SpaceC P) (t : ℝ) (w : PSpace P) (i : Fin 3) : ℂ :=
  ((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
    ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
      (F (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i

/-- The explicit outer semigroup as a vector of `ℂ³`. -/
def kfSgVec (ν ε P : ℝ) [Fact (0 < P)] (F : X SpaceC P) (t : ℝ) (w : PSpace P) : SpaceC :=
  WithLp.toLp 2 (fun i => kfSgInt ν ε P F t w i)

theorem kfSgVec_apply (ν ε P : ℝ) [Fact (0 < P)] (F : X SpaceC P) (t : ℝ) (w : PSpace P)
    (i : Fin 3) : kfSgVec ν ε P F t w i = kfSgInt ν ε P F t w i := rfl

/-- **KF1pos** (3606-3608): `KF1` of `Sub1` with the hypothesis `0 < νε²` (source `ν > 0`, `ε > 0`;
the hypothesis of `B0223.Sop_rep`; heat time `θ_t = νε²(eᵗ-1) > 0` for `t > 0`): the outer
semigroup `S_ε(t) = e^{-t/4} dilN(e^{t/2}) e^{θ_tΔ} transC t` acts pointwise a.e. by
`e^{t/2}[e^{θ_tΔ}F(·, τ-t)](e^{t/2}x)`, componentwise. -/
def KF1pos : Prop :=
  ∀ (ν ε : ℝ) (P : ℝ) [Fact (0 < P)] (F : X SpaceC P) (t : ℝ), 0 < ν * ε ^ 2 → 0 < t →
    ∀ᵐ w : PSpace P ∂volume, ∀ i : Fin 3,
      (Sop (ν * ε ^ 2) t F w) i =
        ((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
          ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
            (F (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i

/-- **KF2pos** (3613, "In its Laplace integral"): `KF2` of `Sub1` with the source hypothesis
`ε > 0`: `physRes = ∫_0^∞ e^{-μt}S_ε(t)dt` evaluated pointwise a.e. with the explicit semigroup
of `KF1pos`. -/
def KF2pos : Prop :=
  ∀ (ν ε : ℝ) (hν : 0 < ν), 0 < ε → ∀ (P : ℝ) [Fact (0 < P)] (μ : ℂ), -(1 / 4) < μ.re →
    ∀ F : X SpaceC P,
    ∀ᵐ w : PSpace P ∂volume, ∀ i : Fin 3,
      (physRes hν ε μ F w) i =
        ∫ t in Ioi (0 : ℝ), Complex.exp (-μ * t) *
          (((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
            ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
              (F (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i)

/-- **KF2a** (joint measurability of the explicit integrand, 3606-3608, 3613): each component of
`(t, w) ↦ e^{t/2} ∫ G_{θ_t}(y) F(e^{t/2}w.1 - y, w.2 - t) dy` is strongly measurable on
`ℝ × PSpace P`.  Route: the integrand `((t, w), y) ↦ G_{θ_t}(y) F(e^{t/2}w.1 - y, w.2 - t)_i` is
strongly measurable (`Lp.stronglyMeasurable F` composed with a continuous map, `heatG`
measurable), so `StronglyMeasurable.integral_prod_right'` applies; multiply by the continuous
`e^{t/2}`. -/
def KF2a : Prop :=
  ∀ (ν ε P : ℝ) [Fact (0 < P)] (F : X SpaceC P) (i : Fin 3),
    StronglyMeasurable (fun p : ℝ × PSpace P => kfSgInt ν ε P F p.1 p.2 i)

/-- **KF2b1** (Fubini integrability for the Laplace integral in `L²`, 3613): if `G` is a jointly
strongly measurable representative of `t ↦ S(t)x` for `t > 0` and `ω < Re μ`, then
`(w, t) ↦ e^{-μt} G(t, w)` is integrable on `A × (0, ∞)` for every `A` of finite measure:
`∫_A |S(t)x| ≤ |A|^{1/2} ‖S(t)x‖ ≤ |A|^{1/2} M e^{ωt} ‖x‖` (`B0225.integral_norm_le_Lp`,
`ExpSemigroup.norm_T_apply_le`), then `integrable_prod_iff'` (template: `B0225.integrable_lapRep`). -/
def KF2b1 : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (S : ExpSemigroup (X SpaceC P)) (μ : ℂ), S.ω < μ.re →
    ∀ (x : X SpaceC P) (G : ℝ → PSpace P → SpaceC),
      StronglyMeasurable (Function.uncurry G) →
      (∀ t : ℝ, 0 < t → G t =ᵐ[volume] (S.T t x : PSpace P → SpaceC)) →
      ∀ A : Set (PSpace P), volume A < ∞ →
        Integrable (fun p : PSpace P × ℝ => Complex.exp (-(μ * p.2)) • G p.2 p.1)
          ((volume.restrict A).prod (volume.restrict (Ioi 0)))

/-- **KF2b2** (the `L²`-valued Bochner integral evaluated pointwise, 3613): under the hypotheses of
`KF2b1` and the Fubini integrability it provides, for a.e. `w` the scalar integrand is integrable
on `(0, ∞)` and `S.laplace μ x (w) = ∫_0^∞ e^{-μt} G(t, w) dt`.  Route: test against sets `A` of
finite measure (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`); `f ↦ ∫_A f` is a bounded
functional (`B0225.setIntL`) commuting with the Bochner integral (`integral_comp_comm`,
`ExpSemigroup.laplace_apply`, `integrableOn_lapInt`), then `integral_integral_swap` (template:
`B0225.R0_ae_eq`). -/
def KF2b2 : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (S : ExpSemigroup (X SpaceC P)) (μ : ℂ), S.ω < μ.re →
    ∀ (x : X SpaceC P) (G : ℝ → PSpace P → SpaceC),
      StronglyMeasurable (Function.uncurry G) →
      (∀ t : ℝ, 0 < t → G t =ᵐ[volume] (S.T t x : PSpace P → SpaceC)) →
      (∀ A : Set (PSpace P), volume A < ∞ →
        Integrable (fun p : PSpace P × ℝ => Complex.exp (-(μ * p.2)) • G p.2 p.1)
          ((volume.restrict A).prod (volume.restrict (Ioi 0)))) →
      (∀ᵐ w : PSpace P ∂volume,
          IntegrableOn (fun t : ℝ => Complex.exp (-(μ * t)) • G t w) (Ioi 0)) ∧
        (S.laplace μ x : PSpace P → SpaceC) =ᵐ[volume]
          fun w => ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) • G t w

/-! ## The assembly -/

theorem stronglyMeasurable_kfSgVec (ha : KF2a) (ν ε P : ℝ) [Fact (0 < P)] (F : X SpaceC P) :
    StronglyMeasurable (Function.uncurry (kfSgVec ν ε P F)) := by
  have hm : Measurable (fun p : ℝ × PSpace P => fun i : Fin 3 => kfSgInt ν ε P F p.1 p.2 i) :=
    measurable_pi_lambda _ (fun i => (ha ν ε P F i).measurable)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp_stronglyMeasurable hm.stronglyMeasurable

/-- **`KF2pos` from the leaves.** -/
theorem kf2pos_of (h1 : KF1pos) (ha : KF2a) (hb1 : KF2b1) (hb2 : KF2b2) : KF2pos := by
  intro ν ε hν hε P _ μ hμ F
  set S : ExpSemigroup (X SpaceC P) := outerS hν ε with hS
  have hω : S.ω < μ.re := omega_lt (by linarith) hν ε
  set G : ℝ → PSpace P → SpaceC := kfSgVec ν ε P F with hG
  have hGm : StronglyMeasurable (Function.uncurry G) := stronglyMeasurable_kfSgVec ha ν ε P F
  have hGT : ∀ t : ℝ, 0 < t → G t =ᵐ[volume] (S.T t F : PSpace P → SpaceC) := by
    intro t ht
    filter_upwards [h1 ν ε P F t (by positivity) ht] with w hw
    ext i
    exact (hw i).symm
  obtain ⟨hint, heq⟩ := hb2 P S μ hω F G hGm hGT (hb1 P S μ hω F G hGm hGT)
  filter_upwards [hint, heq] with w hwi hwe
  intro i
  have hR : (physRes hν ε μ F : PSpace P → SpaceC) w = (S.laplace μ F : PSpace P → SpaceC) w :=
    rfl
  rw [hR, hwe]
  have hc := (EuclideanSpace.proj i : SpaceC →L[ℂ] ℂ).integral_comp_comm hwi
  change (EuclideanSpace.proj i : SpaceC →L[ℂ] ℂ)
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) • G t w) = _
  rw [← hc]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [map_smul, smul_eq_mul, neg_mul]
  rfl

/-- **`KernelFormulaSmooth` from the leaves**, with `KF2pos` (`Sub1.kernelFormulaSmooth_of`, whose
`KF2` lacks `ε > 0`). -/
theorem kernelFormulaSmooth_of' (h2 : KF2pos) (h3 : KF3) (h5a : KF5a) (h5b : KF5b) (h6 : KF6)
    (h7 : KF7) : KernelFormulaSmooth := by
  intro ν ε c P _ hν hε hc hP μ hμ T hT hM
  set F := toX hP (UnforcedLeray.B0226.P3D ε c (hM.toLp (cartDiv (outerField ε⁻¹ T)))) with hF
  have hCS : (CartStress hν hP μ (outerField ε⁻¹ T) hM :
      UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =
      (UnforcedLeray.B0223.physRes hν ε μ F : UnforcedLeray.B0223.PSpace P →
        UnforcedLeray.B0223.SpaceC) := rfl
  rw [hCS]
  have a2 := h2 ν ε hν hε P μ hμ F
  have a3 := h3 ν ε c P hν hε hc hP T hT hM
  have a3' : ∀ᵐ w : UnforcedLeray.B0223.PSpace P ∂volume, ∀ (x : Space) (θ : ℝ), 0 < θ →
      ∀ i : Fin 3, ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (x - y, w.2)) i =
        convTerm θ ε⁻¹ T x (UnforcedLeray.B0223.toCell P (0, w.2)).2 i :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Space))
      (ν := (volume : Measure (AddCircle P)))).ae a3
  filter_upwards [a2, a3'] with w hw2 hw3
  ext i
  rw [hw2 i]
  set N : Set (AddCircle P) := {s : AddCircle P | ¬ ∀ (x : Space)
      (θ : ℝ), 0 < θ → ∀ i : Fin 3, ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (x - y, s)) i =
        convTerm θ ε⁻¹ T x (UnforcedLeray.B0223.toCell P (0, s)).2 i} with hN
  have hNull := h7 P N (ae_iff.1 a3) w.2
  have h0 : ∀ᵐ t : ℝ, w.2 - (t : AddCircle P) ∉ N := by
    rw [ae_iff]
    simpa using hNull
  have key : ∫ t in Ioi (0 : ℝ), Complex.exp (-μ * t) *
      (((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
        ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
          ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC)
            (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-μ * t) *
        (((ε⁻¹ * Real.exp (-t / 2) ^ 3 : ℝ) : ℂ) * sepInner ν (Real.exp (-t / 2)) T (ε⁻¹ • w.1)
          ((UnforcedLeray.B0223.toCell P w).2 - t) i) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_Ioi] with t ht htpos
    have ht' : ∀ (x : Space) (θ : ℝ), 0 < θ → ∀ i : Fin 3,
        ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC)
            (x - y, w.2 - (t : AddCircle P))) i =
        convTerm θ ε⁻¹ T x (UnforcedLeray.B0223.toCell P (0, w.2 - (t : AddCircle P))).2 i := by
      have h' := ht
      rw [hN] at h'
      simpa using h'
    have htp : (0 : ℝ) < t := htpos
    have hθ : 0 < ν * ε ^ 2 * (Real.exp t - 1) := by
      have : 0 < Real.exp t - 1 := by linarith [Real.add_one_lt_exp htp.ne']
      positivity
    have e1 := h5a ν ε hν hε T w.1 ((UnforcedLeray.B0223.toCell P w).2 - t) t htp i
    rw [ht' _ _ hθ i, convTerm_congr _ _ T _ (h6 P T hT.periodic w.2 t) i, ← e1]
    rfl
  rw [key, h5b ν μ ε⁻¹ T (ε⁻¹ • w.1) (UnforcedLeray.B0223.toCell P w).2 i]
  simp only [kernelField, sepW_eq_sepInner]
  ring

/-! ## The literal `KF1`, `KF2` of `Sub1` are false at `ε = 0` -/

/-- A nonzero element of `X SpaceC P`: the indicator of `B(0,1) × (ℝ/Pℤ)` times `e₀`. -/
theorem exists_ne_zero_X (P : ℝ) [Fact (0 < P)] : ∃ F : X SpaceC P, F ≠ 0 := by
  set s : Set (PSpace P) := Metric.ball (0 : Space) 1 ×ˢ (univ : Set (AddCircle P)) with hs_def
  have hs : MeasurableSet s := measurableSet_ball.prod MeasurableSet.univ
  have hvol : volume s = volume (Metric.ball (0 : Space) 1) * volume (univ : Set (AddCircle P)) := by
    rw [hs_def, Measure.volume_eq_prod, Measure.prod_prod]
  have hfin : volume s ≠ ∞ := by
    rw [hvol, AddCircle.measure_univ]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  have hpos : volume s ≠ 0 := by
    rw [hvol, AddCircle.measure_univ]
    exact mul_ne_zero (Metric.measure_ball_pos volume _ one_pos).ne'
      (ENNReal.ofReal_pos.2 (Fact.out : 0 < P)).ne'
  refine ⟨indicatorConstLp 2 hs hfin (EuclideanSpace.single (0 : Fin 3) (1 : ℂ)), fun h => ?_⟩
  have hn := norm_indicatorConstLp (p := 2) (μ := volume) (hs := hs) (hμs := hfin)
    (c := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) (by norm_num) (by norm_num)
  rw [h, norm_zero, PiLp.norm_single, norm_one, one_mul] at hn
  have : 0 < volume.real s ^ (1 / (2 : ℝ≥0∞).toReal) :=
    Real.rpow_pos_of_pos (by rw [measureReal_def]; exact ENNReal.toReal_pos hpos hfin) _
  linarith

theorem heatG_zero_time (y : Space) : UnforcedLeray.Short.IIIa.heatG 0 y = 0 := by
  rw [UnforcedLeray.Short.IIIa.heatG, mul_zero, Real.zero_rpow (by norm_num), zero_mul]

/-- **`KF1` of `Sub1` is false** (its literal body; `ν = 1`, `ε = 0`, `t = 1`): the right-hand side
vanishes (`heatG 0 = 0`), while `‖S(1)F‖ = e^{-1/4}‖F‖`. -/
theorem not_KF1_body :
    ¬ ∀ (ν ε : ℝ) (P : ℝ) [Fact (0 < P)] (F : X SpaceC P) (t : ℝ), 0 < t →
      ∀ᵐ w : PSpace P ∂volume, ∀ i : Fin 3,
        (Sop (ν * ε ^ 2) t F w) i =
          ((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
            ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
              (F (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i := by
  intro h
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  obtain ⟨F, hF⟩ := exists_ne_zero_X 1
  have h0 := h 1 0 1 F 1 one_pos
  have hθ : (1 : ℝ) * (0 : ℝ) ^ 2 * (Real.exp 1 - 1) = 0 := by ring
  have hz : (Sop ((1 : ℝ) * (0 : ℝ) ^ 2) 1 F : X SpaceC 1) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [h0] with w hw
    rw [Pi.zero_apply]
    ext i
    rw [hw i, hθ]
    simp [heatG_zero_time]
  have hn : ‖(Sop ((1 : ℝ) * (0 : ℝ) ^ 2) 1 F : X SpaceC 1)‖ = Real.exp (-1 / 4) * ‖F‖ := by
    rw [Sop_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      norm_dilN_apply, heatC_of_nonpos (by rw [hθ]), LinearIsometry.norm_map]
  rw [hz, norm_zero] at hn
  have hF0 : ‖F‖ = 0 := by
    have := Real.exp_pos (-1 / 4)
    rcases mul_eq_zero.1 hn.symm with h' | h'
    · linarith
    · exact h'
  exact hF (norm_eq_zero.1 hF0)

/-- **`KF2` of `Sub1` is false** (its literal body; `ν = 1`, `ε = 0`, `μ = 0`): the right-hand side
vanishes (`heatG 0 = 0`), while `physRes` is injective (`ExpSemigroup.laplace_injective`). -/
theorem not_KF2_body :
    ¬ ∀ (ν ε : ℝ) (hν : 0 < ν) (P : ℝ) [Fact (0 < P)] (μ : ℂ), -(1 / 4) < μ.re →
      ∀ F : X SpaceC P,
      ∀ᵐ w : PSpace P ∂volume, ∀ i : Fin 3,
        (physRes hν ε μ F w) i =
          ∫ t in Ioi (0 : ℝ), Complex.exp (-μ * t) *
            (((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
              ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
                (F (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i) := by
  intro h
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  obtain ⟨F, hF⟩ := exists_ne_zero_X 1
  have h0 := h 1 0 one_pos 1 0 (by norm_num) F
  have hz : (physRes (E := SpaceC) (P := 1) one_pos 0 0 F) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [h0] with w hw
    rw [Pi.zero_apply]
    ext i
    rw [hw i]
    simp [heatG_zero_time]
  have hω : (outerS (E := SpaceC) (P := 1) one_pos 0).ω < (0 : ℂ).re :=
    omega_lt (by norm_num) one_pos 0
  exact hF ((outerS (E := SpaceC) (P := 1) one_pos 0).laplace_injective hω hz)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
