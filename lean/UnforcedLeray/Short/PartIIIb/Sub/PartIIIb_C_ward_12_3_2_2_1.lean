import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualCartesianNS
import UnforcedLeray.Lib.Axisymmetric.Measure

/-!
# `PartIII-b:C/ward/12/3/2/2/1` (decomposition): `RawResidualDeriv2Y`

Source of record:
`the November 2 reference manuscript`,
lines 2542-2551 at `k = 2` (the train complete source belongs to `W^{2,Y_p}`: in the large-radius
region `ϱ > R₀` its unprojected second derivatives are bounded by
`C_{2,N} ϱ^{-5} (1 + |y₃|/ϱ)^{-N} ≤ C' ϱ^{-3} (1 + |y₃|/ϱ)^{-2}`, and on `ϱ ≤ R₀` the all-age
heat expansion gives smooth even radial powers with weighted axial decay `C (1 + |y₃|)^{-2}`),
1204-1225 (`F_R = s^{3/2} r`), 1270-1305, and 1305-1325 (smoothness through the axis).

By `RingLiftSmoothExt` (task `PartII-b:R1/6`, `Short/PartII-b/Sub/R1.lean:145`) and the proved
`ringResidualCartesianNS_proof` (`Short/PartII-b/Tasks/RawResidualFamily/RingResidualCartesianNS.lean`),
the complexified ring residual `rawResidualC p` agrees off the axis (`Axi.ϱ y ≠ 0`) with the
globally `C^∞` Cartesian Navier-Stokes expression
`Fc = L₀ p.ν U + advT U U + gradT Pw`.
Because `{x | Axi.ϱ x.2 ≠ 0}` is open and its complement has measure zero (`Axi.volume_axis`,
`Axi.ae_not_mem_axis`):
1. `pairF p.period (dy l (dy j Φ)) (rawResidualC p) = pairF p.period (dy l (dy j Φ)) Fc`, and two
   applications of `pairF_dy_of_smooth` (`PartIII-b_C_ward_12_3_2_2_2.lean:99`) turn this into
   `pairF p.period Φ (dy j (dy l Fc))`;
2. off the axis, `dy j (dy l Fc) = dy j (dy l (rawResidualC p))`, and `dy j (dy l Fc)` is smooth
   (hence a.e. strongly measurable on the phase-space cell);
3. the cylindrical envelope `RawResidualD2Envelope` (proved from `RawResidualD2FarDecay` and
   `RawResidualD2NearBound`) together with `cylProfile_memLp` (`CylMemLp.lean:117`) and
   `inletRepYq` (`Rep.lean:32`) represents `dy j (dy l Fc)` in `Y_{q₀}`, proving
   `rawResidualDeriv2Y_of_env`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF advT rep)
open UnforcedLeray.Short.IIb (trainStream trainPressure rawResidualC isExactPlanarTrain_params
  isExactPlanarTrain_params_rpow)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Order-2 far-field decay of the raw ring residual** (source lines 2542-2548 at `k = 2`,
1287-1305: in the large-radius region `ϱ > R₀` the unprojected second derivatives of the train
complete source satisfy `|D² F_R| ≤ C_{2,N} ϱ^{-5} (1 + |y₃|/ϱ)^{-N} ≤ C ϱ^{-3} (1 + |y₃|/ϱ)^{-2}`;
order-2 raw analogue of `InletFn2FarDecay`, `PartIII-b_C_ward_12_3_2_2_2.lean:186`). -/
def RawResidualD2FarDecay : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ j l : Fin 3,
      ∃ C R0 : ℝ, 0 < R0 ∧
        ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
          R0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
          ‖dy j (dy l (rawResidualC p)) (τ, y)‖ ≤
            C * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
              (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ))

/-- **Order-2 near-axis bound of the raw ring residual** (source lines 2548-2551 at `k = 2`,
1270-1304, 1310-1325: on `0 < ϱ ≤ R₀`, the all-age heat expansion extends smoothly through the axis
and its weighted remainder gives axial decay `|D² F_R| ≤ C (1 + |y₃|)^{-2}` off the axis; order-2
raw analogue of `InletFn2NearBound`, `PartIII-b_C_ward_12_3_2_2_2.lean:195`). -/
def RawResidualD2NearBound : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ (j l : Fin 3) (R0 : ℝ), 0 < R0 →
      ∃ C : ℝ, ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
        UnforcedLeray.Axi.ϱ y ≠ 0 → Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
        ‖dy j (dy l (rawResidualC p)) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)

/-- **Order-2 cylindrical envelope of the raw ring residual off the axis** (source lines 2542-2551,
1204-1225, 1305-1325; order-2 raw analogue of `InletFn2Envelope`,
`PartIII-b_C_ward_12_3_2_2_2.lean:203`). -/
def RawResidualD2Envelope : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ j l : Fin 3,
      ∃ C R0 : ℝ, 0 < R0 ∧
        ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
          UnforcedLeray.Axi.ϱ y ≠ 0 →
          ‖dy j (dy l (rawResidualC p)) (τ, y)‖ ≤ C * cylProfile R0 y

/-- `RawResidualD2Envelope` from `RawResidualD2FarDecay` and `RawResidualD2NearBound`. -/
theorem rawResidualD2Envelope_of (h1 : RawResidualD2FarDecay) (h2 : RawResidualD2NearBound) :
    RawResidualD2Envelope := by
  obtain ⟨ν₁, hν₁, H1⟩ := h1
  obtain ⟨ν₂, hν₂, H2⟩ := h2
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p htr hν hc hR hP j l => ?_⟩
  obtain ⟨Cf, R0, hR0, hf⟩ := H1 p htr (lt_of_lt_of_le hν (min_le_left _ _)) hc hR hP j l
  obtain ⟨Cn, hn⟩ := H2 p htr (lt_of_lt_of_le hν (min_le_right _ _)) hc hR hP j l R0 hR0
  refine ⟨max Cf Cn, R0, hR0, fun τ hτ y hy0 => ?_⟩
  unfold cylProfile
  split_ifs with hy
  · have hpos : 0 < (1 + |y 2|) ^ (-2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    exact (hn τ hτ y hy0 hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le)
  · have hy' : R0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := not_le.mp hy
    have hρ : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hR0.trans hy'
    have hpos : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
        (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos (by positivity) _)
    exact (hf τ hτ y hy').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)

namespace RawDeriv2EnvSub

theorem dy_eq_off_axis {F1 F2 : ℝ × UnforcedLeray.Space → CVec3}
    (h : ∀ x : ℝ × UnforcedLeray.Space, UnforcedLeray.Axi.ϱ x.2 ≠ 0 → F1 x = F2 x)
    (j : Fin 3) {x : ℝ × UnforcedLeray.Space} (hx : UnforcedLeray.Axi.ϱ x.2 ≠ 0) :
    dy j F1 x = dy j F2 x := by
  have hop : IsOpen {z : ℝ × UnforcedLeray.Space | z.2 ∉ UnforcedLeray.Axi.axis} :=
    UnforcedLeray.Axi.isOpen_compl_axis.preimage continuous_snd
  have hx' : x ∈ {z : ℝ × UnforcedLeray.Space | z.2 ∉ UnforcedLeray.Axi.axis} := by
    change x.2 ∉ UnforcedLeray.Axi.axis
    rwa [UnforcedLeray.Axi.mem_axis_iff]
  have hev : F1 =ᶠ[𝓝 x] F2 :=
    Filter.eventuallyEq_of_mem (hop.mem_nhds hx') fun z hz => h z
      (mt (UnforcedLeray.Axi.mem_axis_iff z.2).mpr hz)
  unfold dy
  rw [hev.fderiv_eq]

theorem dy2_eq_off_axis {F1 F2 : ℝ × UnforcedLeray.Space → CVec3}
    (h : ∀ x : ℝ × UnforcedLeray.Space, UnforcedLeray.Axi.ϱ x.2 ≠ 0 → F1 x = F2 x)
    (j l : Fin 3) {x : ℝ × UnforcedLeray.Space} (hx : UnforcedLeray.Axi.ϱ x.2 ≠ 0) :
    dy j (dy l F1) x = dy j (dy l F2) x :=
  dy_eq_off_axis (fun _ hz => dy_eq_off_axis h l hz) j hx

theorem contDiff_ns_rhs (ν : ℝ) {U : ℝ × UnforcedLeray.Space → CVec3}
    {Pw : ℝ × UnforcedLeray.Space → ℂ} (hU : ContDiff ℝ ∞ U) (hPw : ContDiff ℝ ∞ Pw) :
    ContDiff ℝ ∞ (fun x =>
      UnforcedLeray.B0411.L0 ν U x + advT U U x + gradT Pw x) := by
  have hL : ContDiff ℝ ∞ (UnforcedLeray.B0411.L0 ν U) := by
    unfold UnforcedLeray.B0411.L0 UnforcedLeray.B0411.T0
    exact (((contDiff_dτ hU).sub ((contDiff_radialT hU).const_smul _)).sub
      ((contDiff_lapT hU).const_smul _)).sub (hU.const_smul _)
  have hA : ContDiff ℝ ∞ (advT U U) := by
    unfold advT
    exact ContDiff.sum fun k _ =>
      ((contDiff_piLp_apply (p := 2) (i := k)).comp hU).smul
        (UnforcedLeray.PhaseSpace.contDiff_dy hU k)
  have hG : ContDiff ℝ ∞ (gradT Pw) := by
    unfold gradT dy
    refine ContDiff.sum fun j _ => ?_
    exact ((hPw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).smul contDiff_const
  exact (hL.add hA).add hG

theorem pairF_congr_off_axis (P : ℝ) (Ψ F1 F2 : ℝ × UnforcedLeray.Space → CVec3)
    (h : ∀ x : ℝ × UnforcedLeray.Space, UnforcedLeray.Axi.ϱ x.2 ≠ 0 → F1 x = F2 x) :
    pairF P Ψ F1 = pairF P Ψ F2 := by
  unfold pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards with τ _
  refine integral_congr_ae ?_
  filter_upwards [UnforcedLeray.Axi.ae_not_mem_axis] with y hy
  rw [h (τ, y) (mt (UnforcedLeray.Axi.mem_axis_iff y).mpr hy)]

end RawDeriv2EnvSub

/-- `RawResidualDeriv2Y` from `RingLiftSmoothExt` and `RawResidualD2Envelope` (source lines
2542-2551, 1204-1225, 1305-1325). -/
theorem rawResidualDeriv2Y_of_smooth_env (hExt : UnforcedLeray.Short.IIb.RingLiftSmoothExt)
    (hEnv : RawResidualD2Envelope) : RawResidualDeriv2Y := by
  obtain ⟨ν₁, hν₁, H1⟩ := hExt
  obtain ⟨ν₂, hν₂, H2⟩ := hEnv
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p htr hν hc hR hP j l => ?_⟩
  obtain ⟨U, Pw, hU, hPw, -, -, hext⟩ :=
    H1 p.ν ⟨p.ν_pos, lt_of_lt_of_le hν (min_le_left _ _)⟩ (trainStream p) (trainPressure p)
      (isExactPlanarTrain_params_rpow p htr hc) p.R hR
  obtain ⟨C, R0, hR0, henv⟩ :=
    H2 p htr (lt_of_lt_of_le hν (min_le_right _ _)) hc hR hP j l
  let Fc : ℝ × UnforcedLeray.Space → CVec3 :=
    fun x => UnforcedLeray.B0411.L0 p.ν U x + advT U U x + gradT Pw x
  have hFc : ContDiff ℝ ∞ Fc := RawDeriv2EnvSub.contDiff_ns_rhs p.ν hU hPw
  have hoff : ∀ x : ℝ × UnforcedLeray.Space, UnforcedLeray.Axi.ϱ x.2 ≠ 0 →
      rawResidualC p x = Fc x := fun x hx =>
    UnforcedLeray.Short.IIb.ringResidualCartesianNS_proof p.ν p.c p.R
      (trainStream p) (trainPressure p) p.ν_pos p.c_pos hR
      (isExactPlanarTrain_params p htr) U Pw hU hPw hext x.1 x.2 hx
  let Fn : ℝ × UnforcedLeray.Space → CVec3 := dy j (dy l Fc)
  have hFn_smooth : ContDiff ℝ ∞ Fn :=
    UnforcedLeray.PhaseSpace.contDiff_dy (UnforcedLeray.PhaseSpace.contDiff_dy hFc l) j
  have hP0 : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hμ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p.period)) := ⟨by simp⟩
  have hg1 : MemLp (fun x : ℝ × UnforcedLeray.Space => C * cylProfile R0 x.2)
      UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) :=
    ((cylProfile_memLp R0 hR0).const_mul C).comp_snd (volume.restrict (Ioc (0 : ℝ) p.period))
  have hFn_lp : MemLp Fn UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) := by
    refine hg1.mono' hFn_smooth.continuous.aestronglyMeasurable ?_
    have hae1 : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume : Measure UnforcedLeray.Space)), x.1 ∈ Ioc (0 : ℝ) p.period :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    have hae2 : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume : Measure UnforcedLeray.Space)), x.2 ∉ UnforcedLeray.Axi.axis :=
      Measure.quasiMeasurePreserving_snd.ae UnforcedLeray.Axi.ae_not_mem_axis
    filter_upwards [hae1, hae2] with x hx1 hx2
    have hx0 : UnforcedLeray.Axi.ϱ x.2 ≠ 0 := mt (UnforcedLeray.Axi.mem_axis_iff x.2).mpr hx2
    have hd2 := RawDeriv2EnvSub.dy2_eq_off_axis hoff j l hx0
    show ‖Fn x‖ ≤ C * cylProfile R0 x.2
    rw [show Fn x = dy j (dy l (rawResidualC p)) x from hd2.symm]
    exact henv x.1 hx1 x.2 hx0
  obtain ⟨G, hG⟩ := inletRepYq p.period Fn hFn_lp
  refine ⟨G, fun Φ hΦ => ?_⟩
  have hΦt : IsPhaseTest p.period Φ := hΦ.1
  have hdyΦ : IsPhaseTest p.period (dy j Φ) := hΦt.dy j
  have h1 : pairF p.period (dy l (dy j Φ)) (rawResidualC p) =
      pairF p.period (dy l (dy j Φ)) Fc :=
    RawDeriv2EnvSub.pairF_congr_off_axis p.period (dy l (dy j Φ)) (rawResidualC p) Fc hoff
  have h2 : pairF p.period (dy l (dy j Φ)) Fc = pairF p.period (dy j Φ) (-dy l Fc) :=
    pairF_dy_of_smooth p.period l hdyΦ hFc
  have h3 : pairF p.period (dy j Φ) (-dy l Fc) = pairF p.period Φ Fn := by
    have h2' := pairF_dy_of_smooth p.period j hΦt (UnforcedLeray.PhaseSpace.contDiff_dy hFc l).neg
    change pairF p.period (dy j Φ) (-dy l Fc) = pairF p.period Φ (-dy j (-dy l Fc)) at h2'
    rw [h2', dy_neg, neg_neg]
  rw [h1, h2, h3, UnforcedLeray.Cons.C03.Concrete.phasePair_eq_pairF_rep hΦt G]
  unfold pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hG] with t ht' ht
  refine integral_congr_ae ?_
  filter_upwards [ht' ht] with y hy
  rw [hy]

/-- `RawResidualDeriv2Y` from `RingLiftSmoothExt`, `RawResidualD2FarDecay`, and
`RawResidualD2NearBound` (source lines 2542-2551, 1204-1225, 1305-1325). -/
theorem rawResidualDeriv2Y_of_env (hExt : UnforcedLeray.Short.IIb.RingLiftSmoothExt)
    (hFar : RawResidualD2FarDecay) (hNear : RawResidualD2NearBound) : RawResidualDeriv2Y :=
  rawResidualDeriv2Y_of_smooth_env hExt (rawResidualD2Envelope_of hFar hNear)

end UnforcedLeray.Short.PartIIIb.Concrete
