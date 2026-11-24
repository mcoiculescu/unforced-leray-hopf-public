import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Inputs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Proofs.MultPin
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift
import UnforcedLeray.Units.B0005.Bridge.Solenoidal

/-!
# `modeOfReturn` — Task `PartIII-b:IIIb-D5/2` decomposition (source 5969-5985)

Source of record: `the November 2 reference manuscript`.

Conditional proof `modeOfReturn_of` of `Wiring.ModeOfReturn` (`Proofs/Wiring/Inputs.lean:240`).
At an actual level `n` of the sequence with `NearAt` and `RegimePins` at `σ = μ_n(z) ∈ (0, 1/4)`,
given a return solution `T' ≠ 0`, `D T' = 0` with `b = -S_σ T'`, `T' = M_U b`, `b ≠ 0`, we define
the candidate energy mode `M = modeCore (D.level n) (D.mu n z) b` with physical velocity field
`modeBstar L b τ y = Nv L.ε⁻¹ (perExt (cOf L.ν) b) τ y` (whose complexification is
`velPhys L.ε⁻¹ (cOf L.ν) b`).

Proved outright here:
* `phaseμ_eq_smul_restrict_periodSlab`, `restrict_periodSlab_eq_smul_phaseμ` : comparison between
  `Axi.phaseμ P` and `volume.restrict (periodSlab P)`;
* `modeBstar_periodic` : `Function.Periodic (modeBstar L b) (2 * L.ε * cOf L.ν)` (`Axi.Nv_dss`,
  `Axi.perExt_periodic`);
* `modeBstar_measurable` : joint `AEStronglyMeasurable` of `modeBstar L b` (`Axi.measurable_Nv`,
  `Axi.measurable_perExt`);
* `modeBstar_memL2` : `MemLp (fun z : SpaceTime => modeBstar L b z.1 z.2) 2
  (volume.restrict (periodSlab (2 * L.ε * cOf L.ν)))` (`Axi.memLp_liftFun`,
  `Axi.liftFun_congr_ae`, `NearInst.coeFn_hOfVel`);
* `modeBstar_nonzero` : `b ≠ 0 → ¬ (modeBstar L b =ᵐ[volume.restrict (periodSlab P)] 0)`
  (`Axi.Jv` isometry + `NearInst.coeFn_hOfVel` + `NearInst.ae_bodyMeasure`);
* `modeBstar_symmetric` : `∀ᵐ τ, IsAxisymmetricNoSwirl (modeBstar L b τ)`
  (`Axi.isAxisymmetricNoSwirl_Nv`);
* `mode_weakDmu_and_mult` : operator unpacking at a `NearAt` + `RegimePins` level
  via `concreteOps_eq`, `concreteBase_isStressInverse` and `concreteBase_isExactMultiplier` with
  `NearInst.multPinOfLink`, together with `stressPair_neg_mult_eq` (`strSumExactAE_proved` +
  `NearInst.stressPairAE`);
* `modeBstar_isY2`, `jointC_modeBstar`, `phasePair_toY_modeBstar`, `isPhaseSolenoidal_toY_modeBstar`,
  `modeBstar_solenoidal` : slice solenoidality `∀ᵐ τ, IsSolenoidal (modeBstar L b τ)` proved
  outright from `IsWeakSolenoidal` via `B0005.IsY2.ae_isSolenoidal_of_phase`;
* `dotL_L0T_cplxT_velPhys`, `pairF_L0T_cplxT_velPhys` : pointwise and period-slab integral
  agreement of `dotL (L0T L.ν (B0005.cplxT φ) z + μ • B0005.cplxT φ z) (velPhys L.ε⁻¹ (cOf L.ν) b z)`
  with `weakModeIntegrand L.ν μ (modeBstar L b) φ z`;
* `modeBstar_isH1Periodic_of_grad`, `modeOfReturn_of`, `modeOfReturn_of_grad` :
  assembly of `Interface.IsEnergyMode` and `Wiring.ModeOfReturn` from the two remaining analytic
  bridge hypotheses `StressInvH1Grad` (source 1556-1572, 5975-5978) and `WeakDmuToPeriodicModeEq`
  (source 4145-4147, 5975-5985).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

namespace Wiring.ModeAux

/-- The physical velocity field `b_*(τ, y) = 𝒩_v b (τ, y)` of a chart velocity `b` at level `L`
(source 2683, 5975-5978; the real part of `velPhys L.ε⁻¹ (cOf L.ν) b`). -/
def modeBstar (L : ReturnLevel) (b : Chart → Merid) : ℝ → SpatialField :=
  fun τ y => Nv L.ε⁻¹ (perExt (cOf L.ν) b) τ y

/-- The candidate `Interface.EnergyModeCore` at level `L`, rate `μ`, and chart velocity `b`. -/
def modeCore (L : ReturnLevel) (μ : ℝ) (b : Chart → Merid) : Interface.EnergyModeCore where
  σ := μ
  bstar := modeBstar L b

@[simp]
theorem modeCore_σ (L : ReturnLevel) (μ : ℝ) (b : Chart → Merid) :
    (modeCore L μ b).σ = μ := rfl

@[simp]
theorem modeCore_bstar (L : ReturnLevel) (μ : ℝ) (b : Chart → Merid) :
    (modeCore L μ b).bstar = modeBstar L b := rfl

theorem velPhys_eq_realC_modeBstar (L : ReturnLevel) (b : Chart → Merid) :
    velPhys L.ε⁻¹ (cOf L.ν) b = fun x => B0412.realC (modeBstar L b x.1 x.2) := rfl

/-- `Axi.phaseμ P` is `(ENNReal.ofReal P)⁻¹` times `volume.restrict (periodSlab P)`. -/
theorem phaseμ_eq_smul_restrict_periodSlab (P : ℝ) :
    Axi.phaseμ P = (ENNReal.ofReal P)⁻¹ • volume.restrict (periodSlab P) := by
  rw [Axi.phaseμ, Measure.prod_smul_left, periodSlab]
  change (ENNReal.ofReal P)⁻¹ • (volume.restrict (Ioc 0 P)).prod volume =
    (ENNReal.ofReal P)⁻¹ • (volume.prod volume).restrict (Ioc 0 P ×ˢ univ)
  rw [Measure.restrict_prod_eq_prod_univ]

/-- For `P > 0`, `volume.restrict (periodSlab P)` is `ENNReal.ofReal P` times `Axi.phaseμ P`. -/
theorem restrict_periodSlab_eq_smul_phaseμ {P : ℝ} (hP : 0 < P) :
    volume.restrict (periodSlab P) = ENNReal.ofReal P • Axi.phaseμ P := by
  rw [phaseμ_eq_smul_restrict_periodSlab, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hP).ne' ENNReal.ofReal_ne_top, one_smul]

/-- `modeBstar L b` is `(√π * L.ε⁻¹) • liftFun L.ε⁻¹ (cOf L.ν) b`. -/
theorem modeBstar_eq_smul_liftFun (L : ReturnLevel) (b : Chart → Merid) :
    (fun z : SpaceTime => modeBstar L b z.1 z.2) =
      (Real.sqrt Real.pi * L.ε⁻¹) • Axi.liftFun L.ε⁻¹ (cOf L.ν) b := by
  have hpos : (Real.sqrt Real.pi * L.ε⁻¹) ≠ 0 :=
    (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (inv_pos.2 L.ε_pos)).ne'
  funext z
  simp only [Pi.smul_apply, Axi.liftFun, modeBstar, smul_smul, mul_inv_cancel₀ hpos, one_smul]

/-- Phase periodicity of `modeBstar L b` with period `2 * L.ε * cOf L.ν` (source 5975-5978). -/
theorem modeBstar_periodic (L : ReturnLevel) (b : Chart → Merid) :
    Function.Periodic (modeBstar L b) (2 * L.ε * cOf L.ν) := by
  have hP : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by rw [div_inv_eq_mul]; ring
  rw [hP]
  exact Axi.Nv_dss (inv_pos.2 L.ε_pos).ne' rfl
    (Axi.perExt_periodic (cOf_pos L.ν_pos).ne' b)

/-- Joint strong measurability of `modeBstar L b` on `SpaceTime = ℝ × Space`. -/
theorem modeBstar_measurable {Pl : PlanarData} (L : ReturnLevel) (b : LVel Pl L) :
    AEStronglyMeasurable (fun z : SpaceTime => modeBstar L b z.1 z.2) volume :=
  (Axi.measurable_Nv L.ε⁻¹
    (Axi.measurable_perExt (cOf L.ν) (Lp.stronglyMeasurable b).measurable)).aestronglyMeasurable

/-- Square-integrability of `modeBstar L b` on `periodSlab (2 * L.ε * cOf L.ν)` (source 5975-5978). -/
theorem modeBstar_memL2 {Pl : PlanarData} (L : ReturnLevel) (b : LVel Pl L) :
    MemLp (fun z : SpaceTime => modeBstar L b z.1 z.2) 2
      (volume.restrict (periodSlab (2 * L.ε * cOf L.ν))) := by
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hP0 : 0 < 2 * L.ε * cOf L.ν := mul_pos (mul_pos two_pos L.ε_pos) hc
  have hP : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by rw [div_inv_eq_mul]; ring
  set u : Hsp (cOf L.ν) :=
    (Real.sqrt Real.pi)⁻¹ •
      NearInst.gainH (cOf L.ν) (gRate Pl) L.ν_pos (NearInst.velIso (cOf L.ν) (gRate Pl) L.ν b)
  have hu_ae : Axi.liftFun L.ε⁻¹ (cOf L.ν) u =ᵐ[Axi.phaseμ (2 * L.ε * cOf L.ν)]
      Axi.liftFun L.ε⁻¹ (cOf L.ν) b :=
    Axi.liftFun_congr_ae hR hc hP (Lp.stronglyMeasurable u).measurable
      (Lp.stronglyMeasurable b).measurable (NearInst.coeFn_hOfVel (gRate Pl) L.ν_pos b)
  have hmem_lift : MemLp (Axi.liftFun L.ε⁻¹ (cOf L.ν) b) 2 (Axi.phaseμ (2 * L.ε * cOf L.ν)) :=
    (Axi.memLp_liftFun hR hc hP u).ae_eq hu_ae
  have hmem_phase : MemLp (fun z : SpaceTime => modeBstar L b z.1 z.2) 2
      (Axi.phaseμ (2 * L.ε * cOf L.ν)) := by
    rw [modeBstar_eq_smul_liftFun]
    exact hmem_lift.const_smul (Real.sqrt Real.pi * L.ε⁻¹)
  rw [restrict_periodSlab_eq_smul_phaseμ hP0]
  exact hmem_phase.smul_measure ENNReal.ofReal_ne_top

/-- Axisymmetry without swirl of `modeBstar L b` at every phase (source 5975-5978). -/
theorem modeBstar_symmetric (L : ReturnLevel) (b : Chart → Merid) :
    ∀ᵐ τ : ℝ, IsAxisymmetricNoSwirl (modeBstar L b τ) :=
  Eventually.of_forall fun τ => Axi.isAxisymmetricNoSwirl_Nv L.ε⁻¹ (Axi.perExt (cOf L.ν) b) τ

/-- Nonvanishing of `modeBstar L b` on `periodSlab (2 * L.ε * cOf L.ν)` when `b ≠ 0` in `LVel Pl L`
(source 5978-5980). -/
theorem modeBstar_nonzero {Pl : PlanarData} (L : ReturnLevel) {b : LVel Pl L} (hb0 : b ≠ 0) :
    ¬ ((fun z : SpaceTime => modeBstar L b z.1 z.2) =ᵐ[
      volume.restrict (periodSlab (2 * L.ε * cOf L.ν))] 0) := by
  intro hz
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hP0 : 0 < 2 * L.ε * cOf L.ν := mul_pos (mul_pos two_pos L.ε_pos) hc
  have hP : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by rw [div_inv_eq_mul]; ring
  set u : Hsp (cOf L.ν) :=
    (Real.sqrt Real.pi)⁻¹ •
      NearInst.gainH (cOf L.ν) (gRate Pl) L.ν_pos (NearInst.velIso (cOf L.ν) (gRate Pl) L.ν b)
  have hz_phase : (fun z : SpaceTime => modeBstar L b z.1 z.2) =ᵐ[
      Axi.phaseμ (2 * L.ε * cOf L.ν)] 0 := by
    rw [EventuallyEq, ae_iff, phaseμ_eq_smul_restrict_periodSlab, Measure.smul_apply,
      ae_iff.1 hz, smul_zero]
  have hlift_b : Axi.liftFun L.ε⁻¹ (cOf L.ν) b =ᵐ[Axi.phaseμ (2 * L.ε * cOf L.ν)] 0 := by
    filter_upwards [hz_phase] with z hzz
    simp only [Axi.liftFun, Pi.zero_apply] at hzz ⊢
    unfold modeBstar at hzz
    rw [hzz, smul_zero]
  have hu_ae : Axi.liftFun L.ε⁻¹ (cOf L.ν) u =ᵐ[Axi.phaseμ (2 * L.ε * cOf L.ν)]
      Axi.liftFun L.ε⁻¹ (cOf L.ν) b :=
    Axi.liftFun_congr_ae hR hc hP (Lp.stronglyMeasurable u).measurable
      (Lp.stronglyMeasurable b).measurable (NearInst.coeFn_hOfVel (gRate Pl) L.ν_pos b)
  have hJv0 : Axi.Jv hR hc hP u = 0 := by
    rw [Lp.ext_iff]
    exact (Axi.coeFn_Jv hR hc hP u).trans (hu_ae.trans (hlift_b.trans (Lp.coeFn_zero _ _ _).symm))
  have hu0 : u = 0 := (Axi.Jv hR hc hP).injective (hJv0.trans (map_zero _).symm)
  have hb_age : (b : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)] (0 : LVel Pl L) := by
    have h1 := (NearInst.coeFn_hOfVel (gRate Pl) L.ν_pos b).symm
    have h2 : (u : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)] 0 := by
      rw [hu0]
      exact Lp.coeFn_zero _ _ _
    have h3 : (0 : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)] ((0 : LVel Pl L) : Chart → Merid) := by
      have hz0 : ((0 : LVel Pl L) : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν] 0 :=
        Lp.coeFn_zero _ _ _
      rw [NearInst.ae_bodyMeasure] at hz0
      exact hz0.symm
    exact h1.trans (h2.trans h3)
  have hb_body : (b : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν] (0 : LVel Pl L) := by
    rw [NearInst.ae_bodyMeasure]
    exact hb_age
  exact hb0 (Lp.ext hb_body)

/-- Unpacking the exact return equations `b = -S_σ T'` and `T' = M_U b` at a `NearAt` + `RegimePins`
level gives `IsWeakDmu` for `velPhys L.ε⁻¹ (cOf L.ν) b` with right-hand side
`-stressPair P (strPhys L.ε⁻¹ (cOf L.ν) (strSum (-(B.M b))))` and `IsExactMultiplier B L.ε⁻¹ L.V L.rb`
(source 4145-4147, 5975-5985). -/
theorem mode_weakDmu_and_mult {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (hne : NearAt Pl K L μ) (hp : RegimePins Pl K L μ)
    {T' : LStr Pl K L} {b : LVel Pl L}
    (hb : b = -((concreteOps Pl K L μ).S T'))
    (hT : T' = (concreteOps Pl K L μ).M b) :
    b = (concreteBase Pl K L μ hne).S (-T') ∧
    IsWeakStressInverse (concreteBase Pl K L μ hne).S L.ε μ ∧
    IsExactMultiplier (concreteBase Pl K L μ hne) L.ε⁻¹ L.V L.rb ∧
    IsWeakDmu L.ν μ (2 * L.ε * cOf L.ν) (velPhys L.ε⁻¹ (cOf L.ν) b)
      (fun Φ => -stressPair (2 * L.ε * cOf L.ν)
        (strPhys L.ε⁻¹ (cOf L.ν) (strSum (-((concreteBase Pl K L μ hne).M b)))) Φ) := by
  have hS_inv : IsWeakStressInverse (concreteBase Pl K L μ hne).S L.ε μ :=
    concreteBase_isStressInverse hne hp.stress
  have hM_ex : IsExactMultiplier (concreteBase Pl K L μ hne) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier hne NearInst.multPinOfLink hp.split
  have hbS : b = (concreteBase Pl K L μ hne).S (-T') := by
    rw [hb, concreteOps_eq _ _ _ _ hne]
    exact ((concreteBase Pl K L μ hne).S.map_neg T').symm
  have hTM : T' = (concreteBase Pl K L μ hne).M b := by
    rw [hT, concreteOps_eq _ _ _ _ hne]
    rfl
  refine ⟨hbS, hS_inv, hM_ex, ?_⟩
  have hw := hS_inv (-T')
  rw [← hbS, hTM] at hw
  exact hw

/-- For an exact multiplier `B`, the stress pairing of `strSum (-(B.M b))` equals the stress pairing
of the chart symmetric outer product `symOuter (chartCoeff L.ε⁻¹ L.U p) ((-b) p)` (from
`strSumExactAE_proved` and `NearInst.stressPairAE`, source 4147). -/
theorem stressPair_neg_mult_eq {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel}
    (hC0 : 0 < K.C0)
    {B : ReturnBase (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν (AffSp K.as)}
    (hM : IsExactMultiplier B L.ε⁻¹ L.V L.rb) (b : LVel Pl L)
    (Φ : ℝ × Space → CVec3) :
    stressPair (2 * L.ε * cOf L.ν) (strPhys L.ε⁻¹ (cOf L.ν) (strSum (-(B.M b)))) Φ =
      stressPair (2 * L.ε * cOf L.ν)
        (strPhys L.ε⁻¹ (cOf L.ν) (fun p => NearInst.ten3Of
          (IIIa.symOuter (IIIa.chartCoeff L.ε⁻¹ L.U p) ((-b : LVel Pl L) p)))) Φ := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hρb : 0 < L.ρb Pl K :=
    mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos L.ν_pos _))) (Real.exp_pos _))
      (Real.rpow_pos_of_pos L.ε_pos _)
  have hneg : -(B.M b) = B.M (-b) := (B.M.map_neg b).symm
  rw [hneg]
  have hae := strSumExactAE_proved B hc hρb L.ε L.V L.rb hM (-b)
  exact NearInst.stressPairAE (cOf L.ν) L.ε hc L.ε_pos _ _ hae Φ

/-- `modeBstar L b` belongs to `B0005.IsY2 (2 * L.ε * cOf L.ν)` (periodic, jointly measurable,
square-integrable on the period slab). -/
theorem modeBstar_isY2 {Pl : PlanarData} (L : ReturnLevel) (b : LVel Pl L) :
    B0005.IsY2 (2 * L.ε * cOf L.ν) (modeBstar L b) :=
  ⟨modeBstar_periodic L b, modeBstar_measurable L b, modeBstar_memL2 L b⟩

/-- The complexified joint field `B0005.jointC (modeBstar L b)` is `velPhys L.ε⁻¹ (cOf L.ν) b`. -/
theorem jointC_modeBstar (L : ReturnLevel) (b : Chart → Merid) :
    B0005.jointC (modeBstar L b) = velPhys L.ε⁻¹ (cOf L.ν) b := by
  ext x i
  simp [B0005.jointC, velPhys, modeBstar, B0412.realC_apply]

/-- For any phase test `Φ`, the phase pairing of `B0005.toY P (modeBstar L b)` equals
`pairF P Φ (velPhys L.ε⁻¹ (cOf L.ν) b)` (`P = 2 * L.ε * cOf L.ν`). -/
theorem phasePair_toY_modeBstar {Pl : PlanarData} (L : ReturnLevel) (b : LVel Pl L)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest (2 * L.ε * cOf L.ν) Φ) :
    haveI : Fact (0 < 2 * L.ε * cOf L.ν) :=
      ⟨mul_pos (mul_pos two_pos L.ε_pos) (cOf_pos L.ν_pos)⟩
    phasePair (2 * L.ε * cOf L.ν) 2 Φ (B0005.toY (2 * L.ε * cOf L.ν) (modeBstar L b)) =
      UnforcedLeray.Cons.C03.Concrete.pairF (2 * L.ε * cOf L.ν) Φ
        (velPhys L.ε⁻¹ (cOf L.ν) b) := by
  set P : ℝ := 2 * L.ε * cOf L.ν
  have hP0 : 0 < P := mul_pos (mul_pos two_pos L.ε_pos) (cOf_pos L.ν_pos)
  have : Fact (0 < P) := ⟨hP0⟩
  have hf := modeBstar_isY2 L b
  rw [phasePair_eq_periodIntegral hΦ (B0005.toY P (modeBstar L b))]
  simp only [zero_add, UnforcedLeray.Cons.C03.Concrete.pairF,
    UnforcedLeray.Cons.C03.Concrete.phaseInt]
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [hf.toY_ae, hf.ae_pathOf_eq hP0] with t ht ht' _
  rw [ht]
  refine integral_congr_ae ?_
  filter_upwards [ht'] with y hy
  rw [hy, jointC_modeBstar]

/-- Weak solenoidality `IsWeakSolenoidal P (velPhys L.ε⁻¹ (cOf L.ν) b)` implies phase solenoidality
`IsPhaseSolenoidal (B0005.toY P (modeBstar L b))`. -/
theorem isPhaseSolenoidal_toY_modeBstar {Pl : PlanarData} (L : ReturnLevel) (b : LVel Pl L)
    (hsol : IsWeakSolenoidal (2 * L.ε * cOf L.ν) (velPhys L.ε⁻¹ (cOf L.ν) b)) :
    haveI : Fact (0 < 2 * L.ε * cOf L.ν) :=
      ⟨mul_pos (mul_pos two_pos L.ε_pos) (cOf_pos L.ν_pos)⟩
    IsPhaseSolenoidal (B0005.toY (2 * L.ε * cOf L.ν) (modeBstar L b)) := by
  have : Fact (0 < 2 * L.ε * cOf L.ν) :=
    ⟨mul_pos (mul_pos two_pos L.ε_pos) (cOf_pos L.ν_pos)⟩
  intro φ hφ
  rw [phasePair_toY_modeBstar L b hφ.gradT]
  exact hsol φ hφ

/-- **Slice solenoidality of `modeBstar L b` from `IsWeakSolenoidal`** (source 1556-1572, 5975-5978):
if `velPhys L.ε⁻¹ (cOf L.ν) b` is weakly solenoidal against scalar phase tests, then
`IsSolenoidal (modeBstar L b τ)` holds for almost every `τ ∈ ℝ` (via `B0005.IsY2.ae_isSolenoidal_of_phase`). -/
theorem modeBstar_solenoidal {Pl : PlanarData} (L : ReturnLevel) (b : LVel Pl L)
    (hsol : IsWeakSolenoidal (2 * L.ε * cOf L.ν) (velPhys L.ε⁻¹ (cOf L.ν) b)) :
    ∀ᵐ τ : ℝ, IsSolenoidal (modeBstar L b τ) := by
  have : Fact (0 < 2 * L.ε * cOf L.ν) :=
    ⟨mul_pos (mul_pos two_pos L.ε_pos) (cOf_pos L.ν_pos)⟩
  exact (modeBstar_isY2 L b).ae_isSolenoidal_of_phase (isPhaseSolenoidal_toY_modeBstar L b hsol)

/-- Pointwise agreement between the complexified transposed operator `L0T L.ν + μ` paired with
`velPhys L.ε⁻¹ (cOf L.ν) b` and `weakModeIntegrand L.ν μ (modeBstar L b) φ` for any smooth real
test `φ : SpaceTime → Space`. -/
theorem dotL_L0T_cplxT_velPhys (L : ReturnLevel) (μ : ℝ) (b : Chart → Merid)
    {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) (z : ℝ × Space) :
    dotL (L0T L.ν (B0005.cplxT φ) z + (μ : ℂ) • B0005.cplxT φ z)
        (velPhys L.ε⁻¹ (cOf L.ν) b z) =
      ((weakModeIntegrand L.ν μ (modeBstar L b) φ z : ℝ) : ℂ) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hL0 : L0T L.ν (B0005.cplxT φ) z + (μ : ℂ) • B0005.cplxT φ z =
      B0005.cplxT (fun x => (μ - 1 / 2) • φ x + driftT φ x - L.ν • lapT φ x) z := by
    simp only [L0T, nuLapT, B0005.driftT_cplxT hd, B0005.lapT_cplxT hφ, B0005.cplxT,
      Pi.sub_apply, Pi.smul_apply, map_sub, map_add, map_smul]
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, B0005.cplxL_apply,
      Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  rw [hL0, ← jointC_modeBstar, B0005.dotL_cplxT_jointC]
  congr 1
  have hdiff := congrFun (B0005.diffusionTerm_eq (modeBstar L b) hφ) z
  have hdrift := congrFun (B0005.driftAdjointTerm_eq (modeBstar L b) hd) z
  simp only [weakModeIntegrand, hdiff, hdrift, pairTerm, inner_sub_right, inner_add_right,
    real_inner_smul_right]

/-- Period-slab integral agreement between `pairF P (fun x => L0T L.ν (B0005.cplxT φ) x + μ • B0005.cplxT φ x)
(velPhys L.ε⁻¹ (cOf L.ν) b)` and `P⁻¹ * ∫ z in periodSlab P, weakModeIntegrand L.ν μ (modeBstar L b) φ z`. -/
theorem pairF_L0T_cplxT_velPhys (L : ReturnLevel) (μ : ℝ) (b : Chart → Merid)
    {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ)
    (hint : Integrable (weakModeIntegrand L.ν μ (modeBstar L b) φ)
      (volume.restrict (periodSlab (2 * L.ε * cOf L.ν)))) :
    UnforcedLeray.Cons.C03.Concrete.pairF (2 * L.ε * cOf L.ν)
        (fun x => L0T L.ν (B0005.cplxT φ) x + (μ : ℂ) • B0005.cplxT φ x)
        (velPhys L.ε⁻¹ (cOf L.ν) b) =
      (((2 * L.ε * cOf L.ν)⁻¹ *
        ∫ z in periodSlab (2 * L.ε * cOf L.ν),
          weakModeIntegrand L.ν μ (modeBstar L b) φ z : ℝ) : ℂ) := by
  set P : ℝ := 2 * L.ε * cOf L.ν
  simp only [UnforcedLeray.Cons.C03.Concrete.pairF, UnforcedLeray.Cons.C03.Concrete.phaseInt,
    dotL_L0T_cplxT_velPhys L μ b hφ]
  have hint_prod : Integrable (fun z : ℝ × Space => weakModeIntegrand L.ν μ (modeBstar L b) φ z)
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
    rwa [← B0005.IsY2.slab_eq P]
  have hprod : (∫ z in periodSlab P, weakModeIntegrand L.ν μ (modeBstar L b) φ z) =
      ∫ t in Ioc (0 : ℝ) P, ∫ y, weakModeIntegrand L.ν μ (modeBstar L b) φ (t, y) := by
    rw [B0005.IsY2.slab_eq P]
    exact integral_prod _ hint_prod
  rw [hprod]
  simp_rw [integral_complex_ofReal]
  rw [Complex.real_smul, Complex.ofReal_mul]

/-- **`Y_2` weak spatial gradient of the stress inverse** (source 1556-1572 `free:weak-stress`,
5975-5978): at an actual level of a `RepairStanding` sequence with `NearAt` and `RegimePins` at
`0 < μ < 1/4`, for a weak stress inverse `S = R_μ ℙ div` and any stress `T`, the lifted velocity
`modeBstar (D.level n) (S T)` has three weak spatial derivatives square-integrable on one period
(`HasWeakSpatialDerivative`).  Slice solenoidality is proved outright above in
`modeBstar_solenoidal`. -/
def StressInvH1Grad : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ), D.RepairStanding dm dp → ∀ n : ℕ, D.IsActualLevel dm dp n →
    2 * (D.level n).ε * cOf (D.level n).ν ≤ 1 →
    ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z) →
      RegimePins D.Pl D.K (D.level n) (D.mu n z) →
      0 < D.mu n z → D.mu n z < 1 / 4 →
      ∀ (S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)),
        IsWeakStressInverse S (D.level n).ε (D.mu n z) →
      ∀ (T : LStr D.Pl D.K (D.level n)),
        ∃ G : Fin 3 → ℝ → SpatialField, ∀ i : Fin 3,
          AEStronglyMeasurable (fun x : SpaceTime => G i x.1 x.2) volume ∧
          MemLp (fun x : SpaceTime => G i x.1 x.2) 2
            (volume.restrict (periodSlab (2 * (D.level n).ε * cOf (D.level n).ν))) ∧
          ∀ᵐ τ, HasWeakSpatialDerivative i (modeBstar (D.level n) (S T) τ) (G i τ)

/-- Combined `H¹` and solenoidal package for the stress inverse (from `modeBstar_solenoidal` and
`StressInvH1Grad`). -/
def StressInvH1Solenoidal : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ), D.RepairStanding dm dp → ∀ n : ℕ, D.IsActualLevel dm dp n →
    2 * (D.level n).ε * cOf (D.level n).ν ≤ 1 →
    ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z) →
      RegimePins D.Pl D.K (D.level n) (D.mu n z) →
      0 < D.mu n z → D.mu n z < 1 / 4 →
      ∀ (S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)),
        IsWeakStressInverse S (D.level n).ε (D.mu n z) →
      ∀ (T : LStr D.Pl D.K (D.level n)),
        (∀ᵐ τ, IsSolenoidal (modeBstar (D.level n) (S T) τ)) ∧
        ∃ G : Fin 3 → ℝ → SpatialField, ∀ i : Fin 3,
          AEStronglyMeasurable (fun x : SpaceTime => G i x.1 x.2) volume ∧
          MemLp (fun x : SpaceTime => G i x.1 x.2) 2
            (volume.restrict (periodSlab (2 * (D.level n).ε * cOf (D.level n).ν))) ∧
          ∀ᵐ τ, HasWeakSpatialDerivative i (modeBstar (D.level n) (S T) τ) (G i τ)

theorem stressInvH1Solenoidal_of_grad (hGrad : StressInvH1Grad) : StressInvH1Solenoidal :=
  fun D dm dp hst n hact hP1 z hz hne hp hμ0 hμ1 S hS T =>
    ⟨modeBstar_solenoidal (D.level n) (S T) (hS T).solenoidal,
      hGrad D dm dp hst n hact hP1 z hz hne hp hμ0 hμ1 S hS T⟩

/-- Assembly of `IsH1Periodic (2 * (D.level n).ε * cOf (D.level n).ν) (modeBstar (D.level n) (S T))`
from the proved `𝒴_{2,div}` properties (`modeBstar_periodic`, `modeBstar_measurable`,
`modeBstar_memL2`, `modeBstar_solenoidal`) and `StressInvH1Grad`. -/
theorem modeBstar_isH1Periodic_of_grad (hGrad : StressInvH1Grad)
    (D : SeqData) (dm dp : ℝ) (hst : D.RepairStanding dm dp) (n : ℕ) (hact : D.IsActualLevel dm dp n)
    (hP1 : 2 * (D.level n).ε * cOf (D.level n).ν ≤ 1) (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) (hne : NearAt D.Pl D.K (D.level n) (D.mu n z))
    (hp : RegimePins D.Pl D.K (D.level n) (D.mu n z))
    (hμ0 : 0 < D.mu n z) (hμ1 : D.mu n z < 1 / 4)
    {S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)}
    (hS : IsWeakStressInverse S (D.level n).ε (D.mu n z))
    (T : LStr D.Pl D.K (D.level n)) :
    IsH1Periodic (2 * (D.level n).ε * cOf (D.level n).ν) (modeBstar (D.level n) (S T)) :=
  ⟨⟨modeBstar_periodic (D.level n) (S T), modeBstar_measurable (D.level n) (S T),
    modeBstar_memL2 (D.level n) (S T), modeBstar_solenoidal (D.level n) (S T) (hS T).solenoidal⟩,
    hGrad D dm dp hst n hact hP1 z hz hne hp hμ0 hμ1 S hS T⟩

/-- Assembly of `IsH1Periodic (2 * (D.level n).ε * cOf (D.level n).ν) (modeBstar (D.level n) (S T))`
from `StressInvH1Solenoidal`. -/
theorem modeBstar_isH1Periodic (hH1 : StressInvH1Solenoidal)
    (D : SeqData) (dm dp : ℝ) (hst : D.RepairStanding dm dp) (n : ℕ) (hact : D.IsActualLevel dm dp n)
    (hP1 : 2 * (D.level n).ε * cOf (D.level n).ν ≤ 1) (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) (hne : NearAt D.Pl D.K (D.level n) (D.mu n z))
    (hp : RegimePins D.Pl D.K (D.level n) (D.mu n z))
    (hμ0 : 0 < D.mu n z) (hμ1 : D.mu n z < 1 / 4)
    {S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)}
    (hS : IsWeakStressInverse S (D.level n).ε (D.mu n z))
    (T : LStr D.Pl D.K (D.level n)) :
    IsH1Periodic (2 * (D.level n).ε * cOf (D.level n).ν) (modeBstar (D.level n) (S T)) := by
  obtain ⟨hsol, hgrad⟩ := hH1 D dm dp hst n hact hP1 z hz hne hp hμ0 hμ1 S hS T
  exact ⟨⟨modeBstar_periodic (D.level n) (S T), modeBstar_measurable (D.level n) (S T),
    modeBstar_memL2 (D.level n) (S T), hsol⟩, hgrad⟩

/-- **Transfer from the solenoidal-test `IsWeakDmu` equation with exact multiplier rhs to
`Interface.SolvesPeriodicModeEquation`** (source 4145-4147, 5975-5985): at an actual level of the
standing sequence with `NearAt` and `RegimePins` at `0 < μ < 1/4`, if `modeBstar (D.level n) b`
belongs to `IsH1Periodic` and `velPhys ε⁻¹ c b` solves `D_μ b_* = -ℙ div 𝒩_T(M_U b)` in the sense
of `IsWeakDmu` for a base `B` satisfying `IsExactMultiplier B ε⁻¹ V rb`, then the real lift
`modeBstar (D.level n) b` satisfies `Interface.SolvesPeriodicModeEquation` against all real
periodic tests `Interface.IsPeriodicTest`. -/
def WeakDmuToPeriodicModeEq : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ), D.RepairStanding dm dp → ∀ n : ℕ, D.IsActualLevel dm dp n →
    ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z) →
      RegimePins D.Pl D.K (D.level n) (D.mu n z) →
      0 < D.mu n z → D.mu n z < 1 / 4 →
      ∀ (B : ReturnBase (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K)
          (gRate D.Pl) (D.level n).ν (AffSp D.K.as)),
        IsExactMultiplier B (D.level n).ε⁻¹ (D.level n).V (D.level n).rb →
      ∀ (b : LVel D.Pl (D.level n)),
        IsH1Periodic (2 * (D.level n).ε * cOf (D.level n).ν) (modeBstar (D.level n) b) →
        IsWeakDmu (D.level n).ν (D.mu n z) (2 * (D.level n).ε * cOf (D.level n).ν)
          (velPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) b)
          (fun Φ => -stressPair (2 * (D.level n).ε * cOf (D.level n).ν)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum (-(B.M b)))) Φ) →
        Interface.SolvesPeriodicModeEquation (D.level n).ν (D.mu n z)
          (2 * (D.level n).ε * cOf (D.level n).ν) (D.level n).U (modeBstar (D.level n) b)

end Wiring.ModeAux

open Wiring.ModeAux

/-- **Conditional proof of `Wiring.ModeOfReturn`** (Task `PartIII-b:IIIb-D5/2`, source 5969-5985)
from `StressInvH1Solenoidal` and `WeakDmuToPeriodicModeEq`, with the mode candidate construction,
`σ ∈ (0, 1/4)`, axisymmetry without swirl, periodicity, joint measurability, `L²` membership on the
period slab, nonvanishing on the period slab, and operator unpacking at a `NearAt` + `RegimePins`
level proved outright. -/
theorem modeOfReturn_of_sol (hH1 : StressInvH1Solenoidal) (hEq : WeakDmuToPeriodicModeEq) :
    Wiring.ModeOfReturn := by
  intro D dm dp hst n hact hP1 z hz hne hp hμ0 hμ1 T' b _hT0 _hDT hb hT hb0 a Q
  obtain ⟨hbS, hS_inv, hM_ex, hweak⟩ := mode_weakDmu_and_mult hne hp hb hT
  have hH1_b : IsH1Periodic (2 * (D.level n).ε * cOf (D.level n).ν) (modeBstar (D.level n) b) := by
    rw [hbS]
    exact modeBstar_isH1Periodic hH1 D dm dp hst n hact hP1 z hz hne hp hμ0 hμ1 hS_inv (-T')
  refine ⟨modeCore (D.level n) (D.mu n z) b, rfl, ?_⟩
  exact ⟨hμ0, hμ1, hH1_b, modeBstar_nonzero (D.level n) hb0,
    hEq D dm dp hst n hact z hz hne hp hμ0 hμ1
      (concreteBase D.Pl D.K (D.level n) (D.mu n z) hne) hM_ex b hH1_b hweak,
    modeBstar_symmetric (D.level n) b⟩

/-- **Conditional proof of `Wiring.ModeOfReturn`** from `StressInvH1Grad` and
`WeakDmuToPeriodicModeEq` (with slice solenoidality proved outright via `modeBstar_solenoidal`). -/
theorem modeOfReturn_of (hGrad : StressInvH1Grad) (hEq : WeakDmuToPeriodicModeEq) :
    Wiring.ModeOfReturn :=
  modeOfReturn_of_sol (stressInvH1Solenoidal_of_grad hGrad) hEq

theorem modeOfReturn_of_grad (hGrad : StressInvH1Grad) (hEq : WeakDmuToPeriodicModeEq) :
    Wiring.ModeOfReturn :=
  modeOfReturn_of hGrad hEq

end UnforcedLeray.Short.PartIIIb.Concrete
end
