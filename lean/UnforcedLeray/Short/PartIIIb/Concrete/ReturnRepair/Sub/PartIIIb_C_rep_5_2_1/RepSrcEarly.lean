import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.PhasePointwiseEarly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.VelPhysL2Early
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RbFacts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.VelSliceMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.HolderPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.PeriodSmall
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# Proof of `RepSrcEarly` (`PartIII-b:C/rep/5/2/1/11`, source 5169-5176 with 5318-5319)

Mirror of `repairSource_of` (`Sub/PartIII-b_C_rep_1.lean`) for the early repair source
`(1-χ_o)M_{r_b}w`: the leaves `repPhasePointwiseEarly` (task /9) and `velPhysL2Early` (task /10)
replace `repPhasePointwise` and `velPhysL2`. The velocity slices of `𝒩_v((1-χ_o)w)` are the slices
of `𝒩_v w` multiplied by the measurable real factor `1 - χ_o(ν·age)`. The constant is
`C = 2·C₀·C₁` and the power is `k = k₀` (no gauge factor: the early gain is `e^{3γ/(5ν)}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

/-- The early velocity in physical form at a space-time point:
`𝒩_v((1-χ_o)w)(τ,y) = (1-χ_o(ν·age)) 𝒩_v w(τ,y)`. -/
theorem velPhys_earlyVel_pt (K : ReturnConsts) (L : ReturnLevel) (c : ℝ) (w : Chart → Merid)
    (τ : ℝ) (y : Space) :
    velPhys L.ε⁻¹ c (earlyVel K L w) (τ, y) =
      (((1 - K.χo (L.ν * (NearInst.chartOf L.ε⁻¹ c y τ).1) : ℝ)) : ℂ) •
        velPhys L.ε⁻¹ c w (τ, y) := by
  unfold velPhys
  rw [pe_Nv_earlyVel K L c w τ y, wda_realC_smul]

/-- The chart age `s = R²/ϱ²` as a function of the spatial variable, measurable. -/
theorem earlyAge_measurable (R c τ : ℝ) :
    Measurable (fun y : Space => (NearInst.chartOf R c y τ).1) := by
  have h : (fun y : Space => (NearInst.chartOf R c y τ).1) = fun y => R ^ 2 / NearInst.hRad y ^ 2 := by
    funext y
    rfl
  rw [h]
  have hrad : Measurable (fun y : Space => NearInst.hRad y) := by
    unfold NearInst.hRad
    fun_prop
  exact measurable_const.div (hrad.pow_const 2)

/-- The early cut factor `1 - χ_o(ν·age)` as a complex function of the spatial variable. -/
theorem earlyCut_measurable (K : ReturnConsts) (L : ReturnLevel) (c τ : ℝ) :
    Measurable (fun y : Space =>
      (((1 - K.χo (L.ν * (NearInst.chartOf L.ε⁻¹ c y τ).1) : ℝ)) : ℂ)) := by
  have hchart := earlyAge_measurable L.ε⁻¹ c τ
  have hr : Measurable (fun y : Space => (1 : ℝ) - K.χo (L.ν * (NearInst.chartOf L.ε⁻¹ c y τ).1)) :=
    measurable_const.sub (K.hχo.smooth.continuous.measurable.comp (measurable_const.mul hchart))
  exact Complex.measurable_ofReal.comp hr

/-- **Phase slices of the early velocity**: the slices of `𝒩_v((1-χ_o)w)` are a.e.-strongly
measurable for a.e. phase in the cell (`velSliceMeas` times the measurable factor
`1 - χ_o(ν·age)`, with `age = R²/ϱ²` measurable by `T8_1.measurable_chartOf`). -/
theorem earlySliceMeas (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (w : LVel Pl L) :
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * L.ε * cOf L.ν))),
      AEStronglyMeasurable
        (fun y : Space => velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (τ, y))
        volume := by
  filter_upwards [velSliceMeas Pl L w] with τ hτ
  have hcut := earlyCut_measurable K L (cOf L.ν) τ
  have hfun : (fun y : Space =>
        velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (τ, y)) =
      fun y : Space =>
        (((1 - K.χo (L.ν * (NearInst.chartOf L.ε⁻¹ (cOf L.ν) y τ).1) : ℝ)) : ℂ) •
          velPhys L.ε⁻¹ (cOf L.ν) (w : Chart → Merid) (τ, y) :=
    funext fun y => velPhys_earlyVel_pt K L (cOf L.ν) (w : Chart → Merid) τ y
  rw [hfun]
  exact hcut.aestronglyMeasurable.smul hτ

/-- **Per-level early repair source** (5169-5176 with 5318-5319): the leaves `RbFacts`,
`RepPhasePointwiseEarly`, `HolderPhase`, `VelPhysL2Early` (with constant `C₁`) give the bound
with constant `2·C₀·C₁`, power `k₀`, and gain `e^{3γ/(5ν)}`. -/
theorem repSrcEarly_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (S μ : ℝ)
    (hC0 : 0 < K.C0) (hP : 2 * L.ε * cOf L.ν ≤ 1)
    (hsplit : UnforcedLeray.Short.IIb.ExactSplitII (L.params Pl) (L.ρb Pl K) S L.V L.rb)
    (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (hRb : RbFacts) (hpt : RepPhasePointwiseEarly) (hH : HolderPhase)
    (C1 : ℝ) (hC1 : 0 ≤ C1)
    (hV : ∀ w : LVel Pl L,
      ENNReal.ofReal (2 * L.ε * cOf L.ν)⁻¹ *
        ∫⁻ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), ∫⁻ y : Space,
          ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (t, y)‖ ^ 2 ≤
        ENNReal.ofReal ((C1 * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖) ^ 2)) :
    RepSrcEarlyAt Pl K L (2 * K.C0 * C1) K.k0 := by
  intro w
  obtain ⟨hax, hper, hrbm⟩ := hRb Pl K L S hsplit hP
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hρeq := rhoB_eq Pl K L
  have hrho : 0 ≤ rhoRep K L := by unfold rhoRep; positivity
  have hρb : 0 ≤ L.ρb Pl K := by rw [hρeq]; positivity
  set P := 2 * L.ε * cOf L.ν with hPdef
  set X : ℝ := C1 * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖ with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  -- per-phase bound
  have hphase : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)),
      (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w) (τ, y))) ^ (22 / 19 : ℝ)) ^
          (2 / (22 / 19 : ℝ)) ≤
        (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          ∫⁻ y : Space, ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν)
            (earlyVel K L (w : Chart → Merid)) (τ, y)‖ ^ 2 := by
    filter_upwards [hpt Pl K L μ hC0 hnear hs hax hper w, earlySliceMeas Pl K L w] with τ h1 h2
    refine le_trans (hH (L.rb τ)
      (fun y => velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (τ, y)) _
      (hrbm τ) h2 h1) ?_
    have he : eLpNorm (L.rb τ) (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤
        ENNReal.ofReal (L.ρb Pl K) :=
      le_trans le_self_add (hsplit.energy τ)
    rw [mul_assoc, mul_assoc]
    gcongr
  have hint : (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w) (t, y))) ^ (22 / 19 : ℝ)) ^
          (2 / (22 / 19 : ℝ))) ≤
      (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
        ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (t, y)‖ ^ 2 := by
    rw [← lintegral_const_mul']
    · exact lintegral_mono_ae hphase
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hfin : ENNReal.ofReal P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w) (t, y))) ^ (22 / 19 : ℝ)) ^
          (2 / (22 / 19 : ℝ))) ≤
      ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2) := by
    calc _ ≤ ENNReal.ofReal P⁻¹ * ((ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (t, y)‖ ^ 2) := by
          gcongr
      _ = (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (t, y)‖ ^ 2) := by
          ring
      _ ≤ (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) * ENNReal.ofReal (X ^ 2) := by
          gcongr; exact hV w
      _ = ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2) := by
          rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow hρb,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  -- take the square root
  have hroot : (ENNReal.ofReal P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w) (t, y))) ^ (22 / 19 : ℝ)) ^
          (2 / (22 / 19 : ℝ)))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * L.ρb Pl K * X) := by
    calc _ ≤ (ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hfin (by norm_num)
      _ = ENNReal.ofReal (2 * L.ρb Pl K * X) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_sq (by positivity)
  refine le_trans hroot (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hρeq, hX]
  ring

/-- **`RepSrcEarly`** (`PartIII-b:C/rep/5/2/1/11`, source 5169-5176 with 5318-5319): the early
repair source bound along the sequence, from the leaves `rbFacts`, `repPhasePointwiseEarly`,
`holderPhase`, `velPhysL2Early` and `periodSmall`. -/
theorem repSrcEarly (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.RepSrcEarly := by
  obtain ⟨C1, hC1, hV⟩ := velPhysL2Early
  refine ⟨2 * D.K.C0 * C1, D.K.k0, ?_⟩
  filter_upwards [periodSmall D hst, hst.actual, hst.pins, hst.near] with n h2 h3 h4 h5
  have h4' := h4 0 ⟨by norm_num, by norm_num⟩
  exact repSrcEarly_level D.Pl D.K (D.level n) (D.Sin n) (D.mu n 0) hst.C0_pos h2
    h3.split (h5 0 ⟨by norm_num, by norm_num⟩) h4'.split rbFacts repPhasePointwiseEarly
    holderPhase C1 hC1 (fun w => hV D.Pl hst.gamma_pos.le D.K (D.level n) w)

end UnforcedLeray.Short.PartIIIb.Concrete
