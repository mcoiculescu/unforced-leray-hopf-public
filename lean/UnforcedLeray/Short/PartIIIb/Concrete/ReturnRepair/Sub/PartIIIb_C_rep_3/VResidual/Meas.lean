import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.EMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.OldNorm
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L8
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1

/-!
# Measurability and periodicity helpers for `VResidualOf` (`PartIII-b:C/rep/3/2`)

Splits `wardEXY` into `vrDiv` (`2V·∇Y`), `vrJetV` (`-2νC_diff + (V⊗V):D²X`), and `vrJetP`
(`-(DX+DXᵀ)∇p_V`), proves `IsOldL2` for `repSrcTen`, and establishes the measurability of the chart
coefficients and the phase measurability/periodicity of `τ ↦ ‖fderiv ℝ (repY … τ) y‖` off the axis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Blueprint.Planar (PlanarData)
open WardEMeasAux

/-! ## 1. The three pieces of `wardEXY` -/

/-- The transport term `2V·∇Y` of `wardEXY`. -/
def vrDiv (V Y : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  (2 : ℝ) • fderiv ℝ (Y τ) y (V τ y)

/-- The `V`-jet terms `-2νC_diff(V, X) + (V⊗V):D²X` of `wardEXY`. -/
def vrJetV (ν : ℝ) (V X : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  -((2 * ν) • physCdiff (V τ) (X τ) y) + physUUD2 (V τ) (X τ) y

/-- The pressure-jet term `-(DX + DXᵀ)∇p_V` of `wardEXY`. -/
def vrJetP (X : ℝ → Space → Space) (pV : ℝ → Space → ℝ) (τ : ℝ) (y : Space) : Space :=
  -physDXp (X τ) (pV τ) y

theorem wardEXY_eq_vr_sum (ν μ R : ℝ) (V : ℝ → SpatialField) (pV : ℝ → Space → ℝ)
    (X Y : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    wardEXY ν μ R V pV X Y τ y =
      vrDiv V Y τ y + (vrJetV ν V X τ y + vrJetP X pV τ y) := by
  unfold wardEXY vrDiv vrJetV vrJetP
  abel

theorem coefOf_wardEXY_eq_vr_sum (ν μ R : ℝ) (V : ℝ → SpatialField) (pV : ℝ → Space → ℝ)
    (X Y : ℝ → Space → Space) :
    coefOf R (wardEXY ν μ R V pV X Y) =
      coefOf R (vrDiv V Y) + (coefOf R (vrJetV ν V X) + coefOf R (vrJetP X pV)) := by
  rw [← wo_coefOf_add, ← wo_coefOf_add]
  congr 1
  funext τ y
  exact wardEXY_eq_vr_sum ν μ R V pV X Y τ y

/-! ## 2. `repSrcTen` is old `L²` data -/

theorem vr_rhoB_pos (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) :
    0 < L.ρb Pl K :=
  mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos (L.params Pl).ν_pos _))) (Real.exp_pos _))
    (Real.rpow_pos_of_pos (L.params Pl).ε_pos _)

theorem vr_isOldL2_repSrcTen (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (w : LVel Pl L) :
    IsOldL2 (cOf L.ν) L.ν (repSrcTen Pl K L w) := by
  have hρ : 0 < L.ρb Pl K := vr_rhoB_pos Pl K L hC0
  have hν : 0 < L.ν := L.ν_pos
  set S := chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (multOp Pl K L w)
  have hmeas : Measurable (repSrcTen Pl K L w) :=
    (Lp.stronglyMeasurable S.snd).measurable
  obtain ⟨κ, hκ, hκle⟩ := gainMeasureLower (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρ hmZ hν
  have ha0 : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.2 hκ).ne'
  have hat : ENNReal.ofReal κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle2 : ENNReal.ofReal κ • ageμ (cOf L.ν) (-1 / 2) ≤
      gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν :=
    wo_smul_le_of_lintegral fun f hf => (hκle f hf).2
  have hb_ne_top : (ENNReal.ofReal κ ^ (1 / (2 : ℝ≥0∞)).toReal)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hat).ne'
  have hlt : eLpNorm (repSrcTen Pl K L w) 2 (ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    lt_of_le_of_lt (wo_eLpNorm_le_of_smul_le ha0 hat hle2 (S.snd : Chart → Ten3))
      (ENNReal.mul_lt_top hb_ne_top.lt_top (Lp.eLpNorm_lt_top S.snd))
  refine ⟨hmeas, ⟨hmeas.aestronglyMeasurable, hlt⟩, ?_⟩
  obtain ⟨_, a2⟩ := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo
    (multOp Pl K L w)
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at a2
  filter_upwards [a2] with p e2 hp
  have h0 : cutFun K.χo L.ν p = 0 := K.hχo.zero _ hp
  simp only [repSrcTen, e2, h0, zero_smul]

/-! ## 3. Phase periodicity of `wardY` -/

theorem vr_wardY_periodic (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) :
    wardY ν μ R c χy g (τ + 2 * c / R) = wardY ν μ R c χy g τ := by
  have hZ : ∀ t, wardX0 ν μ R c g (t + 2 * c / R) = wardX0 ν μ R c g t :=
    fun t => funext (wardX0_periodic oldPhysPeriodic ν μ R c g t)
  have hX : ∀ t, wardX ν μ R c χy g (t + 2 * c / R) = wardX ν μ R c χy g t := by
    intro t
    funext y
    simp only [wardX, wardStreamCut, outPrim, hZ t]
  funext y
  have hd : deriv (fun t => wardX ν μ R c χy g t y) (τ + 2 * c / R) =
      deriv (fun t => wardX ν μ R c χy g t y) τ := by
    rw [← deriv_comp_add_const]
    congr 1
    funext t
    rw [hX t]
  simp only [wardY, physDmu, hd, hX τ]

/-! ## 4. Off-axis measurability of `L.V`, `vrDiv`, `vrJetV`, `vrJetP`, and `τ ↦ ‖DY(τ, y)‖` -/

theorem vr_offAxis_eq : {x : ℝ × Space | 0 < ϱ x.2} = {x : ℝ × Space | x.2 ∉ axis} := by
  ext x
  exact ⟨fun h hx => h.ne' ((mem_axis_iff x.2).1 hx), ϱ_pos⟩

theorem vr_wemOff_V_meas {V : ℝ → SpatialField}
    (hV : ContDiffOn ℝ 2 (fun x : ℝ × Space => V x.1 x.2) {x | 0 < ϱ x.2}) :
    Measurable fun x : ℝ × Space => wemOff V x.1 x.2 := by
  have hcl : IsClosed {x : ℝ × Space | x.2 ∈ axis} := isClosed_axis.preimage continuous_snd
  have hV' : ContDiffOn ℝ 2 (fun x : ℝ × Space => V x.1 x.2) {x : ℝ × Space | x.2 ∉ axis} := by
    rwa [← vr_offAxis_eq]
  have hcont : ContinuousOn (fun x : ℝ × Space => wemOff V x.1 x.2)
      {x : ℝ × Space | x.2 ∉ axis} :=
    hV'.continuousOn.congr fun x hx => wem_off_of_not_mem hx
  have heq : (fun x : ℝ × Space => wemOff V x.1 x.2) =
      {x : ℝ × Space | x.2 ∈ axis}.piecewise (fun _ => (0 : Space))
        (fun x : ℝ × Space => wemOff V x.1 x.2) := by
    funext x
    by_cases hx : x.2 ∈ axis <;> simp [Set.piecewise, wemOff, hx]
  rw [heq]
  exact ContinuousOn.measurable_piecewise continuousOn_const hcont hcl.measurableSet

theorem vr_slice_V {V : ℝ → SpatialField}
    (hV : ContDiffOn ℝ 2 (fun x : ℝ × Space => V x.1 x.2) {x | 0 < ϱ x.2})
    (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    DifferentiableAt ℝ (V τ) y ∧
      ∀ l : Fin 3, DifferentiableAt ℝ ((fun t z => physPd (V t) l z) τ) y := by
  have hopen : IsOpen {x : ℝ × Space | 0 < ϱ x.2} :=
    isOpen_lt continuous_const (continuous_ϱ.comp continuous_snd)
  have hat : ContDiffAt ℝ 2 (fun x : ℝ × Space => V x.1 x.2) (τ, y) :=
    hV.contDiffAt (hopen.mem_nhds (ϱ_pos hy))
  have hsl : ContDiffAt ℝ 2 (V τ) y :=
    hat.comp y (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨hsl.differentiableAt (by norm_num), fun l => ?_⟩
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (V τ)) y := hsl.fderiv_right (m := 1) (by norm_num)
  exact (h1.clm_apply contDiffAt_const).differentiableAt (by norm_num)

theorem vr_meas_pieces {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    {pV : ℝ → Space → ℝ} (hχy : IsYoungCutoff K.χy) (hμ : -(1 / 4) < μ)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ)
    (hV : ContDiffOn ℝ 2 (fun x : ℝ × Space => L.V x.1 x.2) {x | 0 < ϱ x.2})
    (hpV : ContDiff ℝ 1 (fun x : ℝ × Space => pV x.1 x.2)) (w : LVel Pl L) :
    Measurable (coefOf L.ε⁻¹ (vrDiv L.V (repY Pl K L μ w))) ∧
      AEStronglyMeasurable (coefOf L.ε⁻¹ (vrJetV L.ν L.V (repX Pl K L μ w)))
        (srcMeasure (cOf L.ν)) ∧
      AEStronglyMeasurable (coefOf L.ε⁻¹ (vrJetP (repX Pl K L μ w) pV))
        (srcMeasure (cOf L.ν)) ∧
      (∀ y : Space, y ∉ axis → Measurable fun τ : ℝ => ‖fderiv ℝ (repY Pl K L μ w τ) y‖) := by
  have hO : IsOpen axisᶜ := isClosed_axis.isOpen_compl
  have hν : 0 < L.ν := L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hg : IsOldL2 (cOf L.ν) L.ν (repSrcTen Pl K L w) :=
    vr_isOldL2_repSrcTen Pl K L hC0 hmZ w
  set X := repX Pl K L μ w with hXdef
  set Y := repY Pl K L μ w with hYdef
  have hD := fun τ =>
    wardXDiff_proved L.ν μ L.ε⁻¹ (cOf L.ν) K.χy hχy hν hR hc hμ (repSrcTen Pl K L w) hg τ
  have hC3 : ∀ τ, ContDiffOn ℝ 3 (X τ) axisᶜ := fun τ => (hD τ).1
  have hXm : Measurable fun x : ℝ × Space => X x.1 x.2 :=
    T8_4.t84_ward_stream hχy hg.measurable
  have dX : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (X τ) y := fun τ y hy =>
    WardCalc.diffAt_of_contDiffOn hO (hC3 τ) hy
  have dpX : ∀ l : Fin 3, ∀ τ y, y ∉ axis →
      DifferentiableAt ℝ ((fun τ y => physPd (X τ) l y) τ) y := fun l τ y hy =>
    WardCalc.differentiableAt_physPd hO (hC3 τ) hy l
  have dY : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (Y τ) y := by
    intro τ y hy
    have hcd : ContDiffAt ℝ 3 (X τ) y := (hC3 τ).contDiffAt (hO.mem_nhds hy)
    have d1 : DifferentiableAt ℝ (fun y' => deriv (fun t => X t y') τ) y :=
      ((hD τ).2.2).differentiableAt (hO.mem_nhds hy)
    have d2 : DifferentiableAt ℝ (fun y' => fderiv ℝ (X τ) y' y') y :=
      ((hcd.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).clm_apply
        differentiableAt_id
    have d3 : DifferentiableAt ℝ (fun y' => physLap (X τ) y') y := by
      unfold physLap
      exact DifferentiableAt.fun_sum fun j _ =>
        WardCalc.differentiableAt_physPd2 hO (hC3 τ) hy j j
    have d4 : DifferentiableAt ℝ (X τ) y := dX τ y hy
    have hfun : Y τ = fun y' => deriv (fun t => X t y') τ - (1 / 2 : ℝ) • fderiv ℝ (X τ) y' y' -
        L.ν • physLap (X τ) y' + (μ + 1 - 1 / 2) • X τ y' := by
      funext y'
      simp only [hYdef, hXdef, repY, repX, wardY, physDmu]
    rw [hfun]
    exact ((d1.sub (d2.const_smul (1 / 2 : ℝ))).sub (d3.const_smul L.ν)).add
      (d4.const_smul (μ + 1 - 1 / 2))
  have mX : Measurable fun x : ℝ × Space => wemOff X x.1 x.2 := wem_off_meas hXm
  have mpX : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (X τ) j y) x.1 x.2 := fun j => wem_meas_pd mX dX j
  have mp2X : ∀ j l : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 := fun j l =>
    wem_meas_pd (F := fun τ y => physPd (X τ) l y) (mpX l) (dpX l) j
  have mV : Measurable fun x : ℝ × Space => wemOff L.V x.1 x.2 := vr_wemOff_V_meas hV
  have dV : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (L.V τ) y :=
    fun τ y hy => (vr_slice_V hV τ hy).1
  have dpV : ∀ l : Fin 3, ∀ τ y, y ∉ axis →
      DifferentiableAt ℝ ((fun τ y => physPd (L.V τ) l y) τ) y :=
    fun l τ y hy => (vr_slice_V hV τ hy).2 l
  have mpV : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (L.V τ) j y) x.1 x.2 := fun j => wem_meas_pd mV dV j
  have mp2V : ∀ j l : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd2 (L.V τ) j l y) x.1 x.2 := fun j l =>
    wem_meas_pd (F := fun τ y => physPd (L.V τ) l y) (mpV l) (dpV l) j
  have hpm : Measurable fun x : ℝ × Space => pV x.1 x.2 := hpV.continuous.measurable
  have dp : ∀ τ y, DifferentiableAt ℝ (pV τ) y := fun τ y =>
    (hpV.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) y
  have mdp : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      fderiv ℝ (pV x.1) x.2 (coordinateVector j) := fun j =>
    wem_meas_fderiv_scalar hpm dp _
  have mdt : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => deriv (fun t => X t y) τ) x.1 x.2 :=
    wem_meas_deriv_tau hXm fun τ y hy => (hD τ).2.1 y hy
  have mfy : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => fderiv ℝ (X τ) y y) x.1 x.2 :=
    wem_meas_fderiv_apply (V := fun _ y => y) mX measurable_snd dX
  have mY : Measurable fun x : ℝ × Space => wemOff Y x.1 x.2 := by
    have heq : (fun x : ℝ × Space => wemOff Y x.1 x.2) = fun x =>
        wemOff (fun τ y => deriv (fun t => X t y) τ) x.1 x.2 -
          (1 / 2 : ℝ) • wemOff (fun τ y => fderiv ℝ (X τ) y y) x.1 x.2 -
          L.ν • ∑ j : Fin 3, wemOff (fun τ y => physPd2 (X τ) j j y) x.1 x.2 +
          (μ + 1 - 1 / 2) • wemOff X x.1 x.2 := by
      funext x
      by_cases hx : x.2 ∈ axis
      · simp [wemOff, hx]
      · simp only [wem_off_of_not_mem hx, hYdef, hXdef, repY, repX, wardY, physDmu, physLap]
    rw [heq]
    exact ((mdt.sub (mfy.const_smul (1 / 2 : ℝ))).sub
      ((Finset.measurable_sum _ fun j _ => mp2X j j).const_smul L.ν)).add
      (mX.const_smul (μ + 1 - 1 / 2))
  have mpY : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (Y τ) j y) x.1 x.2 := fun j => wem_meas_pd mY dY j
  have mDYV : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => fderiv ℝ (Y τ) y (L.V τ y)) x.1 x.2 := by
    have h1 := wem_meas_fderiv_apply mY mV dY
    have heq : (fun x : ℝ × Space => wemOff (fun τ y => fderiv ℝ (Y τ) y (L.V τ y)) x.1 x.2) =
        fun x : ℝ × Space =>
          wemOff (fun τ y => fderiv ℝ (Y τ) y (wemOff L.V τ y)) x.1 x.2 := by
      funext x
      by_cases hx : x.2 ∈ axis <;> simp [wemOff, hx]
    rwa [heq]
  have hcoord : ∀ l : Fin 3, Measurable fun v : Space => v l := T8_4.t84_coord
  have mDiv : Measurable fun x : ℝ × Space => wemOff (vrDiv L.V Y) x.1 x.2 := by
    have heq : (fun x : ℝ × Space => wemOff (vrDiv L.V Y) x.1 x.2) =
        fun x => (2 : ℝ) • wemOff (fun τ y => fderiv ℝ (Y τ) y (L.V τ y)) x.1 x.2 := by
      funext x
      by_cases hx : x.2 ∈ axis <;> simp [wemOff, vrDiv, hx]
    rw [heq]
    exact mDYV.const_smul (2 : ℝ)
  have mJetV : Measurable fun x : ℝ × Space => wemOff (vrJetV L.ν L.V X) x.1 x.2 := by
    have heq : (fun x : ℝ × Space => wemOff (vrJetV L.ν L.V X) x.1 x.2) = fun x =>
        if x.2 ∈ axis then (0 : Space) else
          -((2 * L.ν) • (∑ j : Fin 3, ∑ l : Fin 3,
            ((wemOff (fun τ y => physPd (L.V τ) j y) x.1 x.2) l •
                wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 -
              (wemOff (fun τ y => physPd (X τ) j y) x.1 x.2) l •
                wemOff (fun τ y => physPd2 (L.V τ) j l y) x.1 x.2))) +
          (∑ j : Fin 3, ∑ l : Fin 3,
            (wemOff L.V x.1 x.2 j * wemOff L.V x.1 x.2 l) •
              wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2) := by
      funext x
      by_cases hx : x.2 ∈ axis
      · simp only [wemOff, hx, ↓reduceIte]
      · simp only [hx, ↓reduceIte, wem_off_of_not_mem hx]
        rfl
    rw [heq]
    refine Measurable.ite wem_axis_meas measurable_const ?_
    have m2 : Measurable fun x : ℝ × Space => ∑ j : Fin 3, ∑ l : Fin 3,
        ((wemOff (fun τ y => physPd (L.V τ) j y) x.1 x.2) l •
            wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 -
          (wemOff (fun τ y => physPd (X τ) j y) x.1 x.2) l •
            wemOff (fun τ y => physPd2 (L.V τ) j l y) x.1 x.2) :=
      Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ =>
        (((hcoord l).comp (mpV j)).smul (mp2X j l)).sub
          (((hcoord l).comp (mpX j)).smul (mp2V j l))
    have m3 : Measurable fun x : ℝ × Space => ∑ j : Fin 3, ∑ l : Fin 3,
        (wemOff L.V x.1 x.2 j * wemOff L.V x.1 x.2 l) •
          wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 :=
      Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ =>
        (((hcoord j).comp mV).mul ((hcoord l).comp mV)).smul (mp2X j l)
    exact (m2.const_smul (2 * L.ν)).neg.add m3
  have mJetP : Measurable fun x : ℝ × Space => wemOff (vrJetP X pV) x.1 x.2 := by
    have heq : (fun x : ℝ × Space => wemOff (vrJetP X pV) x.1 x.2) = fun x =>
        if x.2 ∈ axis then (0 : Space) else
          -(WithLp.toLp 2 (fun i => ∑ j : Fin 3,
            ((wemOff (fun τ y => physPd (X τ) j y) x.1 x.2) i +
              (wemOff (fun τ y => physPd (X τ) i y) x.1 x.2) j) *
              fderiv ℝ (pV x.1) x.2 (coordinateVector j))) := by
      funext x
      by_cases hx : x.2 ∈ axis
      · simp only [wemOff, hx, ↓reduceIte]
      · simp only [hx, ↓reduceIte, wem_off_of_not_mem hx]
        rfl
    rw [heq]
    refine Measurable.ite wem_axis_meas measurable_const ?_
    have m4 : Measurable fun x : ℝ × Space =>
        (WithLp.toLp 2 (fun i => ∑ j : Fin 3,
          ((wemOff (fun τ y => physPd (X τ) j y) x.1 x.2) i +
            (wemOff (fun τ y => physPd (X τ) i y) x.1 x.2) j) *
            fderiv ℝ (pV x.1) x.2 (coordinateVector j)) : Space) := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
      refine measurable_pi_iff.2 fun i => ?_
      exact Finset.measurable_sum _ fun j _ =>
        (((hcoord i).comp (mpX j)).add ((hcoord j).comp (mpX i))).mul (mdp j)
    exact m4.neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coefOf_eq_off hR]
    exact coefOf_meas mDiv
  · rw [coefOf_eq_off hR]
    exact (coefOf_meas mJetV).aestronglyMeasurable
  · rw [coefOf_eq_off hR]
    exact (coefOf_meas mJetP).aestronglyMeasurable
  · intro y hy
    have heq : (fun τ : ℝ => fderiv ℝ (Y τ) y) =
        fun τ : ℝ => jet1 fun j => wemOff (fun t z => physPd (Y t) j z) τ y := by
      funext τ
      conv_lhs => rw [eq_jet1 (fderiv ℝ (Y τ) y)]
      congr 1
      funext j
      exact (wem_off_of_not_mem (F := fun t z => physPd (Y t) j z) hy).symm
    have hm : Measurable fun τ : ℝ => fderiv ℝ (Y τ) y := by
      rw [heq]
      refine continuous_jet1.measurable.comp (measurable_pi_iff.2 fun j => ?_)
      exact (mpY j).comp (measurable_id.prodMk measurable_const)
    exact hm.norm

end UnforcedLeray.Short.PartIIIb.Concrete
