import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YHAdd.Calc
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_4

/-!
# Measurability of the coefficient of `Ẽ_μ` (`PartIII-b:C/ward/8`; source 4271-4280, 4139-4141,
4171-4186)

Source of record: `the November 2 reference manuscript` (73 pages).

`Ẽ_μ = 2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX + DXᵀ)∇p` (4276-4280) reads, off the axis, `X`, its
first and second partials, `Y = D_{μ+1}X` and its first partials (through `DY(y)U(y)`), and `U`,
`∂U`, `∂²U`, `∇p`.  The chart coefficient reads its field only off the axis (`coefOf_eq_off`), so
it suffices that the off-axis version (value `0` on the axis) is jointly measurable.

* `X` is jointly measurable (`T8_4.t84_ward_stream`, from `wardX0_measurable_of_measurable`);
* a spatial partial of a jointly measurable field that is differentiable off the axis is jointly
  measurable off the axis (difference quotients, `measurable_fderiv_apply_offaxis`, `wem_meas_pd`);
  iterated for `∂²X` (`X(τ, ·)` is `C³` off the axis, `WardXDiff` item 1), for `Y` the phase
  derivative is the limit of the phase difference quotients (`WardXDiff` item 2,
  `wem_meas_deriv_tau`), and `Y(τ, ·)` is differentiable off the axis (`WardXDiff` items 1, 3);
* `U`, `p` are smooth (`IsExactProfile`, 4139-4141).

`wardEMeas_of : WardXDiff → WardEMeas`; `WardXDiff` is the target of `PartIII-b:C/ward/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace WardEMeasAux

/-- The off-axis version of a field: its value off the axis, `0` on the axis. -/
def wemOff (F : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  if y ∈ axis then 0 else F τ y

theorem wem_off_of_not_mem {F : ℝ → Space → Space} {τ : ℝ} {y : Space} (hy : y ∉ axis) :
    wemOff F τ y = F τ y := if_neg hy

theorem wem_off_ev {F : ℝ → Space → Space} {τ : ℝ} {y : Space} (hy : y ∉ axis) :
    wemOff F τ =ᶠ[𝓝 y] F τ := by
  filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
  exact if_neg hz

theorem wem_axis_meas : MeasurableSet {x : ℝ × Space | x.2 ∈ axis} :=
  isClosed_axis.measurableSet.preimage measurable_snd

theorem wem_off_meas {F : ℝ → Space → Space} (hF : Measurable fun x : ℝ × Space => F x.1 x.2) :
    Measurable fun x : ℝ × Space => wemOff F x.1 x.2 :=
  Measurable.ite wem_axis_meas measurable_const hF

/-- A spatial partial of a field that is jointly measurable off the axis and differentiable off the
axis is jointly measurable off the axis. -/
theorem wem_meas_pd {F : ℝ → Space → Space}
    (hF : Measurable fun x : ℝ × Space => wemOff F x.1 x.2)
    (hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (F τ) y) (j : Fin 3) :
    Measurable fun x : ℝ × Space => wemOff (fun τ y => physPd (F τ) j y) x.1 x.2 := by
  have hd' : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (wemOff F τ) y := fun τ y hy =>
    (hd τ y hy).congr_of_eventuallyEq (wem_off_ev hy)
  have h := measurable_fderiv_apply_offaxis (F := wemOff F)
    (V := fun _ _ => coordinateVector j) hF measurable_const hd'
  have heq : (fun x : ℝ × Space => wemOff (fun τ y => physPd (F τ) j y) x.1 x.2) =
      fun x : ℝ × Space => if x.2 ∈ axis then (0 : Space)
        else fderiv ℝ (wemOff F x.1) x.2 (coordinateVector j) := by
    funext x
    by_cases hx : x.2 ∈ axis
    · simp only [wemOff, if_pos hx]
    · rw [wem_off_of_not_mem hx, if_neg hx, (wem_off_ev hx).fderiv_eq]
      rfl
  rw [heq]
  exact h

/-- The directional derivative `Df(y)V(y)` off the axis, for a field differentiable off the axis
and jointly measurable off the axis. -/
theorem wem_meas_fderiv_apply {F V : ℝ → Space → Space}
    (hF : Measurable fun x : ℝ × Space => wemOff F x.1 x.2)
    (hV : Measurable fun x : ℝ × Space => V x.1 x.2)
    (hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (F τ) y) :
    Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => fderiv ℝ (F τ) y (V τ y)) x.1 x.2 := by
  have hd' : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (wemOff F τ) y := fun τ y hy =>
    (hd τ y hy).congr_of_eventuallyEq (wem_off_ev hy)
  have h := measurable_fderiv_apply_offaxis (F := wemOff F) (V := V) hF hV hd'
  have heq : (fun x : ℝ × Space => wemOff (fun τ y => fderiv ℝ (F τ) y (V τ y)) x.1 x.2) =
      fun x : ℝ × Space => if x.2 ∈ axis then (0 : Space)
        else fderiv ℝ (wemOff F x.1) x.2 (V x.1 x.2) := by
    funext x
    by_cases hx : x.2 ∈ axis
    · simp only [wemOff, if_pos hx]
    · rw [wem_off_of_not_mem hx, if_neg hx, (wem_off_ev hx).fderiv_eq]
  rw [heq]
  exact h

/-- The phase derivative off the axis is jointly measurable (limit of the phase difference
quotients). -/
theorem wem_meas_deriv_tau {F : ℝ → Space → Space}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2)
    (hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (fun t => F t y) τ) :
    Measurable fun p : ℝ × Space => wemOff (fun τ y => deriv (fun t => F t y) τ) p.1 p.2 := by
  have hq : ∀ n : ℕ, Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : Space)
      else ((n : ℝ) + 1) • (F (p.1 + ((n : ℝ) + 1)⁻¹) p.2 - F p.1 p.2) := by
    intro n
    have hA : Measurable fun p : ℝ × Space => F (p.1 + ((n : ℝ) + 1)⁻¹) p.2 :=
      hF.comp ((measurable_fst.add_const _).prodMk measurable_snd)
    exact Measurable.ite wem_axis_meas measurable_const ((hA.sub hF).const_smul (((n : ℝ) + 1)))
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
  refine measurable_of_tendsto_metrizable hq ?_
  rw [tendsto_pi_nhds]
  intro p
  by_cases hp : p.2 ∈ axis
  · simp only [wemOff, if_pos hp]
    exact tendsto_const_nhds
  · simp only [wemOff, if_neg hp]
    have h := (hd p.1 p.2 hp).hasDerivAt.hasFDerivAt.lim (1 : ℝ) hc
    simpa using h

/-- The partial derivative of a scalar field differentiable everywhere is jointly measurable. -/
theorem wem_meas_fderiv_scalar {q : ℝ → Space → ℝ}
    (hq : Measurable fun x : ℝ × Space => q x.1 x.2) (hd : ∀ τ y, DifferentiableAt ℝ (q τ) y)
    (v : Space) : Measurable fun x : ℝ × Space => fderiv ℝ (q x.1) x.2 v := by
  have hqn : ∀ n : ℕ, Measurable fun x : ℝ × Space =>
      ((n : ℝ) + 1) • (q x.1 (x.2 + ((n : ℝ) + 1)⁻¹ • v) - q x.1 x.2) := by
    intro n
    have hA : Measurable fun x : ℝ × Space => q x.1 (x.2 + ((n : ℝ) + 1)⁻¹ • v) :=
      hq.comp (measurable_fst.prodMk (measurable_snd.add_const _))
    exact (hA.sub hq).const_smul ((n : ℝ) + 1)
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
  refine measurable_of_tendsto_metrizable hqn ?_
  rw [tendsto_pi_nhds]
  intro x
  exact (hd x.1 x.2).hasFDerivAt.lim (c := fun n : ℕ => (n : ℝ) + 1) v hc

/-- The chart coefficient reads its field only off the axis. -/
theorem coefOf_eq_off {R : ℝ} (hR : 0 < R) (F : ℝ → Space → Space) :
    coefOf R F = coefOf R (wemOff F) := by
  funext p
  by_cases hp : 0 < p.1
  · have hy : NearInst.chartY R p ∉ axis := by
      intro h
      have h' : NearInst.chartY R p 0 = 0 ∧ NearInst.chartY R p 1 = 0 := h
      have h1 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by
        simp [NearInst.chartY]
      have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hp).ne'
      exact hne (h1 ▸ h'.1)
    unfold coefOf
    rw [wem_off_of_not_mem hy]
  · have hs : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
    simp [coefOf, hs]

/-- The chart coefficient of a jointly measurable field is measurable. -/
theorem coefOf_meas {R : ℝ} {F : ℝ → Space → Space}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2) : Measurable (coefOf R F) := by
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hτ : Measurable fun p : Chart => NearInst.chartTau R p := by
    unfold NearInst.chartTau
    exact (((measurable_fst.comp measurable_snd).const_mul 2).div_const R).add
      (Real.measurable_log.comp measurable_fst)
  have hY : Measurable fun p : Chart => NearInst.chartY R p := by
    unfold NearInst.chartY
    exact T8_4.t84_vec3 (a := fun p : Chart => R / Real.sqrt p.1) (b := fun _ => (0 : ℝ))
      (c := fun p : Chart => p.2.2 / Real.sqrt p.1)
      (measurable_const.div hsq) measurable_const
      ((measurable_snd.comp measurable_snd).div hsq)
  have hFmP : Measurable fun p : Chart => F (NearInst.chartTau R p) (NearInst.chartY R p) :=
    hF.comp (hτ.prodMk hY)
  have h0 := (T8_4.t84_coord 0).comp hFmP
  have h2 := (T8_4.t84_coord 2).comp hFmP
  have hv := T8_4.t84_vec2 h0 h2
  unfold coefOf
  exact (measurable_inv.comp hsq).smul hv

end WardEMeasAux

open WardEMeasAux in
/-- **`WardEMeas` from the off-axis regularity of `X`** (source 4271-4280, 4139-4141,
4171-4186). -/
theorem wardEMeas_of (hdiff : WardXDiff) : WardEMeas := by
  intro ν μ R c P χy U p hχy hν hR hc hμ hU g hg
  have hO : IsOpen axisᶜ := isClosed_axis.isOpen_compl
  set X := wardX ν μ R c χy g with hXdef
  set Y := wardY ν μ R c χy g with hYdef
  have hD := fun τ => hdiff ν μ R c χy hχy hν hR hc hμ g hg τ
  have hC3 : ∀ τ, ContDiffOn ℝ 3 (X τ) axisᶜ := fun τ => (hD τ).1
  have hXm : Measurable fun x : ℝ × Space => X x.1 x.2 := T8_4.t84_ward_stream hχy hg.measurable
  -- differentiability off the axis
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
        ν • physLap (X τ) y' + (μ + 1 - 1 / 2) • X τ y' := by
      funext y'
      simp only [hYdef, hXdef, wardY, physDmu]
    rw [hfun]
    exact ((d1.sub (d2.const_smul (1 / 2 : ℝ))).sub (d3.const_smul ν)).add
      (d4.const_smul (μ + 1 - 1 / 2))
  -- the background
  have hUs : ∀ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U τ) := fun τ =>
    hU.smoothU.comp (contDiff_const.prodMk contDiff_id)
  have hps : ∀ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (p τ) := fun τ =>
    hU.smoothP.comp (contDiff_const.prodMk contDiff_id)
  have hUm : Measurable fun x : ℝ × Space => U x.1 x.2 := hU.smoothU.continuous.measurable
  have hpm : Measurable fun x : ℝ × Space => p x.1 x.2 := hU.smoothP.continuous.measurable
  have dU : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (U τ) y := fun τ y _ =>
    (hUs τ).differentiable (by simp) y
  have dpU : ∀ l : Fin 3, ∀ τ y, y ∉ axis →
      DifferentiableAt ℝ ((fun τ y => physPd (U τ) l y) τ) y := by
    intro l τ y _
    have h1 : ContDiff ℝ 1 (fderiv ℝ (U τ)) :=
      (hUs τ).fderiv_right (m := 1) (by exact WithTop.coe_le_coe.2 le_top)
    exact (h1.differentiable (by norm_num) y).clm_apply (differentiableAt_const _)
  have dp : ∀ τ y, DifferentiableAt ℝ (p τ) y := fun τ y => (hps τ).differentiable (by simp) y
  -- the measurable pieces (off the axis)
  have mX : Measurable fun x : ℝ × Space => wemOff X x.1 x.2 := wem_off_meas hXm
  have mpX : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (X τ) j y) x.1 x.2 := fun j => wem_meas_pd mX dX j
  have mp2X : ∀ j l : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 := fun j l =>
    wem_meas_pd (F := fun τ y => physPd (X τ) l y) (mpX l) (dpX l) j
  have mU : Measurable fun x : ℝ × Space => wemOff U x.1 x.2 := wem_off_meas hUm
  have mpU : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (U τ) j y) x.1 x.2 := fun j => wem_meas_pd mU dU j
  have mp2U : ∀ j l : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd2 (U τ) j l y) x.1 x.2 := fun j l =>
    wem_meas_pd (F := fun τ y => physPd (U τ) l y) (mpU l) (dpU l) j
  have mdp : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      fderiv ℝ (p x.1) x.2 (coordinateVector j) := fun j =>
    wem_meas_fderiv_scalar hpm dp _
  -- `Y` off the axis
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
          ν • ∑ j : Fin 3, wemOff (fun τ y => physPd2 (X τ) j j y) x.1 x.2 +
          (μ + 1 - 1 / 2) • wemOff X x.1 x.2 := by
      funext x
      by_cases hx : x.2 ∈ axis
      · simp [wemOff, hx]
      · simp only [wem_off_of_not_mem hx, hYdef, hXdef, wardY, physDmu, physLap]
    rw [heq]
    exact ((mdt.sub (mfy.const_smul (1 / 2 : ℝ))).sub
      ((Finset.measurable_sum _ fun j _ => mp2X j j).const_smul ν)).add
      (mX.const_smul (μ + 1 - 1 / 2))
  have mDYU : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => fderiv ℝ (Y τ) y (U τ y)) x.1 x.2 :=
    wem_meas_fderiv_apply mY hUm dY
  -- assembly
  have hcoord : ∀ l : Fin 3, Measurable fun v : Space => v l := T8_4.t84_coord
  have mE : Measurable fun x : ℝ × Space => wemOff (wardE ν μ R c χy U p g) x.1 x.2 := by
    have heq : (fun x : ℝ × Space => wemOff (wardE ν μ R c χy U p g) x.1 x.2) = fun x =>
        if x.2 ∈ axis then (0 : Space) else
          (2 : ℝ) • wemOff (fun τ y => fderiv ℝ (Y τ) y (U τ y)) x.1 x.2 -
            (2 * ν) • (∑ j : Fin 3, ∑ l : Fin 3,
              ((wemOff (fun τ y => physPd (U τ) j y) x.1 x.2) l •
                  wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 -
                (wemOff (fun τ y => physPd (X τ) j y) x.1 x.2) l •
                  wemOff (fun τ y => physPd2 (U τ) j l y) x.1 x.2)) +
            (∑ j : Fin 3, ∑ l : Fin 3, (U x.1 x.2 j * U x.1 x.2 l) •
              wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2) -
            WithLp.toLp 2 (fun i => ∑ j : Fin 3,
              ((wemOff (fun τ y => physPd (X τ) j y) x.1 x.2) i +
                (wemOff (fun τ y => physPd (X τ) i y) x.1 x.2) j) *
                fderiv ℝ (p x.1) x.2 (coordinateVector j)) := by
      funext x
      by_cases hx : x.2 ∈ axis
      · simp only [wemOff, if_pos hx]
      · simp only [if_neg hx, wem_off_of_not_mem hx]
        rfl
    rw [heq]
    refine Measurable.ite wem_axis_meas measurable_const ?_
    have m1 := mDYU.const_smul (2 : ℝ)
    have m2 : Measurable fun x : ℝ × Space => ∑ j : Fin 3, ∑ l : Fin 3,
        ((wemOff (fun τ y => physPd (U τ) j y) x.1 x.2) l •
            wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 -
          (wemOff (fun τ y => physPd (X τ) j y) x.1 x.2) l •
            wemOff (fun τ y => physPd2 (U τ) j l y) x.1 x.2) :=
      Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ =>
        (((hcoord l).comp (mpU j)).smul (mp2X j l)).sub
          (((hcoord l).comp (mpX j)).smul (mp2U j l))
    have m3 : Measurable fun x : ℝ × Space => ∑ j : Fin 3, ∑ l : Fin 3,
        (U x.1 x.2 j * U x.1 x.2 l) • wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 :=
      Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ =>
        (((hcoord j).comp hUm).mul ((hcoord l).comp hUm)).smul (mp2X j l)
    have m4 : Measurable fun x : ℝ × Space =>
        (WithLp.toLp 2 (fun i => ∑ j : Fin 3,
          ((wemOff (fun τ y => physPd (X τ) j y) x.1 x.2) i +
            (wemOff (fun τ y => physPd (X τ) i y) x.1 x.2) j) *
            fderiv ℝ (p x.1) x.2 (coordinateVector j)) : Space) := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
      refine measurable_pi_iff.2 fun i => ?_
      exact Finset.measurable_sum _ fun j _ =>
        (((hcoord i).comp (mpX j)).add ((hcoord j).comp (mpX i))).mul (mdp j)
    exact ((m1.sub (m2.const_smul (2 * ν))).add m3).sub m4
  rw [coefOf_eq_off hR]
  exact (coefOf_meas mE).aestronglyMeasurable

theorem wardEMeas_proved : WardEMeas := wardEMeas_of wardXDiff_proved

end UnforcedLeray.Short.PartIIIb.Concrete
