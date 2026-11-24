import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.EMeas

/-!
# `PartIII-b:C/ward/9/4`: measurability of the young chart reading of `Y = D_{μ+1}X`

Source `the November 2 reference manuscript` 4171-4186, 4202-4216, 2683-2689.

`Y` is jointly measurable off the axis (difference quotients, `WardXDiff`), the chart point
`q = (s, (q, η))` with `s > 0` has an off-axis receiver `chartY R q` and the prefactor `s^{-1/2}`
vanishes for `s ≤ 0`, so the reading equals the reading of the off-axis version of `Y`, which is
a measurable function of the chart point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open WardEMeasAux

private theorem l4_chartTau_meas (R : ℝ) : Measurable fun p : Chart => NearInst.chartTau R p := by
  unfold NearInst.chartTau
  exact (((measurable_fst.comp measurable_snd).const_mul 2).div_const R).add
    (Real.measurable_log.comp measurable_fst)

private theorem l4_chartY_meas (R : ℝ) : Measurable fun p : Chart => NearInst.chartY R p := by
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  unfold NearInst.chartY
  exact T8_4.t84_vec3 (a := fun p : Chart => R / Real.sqrt p.1) (b := fun _ => (0 : ℝ))
    (c := fun p : Chart => p.2.2 / Real.sqrt p.1)
    (measurable_const.div hsq) measurable_const
    ((measurable_snd.comp measurable_snd).div hsq)

private theorem l4_wardY_offaxis_meas {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) {g : Chart → Ten3}
    (hg : IsOldL2 c ν g) :
    Measurable fun x : ℝ × Space => wemOff (wardY ν μ R c χy g) x.1 x.2 := by
  have hO : IsOpen axisᶜ := isClosed_axis.isOpen_compl
  set X := wardX ν μ R c χy g with hXdef
  have hD := fun τ => wardXDiff_proved ν μ R c χy hχy hν hR hc hμ g hg τ
  have hC3 : ∀ τ, ContDiffOn ℝ 3 (X τ) axisᶜ := fun τ => (hD τ).1
  have hXm : Measurable fun x : ℝ × Space => X x.1 x.2 := T8_4.t84_ward_stream hχy hg.measurable
  have dX : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (X τ) y := fun τ y hy =>
    WardCalc.diffAt_of_contDiffOn hO (hC3 τ) hy
  have dpX : ∀ l : Fin 3, ∀ τ y, y ∉ axis →
      DifferentiableAt ℝ ((fun τ y => physPd (X τ) l y) τ) y := fun l τ y hy =>
    WardCalc.differentiableAt_physPd hO (hC3 τ) hy l
  have mX : Measurable fun x : ℝ × Space => wemOff X x.1 x.2 := wem_off_meas hXm
  have mpX : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (X τ) j y) x.1 x.2 := fun j => wem_meas_pd mX dX j
  have mp2X : ∀ j l : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 := fun j l =>
    wem_meas_pd (F := fun τ y => physPd (X τ) l y) (mpX l) (dpX l) j
  have mdt : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => deriv (fun t => X t y) τ) x.1 x.2 :=
    wem_meas_deriv_tau hXm fun τ y hy => (hD τ).2.1 y hy
  have mfy : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => fderiv ℝ (X τ) y y) x.1 x.2 :=
    wem_meas_fderiv_apply (V := fun _ y => y) mX measurable_snd dX
  have heq : (fun x : ℝ × Space => wemOff (wardY ν μ R c χy g) x.1 x.2) = fun x =>
      wemOff (fun τ y => deriv (fun t => X t y) τ) x.1 x.2 -
        (1 / 2 : ℝ) • wemOff (fun τ y => fderiv ℝ (X τ) y y) x.1 x.2 -
        ν • ∑ j : Fin 3, wemOff (fun τ y => physPd2 (X τ) j j y) x.1 x.2 +
        (μ + 1 - 1 / 2) • wemOff X x.1 x.2 := by
    funext x
    by_cases hx : x.2 ∈ axis
    · simp [wemOff, hx]
    · simp only [wem_off_of_not_mem hx, hXdef, wardY, physDmu, physLap]
  rw [heq]
  exact ((mdt.sub (mfy.const_smul (1 / 2 : ℝ))).sub
    ((Finset.measurable_sum _ fun j _ => mp2X j j).const_smul ν)).add
    (mX.const_smul (μ + 1 - 1 / 2))

theorem wardYYoungMeas_proved : WardYYoungMeas := by
  intro ν μ R c χy hχy hν hR hc hμ g hg
  have mY := l4_wardY_offaxis_meas hχy hν hR hc hμ hg
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hFm : Measurable fun p : Chart =>
      ‖wemOff (wardY ν μ R c χy g) (NearInst.chartTau R p) (NearInst.chartY R p)‖ :=
    (mY.comp ((l4_chartTau_meas R).prodMk (l4_chartY_meas R))).norm
  have hyoung : MeasurableSet (wardYoungSet ν) := by
    unfold wardYoungSet
    exact measurableSet_le (measurable_fst.const_mul ν) measurable_const
  have heq : wardYoungRead ν R (wardY ν μ R c χy g) =
      wardYoungRead ν R (wemOff (wardY ν μ R c χy g)) := by
    funext q
    unfold wardYoungRead
    by_cases hp : 0 < q.1
    · have hy : NearInst.chartY R q ∉ axis := by
        intro h
        have h' : NearInst.chartY R q 0 = 0 ∧ NearInst.chartY R q 1 = 0 := h
        have h1 : NearInst.chartY R q 0 = R / Real.sqrt q.1 := by
          simp [NearInst.chartY]
        have hne : R / Real.sqrt q.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hp).ne'
        exact hne (h1 ▸ h'.1)
      by_cases hm : q ∈ wardYoungSet ν
      · rw [indicator_of_mem hm, indicator_of_mem hm, wem_off_of_not_mem hy]
      · rw [indicator_of_notMem hm, indicator_of_notMem hm]
    · have hs : Real.sqrt q.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
      by_cases hm : q ∈ wardYoungSet ν
      · rw [indicator_of_mem hm, indicator_of_mem hm, hs, inv_zero, zero_mul, zero_mul]
      · rw [indicator_of_notMem hm, indicator_of_notMem hm]
  rw [heq]
  unfold wardYoungRead
  exact ((measurable_inv.comp hsq).mul hFm |>.indicator hyoung).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
