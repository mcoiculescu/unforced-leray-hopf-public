import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.EMeas

/-!
# `PartIII-b:C/ward/9/3/4`: measurability of the young reading of `transField`

Source `the November 2 reference manuscript` 4196-4216.  On the young region
`ϱ > 0`, `Y = χ_yW_μ + transField` (`wardY_split`, from `ward:shifted-resolvent`), so
`transField = Y - χ_yW_μ` there; `Y` is measurable off the axis (as in `WardYYoungMeas`) and
`χ_yW_μ` is measurable (`sepW` jointly measurable).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open WardEMeasAux

namespace WardS4

theorem chartTau_meas (R : ℝ) : Measurable fun p : Chart => NearInst.chartTau R p := by
  unfold NearInst.chartTau
  exact (((measurable_fst.comp measurable_snd).const_mul 2).div_const R).add
    (Real.measurable_log.comp measurable_fst)

theorem chartY_meas (R : ℝ) : Measurable fun p : Chart => NearInst.chartY R p := by
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  unfold NearInst.chartY
  exact T8_4.t84_vec3 (a := fun p : Chart => R / Real.sqrt p.1) (b := fun _ => (0 : ℝ))
    (c := fun p : Chart => p.2.2 / Real.sqrt p.1)
    (measurable_const.div hsq) measurable_const
    ((measurable_snd.comp measurable_snd).div hsq)

theorem wardY_offaxis_meas {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
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

theorem wardW_meas (ν μ R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable fun p : ℝ × Space => wardW ν μ R c g p.1 p.2 := by
  have hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => oldPhys R c g s.1 s.2 j k :=
    fun j k => T8_1.measurable_oldPhys_entry R c g hg j k
  have h1 : ∀ i : Fin 3, Measurable fun q : ℝ × Space =>
      IIIa.sepW ν (μ : ℂ) (oldPhys R c g) q.2 q.1 i :=
    fun i => T8_1.measurable_sepW_comp ν (μ : ℂ) (oldPhys R c g) i hT
  have hcomp : ∀ i : Fin 3, Measurable fun q : ℝ × Space =>
      (IIIa.sepW ν (μ : ℂ) (oldPhys R c g) q.2 q.1 i).re :=
    fun i => Complex.measurable_re.comp (h1 i)
  unfold wardW
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp (measurable_pi_iff.2 hcomp)

end WardS4

/-- **Sub 4** (measurability of the young reading of `transField`). -/
theorem wardYTransMeasG_proved : WardYTransMeasG := by
  intro ν μ R c χy hχy hν hR hc hμ g hg
  have hres := wardYShiftedRes_proved ν μ R c g hν hR hc hμ hg
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  have mY := WardS4.wardY_offaxis_meas hχy hν hR hc hμ hg
  have mW := WardS4.wardW_meas ν μ R c g hg.measurable
  have hχm : Measurable fun x : ℝ × Space => χy (ν * age R x.2) := by
    have h1 : Measurable fun x : ℝ × Space => ν * age R x.2 := by
      unfold age
      have hϱ : Measurable fun x : ℝ × Space => ϱ x.2 :=
        continuous_ϱ.measurable.comp measurable_snd
      exact measurable_const.mul (measurable_const.div (hϱ.pow_const 2))
    exact hχy.smooth.continuous.measurable.comp h1
  have mYW : Measurable fun x : ℝ × Space => wardYoungW ν μ R c χy g x.1 x.2 := by
    have : (fun x : ℝ × Space => wardYoungW ν μ R c χy g x.1 x.2) =
        fun x => χy (ν * age R x.2) • wardW ν μ R c g x.1 x.2 := rfl
    rw [this]
    exact hχm.smul mW
  have mD : Measurable fun x : ℝ × Space =>
      wemOff (wardY ν μ R c χy g) x.1 x.2 - wardYoungW ν μ R c χy g x.1 x.2 := mY.sub mYW
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hyoung : MeasurableSet (wardYoungSet ν) := by
    unfold wardYoungSet
    exact measurableSet_le (measurable_fst.const_mul ν) measurable_const
  have hFm : Measurable fun p : Chart =>
      ‖wemOff (wardY ν μ R c χy g) (NearInst.chartTau R p) (NearInst.chartY R p) -
        wardYoungW ν μ R c χy g (NearInst.chartTau R p) (NearInst.chartY R p)‖ :=
    (mD.comp ((WardS4.chartTau_meas R).prodMk (WardS4.chartY_meas R))).norm
  have heq : wardYoungRead ν R (transField ν μ R c χy g) = fun q =>
      (wardYoungSet ν).indicator (fun q => (Real.sqrt q.1)⁻¹ *
        ‖wemOff (wardY ν μ R c χy g) (NearInst.chartTau R q) (NearInst.chartY R q) -
          wardYoungW ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q)‖) q := by
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
      have hy0 : 0 < ϱ (NearInst.chartY R q) := by
        rw [ϱ_chartY hR hp]; positivity
      have hsplit := wardY_split hχ hν.le hres (NearInst.chartTau R q) hy0
      have hT : transField ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) =
          wardY ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) -
            wardYoungW ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) := by
        rw [hsplit]; abel
      by_cases hm : q ∈ wardYoungSet ν
      · rw [indicator_of_mem hm, indicator_of_mem hm, hT, wem_off_of_not_mem hy]
      · rw [indicator_of_notMem hm, indicator_of_notMem hm]
    · have hs : Real.sqrt q.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
      by_cases hm : q ∈ wardYoungSet ν
      · rw [indicator_of_mem hm, indicator_of_mem hm, hs, inv_zero, zero_mul, zero_mul]
      · rw [indicator_of_notMem hm, indicator_of_notMem hm]
  rw [heq]
  exact (((measurable_inv.comp hsq).mul hFm).indicator hyoung).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete

end
