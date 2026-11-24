import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `sepBoxMeasurable` (`PartIII-b:C/near/masked/18/3/4/2/1/3`)

Source 3611-3621.  The integrand `sepPhi ν μ (UnforcedLeray.Short.PartIIIb.NearInst.cartLift R c m) τ i · y` is a product of the constant
`-2`, the power `l^{2μ+2}`, the derivative of the heat-Leray kernel at `y - l z` (joint measurability
from `HeatLerayJointMeas` after the parabolic time change `t = ν(1-l²)`), and the measurable
Cartesian lift entry `UnforcedLeray.Short.PartIIIb.NearInst.cartLift R c m (τ + 2 log l) z` (`T8_1.measurable_cartLift_entry`).
The kernel factor is measurable on `(0,1) × Space` only (`t > 0`), which is all `sepRho` sees.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open MeasureTheory Set Filter UnforcedLeray.Axi UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.PartIIIb.Concrete

lemma sepBox_deriv_aesm (ν : ℝ) (hν : 0 < ν) (y : Space) (i j k : Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × Space =>
      ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y - p.1 • p.2)
        (coordinateVector k) : ℝ) : ℂ)) sepRho := by
  have hJ : HeatLerayJointMeas :=
    heatLerayJointMeas_of (heatLerayScale_of heatGTailScale) heatLerayKSmooth
  have hg : Measurable fun p : ℝ × Space => (ν * (1 - p.1 ^ 2), y - p.1 • p.2) := by
    fun_prop
  have hsm := (hJ i j 1 (by norm_num)).comp_measurable hg
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Space) ℝ
    (fun _ => coordinateVector k)).continuous.comp_stronglyMeasurable hsm
  have hc := Complex.ofRealCLM.continuous.comp_stronglyMeasurable hev
  refine hc.aestronglyMeasurable.congr ?_
  filter_upwards [ae_mem_Ioo_sepRho] with p hp
  obtain ⟨h0, h1⟩ := hp
  have hpos : 0 < ν * (1 - p.1 ^ 2) := mul_pos hν (by nlinarith)
  simp [hpos, iteratedFDeriv_one_apply]

lemma sepBox_cart_real (R c τ : ℝ) (m : UnforcedLeray.Short.PartIIIb.Concrete.Chart →
    UnforcedLeray.Short.PartIIIb.Concrete.Ten3) (hm : Measurable m) (j k : Fin 3) :
    Measurable fun p : ℝ × Space =>
      UnforcedLeray.Short.PartIIIb.NearInst.cartLift R c m (τ + 2 * Real.log p.1) p.2 j k := by
  have hh : Measurable (fun p : ℝ × Space => (τ + 2 * Real.log p.1, p.2)) :=
    ((measurable_const.add (measurable_const.mul (Real.measurable_log.comp measurable_fst))).prodMk
      measurable_snd)
  have h3 : Measurable (fun s : ℝ × Space =>
      UnforcedLeray.Short.PartIIIb.NearInst.cartLift R c m s.1 s.2 j k) :=
    T8_1.measurable_cartLift_entry R c m hm j k
  have h4 := h3.comp hh
  exact h4

lemma sepBox_cart_meas (R c τ : ℝ) (m : UnforcedLeray.Short.PartIIIb.Concrete.Chart →
    UnforcedLeray.Short.PartIIIb.Concrete.Ten3) (hm : Measurable m) (j k : Fin 3) :
    Measurable fun p : ℝ × Space =>
      ((UnforcedLeray.Short.PartIIIb.NearInst.cartLift R c m (τ + 2 * Real.log p.1) p.2 j k : ℝ)
        : ℂ) := by
  have h4 := sepBox_cart_real R c τ m hm j k
  have h5 := Complex.measurable_ofReal.comp h4
  exact h5

theorem sepBoxMeasurable :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SepBoxMeasurable := by
  intro ν R c μ hν _hR _hc m hm τ y i
  have hmeas : Measurable m := hm.measurable
  have hpow : AEStronglyMeasurable (fun p : ℝ × Space => ((p.1 : ℝ) : ℂ) ^ (2 * (μ : ℂ) + 2))
      sepRho :=
    ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).aestronglyMeasurable
  have hsum : AEStronglyMeasurable (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y - p.1 • p.2)
        (coordinateVector k) : ℝ) : ℂ) *
        ((UnforcedLeray.Short.PartIIIb.NearInst.cartLift R c m (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ)) sepRho := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun j _ =>
      Finset.aestronglyMeasurable_fun_sum _ (fun k _ => ?_))
    exact (sepBox_deriv_aesm ν hν y i j k).mul
      (sepBox_cart_meas R c τ m hmeas j k).aestronglyMeasurable
  unfold sepPhi
  exact (aestronglyMeasurable_const.mul hpow).mul hsum

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
