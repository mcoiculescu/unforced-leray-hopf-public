import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1.Route
import UnforcedLeray.Short.PartIIb.Sub.TrainCloseCell
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.Regular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.DriftC2.VcBound

/-!
# Part II-b, task `PartII-b:T22/2/3/1/3` (`TrainCylCoeff`): the train velocity is a `CylCoeff` drift

Source: `the November 2 reference manuscript` lines 2085-2093 (`TrainClose` at
orders `0, 1`).  For `0 < c` (not only `1 ≤ c`), `CylCoeff c (Σ/ν) tr.v` has six fields:

* slices `C¹`, joint continuity of `v` and of `fderiv`: `tcRegular` (`ClassicalExists/TrainCoeff`);
* periodicity: `IsTrain.periodic_v`;
* boundedness: `‖v - V_c‖ ≤ δ` (`TrainClose.norm_sub_le`) and `‖V_c‖ ≤ M0` (`Vc_iter_bound`, order 0);
* bounded derivative: `‖D(v - V_c)‖ ≤ δ` (`TrainClose.norm_fderiv_sub_le`), `V_c` differentiable
  (`vcRegularity_proof`, `C³`) with `‖DV_c‖ ≤ M1` (`Vc_iter_bound`, order 1).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

/-- **Leaf `T22/2/3/1/3`** (SP 2085-2093): for every `c > 0` the train velocity is a `CylCoeff`
drift on `[0, Σ/ν]`. -/
theorem trainCylCoeff : UnforcedLeray.Short.IIb.BwdRoute.TrainCylCoeff := by
  intro Sg ν c δ hSg hν hc _hδ tr htr
  have hT : (0 : ℝ) ≤ Sg / ν := div_nonneg hSg.le hν.le
  obtain ⟨hs, hc0, hd0⟩ := UnforcedLeray.Short.IIb.CylPDE.tcRegular ν c tr (Sg / ν) hT
  obtain ⟨M0, hM0⟩ := UnforcedLeray.Short.IIb.Vc_iter_bound ν c Sg hν hc hSg.le 0
  obtain ⟨M1, hM1⟩ := UnforcedLeray.Short.IIb.Vc_iter_bound ν c Sg hν hc hSg.le 1
  have hνs : ∀ σ ∈ Icc (0 : ℝ) (Sg / ν), ν * σ ≤ Sg := fun σ hσ => by
    rw [mul_comm]
    exact (le_div_iff₀ hν).1 hσ.2
  refine ⟨hs, hc0, hd0, ?_, ⟨δ + M0, ?_⟩, ⟨δ + M1, ?_⟩⟩
  · intro σ hσ x
    exact tr.isTrain.periodic_v σ hσ.1 x
  · intro σ hσ x
    have h1 := UnforcedLeray.Short.IIb.TrainClose.norm_sub_le hc htr hσ.1 hσ.2 x
    have h2 := hM0 σ hσ.1 (hνs σ hσ) x
    rw [norm_iteratedFDeriv_zero] at h2
    calc ‖tr.v σ x‖ = ‖(tr.v σ x - UnforcedLeray.Train.Vc ν c σ x) +
          UnforcedLeray.Train.Vc ν c σ x‖ := by rw [sub_add_cancel]
      _ ≤ ‖tr.v σ x - UnforcedLeray.Train.Vc ν c σ x‖ + ‖UnforcedLeray.Train.Vc ν c σ x‖ :=
          norm_add_le _ _
      _ ≤ δ + M0 := add_le_add h1 h2
  · intro σ hσ x
    have hσ0 : (0 : ℝ) ≤ σ := hσ.1
    have hv : Differentiable ℝ (tr.v σ) := (hs σ hσ).differentiable one_ne_zero
    have hVc : Differentiable ℝ (UnforcedLeray.Train.Vc ν c σ) :=
      ((UnforcedLeray.Short.Spine.vcRegularity_proof).1 ν c σ hν hc hσ0).differentiable
        (by norm_num)
    have heq : fderiv ℝ (tr.v σ) x =
        fderiv ℝ (fun z => tr.v σ z - UnforcedLeray.Train.Vc ν c σ z) x +
          fderiv ℝ (UnforcedLeray.Train.Vc ν c σ) x := by
      rw [show (fun z => tr.v σ z - UnforcedLeray.Train.Vc ν c σ z) =
          tr.v σ - UnforcedLeray.Train.Vc ν c σ from rfl, fderiv_sub (hv x) (hVc x)]
      abel
    have h2 := hM1 σ hσ0 (hνs σ hσ) x
    rw [norm_iteratedFDeriv_one] at h2
    rw [heq]
    exact (norm_add_le _ _).trans
      (add_le_add (UnforcedLeray.Short.IIb.TrainClose.norm_fderiv_sub_le hc htr hσ0 hσ.2 x) h2)
