import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelCovarianceClosure
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelCellNormScale
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelSmoothPeriodicBound
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelTensorDensity
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelTensorDensityValue
import UnforcedLeray.Lib.HeatCylinder.L2Operator
import UnforcedLeray.Lib.SobolevC.CylSmooth
import UnforcedLeray.Lib.TrainB.TensorBridge

/-!
# Actual smooth periodic density in the normalized kernel tensor carrier

This module transports the proved compact-axial smooth density from the centered cylinder cell
to the normalized cell used by the literal heat and heat-divergence CLMs. The `√c` conversion is
kept explicit and only used for each fixed positive period.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.HeatCylinder
open UnforcedLeray.TrainB (TensorVal)

private theorem wμ_zero_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private theorem tensorRep_centered_memLp {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    MemLp (tensorRep hc x) 2 (UnforcedLeray.Cyl.cellμ c) :=
  memLp_cyl_of_memLp_cellMeasure hc (tensorRep_measurable hc x)
    (tensorRep_spec hc x).2.1 (memLp_tensorRep hc x)

/-- Every actual normalized-cell tensor class is the limit of actual normalized-cell classes
represented by bounded continuous periodic images of compact-axial smooth cylinder tensors. This
is the density supplier needed to close the arbitrary-L² covariance theorem. -/
theorem exists_bddContinuous_periodic_kernelTensor_approx {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    ∃ xSeq : ℕ → Lp (Plane × Plane) 2 (cellMeasure c),
    ∃ Tn : ℕ → Plane → Plane × Plane,
    ∃ hn : ∀ n, MemLp (Tn n) 2 (cellMeasure c),
      (∀ n, Continuous (Tn n)) ∧
      (∀ n, ∃ M : ℝ, ∀ z, ‖Tn n z‖ ≤ M) ∧
      (∀ n, IsQPeriodic c (Tn n)) ∧
      (∀ n, xSeq n = (hn n).toLp (Tn n)) ∧
      Tendsto xSeq atTop (𝓝 x) := by
  let T := tensorRep hc x
  let hTC := tensorRep_centered_memLp hc x
  let xC := hTC.toLp T
  let Linv := UnforcedLeray.TrainB.tensorToPlaneCLE.symm.toContinuousLinearMap
  let xTensor := Linv.compLpL 2 (UnforcedLeray.Cyl.cellμ c) xC
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let valueToCell : Lp TensorVal 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) →L[ℝ]
      Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c) :=
    Lp.LpToLpOfMeasureLeSMul (E := TensorVal) (p := (2 : ℝ≥0∞))
      (μ := UnforcedLeray.Cyl.cellμ c)
      (ν := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) (c := (1 : ℝ≥0∞)) (by simp) (by
        rw [wμ_zero_eq_cell c]
        simp)
  obtain ⟨y, u, hu, hy, hlim⟩ :=
    exists_smooth_centeredTensorW0_sequence hc xTensor
  let value (n : ℕ) : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c) := by
    exact valueToCell (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2 (y n))
  let valueLimit : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c) := by
    exact valueToCell (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2
      (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.centeredTensorW0 hc xTensor))
  have hvalueLim : Tendsto value atTop (𝓝 valueLimit) := by
    have h := tendsto_tensorW0_value_of_tendsto hlim
    exact (valueToCell.continuous.tendsto _).comp h
  let L : TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  let LpL := L.compLpL 2 (UnforcedLeray.Cyl.cellμ c)
  let centeredTn (n : ℕ) : Plane → Plane × Plane := fun z => L (u n z)
  let centeredMem (n : ℕ) : MemLp (centeredTn n) 2 (UnforcedLeray.Cyl.cellμ c) := by
    haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    have hU := (hu n).memLp (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (2 : ℝ≥0∞)
    have hU' : MemLp (u n) 2 (UnforcedLeray.Cyl.cellμ c) := by
      simpa only [wμ_zero_eq_cell c] using hU
    exact L.comp_memLp' hU'
  let centeredClass (n : ℕ) := (centeredMem n).toLp (centeredTn n)
  have hcenterClass : ∀ n, LpL (value n) = centeredClass n := by
    intro n
    apply Lp.ext
    have hvalueW : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2 (y n) : Plane → TensorVal) =ᵐ[
          UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))] (u n) := by
      rw [hy n]
      exact UnforcedLeray.Sob.W.value_ofCylSmooth
        (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := TensorVal) (k := 0) (p := 2) hc (u n) (hu n)
    have hcell : (value n : Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c] (u n) := by
      have hcast := Lp.coeFn_LpToLpOfMeasureLeSMul (E := TensorVal) (p := (2 : ℝ≥0∞))
        (μ := UnforcedLeray.Cyl.cellμ c)
        (ν := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) (c := (1 : ℝ≥0∞)) (by simp)
        (by rw [wμ_zero_eq_cell c]; simp)
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2 (y n))
      have hvalueWCell :
          (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2 (y n) :
            Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c] (u n) := by
        simpa only [← wμ_zero_eq_cell c] using hvalueW
      filter_upwards [hcast, hvalueWCell] with z hz₁ hz₂
      exact hz₁.trans hz₂
    have hcomp := L.coeFn_compLpL (value n)
    filter_upwards [hcomp, (centeredMem n).coeFn_toLp, hcell] with z hz1 hz2 hz3
    calc
      (LpL (value n) : Plane → Plane × Plane) z = L ((value n : Plane → TensorVal) z) := hz1
      _ = L (u n z) := congrArg L hz3
      _ = (centeredClass n : Plane → Plane × Plane) z := hz2.symm
  have htarget : LpL valueLimit = xC := by
    apply Lp.ext
    have hcomp := L.coeFn_compLpL valueLimit
    have hval0 := centeredTensorW0_value_ae hc xTensor
    have hval : (valueLimit : Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        (xTensor : Plane → TensorVal) := by
      have hcast := Lp.coeFn_LpToLpOfMeasureLeSMul (E := TensorVal) (p := (2 : ℝ≥0∞))
        (μ := UnforcedLeray.Cyl.cellμ c)
        (ν := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) (c := (1 : ℝ≥0∞)) (by simp)
        (by rw [wμ_zero_eq_cell c]; simp)
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2
          (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.centeredTensorW0 hc xTensor))
      have hvalWCell :
          (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2
            (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.centeredTensorW0 hc xTensor) :
            Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c] (xTensor : Plane → TensorVal) := by
        simpa only [← wμ_zero_eq_cell c] using hval0
      filter_upwards [hcast, hvalWCell] with z hz₁ hz₂
      exact hz₁.trans hz₂
    have hLinv := Linv.coeFn_compLpL xC
    filter_upwards [hcomp, hval, hLinv] with z h1 h2 h3
    calc
      (LpL valueLimit : Plane → Plane × Plane) z = L (valueLimit z) := h1
      _ = L (xTensor z) := congrArg L h2
      _ = xC z := by
        rw [h3]
        simp [L, Linv]
  have hcenterLim : Tendsto centeredClass atTop (𝓝 xC) := by
    have hmap : Tendsto (fun n => LpL (value n)) atTop (𝓝 (LpL valueLimit)) :=
      (LpL.continuous.tendsto valueLimit).comp hvalueLim
    have hmap' := hmap.congr' (Filter.Eventually.of_forall fun n => hcenterClass n)
    simpa [htarget] using hmap'
  let Tn := centeredTn
  let hcenter := centeredMem
  have hcont : ∀ n, Continuous (Tn n) := by
    intro n
    exact L.continuous.comp (hu n).smooth.continuous
  have hbound : ∀ n, ∃ M : ℝ, ∀ z, ‖Tn n z‖ ≤ M := by
    intro n
    rcases exists_bound_of_isCylSmooth hc (hu n) with ⟨M, hM⟩
    refine ⟨M, fun z => ?_⟩
    have hz := hM z
    simpa [Tn, centeredTn, L] using hz
  have hper : ∀ n, IsQPeriodic c (Tn n) := by
    intro n z
    change L (u n (z.1 + c, z.2)) = L (u n z)
    have hz : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hz, (hu n).periodic]
  let hnorm : ∀ n, MemLp (Tn n) 2 (cellMeasure c) := fun n =>
    memLp_cellMeasure_of_memLp_cyl hc (hcont n).measurable (hper n) (hcenter n)
  let xSeq : ℕ → Lp (Plane × Plane) 2 (cellMeasure c) :=
    fun n => (hnorm n).toLp (Tn n)
  have hperiodicTarget : IsQPeriodic c T := (tensorRep_spec hc x).2.1
  have htargetMemNorm : MemLp T 2 (cellMeasure c) := memLp_tensorRep hc x
  have hnormTarget : x = htargetMemNorm.toLp T := by
    apply Lp.ext
    filter_upwards [(tensorRep_spec hc x).2.2,
      htargetMemNorm.coeFn_toLp] with z hz₁ hz₂
    exact hz₁.symm.trans hz₂.symm
  have hxCenter : xC = hTC.toLp T := rfl
  have hnormDiff : Tendsto (fun n => ‖xSeq n - x‖) atTop (𝓝 0) := by
    have hcenterDiff : Tendsto (fun n => ‖centeredClass n - xC‖) atTop (𝓝 0) := by
      exact tendsto_iff_norm_sub_tendsto_zero.mp hcenterLim
    have hscaled : ∀ n, ‖centeredClass n - xC‖ =
        Real.sqrt c * ‖xSeq n - x‖ := by
      intro n
      let f : Plane → Plane × Plane := fun z => Tn n z - T z
      have hfmeas : Measurable f := (hcont n).measurable.sub (tensorRep_measurable hc x)
      have hfper : IsQPeriodic c f := by
        intro z
        change Tn n (z.1 + c, z.2) - T (z.1 + c, z.2) = Tn n z - T z
        rw [hper n z, hperiodicTarget z]
      have hfc : MemLp f 2 (UnforcedLeray.Cyl.cellμ c) :=
        (hcenter n).sub hTC
      have hfn : MemLp f 2 (cellMeasure c) :=
        (hnorm n).sub htargetMemNorm
      have hnormScale := norm_centered_toLp_eq_sqrt_period_mul_normalized
        hc hfmeas hfper hfc hfn
      have hcenterRep : centeredClass n - xC = hfc.toLp f := by
        apply Lp.ext
        have hsub := Lp.coeFn_sub (centeredClass n) xC
        filter_upwards [hsub, (centeredMem n).coeFn_toLp, hTC.coeFn_toLp,
          hfc.coeFn_toLp] with z hsub h1 h2 h3
        have h1' : centeredClass n z = Tn n z := by
          simpa [centeredClass, centeredMem, Tn, centeredTn] using h1
        have h2' : xC z = T z := by simpa [xC] using h2
        calc
          (centeredClass n - xC) z = centeredClass n z - xC z := hsub
          _ = Tn n z - T z := by rw [h1', h2']
          _ = (hfc.toLp f : Lp (Plane × Plane) 2
              (UnforcedLeray.Cyl.cellμ c)) z := h3.symm
      have hnormRep : xSeq n - x = hfn.toLp f := by
        apply Lp.ext
        have hsub := Lp.coeFn_sub (xSeq n) x
        filter_upwards [hsub, (hnorm n).coeFn_toLp, htargetMemNorm.coeFn_toLp,
          hfn.coeFn_toLp] with z hsub h1 h2 h3
        have h1' : xSeq n z = Tn n z := by simpa [xSeq] using h1
        have h2' : x z = T z := by simpa [hnormTarget] using h2
        calc
          (xSeq n - x) z = xSeq n z - x z := hsub
          _ = Tn n z - T z := by rw [h1', h2']
          _ = (hfn.toLp f : Lp (Plane × Plane) 2 (cellMeasure c)) z := h3.symm
      calc
        ‖centeredClass n - xC‖ = ‖hfc.toLp f‖ := by rw [hcenterRep]
        _ = Real.sqrt c * ‖hfn.toLp f‖ := hnormScale
        _ = Real.sqrt c * ‖xSeq n - x‖ := by rw [← hnormRep]
    have hsqrtne : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
    have hscaledNorm : Tendsto (fun n => ‖xSeq n - x‖) atTop (𝓝 0) := by
      have hdiv : ∀ n, ‖xSeq n - x‖ = (Real.sqrt c)⁻¹ *
          ‖centeredClass n - xC‖ := by
        intro n
        rw [hscaled n]
        field_simp
      rw [show (0 : ℝ) = (Real.sqrt c)⁻¹ * 0 by ring]
      exact (tendsto_const_nhds.mul hcenterDiff).congr' (Filter.Eventually.of_forall fun n =>
        (hdiv n).symm)
    exact hscaledNorm
  refine ⟨xSeq, Tn, hnorm, hcont, hbound, hper, ?_, ?_⟩
  · intro n
    rfl
  · exact tendsto_iff_norm_sub_tendsto_zero.mpr hnormDiff

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.exists_bddContinuous_periodic_kernelTensor_approx
