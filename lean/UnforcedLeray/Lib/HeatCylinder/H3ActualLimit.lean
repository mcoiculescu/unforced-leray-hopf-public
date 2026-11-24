import UnforcedLeray.Lib.HeatCylinder.H3Extension
import UnforcedLeray.Lib.HeatCylinder.PeriodicLift
import UnforcedLeray.Lib.HeatCylinder.CellBridge
import UnforcedLeray.Lib.HeatCylinder.VectorL2
import UnforcedLeray.Lib.HeatCylinder.L2Operator
import UnforcedLeray.Lib.SobolevC.Weights

/-!
# Actual L² input represented from the train H³ graph

A Sobolev value on the centered cell is extended periodically, converted to the kernel's plane
coordinates, and transferred to B0284's normalized cell. This is the input class to the actual
Gaussian quotient operator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.TrainB (TensorVal)

private noncomputable def tensorH3ValueRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) : Plane → TensorVal :=
  AEStronglyMeasurable.mk
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x)
    (Lp.aestronglyMeasurable _)

/-- Periodically extend the chosen measurable representative of the centered-cell Sobolev value
and convert the two tensor rows into the kernel's product-plane carrier. -/
noncomputable def tensorH3KernelRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) : Plane → Plane × Plane :=
  fun z => (UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap)
    (centeredPerLift hc (tensorH3ValueRep hc x) z)

theorem measurable_tensorH3KernelRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    Measurable (tensorH3KernelRep hc x) := by
  exact (UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap.continuous.measurable).comp
    (measurable_centeredPerLift hc
      (AEStronglyMeasurable.measurable_mk (Lp.aestronglyMeasurable _)))

theorem periodic_tensorH3KernelRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    UnforcedLeray.B0284.IsQPeriodic c (tensorH3KernelRep hc x) := by
  intro z
  exact congrArg (UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap)
    (centeredPerLift_periodic hc (tensorH3ValueRep hc x) z)

private theorem h3Measure_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private theorem memLp_tensorH3ValueCell {c : ℝ}
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    MemLp
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x : Plane → TensorVal)
      2 (UnforcedLeray.Cyl.cellμ c) := by
  rw [← h3Measure_eq_cell c]
  exact Lp.memLp _

/-- The TensorH3 value viewed on the centered cell measure. -/
noncomputable def tensorH3ValueCellLp {c : ℝ}
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c) :=
  (memLp_tensorH3ValueCell x).toLp
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x)

theorem tensorH3ValueCellLp_coe_ae {c : ℝ}
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    (tensorH3ValueCellLp x : Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x : Plane → TensorVal) :=
  (memLp_tensorH3ValueCell x).coeFn_toLp

private theorem ae_tensorH3ValueRep_cell {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    tensorH3ValueRep hc x =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x : Plane → TensorVal) := by
  let v := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x
  have hv : AEStronglyMeasurable (v : Plane → TensorVal)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := Lp.aestronglyMeasurable v
  have heq := hv.ae_eq_mk
  simpa only [tensorH3ValueRep, v, h3Measure_eq_cell] using heq.symm

theorem memLp_tensorH3KernelRep_centered {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    MemLp (tensorH3KernelRep hc x) 2 (UnforcedLeray.Cyl.cellμ c) := by
  let L : TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  have hqeq : centeredPerLift hc (tensorH3ValueRep hc x) =ᵐ[
      UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x : Plane → TensorVal) := by
    filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c),
      ae_tensorH3ValueRep_cell hc x] with z hzcell hrep
    rw [centeredPerLift_eq_on_cell hc (tensorH3ValueRep hc x) hzcell]
    exact hrep
  have hmemVal : MemLp
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x : Plane → TensorVal)
      2 (UnforcedLeray.Cyl.cellμ c) := by
    simpa only [h3Measure_eq_cell] using
      (Lp.memLp (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x))
  have hmemLift : MemLp (centeredPerLift hc (tensorH3ValueRep hc x))
      2 (UnforcedLeray.Cyl.cellμ c) := (memLp_congr_ae hqeq).mpr hmemVal
  have hmemMap : MemLp (fun z => L (centeredPerLift hc (tensorH3ValueRep hc x) z))
      2 (UnforcedLeray.Cyl.cellμ c) := L.comp_memLp' hmemLift
  change MemLp (fun z => L (centeredPerLift hc (tensorH3ValueRep hc x) z))
    2 (UnforcedLeray.Cyl.cellμ c)
  exact hmemMap

theorem memLp_tensorH3KernelRep_normalized {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    MemLp (tensorH3KernelRep hc x) 2 (UnforcedLeray.B0284.cellMeasure c) := by
  exact memLp_cellMeasure_of_memLp_cyl hc (measurable_tensorH3KernelRep hc x)
    (periodic_tensorH3KernelRep hc x) (memLp_tensorH3KernelRep_centered hc x)


/-- Periodic fields equal on the centered train cell are equal on B0284's normalized cell. -/
theorem ae_eq_of_ae_centered_periodic {c : ℝ} (hc : 0 < c)
    {E : Type*} {f g : Plane → E}
    (hf : UnforcedLeray.B0284.IsQPeriodic c f)
    (hg : UnforcedLeray.B0284.IsQPeriodic c g)
    (hfg : f =ᵐ[UnforcedLeray.Cyl.cellμ c] g) :
    f =ᵐ[UnforcedLeray.B0284.cellMeasure c] g := by
  let S : Set Plane := {z | f z ≠ g z}
  have hSper : UnforcedLeray.B0284.IsQPeriodic c (· ∈ S) := by
    intro z
    change (f (z.1 + c, z.2) ≠ g (z.1 + c, z.2)) = (f z ≠ g z)
    rw [hf z, hg z]
  have hcenter : volume (S ∩ UnforcedLeray.Cyl.cell c) = 0 := by
    have hzero : volume.restrict (UnforcedLeray.Cyl.cell c) S = 0 := by
      have hae := ae_iff.mp hfg
      simpa [S, UnforcedLeray.Cyl.cellμ] using hae
    rw [Measure.restrict_apply' (UnforcedLeray.Cyl.measurableSet_cell c)] at hzero
    simpa [Set.inter_comm] using hzero
  have hglobalNull := (UnforcedLeray.Cyl.isAddFundamentalDomain_cell hc).measure_zero_of_invariant
    S ?_ hcenter
  · have hglobal : f =ᵐ[volume] g := ae_iff.mpr (by simpa [S] using hglobalNull)
    have hnorm := (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hglobal)
    exact ae_iff.mpr (by simpa [S] using hnorm)
  · rintro ⟨v, hv⟩
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have e : (-(⟨m • ((c, 0) : Plane), hv⟩ : AddSubgroup.zmultiples ((c, 0) : Plane)) +ᵥ z :
        Plane) = (z.1 + ((-m : ℤ) : ℝ) * c, z.2) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add]
      ext <;> simp <;> ring
    rw [e]
    exact iff_of_eq (UnforcedLeray.B0289.IsQPeriodic.add_int_mul hSper (-m) z)

/-- The actual normalized-cell tensor class associated with the H³ input value. -/
noncomputable def tensorH3KernelInput {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (memLp_tensorH3KernelRep_normalized hc x).toLp (tensorH3KernelRep hc x)



/-- The normalized input represented from the TensorH3 graph is additive. -/
theorem tensorH3KernelInput_add {c : ℝ} (hc : 0 < c)
    (x y : UnforcedLeray.TrainB.TensorH3 c) :
    tensorH3KernelInput hc (x + y) = tensorH3KernelInput hc x + tensorH3KernelInput hc y := by
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
  let L : TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  have hmap := map_add V x y
  have hadd := Lp.coeFn_add (V x) (V y)
  have haddCell : (↑↑(V x + V y)) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (↑↑(V x) + ↑↑(V y)) := by
    simpa only [h3Measure_eq_cell c] using hadd
  have hcenter : tensorH3KernelRep hc (x + y) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => tensorH3KernelRep hc x z + tensorH3KernelRep hc y z) := by
    filter_upwards [ae_tensorH3ValueRep_cell hc (x + y),
      ae_tensorH3ValueRep_cell hc x, ae_tensorH3ValueRep_cell hc y,
      ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c), haddCell] with z hsum hx hy hz haddz
    change L (centeredPerLift hc (tensorH3ValueRep hc (x + y)) z) =
      L (centeredPerLift hc (tensorH3ValueRep hc x) z) +
        L (centeredPerLift hc (tensorH3ValueRep hc y) z)
    rw [centeredPerLift_eq_on_cell hc _ hz, centeredPerLift_eq_on_cell hc _ hz,
      centeredPerLift_eq_on_cell hc _ hz]
    have hmapz := congrArg (fun u : Lp TensorVal 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => u z) hmap
    have hpoint : tensorH3ValueRep hc (x + y) z =
        tensorH3ValueRep hc x z + tensorH3ValueRep hc y z := by
      calc
        _ = (V (x + y) : Plane → TensorVal) z := hsum
        _ = (V x + V y) z := hmapz
        _ = (V x : Plane → TensorVal) z + (V y : Plane → TensorVal) z := haddz
        _ = _ := by rw [← hx, ← hy]
    rw [← map_add L]
    exact congrArg L hpoint
  have hperiodic : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => tensorH3KernelRep hc x z + tensorH3KernelRep hc y z) := by
    intro z
    change tensorH3KernelRep hc x (z.1 + c, z.2) +
        tensorH3KernelRep hc y (z.1 + c, z.2) = _
    rw [periodic_tensorH3KernelRep hc x z, periodic_tensorH3KernelRep hc y z]
  have hnorm := ae_eq_of_ae_centered_periodic hc
    (periodic_tensorH3KernelRep hc (x + y)) hperiodic hcenter
  have hclasssum :
      (tensorH3KernelInput hc x + tensorH3KernelInput hc y :
        Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c)) =ᵐ[
        UnforcedLeray.B0284.cellMeasure c]
        (fun z => tensorH3KernelRep hc x z + tensorH3KernelRep hc y z) := by
    filter_upwards [Lp.coeFn_add (tensorH3KernelInput hc x) (tensorH3KernelInput hc y),
      (memLp_tensorH3KernelRep_normalized hc x).coeFn_toLp,
      (memLp_tensorH3KernelRep_normalized hc y).coeFn_toLp] with z hsum hx hy
    have hx' : (tensorH3KernelInput hc x : Plane → Plane × Plane) z =
        tensorH3KernelRep hc x z := by simpa [tensorH3KernelInput] using hx
    have hy' : (tensorH3KernelInput hc y : Plane → Plane × Plane) z =
        tensorH3KernelRep hc y z := by simpa [tensorH3KernelInput] using hy
    change (↑(tensorH3KernelInput hc x + tensorH3KernelInput hc y) :
      Plane → Plane × Plane) z = _
    calc
      _ = ((tensorH3KernelInput hc x : Plane → Plane × Plane) +
          (tensorH3KernelInput hc y : Plane → Plane × Plane)) z := hsum
      _ = tensorH3KernelRep hc x z + tensorH3KernelRep hc y z := by
        change (tensorH3KernelInput hc x : Plane → Plane × Plane) z +
          (tensorH3KernelInput hc y : Plane → Plane × Plane) z = _
        rw [hx', hy']
  have hclass : (tensorH3KernelInput hc (x + y) : Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] tensorH3KernelRep hc (x + y) := by
    simpa [tensorH3KernelInput] using
      (memLp_tensorH3KernelRep_normalized hc (x + y)).coeFn_toLp
  apply Lp.ext
  filter_upwards [hclass, hnorm, hclasssum] with z hx hnorm hsum
  exact hx.trans (hnorm.trans hsum.symm)


/-- The normalized input represented from the TensorH3 graph respects real scalar multiplication. -/
theorem tensorH3KernelInput_smul {c : ℝ} (hc : 0 < c)
    (r : ℝ) (x : UnforcedLeray.TrainB.TensorH3 c) :
    tensorH3KernelInput hc (r • x) = r • tensorH3KernelInput hc x := by
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
  let L : TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  have hmap := map_smul V r x
  have hsmul := Lp.coeFn_smul r (V x)
  have hsmulCell : (↑↑(r • V x)) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (r • (V x : Plane → TensorVal)) := by
    simpa only [h3Measure_eq_cell c] using hsmul
  have hcenter : tensorH3KernelRep hc (r • x) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => r • tensorH3KernelRep hc x z) := by
    filter_upwards [ae_tensorH3ValueRep_cell hc (r • x),
      ae_tensorH3ValueRep_cell hc x,
      ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c), hsmulCell] with
      z hsum hx hz hsmulz
    change L (centeredPerLift hc (tensorH3ValueRep hc (r • x)) z) =
      r • L (centeredPerLift hc (tensorH3ValueRep hc x) z)
    rw [centeredPerLift_eq_on_cell hc _ hz, centeredPerLift_eq_on_cell hc _ hz]
    have hmapz := congrArg (fun u : Lp TensorVal 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => u z) hmap
    have hpoint : tensorH3ValueRep hc (r • x) z = r • tensorH3ValueRep hc x z := by
      calc
        _ = (V (r • x) : Plane → TensorVal) z := hsum
        _ = (r • V x) z := hmapz
        _ = r • (V x : Plane → TensorVal) z := hsmulz
        _ = _ := by rw [← hx]
    calc
      L (tensorH3ValueRep hc (r • x) z) = L (r • tensorH3ValueRep hc x z) :=
        congrArg L hpoint
      _ = r • L (tensorH3ValueRep hc x z) := map_smul L r _
  have hperiodic : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => r • tensorH3KernelRep hc x z) := by
    intro z
    change r • tensorH3KernelRep hc x (z.1 + c, z.2) = _
    rw [periodic_tensorH3KernelRep hc x z]
  have hnorm := ae_eq_of_ae_centered_periodic hc
    (periodic_tensorH3KernelRep hc (r • x)) hperiodic hcenter
  have hclass : (tensorH3KernelInput hc (r • x) : Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] tensorH3KernelRep hc (r • x) := by
    simpa [tensorH3KernelInput] using
      (memLp_tensorH3KernelRep_normalized hc (r • x)).coeFn_toLp
  have hclassSmul : (r • tensorH3KernelInput hc x :
      Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c)) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] (fun z => r • tensorH3KernelRep hc x z) := by
    filter_upwards [Lp.coeFn_smul r (tensorH3KernelInput hc x),
      (memLp_tensorH3KernelRep_normalized hc x).coeFn_toLp] with z hsm hx
    have hx' : (tensorH3KernelInput hc x : Plane → Plane × Plane) z =
        tensorH3KernelRep hc x z := by simpa [tensorH3KernelInput] using hx
    calc
      _ = (r • (tensorH3KernelInput hc x : Plane → Plane × Plane)) z := hsm
      _ = r • tensorH3KernelRep hc x z := by
        change r • ((tensorH3KernelInput hc x : Plane → Plane × Plane) z) = _
        rw [hx']
  apply Lp.ext
  filter_upwards [hclass, hnorm, hclassSmul] with z hx hnorm hsm
  exact hx.trans (hnorm.trans hsm.symm)


/-- The actual value-to-kernel-input map is linear on the TensorH3 graph. -/
noncomputable def tensorH3KernelInputLinear {c : ℝ} (hc : 0 < c) :
    UnforcedLeray.TrainB.TensorH3 c →ₗ[ℝ]
      Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) where
  toFun := tensorH3KernelInput hc
  map_add' := tensorH3KernelInput_add hc
  map_smul' := tensorH3KernelInput_smul hc


/-- The squared normalized-cell norm of the represented input is exactly `1/c` times the squared
centered-cell coordinate value norm. -/
theorem norm_sq_tensorH3KernelInput_eq {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ‖tensorH3KernelInput hc x‖ ^ 2 =
      c⁻¹ * ‖((UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap).compLpL 2
        (UnforcedLeray.Cyl.cellμ c)) (tensorH3ValueCellLp x)‖ ^ 2 := by
  let L : TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
  have hcenterRep : tensorH3KernelRep hc x =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => L ((tensorH3ValueCellLp x : Plane → TensorVal) z)) := by
    filter_upwards [ae_tensorH3ValueRep_cell hc x,
      ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c),
      tensorH3ValueCellLp_coe_ae x] with z hrep hz hval
    change L (centeredPerLift hc (tensorH3ValueRep hc x) z) = _
    rw [centeredPerLift_eq_on_cell hc _ hz]
    exact congrArg L (hrep.trans hval.symm)
  have hnormRepN : (eLpNorm (tensorH3KernelRep hc x) 2
      (UnforcedLeray.B0284.cellMeasure c)).toReal =
      ‖tensorH3KernelInput hc x‖ := by
    calc
      _ = (eLpNorm (tensorH3KernelInput hc x : Plane → Plane × Plane) 2
          (UnforcedLeray.B0284.cellMeasure c)).toReal := by
            congr 1
            exact eLpNorm_congr_ae
              (memLp_tensorH3KernelRep_normalized hc x).coeFn_toLp.symm
      _ = ‖tensorH3KernelInput hc x‖ := (Lp.norm_def _).symm
  have hnormRepC : (eLpNorm (tensorH3KernelRep hc x) 2
      (UnforcedLeray.Cyl.cellμ c)).toReal =
      ‖(L.compLpL 2 (UnforcedLeray.Cyl.cellμ c)) (tensorH3ValueCellLp x)‖ := by
    let hm := memLp_tensorH3KernelRep_centered hc x
    let f := hm.toLp (tensorH3KernelRep hc x)
    let Vc : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c) := tensorH3ValueCellLp x
    have hclass : f = (L.compLpL 2 (UnforcedLeray.Cyl.cellμ c)) Vc := by
      apply Lp.ext
      have hcomp := L.coeFn_compLpL Vc
      filter_upwards [hm.coeFn_toLp, hcomp, hcenterRep] with z hf hcpt hrep
      exact hf.trans (hrep.trans hcpt.symm)
    have hae : (f : Plane → Plane × Plane) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        tensorH3KernelRep hc x := hm.coeFn_toLp
    calc
      (eLpNorm (tensorH3KernelRep hc x) 2 (UnforcedLeray.Cyl.cellμ c)).toReal =
          (eLpNorm (f : Plane → Plane × Plane) 2
            (UnforcedLeray.Cyl.cellμ c)).toReal := by
              congr 1
              exact eLpNorm_congr_ae hae.symm
      _ = ‖f‖ := (Lp.norm_def f).symm
      _ = ‖(L.compLpL 2 (UnforcedLeray.Cyl.cellμ c)) (tensorH3ValueCellLp x)‖ := by
        change ‖f‖ = ‖(L.compLpL 2 (UnforcedLeray.Cyl.cellμ c)) Vc‖
        rw [hclass]
  have hsq := eLpNorm_sq_cellMeasure_eq_cyl hc
    (measurable_tensorH3KernelRep hc x) (periodic_tensorH3KernelRep hc x)
  have hreal := congrArg ENNReal.toReal hsq
  have hreal' : (eLpNorm (tensorH3KernelRep hc x) 2
      (UnforcedLeray.B0284.cellMeasure c)).toReal ^ 2 =
      c⁻¹ * (eLpNorm (tensorH3KernelRep hc x) 2
        (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (le_of_lt hc)] at hreal
    exact hreal
  rw [hnormRepN, hnormRepC] at hreal'
  simpa [L] using hreal'


/-- The transported centered-cell TensorH3 value keeps exactly the Sobolev value norm. -/
theorem norm_tensorH3ValueCellLp_eq {c : ℝ}
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ‖tensorH3ValueCellLp x‖ =
      ‖UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  let f : Plane → TensorVal :=
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x : Plane → TensorVal)
  calc
    (eLpNorm (tensorH3ValueCellLp x : Plane → TensorVal) 2
        (UnforcedLeray.Cyl.cellμ c)).toReal = (eLpNorm f 2
          (UnforcedLeray.Cyl.cellμ c)).toReal := by
            congr 1
            exact eLpNorm_congr_ae (tensorH3ValueCellLp_coe_ae x)
    _ = (eLpNorm f 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))).toReal := by
            rw [h3Measure_eq_cell c]
    _ = ‖UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x‖ := rfl

/-- Explicit `c^{-1/2}` continuity of the actual H³-value-to-normalized-L² map. -/
theorem norm_tensorH3KernelInput_le {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ‖tensorH3KernelInput hc x‖ ≤ Real.sqrt (c⁻¹) * ‖x‖ := by
  let L : TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  let C : Lp (Plane × Plane) 2 (UnforcedLeray.Cyl.cellμ c) :=
    (L.compLpL 2 (UnforcedLeray.Cyl.cellμ c)) (tensorH3ValueCellLp x)
  have hC : ‖C‖ ≤ ‖x‖ := by
    have hL : ‖L‖ ≤ 1 := by
      simpa [L] using UnforcedLeray.TrainB.norm_tensorToPlaneCLE_le_one
    calc
      ‖C‖ ≤ ‖L.compLpL 2 (UnforcedLeray.Cyl.cellμ c)‖ *
          ‖tensorH3ValueCellLp x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖L‖ * ‖tensorH3ValueCellLp x‖ := by
          exact mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.norm_compLpL_le L) (norm_nonneg _)
      _ ≤ 1 * ‖x‖ := by
          have hval : ‖tensorH3ValueCellLp x‖ ≤ ‖x‖ := by
            rw [norm_tensorH3ValueCellLp_eq]
            exact UnforcedLeray.Sob.norm_value_le x
          exact mul_le_mul hL hval (norm_nonneg _) (by positivity)
      _ = ‖x‖ := by simp
  have hsq : ‖tensorH3KernelInput hc x‖ ^ 2 ≤
      (Real.sqrt (c⁻¹) * ‖x‖) ^ 2 := by
    rw [norm_sq_tensorH3KernelInput_eq hc x]
    have hnonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc)
    calc
      c⁻¹ * ‖C‖ ^ 2 ≤ c⁻¹ * ‖x‖ ^ 2 := by
        have hnormSq : ‖C‖ ^ 2 ≤ ‖x‖ ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hC
        exact mul_le_mul_of_nonneg_left hnormSq hnonneg
      _ = (Real.sqrt (c⁻¹) * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hnonneg]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq


/-- The represented input map is a continuous linear map with explicit normalization factor. -/
noncomputable def tensorH3KernelInputCLM {c : ℝ} (hc : 0 < c) :
    UnforcedLeray.TrainB.TensorH3 c →L[ℝ]
      Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (tensorH3KernelInputLinear hc).mkContinuous (Real.sqrt (c⁻¹)) fun x =>
    norm_tensorH3KernelInput_le hc x

theorem tendsto_tensorH3KernelInput_of_tendsto {c : ℝ} (hc : 0 < c)
    {y : ℕ → UnforcedLeray.TrainB.TensorH3 c} {x : UnforcedLeray.TrainB.TensorH3 c}
    (hy : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun n => tensorH3KernelInput hc (y n)) atTop
      (𝓝 (tensorH3KernelInput hc x)) := by
  have hcont := (tensorH3KernelInputCLM hc).continuous.tendsto x
  exact hcont.comp hy


/-- The actual B0296 Gaussian output is in normalized-cell L² for any periodic L² tensor. -/
theorem periodicHeatDivMemLp {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (T : Plane → Plane × Plane) (hper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hmeas : AEStronglyMeasurable T volume) (hmem : MemLp T 2
      (UnforcedLeray.B0284.cellMeasure c)) :
    MemLp (UnforcedLeray.B0296.heatDiv θ T) 2 (UnforcedLeray.B0284.cellMeasure c) :=
  UnforcedLeray.B0296.memLp_heatDiv hc hθ hper hmeas
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top

/-- On an actual periodic representative, the descended L² operator is the literal B0296
Gaussian convolution class. -/
theorem heatDivL2CLM_apply_to_periodic {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hmeas : AEStronglyMeasurable T volume)
    (hmem : MemLp T 2 (UnforcedLeray.B0284.cellMeasure c)) :
    UnforcedLeray.HeatCylinder.heatDivL2CLM hc hθ (hmem.toLp T) =
      (periodicHeatDivMemLp hc hθ T hper hmeas hmem).toLp
        (UnforcedLeray.B0296.heatDiv θ T) := by
  let x : Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) := hmem.toLp T
  let R := tensorRep hc x
  have hR := tensorRep_spec hc x
  have hRmem := memLp_tensorRep hc x
  have hRae : R =ᵐ[UnforcedLeray.B0284.cellMeasure c] T := by
    filter_upwards [hR.2.2, hmem.coeFn_toLp] with z hRx hTx
    exact hRx.trans hTx
  have hperEq : UnforcedLeray.B0284.IsQPeriodic c (fun z => R z = T z) := by
    intro z
    have hRper : R (z.1 + c, z.2) = R z := hR.2.1 z
    have hTper : T (z.1 + c, z.2) = T z := hper z
    simp [hRper, hTper]
  have hRvol := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hperEq hRae
  have hcongr := heatDiv_congr_ae hc hθ hR.2.1 hper hR.1 hmeas
    hRmem hmem hRvol
  let hOutR := UnforcedLeray.B0296.memLp_heatDiv hc hθ hR.2.1 hR.1
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hRmem.eLpNorm_ne_top
  change hOutR.toLp (UnforcedLeray.B0296.heatDiv θ R) =
    (periodicHeatDivMemLp hc hθ T hper hmeas hmem).toLp
      (UnforcedLeray.B0296.heatDiv θ T)
  apply Lp.ext
  filter_upwards [hOutR.coeFn_toLp,
    (periodicHeatDivMemLp hc hθ T hper hmeas hmem).coeFn_toLp, hcongr] with
    z hRout hTout hEq
  calc
    (hOutR.toLp (UnforcedLeray.B0296.heatDiv θ R)) z =
        UnforcedLeray.B0296.heatDiv θ R z := hRout
    _ = UnforcedLeray.B0296.heatDiv θ T z := hEq
    _ = ((periodicHeatDivMemLp hc hθ T hper hmeas hmem).toLp
        (UnforcedLeray.B0296.heatDiv θ T)) z := hTout.symm


/-- The actual vector heat output is in normalized-cell L². -/
theorem periodicHeatDivVecMemLp {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (T : Plane → Plane × Plane) (hper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hmeas : AEStronglyMeasurable T volume) (hmem : MemLp T 2
      (UnforcedLeray.B0284.cellMeasure c)) :
    MemLp (fun z => UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ T z))
      2 (UnforcedLeray.B0284.cellMeasure c) :=
  (UnforcedLeray.Train.toVecL : Plane →L[ℝ] UnforcedLeray.Train.Vec).comp_memLp'
    (periodicHeatDivMemLp hc hθ T hper hmeas hmem)

/-- The actual vector L² quotient operator agrees with the literal Gaussian convolution on every
periodic representative. -/
theorem heatDivVecL2CLM_apply_to_periodic {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hmeas : AEStronglyMeasurable T volume)
    (hmem : MemLp T 2 (UnforcedLeray.B0284.cellMeasure c)) :
    heatDivVecL2CLM hc hθ (hmem.toLp T) =
      (periodicHeatDivVecMemLp hc hθ T hper hmeas hmem).toLp
        (fun z => UnforcedLeray.Train.toVec
          (UnforcedLeray.B0296.heatDiv θ T z)) := by
  change ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] UnforcedLeray.Train.Vec).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c))
      (heatDivL2CLM hc hθ (hmem.toLp T)) = _
  rw [heatDivL2CLM_apply_to_periodic hc hθ hper hmeas hmem]
  apply Lp.ext
  have hcomp := ContinuousLinearMap.coeFn_compLpL
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] UnforcedLeray.Train.Vec)
    ((periodicHeatDivMemLp hc hθ T hper hmeas hmem).toLp
      (UnforcedLeray.B0296.heatDiv θ T))
  filter_upwards [hcomp,
    (periodicHeatDivMemLp hc hθ T hper hmeas hmem).coeFn_toLp,
    (periodicHeatDivVecMemLp hc hθ T hper hmeas hmem).coeFn_toLp] with z hmap hout hvec
  calc
    (((UnforcedLeray.Train.toVecL : Plane →L[ℝ] UnforcedLeray.Train.Vec).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c))
      ((periodicHeatDivMemLp hc hθ T hper hmeas hmem).toLp
        (UnforcedLeray.B0296.heatDiv θ T))) z =
        UnforcedLeray.Train.toVec
          (((periodicHeatDivMemLp hc hθ T hper hmeas hmem).toLp
            (UnforcedLeray.B0296.heatDiv θ T)) z) := hmap
    _ = UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ T z) := by rw [hout]
    _ = ((periodicHeatDivVecMemLp hc hθ T hper hmeas hmem).toLp
        (fun z => UnforcedLeray.Train.toVec
          (UnforcedLeray.B0296.heatDiv θ T z))) z := hvec.symm

/-- On a smooth TensorVal input, the normalized-cell class constructed from the H³ value is the
actual rowwise plane field almost everywhere. -/
theorem tensorH3KernelInput_coe_ae_ofCylSmooth {c : ℝ} (hc : 0 < c)
    {T : Plane → TensorVal} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    (tensorH3KernelInput hc
      (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := TensorVal) (k := 3) (p := 2) hc T hT) : Plane → Plane × Plane) =ᵐ[
          UnforcedLeray.B0284.cellMeasure c]
      (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T z)) := by
  let x := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := TensorVal) (k := 3) (p := 2) hc T hT
  have hvalue :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x : Plane → TensorVal) =ᵐ[
          UnforcedLeray.Cyl.cellμ c] T := by
    change (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
      (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := TensorVal) (k := 3) (p := 2) hc T hT) : Plane → TensorVal) =ᵐ[
          UnforcedLeray.Cyl.cellμ c] T
    have hval := UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc T hT
    simpa only [h3Measure_eq_cell c] using hval
  have hlift : centeredPerLift hc (tensorH3ValueRep hc x) =ᵐ[
      UnforcedLeray.Cyl.cellμ c] T := by
    filter_upwards [ae_tensorH3ValueRep_cell hc x,
      ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c), hvalue] with z hrep hzcell hv
    rw [centeredPerLift_eq_on_cell hc (tensorH3ValueRep hc x) hzcell]
    exact hrep.trans hv
  have hfield : tensorH3KernelRep hc x =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T z)) := by
    filter_upwards [hlift] with z hz
    exact congrArg UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap hz
  have hperiodic : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T z)) := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact congrArg UnforcedLeray.TrainB.tensorToPlaneCLE (hT.periodic z)
  have hrep := ae_eq_of_ae_centered_periodic hc
    (periodic_tensorH3KernelRep hc x) hperiodic hfield
  have hclass := (memLp_tensorH3KernelRep_normalized hc x).coeFn_toLp
  have hclass' : (tensorH3KernelInput hc x : Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] tensorH3KernelRep hc x := by
    simpa [tensorH3KernelInput] using hclass
  have hout : (tensorH3KernelInput hc x : Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c]
      (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T z)) := hclass'.trans hrep
  simpa [x] using hout


/-- Retain the actual H³ approximation when passing to Cauchy heat outputs. The output sequence is
built from the same smooth dense representatives that converge to `x`; this rules out an unrelated
Cauchy witness. -/
theorem exists_approximating_cauchy_heatDivH3_sequence {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (x : UnforcedLeray.TrainB.TensorH3 c) :
    ∃ y : ℕ → UnforcedLeray.TrainB.TensorH3 c,
    ∃ T : ℕ → Plane → TensorVal,
    ∃ hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n),
    ∃ hS : ∀ n, UnforcedLeray.Sob.IsCylSmooth c
      (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T n z)),
      (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := TensorVal) (k := 3) (p := 2) hc (T n) (hT n)) ∧
      Tendsto y atTop (𝓝 x) ∧
      Tendsto (fun n => tensorH3KernelInput hc (y n)) atTop
        (𝓝 (tensorH3KernelInput hc x)) ∧
      CauchySeq (smoothHeatOutputSequence hc hθ hS) := by
  obtain ⟨y, T, hT, hyrep, hlim⟩ := exists_smoothTensorH3_sequence hc x
  let L : TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  let S : ℕ → Plane → Plane × Plane := fun n z => L (T n z)
  have hS : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (S n) := by
    intro n
    exact isCylSmooth_postcomp_clm (hT n) L
  have hsub : ∀ m n, UnforcedLeray.Sob.IsCylSmooth c (fun z => S m z - S n z) := by
    intro m n
    exact isCylSmooth_sub (hS m) (hS n)
  have hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      heatTensorH3Distance c (S m) (S n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hlim.cauchySeq) ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hcontract := heatTensorH3Distance_tensorToPlane_le (hT m) (hT n)
    have henergy : cylinderDerivativeEnergyDistance c (T m) (T n) = dist (y m) (y n) := by
      rw [cylinderDerivativeEnergyDistance_eq_norm_ofCylSmooth hc (hT m) (hT n)]
      rw [ofCylSmooth_tensor_sub_eq hc (hT m) (hT n)]
      rw [hyrep m, hyrep n, dist_eq_norm]
    calc
      heatTensorH3Distance c (S m) (S n) ≤
          cylinderDerivativeEnergyDistance c (T m) (T n) := by
        simpa [S, L] using hcontract
      _ = dist (y m) (y n) := henergy
      _ < ε := hN m hm n hn
  refine ⟨y, T, hT, ?_, hyrep, hlim,
    tendsto_tensorH3KernelInput_of_tendsto hc hlim, ?_⟩
  · intro n
    simpa [L] using isCylSmooth_postcomp_clm (hT n)
      (UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap)
  · exact heatOutputSequence_cauchy_of_heatTensorH3Distance hc hθ hS hsub hC

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tensorH3ValueCellLp
#print axioms UnforcedLeray.HeatCylinder.tensorH3KernelInput
#print axioms UnforcedLeray.HeatCylinder.tensorH3KernelInput_add
#print axioms UnforcedLeray.HeatCylinder.tensorH3KernelInput_smul
#print axioms UnforcedLeray.HeatCylinder.norm_sq_tensorH3KernelInput_eq
#print axioms UnforcedLeray.HeatCylinder.norm_tensorH3ValueCellLp_eq
#print axioms UnforcedLeray.HeatCylinder.norm_tensorH3KernelInput_le
#print axioms UnforcedLeray.HeatCylinder.periodicHeatDivMemLp
#print axioms UnforcedLeray.HeatCylinder.heatDivL2CLM_apply_to_periodic
#print axioms UnforcedLeray.HeatCylinder.heatDivVecL2CLM_apply_to_periodic
#print axioms UnforcedLeray.HeatCylinder.tensorH3KernelInputCLM
#print axioms UnforcedLeray.HeatCylinder.tendsto_tensorH3KernelInput_of_tendsto
#print axioms UnforcedLeray.HeatCylinder.tensorH3KernelInputLinear
#print axioms UnforcedLeray.HeatCylinder.tensorH3KernelInput
#print axioms UnforcedLeray.HeatCylinder.exists_approximating_cauchy_heatDivH3_sequence
