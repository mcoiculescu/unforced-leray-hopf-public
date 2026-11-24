import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.HeatDivDeriv.Defs

/-!
# Part I, task `PartI:T02/1/2/3/5`: leaf A1 (smooth input)

Source of record: `the November 2 reference manuscript`, lines 261-288.
`bdpHddKernelSmooth_proof : BdpHddKernelSmooth`: for a smooth periodic tensor `T`, the kernel
class `bdpTensorH3DerivKernel hc α` of `W.ofCylSmooth T` is the literal normalized-cell class of
`∂^α (tensorToPlaneCLE ∘ T)`.  Each row is a periodic field a.e. equal on the centered cell to
the row of `∂^α T`, so its centered-to-normalized transport is that row; reassembling the rows
gives `tensorToPlaneCLE (∂^α T)`.  No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane cellμ)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- The centered-to-normalized transport of a class that is a.e. equal on the centered cell to a
periodic field is that field. -/
private theorem bdpHdd_centeredVecToNormalized_ae_of_periodic {c : ℝ} (hc : 0 < c)
    (f : Lp Vec 2 (cellμ c)) {R : Plane → Vec} (hRper : Cyl.IsPeriodic c R)
    (hfR : (f : Plane → Vec) =ᵐ[cellμ c] R) :
    (centeredVecToNormalizedCLM hc f : Plane → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c] R := by
  have hbase : centeredVecL2Rep f =ᵐ[cellμ c] R := (centeredVecL2Rep_ae f).trans hfR
  have hlift := centeredPerLift_congr_ae hc hbase
  have hself := centeredPerLift_eq_self_of_periodic hc hRper
  have hglobal : centeredVecL2PeriodicRep hc f =ᵐ[volume] R := by
    filter_upwards [hlift] with z hz
    exact hz.trans (congrFun hself z)
  have hnorm : centeredVecL2PeriodicRep hc f =ᵐ[UnforcedLeray.B0284.cellMeasure c] R := by
    apply ae_iff.mpr
    exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hglobal)
  have hmap : (centeredVecToNormalizedCLM hc f : Plane → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      centeredVecL2PeriodicRep hc f :=
    (memLp_centeredVecL2PeriodicRep_normalized hc f).coeFn_toLp
  exact hmap.trans hnorm

theorem bdpHddKernelSmooth_proof : BdpHddKernelSmooth := by
  intro c hc T hT α
  let vs := (Sob.cylinder c).word α
  let Tα : Plane → TensorVal := Sob.iterD vs T
  have hTα : Sob.IsCylSmooth c Tα := hT.iterD vs
  let x : TensorH3 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := TensorVal)
    (k := 3) (p := 2) hc T hT
  let D := Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 α x
  let g : Lp TensorVal 2 (cellμ c) := bdpTensorWeightedToCellCLM c D
  have hgD : (g : Plane → TensorVal) =ᵐ[cellμ c] (D : Plane → TensorVal) := by
    change Lp.LpToLpOfMeasureLeSMul (μ := cellμ c) (c := 1)
        (by simp) (by rw [← heatVecH3_measure_eq_cell_deriv c]; simp) D =ᵐ[cellμ c] _
    exact Lp.coeFn_LpToLpOfMeasureLeSMul (μ := cellμ c) (c := 1)
      (by simp) (by rw [← heatVecH3_measure_eq_cell_deriv c]; simp) D
  have hDT : (D : Plane → TensorVal) =ᵐ[cellμ c] Tα := by
    have hderiv := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc T hT α
    simpa only [heatVecH3_measure_eq_cell_deriv c] using hderiv
  have hg : (g : Plane → TensorVal) =ᵐ[cellμ c] Tα := hgD.trans hDT
  -- the two rows
  let R₁ : Plane → Vec := fun z => bdpTensorRow₁CLM (Tα z)
  let R₂ : Plane → Vec := fun z => bdpTensorRow₂CLM (Tα z)
  have hTαper : ∀ z : Plane, Tα (z.1 + c, z.2) = Tα z := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hTα.periodic z
  have hR₁per : Cyl.IsPeriodic c R₁ := by
    intro z
    exact congrArg bdpTensorRow₁CLM (hTαper z)
  have hR₂per : Cyl.IsPeriodic c R₂ := by
    intro z
    exact congrArg bdpTensorRow₂CLM (hTαper z)
  have hr₁ : ((bdpTensorRow₁CLM.compLpL 2 (cellμ c) g : Lp Vec 2 (cellμ c)) : Plane → Vec)
      =ᵐ[cellμ c] R₁ := by
    filter_upwards [bdpTensorRow₁CLM.coeFn_compLpL g, hg] with z hz hgz
    rw [hz, hgz]
  have hr₂ : ((bdpTensorRow₂CLM.compLpL 2 (cellμ c) g : Lp Vec 2 (cellμ c)) : Plane → Vec)
      =ᵐ[cellμ c] R₂ := by
    filter_upwards [bdpTensorRow₂CLM.coeFn_compLpL g, hg] with z hz hgz
    rw [hz, hgz]
  have hN₁ := bdpHdd_centeredVecToNormalized_ae_of_periodic hc _ hR₁per hr₁
  have hN₂ := bdpHdd_centeredVecToNormalized_ae_of_periodic hc _ hR₂per hr₂
  let N₁ : Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c) :=
    centeredVecToNormalizedCLM hc (bdpTensorRow₁CLM.compLpL 2 (cellμ c) g)
  let N₂ : Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c) :=
    centeredVecToNormalizedCLM hc (bdpTensorRow₂CLM.compLpL 2 (cellμ c) g)
  let I₁ : Vec →L[ℝ] Plane × Plane :=
    (ContinuousLinearMap.inl ℝ Plane Plane).comp (Train.toVecL.symm : Vec →L[ℝ] Plane)
  let I₂ : Vec →L[ℝ] Plane × Plane :=
    (ContinuousLinearMap.inr ℝ Plane Plane).comp (Train.toVecL.symm : Vec →L[ℝ] Plane)
  have hkernel : bdpTensorH3DerivKernel hc α x =
      I₁.compLpL 2 (UnforcedLeray.B0284.cellMeasure c) N₁ +
        I₂.compLpL 2 (UnforcedLeray.B0284.cellMeasure c) N₂ := rfl
  have hn₁' : (N₁ : Plane → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c] R₁ := hN₁
  have hn₂' : (N₂ : Plane → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c] R₂ := hN₂
  have hiter : Sob.iterD vs (fun z => tensorToPlaneCLE.toContinuousLinearMap (T z)) =
      fun z => tensorToPlaneCLE.toContinuousLinearMap (Tα z) :=
    iterD_isCylSmooth_postcomp_clm hT tensorToPlaneCLE.toContinuousLinearMap vs
  have hmem := memLp_tensor_iterD_cylSmooth_normalized hc
    (isCylSmooth_postcomp_clm hT tensorToPlaneCLE.toContinuousLinearMap) vs
  change bdpTensorH3DerivKernel hc α x =
    hmem.toLp (Sob.iterD vs (fun z => tensorToPlaneCLE.toContinuousLinearMap (T z)))
  rw [hkernel]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (I₁.compLpL 2 (UnforcedLeray.B0284.cellMeasure c) N₁)
      (I₂.compLpL 2 (UnforcedLeray.B0284.cellMeasure c) N₂),
    I₁.coeFn_compLpL N₁, I₂.coeFn_compLpL N₂, hn₁', hn₂', hmem.coeFn_toLp] with
    z hadd h₁ h₂ hn₁ hn₂ hto
  rw [hadd, Pi.add_apply, h₁, h₂, hto, hiter, hn₁, hn₂]
  first
    | (simp only [I₁, I₂, R₁, R₂, bdpTensorRow₁CLM, bdpTensorRow₂CLM,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply, Prod.mk_add_mk, add_zero, zero_add,
        Prod.mk.eta]; done)
    | (ext <;> simp [I₁, I₂, R₁, R₂, bdpTensorRow₁CLM, bdpTensorRow₂CLM])

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.bdpHddKernelSmooth_proof
