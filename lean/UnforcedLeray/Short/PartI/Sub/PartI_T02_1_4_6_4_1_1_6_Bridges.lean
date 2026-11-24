import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6

/-!
# Bridge lemmas for `KernelInputRowTensor` and `HeatVecAdvectionClass`

Source: `the November 2 reference manuscript`,
lines 261-288 (the Duhamel term is the heat flow of `div (u ⊗ u)`).  Each `Prop` below is a true
statement about the concrete library objects; the two `_of` theorems reduce the sub-statements
`Sub2`, `Sub3` of `PartI_T02_1_4_6_4_1_1_6` to them.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- **Bridge 2a** (lines 261-288): the normalized kernel input of an `H³` tensor `X` is a.e. on the
normalized cell any `Q`-periodic field `T` that agrees a.e. on the centered cell with
`tensorToPlaneCLE` of the `H³` value of `X`.  (Body of `tensorH3KernelInput_coe_ae_ofCylSmooth`,
`Lib/HeatCylinder/H3ActualLimit.lean:560`, with `hvalue` replaced by the hypothesis; the private
helper `ae_tensorH3ValueRep_cell` (line 87) must be reproved.) -/
def TensorKernelInputPeriodicAE : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (X : TensorH3 c) (T : Plane → Plane × Plane),
    UnforcedLeray.B0284.IsQPeriodic c T →
    (fun z => tensorToPlaneCLE
      ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 X : Plane → TensorVal) z))
        =ᵐ[UnforcedLeray.Cyl.cellμ c] T →
    (tensorH3KernelInput hc X : Plane → Plane × Plane) =ᵐ[UnforcedLeray.B0284.cellMeasure c] T

/-- **Bridge 2b** (lines 261-288): the zero-order centered class of an `H³` vector field is a.e.
on the centered cell its `H³` value.  (The private lemma
`centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local`,
`Lib/HeatCylinder/HeatVecH3P0Compatibility.lean:27`, together with `centeredVecH3DerivativeClass_coe_ae`;
or `vecH3CellDerivCLM` unfolded with `Lp.coeFn_compMeasurePreserving`.) -/
def VecH3ZeroClassValueAE : Prop :=
  ∀ (c : ℝ) (x : VectorH3 c),
    ((vecH3CellDerivCLM Sob.Idx.zero x : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x : Plane → Vec)

theorem planeRowTensorValue_qperiodic {c : ℝ} {w : Plane → Vec} (hper : Cyl.IsPeriodic c w) :
    UnforcedLeray.B0284.IsQPeriodic c (planeRowTensorValue w w) := by
  intro z
  simp only [planeRowTensorValue, hper z]

theorem kernelInputRowTensor_of (b1 : TensorKernelInputPeriodicAE) (b2 : VecH3ZeroClassValueAE) :
    KernelInputRowTensor := by
  intro c hc hc1 x w _hw hper _hbd hx hmem
  have hv : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x : Plane → Vec)
        =ᵐ[Cyl.cellμ c] w := (b2 c x).symm.trans hx
  have hpl := tensorH3Bilinear_planeValue_ae hc1 x x
  have hT : (fun z => tensorToPlaneCLE
      ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (tensorH3Bilinear hc1 x x) : Plane → TensorVal) z))
        =ᵐ[Cyl.cellμ c] planeRowTensorValue w w := by
    filter_upwards [hpl, hv] with z h1 h2
    rw [h1]
    simp only [planeRowTensorValue, h2]
  have hK := b1 c hc (tensorH3Bilinear hc1 x x) _ (planeRowTensorValue_qperiodic hper) hT
  exact Lp.ext (hK.trans hmem.coeFn_toLp.symm)

/-- **Bridge 3a** (lines 261-288): the centered-to-normalized transport of an `L²` class that equals
a `Q`-periodic field a.e. on the centered cell is that field a.e. on the normalized cell.
(Coe lemma for `centeredVecToNormalizedCLM`, `Lib/HeatCylinder/HeatVecH3DerivativeTransport.lean`
lines 100-180, then `ae_eq_of_ae_centered_periodic`, `H3ActualLimit.lean:136`.) -/
def CenteredVecTransportPeriodicAE : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (G : Cyl.L2v c) (F : Plane → Vec),
    UnforcedLeray.B0284.IsQPeriodic c F →
    ((G : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] F →
    (centeredVecToNormalizedCLM hc G : Plane → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c] F

/-- **Bridge 3b** (lines 261-288): the advection of a smooth `c`-periodic field is continuous and
`Q`-periodic.  (`Train.advection`, `Lib/Train/Ops.lean:95`; partials are `fderiv`s of a periodic
smooth function, which are periodic.) -/
def AdvectionPeriodicContinuous : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), ContDiff ℝ ∞ w → Cyl.IsPeriodic c w →
    UnforcedLeray.B0284.IsQPeriodic c (Train.advection w) ∧ Continuous (Train.advection w)

/-- **Bridge 3c** (lines 261-288): given N4, the normalized vector heat of an `L²` class `K` equal
a.e. to `toVec ∘ T` (`T` periodic, measurable) is the class of `toVec ∘ heat θ T`.
(`T ∈ L²(cellMeasure)` follows from `K ∈ L²` since `toVec` is a linear equivalence;
`heatVecL2CLM_apply`, `Lib/HeatCylinder/HeatVecL2.lean:41`, then `NeedHeatPeriodicL2` applied to
`T` and `MemLp.toLp_congr`.) -/
def HeatVecOfPeriodicClass : Prop :=
  NeedHeatPeriodicL2 →
  ∀ (c : ℝ) (hc : 0 < c) (θ : ℝ) (_hθ : 0 < θ) (T : Plane → Plane),
    UnforcedLeray.B0284.IsQPeriodic c T → AEStronglyMeasurable T volume →
    ∀ K : Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c),
      (K : Plane → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c] (fun z => toVec (T z)) →
      ∀ hm : MemLp (fun z => toVec (UnforcedLeray.B0284.heat θ T z)) 2
          (UnforcedLeray.B0284.cellMeasure c),
        heatVecL2CLM hc θ K = hm.toLp (fun z => toVec (UnforcedLeray.B0284.heat θ T z))

theorem heatVecAdvectionClass_of (b1 : CenteredVecTransportPeriodicAE)
    (b2 : AdvectionPeriodicContinuous) (b3 : HeatVecOfPeriodicClass) :
    HeatVecAdvectionClass := by
  intro n4 n3 c hc θ hθ w hw hper _hbd hdiv G hG hm
  have hTv : ∀ z, toVec (rowDivergence (planeRowTensorValue w w) z) = Train.advection w z :=
    n3 w hw hdiv
  have hTeq : ∀ z, rowDivergence (planeRowTensorValue w w) z =
      Train.toVecL.symm (Train.advection w z) := by
    intro z
    rw [← hTv z]
    exact (Train.toVecL.symm_apply_apply _).symm
  obtain ⟨hperA, hcontA⟩ := b2 c w hw hper
  have hTfun : rowDivergence (planeRowTensorValue w w) =
      fun z => Train.toVecL.symm (Train.advection w z) := funext hTeq
  have hTper : UnforcedLeray.B0284.IsQPeriodic c (rowDivergence (planeRowTensorValue w w)) := by
    intro z
    rw [hTeq, hTeq, hperA z]
  have hTmeas : AEStronglyMeasurable (rowDivergence (planeRowTensorValue w w)) volume := by
    rw [hTfun]
    exact (Train.toVecL.symm.continuous.comp hcontA).aestronglyMeasurable
  have hK := b1 c hc G (Train.advection w) hperA hG
  have hK' : (centeredVecToNormalizedCLM hc G : Plane → Vec) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c]
      (fun z => toVec (rowDivergence (planeRowTensorValue w w) z)) := by
    refine hK.trans (Eventually.of_forall fun z => ?_)
    exact (hTv z).symm
  exact b3 n4 c hc θ hθ _ hTper hTmeas _ hK' hm

end UnforcedLeray.Short.PartI
