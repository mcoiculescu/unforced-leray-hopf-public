import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Part I, task `PartI:T02/1/4/6/4/5/1`: the advection of the smooth representative is `L²(cell)`

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `AdvectionMemLpLeaf` (`Short/PartI/Sub/T02_1_4_6_4_5.lean`).  For the smooth periodic
representative `w r` with bounded derivatives (`IsSpatialRepOn.bounded`, `IsSpatialRepOn.smooth`),
the advection `Train.advection (w r)` is `L²(cell)`: each component is a sum of products of a
sup-bounded continuous factor `w r · j` and a first partial derivative of `w r`, and the first partials
are `L²(cell)` by `IsSpatialRepOn.represents` at the order-one words `iQ`, `iEta`.
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

/-- A continuous factor bounded by `M` times an `L²` function is `L²`. -/
theorem advLeaf_memLp_bdd_mul {c : ℝ} {φ D : Plane → ℝ} {M : ℝ}
    (hφc : Continuous φ) (hφ : ∀ z, |φ z| ≤ M) (hD : MemLp D 2 (Cyl.cellμ c)) :
    MemLp (fun z => φ z * D z) 2 (Cyl.cellμ c) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hφ 0)
  refine MemLp.of_le (hD.norm.const_mul M)
    (hφc.aestronglyMeasurable.mul hD.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  show ‖φ z * D z‖ ≤ ‖M * ‖D z‖‖
  rw [Real.norm_of_nonneg (mul_nonneg hM0 (norm_nonneg _)), norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hφ z) (norm_nonneg _)

/-- The coordinate projection of `Vec` as a continuous linear functional. -/
def advLeafProj (j : Fin 2) : Vec →L[ℝ] ℝ := EuclideanSpace.proj j

theorem advLeafProj_apply (j : Fin 2) (x : Vec) : advLeafProj j x = x j := rfl

/-- Coordinates of a vector are bounded by its norm. -/
theorem advLeaf_abs_comp_le {f : Plane → Vec} {M : ℝ} (h : ∀ z, ‖f z‖ ≤ M) (j : Fin 2)
    (z : Plane) : |f z j| ≤ M := by
  have h1 : ‖f z j‖ ≤ ‖f z‖ := PiLp.norm_apply_le (f z) j
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (h z)

/-- The `∂_q` derivative commutes with the coordinate projection. -/
theorem advLeaf_partialQ_proj {f : Plane → Vec} (hd : Differentiable ℝ f) (j : Fin 2)
    (z : Plane) :
    Cyl.partialQ (fun w => advLeafProj j (f w)) z =
      advLeafProj j (Cyl.partialQ f z) := by
  have hdiff : Differentiable ℝ (fun w => advLeafProj j (f w)) := fun w =>
    ((advLeafProj j).hasFDerivAt.comp w (hd w).hasFDerivAt).differentiableAt
  have hf : HasFDerivAt (fun w => advLeafProj j (f w))
      ((advLeafProj j).comp (fderiv ℝ f z)) z :=
    (advLeafProj j).hasFDerivAt.comp z (hd z).hasFDerivAt
  rw [Cyl.partialQ_eq_fderiv hdiff z, Cyl.partialQ_eq_fderiv hd z, hf.fderiv]
  rfl

/-- The `∂_η` derivative commutes with the coordinate projection. -/
theorem advLeaf_partialEta_proj {f : Plane → Vec} (hd : Differentiable ℝ f) (j : Fin 2)
    (z : Plane) :
    Cyl.partialEta (fun w => advLeafProj j (f w)) z =
      advLeafProj j (Cyl.partialEta f z) := by
  have hdiff : Differentiable ℝ (fun w => advLeafProj j (f w)) := fun w =>
    ((advLeafProj j).hasFDerivAt.comp w (hd w).hasFDerivAt).differentiableAt
  have hf : HasFDerivAt (fun w => advLeafProj j (f w))
      ((advLeafProj j).comp (fderiv ℝ f z)) z :=
    (advLeafProj j).hasFDerivAt.comp z (hd z).hasFDerivAt
  rw [Cyl.partialEta_eq_fderiv hdiff z, Cyl.partialEta_eq_fderiv hd z, hf.fderiv]
  rfl

/-- The `∂_q` derivative of the smooth representative is `L²(cell)`, read off from
`represents` at the word `iQ`. -/
theorem advLeaf_partialQ_memLp {c T : ℝ} {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
    {w : ℝ → Plane → Vec} (hw : IsSpatialRepOn c T u w) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    MemLp (Cyl.partialQ (w r)) 2 (Cyl.cellμ c) := by
  have hd : Differentiable ℝ (w r) := (hw.smooth r hr).differentiable (by simp)
  have hrep : (vecH3CellDerivCLM (Cyl.iQ (k := 2)) (u ⟨r, hr⟩) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      Sob.iterD [((1 : ℝ), (0 : ℝ))] (w r) := by
    have h := hw.represents ⟨r, hr⟩ (Cyl.iQ (k := 2))
    rwa [Cyl.word_iQ c (k := 2)] at h
  have hfun : Sob.iterD [((1 : ℝ), (0 : ℝ))] (w r) = Cyl.partialQ (w r) :=
    funext fun z => by
      rw [Cyl.partialQ_eq_fderiv hd z]
      rfl
  rw [hfun] at hrep
  exact MemLp.ae_eq hrep (Lp.memLp _)

/-- The `∂_η` derivative of the smooth representative is `L²(cell)`, read off from
`represents` at the word `iEta`. -/
theorem advLeaf_partialEta_memLp {c T : ℝ} {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
    {w : ℝ → Plane → Vec} (hw : IsSpatialRepOn c T u w) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    MemLp (Cyl.partialEta (w r)) 2 (Cyl.cellμ c) := by
  have hd : Differentiable ℝ (w r) := (hw.smooth r hr).differentiable (by simp)
  have hrep : (vecH3CellDerivCLM (Cyl.iEta (k := 2)) (u ⟨r, hr⟩) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      Sob.iterD [((0 : ℝ), (1 : ℝ))] (w r) := by
    have h := hw.represents ⟨r, hr⟩ (Cyl.iEta (k := 2))
    rwa [Cyl.word_iEta c (k := 2)] at h
  have hfun : Sob.iterD [((0 : ℝ), (1 : ℝ))] (w r) = Cyl.partialEta (w r) :=
    funext fun z => by
      rw [Cyl.partialEta_eq_fderiv hd z]
      rfl
  rw [hfun] at hrep
  exact MemLp.ae_eq hrep (Lp.memLp _)

/-- **Leaf A** (membership in `L²(cell)`).  Target `AdvectionMemLpLeaf`. -/
theorem advectionMemLpLeaf_proof : UnforcedLeray.Short.PartI.AdvectionMemLpLeaf := by
  intro ν c T hν hc hc1 hT u _hu w hw r hr
  have hd : Differentiable ℝ (w r) := (hw.smooth r hr).differentiable (by simp)
  have hcw : Continuous (w r) := (hw.smooth r hr).continuous
  obtain ⟨M, hM⟩ := hw.bounded 0
  have hbd : ∀ z, ‖w r z‖ ≤ M := fun z => by
    have h := hM r hr z
    rwa [norm_iteratedFDeriv_zero] at h
  have hQ : MemLp (Cyl.partialQ (w r)) 2 (Cyl.cellμ c) := advLeaf_partialQ_memLp hw hr
  have hE : MemLp (Cyl.partialEta (w r)) 2 (Cyl.cellμ c) := advLeaf_partialEta_memLp hw hr
  -- component-wise `L²` bounds for the partial derivatives of the coordinates
  have hQc : ∀ j : Fin 2, MemLp (fun z => Cyl.partialQ (fun y => w r y j) z) 2 (Cyl.cellμ c) :=
    fun j => by
      have h := hQ.continuousLinearMap_comp (advLeafProj j)
      have hfun : (fun z => Cyl.partialQ (fun y => w r y j) z) =
          fun z => advLeafProj j (Cyl.partialQ (w r) z) :=
        funext fun z => advLeaf_partialQ_proj hd j z
      rw [hfun]
      exact h
  have hEc : ∀ j : Fin 2, MemLp (fun z => Cyl.partialEta (fun y => w r y j) z) 2 (Cyl.cellμ c) :=
    fun j => by
      have h := hE.continuousLinearMap_comp (advLeafProj j)
      have hfun : (fun z => Cyl.partialEta (fun y => w r y j) z) =
          fun z => advLeafProj j (Cyl.partialEta (w r) z) :=
        funext fun z => advLeaf_partialEta_proj hd j z
      rw [hfun]
      exact h
  have hcj : ∀ j : Fin 2, Continuous (fun z => w r z j) := fun j =>
    (advLeafProj j).continuous.comp hcw
  have hbj : ∀ j : Fin 2, ∀ z, |w r z j| ≤ M := fun j z => advLeaf_abs_comp_le hbd j z
  -- the two advection components
  have hA : ∀ j : Fin 2, MemLp (fun z => w r z 0 * Cyl.partialQ (fun y => w r y j) z +
      w r z 1 * Cyl.partialEta (fun y => w r y j) z) 2 (Cyl.cellμ c) := fun j =>
    (advLeaf_memLp_bdd_mul (hcj 0) (hbj 0) (hQc j)).add
      (advLeaf_memLp_bdd_mul (hcj 1) (hbj 1) (hEc j))
  have h0 : MemLp (fun z => Train.advection (w r) z 0) 2 (Cyl.cellμ c) := by
    have key : (fun z => Train.advection (w r) z 0) = fun z => w r z 0 *
        Cyl.partialQ (fun y => w r y 0) z + w r z 1 * Cyl.partialEta (fun y => w r y 0) z :=
      funext fun z => rfl
    rw [key]
    exact hA 0
  have h1 : MemLp (fun z => Train.advection (w r) z 1) 2 (Cyl.cellμ c) := by
    have key : (fun z => Train.advection (w r) z 1) = fun z => w r z 0 *
        Cyl.partialQ (fun y => w r y 1) z + w r z 1 * Cyl.partialEta (fun y => w r y 1) z :=
      funext fun z => rfl
    rw [key]
    exact hA 1
  refine memLp_piLp_iff.2 fun i => ?_
  fin_cases i
  · exact h0
  · exact h1

end UnforcedLeray.Short.PartI
