import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3
import UnforcedLeray.Lib.SobolevC.CylSmooth

/-!
# Part I, leaf `PartI:T02/1/4/6/4/2/3/3` (`LeafLapCellTestCH`)

The vector Laplacian of a cell test is a cell test. Route: a cell test is a `Sob.IsCylSmooth`
field; `IsCylSmooth.dir` (directional derivatives keep the class) gives the scalar Laplacian,
componentwise, and the componentwise Laplacians are reassembled with `toVecL`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec toVecL lapS vecLaplacian)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

namespace LapCellTestAux

theorem isCylSmooth_of_cellTest {c : ℝ} {ψ : Plane → Vec} (hψ : IsCellTest c ψ) :
    UnforcedLeray.Sob.IsCylSmooth c ψ :=
  { smooth := hψ.1
    periodic := fun z => by
      have e : z + ((c : ℝ), (0 : ℝ)) = (z.1 + c, z.2) := by ext <;> simp
      rw [e]
      exact hψ.2.1 z
    bounded := hψ.2.2 }

theorem isCylSmooth_clm {c : ℝ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {u : Plane → F}
    (L : F →L[ℝ] G) (hu : UnforcedLeray.Sob.IsCylSmooth c u) :
    UnforcedLeray.Sob.IsCylSmooth c (fun z => L (u z)) :=
  { smooth := L.contDiff.comp hu.smooth
    periodic := fun z => by
      rw [hu.periodic z]
    bounded := by
      obtain ⟨R, hR⟩ := hu.bounded
      exact ⟨R, fun z hz => by rw [hR z hz, map_zero]⟩ }

theorem isCylSmooth_pair {c : ℝ} {a b : Plane → ℝ}
    (ha : UnforcedLeray.Sob.IsCylSmooth c a) (hb : UnforcedLeray.Sob.IsCylSmooth c b) :
    UnforcedLeray.Sob.IsCylSmooth c (fun z => (a z, b z)) :=
  { smooth := ha.smooth.prodMk hb.smooth
    periodic := fun z => by
      rw [ha.periodic z, hb.periodic z]
    bounded := by
      obtain ⟨R1, hR1⟩ := ha.bounded
      obtain ⟨R2, hR2⟩ := hb.bounded
      refine ⟨max R1 R2, fun z hz => ?_⟩
      have h1 := hR1 z (lt_of_le_of_lt (le_max_left _ _) hz)
      have h2 := hR2 z (lt_of_le_of_lt (le_max_right _ _) hz)
      rw [h1, h2]
      rfl }

theorem isCylSmooth_lapS {c : ℝ} {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    UnforcedLeray.Sob.IsCylSmooth c (lapS f) := by
  have h1 : UnforcedLeray.Sob.IsCylSmooth c (fun z => fderiv ℝ f z (1, 0)) := hf.dir (1, 0)
  have h2 : UnforcedLeray.Sob.IsCylSmooth c (fun z => fderiv ℝ f z (0, 1)) := hf.dir (0, 1)
  have h3 := h1.dir (1, 0)
  have h4 := h2.dir (0, 1)
  have hsum : UnforcedLeray.Sob.IsCylSmooth c (fun z =>
      fderiv ℝ (fun w => fderiv ℝ f w (1, 0)) z (1, 0) +
        fderiv ℝ (fun w => fderiv ℝ f w (0, 1)) z (0, 1)) :=
    { smooth := h3.smooth.add h4.smooth
      periodic := fun z => by
        rw [h3.periodic z, h4.periodic z]
      bounded := by
        obtain ⟨R1, hR1⟩ := h3.bounded
        obtain ⟨R2, hR2⟩ := h4.bounded
        refine ⟨max R1 R2, fun z hz => ?_⟩
        have e1 := hR1 z (lt_of_le_of_lt (le_max_left _ _) hz)
        have e2 := hR2 z (lt_of_le_of_lt (le_max_right _ _) hz)
        rw [e1, e2, add_zero] }
  have hd : Differentiable ℝ f := hf.smooth.differentiable (by simp)
  have hd1 : Differentiable ℝ (fun w => fderiv ℝ f w (1, 0)) := h1.smooth.differentiable (by simp)
  have hd2 : Differentiable ℝ (fun w => fderiv ℝ f w (0, 1)) := h2.smooth.differentiable (by simp)
  have hdq : UnforcedLeray.Cyl.partialQ f = fun w => fderiv ℝ f w (1, 0) :=
    funext fun w => UnforcedLeray.Cyl.partialQ_eq_fderiv hd w
  have hdη : UnforcedLeray.Cyl.partialEta f = fun w => fderiv ℝ f w (0, 1) :=
    funext fun w => UnforcedLeray.Cyl.partialEta_eq_fderiv hd w
  have e : lapS f = fun z =>
      fderiv ℝ (fun w => fderiv ℝ f w (1, 0)) z (1, 0) +
        fderiv ℝ (fun w => fderiv ℝ f w (0, 1)) z (0, 1) := by
    funext z
    unfold lapS
    rw [hdq, hdη, UnforcedLeray.Cyl.partialQ_eq_fderiv hd1 z,
      UnforcedLeray.Cyl.partialEta_eq_fderiv hd2 z]
  rw [e]
  exact hsum

end LapCellTestAux

open LapCellTestAux in
theorem leafLapCellTestCH_proof : LeafLapCellTestCH := by
  intro c ψ hψ
  have hS := isCylSmooth_of_cellTest hψ
  have h0 : UnforcedLeray.Sob.IsCylSmooth c (fun w => ψ w 0) :=
    isCylSmooth_clm (EuclideanSpace.proj (0 : Fin 2)) hS
  have h1 : UnforcedLeray.Sob.IsCylSmooth c (fun w => ψ w 1) :=
    isCylSmooth_clm (EuclideanSpace.proj (1 : Fin 2)) hS
  have hV : UnforcedLeray.Sob.IsCylSmooth c (vecLaplacian ψ) :=
    isCylSmooth_clm toVecL.toContinuousLinearMap
      (isCylSmooth_pair (isCylSmooth_lapS h0) (isCylSmooth_lapS h1))
  refine ⟨hV.smooth, ?_, hV.bounded⟩
  intro z
  have e : (z.1 + c, z.2) = z + ((c : ℝ), (0 : ℝ)) := by ext <;> simp
  rw [e]
  exact hV.periodic z

end UnforcedLeray.Short.PartI
