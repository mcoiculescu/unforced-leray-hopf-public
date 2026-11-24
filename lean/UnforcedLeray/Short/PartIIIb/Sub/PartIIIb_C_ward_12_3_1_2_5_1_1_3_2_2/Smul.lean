import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2.Jets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2.DerivBoundAux
import UnforcedLeray.Units.B0412.Action
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Product-rule and coordinate-projection helpers for `inletSrcDerivBound`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Jets

open UnforcedLeray UnforcedLeray.PhaseSpace

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem norm_fderiv_smul_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] {f : X → 𝕜} {g : X → W} {y : X}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) (v : X) :
    ‖fderiv ℝ (fun z => f z • g z) y v‖ ≤ ‖f y‖ * ‖fderiv ℝ g y v‖ + ‖fderiv ℝ f y v‖ * ‖g y‖ := by
  have hh : HasFDerivAt (fun z => f z • g z) (f y • fderiv ℝ g y + (fderiv ℝ f y).smulRight (g y)) y :=
    hf.hasFDerivAt.smul hg.hasFDerivAt
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  refine (norm_add_le _ _).trans (add_le_add (norm_smul_le _ _) (norm_smul_le _ _))

/-- Coordinate of a derivative. -/
theorem fderiv_coord {𝕜 : Type*} [RCLike 𝕜] {f : X → EuclideanSpace 𝕜 (Fin 3)} {y : X}
    (hf : DifferentiableAt ℝ f y) (k : Fin 3) (v : X) :
    fderiv ℝ (fun z => f z k) y v = fderiv ℝ f y v k := by
  have h := (((EuclideanSpace.proj k : EuclideanSpace 𝕜 (Fin 3) →L[𝕜] 𝕜).restrictScalars ℝ).hasFDerivAt.comp
    y hf.hasFDerivAt).fderiv
  have h2 := congrArg (fun A => A v) h
  have e : (fun z => f z k) = ((EuclideanSpace.proj k : EuclideanSpace 𝕜 (Fin 3) →L[𝕜] 𝕜).restrictScalars ℝ) ∘ f := rfl
  rw [e]
  simpa using h2

theorem abs_coord_le {𝕜 : Type*} [RCLike 𝕜] (w : EuclideanSpace 𝕜 (Fin 3)) (k : Fin 3) :
    ‖w k‖ ≤ ‖w‖ := PiLp.norm_apply_le w k

theorem norm_single_one (k : Fin 3) : ‖(EuclideanSpace.single k (1 : ℝ) : UnforcedLeray.Space)‖ = 1 := by
  simp

/-- `realC` as a continuous linear map. -/
def realCL : UnforcedLeray.Space →L[ℝ] UnforcedLeray.PhaseSpace.CVec3 :=
  ∑ i : Fin 3, (EuclideanSpace.proj i : UnforcedLeray.Space →L[ℝ] ℝ).smulRight
    (EuclideanSpace.single i (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3)

theorem realCL_apply (x : UnforcedLeray.Space) : realCL x = UnforcedLeray.B0412.realC x := by
  simp [realCL, UnforcedLeray.B0412.realC, Complex.coe_smul]

theorem norm_realC (x : UnforcedLeray.Space) : ‖UnforcedLeray.B0412.realC x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [UnforcedLeray.B0412.realC_apply]

theorem fderiv_realC {R : X → UnforcedLeray.Space} {y : X} (hR : DifferentiableAt ℝ R y) (v : X) :
    fderiv ℝ (fun z => UnforcedLeray.B0412.realC (R z)) y v =
      UnforcedLeray.B0412.realC (fderiv ℝ R y v) := by
  have e : (fun z => UnforcedLeray.B0412.realC (R z)) = fun z => realCL (R z) := by
    funext z; rw [realCL_apply]
  have hh : HasFDerivAt (fun z => realCL (R z)) (realCL.comp (fderiv ℝ R y)) y :=
    realCL.hasFDerivAt.comp y hR.hasFDerivAt
  rw [e, hh.fderiv, ← realCL_apply]
  rfl

theorem fderiv_ofReal_coord {R : X → UnforcedLeray.Space} {y : X} (hR : DifferentiableAt ℝ R y)
    (k : Fin 3) (v : X) :
    fderiv ℝ (fun z => ((R z k : ℝ) : ℂ)) y v = ((fderiv ℝ R y v k : ℝ) : ℂ) := by
  have h1 : DifferentiableAt ℝ (fun z => R z k) y := by
    have := (((EuclideanSpace.proj k : UnforcedLeray.Space →L[ℝ] ℝ)).differentiableAt (x := R y)).comp y hR
    exact this
  have h := (Complex.ofRealCLM.hasFDerivAt.comp y h1.hasFDerivAt).fderiv
  have h2 := congrArg (fun A => A v) h
  simp only [ContinuousLinearMap.comp_apply] at h2
  have e : (fun z => ((R z k : ℝ) : ℂ)) = Complex.ofRealCLM ∘ (fun z => R z k) := rfl
  rw [e, h2, fderiv_coord hR]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.Jets

end
