import UnforcedLeray.Lib.SobolevC.CylSmooth

/-!
# Smooth cylinder fields under continuous linear coordinate maps

The tensor heat estimates use a Plane-valued representative, while the dense cylinder Sobolev
carrier is Hilbert-valued. These lemmas transfer smooth periodic compact-axial representatives
through the actual finite-dimensional coordinate map and commute every derivative word with that
map.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Sob
open UnforcedLeray.GaussianVortex (Plane)

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Iterated directional derivatives commute with a continuous linear map on the value space. -/
theorem iterD_postcomp_clm (L : F →L[ℝ] G) {f : E → F}
    (hf : ContDiff ℝ ∞ f) (vs : List E) :
    iterD vs (fun x => L (f x)) = fun x => L (iterD vs f x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      funext x
      rw [iterD_cons, ih]
      have hd : DifferentiableAt ℝ (iterD vs f) x :=
        (contDiff_iterD hf vs).differentiable (by simp) x
      change fderiv ℝ (L ∘ iterD vs f) x v =
        L (fderiv ℝ (iterD vs f) x v)
      rw [fderiv_comp x L.differentiableAt hd, L.fderiv]
      rfl

/-- Smooth cylinder fields are closed under subtraction. -/
theorem isCylSmooth_sub {c : ℝ} {f g : Plane → F}
    (hf : IsCylSmooth c f) (hg : IsCylSmooth c g) :
    IsCylSmooth c (fun x => f x - g x) := by
  refine ⟨hf.smooth.sub hg.smooth, fun x => ?_, ?_⟩
  · rw [hf.periodic x, hg.periodic x]
  · obtain ⟨R, hR⟩ := hf.bounded
    obtain ⟨S, hS⟩ := hg.bounded
    refine ⟨max R S, fun x hx => ?_⟩
    rw [hR x (lt_of_le_of_lt (le_max_left R S) hx),
      hS x (lt_of_le_of_lt (le_max_right R S) hx), sub_zero]

/-- A continuous linear map preserves smooth periodic cylinder fields vanishing at axial infinity. -/
theorem isCylSmooth_postcomp_clm {c : ℝ} {f : Plane → F}
    (hf : IsCylSmooth c f) (L : F →L[ℝ] G) :
    IsCylSmooth c (fun x => L (f x)) := by
  refine ⟨L.contDiff.comp hf.smooth, fun x => ?_, ?_⟩
  · exact congrArg L (hf.periodic x)
  · obtain ⟨R, hR⟩ := hf.bounded
    refine ⟨R, fun x hx => ?_⟩
    rw [hR x hx, map_zero]

/-- The iterated derivative of a linearly remapped smooth cylinder field is the remapping of the
actual derivative word. -/
theorem iterD_isCylSmooth_postcomp_clm {c : ℝ} {f : Plane → F}
    (hf : IsCylSmooth c f) (L : F →L[ℝ] G) (vs : List Plane) :
    iterD vs (fun x => L (f x)) = fun x => L (iterD vs f x) :=
  iterD_postcomp_clm L hf.smooth vs

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.iterD_postcomp_clm
#print axioms UnforcedLeray.HeatCylinder.isCylSmooth_postcomp_clm
#print axioms UnforcedLeray.HeatCylinder.isCylSmooth_sub
