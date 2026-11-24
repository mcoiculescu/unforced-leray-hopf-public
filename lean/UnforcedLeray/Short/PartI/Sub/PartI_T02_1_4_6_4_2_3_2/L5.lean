import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2

/-!
# Leaf `LeafVecLaplacianPartialsCH` (vector Laplacian as componentwise partials)

For a smooth `ψ : Plane → Vec`, the componentwise scalar Laplacian `Train.vecLaplacian ψ` equals
`∂_q ∂_q ψ + ∂_η ∂_η ψ`, since the coordinate projections commute with the classical partials.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open scoped ContDiff

/-- Coordinate projection commutes with the `q`-derivative of a differentiable `Vec`-valued line. -/
theorem deriv_coordVec_aux (g : ℝ → Vec) (hg : Differentiable ℝ g) (k : Fin 2) (x : ℝ) :
    deriv (fun t => g t k) x = deriv g x k := by
  have h := (hg x).hasDerivAt
  have h2 := (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt x h
  have h3 : (fun t => g t k) = (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) ∘ g := rfl
  rw [h3, h2.deriv]
  rfl

theorem partialQ_coordVec_aux (f : Plane → Vec) (hf : ∀ η : ℝ, Differentiable ℝ (fun q : ℝ => f (q, η)))
    (k : Fin 2) (z : Plane) :
    Cyl.partialQ f z k = Cyl.partialQ (fun w => f w k) z := by
  unfold Cyl.partialQ
  exact (deriv_coordVec_aux (fun q => f (q, z.2)) (hf z.2) k z.1).symm

theorem partialEta_coordVec_aux (f : Plane → Vec) (hf : ∀ q : ℝ, Differentiable ℝ (fun η : ℝ => f (q, η)))
    (k : Fin 2) (z : Plane) :
    Cyl.partialEta f z k = Cyl.partialEta (fun w => f w k) z := by
  unfold Cyl.partialEta
  exact (deriv_coordVec_aux (fun η => f (z.1, η)) (hf z.1) k z.2).symm

theorem slice_q_aux {f : Plane → Vec} (hf : Differentiable ℝ f) (η : ℝ) :
    Differentiable ℝ (fun q : ℝ => f (q, η)) :=
  hf.comp (differentiable_id.prodMk (differentiable_const η))

theorem slice_e_aux {f : Plane → Vec} (hf : Differentiable ℝ f) (q : ℝ) :
    Differentiable ℝ (fun η : ℝ => f (q, η)) :=
  hf.comp ((differentiable_const q).prodMk differentiable_id)

theorem partialQ_comp_coord_aux (f : Plane → Vec) (hf : Differentiable ℝ f) (k : Fin 2) :
    (fun w => Cyl.partialQ f w k) = Cyl.partialQ (fun w => f w k) :=
  funext fun z => partialQ_coordVec_aux f (fun η => slice_q_aux hf η) k z

theorem partialEta_comp_coord_aux (f : Plane → Vec) (hf : Differentiable ℝ f) (k : Fin 2) :
    (fun w => Cyl.partialEta f w k) = Cyl.partialEta (fun w => f w k) :=
  funext fun z => partialEta_coordVec_aux f (fun q => slice_e_aux hf q) k z

theorem leafVecLaplacianPartialsCH_proof : UnforcedLeray.Short.PartI.LeafVecLaplacianPartialsCH := by
  intro c ψ hψ
  have hC : ContDiff ℝ ∞ ψ := hψ.1
  have hd : Differentiable ℝ ψ := hC.differentiable (by simp)
  have hQ : ContDiff ℝ 1 (Cyl.partialQ ψ) := Cyl.contDiff_partialQ (n := 1) (hC.of_le (by simp))
  have hE : ContDiff ℝ 1 (Cyl.partialEta ψ) := Cyl.contDiff_partialEta (n := 1) (hC.of_le (by simp))
  have hQd : Differentiable ℝ (Cyl.partialQ ψ) := hQ.differentiable (by simp)
  have hEd : Differentiable ℝ (Cyl.partialEta ψ) := hE.differentiable (by simp)
  funext z
  refine UnforcedLeray.Train.Vec.ext ?_ ?_
  · have e1 : Cyl.partialQ (Cyl.partialQ ψ) z 0 = Cyl.partialQ (Cyl.partialQ (fun w => ψ w 0)) z := by
      rw [partialQ_coordVec_aux (Cyl.partialQ ψ) (fun η => slice_q_aux hQd η) 0 z,
        partialQ_comp_coord_aux ψ hd 0]
    have e2 : Cyl.partialEta (Cyl.partialEta ψ) z 0
        = Cyl.partialEta (Cyl.partialEta (fun w => ψ w 0)) z := by
      rw [partialEta_coordVec_aux (Cyl.partialEta ψ) (fun q => slice_e_aux hEd q) 0 z,
        partialEta_comp_coord_aux ψ hd 0]
    simp only [UnforcedLeray.Train.vecLaplacian, UnforcedLeray.Train.toVec_zero, PiLp.add_apply, e1, e2]
    rfl
  · have e1 : Cyl.partialQ (Cyl.partialQ ψ) z 1 = Cyl.partialQ (Cyl.partialQ (fun w => ψ w 1)) z := by
      rw [partialQ_coordVec_aux (Cyl.partialQ ψ) (fun η => slice_q_aux hQd η) 1 z,
        partialQ_comp_coord_aux ψ hd 1]
    have e2 : Cyl.partialEta (Cyl.partialEta ψ) z 1
        = Cyl.partialEta (Cyl.partialEta (fun w => ψ w 1)) z := by
      rw [partialEta_coordVec_aux (Cyl.partialEta ψ) (fun q => slice_e_aux hEd q) 1 z,
        partialEta_comp_coord_aux ψ hd 1]
    simp only [UnforcedLeray.Train.vecLaplacian, UnforcedLeray.Train.toVec_one, PiLp.add_apply, e1, e2]
    rfl

end UnforcedLeray.Short.PartI

end
