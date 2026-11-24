import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.TrainDiff

/-!
# Part II-b, task `PartII-b:G4/3/8/2` (`FlatColumnReal`)

Source of record: `the November 2 reference manuscript` (SP), lines 2370-2382
(`ε = 0`). The complex flat column `flatColumn p i` equals the lift of the real flat column
`flatReal p i` on `s > 0`. The only nontrivial point is that the partial derivatives
`fderiv ℝ (fun z => v s z i) (1,0)` and `(0,1)` appearing in `flatK` are the components of
`Axi.dQ (trainProf p) x` and `Axi.dEta (trainProf p) x`, which holds because `trainProf p` is
differentiable at `x` (`TrainDiff`, task `PartII-b:G4/3/8/1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- A partial derivative in the plane variable `z = (q, η)` of a component of a differentiable
chart profile is the corresponding component of the directional derivative. -/
theorem flatPartial_comp_eq (F : Coord → Axi.Merid) (x : Coord) (hF : DifferentiableAt ℝ F x)
    (j : Fin 2) (w : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => F (x.1, z) j) x.2 w = fderiv ℝ F x (0, w) j := by
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => ((x.1, z) : Coord))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x.2 :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have h2 : HasFDerivAt (fun z : ℝ × ℝ => F (x.1, z))
      ((fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x.2 :=
    hF.hasFDerivAt.comp x.2 h1
  have h3 : HasFDerivAt (fun z : ℝ × ℝ => F (x.1, z) j)
      ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
        ((fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)))) x.2 :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp x.2 h2
  rw [h3.fderiv]
  simp [ContinuousLinearMap.inr_apply]

/-- **The flat column is the lift of `flatReal`** (SP 2370-2382, `ε = 0`). -/
theorem flatColumnReal : UnforcedLeray.Short.IIb.FlatColumnReal := by
  intro Sig lam q hSig hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg i x hx
  have hT : DifferentiableAt ℝ (trainProf p) x :=
    (trainDiff p d dm dp hreg.1 x hx).1
  have hQ : ∀ j : Fin 2, fderiv ℝ (fun z : ℝ × ℝ => p.train.v x.1 z j) x.2 (1, 0) =
      Axi.dQ (trainProf p) x j := fun j =>
    flatPartial_comp_eq (trainProf p) x hT j (1, 0)
  have hE : ∀ j : Fin 2, fderiv ℝ (fun z : ℝ × ℝ => p.train.v x.1 z j) x.2 (0, 1) =
      Axi.dEta (trainProf p) x j := fun j =>
    flatPartial_comp_eq (trainProf p) x hT j (0, 1)
  ext j
  simp only [flatColumn, flatK, flatReal, flatB, cplx, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, PiLp.toLp_apply, smul_eq_mul]
  rw [hQ j, hE j]
  simp only [trainProf]
  push_cast
  ring

end UnforcedLeray.Short.IIb

end
