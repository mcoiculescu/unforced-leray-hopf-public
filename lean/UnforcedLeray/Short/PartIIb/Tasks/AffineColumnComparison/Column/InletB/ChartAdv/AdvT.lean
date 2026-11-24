import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_4

/-!
# Part II-b, task `PartII-b:G4/3/4/1/A` (`chartAdv_advT`)

Source of record: `the November 2 reference manuscript`, SP 1919-1921, 2007-2012.
`advT u Φ x = ∑ₖ uₖ ∂ₖΦ x`. For the real lift `Φ = realC ∘ Nv d`, the spatial derivative
`∂ₖΦ(τ,y)` is `realC (D(Nv d τ)(y) eₖ)` (the slice `y ↦ Nv d τ y` at fixed `τ`), and the
coefficients `uₖ` are the components of `realC (Nv b τ y)`. Linearity of `D(Nv d τ)(y)` then
gives `realC (D(Nv d τ)(y) (Nv b τ y)) = realC (advection (Nv b τ) (Nv d τ) y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- Real vectors of `ℝ³` seen in `ℂ³`, as a real-linear map. -/
private def realCLa : UnforcedLeray.Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => UnforcedLeray.B0412.realC x
      map_add' := fun x y => by ext i; simp [UnforcedLeray.B0412.realC_apply]
      map_smul' := fun c x => by
        ext i; simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul] }

/-- **`PartII-b:G4/3/4/1/A`**: the advection test of the ring lift is the lift of the advection. -/
theorem chartAdv_advT (R : ℝ) (b d : Coord → Axi.Merid) (τ : ℝ) (y : Space)
    (hd : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.Nv R d x.1 x.2) (τ, y)) :
    advT (fun x => realC (Axi.Nv R b x.1 x.2)) (fun x => realC (Axi.Nv R d x.1 x.2)) (τ, y) =
      realC (Axi.advection (Axi.Nv R b τ) (Axi.Nv R d τ) y) := by
  have hD : ∀ j : Fin 3, dy j (fun x : ℝ × Space => realC (Axi.Nv R d x.1 x.2)) (τ, y) =
      realC (fderiv ℝ (Axi.Nv R d τ) y (coordinateVector j)) := by
    intro j
    have h1 : HasFDerivAt (fun x : ℝ × Space => realC (Axi.Nv R d x.1 x.2))
        (realCLa.comp (fderiv ℝ (fun x : ℝ × Space => Axi.Nv R d x.1 x.2) (τ, y))) (τ, y) :=
      realCLa.hasFDerivAt.comp (τ, y) hd.hasFDerivAt
    have h2 : HasFDerivAt (Axi.Nv R d τ)
        ((fderiv ℝ (fun x : ℝ × Space => Axi.Nv R d x.1 x.2) (τ, y)).comp
          ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) y :=
      hd.hasFDerivAt.comp y ((hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y))
    show fderiv ℝ (fun x : ℝ × Space => realC (Axi.Nv R d x.1 x.2)) (τ, y)
        (0, coordinateVector j) = _
    rw [h1.fderiv, h2.fderiv]
    rfl
  have hvec : ∀ v : Space, v = ∑ k : Fin 3, v k • coordinateVector k := by
    intro v
    ext j
    simp [coordinateVector, Pi.single_apply]
  have hreal_smul : ∀ (c : ℝ) (x : Space), realC (c • x) = (c : ℂ) • realC x := by
    intro c x
    ext i
    simp [realC_apply]
  have hsum : ∀ (f : Fin 3 → Space), realC (∑ k : Fin 3, f k) = ∑ k : Fin 3, realC (f k) :=
    fun f => map_sum realCLa f _
  have hw : fderiv ℝ (Axi.Nv R d τ) y (Axi.Nv R b τ y) =
      ∑ k : Fin 3, (Axi.Nv R b τ y) k • fderiv ℝ (Axi.Nv R d τ) y (coordinateVector k) := by
    conv_lhs => rw [hvec (Axi.Nv R b τ y)]
    rw [map_sum]
    simp [map_smul]
  show _ = realC (fderiv ℝ (Axi.Nv R d τ) y (Axi.Nv R b τ y))
  rw [hw]
  simp only [advT, hD, realC_apply]
  rw [hsum]
  simp only [hreal_smul]

end UnforcedLeray.Short.IIb
