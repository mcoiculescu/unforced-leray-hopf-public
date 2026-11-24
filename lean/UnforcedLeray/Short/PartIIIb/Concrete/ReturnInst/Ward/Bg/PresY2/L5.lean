import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs

/-!
# Equivariance of the pressure gradient (source 4138-4145, 117-121)

The profile equation `D₀U + U·∇U + ∇p = 0` fixes `∇p` pointwise, and an axisymmetric
background without swirl commutes with the isometries fixing `e₃`. Hence `∇p` commutes with
them as well.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **The pressure gradient of a symmetric exact profile is equivariant** (source 4138-4145). -/
theorem presGradEquivar_of (hL : PhysLapEquivar) : PresGradEquivar := by
  intro ν P U pres hU hax g hg τ y
  -- the field commutes with `g` at every phase
  have hzt : ∀ t z, U t (g z) = g (U t z) := by
    intro t z
    have h := hax t g hg (g z)
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    exact h.symm
  let Gc : Space →L[ℝ] Space := g.toContinuousLinearEquiv.toContinuousLinearMap
  have hGc : ∀ v, Gc v = g v := fun v => rfl
  have hUd2 : Differentiable ℝ (fun x : ℝ × Space => U x.1 x.2) :=
    hU.smoothU.differentiable (by simp)
  have hUt : ∀ t, DifferentiableAt ℝ (fun s => U s y) t := fun t => by
    have hA : DifferentiableAt ℝ (fun s : ℝ => ((s, y) : ℝ × Space)) t :=
      DifferentiableAt.prodMk (differentiableAt_id (𝕜 := ℝ) (E := ℝ)) (differentiableAt_const y)
    exact (hUd2 (t, y)).comp t hA
  -- `U τ` is smooth in space
  have hUs : ContDiff ℝ 2 (U τ) :=
    (hU.smoothU.comp (contDiff_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := Space) τ)).of_le
      (by simp)
  have hUsd : ∀ z, DifferentiableAt ℝ (U τ) z := fun z =>
    (hUs.differentiable (by norm_num)) z
  -- derivative in space: `fderiv (U τ) (g y) (g v) = g (fderiv (U τ) y v)`
  have hfd : ∀ v, fderiv ℝ (U τ) (g y) (g v) = g (fderiv ℝ (U τ) y v) := by
    intro v
    have h1 : HasFDerivAt (fun z => U τ (g z)) ((fderiv ℝ (U τ) (g y)).comp Gc) y :=
      (hUsd (g y)).hasFDerivAt.comp y Gc.hasFDerivAt
    have h2 : HasFDerivAt (fun z => g (U τ z)) (Gc.comp (fderiv ℝ (U τ) y)) y :=
      Gc.hasFDerivAt.comp y (hUsd y).hasFDerivAt
    have hfun : (fun z => g (U τ z)) = fun z => U τ (g z) :=
      funext fun z => (hzt τ z).symm
    have h1' : HasFDerivAt (fun z => g (U τ z)) ((fderiv ℝ (U τ) (g y)).comp Gc) y := by
      rw [hfun]
      exact h1
    have heq := h1'.unique h2
    have := congrArg (fun L : Space →L[ℝ] Space => L v) heq
    simpa [hGc] using this
  -- time derivative
  have hdt : deriv (fun t => U t (g y)) τ = g (deriv (fun t => U t y) τ) := by
    have h := (Gc.hasFDerivAt (x := U τ y)).comp_hasDerivAt τ (hUt τ).hasDerivAt
    have hfun : (fun t => U t (g y)) = Gc ∘ (fun t => U t y) :=
      funext fun t => by simp [hGc, hzt]
    rw [hfun, h.deriv, hGc]
  -- the Laplacian
  have hlap : physLap (U τ) (g y) = g (physLap (U τ) y) :=
    hL (U τ) g hUs (fun z => hzt τ z) y
  have hUgy : U τ (g y) = g (U τ y) := hzt τ y
  -- the linear part `D_0 U` is equivariant
  have hD : physDmu ν 0 U τ (g y) = g (physDmu ν 0 U τ y) := by
    unfold physDmu
    rw [hdt, hfd y, hlap, hUgy]
    simp only [map_sub, map_add, map_smul]
  -- the convective term is equivariant
  have hB : fderiv ℝ (U τ) (g y) (U τ (g y)) = g (fderiv ℝ (U τ) y (U τ y)) := by
    rw [hUgy, hfd]
  -- the profile equation at `g y`, compared with `g` applied to the equation at `y`
  have e1 := hU.equation τ (g y)
  rw [hD, hB] at e1
  have h0 : g (physDmu ν 0 U τ y + fderiv ℝ (U τ) y (U τ y) + physGrad (pres τ) y) = 0 := by
    rw [hU.equation τ y, map_zero]
  rw [map_add, map_add] at h0
  exact add_left_cancel (e1.trans h0.symm)

end UnforcedLeray.Short.PartIIIb.Concrete
