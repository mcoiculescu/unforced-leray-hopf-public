import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Algebra

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2/1`: mixed partials of smooth fields commute (`stAdjComm`)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
(the energies are differentiated: `∂^w` commutes with `Δ` and with `∂_l`).

For smooth complex `H`, `pdCx k (pdCx l H) y = fderiv (fderiv H) y (dir k) (dir l)` (the derivative of
the evaluation `y ↦ fderiv H y (dir l)` at a fixed vector), and the second derivative of a `C²` map is
symmetric (`ContDiffAt.isSymmSndFDerivAt`).  Then induction on the word.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The derivative of an evaluation `y ↦ A y v` of a CLM-valued map at a fixed vector. -/
theorem sac_fderiv_apply {A : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)} {z : ℝ × ℝ}
    (hA : DifferentiableAt ℝ A z) (v e : ℝ × ℝ) :
    fderiv ℝ (fun y => A y v) z e = fderiv ℝ A z e v := by
  have hev := (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp z hA.hasFDerivAt
  rw [show (fun y => A y v) = (ContinuousLinearMap.apply ℝ ℂ v) ∘ A from rfl, hev.fderiv]
  rfl

/-- `pdCx k (pdCx l H) y` is the second derivative, applied to the coordinate directions. -/
theorem sac_pdCx_pdCx {H : ℝ × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (k l : Fin 2) (y : ℝ × ℝ) :
    pdCx k (pdCx l H) y = fderiv ℝ (fderiv ℝ H) y (B0579.dir k) (B0579.dir l) := by
  have hH' : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  show fderiv ℝ (fun y => fderiv ℝ H y (B0579.dir l)) y (B0579.dir k) = _
  rw [sac_fderiv_apply (hH' y)]

theorem sac_comm {H : ℝ × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (k l : Fin 2) :
    pdCx k (pdCx l H) = pdCx l (pdCx k H) := by
  funext y
  rw [sac_pdCx_pdCx hH k l y, sac_pdCx_pdCx hH l k y]
  have hsymm : IsSymmSndFDerivAt ℝ H y := hH.contDiffAt.isSymmSndFDerivAt (by simp)
  exact hsymm (B0579.dir k) (B0579.dir l)

/-- **(1) Mixed partials of smooth fields commute** (SP 3060-3071). -/
theorem stAdjComm : UnforcedLeray.Short.IIIa.StAdjComm := by
  intro F hF w l
  induction w with
  | nil => rfl
  | cons k w ih =>
    rw [show adjSpatial (k :: w) (pdCx l F) = pdCx k (adjSpatial w (pdCx l F)) from rfl,
      show adjSpatial (k :: w) F = pdCx k (adjSpatial w F) from rfl, ih,
      sac_comm (st_contDiff_adjSpatial hF w) k l]

end UnforcedLeray.Short.IIIa
