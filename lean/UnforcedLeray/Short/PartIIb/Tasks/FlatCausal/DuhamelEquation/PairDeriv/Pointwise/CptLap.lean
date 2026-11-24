import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_5_1

/-!
# Part II-b, task `PartII-b:T12/7/5/1/2` (`DeqpdCptLap`): chain rule for the planar Laplacian

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
For a smooth `Φ` on `Coord = ℝ × (ℝ × ℝ)`, the slice `y ↦ Φ(s, y)` has planar Laplacian
`(cpd 1 ∘ cpd 1 + cpd 2 ∘ cpd 2) Φ (s, y)`, since `fderiv` of `y ↦ Φ(s, y)` in direction `v` is
`fderiv Φ (s, y) (0, v)` and `cdir 1 = (0, (1, 0))`, `cdir 2 = (0, (0, 1))`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Chain rule for the slice `y ↦ g(s, y)` of a function `g` on `Coord`. -/
theorem deqpc_slice_fderiv (g : Coord → ℝ) (s : ℝ) (y : ℝ × ℝ)
    (hg : DifferentiableAt ℝ g (s, y)) (v : ℝ × ℝ) :
    fderiv ℝ (fun y' : ℝ × ℝ => g (s, y')) y v = fderiv ℝ g (s, y) (0, v) := by
  have he : HasFDerivAt (fun y' : ℝ × ℝ => ((s, y') : Coord))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
  have hc : HasFDerivAt (fun y' : ℝ × ℝ => g (s, y'))
      ((fderiv ℝ g (s, y)).comp ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))))
      y := (hg.hasFDerivAt).comp y he
  rw [hc.fderiv]
  simp

/-- Planar Laplacian of a slice of a smooth function on `Coord`. -/
theorem deqpc_slice_lap (Φ : Coord → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (s : ℝ) (y : ℝ × ℝ) :
    planarLap (fun y' : ℝ × ℝ => Φ (s, y')) y =
      cpd 1 (fun x => cpd 1 Φ x) (s, y) + cpd 2 (fun x => cpd 2 Φ x) (s, y) := by
  have hd : ∀ x : Coord, DifferentiableAt ℝ Φ x := fun x =>
    (hΦ.differentiable (by simp)) x
  have hD : ∀ j : Fin 3, Differentiable ℝ (fun x : Coord => cpd j Φ x) := by
    intro j
    have h1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (m := 1) (by simp)
    exact ((h1.clm_apply contDiff_const).differentiable (by simp))
  have h1 : (fun y' : ℝ × ℝ => fderiv ℝ (fun y'' : ℝ × ℝ => Φ (s, y'')) y' (1, 0)) =
      fun y' => cpd 1 Φ (s, y') := by
    funext y'
    rw [deqpc_slice_fderiv Φ s y' (hd _) (1, 0)]
    rfl
  have h2 : (fun y' : ℝ × ℝ => fderiv ℝ (fun y'' : ℝ × ℝ => Φ (s, y'')) y' (0, 1)) =
      fun y' => cpd 2 Φ (s, y') := by
    funext y'
    rw [deqpc_slice_fderiv Φ s y' (hd _) (0, 1)]
    rfl
  have h1' : fderiv ℝ (fun y' : ℝ × ℝ => cpd 1 Φ (s, y')) y (1, 0) =
      cpd 1 (fun x => cpd 1 Φ x) (s, y) := by
    rw [deqpc_slice_fderiv (fun x => cpd 1 Φ x) s y (hD 1 (s, y)) (1, 0)]
    rfl
  have h2' : fderiv ℝ (fun y' : ℝ × ℝ => cpd 2 Φ (s, y')) y (0, 1) =
      cpd 2 (fun x => cpd 2 Φ x) (s, y) := by
    rw [deqpc_slice_fderiv (fun x => cpd 2 Φ x) s y (hD 2 (s, y)) (0, 1)]
    rfl
  unfold planarLap
  rw [h1, h2, h1', h2']

/-- **Task `PartII-b:T12/7/5/1/2`**: the planar Laplacian of `y ↦ Ψ_i(s, y)` is
`(cpd 1 ∘ cpd 1 + cpd 2 ∘ cpd 2) Ψ_i (s, y)` (SP 1923-1927). -/
theorem deqpdCptLap : UnforcedLeray.Short.IIb.DeqpdCptLap := by
  intro Ψ hΨ i s y
  exact deqpc_slice_lap (fun z => Ψ z i) (hΨ.smooth i).smooth s y

end UnforcedLeray.Short.IIb
