import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7` leaf: the pressure-gradient similarity scaling

Source of record: `the November 2 reference manuscript`, lines 1196-1263
(Proposition `sct:lift`: `p_raw = (R/r)^2 p`, and the similarity pressure of line 1263).
The Prop proved here is `SimGradScaling` of `Sub/R1_7.lean` (lines 153-160), unchanged:
for `π` differentiable at `(e^τ, e^{τ/2} y)`,
`gradT Q (τ, y) = realC (e^{3τ/2} • cartGrad (π (e^τ)) (e^{τ/2} y))`, where
`Q (τ, y) = (e^{τ/2})^2 π (e^τ, e^{τ/2} y)`.

Proof: the `y`-directional derivative of `Q` along `e_j` is computed along the line
`s ↦ (τ, y + s e_j)`, through the chain rule for `y ↦ e^{τ/2} y`, which gives
`e^{τ/2} (e^{τ/2})^2 ∂_j π`. The components are then compared with `cartGrad`.

No hypothesis is added, and the proof uses no placeholder or escape declaration.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-- Along a line `s ↦ x + s • v` through `x`, a scalar function differentiable at `x` has
derivative `Df(x) v` at `s = 0`. -/
theorem simGrad_spatial_deriv (f : Space → ℝ) (x v : Space) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f x v) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    have h := (hasDerivAt_id' (0 : ℝ)).smul_const v
    rw [one_smul] at h
    exact h
  have h2 : HasDerivAt (fun s : ℝ => x + s • v) v 0 := h1.const_add x
  have hy : x = (fun s : ℝ => x + s • v) 0 := by simp
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 hy

/-- **Scaling of the pressure gradient** (`SimGradScaling`, `Sub/R1_7.lean`, tex 1196-1263). -/
theorem simGradScaling : UnforcedLeray.Short.IIb.SimGradScaling := by
  unfold SimGradScaling
  intro pi tau y hdiff
  -- The scaling map `q ↦ (e^{q₁}, e^{q₁/2} q₂)` is smooth; compose with `hdiff`.
  have hPhi : DifferentiableAt ℝ
      (fun q : ℝ × Space => (Real.exp q.1, Real.exp (q.1 / 2) • q.2)) (tau, y) := by
    fun_prop
  have hFP := hdiff.comp (tau, y) hPhi
  have hcoef : DifferentiableAt ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2) ^ 2) (tau, y) := by
    fun_prop
  have hG : DifferentiableAt ℝ
      (fun q : ℝ × Space => UnforcedLeray.B0190.simProfile 2 pi q.1 q.2) (tau, y) := by
    unfold UnforcedLeray.B0190.simProfile
    exact hcoef.smul hFP
  have hφ0 : DifferentiableAt ℝ
      (fun q : ℝ × Space => ((UnforcedLeray.B0190.simProfile 2 pi q.1 q.2 : ℝ) : ℂ)) (tau, y) :=
    Complex.ofRealCLM.differentiableAt.comp (tau, y) hG
  -- Spatial differentiability of `π(e^τ, ·)` at `e^{τ/2} y`.
  have hpr : DifferentiableAt ℝ (fun x' : Space => (Real.exp tau, x')) (Real.exp (tau / 2) • y) :=
    (differentiableAt_const (Real.exp tau)).prodMk differentiableAt_id
  have hπt : DifferentiableAt ℝ (pi (Real.exp tau)) (Real.exp (tau / 2) • y) := by
    have h := hdiff.comp (Real.exp (tau / 2) • y) hpr
    exact h
  set φ : ℝ × Space → ℂ :=
    fun q : ℝ × Space => ((UnforcedLeray.B0190.simProfile 2 pi q.1 q.2 : ℝ) : ℂ)
  -- Directional derivatives of `φ` along `(0, e_j)`.
  have hdir : ∀ j : Fin 3, fderiv ℝ φ (tau, y) (0, coordinateVector j) =
      ((Real.exp (tau / 2) ^ 3 * fderiv ℝ (pi (Real.exp tau)) (Real.exp (tau / 2) • y)
        (coordinateVector j) : ℝ) : ℂ) := by
    intro j
    -- (1) the line `s ↦ (τ, y + s e_j)` in the phase variables
    have h1 : HasDerivAt (fun s : ℝ => s • coordinateVector j) (coordinateVector j) 0 := by
      have h := (hasDerivAt_id' (0 : ℝ)).smul_const (coordinateVector j)
      rw [one_smul] at h
      exact h
    have h2 : HasDerivAt (fun s : ℝ => y + s • coordinateVector j) (coordinateVector j) 0 :=
      h1.const_add y
    have hc0 : HasDerivAt (fun _ : ℝ => tau) 0 (0 : ℝ) := hasDerivAt_const _ _
    have hline : HasDerivAt (fun s : ℝ => ((tau, y + s • coordinateVector j) : ℝ × Space))
        ((0 : ℝ), coordinateVector j) 0 := hc0.prodMk h2
    have hy : ((tau, y) : ℝ × Space) =
        (fun s : ℝ => ((tau, y + s • coordinateVector j) : ℝ × Space)) 0 := by
      simp
    have hφline := hφ0.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hy
    -- (2) the chain rule: `e^{τ/2} y + s e^{τ/2} e_j` is the scaled line
    have hsplit : ∀ s : ℝ, Real.exp (tau / 2) • (y + s • coordinateVector j)
        = Real.exp (tau / 2) • y + s • (Real.exp (tau / 2) • coordinateVector j) := by
      intro s
      rw [smul_add, smul_comm]
    have hd1 := simGrad_spatial_deriv (pi (Real.exp tau)) (Real.exp (tau / 2) • y)
      (Real.exp (tau / 2) • coordinateVector j) hπt
    have hd2 : HasDerivAt
        (fun s : ℝ => pi (Real.exp tau) (Real.exp (tau / 2) • (y + s • coordinateVector j)))
        (fderiv ℝ (pi (Real.exp tau)) (Real.exp (tau / 2) • y)
          (Real.exp (tau / 2) • coordinateVector j)) 0 := by
      simp only [hsplit]
      exact hd1
    have hsm : fderiv ℝ (pi (Real.exp tau)) (Real.exp (tau / 2) • y)
          (Real.exp (tau / 2) • coordinateVector j)
        = Real.exp (tau / 2) * fderiv ℝ (pi (Real.exp tau)) (Real.exp (tau / 2) • y)
          (coordinateVector j) := by
      rw [map_smul, smul_eq_mul]
    rw [hsm] at hd2
    -- (3) the real profile `s ↦ (e^{τ/2})^2 π(e^τ, e^{τ/2}(y + s e_j))`
    have e3 : Real.exp (tau / 2) ^ 3 * fderiv ℝ (pi (Real.exp tau)) (Real.exp (tau / 2) • y)
          (coordinateVector j)
        = Real.exp (tau / 2) ^ 2 • (Real.exp (tau / 2) *
          fderiv ℝ (pi (Real.exp tau)) (Real.exp (tau / 2) • y) (coordinateVector j)) := by
      rw [smul_eq_mul]
      ring
    have hreal : HasDerivAt
        (fun s : ℝ => UnforcedLeray.B0190.simProfile 2 pi tau (y + s • coordinateVector j))
        (Real.exp (tau / 2) ^ 3 * fderiv ℝ (pi (Real.exp tau)) (Real.exp (tau / 2) • y)
          (coordinateVector j)) 0 := by
      rw [e3]
      unfold UnforcedLeray.B0190.simProfile
      exact hd2.const_smul (Real.exp (tau / 2) ^ 2)
    -- (4) identify the directional derivative of `φ` with the real one
    have hc := hreal.ofReal_comp
    exact hφline.unique hc
  -- Assemble `gradT` and compare componentwise with `realC (e^{3τ/2} • cartGrad)`.
  simp only [UnforcedLeray.PhaseSpace.gradT, UnforcedLeray.PhaseSpace.dy, hdir]
  rw [Fin.sum_univ_three]
  ext i
  fin_cases i <;>
    simp [UnforcedLeray.B0412.realC_apply, cartGrad]

end UnforcedLeray.Short.IIb

end
