import UnforcedLeray.Short.PartIIb.Sub.R1_7
import UnforcedLeray.Lib.AxisymmetricB.Bridge

/-!
# Part II-b, task `PartII-b:R1/7/1`: the drift scaling `SimT0Scaling`

Target: `UnforcedLeray.Short.IIb.SimT0Scaling` (`Sub/R1_7.lean`). Source of record:
`the November 2 reference manuscript` lines 1196-1263 (the lift and the
residual `F_R = s^{3/2} r`), and `paper/main.tex` 2917 (`simProfile k u τ y = e^{kτ/2} u(e^τ, e^{τ/2} y)`).

Notation: `t = e^τ`, `E = e^{τ/2}`, `x = E • y`, `F q = u q.1 q.2`, and `W q = realC (E(q.1) • F(e^{q.1}, E(q.1) • q.2))`.
Along the lines `s ↦ (τ + s, y)` and `s ↦ (τ, y + s • v)` the chain rule gives

* `∂_τ W = realC (E • (t • ∂₁F + ½ • ∂₂F x) + ½E • F)`, where `∂₁F = fderiv F (t,x) (1,0)`,
  `∂₂F v = fderiv F (t,x) (0,v)`;
* `∂_{y} W (0, v) = realC (E • ∂₂F (E • v))`, hence `y·∇W = realC (E • ∂₂F x)`.

So `T₀W = ∂_τ W - ½ y·∇W = realC (½ E • F + E t • ∂₁F)`, and `E t = E³` since `t = E²`.

Helpers are prefixed `simT0_`. The complexification is `realC = Axi.cplxV`
(`Lib/AxisymmetricB/Bridge.lean`). No placeholder proofs; only the standard axioms are used.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ContDiff

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-! ## Complexification and linear algebra -/

theorem simT0_realC_apply (x : Space) : realC x = UnforcedLeray.Axi.cplxV x := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply, UnforcedLeray.Axi.cplxV_apply]

theorem simT0_smul_cplxV (c : ℝ) (v : Space) :
    c • UnforcedLeray.Axi.cplxV v = UnforcedLeray.Axi.cplxV (c • v) := by
  rw [map_smul]

theorem simT0_pair_decomp (w : Space) :
    ((0 : ℝ), w) = ∑ j : Fin 3, w j • ((0 : ℝ), coordinateVector j) := by
  have hw : w = ∑ j : Fin 3, w j • coordinateVector j := by
    ext k
    simp [coordinateVector, Pi.single_apply]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simp only [Prod.snd_sum, Prod.smul_snd]
    exact hw

/-- The radial term `y·∇G` at `(τ, y)` is the derivative of `G` in the direction `(0, y)`. -/
theorem simT0_radialT_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ × Space → E) (τ : ℝ) (y : Space) :
    UnforcedLeray.PhaseSpace.radialT G (τ, y) = fderiv ℝ G (τ, y) (0, y) := by
  rw [simT0_pair_decomp y]
  simp only [UnforcedLeray.PhaseSpace.radialT, UnforcedLeray.PhaseSpace.dy, map_sum, map_smul]

/-- A Fréchet derivative equals the derivative of the composite along a line through the base point. -/
theorem simT0_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × Space → E} {p w : ℝ × Space} {ℓ : ℝ → ℝ × Space} {D : E}
    (hG : DifferentiableAt ℝ G p) (hℓ : HasDerivAt ℓ w 0) (hp : ℓ 0 = p)
    (hD : HasDerivAt (fun s => G (ℓ s)) D 0) : fderiv ℝ G p w = D := by
  have h : HasDerivAt (G ∘ ℓ) (fderiv ℝ G p w) 0 :=
    hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 hℓ hp.symm
  exact h.unique hD

/-- The `s`-derivative of `s ↦ F (s, x)` is the first partial derivative of `F`. -/
theorem simT0_deriv_fst (F : ℝ × Space → Space) (t : ℝ) (x : Space)
    (hF : DifferentiableAt ℝ F (t, x)) :
    deriv (fun s => F (s, x)) t = fderiv ℝ F (t, x) (1, 0) := by
  have hℓ : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × Space)) ((1 : ℝ), (0 : Space)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
  exact (hF.hasFDerivAt.comp_hasDerivAt_of_eq t hℓ rfl).deriv

/-! ## The drift of the similarity lift -/

/-- The drift `T₀` of the similarity lift `W q = realC (e^{q₁/2} F(e^{q₁}, e^{q₁/2} q₂))` of a field `F`,
at `(τ, y)`, where `F` is differentiable at `(e^τ, e^{τ/2} y)`. -/
theorem simT0_core (F : ℝ × Space → Space) (τ : ℝ) (y : Space)
    (hF : DifferentiableAt ℝ F (Real.exp τ, Real.exp (τ / 2) • y)) :
    UnforcedLeray.B0411.T0
        (fun q : ℝ × Space =>
          UnforcedLeray.Axi.cplxV (Real.exp (q.1 / 2) • F (Real.exp q.1, Real.exp (q.1 / 2) • q.2)))
        (τ, y) =
      UnforcedLeray.Axi.cplxV ((1 / 2 : ℝ) • (Real.exp (τ / 2) • F (Real.exp τ, Real.exp (τ / 2) • y)) +
        (Real.exp (τ / 2) * Real.exp τ) • fderiv ℝ F (Real.exp τ, Real.exp (τ / 2) • y) (1, 0)) := by
  -- differentiability of the similarity field at `(τ, y)`
  have hΦ : DifferentiableAt ℝ (fun q : ℝ × Space => (Real.exp q.1, Real.exp (q.1 / 2) • q.2)) (τ, y) := by
    fun_prop
  have hc : DifferentiableAt ℝ
      (F ∘ fun q : ℝ × Space => (Real.exp q.1, Real.exp (q.1 / 2) • q.2)) (τ, y) :=
    hF.comp (τ, y) hΦ
  have hs : DifferentiableAt ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2)) (τ, y) := by
    fun_prop
  have hG : DifferentiableAt ℝ
      (fun q : ℝ × Space => Real.exp (q.1 / 2) • F (Real.exp q.1, Real.exp (q.1 / 2) • q.2)) (τ, y) :=
    hs.smul hc
  have hWd : DifferentiableAt ℝ
      (fun q : ℝ × Space =>
        UnforcedLeray.Axi.cplxV (Real.exp (q.1 / 2) • F (Real.exp q.1, Real.exp (q.1 / 2) • q.2)))
      (τ, y) :=
    UnforcedLeray.Axi.cplxV.differentiableAt.comp (τ, y) hG
  -- the `τ`-derivative, along the line `s ↦ (τ + s, y)`
  have hℓ1 : HasDerivAt (fun s : ℝ => ((τ + s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_add τ).prodMk (hasDerivAt_const (0 : ℝ) y)
  have hc1 : HasDerivAt (fun s : ℝ => Real.exp ((τ + s) / 2)) (Real.exp (τ / 2) * (1 / 2)) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).const_add τ).div_const 2).exp
  have hc2 : HasDerivAt (fun s : ℝ => Real.exp (τ + s)) (Real.exp τ) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add τ).exp
  have hy2 : HasDerivAt (fun s : ℝ => Real.exp ((τ + s) / 2) • y)
      ((1 / 2 : ℝ) • (Real.exp (τ / 2) • y)) 0 :=
    (hc1.smul_const y).congr_deriv (by rw [smul_smul]; congr 1; ring)
  have hcurve : HasDerivAt
      (fun s : ℝ => ((Real.exp (τ + s), Real.exp ((τ + s) / 2) • y) : ℝ × Space))
      ((Real.exp τ, (1 / 2 : ℝ) • (Real.exp (τ / 2) • y)) : ℝ × Space) 0 :=
    hc2.prodMk hy2
  have hFc : HasDerivAt (fun s : ℝ => F (Real.exp (τ + s), Real.exp ((τ + s) / 2) • y))
      (fderiv ℝ F (Real.exp τ, Real.exp (τ / 2) • y)
        (Real.exp τ, (1 / 2 : ℝ) • (Real.exp (τ / 2) • y))) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  have hG1 : HasDerivAt
      (fun s : ℝ => Real.exp ((τ + s) / 2) • F (Real.exp (τ + s), Real.exp ((τ + s) / 2) • y))
      (Real.exp (τ / 2) •
          fderiv ℝ F (Real.exp τ, Real.exp (τ / 2) • y)
            (Real.exp τ, (1 / 2 : ℝ) • (Real.exp (τ / 2) • y)) +
        (Real.exp (τ / 2) * (1 / 2)) • F (Real.exp τ, Real.exp (τ / 2) • y)) 0 := by
    have h := hc1.fun_smul hFc
    simpa only [add_zero] using h
  have hpairsplit : ((Real.exp τ, (1 / 2 : ℝ) • (Real.exp (τ / 2) • y)) : ℝ × Space) =
      Real.exp τ • ((1 : ℝ), (0 : Space)) + (1 / 2 : ℝ) • ((0 : ℝ), Real.exp (τ / 2) • y) :=
    Prod.ext (by simp) (by simp)
  have hW1 : HasDerivAt
      (fun s : ℝ => UnforcedLeray.Axi.cplxV
        (Real.exp ((τ + s) / 2) • F (Real.exp (τ + s), Real.exp ((τ + s) / 2) • y)))
      (UnforcedLeray.Axi.cplxV
        (Real.exp (τ / 2) •
            (Real.exp τ • fderiv ℝ F (Real.exp τ, Real.exp (τ / 2) • y) (1, 0) +
              (1 / 2 : ℝ) • fderiv ℝ F (Real.exp τ, Real.exp (τ / 2) • y) (0, Real.exp (τ / 2) • y)) +
          (Real.exp (τ / 2) * (1 / 2)) • F (Real.exp τ, Real.exp (τ / 2) • y))) 0 := by
    refine (UnforcedLeray.Axi.cplxV.hasFDerivAt.comp_hasDerivAt 0 hG1).congr_deriv ?_
    congr 1
    rw [hpairsplit, map_add, map_smul, map_smul]
  have hD1 := simT0_fderiv_eq hWd hℓ1 (by simp) hW1
  -- the `y`-derivatives, along the lines `s ↦ (τ, y + s • v)`
  have hdy : ∀ v : Space,
      fderiv ℝ (fun q : ℝ × Space =>
          UnforcedLeray.Axi.cplxV (Real.exp (q.1 / 2) • F (Real.exp q.1, Real.exp (q.1 / 2) • q.2)))
        (τ, y) (0, v) =
      UnforcedLeray.Axi.cplxV
        (Real.exp (τ / 2) • fderiv ℝ F (Real.exp τ, Real.exp (τ / 2) • y) (0, Real.exp (τ / 2) • v)) := by
    intro v
    have h3 : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add y
    have hℓ2 : HasDerivAt (fun s : ℝ => ((τ, y + s • v) : ℝ × Space)) ((0 : ℝ), v) 0 :=
      (hasDerivAt_const (0 : ℝ) τ).prodMk h3
    have hcurve2 : HasDerivAt
        (fun s : ℝ => ((Real.exp τ, Real.exp (τ / 2) • (y + s • v)) : ℝ × Space))
        ((0 : ℝ), Real.exp (τ / 2) • v) 0 :=
      (hasDerivAt_const (0 : ℝ) (Real.exp τ)).prodMk (h3.const_smul (Real.exp (τ / 2)))
    have hF2 : HasDerivAt (fun s : ℝ => F (Real.exp τ, Real.exp (τ / 2) • (y + s • v)))
        (fderiv ℝ F (Real.exp τ, Real.exp (τ / 2) • y) (0, Real.exp (τ / 2) • v)) 0 :=
      hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve2 (by simp)
    have hG2 : HasDerivAt
        (fun s : ℝ => Real.exp (τ / 2) • F (Real.exp τ, Real.exp (τ / 2) • (y + s • v)))
        (Real.exp (τ / 2) •
          fderiv ℝ F (Real.exp τ, Real.exp (τ / 2) • y) (0, Real.exp (τ / 2) • v)) 0 := by
      have h := (hasDerivAt_const (0 : ℝ) (Real.exp (τ / 2))).fun_smul hF2
      simpa only [zero_smul, add_zero] using h
    exact simT0_fderiv_eq hWd hℓ2 (by simp)
      (UnforcedLeray.Axi.cplxV.hasFDerivAt.comp_hasDerivAt 0 hG2)
  -- assemble `T₀ = ∂_τ - ½ y·∇`
  simp only [UnforcedLeray.B0411.T0, UnforcedLeray.PhaseSpace.dτ]
  rw [hD1, simT0_radialT_eq, hdy y, simT0_smul_cplxV, ← map_sub]
  congr 1
  module

/-! ## The statement -/

theorem simT0Scaling : UnforcedLeray.Short.IIb.SimT0Scaling := by
  unfold SimT0Scaling
  intro u τ y hdiff
  have hW : (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1 u q.1 q.2)) =
      fun q : ℝ × Space => UnforcedLeray.Axi.cplxV
        (Real.exp (q.1 / 2) • (fun r : ℝ × Space => u r.1 r.2) (Real.exp q.1, Real.exp (q.1 / 2) • q.2)) := by
    funext q
    simp only [UnforcedLeray.B0190.simProfile, pow_one, simT0_realC_apply]
  have hderiv : deriv (fun s : ℝ => u s (Real.exp (τ / 2) • y)) (Real.exp τ) =
      fderiv ℝ (fun r : ℝ × Space => u r.1 r.2) (Real.exp τ, Real.exp (τ / 2) • y) (1, 0) :=
    simT0_deriv_fst (fun r : ℝ × Space => u r.1 r.2) (Real.exp τ) (Real.exp (τ / 2) • y) hdiff
  have hE3 : Real.exp (τ / 2) ^ 3 = Real.exp (τ / 2) * Real.exp τ := by
    have h : Real.exp τ = Real.exp (τ / 2) * Real.exp (τ / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h]
    ring
  rw [hW]
  refine (simT0_core (fun r : ℝ × Space => u r.1 r.2) τ y hdiff).trans ?_
  simp only [simT0_realC_apply]
  congr 1
  rw [hderiv, hE3]

end UnforcedLeray.Short.IIb
