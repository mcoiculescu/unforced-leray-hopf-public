import UnforcedLeray.Short.PartIIb.Sub.R1_7
import UnforcedLeray.Lib.AxisymmetricB.Bridge

/-!
# Part II-b, task `PartII-b:R1/7`, leaf `SimAdvScaling`: the advection of the similarity profile

Target: `UnforcedLeray.Short.IIb.SimAdvScaling` (`Sub/R1_7.lean`, unchanged).
Source of record: `the November 2 reference manuscript`, lines 1196-1263;
`paper/main.tex` 2917 (`B0190.simProfile`).

Notation: `t = e^τ`, `E = e^{τ/2}`, `x = E • y`, `F q = u q.1 q.2`. The profile is
`W q = realC (simProfile 1 u q.1 q.2) = cplxV (E(q.1) • u (e^{q.1}) (E(q.1) • q.2))`.
Along the line `s ↦ (τ, y + s e_j)` the chain rule gives `∂_j W (τ,y) = cplxV (E^2 • ∂_j (u t) x)`.
Summing `W_k ∂_k W` gives `E^3 ∑_k u_k ∂_k (u t) x = E^3 (u·∇)u`.

Helpers are prefixed `simAdv_`. `realC` is `Axi.cplxV` (`Lib/AxisymmetricB/Bridge.lean`).
No hypothesis is added and no placeholder is used.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ContDiff

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-- Along a line `s ↦ p + s • w`, a function differentiable at `p` has derivative `fderiv G p w`
at `s = 0`. -/
theorem simAdv_line {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : X → E) (p w : X) (hG : DifferentiableAt ℝ G p) :
    HasDerivAt (fun s : ℝ => G (p + s • w)) (fderiv ℝ G p w) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s • w) w 0 := by
    have h := (hasDerivAt_id' (0 : ℝ)).smul_const w
    rw [one_smul] at h
    exact h
  have h2 : HasDerivAt (fun s : ℝ => p + s • w) w 0 := h1.const_add p
  have hy : p = (fun s : ℝ => p + s • w) 0 := by simp
  exact hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 hy

/-- The realification `realC` is the complexification `Axi.cplxV`. -/
theorem simAdv_realC_eq (x : Space) :
    UnforcedLeray.B0412.realC x = UnforcedLeray.Axi.cplxV x := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply, UnforcedLeray.Axi.cplxV_apply]

/-- A complex coordinate `cplxV w k` times `cplxV v` is `cplxV` of the scaled vector. -/
theorem simAdv_coord_smul (w v : Space) (k : Fin 3) :
    UnforcedLeray.Axi.cplxV w k • UnforcedLeray.Axi.cplxV v
      = UnforcedLeray.Axi.cplxV (w k • v) := by
  ext i
  simp [UnforcedLeray.Axi.cplxV_apply]

/-- Expansion of a continuous linear map on `ℝ³` in the standard basis. -/
theorem simAdv_decomp (L : Space →L[ℝ] Space) (V : Space) :
    L V = ∑ k : Fin 3, V k • L (coordinateVector k) := by
  have hV : V = ∑ k : Fin 3, V k • coordinateVector k := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  conv_lhs => rw [hV]
  rw [map_sum]
  simp only [map_smul]

/-- **Scaling of the advection** (`SimAdvScaling`, `Sub/R1_7.lean`, tex 1196-1263). -/
theorem simAdvScaling : UnforcedLeray.Short.IIb.SimAdvScaling := by
  unfold SimAdvScaling
  intro u tau y hdiff
  -- the profile, as a `cplxV`-valued function `W`
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ × Space → UnforcedLeray.PhaseSpace.CVec3, ∀ q : ℝ × Space,
      W q = UnforcedLeray.Axi.cplxV
        (Real.exp (q.1 / 2) • u (Real.exp q.1) (Real.exp (q.1 / 2) • q.2)) :=
    ⟨fun q => UnforcedLeray.Axi.cplxV
        (Real.exp (q.1 / 2) • u (Real.exp q.1) (Real.exp (q.1 / 2) • q.2)), fun q => rfl⟩
  have hWfun : (fun q : ℝ × Space => UnforcedLeray.B0412.realC
      (UnforcedLeray.B0190.simProfile 1 u q.1 q.2)) = W := by
    funext q
    rw [hWdef]
    simp only [UnforcedLeray.B0190.simProfile, pow_one, simAdv_realC_eq]
  rw [hWfun]
  -- differentiability of the scaling map and of the profile
  have hPhi : DifferentiableAt ℝ
      (fun q : ℝ × Space => (Real.exp q.1, Real.exp (q.1 / 2) • q.2)) (tau, y) := by
    fun_prop
  have hFP : DifferentiableAt ℝ
      ((fun q : ℝ × Space => u q.1 q.2) ∘
        (fun q : ℝ × Space => (Real.exp q.1, Real.exp (q.1 / 2) • q.2))) (tau, y) :=
    hdiff.comp (tau, y) hPhi
  have hc : DifferentiableAt ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2)) (tau, y) := by
    fun_prop
  have hS : DifferentiableAt ℝ
      (fun q : ℝ × Space => Real.exp (q.1 / 2) • u (Real.exp q.1) (Real.exp (q.1 / 2) • q.2))
      (tau, y) :=
    hc.smul hFP
  have hW : DifferentiableAt ℝ W (tau, y) := by
    have hWe : W = fun q : ℝ × Space => UnforcedLeray.Axi.cplxV
        (Real.exp (q.1 / 2) • u (Real.exp q.1) (Real.exp (q.1 / 2) • q.2)) := funext hWdef
    rw [hWe]
    exact UnforcedLeray.Axi.cplxV.differentiableAt.comp (tau, y) hS
  -- spatial differentiability of `u (e^τ)` at `x = e^{τ/2} y`
  have hu : DifferentiableAt ℝ (u (Real.exp tau)) (Real.exp (tau / 2) • y) :=
    hdiff.comp (Real.exp (tau / 2) • y)
      ((differentiableAt_const (Real.exp tau)).prodMk differentiableAt_id)
  -- directional derivatives of `W` along `(0, e_j)`
  have hdy : ∀ j : Fin 3,
      UnforcedLeray.PhaseSpace.dy j W (tau, y) =
        UnforcedLeray.Axi.cplxV ((Real.exp (tau / 2)) ^ 2 •
          fderiv ℝ (u (Real.exp tau)) (Real.exp (tau / 2) • y) (coordinateVector j)) := by
    intro j
    have hpt : ∀ s : ℝ, ((tau, y) + s • ((0 : ℝ), coordinateVector j) : ℝ × Space)
        = (tau, y + s • coordinateVector j) := by
      intro s
      ext <;> simp
    have hsplit : ∀ s : ℝ, Real.exp (tau / 2) • (y + s • coordinateVector j)
        = Real.exp (tau / 2) • y + s • (Real.exp (tau / 2) • coordinateVector j) := by
      intro s
      rw [smul_add, smul_comm (Real.exp (tau / 2)) s (coordinateVector j)]
    have hfun : (fun s : ℝ => W ((tau, y) + s • ((0 : ℝ), coordinateVector j)))
        = fun s : ℝ => UnforcedLeray.Axi.cplxV (Real.exp (tau / 2) •
            u (Real.exp tau)
              (Real.exp (tau / 2) • y + s • (Real.exp (tau / 2) • coordinateVector j))) := by
      funext s
      rw [hWdef, hpt s]
      dsimp only
      rw [hsplit s]
    have hline : HasDerivAt (fun s : ℝ => W ((tau, y) + s • ((0 : ℝ), coordinateVector j)))
        (fderiv ℝ W (tau, y) ((0 : ℝ), coordinateVector j)) 0 :=
      simAdv_line W (tau, y) ((0 : ℝ), coordinateVector j) hW
    have hline' : HasDerivAt (fun s : ℝ => UnforcedLeray.Axi.cplxV (Real.exp (tau / 2) •
            u (Real.exp tau)
              (Real.exp (tau / 2) • y + s • (Real.exp (tau / 2) • coordinateVector j))))
        (fderiv ℝ W (tau, y) ((0 : ℝ), coordinateVector j)) 0 := by
      rw [← hfun]
      exact hline
    have hu_line : HasDerivAt
        (fun s : ℝ => u (Real.exp tau)
          (Real.exp (tau / 2) • y + s • (Real.exp (tau / 2) • coordinateVector j)))
        (fderiv ℝ (u (Real.exp tau)) (Real.exp (tau / 2) • y)
          (Real.exp (tau / 2) • coordinateVector j)) 0 :=
      simAdv_line (u (Real.exp tau)) (Real.exp (tau / 2) • y)
        (Real.exp (tau / 2) • coordinateVector j) hu
    have hline2 : HasDerivAt (fun s : ℝ => UnforcedLeray.Axi.cplxV (Real.exp (tau / 2) •
            u (Real.exp tau)
              (Real.exp (tau / 2) • y + s • (Real.exp (tau / 2) • coordinateVector j))))
        (UnforcedLeray.Axi.cplxV (Real.exp (tau / 2) •
          fderiv ℝ (u (Real.exp tau)) (Real.exp (tau / 2) • y)
            (Real.exp (tau / 2) • coordinateVector j))) 0 :=
      UnforcedLeray.Axi.cplxV.hasFDerivAt.comp_hasDerivAt 0
        (hu_line.const_smul (Real.exp (tau / 2)))
    have hd := hline'.unique hline2
    have hlin : fderiv ℝ (u (Real.exp tau)) (Real.exp (tau / 2) • y)
          (Real.exp (tau / 2) • coordinateVector j)
        = Real.exp (tau / 2) • fderiv ℝ (u (Real.exp tau)) (Real.exp (tau / 2) • y)
          (coordinateVector j) :=
      map_smul _ _ _
    show fderiv ℝ W (tau, y) ((0 : ℝ), coordinateVector j) = _
    rw [hd, hlin, smul_smul, ← pow_two]
  -- assemble `advT W W (τ, y)` as a sum over the coordinates `k`
  unfold UnforcedLeray.Cons.C03.Concrete.advT
  simp only [hdy, hWdef, simAdv_coord_smul]
  rw [← map_sum, simAdv_realC_eq]
  congr 1
  simp only [UnforcedLeray.Axi.advection]
  rw [simAdv_decomp (fderiv ℝ (u (Real.exp tau)) (Real.exp (tau / 2) • y))
      (u (Real.exp tau) (Real.exp (tau / 2) • y)), Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [PiLp.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  ring

end UnforcedLeray.Short.IIb

end
