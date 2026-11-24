import UnforcedLeray.Lib.Train.Ops
import UnforcedLeray.Lib.Gaussian.Periodization

/-!
# The periodized heat vortex `V_c` and its exact residual (INF16 T2)


target T2 (output O3, first half); decision D8. Blueprint unit **B0146** (`eq:st18-t00144`,
`paper/main.tex` lines 2196–2216).

**Statement (tex lines 2196–2216).** With `a = 1 + νs`, `ψ^p(x,s) = -(2/a)e^{-|x|²/(4a)}`,
`V = ∇^⊥ψ^p`, `V_c(q,η,s) = ∑ₙ V(q - nc, η, s)`. Each isolated radial vortex solves
Navier–Stokes with its radial pressure; after summing those pressures into `p_c`, the residual
of `V_c` is the divergence of `Q_c = ∑_{i≠j} V_i ⊗ V_j`, `V_i(q,η,s) = V(q - ic, η, s)`.

**Route.** The calculus is the compiled unit `Units/B0146.lean` (fields valued in `ℝ × ℝ`);
here it is transported to `Vec = EuclideanSpace ℝ (Fin 2)` (decision D1) through the coordinate
equivalence `toVecL`, so nothing is re-proved.

**Conventions and junk values.** `V_c`, `p_c` are `Gaussian.periodize` (`tsum` over `ℤ`), and
`Q_c` is a `tsum` over the off-diagonal pairs; all three series are proved summable for `ν > 0`,
`c ≠ 0`, `s ≥ 0` (`summable_isoV`, `summable_isoP`, `summable_Qc`), so no junk `tsum` enters.
The classical partials entering the residual are genuine derivatives (`Vc_classical`). The
isolated pressure is `isoP = -a⁻³ e^{-|x|²/(2a)}` (unit B0146 `isoPressure`; the manuscript says
"its radial pressure" without a formula). The scoping signature writes the residual as
`-matDiv Q_c`; the manuscript (tex 2211–2213) and the computation give `+ div Q_c`
(`Vc_residual`), consistent with the error equation `e_s - νΔe + ⋯ = -P₀ div Q_c` of INF16 B4.
The period hypothesis is `c ≠ 0` (the manuscript's `c ≥ 2` is not needed).

Main declarations: `isoV`, `isoP`, `Vc`, `pc`, `Qc`, `isoV_apply`, `isoV_residual`,
`Vc_eq`, `Vc_heat`, `Vc_residual`, `Vc_hasDerivAt`, `Vc_div`, `Vc_curl`, `Vc_odd`,
`Vc_periodic`, `pc_periodic`, `Vc_classical`, `summable_isoV`, `summable_isoP`, `summable_Qc`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Train

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Gaussian (periodize periodize_add_period)
open UnforcedLeray.GaussianVortex (partialX partialY radiusSq)
open UnforcedLeray.B0146 (latticeSum shift u1 u2 u1x u1y u2x u2y xd gf_u1x gf_u1y gf_u2x
  gf_u2y lat_add_eq div_u dX_u1 dX_u2 dY_u1 dY_u2 periodicVelocity_fst periodicVelocity_snd)

theorem width_eq_heatWidth (ν s : ℝ) : width ν s = B0113.heatWidth ν s := rfl

/-! ### The isolated vortex -/

/-- The isolated heat vortex `V = ∇^⊥ψ^p` at age `s` (tex line 2204), unit B0146
`isoVelocity`, with values in `Vec`. -/
def isoV (ν s : ℝ) (w : Plane) : Vec := toVec (B0146.isoVelocity ν s w)

/-- Its radial pressure `-a⁻³ e^{-|x|²/(2a)}` (unit B0146 `isoPressure`). -/
def isoP (ν s : ℝ) (w : Plane) : ℝ := B0146.isoPressure ν s w

/-- `V = ∇^⊥ψ^p` with `∇^⊥ = (-∂_η, ∂_q)` (tex lines 2138, 2204) and
`ψ^p = -(2/a) e^{-|x|²/(4a)}` (`B0146.streamP_apply`). -/
theorem isoV_eq_perp (ν s : ℝ) (w : Plane) :
    isoV ν s w = toVec (-partialEta (B0146.streamP ν s) w, partialQ (B0146.streamP ν s) w) :=
  rfl

/-- The explicit isolated velocity `a⁻² e^{-|x|²/(4a)} (-η, q)`. -/
theorem isoV_apply (ν s : ℝ) (w : Plane) :
    isoV ν s w = ((width ν s)⁻¹ ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * width ν s))) •
      toVec (-w.2, w.1) := by
  rw [isoV, B0146.isoVelocity_apply, ← toVec_smul]
  congr 1
  simp only [u1, u2, B0113.gw, radiusSq, Prod.smul_mk, smul_eq_mul, width_eq_heatWidth]
  have he : -((B0113.heatWidth ν s)⁻¹ * (w.1 ^ 2 + w.2 ^ 2) / 4) =
      -(w.1 ^ 2 + w.2 ^ 2) / (4 * B0113.heatWidth ν s) := by ring
  rw [he]
  ext <;> simp only <;> ring

theorem isoV_neg (ν s : ℝ) (w : Plane) : isoV ν s (-w) = -isoV ν s w := by
  rw [isoV_apply, isoV_apply, ← smul_neg, ← toVec_neg]
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sq, Prod.neg_mk, neg_neg]

/-- The isolated vortex is divergence free (tex lines 2206–2208). -/
theorem isoV_div {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (z : Plane) :
    Cyl.divergence (isoV ν s) z = 0 :=
  (B0146.isolated_vortex hν hs).1 z

/-- **Each isolated radial vortex solves Navier–Stokes** with its radial pressure
(tex lines 2206–2211): `∂ₛV + V·∇V - νΔV + ∇P = 0`, with a genuine time derivative. -/
theorem isoV_residual {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (z : Plane) :
    momentumResidual ν (isoV ν) (isoP ν) s z = 0 := by
  have h := (B0146.isolated_vortex hν hs).2.2.2.2.2.2 z
  have e := momentumResidual_toVec (ν := ν) (p := B0146.isoPressure ν) h
  refine e.trans ?_
  rw [B0146.isolated_nsResidual hν hs z]
  exact map_zero toVecL

/-! ### The periodization and the cross stress -/

/-- The periodized heat vortex `V_c(q,η,s) = ∑ₙ V(q - nc, η, s)` (tex line 2205). -/
def Vc (ν c s : ℝ) : Plane → Vec := periodize c (isoV ν s)

/-- The summed isolated pressures `p_c = ∑ₙ P(q - nc, η, s)` (tex line 2211). -/
def pc (ν c s : ℝ) : Plane → ℝ := periodize c (isoP ν s)

/-- The cross stress `Q_c = ∑_{i≠j} V_i ⊗ V_j` (tex lines 2213–2215), entry
`Q_c^{kl} = ∑_{i≠j} V_i^k V_j^l` over the off-diagonal pairs of `ℤ²`. -/
def Qc (ν c s : ℝ) (z : Plane) : Matrix (Fin 2) (Fin 2) ℝ := fun k l =>
  ∑' p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)),
    isoV ν s (z.1 - p.1.1 * c, z.2) k * isoV ν s (z.1 - p.1.2 * c, z.2) l

/-- `V_c` is the `Vec` image of the unit-B0146 periodization (no summability needed). -/
theorem Vc_eq (ν c s : ℝ) (z : Plane) :
    Vc ν c s z = toVec (B0146.periodicVelocity ν c s z) := by
  rw [Vc, periodize, B0146.periodicVelocity, toVec, toVecL.map_tsum]
  rfl

theorem Vc_fun_eq (ν c : ℝ) : Vc ν c = fun t w => toVec (B0146.periodicVelocity ν c t w) :=
  funext fun t => funext fun w => Vc_eq ν c t w

theorem Vc_slice_eq (ν c s : ℝ) : Vc ν c s = fun w => toVec (B0146.periodicVelocity ν c s w) :=
  funext fun w => Vc_eq ν c s w

theorem pc_eq (ν c s : ℝ) : pc ν c s = B0146.periodicPressure ν c s := rfl

theorem Qc_eq (ν c s : ℝ) (z : Plane) (k l : Fin 2) :
    Qc ν c s z k l = B0146.crossStress ν c s z k l := by
  simp only [Qc, B0146.crossStress, isoV, toVec_apply_eq_vcomp]
  rfl

theorem Qc_fun_eq (ν c s : ℝ) : Qc ν c s = B0146.crossStress ν c s :=
  funext fun z => funext fun k => funext fun l => Qc_eq ν c s z k l

/-! ### Convergence of the three series -/

section WellPosed

variable {ν c s : ℝ}

/-- The series defining `V_c` converges (tex line 2205). -/
theorem summable_isoV (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    Summable (fun n : ℤ => isoV ν s (z.1 - n * c, z.2)) :=
  (B0146.summable_imageVelocity hν hc hs z).mapL (toVecL : (ℝ × ℝ) →L[ℝ] Vec)

/-- The series of isolated pressures converges (tex line 2211). -/
theorem summable_isoP (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    Summable (fun n : ℤ => isoP ν s (z.1 - n * c, z.2)) :=
  B0146.summable_isoPressure hν hc hs z

/-- The off-diagonal series defining `Q_c` converges (tex lines 2213–2215). -/
theorem summable_Qc (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) (k l : Fin 2) :
    Summable (fun p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)) =>
      isoV ν s (z.1 - p.1.1 * c, z.2) k * isoV ν s (z.1 - p.1.2 * c, z.2) l) := by
  have h := B0146.summable_crossStress hc (B0113.heatWidth_pos hν hs) z k l
  simp only [isoV, toVec_apply_eq_vcomp]
  exact h

end WellPosed

/-! ### Symmetries -/

/-- Central oddness of a periodization of an odd field (no summability needed). -/
theorem periodize_neg_of_odd {E : Type*} [NormedAddCommGroup E] {f : Plane → E}
    (hf : ∀ w, f (-w) = -f w) (c : ℝ) (z : Plane) :
    periodize c f (-z) = -periodize c f z := by
  unfold periodize
  have h1 : ∀ n : ℤ, f ((-z).1 - n * c, (-z).2) = -f (z.1 - ((-n : ℤ) : ℝ) * c, z.2) := by
    intro n
    rw [← hf]
    congr 1
    ext <;> simp; ring
  simp_rw [h1, tsum_neg]
  congr 1
  exact (Equiv.neg ℤ).tsum_eq (fun m : ℤ => f (z.1 - m * c, z.2))

/-- `V_c(-q,-η,s) = -V_c(q,η,s)` (tex lines 2186–2191 at the level of `V_c`). -/
theorem Vc_odd (ν c s : ℝ) (z : Plane) : Vc ν c s (-z) = -Vc ν c s z :=
  periodize_neg_of_odd (isoV_neg ν s) c z

/-- `V_c` is `c`-periodic (tex line 2205). -/
theorem Vc_periodic (ν c s : ℝ) : Cyl.IsPeriodic c (Vc ν c s) := fun z =>
  periodize_add_period c _ z.1 z.2

theorem pc_periodic (ν c s : ℝ) : Cyl.IsPeriodic c (pc ν c s) := fun z =>
  periodize_add_period c _ z.1 z.2

/-! ### The PDE identities -/

section PDE

variable {ν c s : ℝ}

/-- **`V_c` solves the vector heat equation** `∂ₛV_c = νΔV_c` (termwise; each isolated
vortex does, tex lines 2203–2208), with a genuine time derivative. -/
theorem Vc_heat (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    HasDerivAt (fun t => Vc ν c t z) (ν • vecLaplacian (Vc ν c s) z) s := by
  have ha := B0113.heatWidth_pos hν hs
  have h := B0146.hasDerivAt_periodicVelocity hν hc hs z
  have h2 : HasDerivAt (fun t => toVec (B0146.periodicVelocity ν c t z))
      (toVec (ν * latticeSum c (B0146.u1a (B0113.heatWidth ν s)) z,
        ν * latticeSum c (B0146.u2a (B0113.heatWidth ν s)) z)) s :=
    (toVecL : (ℝ × ℝ) →L[ℝ] Vec).hasFDerivAt.comp_hasDerivAt s h
  have e1 : (fun t => Vc ν c t z) = fun t => toVec (B0146.periodicVelocity ν c t z) :=
    funext fun t => Vc_eq ν c t z
  rw [e1, Vc_slice_eq, vecLaplacian_toVec, B0146.lap_periodicVelocity_fst hc ha,
    B0146.lap_periodicVelocity_snd hc ha, ← toVec_smul]
  exact h2

/-- **The residual identity** (tex lines 2211–2215): with the summed isolated pressures `p_c`,
the Navier–Stokes residual of `V_c` is `div Q_c`. -/
theorem Vc_residual (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    momentumResidual ν (Vc ν c) (pc ν c) s z = matDiv (Qc ν c s) z := by
  have h := B0146.hasDerivAt_periodicVelocity hν hc hs z
  rw [Vc_fun_eq]
  have e := momentumResidual_toVec (ν := ν) (p := B0146.periodicPressure ν c) h
  have hp : pc ν c = B0146.periodicPressure ν c := rfl
  rw [hp, e, B0146.periodicVelocity_nsResidual hν hc hs z, matDiv_eq, Qc_fun_eq]

/-- The residual identity in evolution form:
`∂ₛV_c = νΔV_c - V_c·∇V_c - ∇p_c + div Q_c`, with a genuine time derivative. -/
theorem Vc_hasDerivAt (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    HasDerivAt (fun t => Vc ν c t z)
      (ν • vecLaplacian (Vc ν c s) z - advection (Vc ν c s) z - gradS (pc ν c s) z +
        matDiv (Qc ν c s) z) s := by
  have h := B0146.periodicVelocity_residual hν hc hs z
  have h2 := (toVecL : (ℝ × ℝ) →L[ℝ] Vec).hasFDerivAt.comp_hasDerivAt s h
  have e1 : (fun t => Vc ν c t z) = fun t => toVec (B0146.periodicVelocity ν c t z) :=
    funext fun t => Vc_eq ν c t z
  rw [e1, Vc_slice_eq, vecLaplacian_toVec, advection_toVec, pc_eq, gradS_eq,
    matDiv_eq, Qc_fun_eq, ← toVec_smul, ← toVec_sub, ← toVec_sub, ← toVec_add]
  exact h2

/-- `div V_c = 0`. -/
theorem Vc_div (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    Cyl.divergence (Vc ν c s) z = 0 := by
  have ha := B0113.heatWidth_pos hν hs
  rw [Vc_slice_eq]
  show partialX (fun w => (B0146.periodicVelocity ν c s w).1) z +
    partialY (fun w => (B0146.periodicVelocity ν c s w).2) z = 0
  rw [periodicVelocity_fst hc ha, periodicVelocity_snd hc ha]
  rw [show partialX (latticeSum c (u1 (B0113.heatWidth ν s))) z =
      latticeSum c (u1x (B0113.heatWidth ν s)) z from (dX_u1 hc ha z).deriv,
    show partialY (latticeSum c (u2 (B0113.heatWidth ν s))) z =
      latticeSum c (u2y (B0113.heatWidth ν s)) z from (dY_u2 hc ha z).deriv]
  have hdiv := lat_add_eq hc (k := fun _ => 0) (div_u (B0113.heatWidth ν s))
    (xd (gf_u1x ha)) (xd (gf_u2y ha)) z
  rw [hdiv]
  simp [latticeSum]

/-- The vorticity of `V_c` is the periodized isolated vorticity
`∑ₙ ω^p(q - nc, η)`, `ω^p = a⁻²(2 - |x|²/(2a)) e^{-|x|²/(4a)}` (unit B0113 `eExp`). -/
theorem Vc_curl (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    Cyl.curl (Vc ν c s) z = periodize c (B0113.eExp (width ν s)) z := by
  have ha := B0113.heatWidth_pos hν hs
  rw [Vc_slice_eq]
  show partialX (fun w => (B0146.periodicVelocity ν c s w).2) z -
    partialY (fun w => (B0146.periodicVelocity ν c s w).1) z = _
  rw [periodicVelocity_fst hc ha, periodicVelocity_snd hc ha]
  rw [show partialX (latticeSum c (u2 (B0113.heatWidth ν s))) z =
      latticeSum c (u2x (B0113.heatWidth ν s)) z from (dX_u2 hc ha z).deriv,
    show partialY (latticeSum c (u1 (B0113.heatWidth ν s))) z =
      latticeSum c (u1y (B0113.heatWidth ν s)) z from (dY_u1 hc ha z).deriv]
  have h := ((xd (gf_u2x ha)).hasSum hc z).sub ((xd (gf_u1y ha)).hasSum hc z)
  refine (h.tsum_eq.symm.trans ?_)
  unfold periodize
  congr 1
  funext n
  simp only [shift, u2x, u1y, B0113.eExp, radiusSq, width_eq_heatWidth]
  ring

/-- Every classical partial derivative entering `Vc_residual` and `Vc_heat` is a genuine
derivative (no junk value of `deriv`). -/
theorem Vc_classical (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    B0146.HasPartialX (fun w => Vc ν c s w 0) z ∧
    B0146.HasPartialY (fun w => Vc ν c s w 0) z ∧
    B0146.HasPartialX (fun w => Vc ν c s w 1) z ∧
    B0146.HasPartialY (fun w => Vc ν c s w 1) z ∧
    B0146.HasPartialX (partialQ (fun w => Vc ν c s w 0)) z ∧
    B0146.HasPartialY (partialEta (fun w => Vc ν c s w 0)) z ∧
    B0146.HasPartialX (partialQ (fun w => Vc ν c s w 1)) z ∧
    B0146.HasPartialY (partialEta (fun w => Vc ν c s w 1)) z ∧
    B0146.HasPartialX (pc ν c s) z ∧ B0146.HasPartialY (pc ν c s) z ∧
    B0146.HasPartialX (fun w => Qc ν c s w 0 0) z ∧
    B0146.HasPartialY (fun w => Qc ν c s w 1 0) z ∧
    B0146.HasPartialX (fun w => Qc ν c s w 0 1) z ∧
    B0146.HasPartialY (fun w => Qc ν c s w 1 1) z := by
  rw [Vc_slice_eq, Qc_fun_eq, pc_eq]
  exact B0146.periodic_classical_derivatives hν hc hs z

end PDE

end UnforcedLeray.Train
