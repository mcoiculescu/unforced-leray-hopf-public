import UnforcedLeray.Units.B0146.Explicit

/-!
# B0146 — Isolated heat vortex, its periodization, and the cross-stress residual
(`eq:st18-t00144`)

Blueprint unit **B0146**, label `eq:st18-t00144`, `paper/main.tex` lines 2196–2216
(§`sec:st18-3421`, "Gaussian comparison up to the overlap age"); infrastructure `INF27`.

**Statement (tex lines 2196–2216).** Put `σ = ν s`, `a = 1 + σ`, `s_c = (c² - 1)/ν`, and
`ψ^p(x,s) = -(2/a) e^{-|x|²/(4a)}`, `V = ∇^⊥ψ^p`, `V_c(q,η,s) = ∑ₙ V(q - nc, η, s)`.
Each isolated radial vortex solves Navier–Stokes: its vorticity is radial, its velocity is
tangential, the vorticity transport term vanishes, and its velocity nonlinearity is a
gradient included in its radial pressure. The residual of `V_c`, after summing those
pressures, is the divergence of `Q_c = ∑_{i ≠ j} V_i ⊗ V_j`, `V_i(q,η,s) = V(q - ic, η, s)`.

**Conventions.** `Plane = ℝ × ℝ`, `(q, η) = (z.1, z.2)`; `∇^⊥ = (-∂_η, ∂_q)` (tex line 2138)
is `perpendicularGradient`; Cartesian partials are the classical `partialX`, `partialY`;
`lap` is the planar Laplacian of `NonlinearBackground.TrainScaling`. The width
`a = heatWidth ν s = 1 + ν s` and the explicit fields `ψExp`, `vExp`, `pExp`, `eExp` are
those of unit B0113 (`Units/B0113.lean`), reused, not redefined. The isolated pressure,
which the manuscript calls "its radial pressure" without a formula, is
`pExp a = -a⁻³ e^{-|x|²/(2a)}` (as in the draft
`Analysis/NonlinearBackground/IsolatedHeatVortex.lean`, `heatV_solves_NS`). Series over `ℤ`
are `tsum`s; every series used is proved absolutely summable for `c ≠ 0`, `ν > 0`, `s ≥ 0`
(`summable_imageVelocity`, `summable_isoPressure`, `summable_crossStress`), so no junk value
of `tsum` enters. The cross stress is the matrix `Q_c^{kl} = ∑_{i≠j} V_i^k V_j^l` with the sum
over the off-diagonal set `{(i,j) ∈ ℤ² | i ≠ j}`; its divergence is `(div Q)^l = ∂_k Q^{kl}`
(`Q_c` is symmetric). Time derivatives are stated with `HasDerivAt`; the spatial partials
that enter the statement are proved to be genuine derivatives
(`periodic_classical_derivatives`). The manuscript's period satisfies `c ≥ 2`; only `c ≠ 0`
is used. The isolated statements need only `ν > 0`, `s ≥ 0`.

**Main declarations.** `isolated_vortex` (isolated part), `periodicVelocity_residual` and
`periodicVelocity_nsResidual` (the residual identity), `crossStress_eq` (the off-diagonal
double sum), `periodic_classical_derivatives`, `heat_vortex_periodization` (whole unit).
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace UnforcedLeray.B0146

open UnforcedLeray.GaussianVortex
open UnforcedLeray.NonlinearBackground (lap)
open UnforcedLeray.B0113 (heatWidth gw vExp pExp ψExp eExp heatVelocity heatPressure
  heatVelocityX heatVelocityY heatWidth_pos hasDerivAt_heatWidth eventually_heatWidth_pos
  heatVelocity_eq heatPressure_eq heatVortex_navierStokes ψExp_perp vExp_curl vExp_euler
  eExp_advection vExp_divergence)

/-! ### The manuscript's objects (tex lines 2196–2216) -/

/-- Slow time `σ = ν s` (tex line 2197). -/
def slowTime (ν s : ℝ) : ℝ := ν * s

/-- The overlap age `s_c = (c² - 1)/ν` (tex line 2198). -/
def overlapAge (ν c : ℝ) : ℝ := (c ^ 2 - 1) / ν

/-- `a = 1 + σ` (tex line 2197); the width is B0113's `heatWidth`. -/
theorem heatWidth_eq_one_add_slowTime (ν s : ℝ) : heatWidth ν s = 1 + slowTime ν s := rfl

/-- The isolated stream function `ψ^p(x,s) = -(2/a) e^{-|x|²/(4a)}` (tex line 2203),
B0113's `ψExp` at width `a = 1 + ν s`. -/
def streamP (ν s : ℝ) : Plane → ℝ := ψExp (heatWidth ν s)

theorem streamP_apply (ν s : ℝ) (x : Plane) :
    streamP ν s x =
      -(2 / heatWidth ν s) * Real.exp (-(radiusSq x / (4 * heatWidth ν s))) := by
  simp only [streamP, ψExp, gw]
  rw [show (heatWidth ν s)⁻¹ * radiusSq x / 4 = radiusSq x / (4 * heatWidth ν s) by ring]
  ring

/-- The isolated velocity `V = ∇^⊥ψ^p` (tex line 2204). -/
def isoVelocity (ν s : ℝ) : Plane → Plane := perpendicularGradient (streamP ν s)

/-- The radial pressure of the isolated vortex, `-a⁻³ e^{-|x|²/(2a)}` (tex line 2210). -/
def isoPressure (ν s : ℝ) : Plane → ℝ := pExp (heatWidth ν s)

/-- The isolated vorticity `ω^p = curl V` (tex line 2207). -/
def isoVorticity (ν s : ℝ) : Plane → ℝ := curl (isoVelocity ν s)

/-- The image `V_i(q,η,s) = V(q - ic, η, s)` (tex line 2215). -/
def imageVelocity (ν c : ℝ) (i : ℤ) (s : ℝ) (z : Plane) : Plane :=
  isoVelocity ν s (shift c i z)

/-- The periodization `V_c(q,η,s) = ∑ₙ V(q - nc, η, s)` (tex line 2205). -/
def periodicVelocity (ν c s : ℝ) (z : Plane) : Plane := ∑' n : ℤ, imageVelocity ν c n s z

/-- The summed isolated pressures `p^p_c = ∑ₙ P(q - nc, η, s)` (tex line 2211). -/
def periodicPressure (ν c s : ℝ) (z : Plane) : ℝ := ∑' n : ℤ, isoPressure ν s (shift c n z)

/-- Cartesian components of a planar vector. -/
def vcomp (v : Plane) : Fin 2 → ℝ := ![v.1, v.2]

/-- The cross stress `Q_c = ∑_{i ≠ j} V_i ⊗ V_j` (tex lines 2213–2215), entry
`Q_c^{kl} = ∑_{i ≠ j} V_i^k V_j^l`, summed over the off-diagonal pairs of `ℤ²`. -/
def crossStress (ν c s : ℝ) (z : Plane) (k l : Fin 2) : ℝ :=
  ∑' p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)),
    vcomp (imageVelocity ν c p.1.1 s z) k * vcomp (imageVelocity ν c p.1.2 s z) l

/-- Divergence of a planar 2-tensor field, `(div Q)^l = ∂_k Q^{kl}`. -/
def tensorDiv (Q : Plane → Fin 2 → Fin 2 → ℝ) (z : Plane) : Plane :=
  (partialX (fun w => Q w 0 0) z + partialY (fun w => Q w 1 0) z,
   partialX (fun w => Q w 0 1) z + partialY (fun w => Q w 1 1) z)

/-- The planar Navier–Stokes residual `∂ₛu + u·∇u - νΔu + ∇p` at viscosity `ν`. -/
def nsResidual (ν : ℝ) (u : ℝ → Plane → Plane) (p : ℝ → Plane → ℝ) (s : ℝ) (z : Plane) :
    Plane :=
  deriv (fun t => u t z) s + advection (u s) z -
    ν • (lap (fun t w => (u t w).1) s z, lap (fun t w => (u t w).2) s z) + gradient (p s) z

/-! ### The isolated vortex -/

theorem isoVelocity_eq (ν s : ℝ) : isoVelocity ν s = vExp (heatWidth ν s) :=
  funext fun z => ψExp_perp _ z

theorem isoVorticity_eq (ν s : ℝ) : isoVorticity ν s = eExp (heatWidth ν s) :=
  funext fun z => by rw [isoVorticity, isoVelocity_eq]; exact vExp_curl _ z

/-- Tex lines 2206–2211: the isolated radial vortex. Its velocity is divergence free and
tangential, its vorticity and its pressure are radial, the vorticity transport term vanishes,
the velocity nonlinearity is the gradient `-∇P` of the radial pressure, and `(V, P)` solves
the unforced planar Navier–Stokes equations with viscosity `ν`. -/
theorem isolated_vortex {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    (∀ z, divergence (isoVelocity ν s) z = 0) ∧
    (∀ z : Plane, (isoVelocity ν s z).1 * z.1 + (isoVelocity ν s z).2 * z.2 = 0) ∧
    (∃ f : ℝ → ℝ, ∀ z, isoVorticity ν s z = f (radiusSq z)) ∧
    (∃ f : ℝ → ℝ, ∀ z, isoPressure ν s z = f (radiusSq z)) ∧
    (∀ z, scalarAdvection (isoVelocity ν s) (isoVorticity ν s) z = 0) ∧
    (∀ z, advection (isoVelocity ν s) z = -gradient (isoPressure ν s) z) ∧
    (∀ z, HasDerivAt (fun t => isoVelocity ν t z)
      (ν • (lap (fun t w => (isoVelocity ν t w).1) s z,
            lap (fun t w => (isoVelocity ν t w).2) s z) -
        advection (isoVelocity ν s) z - gradient (isoPressure ν s) z) s) := by
  have ha := heatWidth_pos hν hs
  refine ⟨fun z => ?_, fun z => ?_, ?_, ?_, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · rw [isoVelocity_eq]; exact vExp_divergence _ z
  · rw [isoVelocity_eq]; simp only [vExp]; ring
  · exact ⟨fun r => (heatWidth ν s)⁻¹ ^ 2 * (2 - (heatWidth ν s)⁻¹ * r / 2) *
      Real.exp (-((heatWidth ν s)⁻¹ * r / 4)), fun z => by rw [isoVorticity_eq]; rfl⟩
  · exact ⟨fun r => -((heatWidth ν s)⁻¹ ^ 3) * (Real.exp (-((heatWidth ν s)⁻¹ * r / 4)) *
      Real.exp (-((heatWidth ν s)⁻¹ * r / 4))), fun z => rfl⟩
  · rw [isoVelocity_eq, isoVorticity_eq]; exact eExp_advection _ z
  · rw [isoVelocity_eq]; exact eq_neg_of_add_eq_zero_left (vExp_euler _ z)
  · have hsl : heatVelocity ν s = isoVelocity ν s := by
      rw [heatVelocity_eq ha, isoVelocity_eq]
    have hlap1 : lap (heatVelocityX ν) s z = lap (fun t w => (isoVelocity ν t w).1) s z := by
      show partialX (partialX (fun w => (heatVelocity ν s w).1)) z +
          partialY (partialY (fun w => (heatVelocity ν s w).1)) z =
        partialX (partialX (fun w => (isoVelocity ν s w).1)) z +
          partialY (partialY (fun w => (isoVelocity ν s w).1)) z
      rw [hsl]
    have hlap2 : lap (heatVelocityY ν) s z = lap (fun t w => (isoVelocity ν t w).2) s z := by
      show partialX (partialX (fun w => (heatVelocity ν s w).2)) z +
          partialY (partialY (fun w => (heatVelocity ν s w).2)) z =
        partialX (partialX (fun w => (isoVelocity ν s w).2)) z +
          partialY (partialY (fun w => (isoVelocity ν s w).2)) z
      rw [hsl]
    have h := (heatVortex_navierStokes hν hs z).1
    rw [hlap1, hlap2, hsl, heatPressure_eq ha] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [eventually_heatWidth_pos ha] with t ht
    rw [heatVelocity_eq ht, isoVelocity_eq]

/-- The isolated vortex has zero Navier–Stokes residual with its radial pressure. -/
theorem isolated_nsResidual {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (z : Plane) :
    nsResidual ν (isoVelocity ν) (isoPressure ν) s z = 0 := by
  rw [nsResidual, ((isolated_vortex hν hs).2.2.2.2.2.2 z).deriv]
  abel

/-! ### The lattice sums -/

/-- Absolute convergence of the off-diagonal double sum, and its value
`∑_{i≠j} f_i g_j = (∑ f)(∑ g) - ∑ f_i g_i`. -/
theorem offDiag_tsum {f g : ℤ → ℝ} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) :
    Summable (fun p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)) => f p.1.1 * g p.1.2) ∧
    ∑' p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)), f p.1.1 * g p.1.2 =
      (∑' n, f n) * (∑' n, g n) - ∑' n, f n * g n := by
  have hF : Summable (fun x : ℤ × ℤ => f x.1 * g x.2) := summable_mul_of_summable_norm hf hg
  refine ⟨hF.subtype _, ?_⟩
  have h1 := tsum_mul_tsum_of_summable_norm hf hg
  have h2 := hF.tsum_subtype_add_tsum_subtype_compl {p : ℤ × ℤ | p.1 ≠ p.2}
  let e : ℤ ≃ ↥({p : ℤ × ℤ | p.1 ≠ p.2}ᶜ) :=
    { toFun := fun n => ⟨(n, n), by simp⟩
      invFun := fun x => x.1.1
      left_inv := fun n => rfl
      right_inv := fun x => by
        obtain ⟨⟨i, j⟩, h⟩ := x
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at h
        subst h
        rfl }
  have h3 : ∑' x : ↥({p : ℤ × ℤ | p.1 ≠ p.2}ᶜ), f x.1.1 * g x.1.2 = ∑' n, f n * g n :=
    (e.tsum_eq (fun x => f x.1.1 * g x.1.2)).symm
  rw [h1, ← h2, h3]
  ring

section Fixed

variable {ν c s : ℝ}

theorem isoVelocity_apply (ν s : ℝ) (w : Plane) :
    isoVelocity ν s w = (u1 (heatWidth ν s) w, u2 (heatWidth ν s) w) := by
  rw [isoVelocity_eq]; rfl

theorem xd {f : ℝ → Plane → ℝ} {a : ℝ} (h : GF a a f) : XDecay (f a) :=
  h.xdecay ⟨le_rfl, le_rfl⟩

theorem hasSum_periodicVelocity (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (z : Plane) :
    HasSum (fun n : ℤ => imageVelocity ν c n s z)
      (latticeSum c (u1 (heatWidth ν s)) z, latticeSum c (u2 (heatWidth ν s)) z) := by
  have h := ((xd (gf_u1 ha)).hasSum hc z).prodMk ((xd (gf_u2 ha)).hasSum hc z)
  convert h using 1
  funext n
  exact isoVelocity_apply ν s _

theorem periodicVelocity_eq (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (z : Plane) :
    periodicVelocity ν c s z =
      (latticeSum c (u1 (heatWidth ν s)) z, latticeSum c (u2 (heatWidth ν s)) z) :=
  (hasSum_periodicVelocity hc ha z).tsum_eq

theorem periodicVelocity_fst (hc : c ≠ 0) (ha : 0 < heatWidth ν s) :
    (fun w => (periodicVelocity ν c s w).1) = latticeSum c (u1 (heatWidth ν s)) :=
  funext fun w => by rw [periodicVelocity_eq hc ha]

theorem periodicVelocity_snd (hc : c ≠ 0) (ha : 0 < heatWidth ν s) :
    (fun w => (periodicVelocity ν c s w).2) = latticeSum c (u2 (heatWidth ν s)) :=
  funext fun w => by rw [periodicVelocity_eq hc ha]

theorem periodicPressure_eq (ν c s : ℝ) :
    periodicPressure ν c s = latticeSum c (pExp (heatWidth ν s)) := rfl

/-- Components of the isolated velocity as explicit functions of the width. -/
def uc (k : Fin 2) (a : ℝ) (w : Plane) : ℝ := vcomp (vExp a w) k

theorem gf_uc {A₁ A₂ : ℝ} (hA : 0 < A₁) (k : Fin 2) : GF A₁ A₂ (uc k) := by
  fin_cases k
  · exact gf_u1 hA
  · exact gf_u2 hA

/-- The cross stress is the full tensor product of the lattice sums minus the diagonal. -/
theorem crossStress_eq (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (w : Plane) (k l : Fin 2) :
    crossStress ν c s w k l =
      latticeSum c (uc k (heatWidth ν s)) w * latticeSum c (uc l (heatWidth ν s)) w -
        latticeSum c (fun x => uc k (heatWidth ν s) x * uc l (heatWidth ν s) x) w := by
  have hf := (xd (gf_uc ha k)).summable_norm hc w
  have hg := (xd (gf_uc ha l)).summable_norm hc w
  have h := (offDiag_tsum hf hg).2
  simp only [crossStress, imageVelocity, isoVelocity_eq]
  exact h

theorem summable_crossStress (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (w : Plane)
    (k l : Fin 2) :
    Summable (fun p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)) =>
      vcomp (imageVelocity ν c p.1.1 s w) k * vcomp (imageVelocity ν c p.1.2 s w) l) := by
  have hf := (xd (gf_uc ha k)).summable_norm hc w
  have hg := (xd (gf_uc ha l)).summable_norm hc w
  have h := (offDiag_tsum hf hg).1
  simp only [imageVelocity, isoVelocity_eq]
  exact h

end Fixed

/-! ### Termwise calculus at a fixed width `a > 0` -/

section Width

variable {c a : ℝ}

theorem uc_zero : uc 0 = u1 := rfl
theorem uc_one : uc 1 = u2 := rfl

/-- `∂ₓ(V₁V₁)` termwise. -/
def d00x (a : ℝ) (w : Plane) : ℝ := u1x a w * u1 a w + u1 a w * u1x a w
/-- `∂_y(V₂V₁)` termwise. -/
def d10y (a : ℝ) (w : Plane) : ℝ := u2y a w * u1 a w + u2 a w * u1y a w
/-- `∂ₓ(V₁V₂)` termwise. -/
def d01x (a : ℝ) (w : Plane) : ℝ := u1x a w * u2 a w + u1 a w * u2x a w
/-- `∂_y(V₂V₂)` termwise. -/
def d11y (a : ℝ) (w : Plane) : ℝ := u2y a w * u2 a w + u2 a w * u2y a w

theorem gf_d00x {A₁ A₂ : ℝ} (hA : 0 < A₁) : GF A₁ A₂ d00x := by
  unfold d00x; exact GF.add (gf_mul (gf_u1x hA) (gf_u1 hA)) (gf_mul (gf_u1 hA) (gf_u1x hA))
theorem gf_d10y {A₁ A₂ : ℝ} (hA : 0 < A₁) : GF A₁ A₂ d10y := by
  unfold d10y; exact GF.add (gf_mul (gf_u2y hA) (gf_u1 hA)) (gf_mul (gf_u2 hA) (gf_u1y hA))
theorem gf_d01x {A₁ A₂ : ℝ} (hA : 0 < A₁) : GF A₁ A₂ d01x := by
  unfold d01x; exact GF.add (gf_mul (gf_u1x hA) (gf_u2 hA)) (gf_mul (gf_u1 hA) (gf_u2x hA))
theorem gf_d11y {A₁ A₂ : ℝ} (hA : 0 < A₁) : GF A₁ A₂ d11y := by
  unfold d11y; exact GF.add (gf_mul (gf_u2y hA) (gf_u2 hA)) (gf_mul (gf_u2 hA) (gf_u2y hA))

theorem dX_u1 (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (u1 a) (t, z.2)) (latticeSum c (u1x a) z) z.1 :=
  hasDerivAt_latticeSum_x hc (hx_u1 a) (xd (gf_u1 ha)) (xd (gf_u1x ha)) z
theorem dY_u1 (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (u1 a) (z.1, t)) (latticeSum c (u1y a) z) z.2 :=
  hasDerivAt_latticeSum_y hc (hy_u1 a) (xd (gf_u1 ha)) (xd (gf_u1y ha)) z
theorem dX_u2 (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (u2 a) (t, z.2)) (latticeSum c (u2x a) z) z.1 :=
  hasDerivAt_latticeSum_x hc (hx_u2 a) (xd (gf_u2 ha)) (xd (gf_u2x ha)) z
theorem dY_u2 (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (u2 a) (z.1, t)) (latticeSum c (u2y a) z) z.2 :=
  hasDerivAt_latticeSum_y hc (hy_u2 a) (xd (gf_u2 ha)) (xd (gf_u2y ha)) z
theorem dX_u1x (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (u1x a) (t, z.2)) (latticeSum c (u1xx a) z) z.1 :=
  hasDerivAt_latticeSum_x hc (hx_u1x a) (xd (gf_u1x ha)) (xd (gf_u1xx ha)) z
theorem dY_u1y (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (u1y a) (z.1, t)) (latticeSum c (u1yy a) z) z.2 :=
  hasDerivAt_latticeSum_y hc (hy_u1y a) (xd (gf_u1y ha)) (xd (gf_u1yy ha)) z
theorem dX_u2x (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (u2x a) (t, z.2)) (latticeSum c (u2xx a) z) z.1 :=
  hasDerivAt_latticeSum_x hc (hx_u2x a) (xd (gf_u2x ha)) (xd (gf_u2xx ha)) z
theorem dY_u2y (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (u2y a) (z.1, t)) (latticeSum c (u2yy a) z) z.2 :=
  hasDerivAt_latticeSum_y hc (hy_u2y a) (xd (gf_u2y ha)) (xd (gf_u2yy ha)) z
theorem dX_p (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (pExp a) (t, z.2)) (latticeSum c (prX a) z) z.1 :=
  hasDerivAt_latticeSum_x hc (hx_p a) (xd (gf_p ha)) (xd (gf_prX ha)) z
theorem dY_p (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (pExp a) (z.1, t)) (latticeSum c (prY a) z) z.2 :=
  hasDerivAt_latticeSum_y hc (hy_p a) (xd (gf_p ha)) (xd (gf_prY ha)) z
theorem dX_m00 (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (fun x => u1 a x * u1 a x) (t, z.2))
      (latticeSum c (d00x a) z) z.1 :=
  hasDerivAt_latticeSum_x hc (g := fun x => u1 a x * u1 a x) (g' := d00x a)
    (fun w => (hx_u1 a w).mul (hx_u1 a w)) (xd (gf_mul (gf_u1 ha) (gf_u1 ha)))
    (xd (gf_d00x ha)) z
theorem dY_m10 (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (fun x => u2 a x * u1 a x) (z.1, t))
      (latticeSum c (d10y a) z) z.2 :=
  hasDerivAt_latticeSum_y hc (g := fun x => u2 a x * u1 a x) (g' := d10y a)
    (fun w => (hy_u2 a w).mul (hy_u1 a w)) (xd (gf_mul (gf_u2 ha) (gf_u1 ha)))
    (xd (gf_d10y ha)) z
theorem dX_m01 (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (fun x => u1 a x * u2 a x) (t, z.2))
      (latticeSum c (d01x a) z) z.1 :=
  hasDerivAt_latticeSum_x hc (g := fun x => u1 a x * u2 a x) (g' := d01x a)
    (fun w => (hx_u1 a w).mul (hx_u2 a w)) (xd (gf_mul (gf_u1 ha) (gf_u2 ha)))
    (xd (gf_d01x ha)) z
theorem dY_m11 (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun t => latticeSum c (fun x => u2 a x * u2 a x) (z.1, t))
      (latticeSum c (d11y a) z) z.2 :=
  hasDerivAt_latticeSum_y hc (g := fun x => u2 a x * u2 a x) (g' := d11y a)
    (fun w => (hy_u2 a w).mul (hy_u2 a w)) (xd (gf_mul (gf_u2 ha) (gf_u2 ha)))
    (xd (gf_d11y ha)) z

theorem lat_add_eq (hc : c ≠ 0) {f g k : Plane → ℝ} (h : ∀ w, f w + g w = k w)
    (hf : XDecay f) (hg : XDecay g) (z : Plane) :
    latticeSum c f z + latticeSum c g z = latticeSum c k z := by
  have h2 : HasSum (fun n : ℤ => k (shift c n z)) (latticeSum c f z + latticeSum c g z) := by
    convert (hf.hasSum hc z).add (hg.hasSum hc z) using 1
    funext n
    exact (h _).symm
  exact h2.tsum_eq.symm

theorem lat_add3_zero (hc : c ≠ 0) {f g k : Plane → ℝ} (h : ∀ w, f w + g w + k w = 0)
    (hf : XDecay f) (hg : XDecay g) (hk : XDecay k) (z : Plane) :
    latticeSum c f z + latticeSum c g z + latticeSum c k z = 0 := by
  have h2 := ((hf.hasSum hc z).add (hg.hasSum hc z)).add (hk.hasSum hc z)
  have h3 : HasSum (fun n : ℤ => f (shift c n z) + g (shift c n z) + k (shift c n z)) 0 := by
    convert hasSum_zero using 1
    funext n
    exact h _
  exact h2.unique h3

end Width

/-! ### The residual identity -/

section Residual

variable {ν c s : ℝ}

theorem crossStress_fun (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (k l : Fin 2) :
    (fun w => crossStress ν c s w k l) = fun w =>
      latticeSum c (uc k (heatWidth ν s)) w * latticeSum c (uc l (heatWidth ν s)) w -
        latticeSum c (fun x => uc k (heatWidth ν s) x * uc l (heatWidth ν s) x) w :=
  funext fun w => crossStress_eq hc ha w k l

/-- Termwise time derivative: `∂ₛV_c = ν ∑ₙ ∂ₐV(·-nc)`. -/
theorem hasDerivAt_periodicVelocity (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    HasDerivAt (fun t => periodicVelocity ν c t z)
      (ν * latticeSum c (u1a (heatWidth ν s)) z, ν * latticeSum c (u2a (heatWidth ν s)) z) s := by
  have ha := heatWidth_pos hν hs
  have ha2 : 0 < heatWidth ν s / 2 := half_pos ha
  have h1 : HasDerivAt (fun t => (periodicVelocity ν c t z).1)
      (ν * latticeSum c (u1a (heatWidth ν s)) z) s := by
    have hW := hasDerivAt_latticeSum_width (G := u1) (G' := u1a) hc ha
      (fun b hb w => ha_u1 hb.ne' w) (xd (gf_u1 ha)) (gf_u1a ha2).unif z
    refine ((hW.comp s (hasDerivAt_heatWidth ν s)).congr_of_eventuallyEq ?_).congr_deriv
      (mul_comm _ _)
    filter_upwards [eventually_heatWidth_pos ha] with t ht
    simp only [Function.comp_apply]
    rw [periodicVelocity_eq hc ht]
  have h2 : HasDerivAt (fun t => (periodicVelocity ν c t z).2)
      (ν * latticeSum c (u2a (heatWidth ν s)) z) s := by
    have hW := hasDerivAt_latticeSum_width (G := u2) (G' := u2a) hc ha
      (fun b hb w => ha_u2 hb.ne' w) (xd (gf_u2 ha)) (gf_u2a ha2).unif z
    refine ((hW.comp s (hasDerivAt_heatWidth ν s)).congr_of_eventuallyEq ?_).congr_deriv
      (mul_comm _ _)
    filter_upwards [eventually_heatWidth_pos ha] with t ht
    simp only [Function.comp_apply]
    rw [periodicVelocity_eq hc ht]
  exact h1.prodMk h2

theorem lap_periodicVelocity_fst (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (z : Plane) :
    lap (fun t w => (periodicVelocity ν c t w).1) s z =
      latticeSum c (u1a (heatWidth ν s)) z := by
  show partialX (partialX (fun w => (periodicVelocity ν c s w).1)) z +
    partialY (partialY (fun w => (periodicVelocity ν c s w).1)) z = _
  rw [periodicVelocity_fst hc ha,
    partialX_latticeSum hc (hx_u1 _) (xd (gf_u1 ha)) (xd (gf_u1x ha)),
    partialY_latticeSum hc (hy_u1 _) (xd (gf_u1 ha)) (xd (gf_u1y ha))]
  rw [show partialX (latticeSum c (u1x (heatWidth ν s))) z =
      latticeSum c (u1xx (heatWidth ν s)) z from (dX_u1x hc ha z).deriv,
    show partialY (latticeSum c (u1y (heatWidth ν s))) z =
      latticeSum c (u1yy (heatWidth ν s)) z from (dY_u1y hc ha z).deriv]
  exact lat_add_eq hc (lap_u1 _) (xd (gf_u1xx ha)) (xd (gf_u1yy ha)) z

theorem lap_periodicVelocity_snd (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (z : Plane) :
    lap (fun t w => (periodicVelocity ν c t w).2) s z =
      latticeSum c (u2a (heatWidth ν s)) z := by
  show partialX (partialX (fun w => (periodicVelocity ν c s w).2)) z +
    partialY (partialY (fun w => (periodicVelocity ν c s w).2)) z = _
  rw [periodicVelocity_snd hc ha,
    partialX_latticeSum hc (hx_u2 _) (xd (gf_u2 ha)) (xd (gf_u2x ha)),
    partialY_latticeSum hc (hy_u2 _) (xd (gf_u2 ha)) (xd (gf_u2y ha))]
  rw [show partialX (latticeSum c (u2x (heatWidth ν s))) z =
      latticeSum c (u2xx (heatWidth ν s)) z from (dX_u2x hc ha z).deriv,
    show partialY (latticeSum c (u2y (heatWidth ν s))) z =
      latticeSum c (u2yy (heatWidth ν s)) z from (dY_u2y hc ha z).deriv]
  exact lat_add_eq hc (lap_u2 _) (xd (gf_u2xx ha)) (xd (gf_u2yy ha)) z

theorem advection_periodicVelocity (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (z : Plane) :
    advection (periodicVelocity ν c s) z =
      (latticeSum c (u1 (heatWidth ν s)) z * latticeSum c (u1x (heatWidth ν s)) z +
        latticeSum c (u2 (heatWidth ν s)) z * latticeSum c (u1y (heatWidth ν s)) z,
       latticeSum c (u1 (heatWidth ν s)) z * latticeSum c (u2x (heatWidth ν s)) z +
        latticeSum c (u2 (heatWidth ν s)) z * latticeSum c (u2y (heatWidth ν s)) z) := by
  simp only [advection, scalarAdvection]
  rw [periodicVelocity_fst hc ha, periodicVelocity_snd hc ha, periodicVelocity_eq hc ha z]
  rw [show partialX (latticeSum c (u1 (heatWidth ν s))) z =
      latticeSum c (u1x (heatWidth ν s)) z from (dX_u1 hc ha z).deriv,
    show partialY (latticeSum c (u1 (heatWidth ν s))) z =
      latticeSum c (u1y (heatWidth ν s)) z from (dY_u1 hc ha z).deriv,
    show partialX (latticeSum c (u2 (heatWidth ν s))) z =
      latticeSum c (u2x (heatWidth ν s)) z from (dX_u2 hc ha z).deriv,
    show partialY (latticeSum c (u2 (heatWidth ν s))) z =
      latticeSum c (u2y (heatWidth ν s)) z from (dY_u2 hc ha z).deriv]

theorem gradient_periodicPressure (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (z : Plane) :
    gradient (periodicPressure ν c s) z =
      (latticeSum c (prX (heatWidth ν s)) z, latticeSum c (prY (heatWidth ν s)) z) := by
  rw [periodicPressure_eq]
  exact Prod.ext (dX_p hc ha z).deriv (dY_p hc ha z).deriv

theorem tensorDiv_crossStress (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (z : Plane) :
    tensorDiv (crossStress ν c s) z =
      (latticeSum c (u1x (heatWidth ν s)) z * latticeSum c (u1 (heatWidth ν s)) z +
          latticeSum c (u1 (heatWidth ν s)) z * latticeSum c (u1x (heatWidth ν s)) z -
          latticeSum c (d00x (heatWidth ν s)) z +
        (latticeSum c (u2y (heatWidth ν s)) z * latticeSum c (u1 (heatWidth ν s)) z +
          latticeSum c (u2 (heatWidth ν s)) z * latticeSum c (u1y (heatWidth ν s)) z -
          latticeSum c (d10y (heatWidth ν s)) z),
       latticeSum c (u1x (heatWidth ν s)) z * latticeSum c (u2 (heatWidth ν s)) z +
          latticeSum c (u1 (heatWidth ν s)) z * latticeSum c (u2x (heatWidth ν s)) z -
          latticeSum c (d01x (heatWidth ν s)) z +
        (latticeSum c (u2y (heatWidth ν s)) z * latticeSum c (u2 (heatWidth ν s)) z +
          latticeSum c (u2 (heatWidth ν s)) z * latticeSum c (u2y (heatWidth ν s)) z -
          latticeSum c (d11y (heatWidth ν s)) z)) := by
  unfold tensorDiv
  rw [crossStress_fun hc ha 0 0, crossStress_fun hc ha 1 0, crossStress_fun hc ha 0 1,
    crossStress_fun hc ha 1 1]
  simp only [uc_zero, uc_one]
  refine Prod.ext ?_ ?_
  · exact congrArg₂ (· + ·)
      (((dX_u1 hc ha z).mul (dX_u1 hc ha z)).sub (dX_m00 hc ha z)).deriv
      (((dY_u2 hc ha z).mul (dY_u1 hc ha z)).sub (dY_m10 hc ha z)).deriv
  · exact congrArg₂ (· + ·)
      (((dX_u1 hc ha z).mul (dX_u2 hc ha z)).sub (dX_m01 hc ha z)).deriv
      (((dY_u2 hc ha z).mul (dY_u2 hc ha z)).sub (dY_m11 hc ha z)).deriv

/-- **The residual identity** (tex lines 2211–2215). After summing the isolated radial
pressures into `p^p_c`, the Navier–Stokes residual of the periodization `V_c` is the divergence
of the cross stress `Q_c = ∑_{i≠j} V_i ⊗ V_j`:
`∂ₛV_c = νΔV_c - V_c·∇V_c - ∇p^p_c + div Q_c`, for `ν > 0`, `c ≠ 0`, `s ≥ 0`. -/
theorem periodicVelocity_residual (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    HasDerivAt (fun t => periodicVelocity ν c t z)
      (ν • (lap (fun t w => (periodicVelocity ν c t w).1) s z,
            lap (fun t w => (periodicVelocity ν c t w).2) s z) -
        advection (periodicVelocity ν c s) z - gradient (periodicPressure ν c s) z +
        tensorDiv (crossStress ν c s) z) s := by
  have ha := heatWidth_pos hν hs
  refine (hasDerivAt_periodicVelocity hν hc hs z).congr_deriv ?_
  rw [lap_periodicVelocity_fst hc ha, lap_periodicVelocity_snd hc ha,
    advection_periodicVelocity hc ha, gradient_periodicPressure hc ha,
    tensorDiv_crossStress hc ha]
  have hdiv := lat_add_eq hc (k := fun _ => 0) (div_u (heatWidth ν s))
    (xd (gf_u1x ha)) (xd (gf_u2y ha)) z
  have hzero : latticeSum c (fun _ : Plane => (0 : ℝ)) z = 0 := by
    simp [latticeSum]
  rw [hzero] at hdiv
  have he1 : latticeSum c (prX (heatWidth ν s)) z + latticeSum c (d00x (heatWidth ν s)) z +
      latticeSum c (d10y (heatWidth ν s)) z = 0 :=
    lat_add3_zero hc (fun w => euler_u1 _ w) (xd (gf_prX ha)) (xd (gf_d00x ha))
      (xd (gf_d10y ha)) z
  have he2 : latticeSum c (prY (heatWidth ν s)) z + latticeSum c (d01x (heatWidth ν s)) z +
      latticeSum c (d11y (heatWidth ν s)) z = 0 :=
    lat_add3_zero hc (fun w => euler_u2 _ w) (xd (gf_prY ha)) (xd (gf_d01x ha))
      (xd (gf_d11y ha)) z
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_mk, smul_eq_mul, Prod.fst_add, Prod.fst_sub]
    linear_combination (-(latticeSum c (u1 (heatWidth ν s)) z)) * hdiv + he1
  · simp only [Prod.smul_mk, smul_eq_mul, Prod.snd_add, Prod.snd_sub]
    linear_combination (-(latticeSum c (u2 (heatWidth ν s)) z)) * hdiv + he2

/-- The residual identity in the manuscript's words: the Navier–Stokes residual of `V_c`
with the summed isolated pressures `p^p_c` is `div Q_c` (tex lines 2211–2213). -/
theorem periodicVelocity_nsResidual (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    nsResidual ν (periodicVelocity ν c) (periodicPressure ν c) s z =
      tensorDiv (crossStress ν c s) z := by
  rw [nsResidual, (periodicVelocity_residual hν hc hs z).deriv]
  abel

end Residual

/-! ### Well-posedness of the statement: convergence and genuine derivatives -/

/-- `f` has a genuine `x`-derivative at `z`, equal to the classical `partialX f z`. -/
def HasPartialX (f : Plane → ℝ) (z : Plane) : Prop :=
  HasDerivAt (fun t => f (t, z.2)) (partialX f z) z.1

/-- `f` has a genuine `y`-derivative at `z`, equal to the classical `partialY f z`. -/
def HasPartialY (f : Plane → ℝ) (z : Plane) : Prop :=
  HasDerivAt (fun t => f (z.1, t)) (partialY f z) z.2

theorem hasPartialX_of {f : Plane → ℝ} {z : Plane} {v : ℝ}
    (h : HasDerivAt (fun t => f (t, z.2)) v z.1) : HasPartialX f z := by
  unfold HasPartialX partialX
  rw [h.deriv]
  exact h

theorem hasPartialY_of {f : Plane → ℝ} {z : Plane} {v : ℝ}
    (h : HasDerivAt (fun t => f (z.1, t)) v z.2) : HasPartialY f z := by
  unfold HasPartialY partialY
  rw [h.deriv]
  exact h

section WellPosed

variable {ν c s : ℝ}

/-- The series defining `V_c` converges absolutely (tex line 2205). -/
theorem summable_imageVelocity (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    Summable (fun n : ℤ => imageVelocity ν c n s z) :=
  (hasSum_periodicVelocity hc (heatWidth_pos hν hs) z).summable

/-- The series of isolated pressures converges absolutely (tex line 2211). -/
theorem summable_isoPressure (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    Summable (fun n : ℤ => isoPressure ν s (shift c n z)) :=
  (xd (gf_p (heatWidth_pos hν hs))).summable hc z

/-- Every spatial partial derivative entering `periodicVelocity_residual` is a genuine
derivative (so the classical operators `partialX`, `partialY` take no junk values there). -/
theorem periodic_classical_derivatives (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (z : Plane) :
    HasPartialX (fun w => (periodicVelocity ν c s w).1) z ∧
    HasPartialY (fun w => (periodicVelocity ν c s w).1) z ∧
    HasPartialX (fun w => (periodicVelocity ν c s w).2) z ∧
    HasPartialY (fun w => (periodicVelocity ν c s w).2) z ∧
    HasPartialX (partialX (fun w => (periodicVelocity ν c s w).1)) z ∧
    HasPartialY (partialY (fun w => (periodicVelocity ν c s w).1)) z ∧
    HasPartialX (partialX (fun w => (periodicVelocity ν c s w).2)) z ∧
    HasPartialY (partialY (fun w => (periodicVelocity ν c s w).2)) z ∧
    HasPartialX (periodicPressure ν c s) z ∧ HasPartialY (periodicPressure ν c s) z ∧
    HasPartialX (fun w => crossStress ν c s w 0 0) z ∧
    HasPartialY (fun w => crossStress ν c s w 1 0) z ∧
    HasPartialX (fun w => crossStress ν c s w 0 1) z ∧
    HasPartialY (fun w => crossStress ν c s w 1 1) z := by
  have ha := heatWidth_pos hν hs
  rw [periodicVelocity_fst hc ha, periodicVelocity_snd hc ha,
    partialX_latticeSum hc (hx_u1 _) (xd (gf_u1 ha)) (xd (gf_u1x ha)),
    partialY_latticeSum hc (hy_u1 _) (xd (gf_u1 ha)) (xd (gf_u1y ha)),
    partialX_latticeSum hc (hx_u2 _) (xd (gf_u2 ha)) (xd (gf_u2x ha)),
    partialY_latticeSum hc (hy_u2 _) (xd (gf_u2 ha)) (xd (gf_u2y ha)),
    periodicPressure_eq, crossStress_fun hc ha 0 0, crossStress_fun hc ha 1 0,
    crossStress_fun hc ha 0 1, crossStress_fun hc ha 1 1]
  simp only [uc_zero, uc_one]
  exact ⟨hasPartialX_of (dX_u1 hc ha z), hasPartialY_of (dY_u1 hc ha z),
    hasPartialX_of (dX_u2 hc ha z), hasPartialY_of (dY_u2 hc ha z),
    hasPartialX_of (dX_u1x hc ha z), hasPartialY_of (dY_u1y hc ha z),
    hasPartialX_of (dX_u2x hc ha z), hasPartialY_of (dY_u2y hc ha z),
    hasPartialX_of (dX_p hc ha z), hasPartialY_of (dY_p hc ha z),
    hasPartialX_of (((dX_u1 hc ha z).mul (dX_u1 hc ha z)).sub (dX_m00 hc ha z)),
    hasPartialY_of (((dY_u2 hc ha z).mul (dY_u1 hc ha z)).sub (dY_m10 hc ha z)),
    hasPartialX_of (((dX_u1 hc ha z).mul (dX_u2 hc ha z)).sub (dX_m01 hc ha z)),
    hasPartialY_of (((dY_u2 hc ha z).mul (dY_u2 hc ha z)).sub (dY_m11 hc ha z))⟩

/-- **Unit B0146** (`eq:st18-t00144`, tex lines 2196–2216), for `ν > 0`, `c ≠ 0`, `s ≥ 0`.
(1) `a = 1 + σ` and `ψ^p = -(2/a)e^{-|x|²/(4a)}`;
(2) the isolated vortex `V = ∇^⊥ψ^p` is divergence free and tangential, its vorticity and
pressure are radial, `V·∇ω^p = 0`, `V·∇V = -∇P`, and `(V, P)` solves Navier–Stokes;
(3) the series defining `V_c`, `p^p_c` and `Q_c` converge absolutely;
(4) the Navier–Stokes residual of `V_c` with pressure `p^p_c` is `div Q_c`. -/
theorem heat_vortex_periodization (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) :
    heatWidth ν s = 1 + slowTime ν s ∧
    (∀ x, streamP ν s x =
      -(2 / heatWidth ν s) * Real.exp (-(radiusSq x / (4 * heatWidth ν s)))) ∧
    ((∀ z, divergence (isoVelocity ν s) z = 0) ∧
      (∀ z : Plane, (isoVelocity ν s z).1 * z.1 + (isoVelocity ν s z).2 * z.2 = 0) ∧
      (∃ f : ℝ → ℝ, ∀ z, isoVorticity ν s z = f (radiusSq z)) ∧
      (∃ f : ℝ → ℝ, ∀ z, isoPressure ν s z = f (radiusSq z)) ∧
      (∀ z, scalarAdvection (isoVelocity ν s) (isoVorticity ν s) z = 0) ∧
      (∀ z, advection (isoVelocity ν s) z = -gradient (isoPressure ν s) z) ∧
      (∀ z, HasDerivAt (fun t => isoVelocity ν t z)
        (ν • (lap (fun t w => (isoVelocity ν t w).1) s z,
              lap (fun t w => (isoVelocity ν t w).2) s z) -
          advection (isoVelocity ν s) z - gradient (isoPressure ν s) z) s)) ∧
    (∀ z, Summable (fun n : ℤ => imageVelocity ν c n s z) ∧
      Summable (fun n : ℤ => isoPressure ν s (shift c n z)) ∧
      ∀ k l : Fin 2, Summable (fun p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)) =>
        vcomp (imageVelocity ν c p.1.1 s z) k * vcomp (imageVelocity ν c p.1.2 s z) l)) ∧
    (∀ z, HasDerivAt (fun t => periodicVelocity ν c t z)
      (ν • (lap (fun t w => (periodicVelocity ν c t w).1) s z,
            lap (fun t w => (periodicVelocity ν c t w).2) s z) -
        advection (periodicVelocity ν c s) z - gradient (periodicPressure ν c s) z +
        tensorDiv (crossStress ν c s) z) s) ∧
    (∀ z, nsResidual ν (periodicVelocity ν c) (periodicPressure ν c) s z =
      tensorDiv (crossStress ν c s) z) :=
  ⟨rfl, streamP_apply ν s, isolated_vortex hν hs,
    fun z => ⟨summable_imageVelocity hν hc hs z, summable_isoPressure hν hc hs z,
      fun k l => summable_crossStress hc (heatWidth_pos hν hs) z k l⟩,
    periodicVelocity_residual hν hc hs, periodicVelocity_nsResidual hν hc hs⟩

end WellPosed

end UnforcedLeray.B0146
