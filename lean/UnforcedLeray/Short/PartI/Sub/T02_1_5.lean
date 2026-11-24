import UnforcedLeray.Short.PartI.Sub.T02_1

/-!
# Part I, task `PartI:T02/1/5`: from the Leray form to a classical pressure (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288 (the
bounded periodic pressure choice of Gallay-Slijepcevic, line 277; here only the existence of a
smooth periodic pressure is needed, the gauge is `PartI:T02/2`).

Target: `LerayVelocityToClassical` (`Short/PartI/Sub/T02_1.lean`).  Mathematics.  Put
`F(s,z) = ∂ₛv + v·∇v - νΔv` (the momentum residual with zero pressure).  By the field `leray`
of `IsLerayVelocityOn`, for `0 < s < T` the smooth periodic field `F(s,·)` is `L²(cell)`-
orthogonal to every smooth periodic solenoidal field that vanishes for `|η|` large.  Testing with
`φ = ∇^⊥χ = (-∂_η χ, ∂_q χ)` gives `curl F(s,·) = 0`; testing with `φ = (ψ(η), 0)` gives that the
horizontal mean of `F₁(s,·,η)` vanishes for every `η`.  Then the radial potential
`p(x) = -∫₀¹ x·F(tx) dt` satisfies `∇p = -F` (Poincaré lemma on the plane), and is `c`-periodic in
`q` because `p(q+c,η) - p(q,η) = -∫_q^{q+c} F₁(r,η) dr = -∫₀^c F₁(r,η) dr = 0`.  Smoothness up to
`s = 0` and `s = T` is the smoothness of a parametric integral over `[0,1]` whose integrand is
smooth on the closed set `[0,T] × ℝ² × [0,1]`; the force `F` is replaced by its one-sided
version (built from `fderivWithin` of the jointly smooth `v`), which equals the momentum residual
for `0 < s < T`.

The proof below is complete modulo the six leaf `Prop`s (ids `PartI:T02/1/5/1` ... `/6`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **The radial (Poincaré) potential** of a vector field `G` on the plane:
`radialPot G x = -∫₀¹ (x₁ G₁(t x) + x₂ G₂(t x)) dt`.  For a smooth curl-free `G` it satisfies
`∇(radialPot G) = -G`. -/
def radialPot (G : Plane → Vec) (x : Plane) : ℝ :=
  -(∫ t in (0 : ℝ)..1, (x.1 * G (t • x) 0 + x.2 * G (t • x) 1))

/-- `g` is `L²(cell)`-orthogonal to every smooth `c`-periodic solenoidal field that vanishes for
`|η|` large (the `leray` condition of `IsLerayVelocityOn` at one time). -/
def OrthToSolenoidalTests (c : ℝ) (g : Plane → Vec) : Prop :=
  ∀ φ : Plane → Vec, ContDiff ℝ ∞ φ → Cyl.IsPeriodic c φ →
    (∀ z, Cyl.divergence φ z = 0) → (∃ R : ℝ, ∀ z : Plane, R < |z.2| → φ z = 0) →
    ∫ z in Cyl.cell c, inner ℝ (g z) (φ z) = 0

/-! ### The six leaf statements -/

/-- **Leaf 1** (parametric integral on a closed parameter set; a gap in Mathlib, which has
`hasFDerivAt_integral_of_dominated_of_fderiv_le` only for parameters in a neighbourhood).  If
`G(x,t)` is `C^∞` on `S × [0,1]` with `S = [0,T] × ℝ²` (a closed convex set with nonempty
interior, so `ContDiffOn` is the usual one-sided notion), then `x ↦ ∫₀¹ G(x,t) dt` is `C^∞` on
`S`.  Proof idea: induction on the order with `contDiffOn_succ_iff_fderivWithin`, differentiating
under the integral with `fderivWithin` on the convex set `S`, using the mean value inequality
along segments in `S` and uniform continuity of the first derivative on compact sets; the
induction hypothesis is applied to the `CLM`-valued integrand `fderivWithin ℝ (G · t) S x`. -/
def ClosedParamIntegralSmooth : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ G : ℝ × Plane → ℝ → ℝ,
    ContDiffOn ℝ ∞ (fun y : (ℝ × Plane) × ℝ => G y.1 y.2)
      ((Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) ×ˢ Icc (0 : ℝ) 1) →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ∫ t in (0 : ℝ)..1, G x t) (Icc (0 : ℝ) T ×ˢ univ)

/-- **Leaf 2** (the one-sided force).  For a velocity solving the system modulo gradients, the
momentum residual with zero pressure agrees on `(0,T)` with a force `G` that is jointly `C^∞` on
the closed set `[0,T] × ℝ²` and `c`-periodic in `q`.  Proof idea: with `V x = v x.1 x.2` and
`S = Icc 0 T ×ˢ univ` (`UniqueDiffOn`), the maps `fderivWithin ℝ V S` and
`fderivWithin ℝ (fderivWithin ℝ V S) S` are `ContDiffOn` (`ContDiffOn.fderivWithin`); put
`G s z = D(s,z)(1,0) + (v s z 0) D(s,z)(0,e₁) + ... - ν (D²(s,z)... + ...)` with the same
polynomial expression as `Train.momentumResidual` but with `deriv`, `partialQ`, `partialEta`
replaced by evaluations of `D` and `D²`.  On the open set `Ioo 0 T ×ˢ univ ⊆ S`, `fderivWithin`
is `fderiv` and the chain rule identifies these evaluations with `deriv (fun t => v t z) s`,
`Cyl.partialQ`, `Cyl.partialEta` and their iterates.  Periodicity: `V (s,z+(c,0)) = V (s,z)` on
`S` and `fderivWithin` commutes with the translation, which maps `S` to `S`. -/
def LerayForceSmooth : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec), 0 < ν → 1 ≤ c → 0 < T → IsLerayVelocityOn ν c T v →
    ∃ G : ℝ → Plane → Vec,
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
      (∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (G s)) ∧
      ∀ s ∈ Ioo (0 : ℝ) T, ∀ z, G s z = Train.momentumResidual ν v (fun _ _ => (0 : ℝ)) s z

/-- **Leaf 3** (curl-free part of the Leray orthogonality).  A smooth `c`-periodic field that is
orthogonal to all smooth periodic solenoidal fields vanishing for `|η|` large is curl free:
`∂_q g₂ = ∂_η g₁`.  Proof idea: for a cylinder test `χ` (`Sob.IsCylTest c χ`, smooth, periodic,
zero for `|η|` large) the field `φ = (-∂_η χ, ∂_q χ)` is admissible (`Sob.IsCylTest.dirDeriv`,
equality of mixed partials gives `div φ = 0`); integration by parts on the cell
(`Cyl.integral_cell_partialQ_mul`, `Cyl.integral_cell_partialEta_mul`, `Lib/Cylinder/IBP.lean`)
turns the hypothesis into `∫_cell (∂_η g₁ - ∂_q g₂) χ = 0` for all cylinder tests `χ`; the
fundamental lemma on the cylinder (`Sob.cylinder c`, `ae_zero`, `Lib/Sobolev/Cylinder.lean`)
and continuity of the periodic function `∂_η g₁ - ∂_q g₂` give the pointwise identity.  The
transfer `partialQ`/`partialEta` = `fderiv` is `Cyl.partialQ_eq_fderiv`. -/
def OrthCurlFree : Prop :=
  ∀ (c : ℝ) (g : Plane → Vec), 0 < c → ContDiff ℝ ∞ g → Cyl.IsPeriodic c g →
    OrthToSolenoidalTests c g →
    ∀ z, Cyl.partialQ (fun w => g w 1) z = Cyl.partialEta (fun w => g w 0) z

/-- **Leaf 4** (horizontal mean zero part of the Leray orthogonality).  Under the same
hypotheses, `∫₀^c g₁(q,η) dq = 0` for every `η`.  Proof idea: for `ψ : ℝ → ℝ` smooth with compact
support the field `φ(q,η) = (ψ(η), 0)` is smooth, periodic, solenoidal and vanishes for `|η|`
large; the hypothesis gives `∫ ψ(η) m(η) dη = 0` for `m(η) = ∫_{-c/2}^{c/2} g₁(q,η) dq`
(`Cyl.integral_cell_eq_integral_integral`, Fubini); `m` is continuous (parametric integral,
`continuous_parametric_intervalIntegral_of_continuous'`) so `m = 0`
(`ae_eq_zero_of_integral_contDiff_smul_eq_zero` plus continuity); `g₁(·,η)` is `c`-periodic, so
`∫₀^c = ∫_{-c/2}^{c/2}` (`Function.Periodic.intervalIntegral_add_eq`). -/
def OrthMeanZero : Prop :=
  ∀ (c : ℝ) (g : Plane → Vec), 0 < c → ContDiff ℝ ∞ g → Cyl.IsPeriodic c g →
    OrthToSolenoidalTests c g →
    ∀ η : ℝ, ∫ q in (0 : ℝ)..c, g (q, η) 0 = 0

/-- **Leaf 5** (the Poincaré lemma on the plane).  For a smooth curl-free field `G`,
`∇(radialPot G) = -G`.  Proof idea: differentiate under the integral sign (the integrand is
smooth in `(x,t)` on `ℝ² × ℝ`, `contDiff_parametric...`/`hasFDerivAt_integral_of_dominated_of_fderiv_le`
or `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`), use curl-freeness to
replace `t x_j ∂_i G_j(tx)` by `t x_j ∂_j G_i(tx)`, and `∂_t (t G_i(tx)) = G_i(tx) + t x_j ∂_j
G_i(tx)` with the fundamental theorem of calculus on `[0,1]`; this gives
`∂_i radialPot G (x) = -G_i(x)`.  Also records `Cyl.partialQ_eq_fderiv` to pass between the
library's partials and `fderiv`. -/
def RadialPotGrad : Prop :=
  ∀ G : Plane → Vec, ContDiff ℝ ∞ G →
    (∀ z, Cyl.partialQ (fun w => G w 1) z = Cyl.partialEta (fun w => G w 0) z) →
    ∀ z, Train.gradS (radialPot G) z = -(G z)

/-- **Leaf 6** (periodicity of the radial potential).  If `G` is smooth, curl free, `c`-periodic
and has zero horizontal mean at every height, then `radialPot G` is `c`-periodic.  Proof idea:
by Leaf 5, `∂_q (radialPot G) = -G₁`; the fundamental theorem of calculus along `r ↦ (q+r, η)`
gives `radialPot G (q+c,η) - radialPot G (q,η) = -∫₀^c G₁(q+r,η) dr = -∫₀^c G₁(r,η) dr = 0`
(`Function.Periodic.intervalIntegral_add_eq`).  May import the accepted Leaf 5. -/
def RadialPotPeriodic : Prop :=
  ∀ (c : ℝ) (G : Plane → Vec), 0 < c → ContDiff ℝ ∞ G → Cyl.IsPeriodic c G →
    (∀ z, Cyl.partialQ (fun w => G w 1) z = Cyl.partialEta (fun w => G w 0) z) →
    (∀ η : ℝ, ∫ q in (0 : ℝ)..c, G (q, η) 0 = 0) →
    Cyl.IsPeriodic c (radialPot G)

/-! ### The conditional theorem -/

/-- **`LerayVelocityToClassical` from the six leaves.**  The pressure is
`p s = radialPot (G s)` for the one-sided force `G` of Leaf 2. -/
theorem lerayVelocityToClassical_of (h1 : ClosedParamIntegralSmooth) (h2 : LerayForceSmooth)
    (h3 : OrthCurlFree) (h4 : OrthMeanZero) (h5 : RadialPotGrad) (h6 : RadialPotPeriodic) :
    LerayVelocityToClassical := by
  intro ν c T v hν hc1 hT hL
  have hc : 0 < c := zero_lt_one.trans_le hc1
  obtain ⟨G, hGs, hGp, hGeq⟩ := h2 ν c T v hν hc1 hT hL
  -- the slices of `G` are smooth
  have hslice : ∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (G s) := by
    intro s hs
    have hmaps : MapsTo (fun z : Plane => ((s, z) : ℝ × Plane)) univ
        (Icc (0 : ℝ) T ×ˢ univ) := fun z _ => ⟨hs, trivial⟩
    have h : ContDiffOn ℝ ∞ (fun z : Plane => G s z) univ :=
      hGs.comp (contDiff_prodMk_right s).contDiffOn hmaps
    exact contDiffOn_univ.mp h
  -- the orthogonality of the force to the solenoidal tests, for `0 < s < T`
  have horth : ∀ s ∈ Ioo (0 : ℝ) T, OrthToSolenoidalTests c (G s) := by
    intro s hs φ hφ hper hdiv hsupp
    have h := hL.leray s hs φ hφ hper hdiv hsupp
    rw [← h]
    refine setIntegral_congr_fun (Cyl.measurableSet_cell c) fun z _ => ?_
    simp only [hGeq s hs z]
  have hIcc : ∀ s ∈ Ioo (0 : ℝ) T, s ∈ Icc (0 : ℝ) T := fun s hs => ⟨hs.1.le, hs.2.le⟩
  have hcurl : ∀ s ∈ Ioo (0 : ℝ) T, ∀ z,
      Cyl.partialQ (fun w => G s w 1) z = Cyl.partialEta (fun w => G s w 0) z := fun s hs =>
    h3 c (G s) hc (hslice s (hIcc s hs)) (hGp s (hIcc s hs)) (horth s hs)
  have hmean : ∀ s ∈ Ioo (0 : ℝ) T, ∀ η : ℝ, ∫ q in (0 : ℝ)..c, G s (q, η) 0 = 0 := fun s hs =>
    h4 c (G s) hc (hslice s (hIcc s hs)) (hGp s (hIcc s hs)) (horth s hs)
  -- the pressure
  have hsmooth : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => radialPot (G x.1) x.2)
      (Icc (0 : ℝ) T ×ˢ univ) := by
    set Gt : ℝ × Plane → ℝ → ℝ := fun y t =>
      -(y.2.1 * G y.1 (t • y.2) 0 + y.2.2 * G y.1 (t • y.2) 1) with hGt
    have hm : MapsTo (fun y : (ℝ × Plane) × ℝ => ((y.1.1, y.2 • y.1.2) : ℝ × Plane))
        ((Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) T ×ˢ univ) :=
      fun y hy => ⟨hy.1.1, trivial⟩
    have hmc : ContDiff ℝ ∞ (fun y : (ℝ × Plane) × ℝ => ((y.1.1, y.2 • y.1.2) : ℝ × Plane)) :=
      (contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.smul (contDiff_snd.comp contDiff_fst))
    have hΦ : ContDiffOn ℝ ∞ (fun y : (ℝ × Plane) × ℝ => G y.1.1 (y.2 • y.1.2))
        ((Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) ×ˢ Icc (0 : ℝ) 1) :=
      hGs.comp hmc.contDiffOn hm
    have hΦ0 : ContDiffOn ℝ ∞ (fun y : (ℝ × Plane) × ℝ => G y.1.1 (y.2 • y.1.2) 0)
        ((Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) ×ˢ Icc (0 : ℝ) 1) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hΦ
    have hΦ1 : ContDiffOn ℝ ∞ (fun y : (ℝ × Plane) × ℝ => G y.1.1 (y.2 • y.1.2) 1)
        ((Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) ×ˢ Icc (0 : ℝ) 1) :=
      (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hΦ
    have hx1 : ContDiff ℝ ∞ (fun y : (ℝ × Plane) × ℝ => y.1.2.1) :=
      contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
    have hx2 : ContDiff ℝ ∞ (fun y : (ℝ × Plane) × ℝ => y.1.2.2) :=
      contDiff_snd.comp (contDiff_snd.comp contDiff_fst)
    have hGt' : ContDiffOn ℝ ∞ (fun y : (ℝ × Plane) × ℝ => Gt y.1 y.2)
        ((Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) ×ˢ Icc (0 : ℝ) 1) :=
      ((hx1.contDiffOn.mul hΦ0).add (hx2.contDiffOn.mul hΦ1)).neg
    have hint := h1 T hT Gt hGt'
    refine hint.congr fun x _ => ?_
    simp only [hGt, radialPot, intervalIntegral.integral_neg]
  have hper_int : ∀ s ∈ Ioo (0 : ℝ) T, Cyl.IsPeriodic c (radialPot (G s)) := fun s hs =>
    h6 c (G s) hc (hslice s (hIcc s hs)) (hGp s (hIcc s hs)) (hcurl s hs) (hmean s hs)
  have hcont : ∀ w : Plane, ContinuousOn (fun s => radialPot (G s) w) (Icc (0 : ℝ) T) := by
    intro w
    exact hsmooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, trivial⟩)
  refine ⟨fun s => radialPot (G s), hsmooth, ?_, ?_⟩
  · intro s hs z
    have heq : EqOn (fun s => radialPot (G s) (z.1 + c, z.2)) (fun s => radialPot (G s) z)
        (Icc (0 : ℝ) T) :=
      Set.EqOn.of_subset_closure (fun s hs => hper_int s hs z) (hcont _) (hcont _)
        Ioo_subset_Icc_self (closure_Ioo hT.ne).symm.subset
    exact heq hs
  · intro s hs z
    have hG := hGeq s hs z
    have hgrad := h5 (G s) (hslice s (hIcc s hs)) (hcurl s hs) z
    have h0 : Train.gradS (fun _ : Plane => (0 : ℝ)) z = 0 := by
      simp only [Train.gradS, Cyl.partialQ, Cyl.partialEta, deriv_const]
      show Train.toVecL ((0 : ℝ), (0 : ℝ)) = 0
      rw [Prod.mk_zero_zero]
      exact map_zero _
    have hsplit : Train.momentumResidual ν v (fun s => radialPot (G s)) s z =
        Train.momentumResidual ν v (fun _ _ => (0 : ℝ)) s z + Train.gradS (radialPot (G s)) z := by
      unfold Train.momentumResidual
      rw [h0]
      abel
    rw [hsplit, hgrad, ← hG]
    simp

end UnforcedLeray.Short.PartI
