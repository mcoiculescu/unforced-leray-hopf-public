import UnforcedLeray.Short.PartIIIa.Sub.T18_2

/-!
# Part III-a, task `PartIII-a:T18/2/4`: classical solve for nice forces (conditional)

Target (`Sub/T18_2.lean`): `NiceForceSolution`. For `c, ν > 0`, `μ ∈ ℂ` and a nice force `F`
(symmetric, smooth in `(s, q, η)`, `c`-periodic in `q`, zero for `s < a` (`a > 0`), `s > B`,
`|η| > R`) there is `(b, G)` in the causal zero-entrance energy class `IsCausalEnergySolution` for
the free equation `b_s + (μ/s) b - νΔb = 𝒫₀ div F`.
Source of record: `the November 2 reference manuscript`, lines 3427-3440 ("start
from zero at `s = δ`, let `δ ↓ 0`"; the free instance of the energy argument).



The periodic-cell heat semigroup on `L²(cell; ℝ²)`, `H¹` smoothing, a Duhamel operator with the
`(t/s)^μ` propagator and the joint measurability of the Duhamel candidate are not in the library.
Working with the *projected* Duhamel candidate `b(s) = 𝒫₀ ∫_a^s (t/s)^μ e^{ν(s-t)Δ} div F(t) dt`
slice by slice would need all of them. The proof used here avoids the semigroup in the assembly:

1. (*Unprojected classical solve*, `HeatCellClassical`) for a nice force the unprojected equation
   `u_s + (μ/s) u - νΔu = div F` (`div F = (Σ_j ∂_j F_ij)_i`) has a classical, globally smooth,
   `c`-periodic solution with `u = 0` for `s ≤ a` and Gaussian decay in `η` for `s ≤ s₂`
   (Duhamel with the heat kernel of the plane against the periodic, `η`-compact source; the factor
   `(t/s)^μ` is a bounded smooth scalar for `t ∈ [a, s]`).
2. (*Classical to weak*, `ClassicalToWeakFlat`) integration by parts in `s` and in `x` (periodicity
   in `q`, compact `η`-support of the test) turns the classical equation into the tested identity
   `∫∫ flatIntegrand ν μ 0 F u Φ = 0` for every `IsFlatTest Φ`.
3. (*Leray projection of the slices*, `LerayProjectSlices`) `b(s) = 𝒫₀ u(s)` with
   `G(s) = (𝒫₀ ∂_j u(s))_{ij} = ∇b(s)` (`𝒫₀` commutes with translations, hence with weak
   derivatives), chosen jointly measurable in `(s, x)`; `b(s)` is divergence free,
   `b(s) - u(s)` is orthogonal to every smooth periodic `η`-compact divergence-free field, and
   `b(s) = 0` when `u(s) = 0`.
4. (*Swap*, `FlatOrthSwap`) `Φ_s`, `ΔΦ`, `Φ` are divergence-free test fields for each `s`, so
   `flatIntegrand ν μ 0 F b Φ - flatIntegrand ν μ 0 F u Φ = Σ_i (b_i - u_i) Ψ_i` has slice
   integral `0`; Fubini gives the same for the space-time integral. Hence the weak identity for `u`
   transfers to `b`.

Proved here: `niceForceSolution_of` (the wiring: `zeroEntrance` with `δ = a`, the other clauses of
`IsCausalEnergySolution` from `IsLerayProjection` and the two weak-form leaves), from the four
Props `HeatCellClassical`, `LerayProjectSlices`, `ClassicalToWeakFlat`, `FlatOrthSwap`.
The unconditional leaves are queued as tasks `PartIII-a:T18/2/4/1 ... T18/2/4/4`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Notation for the classical equation -/

/-- The classical partial derivative `∂_j`, `j = 0` for `q`, `j = 1` for `η`, of a `ℂ`-valued
function on the plane (`B0579.pd` is the real-valued version). -/
def pdC (j : Fin 2) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  fderiv ℝ f x (B0579.dir j)

/-- The planar Laplacian of a `ℂ`-valued function. -/
def lapC (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  pdC 0 (pdC 0 f) x + pdC 1 (pdC 1 f) x

/-- `u` solves `u_s + (μ/s) u - νΔu = div F` classically for `s > 0`, where
`(div F)_i = Σ_j ∂_j F_ij` (the unprojected equation; its weak form against divergence-free tests
is the free flat equation with `vel = 0`). -/
def IsClassicalFlatSol (ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : Prop :=
  ∀ s : ℝ, 0 < s → ∀ (x : ℝ × ℝ) (i : Fin 2),
    deriv (fun s' => u (s', x) i) s + (μ / (s : ℂ)) * u (s, x) i -
        (ν : ℂ) * lapC (fun y => u (s, y) i) x =
      ∑ j : Fin 2, pdC j (fun y => F (s, y) i j) x

/-- Local-in-age Gaussian decay in `η` of `u` and its spatial gradient: for every `s₂` there are
`C` and `κ > 0` with `‖u(s,x)_i‖ + ‖∇_x u_i(s,x)‖ ≤ C e^{-κ η²}` for all `s ≤ s₂`. -/
def GaussianDecayLoc (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : Prop :=
  ∀ s₂ : ℝ, ∃ C κ : ℝ, 0 < κ ∧ ∀ (s : ℝ) (x : ℝ × ℝ) (i : Fin 2), s ≤ s₂ →
    ‖u (s, x) i‖ + ‖fderiv ℝ (fun y => u (s, y) i) x‖ ≤ C * Real.exp (-κ * x.2 ^ 2)

/-- A smooth, `c`-periodic in `q`, `η`-compactly supported, pointwise divergence-free real vector
field on the plane (a divergence-free test field on the cylinder). -/
def IsDivFreeTestField (c : ℝ) (Ψ : ℝ × ℝ → Fin 2 → ℝ) : Prop :=
  (∀ i, B0579.IsCylTest c (fun x => Ψ x i)) ∧
    ∀ x, B0579.pd 0 (fun y => Ψ y 0) x + B0579.pd 1 (fun y => Ψ y 1) x = 0

/-- `(b, G)` is the slice-wise Leray projection of `u` with weak gradient `G`, jointly measurable,
in the local energy class: `b(s)` is divergence free with weak gradient `G(s)`, `b(s) - u(s)` is
orthogonal (in `L²(cell)`, unweighted pairing) to every divergence-free test field, and
`b(s) = 0` when `u(s) = 0`. These are exactly the clauses of `IsCausalEnergySolution` other than
`zeroEntrance`, `integrable`, `weak`, plus the orthogonality and the vanishing clause. -/
structure IsLerayProjection (c : ℝ) (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop where
  measurable : ∀ i, Measurable fun p => b p i
  gradMeasurable : ∀ i j, Measurable fun p => G p i j
  energyLoc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤
  divFree : ∀ s, 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0
  weakGrad : ∀ s, 0 < s → ∀ i j,
    HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)
  orth : ∀ s, 0 < s → ∀ Ψ, IsDivFreeTestField c Ψ →
    ∫ x in B0579.cell c, ∑ i : Fin 2, (b (s, x) i - u (s, x) i) * (Ψ x i : ℂ) = 0
  zero : ∀ s, (∀ x i, u (s, x) i = 0) → ∀ x i, b (s, x) i = 0

/-! ## The four leaf statements -/

/-- **Unprojected classical solve** (`PartIII-a:T18/2/4/1`; SP 3427-3440). For `c, ν > 0`,
`μ ∈ ℂ` and a nice force `F` there is a globally smooth (jointly in `(s, q, η)`), `c`-periodic in
`q` solution `u` of `u_s + (μ/s) u - νΔu = div F` for `s > 0`, vanishing for `s ≤ a` (some
`a > 0`, `F = 0` for `s < a`), with Gaussian decay in `η` locally uniformly in `s`.
Proof idea: `h(t) = t^μ div F(t)` is smooth, `c`-periodic, supported in `t ∈ [a, B]`, `|η| ≤ R`;
`w(s) = ∫_a^s g_{ν(s-t)} * h(t) dt` (heat kernel of the plane against the bounded periodic source)
solves `w_s - νΔw = h`, `w = 0` for `s ≤ a`, is smooth (differentiate under the integral, `h` has
all derivatives vanishing at `t = a`), and `u = s^{-μ} w`; the kernel bound
`g_τ(y) ≤ C τ^{-1} e^{-|y|²/(8τ)}` gives the decay `e^{-κη²}`, `κ = 1/(16ν s₂)`, after splitting
`|η| ≤ 2R` (bounded) and `|η| > 2R`. -/
def HeatCellClassical : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ), 0 < c → 0 < ν →
    ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, NiceForce c F →
      ∃ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ,
        (∀ i, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => u p i) ∧
        (∀ s x i, u (s, (x.1 + c, x.2)) i = u (s, x) i) ∧
        (∃ a : ℝ, 0 < a ∧ ∀ s x i, s ≤ a → u (s, x) i = 0) ∧
        IsClassicalFlatSol ν μ F u ∧
        GaussianDecayLoc u

/-- **Leray projection of a family of slices** (`PartIII-a:T18/2/4/2`; SP 3427-3440, the
projection `𝒫₀` of the cylinder, `Lib/CylinderB/Leray.lean`). For `c > 0` and a globally smooth,
`c`-periodic `u` with locally uniform Gaussian decay in `η`, there is a jointly measurable
`(b, G)` with `b(s) = 𝒫₀ u(s)` (componentwise on real and imaginary parts) a.e. in `x` for each
`s`, `G(s)_{ij} = (𝒫₀ ∂_j u(s))_i = ∂_j b_i(s)` weakly: all clauses of `IsLerayProjection`.
Proof idea: `u(s), ∂_j u(s) ∈ L²(cell)` with norms bounded locally uniformly and continuous in `s`
(Gaussian decay, dominated convergence); `𝒫₀` commutes with translations (the translate of a
divergence-free field is divergence free), hence with difference quotients, hence with weak
`∂_j` (`P0_comm_weakPartial`, listed as not built in `Lib/CylinderB/Leray.lean`), so
`∇𝒫₀ u = 𝒫₀ ∇u` and `‖∇𝒫₀ u(s)‖ ≤ ‖∇u(s)‖`; orthogonality: a divergence-free test field lies in
`divFree c`, `𝒫₀` is self-adjoint and fixes it (`inner_P0_comm`, `P0_eq_self`); the continuous
curves `s ↦ 𝒫₀u(s)`, `s ↦ 𝒫₀∂_ju(s)` in `L²` have jointly measurable representatives
(`Infra/JointMeasurableRep`, `Lib/BochnerTime/JointRep.lean`), redefined to be `0` on the closed
set of ages with `u(s) ≡ 0`; `energyLoc` by Tonelli from the slice bounds. -/
def LerayProjectSlices : Prop :=
  ∀ c : ℝ, 0 < c → ∀ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ,
    (∀ i, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => u p i) →
    (∀ s x i, u (s, (x.1 + c, x.2)) i = u (s, x) i) →
    GaussianDecayLoc u →
    ∃ b G, IsLerayProjection c u b G

/-- **Classical to weak** (`PartIII-a:T18/2/4/3`; SP 3427-3440). A globally smooth, `c`-periodic
classical solution `u` of the unprojected equation with a nice force `F` satisfies the tested
identity against every `IsFlatTest` (not only against divergence-free tests, but `IsFlatTest` is
all that is needed), and the tested integrand is integrable.
Proof idea: the integrand is continuous and vanishes unless `s ∈ [s₁, s₂]`, `|η| ≤ R` (the
support of `Φ`), so it is integrable on the compact set `[s₁, s₂] × [-c/2, c/2] × [-R, R]`;
integrate by parts once in `s` (`Φ(s₁-) = Φ(s₂+) = 0`) and twice in `q` and `η`: in `q` the
boundary terms cancel by `c`-periodicity of `u`, `F`, `Φ`, in `η` by compact support of `Φ`;
then the integrand equals `Φ · (u_s + (μ/s)u - νΔu - div F) = 0` by the classical equation. -/
def ClassicalToWeakFlat : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ), 0 < c →
    ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, NiceForce c F →
      ∀ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ,
        (∀ i, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => u p i) →
        (∀ s x i, u (s, (x.1 + c, x.2)) i = u (s, x) i) →
        IsClassicalFlatSol ν μ F u →
        ∀ Φ, IsFlatTest c Φ →
          IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F u Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
          ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ (fun _ _ _ => 0) F u Φ p = 0

/-- **Swapping `u` for its projection in the tested identity** (`PartIII-a:T18/2/4/4`; SP
3427-3440, `⟨𝒫₀ f, Φ⟩ = ⟨f, Φ⟩` for divergence-free `Φ`). If `(b, G)` is a Leray projection of a
continuous `u` (`IsLerayProjection`) and the tested identity holds for `u` with integrable
integrand, then the same holds for `b` (the force `F` is arbitrary and cancels).
Proof idea: for `Φ` an `IsFlatTest`, the fields `Ψ¹(s) = -∂_sΦ(s) - νΔΦ(s)` and `Ψ²(s) = Φ(s)`
are `IsDivFreeTestField` for every `s` (smooth, periodic, `η`-compact; the divergence commutes with
`∂_s` and `Δ` for smooth `Φ`, symmetry of second derivatives); then
`flatIntegrand ν μ 0 F b Φ - flatIntegrand ν μ 0 F u Φ = Σ_i (b_i-u_i)(Ψ¹_i + (μ/s)Ψ²_i)`, which is
integrable on `Ioi 0 ×ˢ cell` (supported in a finite-measure set `[s₁,s₂] × cell ∩ {|η| ≤ R}`,
`b ∈ L²` there by `energyLoc`, `u` continuous, `|μ/s| ≤ |μ|/s₁`) and whose slice integrals vanish
by `orth`; Fubini (`integral_prod`) gives total integral `0`. -/
def FlatOrthSwap : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ), 0 < c →
    ∀ (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (u b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
      (∀ i, Continuous fun p : ℝ × (ℝ × ℝ) => u p i) → IsLerayProjection c u b G →
        ∀ Φ, IsFlatTest c Φ →
          IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F u Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) →
          ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ (fun _ _ _ => 0) F u Φ p = 0 →
          IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
          ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p = 0

/-! ## The assembly -/

/-- **Classical solve for nice forces from the four facts** (assembly; SP 3427-3440). Solve the
unprojected equation classically (`hCl`), project the slices (`hLer`), and transfer the weak
identity from `u` to its projection `b` (`hWeak`, `hSwap`); `zeroEntrance` holds with `δ = a`
because `u(s) = 0` for `s ≤ a` forces `b(s) = 0`. -/
theorem niceForceSolution_of (hCl : HeatCellClassical) (hLer : LerayProjectSlices)
    (hWeak : ClassicalToWeakFlat) (hSwap : FlatOrthSwap) : NiceForceSolution := by
  intro c ν μ hc hν F hF
  obtain ⟨u, hus, hup, ⟨a, ha, hu0⟩, hcl, hdec⟩ := hCl c ν μ hc hν F hF
  obtain ⟨b, G, hL⟩ := hLer c hc u hus hup hdec
  have hucont : ∀ i, Continuous fun p : ℝ × (ℝ × ℝ) => u p i := fun i => (hus i).continuous
  refine ⟨b, G, ?_⟩
  refine
    { measurable := hL.measurable
      gradMeasurable := hL.gradMeasurable
      energyLoc := hL.energyLoc
      zeroEntrance := ?_
      divFree := hL.divFree
      weakGrad := hL.weakGrad
      integrable := ?_
      weak := ?_ }
  · refine ⟨a, ha, ?_⟩
    have hmeas : MeasurableSet (Ioo (0 : ℝ) a ×ˢ (univ : Set (ℝ × ℝ))) :=
      measurableSet_Ioo.prod MeasurableSet.univ
    have hz : ∀ p ∈ Ioo (0 : ℝ) a ×ˢ (univ : Set (ℝ × ℝ)),
        ENNReal.ofReal (vnorm2 (b p) ^ 2) = 0 := by
      intro p hp
      have hb0 : ∀ i, b p i = 0 := by
        intro i
        have h := hL.zero p.1 (fun x i => hu0 p.1 x i (le_of_lt hp.1.2)) p.2 i
        simpa using h
      have : vnorm2 (b p) = 0 := by
        unfold vnorm2
        simp [hb0]
      rw [this]
      simp
    rw [setLIntegral_congr_fun hmeas (g := fun _ => 0) hz]
    simp
  · intro Φ hΦ
    have hw := hWeak c ν μ hc F hF u hus hup hcl Φ hΦ
    exact (hSwap c ν μ hc F u b G hucont hL Φ hΦ hw.1 hw.2).1
  · intro Φ hΦ
    have hw := hWeak c ν μ hc F hF u hus hup hcl Φ hΦ
    exact (hSwap c ν μ hc F u b G hucont hL Φ hΦ hw.1 hw.2).2

end UnforcedLeray.Short.IIIa
