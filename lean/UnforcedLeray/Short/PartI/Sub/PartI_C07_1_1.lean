import UnforcedLeray.Short.PartI.Sub.PartI_C07_1
import UnforcedLeray.Cons.L2.CanonicalBranch.Evolution

/-!
# `PartI:C07/1/1`: decomposition of `CanonicalFullDuhamel`

Source `the November 2 reference manuscript`
lines 1094-1125 ("splitting both integrals at any finite `s₀` verifies the coupled mild
initial-value equations, whose uniqueness follows from the bounded coupling maps and Gronwall").
The route: (1) the coupled mild system for `(A, r)` is equivalent to the Duhamel (mild) equation of
the full generator `-V' = (L₀ + θ⁻¹D)V` on `[b,∞)` (`CoupledImpliesFullMild`, Dyson regrouping
along `Q = 1 - q⊗ℓ`); (2) a continuous solution of that Duhamel equation equals `S θ θ' (V θ')`
(`FullMildUnique`, Gronwall with the bounded perturbation `L₀`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

/-- `V` satisfies the Duhamel (mild) equation of `-V' = (L₀ + θ⁻¹D)V` on `[b,∞)` in the form of
`Cons.G3b.S_mild` (source 1094-1125; the evolution `E(θ,θ') = e^{log(θ'/θ)D}` of the free part):
for `b ≤ θ ≤ θ'`,
`V θ = e^{(log θ' - log θ)D}(V θ') + ∫_{-θ'}^{-θ} freeU(-θ,u) L₀ V(-u) du`. -/
def FullMildEq (b : ℝ) (V : ℝ → B0010.XG) : Prop :=
  ∀ θ θ' : ℝ, b ≤ θ → θ ≤ θ' →
    V θ = B0123.expD (Real.log θ' - Real.log θ) (V θ') +
      ∫ u in (-θ')..(-θ), Cons.G3b.freeU (-θ) u (B0012.L0 (V (-u)))

/-- **Gronwall uniqueness** (source 1124: "uniqueness follows from the bounded coupling maps and
Gronwall"): a continuous solution of the full Duhamel equation on `[b,∞)`, `b > 0`, is
transported by the evolution `Cons.G3b.S`. -/
def FullMildUnique : Prop :=
  ∀ (b : ℝ) (V : ℝ → B0010.XG), 0 < b → ContinuousOn V (Ici b) → FullMildEq b V →
    ∀ θ θ' : ℝ, b ≤ θ → θ ≤ θ' → V θ = Cons.G3b.S θ θ' (V θ')

/-- **Coupled mild system ⇒ full Duhamel equation** (source 1094-1125): a canonical mild solution
(`IsCanonicalMild`, i.e. `(A, r)` solves the coupled mild equations with the complement
evolution `canonicalS U`) satisfies the Duhamel equation of the full generator.  Sketch: the
complement generator `Q{L - λ + θ⁻¹(D - κ)}Q` plus the finite-rank couplings
`θ⁻¹ A QDq`, `θ⁻¹ ℓ(D r)` differs from the full generator `L₀ + θ⁻¹ D` (conjugated by
`e^{-λθ}θ^{-κ}`) by an explicit finite-rank source; regroup the Dyson series
(`Evolution.dyson_sum_regroup`, `Cons.G3b.canonicalActualCoupling_mild_of_complement`). -/
def CoupledImpliesFullMild : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (b : ℝ), 0 < b →
    ∀ V : ℝ → B0010.XG, IsCanonicalMild lam q l qd hq hqd b V → FullMildEq b V

theorem canonicalFullDuhamel_of (hU : FullMildUnique) (hC : CoupledImpliesFullMild) :
    CanonicalFullDuhamel := by
  intro lam q l hI qd hl hq hqd b hb V hV θ θ' h1 h2
  exact hU b V hb hV.1 (hC lam q l hI qd hl hq hqd b hb V hV) θ θ' h1 h2

end UnforcedLeray.Short.PartI
