import UnforcedLeray.Short.PartIIb.Sub.T22_2

/-!


Source: `the November 2 reference manuscript` lines 2074-2105 (the regular backward
problem used by the duality argument).

`BwdSol` collects what a classical bounded solution of `φ_r + νΔφ + v·∇φ = 0`, `φ(t) = ψ` on the
periodic cylinder is: jointly `C^∞` on `[s, t] × ℝ²`, `c`-periodic in `q`, bounded, with the
equation on `(s, t)`.  Then:
* `BwdExists`: existence of such a `φ` (parabolic theory, time reversal `r ↦ t - r`);
* `BwdDecay`: every such `φ` decays faster than any power of `1 + η²` with its first and Laplacian
  derivatives, uniformly in `r ∈ [s, t]` (weighted maximum principle / energy estimate, bounded
  drift, compactly supported terminal datum).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- A bounded classical `C^∞` periodic solution of the backward transport-diffusion problem with
terminal datum `ψ` at age `t` and drift `v`. -/
structure BwdSol (ν c s t : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec)
    (ψ : B0579.Plane → ℝ) (φ : ℝ → B0579.Plane → ℝ) : Prop where
  terminal : φ t = ψ
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => φ z.1 z.2)
    (Icc s t ×ˢ univ)
  periodic : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, φ r (x.1 + c, x.2) = φ r x
  bounded : ∃ M : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |φ r x| ≤ M
  pde : ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
    HasDerivAt (fun r' => φ r' x)
      (-(ν * lapP (φ r) x + (v r x 0 * B0579.pd 0 (φ r) x + v r x 1 * B0579.pd 1 (φ r) x))) r

/-- **Leaf `T22/2/3/1`**: existence of a bounded classical `C^∞` periodic backward solution
(SP 2100-2105; time reversal gives a forward drift-diffusion problem with smooth bounded drift
having bounded derivatives, `TrainClose`). -/
def BwdExists : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / ν →
    ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ → ∃ φ : ℝ → B0579.Plane → ℝ, BwdSol ν c s t tr.v ψ φ

/-- **Leaf `T22/2/3/2`**: a bounded classical backward solution with a test-function datum decays
in `η` faster than any power of `1 + η²`, uniformly in the age (SP 2100-2105). -/
def BwdDecay : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / ν →
    ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ → ∀ φ : ℝ → B0579.Plane → ℝ,
      BwdSol ν c s t tr.v ψ φ → ∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
        (|φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| + |lapP (φ r) x|) *
          (1 + x.2 ^ 2) ^ N ≤ C

theorem cylBackwardSolve_of (h1 : BwdExists) (h2 : BwdDecay) : CylBackwardSolve := by
  intro Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ
  obtain ⟨φ, hφ⟩ := h1 Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ
  refine ⟨φ, hφ.terminal, ⟨hφ.smooth, hφ.periodic, h2 Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ φ hφ⟩, hφ.pde⟩

end UnforcedLeray.Short.IIb
