import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Calc

/-!
# Physical inlet sources (`PartIII-b:C/rep/8/2/pres/3/2/6`)

The linear and quadratic inlet sources and the physical inlet source bound `InletSrcPhys`
(source `the November 2 reference manuscript`
2346-2347, 2370-2392).  Split off so the leaf lemma can import it without a cycle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The linear inlet source** `D₀E_εα + E_εα·∇U_raw + U_raw·∇E_εα` of the affine inlet
`E_εα = Σᵢ αᵢE_i` (source 2370-2383: the inlet part of the complete unprojected source column
`𝒞_εα`, in physical variables; `D₀ = physDmu ν 0`, `a·∇b = Db[a]`). -/
def inletLinSrc (p : UnforcedLeray.Cons.C03.Concrete.Params) (α : Fin 2 → ℝ) (τ : ℝ)
    (y : Space) : Space :=
  physDmu p.ν 0 (fun t y' => ∑ i : Fin 2, α i • p.inlet i t y') τ y +
    (fderiv ℝ (fun y' => ∑ i : Fin 2, α i • p.inlet i τ y') y (p.raw τ y) +
      fderiv ℝ (p.raw τ) y (∑ i : Fin 2, α i • p.inlet i τ y))

/-- **The quadratic inlet source** `E_εα·∇E_εα` (source 2388-2390). -/
def inletQuadSrc (p : UnforcedLeray.Cons.C03.Concrete.Params) (α : Fin 2 → ℝ) (τ : ℝ)
    (y : Space) : Space :=
  fderiv ℝ (fun y' => ∑ i : Fin 2, α i • p.inlet i τ y') y (∑ i : Fin 2, α i • p.inlet i τ y)

/-- **The physical inlet source bound** (source 2346-2347: "Its complete equation source is in
`Y_p`"; 2370-2392, `short-bg:affine`: `‖A₀E_εα + 𝔓B_{V₀}E_εα‖_{W^{1,Y_p}} ≤ 𝒫_ν R^{2/p}|α|`, "the
quadratic inlet source has the same bound with `|α|²`", "these assertions compare sources, never
the nonintegrable inlet states"; `p = 11/4`, `R^{2/p} = R^{8/11}`, the Jacobian `πR²s^{-5/2}` of
2681-2688).  At a fixed slow age `Σ` and a fixed growing eigenpair, in the regime and for small `ν`,
the linear and quadratic inlet sources of `E_εα` are in `L^{11/4}(ℝ³)` at every phase, with
`‖·‖_{L^{11/4}} ≤ Cν^{-k}R^{8/11}|α|` and `≤ Cν^{-k}R^{8/11}|α|²`.

This is the phase-uniform, unprojected, physical form of the source's bound (`r_ε` smooth at
zero, compact in upper age, with polynomial weighted bounds, 2377-2381; the young-age exponent
`-9/8 + p = 13/8 > -1`, 2386).  It is not a consequence of `IIb.InletSourceBound`
(`Short/PartII-b/Sub/G4.lean:92`), which bounds a phase-averaged `Y`-norm of a representative of
the source tested against solenoidal phase tests. -/
def InletSrcPhys : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (α : Fin 2 → ℝ) (τ : ℝ),
        eLpNorm (inletLinSrc p α τ) (11 / 4) volume ≤
            ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖) ∧
          eLpNorm (inletQuadSrc p α τ) (11 / 4) volume ≤
            ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖ ^ 2)


end UnforcedLeray.Short.PartIIIb.Concrete
