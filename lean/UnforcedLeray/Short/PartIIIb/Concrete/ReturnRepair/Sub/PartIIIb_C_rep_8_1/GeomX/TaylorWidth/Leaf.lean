import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Moment

/-!
# What `GeomX.TaylorWidth` needs (helper for `PartIII-b:C/rep/8/1/1/1/3`)

Source `the November 2 reference manuscript`
lines 4764-4791 (`E_ij(u)`, "the zero azimuthal row and column are retained as zero entries",
`Σ_M`, `V_{μ,M}`, `W^mt`), 5141-5142 (physical old tensors are swirl free), 5415-5427, 5439-5443.

## 1. The statement `TaylorWidthAt` is false for thin tensors with a hoop entry

`zMid` is built from the lift `cartLift`, which keeps the hoop entry `T(1,1)` (`NearInst.nsSym`:
"`rr, zz, φφ` kept"), while `zMt` is built from `Concrete.phaseMean`, which zeroes the whole
azimuthal row and column, `T(1,1)` included (`if i = 1 ∨ j = 1 then 0`).  For a `T : LStr` whose
thin component has only a `(1,1)` entry (old region, nonzero phase mean), `zMt T = 0` while the
leading term of `D_y zMid` is `ε³ D_xV_{μ,hoop}(x_obs)` with `V_{μ,hoop}` the Newton response of
the hoop stress `σ(ρ) e_φ ⊗ e_φ` (far field `-(1/2)(∫σ) ∂_i∂₃₃N`-type, not zero).  So `dWidth` is
of order `ε³ s^{5/2} N`, and since `ε_n = (e^{-γ/ν_n} ν_n^{Re κ - 5 - 2σ₀}/(2|𝒞|))^{1/3}`
(`retEps`) is exponentially small in `ν_n⁻¹`, no `C ν⁻ᵏ ε⁴ s^{5/2} N` bound holds.  The source's
comparison is for physical old tensors `M_U w` (swirl free: zero azimuthal row and column,
5141-5142), for which the two conventions agree.  The `rz/zr` asymmetry is harmless (the Newton
kernel `D³N` is symmetric).  A correct statement either restricts `T` to thin components with
`thinRep T p 1 1 = 0` a.e., or makes `Concrete.phaseMean` keep the `(1,1)` entry (as `nsSym`).

## 2. The decay form of `IIIa.SepMeanPart`

As for `PhasePrimitive` (`PhasePrimitive/Leaf.lean`), the factor `s^{5/2} = |x_obs'|^{-5}` cannot
come from `IIIa.SepMeanPart`, whose constant does not decay in the receiver radius.  The needed
mean-part leaf is `SepMeanFar` below.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

/-- **Far-field mean comparison** (source 5415-5427, 5439-5443; SP 3735-3766 with the degree `-5`
of `D∇K` kept): for a measurable phase-free thin source `G(x',Y)` supported in `|x'| ≤ ρ_o`, at
every receiver `|x_obs'| ≥ ρ_i > ρ_o`,
`|∇_yW_μ(G)(ε⁻¹x_obs) - ε³∇_xV_{μ,0}(G)(x_obs)| ≤ C(1 + ν⁻¹ + c + ρ_i⁻¹ + ρ_i/(ρ_i - ρ_o))^k
ε⁴ |x_obs'|^{-5} N₁(G)` (transverse Taylor remainder along segments with the strict radial gap,
heat-to-Newton `|D(K_t - K_0)| ≤ Ct|x|^{-6}` at `t = νε²(1 - λ²)`). -/
def SepMeanFar : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) →
          ‖fderiv ℝ (fun y => IIIa.sepW ν μ (IIIa.thinSource ε (IIIa.meanLift G)) y 0) (ε⁻¹ • xo) -
              (ε ^ 3 : ℝ) • fderiv ℝ (IIIa.sepVmu0 μ G) xo‖ₑ ≤
            ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ k * ε ^ 4 *
              Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c (IIIa.meanLift G)

end UnforcedLeray.Short.PartIIIb.Concrete
