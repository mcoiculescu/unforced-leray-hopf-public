import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail.Leaves

/-!
# `PartII-b:T20/2`: the coefficient leaf of the local interaction remainder

Source of record: `the November 2 reference manuscript` (SP), lines 2007-2023
("Exact chart substitution writes the second as `ε` times polynomially bounded coefficients"),
2419-2423 (the raw coefficients `b_raw = v + εHe_z`), 2049-2056 (train estimates).

`RawBoxJet`: on bounded ages `0 < s ≤ Γ` and heights `|η| ≤ Γ` (in particular on every observation
box `obsBox σ H₁ L₁` with `H₁, L₁ ≤ Γ`), the first-order chart jets (`chartJet`: the profile,
`∂_q`, `∂_η` and `K = 2s∂_s + η∂_η`) of the train velocity `v` (`trainProf`) and of the raised
stream `He_z` (`raisedMerid`, `H = (1 - K)ψ`) are bounded by `CΓ^k`, uniformly in the parameters
(`ν⁻¹ ≤ Γ`).  These are the "polynomially bounded coefficients" of SP 2015-2018.

The identification leaf of the remainder is `KOutChartAe` (`TransverseTail/Leaves.lean`, shared
with `PartII-b:G3/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- **Leaf `RawBoxJet`** (SP 2015-2018, 2419-2423): polynomial bounds for the first-order chart jets
of the train velocity and of the raised stream on bounded ages and heights. -/
def RawBoxJet : Prop :=
  ∃ (k : ℕ) (C ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
    ∀ Γ : ℝ, 1 ≤ Γ → p.ν⁻¹ ≤ Γ →
    ∀ x : Coord, 0 < x.1 → x.1 ≤ Γ → |x.2.2| ≤ Γ →
      chartJet (trainProf p) x + chartJet (raisedMerid p) x ≤ C * Γ ^ k

end UnforcedLeray.Short.IIb

end
