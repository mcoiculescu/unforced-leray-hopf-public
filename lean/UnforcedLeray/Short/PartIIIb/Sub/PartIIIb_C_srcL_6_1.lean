import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6

/-!
# `PartIII-b:C/srcL/6/1`: `XSZSmooth` from the smoothness of the Newton field off the old disc

Source of record: `the November 2 reference manuscript` lines 4776-4791 and
4917-4937.  `youngW c ν ε μ = ε² • newtonV c ν μ (ε • ·)`, and `εy` lies in the region
`{5ν/6 < x₀² + x₁²}` exactly when `y ∈ outReg ν ε`; so `XSZSmooth` reduces to the smoothness of the
zero-width Newton field `newtonV` on that region (`NewtonVSmooth`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Leaf**: the zero-width Newton field `V_{μ,M}` (source 4776-4782) is `C^∞` on the open set
`{x | 5ν/6 < x₀² + x₁²}` outside the old source disc `|x'|² < 5ν/6` (`χ_o(νu) = 0` for
`νu ≤ 6/5`, so `Σ_M` vanishes for `|x'|² ≥ 5ν/6`), for `OldThinFinite` old tensors.  Proof: `newtonN`
is `C^∞` off `0` (so `newtonD3` is, with every derivative locally bounded); `Σ_M` is integrable on
`ℝ²` (`OldThinFinite`, polar coordinates `u = ρ⁻²`); for `x` in the region, `t ∈ (0,1]`, `|x'|² <
5ν/6` the point `x - t(x',0)` stays at distance `≥ cylR x - |x'| > 0` from `0`, locally uniformly,
so one differentiates under the integral sign to every order. -/
def NewtonVSmooth : Prop :=
  ∀ (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonV c ν μ χo M)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2}

theorem xsZSmooth_of (h1 : NewtonVSmooth) : XSZSmooth := by
  intro c ν ε μ χo M hc hν hε hμ hχ hM
  have hsq : ∀ y : Vec3, cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := fun y =>
    Real.sq_sqrt (by positivity)
  have hmaps : MapsTo (fun y : Vec3 => ε • y) (outReg ν ε)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
    intro y hy
    have hy' : 5 * ν / (6 * ε ^ 2) < y 0 ^ 2 + y 1 ^ 2 := by
      have := hy; simp only [outReg, mem_setOf_eq] at this; rwa [hsq] at this
    have h2 : 0 < 6 * ε ^ 2 := by positivity
    have := (div_lt_iff₀ h2).1 hy'
    show 5 * ν / 6 < (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith
  have key : ∀ μ' : ℝ, 0 < μ' →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (youngW c ν ε μ' χo M) (outReg ν ε) := by
    intro μ' hμ'
    have h := (h1 c ν μ' χo M hc hν hμ' hχ hM).comp
      ((contDiff_const_smul ε).contDiffOn (s := outReg ν ε)) hmaps
    exact (h.const_smul (ε ^ 2)).congr fun y _ => rfl
  exact (key μ hμ).sub (key (μ + 1) (by linarith))

end UnforcedLeray.Short.PartIIIb.Concrete
