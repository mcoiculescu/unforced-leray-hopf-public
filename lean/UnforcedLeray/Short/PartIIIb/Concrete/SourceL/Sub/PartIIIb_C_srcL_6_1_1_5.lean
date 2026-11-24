import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

/-!
# Vanishing of the Cartesian source beyond `ρ² = 5ν/6` (task `PartIII-b:C/srcL/6/1/1/5`)

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
For `ρ² ≥ 5ν/6` one has `ν u ≤ 6/5` with `u = ρ⁻²`, so the outward cutoff `χ_o(νu)` vanishes
(`IsOutwardCutoff.zero`), hence the phase mean `E(u)` vanishes and so does `Σ_M(x')`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sigmaM_eq_zero_of_ge (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (x' : ℝ × ℝ) (h : 5 * ν / 6 ≤ x'.1 ^ 2 + x'.2 ^ 2) :
    sigmaM c ν χo M x' = 0 := by
  have hs : 0 < x'.1 ^ 2 + x'.2 ^ 2 := by linarith
  have hle : ν * (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ≤ 6 / 5 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hs]
    linarith
  have hz : phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ = 0 := by
    ext a b
    simp [phaseMean, hχ.zero _ hle]
  ext a b
  simp [sigmaM, hz]

end UnforcedLeray.Short.PartIIIb.Concrete
