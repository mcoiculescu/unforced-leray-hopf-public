import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `PartIII-b:C/near/masked/11`: `RealStressBound` (source 1680-1689, the `b`-part)

From the existence part of `NearStressMapExists` (with `M = 1/4 ≥ μ` and `γs = 1/4 ≤ μ + 1/4` for
`0 < μ < 1/4`) we get a stress map `S₀` of `T_ε`, which equals the given `S'` by
`StressMapUnique`; `StressTransportNorm` then bounds the real form `S` by `‖S'‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- **`near:free-energy` in real form** (source 1680-1689, the `b`-part). -/
theorem realStressBound_of (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hU : StressMapUnique) (hT : StressTransportNorm) : RealStressBound := by
  obtain ⟨C, hC0, hbd⟩ := hN
  refine ⟨C * (1 + 1 / 4 + (1 / 4 : ℝ)⁻¹), mul_nonneg hC0 (by norm_num), ?_⟩
  intro ν ε c P _ hν hε hc hP hε1 hP1 μ hμ0 hμ1 mZ ρb hmZ hρ hρ1 S' S hS' hST
  have hM : ‖(μ : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hμ0.le]
    exact hμ1.le
  have hγ : (1 / 4 : ℝ) ≤ (μ : ℂ).re + 1 / 4 := by
    rw [Complex.ofReal_re]
    linarith
  obtain ⟨⟨S₀, hS₀, hS₀b⟩, _⟩ :=
    hbd ν c (1 / 4) (1 / 4) hν hc (by norm_num) ε hε hε1 P hP hP1 (μ : ℂ) hM hγ
  have hEq : S' = S₀ := hU c ε _ S' S₀ hc hS' hS₀
  have hS'b : ‖S'‖ ≤ C * (1 + 1 / 4 + (1 / 4 : ℝ)⁻¹) * ν ^ (-(1 / 2 : ℝ)) := by
    apply ContinuousLinearMap.opNorm_le_bound S' (mul_nonneg (mul_nonneg hC0 (by norm_num))
      (Real.rpow_nonneg hν.le _))
    intro F
    rw [hEq]
    exact (hS₀b F).trans (le_of_eq (by ring))
  calc ‖S‖ ≤ ‖S'‖ := hT c mZ ρb hc hmZ hρ hρ1 S' S hST
    _ ≤ C * (1 + 1 / 4 + (1 / 4 : ℝ)⁻¹) * ν ^ (-(1 / 2 : ℝ)) := hS'b

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
