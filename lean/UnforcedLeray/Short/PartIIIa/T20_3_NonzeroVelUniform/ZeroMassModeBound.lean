import UnforcedLeray.Short.PartIIIa.Sub.T20_3
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.Bridge
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.FourierModeFormula
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.ZeroMassPhaseBound

/-!
# Part III-a, task `PartIII-a:T20/3/6`: the low-frequency Fourier bound of one horizontal mode

Proof of `CTE.T20_3.ZeroMassModeBound` (`Sub/T20_3.lean`). Source of record:
`the November 2 reference manuscript`, lines 3236-3238.

Steps. (1) The `k`-th mode of `U` agrees a.e. with the integral `g` of
`B0581.coeffIntegrand` (`B0581.modes_apply_ae_integral`). (2) `FourierModeFormula` gives
`g ∈ L¹(ℝ)` and the pointwise formula for `𝓕 g`. (3) `g ∈ L²(ℝ)`, so the mode equals
`hg2.toLp g` in `L²(ℝ)`. (4) The `L²` Fourier transform agrees a.e. with `𝓕 g` (`fourier_toLp_ae_eq`).
(5) `ZeroMassPhaseBound` bounds the integral in the formula for `𝓕 g`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

/-- **Low-frequency Fourier bound of one horizontal mode** (task `PartIII-a:T20/3/6`; SP 3236-3238).
Proves `ZeroMassModeBound` (`Sub/T20_3.lean`). -/
theorem zeroMassModeBound : ZeroMassModeBound := by
  intro c hcF U hU hUw hmass k
  have hc : 0 < c := hcF.out
  -- (1) the mode is a.e. the horizontal integral
  have hmode := B0581.modes_apply_ae_integral c k U
  -- (2) integrability of the integral and the formula for its Fourier transform
  obtain ⟨hg1, hgF⟩ := fourierModeFormula c hc k (U : B0579.Plane → ℂ) hU
  set g : ℝ → ℂ := fun η => ∫ q in B0581.qInt c,
    B0581.coeffIntegrand c k (U : B0579.Plane → ℂ) (q, η) with hg
  -- (3) the mode is in L²(ℝ), and equals `hg2.toLp g` there
  have hg2 : MemLp g 2 volume := MemLp.ae_eq hmode (Lp.memLp _)
  have hkeq : (B0581.modes c U : B0581.ModeSeq ℂ) k = hg2.toLp g :=
    Lp.ext (hmode.trans hg2.coeFn_toLp.symm)
  -- (4) the `L²` Fourier transform agrees a.e. with `𝓕 g`
  have hF := fourier_toLp_ae_eq g hg1 hg2
  rw [hkeq]
  filter_upwards [hF] with ξ hξ
  -- (5) the zero-mass phase bound for the integral in the formula
  have hZ := zeroMassPhaseBound c (B0581.kappa c k) ξ (U : B0579.Plane → ℂ) hU hUw hmass
  have hpos : 0 ≤ (Real.sqrt c)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg c)
  rw [hξ, hgF ξ, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos]
  exact le_trans (mul_le_mul_of_nonneg_left hZ hpos) (le_of_eq (by ring))

end UnforcedLeray.Short.IIIa.CTE.T20_3
