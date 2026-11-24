import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2

/-!
# Part III-a, task `PartIII-a:T18/3/2/7` (gainLocBG): the gain conjugation stays locally `L²`

Source: `the November 2 reference manuscript` lines 3541-3552.
For `γ ≥ 0`, `ν > 0`, `s > 0`: `1 ≤ g(s)` so `|g⁻¹ f| ≤ |f|` (`vnorm2_smul_le`, `tnorm2_smul_le`),
and `lintegral_mono_ae` on `[s₁,s₂] × cell` against the assumed finite integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem gainLocBG : UnforcedLeray.Short.IIIa.GainLocBG := by
  intro c ν γ hγ hν b G hsol s1 s2 hs1 hs12
  have hS : MeasurableSet (Icc s1 s2 ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (B0579.measurableSet_cell c)
  -- pointwise bounds on `Icc s1 s2 × cell`, where `p.1 > 0`
  have hscal : ∀ᵐ p ∂(volume.restrict (Icc s1 s2 ×ˢ B0579.cell c)),
      ENNReal.ofReal (vnorm2 (gainConj γ ν b p) ^ 2) ≤
          ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) ∧
        ENNReal.ofReal (tnorm2 (gainConj γ ν G p) ^ 2) ≤
          ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    have hp1 : 0 < p.1 := lt_of_lt_of_le hs1 hp.1.1
    have hr0 : 0 ≤ (gainG γ ν p.1)⁻¹ := by
      unfold gainG
      positivity
    have hr1 : (gainG γ ν p.1)⁻¹ ≤ 1 := gainG_inv_le_one hγ hν hp1
    have hb1 : vnorm2 (gainConj γ ν b p) ≤ vnorm2 (b p) :=
      vnorm2_smul_le hr0 hr1 (b p)
    have hG1 : tnorm2 (gainConj γ ν G p) ≤ tnorm2 (G p) :=
      tnorm2_smul_le hr0 hr1 (G p)
    constructor
    · apply ENNReal.ofReal_le_ofReal
      have h2 : vnorm2 (gainConj γ ν b p) ^ 2 ≤ vnorm2 (b p) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hb1 2
      linarith [sq_nonneg (tnorm2 (G p))]
    · apply ENNReal.ofReal_le_ofReal
      have h2 : tnorm2 (gainConj γ ν G p) ^ 2 ≤ tnorm2 (G p) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hG1 2
      linarith [sq_nonneg (vnorm2 (b p))]
  have hfin := hsol s1 s2 hs1 hs12
  exact ⟨lt_of_le_of_lt (lintegral_mono_ae (hscal.mono fun p hp => hp.1)) hfin,
    lt_of_le_of_lt (lintegral_mono_ae (hscal.mono fun p hp => hp.2)) hfin⟩

end UnforcedLeray.Short.IIIa
