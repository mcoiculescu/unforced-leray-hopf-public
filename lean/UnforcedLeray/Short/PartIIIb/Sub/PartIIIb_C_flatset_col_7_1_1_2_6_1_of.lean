import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_2
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `SFCDivAE` from the weak (time-tested) divergence identity
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1`)

Source `the November 2 reference manuscript`
1650-1656.  `R₀ g ∈ solenoidalHC 0 c` is H-orthogonal to `cgrad 0 (χ ⊗ ψ)`; this is the single
analytic input `SFCDivWeak`.  The fundamental lemma of the calculus of variations (Mathlib
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) together with the continuity
`sfcDivCont` of the slice pairing then gives the a.e. identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Weak divergence identity** (source 1650-1656): for the classical representative `b` of `R₀ g`,
`∫ χ(s) (∫_cell b(s,x)·∇ψ(x) dx) ds = 0` for every `χ ∈ C_c^∞((0,∞))` and cylinder test `ψ`.
(From `R₀ g ∈ solenoidalHC 0 c`, i.e. H-orthogonality to `cgrad 0 (χ ⊗ ψ)`, `PepsC 0 c` being the
orthogonal projection onto it, and `R₀ = B0225.R0 ∘ PepsC 0 c` preserving it.) -/
def SFCDivWeak : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioi (0 : ℝ) →
        ∀ ψ, B0579.IsCylTest c ψ → ∫ s, χ s • divPairing c b ψ s = 0

theorem sfcDivAE_of (hW : SFCDivWeak) : SFCDivAE := by
  intro c ν μ hc R0 g hctx b hb hbe ψ hψ
  have hcont := sfcDivCont c b hb ψ hψ
  have hli : LocallyIntegrableOn (divPairing c b ψ) (Ioi (0 : ℝ)) volume :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  have h := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli
    (fun χ h1 h2 h3 => hW c ν μ hc R0 g hctx b hb hbe χ h1 h2 h3 ψ hψ)
  exact (ae_restrict_iff' measurableSet_Ioi).2 h

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
