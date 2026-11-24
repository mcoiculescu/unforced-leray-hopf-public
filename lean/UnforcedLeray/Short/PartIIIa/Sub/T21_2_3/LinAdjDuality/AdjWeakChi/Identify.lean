import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_8_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakPointwise
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Unique
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K5

/-!
# Part III-a, task `PartIII-a:T21/2/3/1/8/1/3`: the identification `adjWChiIdentify`

Source of record: `the November 2 reference manuscript` lines 3052-3060.

Reduction: `ladChi tr φ ρ - χ'` pairs to zero with every cylinder test, because `adjWeakPointwise`
gives `∫ ladChi ψ = ∫ φ ∂E·uψ` for the kernel velocity `uψ` of `ψ`, and the hypothesis gives
`∫ χ' ψ` the same value. Band integrability of `ladChi` (continuity) and of `χ'` (leaf
`WeakFieldBandInt`) then gives `ladChi = χ'` a.e. by `CellUnique`.

The unconditional statement needs the leaves `AdjE1.KernelBSExists` (kernel velocity of each
test), `AdjE1.WeakFieldBandInt m`, `AdjE1.CellUnique`, `AdjE1.BandMulTest`; they are assumed in
`adjWChiIdentify_of`, which is the proved content of this file.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The identification from the four leaves (SP 3052-3060). -/
theorem adjWChiIdentify_of (m : ℝ) (k1 : AdjE1.KernelBSExists) (k2 : AdjE1.WeakFieldBandInt m)
    (k3 : AdjE1.CellUnique) (k5 : AdjE1.BandMulTest) : AdjWChiIdentify m := by
  intro hm ν c tr t s g φ hc hctx ρ hρ χ' gχ hder hfin hdual
  have hc0 : 0 < c := hctx.2.1
  have hcont : Continuous (ladChi tr φ ρ) :=
    continuous_ladChi tr hctx.2.2.1 hctx.2.2.2.2.2.2 hρ
  have hLb : ∀ R : ℝ, IntegrableOn (ladChi tr φ ρ) (AdjE1.bandSet c R) :=
    fun R => AdjE1.continuous_bandInt hcont R
  have hbandχ := k2 c χ' gχ hc0 hder hfin
  have hsub : (ladChi tr φ ρ - χ') =ᵐ[volume.restrict (B0579.cell c)] 0 := by
    refine k3 c (ladChi tr φ ρ - χ') hc0 (fun R => (hLb R).sub (hbandχ R).1) ?_
    intro ψ hψ
    obtain ⟨u, hu⟩ := k1 c ψ hc0 hψ
    have e1 := adjWeakPointwise m ν c tr t s g φ hctx ρ hρ ψ u hψ hu
    have e2 := hdual ψ u hψ hu
    have i1 := k5 c (ladChi tr φ ρ) ψ hc0 hLb hψ
    have i2 := k5 c χ' ψ hc0 (fun R => (hbandχ R).1) hψ
    rw [AdjE1.int_sub_mul c _ _ ψ i1 i2, e1, e2, sub_eq_zero]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Fin.sum_univ_two]
    push_cast
    ring
  filter_upwards [hsub] with x hx
  exact sub_eq_zero.1 hx

/-- The identification `ladChi = χ'` a.e. (SP 3052-3060), unconditional: the four leaves are proved. -/
theorem adjWChiIdentify (m : ℝ) : UnforcedLeray.Short.IIIa.AdjWChiIdentify m :=
  adjWChiIdentify_of m _root_.kernelBSExists (_root_.weakFieldBandInt m) _root_.cellUnique
    _root_.bandMulTest

end UnforcedLeray.Short.IIIa
