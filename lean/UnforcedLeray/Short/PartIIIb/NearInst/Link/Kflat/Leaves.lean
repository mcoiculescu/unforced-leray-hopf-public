import UnforcedLeray.Short.PartIIIb.NearInst.Link.Kflat.Assembly

/-!
# The two Isos leaves of the `𝒦^flat` assembly (source 2683-2689, 5609, 4109-4111)

Source of record: `the November 2 reference manuscript` (73 pages).

Proofs of `SrcCoefAE` (the force `(√π)⁻¹ srcIso f ∈ H` is any representative of `f`) and
`ThinFlatColG` (the thin component of `flatColG R0 f` is the thin component of `D₀⁻¹M₀R₀h`,
`h = (√π)⁻¹ srcIso f`), both stated in `NearInst/Link/Kflat/Assembly.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Kflat

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst

/-- `SrcCoefAE` (source 2683-2689): `srcMeasure = π·s^{-3/2}dς` has the null sets of
`s^{-3/2}dς`, and `(√π)⁻¹ srcIso f = f` a.e. (`coeFn_hOfSrc`). -/
theorem srcCoefAE : SrcCoefAE := by
  intro c f F hf
  have hπ : ENNReal.ofReal Real.pi ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 Real.pi_pos
  have hf' : (f : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] F := by
    have hf2 : ∀ᵐ p ∂(ENNReal.ofReal Real.pi • ageμ c (-3 / 2)),
        (f : Chart → Merid) p = F p := hf
    exact (Measure.ae_ennreal_smul_measure_iff hπ).1 hf2
  exact (coeFn_hOfSrc f).trans hf'

/-- `ThinFlatColG` (source 4109-4111, 5609): `strIso⁻¹` multiplies the thin component by
`(g⁻¹)⁻¹ = g` and `G⁻¹` by `g⁻¹`, and `(√π)⁻¹` passes through the linear maps. -/
theorem thinFlatColG : ThinFlatColG := by
  intro c mZ ρb γ ν hν o R0 f
  set Y : Zsp c mZ ρb :=
    Ring.inverse o.D0 (o.M0 (R0 ((Real.sqrt Real.pi)⁻¹ • srcIso c f))) with hY
  have hcol : o.flatColG γ hν R0 f =
      (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm Y) := by
    rw [NearOps.flatColG_apply, hY]
    simp only [map_smul]
  have h1 := coeFn_strIso_symm_fst (c := c) (mZ := mZ) (ρb := ρb) (γ := γ) (ν := ν)
    ((gainEquiv c mZ ρb γ hν).symm Y)
  have h2 : (((gainEquiv c mZ ρb γ hν).symm Y).fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
      fun p => gainInvFun γ ν p • (Y.fst : Chart → Ten3) p := by
    have he : ((gainEquiv c mZ ρb γ hν).symm Y).fst = (gainLp (z1Measure c mZ) γ hν).symm Y.fst :=
      rfl
    rw [he]
    exact coeFn_gainLp_symm _ γ hν Y.fst
  have h2' : (((gainEquiv c mZ ρb γ hν).symm Y).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      fun p => gainInvFun γ ν p • (Y.fst : Chart → Ten3) p :=
    (withDensity_absolutelyContinuous (z1Measure c mZ)
      (fun p => ENNReal.ofReal (ginv γ ν p ^ 2))).ae_le h2
  rw [hcol]
  filter_upwards [h1, h2'] with p hp1 hp2
  show Ten3.toMatrix
      ((((strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm Y)).fst : Chart → Ten3) p) =
    Ten3.toMatrix ((Y.fst : Chart → Ten3) p)
  have hne : gainInvFun γ ν p ≠ 0 := (ginv_pos' γ ν p).ne'
  rw [hp1, hp2, smul_smul, ginv_eq_gainInvFun, inv_mul_cancel₀ hne, one_smul]

end UnforcedLeray.Short.PartIIIb.NearInst.Kflat
