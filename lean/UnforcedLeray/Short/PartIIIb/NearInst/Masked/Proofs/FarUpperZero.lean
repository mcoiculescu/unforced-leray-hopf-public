import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.OpBoundOfBox

/-!
# `farUpperZero_of`: the far part has no output `s ≥ S` (source 3907, 4015-4016)

Route: `opNorm_le_of_box` with `B = 0`. For box-type `F`, the far pin gives `Sf F =ᵐ farOut f`,
`outRestr (ageAbove S)` multiplies by the indicator of `{S ≤ s}`, and `farOut f x = 0` for `S ≤ x.1`
(the `if` in `farOut`), so the product vanishes a.e.; then `‖X‖ ≤ 0` forces `X = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The far kernel output vanishes on `{S ≤ s}` (the factor `1_{s<S}` in `farOut`). -/
theorem farOut_eq_zero_of_le {R c ν μ δ S : ℝ} (f : Chart → Ten3) (x : Chart) (hx : S ≤ x.1) :
    farOut R c ν μ δ S f x = 0 := by
  simp [farOut, not_lt.mpr hx]

/-- **`farUpperZero_of`** (source 3907, 4015-4016): `1_{s≥S} S_far = 0`. -/
theorem farUpperZero_of (hD : BoxDenseZ) : FarUpperZero := by
  intro c mZ ρb R ν μ δ S hc hmZ hρ hρ1 Sf hSf
  have hX : ‖outRestr c (ageAbove S) ∘L Sf‖ ≤ 0 := by
    refine opNorm_le_of_box hD hc hmZ hρ hρ1 (outRestr c (ageAbove S) ∘L Sf) le_rfl ?_
    intro F f hf hFf
    have hS := (isFarMask_iff R ν μ δ S Sf).1 hSf F f hf hFf
    have hA : MeasurableSet (ageAbove S) := measurableSet_le measurable_const measurable_fst
    have hres : (outRestr c (ageAbove S) (Sf F) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
        (ageAbove S).indicator (fun _ => (1 : ℝ)) • (Sf F : Chart → Merid) :=
      restrLp_ae hA (Sf F)
    have hzero : ((outRestr c (ageAbove S) ∘L Sf) F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
        (0 : Chart → Merid) := by
      filter_upwards [hres, hS] with x h1 h2
      rw [ContinuousLinearMap.comp_apply, h1]
      change (ageAbove S).indicator (fun _ => (1 : ℝ)) x • (Sf F : Chart → Merid) x = 0
      rw [h2]
      by_cases hx : x ∈ ageAbove S
      · have hx' : S ≤ x.1 := hx
        rw [Set.indicator_of_mem hx, farOut_eq_zero_of_le f x hx', smul_zero]
      · rw [Set.indicator_of_notMem hx, zero_smul]
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
    simp
  exact norm_le_zero_iff.1 hX

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
