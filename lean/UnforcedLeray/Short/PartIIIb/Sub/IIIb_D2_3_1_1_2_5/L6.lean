import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5

/-!
# Moment bound for the source slice (`PartIII-b:IIIb-D2/3/1/1/2/5/6`)

Source of record: `the November 2 reference manuscript`
3631-3646 (`sep:young`, `p = 2`), 3604-3621, 4155-4156 (`SepMoment` is the `Y₂` moment).

`fMom T τ = (∫ |T(τ,z)|² dz)^{1/2}`, so `fMom T τ ^ 2 = ∫ |T(τ,z)|² dz`. Hence the `L²_τ`
integral of `fMom² ` over `(0,P]` is the `L²_τL²_z` moment `SepMoment P T` (with `q = 2`,
the normalisation `(ofReal P)⁻¹` is finite and nonzero for `P > 0`). Periodicity of `fMom` comes
from periodicity of `T`, and measurability from joint measurability of `srcNorm` on `ℝ × Space`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem l5Moment : L5Moment := by
  intro P rOut T hP hS hM
  -- joint measurability of `(τ, z) ↦ |T(τ,z)|`
  have hsrc : Measurable (fun p : ℝ × Space => IIIa.srcNorm T p.1 p.2) := by
    unfold IIIa.srcNorm IIIa.tensorNorm
    have hm : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j :=
      fun i j => hS.measurable i j
    fun_prop
  have hsq : Measurable (fun p : ℝ × Space => IIIa.srcNorm T p.1 p.2 ^ (2 : ℝ)) :=
    hsrc.pow_const _
  have hG : Measurable (fun τ : ℝ => ∫⁻ z, IIIa.srcNorm T τ z ^ (2 : ℝ)) :=
    hsq.lintegral_prod_right'
  have hfm : Measurable (fMom T) := by
    unfold fMom
    exact hG.pow_const _
  -- periodicity
  have hper : ∀ τ z, IIIa.srcNorm T (τ + P) z = IIIa.srcNorm T τ z := by
    intro τ z
    unfold IIIa.srcNorm
    rw [hS.periodic τ z]
  have hfp : ∀ τ, fMom T (τ + P) = fMom T τ := by
    intro τ
    unfold fMom
    simp only [hper]
  -- `fMom² = ∫ srcNorm²`
  have key : ∀ τ, fMom T τ ^ (2 : ℝ) = ∫⁻ z, IIIa.srcNorm T τ z ^ (2 : ℝ) := by
    intro τ
    unfold fMom
    rw [← ENNReal.rpow_mul]
    norm_num
  refine ⟨hfm, hfp, ?_⟩
  simp only [key]
  -- finiteness from `SepMoment`
  have hM' := hM
  unfold SepMoment IIIa.ltauLq at hM'
  rw [show ((2 : ℝ) / 2) = 1 by norm_num] at hM'
  simp only [ENNReal.rpow_one] at hM'
  rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at hM'
  have h0 : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.mpr hP).ne'
  have ht : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ∫⁻ τ in Ioc 0 P, ∫⁻ z, IIIa.srcNorm T τ z ^ (2 : ℝ)
      = ENNReal.ofReal P * ((ENNReal.ofReal P)⁻¹ *
          ∫⁻ τ in Ioc 0 P, ∫⁻ z, IIIa.srcNorm T τ z ^ (2 : ℝ)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM'

end UnforcedLeray.Short.PartIIIb.Concrete
