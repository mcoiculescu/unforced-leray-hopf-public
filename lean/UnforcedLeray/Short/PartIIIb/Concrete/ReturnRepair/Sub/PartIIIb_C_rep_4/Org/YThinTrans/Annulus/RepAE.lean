import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `OldThinPhysAE`: the old thin source has a.e. equal physical phase profiles

Source `the November 2 reference manuscript` 5148-5157 (old source `χ_o(T₁, 0)`),
4163-4166 (`χ_o`), 2666-2668 (chart).

Proof: `oldThin T = χ_o(thinPart T)` has first component `χ̂_o(νs) T₁` (a.e. on the gain measure
`gainZ1`) and second component `0` (`thinPart T` has second component `0`). Hence the two
representatives satisfy `g₁ + g₂ = oldThinTen T` `ageμ c (-1/2)`-a.e. The exceptional chart
set `N` is null, and its chart pullback is null for a.e. `(τ, z)` (`chartOfNullPullback`, applied
to a measurable null hull `N'`). Fubini gives a.e. `z` with a.e. `τ` agreement, hence equal
profiles of `srcNorm` of the physical lifts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

private lemma ra_thin_fst {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    (thinPart T).fst = T.fst := by
  simp [thinPart]

private lemma ra_thin_snd {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    (thinPart T).snd = 0 := by
  simp [thinPart]

/-- **The old thin source has a.e. equal phase profiles** (source 5148-5157, 4163-4166, 2666-2668). -/
theorem oldThinPhysAE : OldThinPhysAE := by
  intro Pl K L hρ T g₁ g₂ hg
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := by
    unfold cOf
    exact inv_pos.2 (pow_pos L.ν_pos 2)
  -- the first component of `χ_o(thinPart T)`
  have h1 : ((oldThin Pl K L T).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      cutFun K.χo L.ν • (((thinPart T).fst : Lp (α := Chart) Ten3 2
        (gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun K.χo L.ν) (cutFun_measurable K.hχo L.ν) 1
      (cutFun_bound K.hχo L.ν) (thinPart T).fst
  rw [ra_thin_fst] at h1
  have hfst : ((oldThin Pl K L T).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      oldThinTen Pl K L T := by
    filter_upwards [h1] with p hp
    rw [hp]
    rfl
  -- the second component of `χ_o(thinPart T)` vanishes
  have h2 : ((oldThin Pl K L T).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
      cutFun K.χo L.ν • (((thinPart T).snd : Lp (α := Chart) Ten3 2
        (gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun K.χo L.ν) (cutFun_measurable K.hχo L.ν) 1
      (cutFun_bound K.hχo L.ν) (thinPart T).snd
  rw [ra_thin_snd] at h2
  have h3 : ((0 : Lp (α := Chart) Ten3 2
      (gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν)) : Chart → Ten3)
      =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν] 0 :=
    Lp.coeFn_zero _ _ _
  have hsnd : ((oldThin Pl K L T).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
      0 := by
    filter_upwards [h2, h3] with p hp1 hp2
    rw [hp1, show ∀ (φ : Chart → ℝ) (g : Chart → Ten3) (x : Chart), (φ • g) x = φ x • g x from
      fun _ _ _ => rfl, hp2]
    simp
  have hg1 : g₁ =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν] oldThinTen Pl K L T :=
    hg.1.symm.trans hfst
  have hg2 : g₂ =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν] 0 :=
    hg.2.symm.trans hsnd
  -- the two components agree `ageμ`-a.e.
  have b1 : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), g₁ p = oldThinTen Pl K L T p := by
    have h := hg1
    unfold EventuallyEq at h
    rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h
    exact h
  have b2 : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), g₂ p = (0 : Chart → Ten3) p := by
    have h := hg2
    unfold EventuallyEq at h
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h
    exact h
  have hsum : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), (g₁ + g₂) p = oldThinTen Pl K L T p := by
    filter_upwards [b1, b2] with p e1 e2
    simp only [Pi.add_apply, e1, e2, Pi.zero_apply, add_zero]
  -- the exceptional set and its measurable null hull
  set N0 : Set Chart := {p : Chart | ¬ ((g₁ + g₂) p = oldThinTen Pl K L T p)} with hN0def
  have hN0' : ageμ (cOf L.ν) (-1 / 2) N0 = 0 := ae_iff.1 hsum
  set N' : Set Chart := toMeasurable (ageμ (cOf L.ν) (-1 / 2)) N0 with hN'def
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
  have hN'0 : ageμ (cOf L.ν) (-1 / 2) N' = 0 := by
    rw [hN'def, measure_toMeasurable]
    exact hN0'
  have hpull := chartOfNullPullback L.ε⁻¹ (cOf L.ν) hR hc N' hN'0
  have hSm : MeasurableSet {x : ℝ × UnforcedLeray.Space |
      NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1 ∈ N'} :=
    (T8_1.measurable_chartOf _ _) hN'm
  have hSc : MeasurableSet {x : ℝ × UnforcedLeray.Space |
      NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1 ∉ N'} :=
    hSm.compl
  -- Fubini: for a.e. `z`, a.e. `τ` the chart point is outside `N'`
  have hfub : ∀ᵐ z : UnforcedLeray.Space, ∀ᵐ τ : ℝ,
      NearInst.chartOf L.ε⁻¹ (cOf L.ν) z τ ∉ N' := by
    have h1' : ∀ᵐ τ : ℝ ∂(volume : Measure ℝ), ∀ᵐ z : UnforcedLeray.Space ∂(volume : Measure UnforcedLeray.Space),
        NearInst.chartOf L.ε⁻¹ (cOf L.ν) z τ ∉ N' :=
      Measure.ae_ae_of_ae_prod hpull
    exact (Measure.ae_ae_comm (μ := (volume : Measure ℝ))
      (ν := (volume : Measure UnforcedLeray.Space))
      (p := fun τ z => NearInst.chartOf L.ε⁻¹ (cOf L.ν) z τ ∉ N') hSc).1 h1'
  -- the profiles agree for a.e. `z`
  filter_upwards [hfub] with z hz
  filter_upwards [hz] with τ hτ
  have hτ0 : NearInst.chartOf L.ε⁻¹ (cOf L.ν) z τ ∉ N0 := fun h => hτ (subset_toMeasurable _ _ h)
  have hval : (g₁ + g₂) (NearInst.chartOf L.ε⁻¹ (cOf L.ν) z τ) =
      oldThinTen Pl K L T (NearInst.chartOf L.ε⁻¹ (cOf L.ν) z τ) := not_not.1 hτ0
  have hc2 : NearInst.cartLift L.ε⁻¹ (cOf L.ν) (g₁ + g₂) τ z =
      NearInst.cartLift L.ε⁻¹ (cOf L.ν) (oldThinTen Pl K L T) τ z := by
    unfold NearInst.cartLift
    rw [hval]
  show ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
      (NearInst.cartLift L.ε⁻¹ (cOf L.ν) (g₁ + g₂) τ z)) =
    ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
      (NearInst.cartLift L.ε⁻¹ (cOf L.ν) (oldThinTen Pl K L T) τ z))
  rw [hc2]

end UnforcedLeray.Short.PartIIIb.Concrete
