import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_1

/-!
# `DictAe` (task `PartIII-b:C/near/pins/3/5/1/2`)

Source `the November 2 reference manuscript` lines 1640-1641 and 2666-2668.
For `g ∈ H` with real chart form `f`, almost every point `z` of `PSpace P` satisfies
`g (cellChart ε c (toCell P z)) = merC (f (cellPt c (cellChart ε c (toCell P z))))`.

Proof: the lift density `ρ z = ofReal ((jConst ε * liftA z.1)^2)` pushes
`volume.withDensity ρ` forward along `T z = cellChart ε c (toCell P z)` to `measureH c`
(`B0223.map_liftDensity`), on which `ChartRep` holds a.e.  Pulling back along `T`
(`ae_of_ae_map`) and removing the density zero set (`ae_withDensity_iff`) gives the claim,
since `ρ z = 0` forces `radius z.1 = 0`, a null set (`B0220.volume_axis`, times the circle).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open UnforcedLeray.B0220 (HSpace measureH Profile jConst liftA radius cellChart measurable_cellChart measurable_liftA)
open UnforcedLeray.B0223 (MeridC PSpace toCell map_liftDensity measurable_toCell)

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem dictAe : DictAe := by
  intro ε c P _ hε hc hP g f hg
  have hmap := map_liftDensity (P := P) (ε := ε) (c := c) hε hc hP
  have hT : Measurable fun z : PSpace P => cellChart ε c (toCell P z) :=
    (measurable_cellChart ε c).comp measurable_toCell
  have hA : ∀ᵐ z ∂((volume : Measure (PSpace P)).withDensity
      fun z => ENNReal.ofReal ((jConst ε * liftA z.1) ^ 2)),
      (g : Profile → MeridC) (cellChart ε c (toCell P z)) =
        merC (f (cellPt c (cellChart ε c (toCell P z)))) := by
    refine ae_of_ae_map (p := fun q => (g : Profile → MeridC) q = merC (f (cellPt c q)))
      hT.aemeasurable ?_
    rw [hmap]
    exact hg
  have hρm : Measurable fun z : PSpace P => ENNReal.ofReal ((jConst ε * liftA z.1) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_liftA.comp measurable_fst).const_mul _).pow_const 2)
  have hB := (ae_withDensity_iff hρm).1 hA
  have hNull : (volume : Measure (PSpace P)) {z : PSpace P | radius z.1 = 0} = 0 := by
    have hset : {z : PSpace P | radius z.1 = 0} =
        UnforcedLeray.B0220.axis ×ˢ (univ : Set (AddCircle P)) := by
      ext z
      exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, UnforcedLeray.B0220.volume_axis,
      zero_mul]
  have hN' : ∀ᵐ z ∂(volume : Measure (PSpace P)), z ∉ {z : PSpace P | radius z.1 = 0} :=
    measure_eq_zero_iff_ae_notMem.1 hNull
  filter_upwards [hB, hN'] with z hz1 hz2
  by_cases hr : radius z.1 = 0
  · exact absurd hr hz2
  · apply hz1
    have hj : jConst ε ≠ 0 := by
      unfold jConst
      exact inv_ne_zero (mul_ne_zero (Real.sqrt_pos.2 (by positivity)).ne' hε.ne')
    have hl : liftA z.1 ≠ 0 := by
      unfold liftA
      exact inv_ne_zero hr
    have hx : 0 < (jConst ε * liftA z.1) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (mul_ne_zero hj hl)).symm
    exact (ENNReal.ofReal_pos.2 hx).ne'

end UnforcedLeray.Short.PartIIIb.NearInst
