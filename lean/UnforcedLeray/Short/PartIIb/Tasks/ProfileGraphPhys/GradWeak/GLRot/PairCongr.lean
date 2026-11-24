import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2

/-!
# `PartII-b:T10/7/1/1/2/6`: `gl_pairCongr` (the pairing sees only the a.e. class of its second slot)

Source of record: `the November 2 reference manuscript` lines 1912-1921.
Mathematics: if `f = f'` a.e. on `ℝ × Space`, then for a.e. `t` the slices agree for a.e. `y`
(`Measure.ae_ae_of_ae_prod`), so the inner `y`-integrals agree for a.e. `t`, and the
`Ioc 0 P`-integral agrees (`integral_congr_ae`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem gl_pairCongr : UnforcedLeray.Short.IIb.GLPairCongr := by
  intro P Φ f f' hff
  unfold pairF phaseInt
  congr 1
  apply integral_congr_ae
  have h1 : ∀ᵐ z ∂(volume : Measure (ℝ × Space)), dotL (Φ z) (f z) = dotL (Φ z) (f' z) :=
    hff.mono fun z hz => by rw [hz]
  rw [Measure.volume_eq_prod] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [ae_restrict_of_ae h2] with t ht
  exact integral_congr_ae ht

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_pairCongr
