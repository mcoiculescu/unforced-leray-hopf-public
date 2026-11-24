import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3

/-!
# `kf3Slice` (source 3613-3616): the heat flow of a phase slice

`F = toX hP [V]` agrees a.e. with `(x, s) ↦ cplx3 (V(x, τ_s))`, `τ_s = (toCell P (0, s)).2`
(`toX_ae`, `mp_toCell_phys`, `toCell P (x, s) = (x, τ_s)` by definition).  Fubini with the
swap (`Measure.ae_ae_of_ae_prod`) gives, for a.e. phase `s`, `F(·, s) = cplx3 (V(·, τ_s))` a.e. in
`x`; the translation `y ↦ x - y` preserves Lebesgue measure, so the heat integrals agree.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem kf3Slice : KF3Slice := by
  intro ε c P _ hP V hV
  have hae := toX_ae hP (hV.toLp V)
  have hmp := mp_toCell_phys (P := P) hP
  have h3 : ∀ᵐ w ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      (hV.toLp V) (UnforcedLeray.B0223.toCell P w) = V (UnforcedLeray.B0223.toCell P w) :=
    hmp.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hV)
  have h4 : ∀ᵐ w ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      (toX hP (hV.toLp V) : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) w =
        cplx3 (V (UnforcedLeray.B0223.toCell P w)) := by
    filter_upwards [hae, h3] with w h1 h2
    rw [h1, h2]
  have hswap : ∀ᵐ z ∂((volume : Measure (AddCircle P)).prod (volume : Measure Space)),
      (toX hP (hV.toLp V) : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC)
          (z.2, z.1) = cplx3 (V (UnforcedLeray.B0223.toCell P (z.2, z.1))) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure (AddCircle P)))
      (ν := (volume : Measure Space))).quasiMeasurePreserving.ae h4
  have hs := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hs] with s hs'
  intro x θ i
  apply integral_congr_ae
  have hy := (Measure.measurePreserving_sub_left (volume : Measure Space) x).quasiMeasurePreserving.ae hs'
  filter_upwards [hy] with y hy'
  try dsimp only at hy'
  rw [hy']
  congr 1
