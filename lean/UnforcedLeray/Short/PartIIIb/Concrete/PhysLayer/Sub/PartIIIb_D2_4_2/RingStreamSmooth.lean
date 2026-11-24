import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs

/-!
# `RingStreamSmooth`: the ring stream is `C²` on `ρ > 0` (source 4991-4997, 5036-5039)

`ringStream R τ φ (ρ, z) = ρ φ(merChart R τ (ρ, z))`, with `merChart` `C^∞` on `ρ > 0`
(`R ≠ 0`, the logarithm argument `R²/ρ²` is positive) and mapping `ρ > 0` into `ρ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ringStreamSmooth_proof : RingStreamSmooth := by
  intro R τ φ hR hφ
  have hmer : ContDiffOn ℝ 2 (merChart R τ) (Ioi 0 ×ˢ univ) := by
    intro p hp
    have hpos : 0 < p.1 := (mem_prod.mp hp).1
    have hp1 : p.1 ≠ 0 := hpos.ne'
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => R ^ 2 / q.1 ^ 2) p :=
      contDiffAt_const.div ((contDiffAt_fst).pow 2) (pow_ne_zero 2 hp1)
    have hne : R ^ 2 / p.1 ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 hR) (pow_ne_zero 2 hp1)
    have h2 : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => R * τ / 2 - (R / 2) * Real.log (R ^ 2 / q.1 ^ 2)) p :=
      contDiffAt_const.sub (contDiffAt_const.mul (h1.log hne))
    have h3 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => R * q.2 / q.1) p :=
      (contDiffAt_const.mul contDiffAt_snd).div contDiffAt_fst hp1
    exact (h1.prodMk (h2.prodMk h3)).contDiffWithinAt
  have hmaps : MapsTo (merChart R τ) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := by
    intro p hp
    have hpos : 0 < p.1 := (mem_prod.mp hp).1
    have hR2 : 0 < R ^ 2 := by positivity
    refine mem_prod.mpr ⟨?_, mem_univ _⟩
    show (0 : ℝ) < R ^ 2 / p.1 ^ 2
    exact div_pos hR2 (pow_pos hpos 2)
  have hcomp : ContDiffOn ℝ 2 (φ ∘ merChart R τ) (Ioi 0 ×ˢ univ) := hφ.comp hmer hmaps
  have hfst : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => p.1) (Ioi 0 ×ˢ univ) :=
    contDiff_fst.contDiffOn
  exact hfst.mul hcomp

end UnforcedLeray.Short.PartIIIb.Concrete
