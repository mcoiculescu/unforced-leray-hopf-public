import UnforcedLeray.Short.PartIIa.Sub.N02_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `CellFubiniS` (`Sub/N02_2.lean`): for `G` integrable on `cell c = Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)`,
the cell integral is `∫ q ∈ (0,c], ∫ η, ∫ s ∈ (0,∞), G (s, q, η)`.

Route: move the first factor `s` to the end with the measure-preserving swap
(`setIntegral_prod_swap`), split off `s` with `setIntegral_prod` (its integrability holds by the
measure-preserving swap), then split `q` and `η` with a second `setIntegral_prod` and
`Measure.restrict_univ`. The almost-everywhere integrability needed for the inner slices comes from
`Integrable.integral_prod_left` on restricted measures (`Measure.prod_restrict`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Fubini on the cell, order `(q, η, s)`** (task `PartII-a:N02/2/12`; the statement is the
unchanged `CellFubiniS` of `Sub/N02_2.lean`). -/
theorem cellFubiniS : UnforcedLeray.Short.PartIIa.CellFubiniS := by
  intro c G hG
  -- the cell and the volume on the profile, as explicit products
  have hcell : UnforcedLeray.B0220.cell c = Ioi (0:ℝ) ×ˢ (Ioc (0:ℝ) c ×ˢ univ) := rfl
  have hG' : IntegrableOn G (UnforcedLeray.B0220.cell c)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := hG
  -- the measure-preserving swap `((q, η), s) ↦ (s, (q, η))`
  have hswap : MeasurePreserving (Prod.swap : (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) :=
    Measure.measurePreserving_swap
  -- integrability of the reordered integrand on `(Ioc 0 c ×ˢ univ) ×ˢ Ioi 0`
  have hint : IntegrableOn (fun z : (ℝ × ℝ) × ℝ => G z.swap)
      ((Ioc (0:ℝ) c ×ˢ univ) ×ˢ Ioi (0:ℝ))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) := by
    have h := (hswap.integrableOn_comp_preimage MeasurableEquiv.prodComm.measurableEmbedding).mpr
      hG'
    have hpre : Prod.swap ⁻¹' UnforcedLeray.B0220.cell c
        = (Ioc (0:ℝ) c ×ˢ univ) ×ˢ Ioi (0:ℝ) := by
      rw [hcell]
      exact Set.preimage_swap_prod _ _
    rw [hpre] at h
    exact h
  -- step 1: move `s` to the end
  have h1 : ∫ p in UnforcedLeray.B0220.cell c, G p
      = ∫ z : (ℝ × ℝ) × ℝ in (Ioc (0:ℝ) c ×ˢ univ) ×ˢ Ioi (0:ℝ), G z.swap
          ∂((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) := by
    rw [hcell]
    exact (setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
      (Ioi (0:ℝ)) (Ioc (0:ℝ) c ×ˢ univ) G).symm
  -- step 2: `s` innermost (Fubini on `(Ioc 0 c ×ˢ univ) ×ˢ Ioi 0`)
  have h2 : ∫ z : (ℝ × ℝ) × ℝ in (Ioc (0:ℝ) c ×ˢ univ) ×ˢ Ioi (0:ℝ), G z.swap
          ∂((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))
      = ∫ x : ℝ × ℝ in Ioc (0:ℝ) c ×ˢ univ, (∫ y in Ioi (0:ℝ), G (y, x))
          ∂(volume : Measure (ℝ × ℝ)) :=
    setIntegral_prod (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))
      (fun z : (ℝ × ℝ) × ℝ => G z.swap) hint
  -- integrability of the inner `s`-integral on `Ioc 0 c ×ˢ univ`, from `hint` and Fubini
  have hF : IntegrableOn (fun x : ℝ × ℝ => ∫ y in Ioi (0:ℝ), G (y, x))
      (Ioc (0:ℝ) c ×ˢ univ) (volume : Measure (ℝ × ℝ)) := by
    have h := hint
    rw [IntegrableOn, ← Measure.prod_restrict] at h
    exact h.integral_prod_left
  -- step 3: split `q` and `η` (Fubini on `Ioc 0 c ×ˢ univ`, then `univ` in `η`)
  have h3 : ∫ x : ℝ × ℝ in Ioc (0:ℝ) c ×ˢ univ, (∫ y in Ioi (0:ℝ), G (y, x))
          ∂(volume : Measure (ℝ × ℝ))
      = ∫ q in Ioc (0:ℝ) c, ∫ η : ℝ, ∫ s in Ioi (0:ℝ), G (s, (q, η)) := by
    have hsplit := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun x : ℝ × ℝ => ∫ y in Ioi (0:ℝ), G (y, x)) hF
    refine hsplit.trans ?_
    simp only [Measure.restrict_univ]
  exact h1.trans (h2.trans h3)
