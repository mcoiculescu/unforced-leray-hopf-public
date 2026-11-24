import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4

/-!
# `PartII-a:N01/9/1/2/4` (heat integral): `HeatIntPeriodic`

Source `the November 2 reference manuscript`
lines 3379-3383 (periodicity in `q` of the heat integral).  The integrand of `smoothHeatInt` is
`(σ/s)^μ • planeHeat (ν(s-σ)) (z ↦ periodize c (q⁻¹ • F) (σ,z))`; the periodized slice is
`c`-periodic in `z.1`, and `planeHeat θ` commutes with the translation `(c,0)` of a periodic
function (for `θ > 0` the Gaussian average is taken at the translated point, for `θ ≤ 0` the map
is the identity).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

/-- `planeHeat` commutes with a `c`-translation in the `q` variable of a `c`-periodic function. -/
theorem planeHeat_translate_q {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (θ : ℝ) (f : ℝ × ℝ → E)
    (hf : ∀ z : ℝ × ℝ, f (z.1 + c, z.2) = f z) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ f (x.1 + c, x.2) = UnforcedLeray.B0224.planeHeat θ f x := by
  by_cases hθ : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
    congr 1
    funext y
    have hxy : ((x.1 + c, x.2) - UnforcedLeray.B0224.planeι y)
        = ((x - UnforcedLeray.B0224.planeι y).1 + c, (x - UnforcedLeray.B0224.planeι y).2) := by
      ext
      · simp; ring
      · simp
    rw [hxy, hf]
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    exact hf x

theorem heatIntPeriodic : UnforcedLeray.Short.PartIIa.N01.HeatIntPeriodic := by
  intro c ν hc hν μ F hF s q η
  unfold UnforcedLeray.Short.PartIIa.N01.smoothHeatInt
  apply intervalIntegral.integral_congr
  intro σ _
  simp only
  congr 1
  have hfz : ∀ z : ℝ × ℝ,
      UnforcedLeray.B0220.periodize c (fun q : UnforcedLeray.B0220.Profile => (q.1)⁻¹ • F q)
          (σ, z.1 + c, z.2)
        = UnforcedLeray.B0220.periodize c (fun q : UnforcedLeray.B0220.Profile => (q.1)⁻¹ • F q)
          (σ, z) := by
    intro z
    simp only [UnforcedLeray.B0220.periodize, UnforcedLeray.B0220.reduceIoc_add hc]
  exact planeHeat_translate_q (ν * (s - σ))
    (fun z => UnforcedLeray.B0220.periodize c (fun q : UnforcedLeray.B0220.Profile => (q.1)⁻¹ • F q) (σ, z))
    hfz (q, η)
