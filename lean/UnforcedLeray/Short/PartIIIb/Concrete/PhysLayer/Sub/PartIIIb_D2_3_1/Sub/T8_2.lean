import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Measurability of the outward primitive in all its arguments (source 4178-4179). -/
theorem outPrim_measurable {Z : ℝ → Space → Space} (hZ : Measurable fun p : ℝ × Space => Z p.1 p.2) :
    Measurable fun q : ℝ × ℝ × ℝ => outPrim Z q.1 q.2.1 q.2.2 := by
  -- the integrand as a function of (q, ρ)
  have hpt : Measurable fun x : (ℝ × ℝ × ℝ) × ℝ => (WithLp.toLp 2 ![x.2, 0, x.1.2.2] : Space) := by
    apply Continuous.measurable
    exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
  have hZc : Measurable fun x : (ℝ × ℝ × ℝ) × ℝ => Z x.1.1 (WithLp.toLp 2 ![x.2, 0, x.1.2.2] : Space) :=
    hZ.comp (measurable_fst.fst.prodMk hpt)
  have hcoord : Measurable fun v : Space => v 2 := by
    exact (measurable_pi_apply 2).comp (PiLp.continuous_ofLp 2 _).measurable
  have hg : Measurable fun x : (ℝ × ℝ × ℝ) × ℝ =>
      x.2 * Z x.1.1 (WithLp.toLp 2 ![x.2, 0, x.1.2.2] : Space) 2 :=
    measurable_snd.mul (hcoord.comp hZc)
  have hset : MeasurableSet {x : (ℝ × ℝ × ℝ) × ℝ | x.1.2.1 < x.2} :=
    measurableSet_lt (by fun_prop) measurable_snd
  have hG : Measurable fun x : (ℝ × ℝ × ℝ) × ℝ =>
      (Ioi x.1.2.1).indicator (fun ρ => ρ * Z x.1.1 (WithLp.toLp 2 ![ρ, 0, x.1.2.2] : Space) 2) x.2 :=
    by
      have heq : (fun x : (ℝ × ℝ × ℝ) × ℝ =>
          (Ioi x.1.2.1).indicator (fun ρ => ρ * Z x.1.1 (WithLp.toLp 2 ![ρ, 0, x.1.2.2] : Space) 2) x.2)
          = {x : (ℝ × ℝ × ℝ) × ℝ | x.1.2.1 < x.2}.indicator
              (fun x : (ℝ × ℝ × ℝ) × ℝ => x.2 * Z x.1.1 (WithLp.toLp 2 ![x.2, 0, x.1.2.2] : Space) 2) := by
        funext x
        by_cases h : x.1.2.1 < x.2
        · simp [Set.indicator, h]
        · simp [Set.indicator, h]
      rw [heq]
      exact hg.indicator hset
  have hGsm : StronglyMeasurable fun x : (ℝ × ℝ × ℝ) × ℝ =>
      (Ioi x.1.2.1).indicator (fun ρ => ρ * Z x.1.1 (WithLp.toLp 2 ![ρ, 0, x.1.2.2] : Space) 2) x.2 :=
    hG.stronglyMeasurable
  have key : (fun q : ℝ × ℝ × ℝ => outPrim Z q.1 q.2.1 q.2.2) =
      fun q : ℝ × ℝ × ℝ => -∫ ρ, (Ioi q.2.1).indicator
        (fun ρ => ρ * Z q.1 (WithLp.toLp 2 ![ρ, 0, q.2.2] : Space) 2) ρ := by
    funext q
    unfold outPrim
    rw [integral_indicator measurableSet_Ioi]
  rw [key]
  exact ((StronglyMeasurable.integral_prod_right' (ν := volume) hGsm).measurable).neg

end UnforcedLeray.Short.PartIIIb.Concrete
