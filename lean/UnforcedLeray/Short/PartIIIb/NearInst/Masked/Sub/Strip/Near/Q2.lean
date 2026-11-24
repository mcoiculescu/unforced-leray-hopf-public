import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_22_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `PartIII-b:C/near/masked/22/2/2`: measurability and `2c/R`-periodicity of `nearM` (source 4000-4003)

Leaf Q2 of `PartIII-b_C_near_masked_22_2.lean`: `NearMeasPeriodic`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

private lemma q2_floor_shift (X c : ℝ) (hc : 0 < c) :
    X + c - c * ⌊(X + c) / c + 1 / 2⌋ = X - c * ⌊X / c + 1 / 2⌋ := by
  have hc' : c ≠ 0 := hc.ne'
  rw [show (X + c) / c + 1 / 2 = X / c + 1 / 2 + 1 by field_simp; ring, Int.floor_add_one]
  push_cast
  ring

private lemma q2_chartOf_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (z : UnforcedLeray.Space)
    (τ : ℝ) :
    NearInst.chartOf R c z (τ + 2 * c / R) = NearInst.chartOf R c z τ := by
  have hR' : R ≠ 0 := hR.ne'
  have hX : R * Real.log (NearInst.hRad z / R) + R * (τ + 2 * c / R) / 2 =
      (R * Real.log (NearInst.hRad z / R) + R * τ / 2) + c := by
    field_simp
    ring
  unfold NearInst.chartOf
  rw [hX, q2_floor_shift _ c hc]

private lemma q2_cartLift_period (R c : ℝ) (g : Chart → Ten3) (hR : 0 < R) (hc : 0 < c)
    (z : UnforcedLeray.Space) (τ : ℝ) :
    NearInst.cartLift R c g (τ + 2 * c / R) z = NearInst.cartLift R c g τ z := by
  unfold NearInst.cartLift
  rw [q2_chartOf_period R c hR hc z τ]

private lemma q2_meas_hRad : Measurable fun y : UnforcedLeray.Space => NearInst.hRad y := by
  have hm0 : Measurable fun z : UnforcedLeray.Space => z 0 :=
    (EuclideanSpace.proj (0 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).continuous.measurable
  have hm1 : Measurable fun z : UnforcedLeray.Space => z 1 :=
    (EuclideanSpace.proj (1 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).continuous.measurable
  unfold NearInst.hRad
  exact Measurable.sqrt ((hm0.pow_const 2).add (hm1.pow_const 2))

/-- **Leaf Q2** (measurability and `2c/R`-periodicity of `nearM`). -/
theorem nearMeasPeriodic_holds : NearMeasPeriodic := by
  intro R c ν μ r g hR hc hν hg
  -- joint measurability of the entries of `cartLift` in `(τ, y)`
  have hT : ∀ j k : Fin 3,
      Measurable fun s : ℝ × UnforcedLeray.Space => NearInst.cartLift R c g s.1 s.2 j k :=
    fun j k => T8_1.measurable_cartLift_entry R c g hg.measurable j k
  -- `sepW` in `(τ, y)`, componentwise
  have hS : Measurable fun q : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c g) q.2 q.1 := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact T8_1.measurable_sepW_comp ν (μ : ℂ) (NearInst.cartLift R c g) i hT
  have hTo : Measurable fun q : ℝ × UnforcedLeray.Space =>
      (WithLp.toLp 2 (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c g) q.2 q.1) :
        EuclideanSpace ℂ (Fin 3)) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℂ)).measurable.comp hS
  have hN : Measurable fun q : ℝ × UnforcedLeray.Space =>
      ‖(WithLp.toLp 2 (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c g) q.2 q.1) :
        EuclideanSpace ℂ (Fin 3))‖ :=
    continuous_norm.measurable.comp hTo
  have hEN : Measurable fun q : ℝ × UnforcedLeray.Space => nearEN ν μ R c g q.1 q.2 :=
    ENNReal.measurable_ofReal.comp hN
  have hSet : MeasurableSet {q : ℝ × UnforcedLeray.Space |
      R / Real.sqrt r < NearInst.hRad q.2} :=
    measurableSet_lt measurable_const (q2_meas_hRad.comp measurable_snd)
  have hM : Measurable (Function.uncurry (nearM ν μ R c r g)) := by
    show Measurable fun q : ℝ × UnforcedLeray.Space => nearM ν μ R c r g q.1 q.2
    show Measurable fun q : ℝ × UnforcedLeray.Space =>
      if R / Real.sqrt r < NearInst.hRad q.2 then nearEN ν μ R c g q.1 q.2 else 0
    exact Measurable.ite hSet hEN measurable_const
  refine ⟨hM, fun τ y => ?_⟩
  -- the `sepW` integrand: `T(τ + P + 2 log l, z)` with `T` `P`-periodic in its phase
  have hl : ∀ (l : ℝ) (z : UnforcedLeray.Space) (j k : Fin 3),
      NearInst.cartLift R c g (τ + 2 * c / R + 2 * Real.log l) z j k =
        NearInst.cartLift R c g (τ + 2 * Real.log l) z j k := by
    intro l z j k
    rw [show τ + 2 * c / R + 2 * Real.log l = (τ + 2 * Real.log l) + 2 * c / R by ring,
      q2_cartLift_period R c g hR hc z (τ + 2 * Real.log l)]
  have hsepP : ∀ y' : UnforcedLeray.Space,
      UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c g) y' (τ + 2 * c / R) =
        UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c g) y' τ := by
    intro y'
    unfold UnforcedLeray.Short.IIIa.sepW
    simp only [hl]
  have hE : nearEN ν μ R c g (τ + 2 * c / R) y = nearEN ν μ R c g τ y := by
    unfold nearEN
    rw [hsepP y]
  unfold nearM
  rw [hE]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
