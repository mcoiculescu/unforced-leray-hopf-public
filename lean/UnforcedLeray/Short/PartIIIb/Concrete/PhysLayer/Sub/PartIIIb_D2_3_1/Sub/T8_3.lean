import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Classical decidability of axis membership (so the target statement elaborates without `open Classical`). -/
instance instDecidableMemAxis (x : Space) : Decidable (x ∈ axis) := Classical.propDecidable _

/-- Measurability of the directional derivative `D F(y) V(y)` off the axis, with value `0` on the
axis (pure measure theory, source 4240-4258 usage). The derivative is the limit of the difference
quotients `(n+1)(F(y + V/(n+1)) - F(y))`, each of which is measurable. -/
theorem measurable_fderiv_apply_offaxis {F V : ℝ → Space → Space}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2)
    (hV : Measurable fun p : ℝ × Space => V p.1 p.2)
    (hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (F τ) y) :
    Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then 0 else fderiv ℝ (F p.1) p.2 (V p.1 p.2) := by
  -- the difference quotients
  have hq : ∀ n : ℕ, Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : Space)
      else ((n : ℝ) + 1) • (F p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • V p.1 p.2) - F p.1 p.2) := by
    intro n
    have hW : Measurable fun p : ℝ × Space => ((n : ℝ) + 1)⁻¹ • V p.1 p.2 :=
      hV.const_smul (((n : ℝ) + 1)⁻¹)
    have hsum : Measurable fun p : ℝ × Space => p.2 + ((n : ℝ) + 1)⁻¹ • V p.1 p.2 :=
      measurable_snd.add hW
    have hA : Measurable fun p : ℝ × Space => F p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • V p.1 p.2) :=
      hF.comp (measurable_fst.prodMk hsum)
    have hB : Measurable fun p : ℝ × Space => F p.1 p.2 := hF
    have hS : MeasurableSet {p : ℝ × Space | p.2 ∈ axis} :=
      isClosed_axis.measurableSet.preimage measurable_snd
    exact Measurable.ite hS measurable_const ((hA.sub hB).const_smul (((n : ℝ) + 1)))
  -- the limit
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
  refine measurable_of_tendsto_metrizable hq ?_
  rw [tendsto_pi_nhds]
  intro p
  by_cases hp : p.2 ∈ axis
  · simp only [if_pos hp]
    exact tendsto_const_nhds
  · simp only [if_neg hp]
    exact (hd p.1 p.2 hp).hasFDerivAt.lim (c := fun n : ℕ => (n : ℝ) + 1) (V p.1 p.2) hc

end UnforcedLeray.Short.PartIIIb.Concrete
