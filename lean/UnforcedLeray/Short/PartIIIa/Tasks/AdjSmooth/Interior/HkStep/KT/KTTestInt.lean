import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs

/-!
# `KTTestInt`: `X_{-m,c}` functions integrate against cylinder tests on the cell

Source: `the November 2 reference manuscript` lines 3052-3058.
A cylinder test is bounded with compact support on the cell; `|φ ψ| = |φ| |ψ|`, and the
product of the nonnegative functions `‖φ‖ ∈ X_{-m,c}` and `‖ψ‖ ∈ X_{m,c}` is integrable on the
cell by the unweighted pairing `B0579.integrableOn_mul_neg`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem ktTestInt : UnforcedLeray.Short.IIIa.KTTestInt := by
  intro c m hc φ hφ ψ hψ
  have hA : MemLp (fun x => ‖ψ x‖) 2 (UnforcedLeray.B0579.cellMeasure c m) :=
    (hψ.memLp m).norm
  have hB : MemLp (fun x => ‖φ x‖) 2 (UnforcedLeray.B0579.cellMeasure c (-m)) :=
    hφ.norm
  have h := UnforcedLeray.B0579.integrableOn_mul_neg c m
    (hA.toLp (fun x => ‖ψ x‖)) (hB.toLp (fun x => ‖φ x‖))
  have transfer : ∀ (m' : ℝ) {p : ℝ × ℝ → Prop},
      (∀ᵐ x ∂UnforcedLeray.B0579.cellMeasure c m', p x) →
      ∀ᵐ x ∂volume.restrict (UnforcedLeray.B0579.cell c), p x :=
    fun m' {p} h => ae_iff.2 ((UnforcedLeray.B0579.ac_cellMeasure c m') (ae_iff.1 h))
  have e1 := transfer m hA.coeFn_toLp
  have e2 := transfer (-m) hB.coeFn_toLp
  have hnorm : IntegrableOn (fun x => ‖ψ x‖ * ‖φ x‖) (UnforcedLeray.B0579.cell c) := by
    refine h.congr ?_
    filter_upwards [e1, e2] with x hx1 hx2
    simp only [hx1, hx2]
  have hφm : AEStronglyMeasurable φ (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    hφ.aestronglyMeasurable.mono_ac (UnforcedLeray.B0579.ac_cellMeasure c (-m))
  have hψc : Continuous fun x => (ψ x : ℂ) := Complex.continuous_ofReal.comp hψ.continuous
  refine Integrable.mono' hnorm (hφm.mul hψc.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x => by simp [norm_mul, mul_comm]
