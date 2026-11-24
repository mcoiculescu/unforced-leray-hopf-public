import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5

/-!
# Lemma `/2` of `PartIII-a:T21/3/5`: the `ω`-terms of the flow integrand are integrable on the cell.

`ω = vortFn hm w ∈ X_{m,c}` pairs with a continuous function vanishing for `|η|` large; such a
pairing is integrable on the cell (`B0579.integrableOn_mul_neg` after passing to `X_{-m,c}`).
The test-function factors `lapP φ` and `v·∇φ` are continuous and `η`-compactly supported.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.Exist.L2Aux

/-- A continuous function vanishing for `|η|` large is square integrable against every weight. -/
theorem memLp_band_cellMeasure {c : ℝ} {g : ℝ × ℝ → ℝ} (hg : Continuous g) {R : ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) (k : ℝ) :
    MemLp g 2 (UnforcedLeray.B0579.cellMeasure c k) := by
  have h := UnforcedLeray.B0579.memLp_cell_of_continuous (c := c)
    (g := fun x => UnforcedLeray.B0579.jb x ^ (k / 2) * g x)
    ((UnforcedLeray.B0579.continuous_jb_rpow (k / 2)).mul hg)
    (UnforcedLeray.B0579.isCompact_box c R) (fun x hx hxK => by
      have hx' : R < |x.2| := by
        by_contra h'
        exact hxK (UnforcedLeray.B0579.mem_box_of_mem_cell hx (not_lt.1 h'))
      simp [hR x hx'])
  exact ⟨hg.aestronglyMeasurable, by
    rw [UnforcedLeray.B0579.eLpNorm_cellMeasure]; exact h.2⟩

/-- The pairing of `f ∈ X_{m,c}` with a continuous, `η`-band-supported function is integrable
on the cell. -/
theorem integrableOn_band_mul {c m : ℝ} (f : UnforcedLeray.B0579.X c m) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) {R : ℝ} (hR : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) :
    IntegrableOn (fun x => f x * g x) (UnforcedLeray.B0579.cell c) := by
  have hGm := memLp_band_cellMeasure (c := c) hg hR (-m)
  have h1 := UnforcedLeray.B0579.integrableOn_mul_neg c m f (hGm.toLp g)
  have hae : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), (hGm.toLp g) x = g x :=
    (UnforcedLeray.B0579.ac_cellMeasure c (-m)).ae_le hGm.coeFn_toLp
  refine Integrable.congr h1 ?_
  filter_upwards [hae] with x hx
  rw [hx]

end UnforcedLeray.Short.IIIa.Exist.L2Aux

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.Short.IIIa.Exist.L2Aux

theorem fluxIntOmega_all : ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c), UnforcedLeray.Short.IIIa.Exist.FluxIntOmega (c := c) (m := m) hm tr := by
  intro ν c m _ hm tr
  unfold FluxIntOmega
  intro r hr w φ hφ
  have hv : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have L0 := (hφ.pd 0).pd 0
  have L1 := (hφ.pd 1).pd 1
  obtain ⟨R0, hR0⟩ := L0.band
  obtain ⟨R1, hR1⟩ := L1.band
  have hlapc : Continuous (lapP φ) := by
    unfold lapP; exact L0.continuous.add L1.continuous
  have hlapR : ∀ x : ℝ × ℝ, max R0 R1 < |x.2| → lapP φ x = 0 := by
    intro x hx
    unfold lapP
    rw [hR0 x (lt_of_le_of_lt (le_max_left _ _) hx), hR1 x (lt_of_le_of_lt (le_max_right _ _) hx),
      add_zero]
  constructor
  · refine (Integrable.ofReal (integrableOn_band_mul (w.1 : UnforcedLeray.B0579.X c m) hlapc hlapR)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [UnforcedLeray.Short.IIIa.Exist.cplx, UnforcedLeray.Short.IIIa.Exist.vortFn]
  · have hc0 : Continuous (fun x => tr.v r x 0) := (UnforcedLeray.B0238.contDiff_comp_apply hv 0).continuous
    have hc1 : Continuous (fun x => tr.v r x 1) := (UnforcedLeray.B0238.contDiff_comp_apply hv 1).continuous
    obtain ⟨S0, hS0⟩ := (hφ.pd 0).band
    obtain ⟨S1, hS1⟩ := (hφ.pd 1).band
    have hgc : Continuous (fun x => tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x +
        tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x) :=
      (hc0.mul (hφ.pd 0).continuous).add (hc1.mul (hφ.pd 1).continuous)
    have hgR : ∀ x : ℝ × ℝ, max S0 S1 < |x.2| → (tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x +
        tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x) = 0 := by
      intro x hx
      rw [hS0 x (lt_of_le_of_lt (le_max_left _ _) hx), hS1 x (lt_of_le_of_lt (le_max_right _ _) hx)]
      simp
    refine (Integrable.ofReal (integrableOn_band_mul (w.1 : UnforcedLeray.B0579.X c m) hgc hgR)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [UnforcedLeray.Short.IIIa.Exist.cplx, UnforcedLeray.Short.IIIa.Exist.vortFn]

end UnforcedLeray.Short.IIIa.Exist
