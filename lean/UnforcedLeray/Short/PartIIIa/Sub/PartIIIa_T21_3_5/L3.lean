import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5

/-!
# Lemma `/3` of `PartIII-a:T21/3/5`: the `u`-terms of the flow integrand are integrable on the cell.

Under `BiotSavartField`, `u = stripVel hm w` is `L²(cell)` componentwise.  The factors
`∂E · φ` and `E · ∂φ` are continuous and `η`-band supported (`E = Ec tr r` is smooth), so each
integrand is an `L²` function times a bounded, band-supported continuous function, hence integrable.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.Exist.L3Aux

/-- A continuous function vanishing for `|η|` large is `L²` on the cell. -/
theorem memLp_band_cell {c : ℝ} {g : ℝ × ℝ → ℝ} (hg : Continuous g) {R : ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) :
    MemLp g 2 (volume.restrict (UnforcedLeray.B0579.cell c)) := by
  refine UnforcedLeray.B0579.memLp_cell_of_continuous (c := c) hg
    (UnforcedLeray.B0579.isCompact_box c R) (fun x hx hxK => ?_)
  have hx' : R < |x.2| := by
    by_contra h'
    exact hxK (UnforcedLeray.B0579.mem_box_of_mem_cell hx (not_lt.1 h'))
  exact hR x hx'

/-- An `L²(cell)` complex function times a continuous band-supported real function is integrable
on the cell. -/
theorem integrableOn_L2_band_mul {c : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (UnforcedLeray.B0579.cell c))) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) {R : ℝ} (hR : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) :
    IntegrableOn (fun x => u x * (g x : ℂ)) (UnforcedLeray.B0579.cell c) :=
  MemLp.integrable_mul hu (memLp_band_cell (c := c) hg hR).ofReal

end UnforcedLeray.Short.IIIa.Exist.L3Aux

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.Short.IIIa.Exist.L3Aux

theorem fluxIntVel_all : ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c), UnforcedLeray.Short.IIIa.Exist.FluxIntVel (c := c) (m := m) hm tr := by
  intro ν c m _ hm tr
  unfold FluxIntVel
  intro hBS r hr w φ hφ
  have hv : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun w => tr.v r w 1) z (1, 0)) :=
    ((UnforcedLeray.B0238.contDiff_comp_apply hv 1).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const
  have h0 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun w => tr.v r w 0) z (0, 1)) :=
    ((UnforcedLeray.B0238.contDiff_comp_apply hv 0).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const
  have hEq : UnforcedLeray.B0238.Ec tr r = fun z =>
      fderiv ℝ (fun w => tr.v r w 1) z (1, 0) - fderiv ℝ (fun w => tr.v r w 0) z (0, 1) :=
    funext (UnforcedLeray.B0238.curl_eq_fderiv (hv.of_le (by exact_mod_cast le_top)))
  have hE : ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr r) := by
    rw [hEq]; exact h1.sub h0
  have hEpd : ∀ j : Fin 2, Continuous (UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr r)) := by
    intro j
    exact (UnforcedLeray.B0579.contDiff_pd hE j).continuous
  obtain ⟨R, hR⟩ := hφ.band
  obtain ⟨S0, hS0⟩ := (hφ.pd 0).band
  obtain ⟨S1, hS1⟩ := (hφ.pd 1).band
  have hu0 := (hBS w).1 0
  have hu1 := (hBS w).1 1
  constructor
  · have i0 := integrableOn_L2_band_mul (c := c) hu0
      (g := fun x => UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x * φ x)
      ((hEpd 0).mul hφ.continuous)
      (R := R) (fun x hx => by rw [hR x hx, mul_zero])
    have i1 := integrableOn_L2_band_mul (c := c) hu1
      (g := fun x => UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x * φ x)
      ((hEpd 1).mul hφ.continuous)
      (R := R) (fun x hx => by rw [hR x hx, mul_zero])
    refine (i0.add i1).congr_fun (fun x _ => ?_) (UnforcedLeray.B0579.measurableSet_cell c)
    simp only [Pi.add_apply, Complex.ofReal_mul]
    ring
  · have i0 := integrableOn_L2_band_mul (c := c) hu0
      (g := fun x => UnforcedLeray.B0238.Ec tr r x * UnforcedLeray.B0579.pd 0 φ x)
      (hE.continuous.mul (hφ.pd 0).continuous)
      (R := S0) (fun x hx => by rw [hS0 x hx, mul_zero])
    have i1 := integrableOn_L2_band_mul (c := c) hu1
      (g := fun x => UnforcedLeray.B0238.Ec tr r x * UnforcedLeray.B0579.pd 1 φ x)
      (hE.continuous.mul (hφ.pd 1).continuous)
      (R := S1) (fun x hx => by rw [hS1 x hx, mul_zero])
    refine (i0.add i1).congr_fun (fun x _ => ?_) (UnforcedLeray.B0579.measurableSet_cell c)
    simp only [Pi.add_apply, Complex.ofReal_mul]
    ring

end UnforcedLeray.Short.IIIa.Exist
