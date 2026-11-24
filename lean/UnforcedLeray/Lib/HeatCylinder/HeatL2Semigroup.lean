import UnforcedLeray.Lib.HeatCylinder.HeatL2Operator
import UnforcedLeray.Units.B0289.Semigroup
import UnforcedLeray.Units.B0295.Kernel

/-!
# Semigroup law for the actual normalized-cell Gaussian heat family

The quotient family is descended from the literal B0284 convolution. Its positive-time
composition law follows from B0289's actual Gaussian kernel semigroup identity, with the finite
absolute convolution required there obtained from the periodic L² kernel estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

private theorem memLp_planeHeat {c θ : ℝ} (hc : 0 < c)
    {f : Plane → Plane} (hf : Measurable f) (hper : IsQPeriodic c f)
    (hmem : MemLp f 2 (cellMeasure c)) :
    MemLp (UnforcedLeray.B0284.heat θ f) 2 (cellMeasure c) := by
  refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c θ hf.aestronglyMeasurable, ?_⟩
  have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hper
    hf.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
  exact lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top

private theorem heatL2_value_ae {c θ : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    (heatL2 hc θ x : Plane → Plane) =ᵐ[cellMeasure c]
      UnforcedLeray.B0284.heat θ (planeRep hc x) := by
  let f := planeRep hc x
  have hf := planeRep_spec hc x
  have hm := memLp_planeRep hc x
  have hh := memLp_planeHeat (θ := θ) hc hf.1 hf.2.1 hm
  change (hh.toLp (UnforcedLeray.B0284.heat θ f) : Plane → Plane) =ᵐ[
    cellMeasure c] UnforcedLeray.B0284.heat θ f
  exact hh.coeFn_toLp

/-- The actual normalized-cell heat family obeys the Gaussian semigroup law for strictly
positive times. -/
theorem heatL2_comp_of_pos {c α β : ℝ} (hc : 0 < c) (hα : 0 < α) (hβ : 0 < β)
    (x : Lp Plane 2 (cellMeasure c)) :
    heatL2 hc α (heatL2 hc β x) = heatL2 hc (α + β) x := by
  let f := planeRep hc x
  let hf := planeRep_spec hc x
  let hm := memLp_planeRep hc x
  let g := planeRep hc (heatL2 hc β x)
  have hg := planeRep_spec hc (heatL2 hc β x)
  have hgm := memLp_planeRep hc (heatL2 hc β x)
  have hαmem := memLp_planeHeat (θ := α) hc hg.1 hg.2.1 hgm
  have hcell : g =ᵐ[cellMeasure c] UnforcedLeray.B0284.heat β f := by
    have h1 : g =ᵐ[cellMeasure c] (heatL2 hc β x : Plane → Plane) := hg.2.2
    have h2 := heatL2_value_ae (θ := β) hc x
    exact h1.trans h2
  have hgeq : g =ᵐ[volume] UnforcedLeray.B0284.heat β f := by
    have hper : IsQPeriodic c (fun z => g z = UnforcedLeray.B0284.heat β f z) := by
      intro z
      change (g (z.1 + c, z.2) = UnforcedLeray.B0284.heat β f (z.1 + c, z.2)) =
        (g z = UnforcedLeray.B0284.heat β f z)
      apply propext
      constructor
      · intro h
        calc
          g z = g (z.1 + c, z.2) := (hg.2.1 z).symm
          _ = UnforcedLeray.B0284.heat β f (z.1 + c, z.2) := h
          _ = UnforcedLeray.B0284.heat β f z := UnforcedLeray.B0284.heat_periodic hf.2.1 z
      · intro h
        calc
          g (z.1 + c, z.2) = g z := hg.2.1 z
          _ = UnforcedLeray.B0284.heat β f z := h
          _ = UnforcedLeray.B0284.heat β f (z.1 + c, z.2) :=
            (UnforcedLeray.B0284.heat_periodic hf.2.1 z).symm
    exact UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hper hcell
  have hkernelFin : ∫⁻ w : Plane,
      ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 (α + β) w) ≠ ⊤ := by
    rw [UnforcedLeray.B0284.lintegral_heatKernel2 (add_pos hα hβ)]
    exact ENNReal.one_ne_top
  have habs := UnforcedLeray.B0295.ae_kernelAbs_lt_top hc
    ((UnforcedLeray.B0284.measurable_heatKernel2_right (α + β)).ennreal_ofReal)
    (fun _ => ENNReal.ofReal_ne_top) hkernelFin hf.2.1 hf.1.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hm.eLpNorm_ne_top
  apply Lp.ext
  filter_upwards [heatL2_value_ae (θ := α) hc (heatL2 hc β x),
    heatL2_value_ae (θ := α + β) hc x, hcell, habs] with z hleft hright hgeqz habsz
  have habs' : UnforcedLeray.B0284.heatAbs (α + β) f z ≠ ⊤ := by
    simpa [UnforcedLeray.B0284.heatAbs] using (ne_of_lt habsz)
  calc
    (heatL2 hc α (heatL2 hc β x) : Plane → Plane) z =
        UnforcedLeray.B0284.heat α g z := hleft
    _ = UnforcedLeray.B0284.heat α (UnforcedLeray.B0284.heat β f) z := by
      exact congrFun (UnforcedLeray.B0289.heat_congr_ae hα hgeq) z
    _ = UnforcedLeray.B0284.heat (α + β) f z :=
      UnforcedLeray.B0289.heat_heat hα hβ hf.1.aestronglyMeasurable habs'
    _ = (heatL2 hc (α + β) x : Plane → Plane) z := hright.symm

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatL2_comp_of_pos
