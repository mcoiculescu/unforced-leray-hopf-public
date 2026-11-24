import UnforcedLeray.Lib.HeatCylinder.HeatL2Semigroup

/-!
# Linearity and the contraction CLM of the actual cylinder heat family

The quotient map is linear because its selected periodic representatives agree almost everywhere
with the algebraic representatives, and B0289 proves linearity of the literal Gaussian integral
where its absolute integrals are finite. Those finiteness conditions hold almost everywhere by the
actual B0295 kernel bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

private theorem ae_heatAbs_finite {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {f : Plane → Plane} (hper : IsQPeriodic c f) (hf : AEStronglyMeasurable f volume)
    (hmem : MemLp f 2 (cellMeasure c)) :
    ∀ᵐ z ∂(cellMeasure c), UnforcedLeray.B0284.heatAbs θ f z < ⊤ := by
  have htop := UnforcedLeray.B0295.ae_kernelAbs_lt_top hc
    ((UnforcedLeray.B0284.measurable_heatKernel2_right θ).ennreal_ofReal)
    (fun _ => ENNReal.ofReal_ne_top)
    (by rw [UnforcedLeray.B0284.lintegral_heatKernel2 hθ]; exact ENNReal.one_ne_top)
    hper hf (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top
  simpa [UnforcedLeray.B0284.heatAbs] using htop

private theorem heat_add_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {f g : Plane → Plane} (hfper : IsQPeriodic c f) (hgper : IsQPeriodic c g)
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume)
    (hff : MemLp f 2 (cellMeasure c)) (hgf : MemLp g 2 (cellMeasure c)) :
    UnforcedLeray.B0284.heat θ (fun z => f z + g z) =ᵐ[cellMeasure c]
      fun z => UnforcedLeray.B0284.heat θ f z + UnforcedLeray.B0284.heat θ g z := by
  have hsumper : IsQPeriodic c (fun z => f z + g z) := by
    intro z
    simp [hfper z, hgper z]
  have hsumMeas : AEStronglyMeasurable (fun z => f z + g z) volume := hfm.add hgm
  have hsumMem : MemLp (fun z => f z + g z) 2 (cellMeasure c) := hff.add hgf
  filter_upwards [ae_heatAbs_finite hc hθ hfper hfm hff,
    ae_heatAbs_finite hc hθ hgper hgm hgf] with z hfz hgz
  simpa only [one_smul, zero_smul, add_zero] using
    UnforcedLeray.B0289.heat_add_smul hθ hfm hgm 1 1 (ne_of_lt hfz) (ne_of_lt hgz)

private theorem heat_smul_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (r : ℝ)
    {f : Plane → Plane} (hper : IsQPeriodic c f) (hf : AEStronglyMeasurable f volume)
    (hmem : MemLp f 2 (cellMeasure c)) :
    UnforcedLeray.B0284.heat θ (fun z => r • f z) =ᵐ[cellMeasure c]
      fun z => r • UnforcedLeray.B0284.heat θ f z := by
  have hzeroMem : MemLp (fun _ : Plane => (0 : Plane)) 2 (cellMeasure c) := MemLp.zero
  have hzeroMeas : AEStronglyMeasurable (fun _ : Plane => (0 : Plane)) volume :=
    stronglyMeasurable_const.aestronglyMeasurable
  filter_upwards [ae_heatAbs_finite hc hθ hper hf hmem] with z hfz
  have h0 : UnforcedLeray.B0284.heatAbs θ (fun _ : Plane => (0 : Plane)) z < ⊤ := by
    simp [UnforcedLeray.B0284.heatAbs]
  simpa only [smul_zero, add_zero, zero_smul, add_zero] using
    UnforcedLeray.B0289.heat_add_smul hθ hf hzeroMeas r 0 (ne_of_lt hfz) (ne_of_lt h0)

private theorem heatL2_memLp_heat {c θ : ℝ} (hc : 0 < c)
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
  have hh := heatL2_memLp_heat (θ := θ) hc hf.1 hf.2.1 hm
  change (hh.toLp (UnforcedLeray.B0284.heat θ f) : Plane → Plane) =ᵐ[
    cellMeasure c] UnforcedLeray.B0284.heat θ f
  exact hh.coeFn_toLp

private theorem heatL2_add_of_pos {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x y : Lp Plane 2 (cellMeasure c)) :
    heatL2 hc θ (x + y) = heatL2 hc θ x + heatL2 hc θ y := by
  let fxy := planeRep hc (x + y)
  let fx := planeRep hc x
  let fy := planeRep hc y
  have hxy := planeRep_spec hc (x + y)
  have hx := planeRep_spec hc x
  have hy := planeRep_spec hc y
  have hae : fxy =ᵐ[cellMeasure c] fun z => fx z + fy z := by
    filter_upwards [hxy.2.2, hx.2.2, hy.2.2, Lp.coeFn_add x y] with z hxyz hxz hyz hadd
    calc
      fxy z = (x + y : Lp Plane 2 (cellMeasure c)) z := hxyz
      _ = x z + y z := hadd
      _ = fx z + fy z := by rw [← hxz, ← hyz]
  have hper : IsQPeriodic c (fun z => fxy z = fx z + fy z) := by
    intro z
    have hxyper := hxy.2.1 z
    have hxper := hx.2.1 z
    have hyper := hy.2.1 z
    change (fxy (z.1 + c, z.2) = fx (z.1 + c, z.2) + fy (z.1 + c, z.2)) =
      (fxy z = fx z + fy z)
    apply propext
    constructor
    · intro h
      calc fxy z = fxy (z.1 + c, z.2) := hxyper.symm
        _ = fx (z.1 + c, z.2) + fy (z.1 + c, z.2) := h
        _ = fx z + fy z := by
          change planeRep hc x (z.1 + c, z.2) + planeRep hc y (z.1 + c, z.2) = _
          rw [hxper, hyper]
    · intro h
      calc fxy (z.1 + c, z.2) = fxy z := hxyper
        _ = fx z + fy z := h
        _ = fx (z.1 + c, z.2) + fy (z.1 + c, z.2) := by
          change planeRep hc x z + planeRep hc y z =
            planeRep hc x (z.1 + c, z.2) + planeRep hc y (z.1 + c, z.2)
          rw [← hxper, ← hyper]
  have haeVol := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hper hae
  have hheatCongr := UnforcedLeray.B0289.heat_congr_ae hθ haeVol
  have hsum := heat_add_ae hc hθ hx.2.1 hy.2.1 hx.1.aestronglyMeasurable
    hy.1.aestronglyMeasurable (memLp_planeRep hc x) (memLp_planeRep hc y)
  have houtxy := heatL2_value_ae (θ := θ) hc (x + y)
  have houtx := heatL2_value_ae (θ := θ) hc x
  have houty := heatL2_value_ae (θ := θ) hc y
  apply Lp.ext
  filter_upwards [houtxy, houtx, houty, hsum,
    Lp.coeFn_add (heatL2 hc θ x) (heatL2 hc θ y)] with z hxyOut hxOut hyOut hsumz hadd
  calc
    (heatL2 hc θ (x + y) : Plane → Plane) z = UnforcedLeray.B0284.heat θ fxy z := hxyOut
    _ = UnforcedLeray.B0284.heat θ (fun z => fx z + fy z) z := congrFun hheatCongr z
    _ = UnforcedLeray.B0284.heat θ fx z + UnforcedLeray.B0284.heat θ fy z := hsumz
    _ = (heatL2 hc θ x : Plane → Plane) z + (heatL2 hc θ y : Plane → Plane) z := by
      rw [hxOut, hyOut]
    _ = (heatL2 hc θ x + heatL2 hc θ y : Lp Plane 2 (cellMeasure c)) z := hadd.symm

private theorem heatL2_smul_of_pos {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (r : ℝ)
    (x : Lp Plane 2 (cellMeasure c)) :
    heatL2 hc θ (r • x) = r • heatL2 hc θ x := by
  let fr := planeRep hc (r • x)
  let f := planeRep hc x
  have hr := planeRep_spec hc (r • x)
  have hf := planeRep_spec hc x
  have hae : fr =ᵐ[cellMeasure c] fun z => r • f z := by
    filter_upwards [hr.2.2, hf.2.2, Lp.coeFn_smul r x] with z hrz hfz hsmul
    calc
      fr z = (r • x : Lp Plane 2 (cellMeasure c)) z := hrz
      _ = r • x z := hsmul
      _ = r • f z := by rw [← hfz]
  have hper : IsQPeriodic c (fun z => fr z = r • f z) := by
    intro z
    have hrper := hr.2.1 z
    have hfper := hf.2.1 z
    change (fr (z.1 + c, z.2) = r • f (z.1 + c, z.2)) = (fr z = r • f z)
    apply propext
    constructor
    · intro h
      calc fr z = fr (z.1 + c, z.2) := hrper.symm
        _ = r • f (z.1 + c, z.2) := h
        _ = r • f z := by
          change r • planeRep hc x (z.1 + c, z.2) = _
          rw [hfper]
    · intro h
      calc fr (z.1 + c, z.2) = fr z := hrper
        _ = r • f z := h
        _ = r • f (z.1 + c, z.2) := by
          change r • planeRep hc x z = _
          rw [← hfper]
  have haeVol := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hper hae
  have hheatCongr := UnforcedLeray.B0289.heat_congr_ae hθ haeVol
  have hsmul := heat_smul_ae hc hθ r hf.2.1 hf.1.aestronglyMeasurable (memLp_planeRep hc x)
  have houtr := heatL2_value_ae (θ := θ) hc (r • x)
  have hout := heatL2_value_ae (θ := θ) hc x
  apply Lp.ext
  filter_upwards [houtr, hout, hsmul, Lp.coeFn_smul r (heatL2 hc θ x)]
    with z hrOut hOut hsmulz hcoesm
  calc
    (heatL2 hc θ (r • x) : Plane → Plane) z = UnforcedLeray.B0284.heat θ fr z := hrOut
    _ = UnforcedLeray.B0284.heat θ (fun z => r • f z) z := congrFun hheatCongr z
    _ = r • UnforcedLeray.B0284.heat θ f z := hsmulz
    _ = r • (heatL2 hc θ x : Plane → Plane) z := by rw [hOut]
    _ = (r • heatL2 hc θ x : Lp Plane 2 (cellMeasure c)) z := hcoesm.symm

/-- The actual B0284 Gaussian heat family as a contractive normalized-cell `L²` CLM. -/
noncomputable def heatL2CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    Lp Plane 2 (cellMeasure c) →L[ℝ] Lp Plane 2 (cellMeasure c) := by
  let L : Lp Plane 2 (cellMeasure c) →ₗ[ℝ] Lp Plane 2 (cellMeasure c) :=
    { toFun := heatL2 hc θ
      map_add' := by
        intro x y
        by_cases hθ : 0 < θ
        · exact heatL2_add_of_pos hc hθ x y
        · rw [heatL2_eq_id_of_nonpos hc (not_lt.mp hθ),
            heatL2_eq_id_of_nonpos hc (not_lt.mp hθ),
            heatL2_eq_id_of_nonpos hc (not_lt.mp hθ)]
      map_smul' := by
        intro r x
        by_cases hθ : 0 < θ
        · exact heatL2_smul_of_pos hc hθ r x
        · rw [heatL2_eq_id_of_nonpos hc (not_lt.mp hθ),
            heatL2_eq_id_of_nonpos hc (not_lt.mp hθ)]
          rfl }
  exact L.mkContinuous 1 (by
    intro x
    change ‖heatL2 hc θ x‖ ≤ 1 * ‖x‖
    simpa using norm_heatL2_le hc x)

@[simp] theorem heatL2CLM_apply {c : ℝ} (hc : 0 < c) (θ : ℝ)
    (x : Lp Plane 2 (cellMeasure c)) : heatL2CLM hc θ x = heatL2 hc θ x := rfl

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatL2CLM
