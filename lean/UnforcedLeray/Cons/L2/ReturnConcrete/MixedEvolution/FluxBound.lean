import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxLinear
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.CellMultiplier

/-!
# Weighted coefficient multiplier for the actual flux

This file begins the fixed-cylinder continuity estimate for the physical flux. The curl factor is
bounded only on the centered cell, matching the weighted pivot and the periodic train coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579
open UnforcedLeray.B0581 (cellVol)
open UnforcedLeray.Train (Vec)

/-- At zero weight, the centered-cell weighted measure is the ordinary cylinder cell measure. -/
theorem cellMeasure_zero_eq_cellVol (c : ℝ) : cellMeasure c 0 = cellVol c := by
  rw [cellMeasure, cellVol]
  have hd : (fun x : Plane => ((B0579.density (0 : ℝ) x : NNReal) : ENNReal)) =
      fun _ => (1 : ENNReal) := by
    funext x
    have hreal : (B0579.density (0 : ℝ) x : ℝ) = 1 := by
      rw [B0579.coe_density]
      simp [Real.rpow_zero]
    have hnn : B0579.density (0 : ℝ) x = 1 := by
      apply Subtype.ext
      exact hreal
    exact_mod_cast hnn
  rw [hd]
  exact withDensity_one

/-- The identity CLM from ordinary cell L² to the zero-weight pivot `X₀`. -/
def cellVolToXZero (c : ℝ) : Lp ℝ 2 (cellVol c) →L[ℝ] X c 0 := by
  exact MeasureTheory.Lp.LpToLpOfMeasureLeSMul
    (E := ℝ) (p := 2) (μ := cellMeasure c 0) (ν := cellVol c) (c := 1)
    (by norm_num) (by rw [cellMeasure_zero_eq_cellVol]; simp)

/-- Weighted multiplication from ordinary cell L² into the physical weighted pivot. -/
def weightedCellMultiplier {c m : ℝ} (E : Plane → ℝ) (hE : Continuous E)
    {CE : ℝ} (hCE : 0 ≤ CE)
    (hbound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    Lp ℝ 2 (cellVol c) →L[ℝ] X c m := by
  let r : Plane → ℝ := fun x => bracket x ^ m * E x
  have hr : Continuous r := (continuous_bracket_rpow m).mul hE
  let W : X c 0 →L[ℝ] X c m := (mulW c 0 m).toContinuousLinearMap
  let R : X c 0 →L[ℝ] X c 0 := mulRCell c 0 r hr hCE hbound
  exact W.comp (R.comp (cellVolToXZero c))

/-- The multiplier realization agrees in the weighted pivot with multiplication by `E` on
ordinary cell `L²`. -/
theorem memLp_cell_E_mul {c m : ℝ} (E : Plane → ℝ) (hE : Continuous E)
    {CE : ℝ} (hCE : 0 ≤ CE)
    (hbound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (f : Lp ℝ 2 (cellVol c)) : MemLp (fun x => E x * f x) 2 (cellMeasure c m) := by
  apply (memLp_cellMeasure_iff c m).2
  have hr : MemLp (fun x => (bracket x ^ m * E x) * f x) 2 (cellVol c) := by
    refine ((Lp.memLp f).const_mul CE).of_le
      (((continuous_bracket_rpow m).mul hE).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))
      (ae_restrict_of_forall_mem (measurableSet_cell c) fun x hx => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |(bracket x ^ m * E x) * f x| ≤ CE * |f x| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg _)
      _ = |CE * f x| := by rw [abs_mul, abs_of_nonneg hCE]
  simpa [cellVol, mul_assoc] using hr

theorem weightedCellMultiplier_eq_mul {c m : ℝ} (E : Plane → ℝ) (hE : Continuous E)
    {CE : ℝ} (hCE : 0 ≤ CE)
    (hbound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (f : Lp ℝ 2 (cellVol c)) :
    weightedCellMultiplier E hE hCE hbound f =
      (memLp_cell_E_mul E hE hCE hbound f).toLp (fun x => E x * f x) := by
  apply Lp.ext
  filter_upwards [
    coeFn_mulW c 0 m
      (mulRCell c 0 (fun x => bracket x ^ m * E x)
        ((continuous_bracket_rpow m).mul hE) hCE hbound (cellVolToXZero c f)),
    (cellMeasure_ac_cellMeasure c m 0).ae_le
      (MemLp.coeFn_toLp (memLp_mulR_cell ((continuous_bracket_rpow m).mul hE)
        hCE hbound (cellVolToXZero c f))),
    (cellMeasure_ac_cellMeasure c m 0).ae_le
      (MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
        (E := ℝ) (p := 2) (μ := cellMeasure c 0) (ν := cellVol c) (c := 1)
        (by norm_num) (by rw [cellMeasure_zero_eq_cellVol]; simp) f),
    MemLp.coeFn_toLp (memLp_cell_E_mul E hE hCE hbound f)] with x hW hR hC hTarget
  change (mulW c 0 m
      (mulRCell c 0 (fun x => bracket x ^ m * E x)
        ((continuous_bracket_rpow m).mul hE) hCE hbound (cellVolToXZero c f) :
          X c 0)) x =
    ((memLp_cell_E_mul E hE hCE hbound f).toLp (fun x => E x * f x) :
      Lp ℝ 2 (cellMeasure c m)) x
  rw [hW]
  change jb x ^ ((0 - m) / 2) *
      (((memLp_mulR_cell ((continuous_bracket_rpow m).mul hE) hCE hbound
          (cellVolToXZero c f)).toLp _) : X c 0) x = _
  rw [hR]
  simp only [cellVolToXZero]
  rw [hC, hTarget]
  have hpow : jb x ^ ((0 - m) / 2) * jb x ^ (m / 2) = 1 := by
    rw [← Real.rpow_add (jb_pos x)]
    have he : (0 - m) / 2 + m / 2 = 0 := by ring
    rw [he, Real.rpow_zero]
  change jb x ^ ((0 - m) / 2) * (bracket x ^ m * E x * f x) = E x * f x
  rw [bracket_rpow]
  calc
    jb x ^ ((0 - m) / 2) * (jb x ^ (m / 2) * E x * f x) =
        (jb x ^ ((0 - m) / 2) * jb x ^ (m / 2)) * (E x * f x) := by ring
    _ = E x * f x := by rw [hpow, one_mul]

/-- The actual weighted multiplication costs only the centered-cell coefficient bound. -/
theorem norm_weightedCellMultiplier_le {c m : ℝ} (E : Plane → ℝ) (hE : Continuous E)
    {CE : ℝ} (hCE : 0 ≤ CE)
    (hbound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (f : Lp ℝ 2 (cellVol c)) :
    ‖weightedCellMultiplier E hE hCE hbound f‖ ≤ CE * ‖f‖ := by
  let z : X c 0 := cellVolToXZero c f
  have hR := norm_mulRCell_le (c := c) (m := 0)
    (r := fun x => bracket x ^ m * E x)
    ((continuous_bracket_rpow m).mul hE) hCE hbound z
  have hW : ‖(mulW c 0 m).toContinuousLinearMap (mulRCell c 0
      (fun x => bracket x ^ m * E x) ((continuous_bracket_rpow m).mul hE)
      hCE hbound z)‖ = ‖mulRCell c 0 (fun x => bracket x ^ m * E x)
      ((continuous_bracket_rpow m).mul hE) hCE hbound z‖ := by
    exact (mulW c 0 m).norm_map _
  change ‖(mulW c 0 m).toContinuousLinearMap
      (mulRCell c 0 (fun x => bracket x ^ m * E x)
        ((continuous_bracket_rpow m).mul hE) hCE hbound z)‖ ≤ CE * ‖f‖
  rw [hW]
  have hz : ‖z‖ ≤ ‖f‖ := by
    have hmap : ‖cellVolToXZero c‖ ≤ 1 := by
      simpa [cellVolToXZero] using
        (MeasureTheory.Lp.norm_LpToLpOfMeasureLeSMul_le
          (E := ℝ) (p := 2) (μ := cellMeasure c 0) (ν := cellVol c) (c := 1)
          (by norm_num) (by rw [cellMeasure_zero_eq_cellVol]; simp))
    calc
      ‖z‖ ≤ ‖cellVolToXZero c‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hmap (norm_nonneg _)
      _ = ‖f‖ := one_mul _
  calc
    ‖mulRCell c 0 (fun x => bracket x ^ m * E x)
        ((continuous_bracket_rpow m).mul hE) hCE hbound z‖ ≤ CE * ‖z‖ := hR
    _ ≤ CE * ‖f‖ := mul_le_mul_of_nonneg_left hz hCE

/-- The coordinate map on the actual Euclidean train vector. -/
def trainVecComponentCLM (i : Fin 2) : Vec →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

/-- Projection to a physical vector component is contractive on cell `L²`. -/
theorem norm_cellComponentLp_le {c : ℝ} (i : Fin 2) (K : Lp Vec 2 (cellVol c)) :
    ‖((trainVecComponentCLM i).compLpL 2 (cellVol c) K)‖ ≤ ‖K‖ := by
  let P : Vec →L[ℝ] ℝ := trainVecComponentCLM i
  change ‖P.compLpL 2 (cellVol c) K‖ ≤ ‖K‖
  calc
    ‖P.compLpL 2 (cellVol c) K‖ ≤ 1 * ‖K‖ := by
      refine Lp.norm_le_mul_norm_of_ae_le_mul (c := 1)
        (f := P.compLpL 2 (cellVol c) K) (g := K) ?_
      filter_upwards [P.coeFn_compLpL K] with x hx
      change ‖(P.compLpL 2 (cellVol c) K) x‖ ≤
        1 * ‖(K : Plane → Vec) x‖
      rw [hx, one_mul]
      exact PiLp.norm_apply_le (K x) i
    _ = ‖K‖ := one_mul _

/-- The actual curl-weighted Biot--Savart term in one flux component has its explicit fixed-cell
bound. This estimate is a fixed-parameter existence input; its `c`-dependence is not a uniform
return-rate estimate. -/
theorem norm_weightedRealBiotSavartComponent_le {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (E : Plane → ℝ) (hE : Continuous E) {CE : ℝ} (hCE : 0 ≤ CE)
    (hbound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (i : Fin 2)
    (w : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)) :
    ‖weightedCellMultiplier E hE hCE hbound
        ((trainVecComponentCLM i).compLpL 2 (cellVol c)
          (realBiotSavartKernelCLM hm w))‖ ≤
      CE * ((c / (2 * Real.pi) + 2) * ‖w‖) := by
  calc
    ‖weightedCellMultiplier E hE hCE hbound
        ((trainVecComponentCLM i).compLpL 2 (cellVol c)
          (realBiotSavartKernelCLM hm w))‖ ≤
        CE * ‖(trainVecComponentCLM i).compLpL 2 (cellVol c)
          (realBiotSavartKernelCLM hm w)‖ :=
      norm_weightedCellMultiplier_le E hE hCE hbound _
    _ ≤ CE * ((c / (2 * Real.pi) + 2) * ‖w‖) := by
      apply mul_le_mul_of_nonneg_left _ hCE
      exact (norm_cellComponentLp_le i (realBiotSavartKernelCLM hm w)).trans
        (norm_realBiotSavartKernelCLM_le hm w)

/-- The coefficient-multiplied first term is represented by the actual centered-cell multiplier. -/
theorem coeFn_mulRCell {c m : ℝ} {r : Plane → ℝ} (hr : Continuous r) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x ∈ cell c, |r x| ≤ C) (f : X c m) :
    (mulRCell c m r hr hC hbound f : Plane → ℝ) =ᵐ[cellMeasure c m]
      fun x => r x * f x :=
  MemLp.coeFn_toLp (memLp_mulR_cell hr hC hbound f)

/-- The actual physical flux column splits into bounded train multiplication and the actual
curl-weighted B0583 Biot--Savart term. -/
theorem physicalFluxX_component_decomp {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (i : Fin 2) :
    physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound i =
      mulRCell c m (fun x => v x i)
        (by fun_prop) hCv
        (fun x hx => hvBound x i) w +
      weightedCellMultiplier E hE hCE hEBound
        ((trainVecComponentCLM i).compLpL 2 (cellVol c)
          (realBiotSavartKernelCLM hm
            ⟨w, (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w).2 hcirc⟩)) := by
  let wz : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) :=
    ⟨w, (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w).2 hcirc⟩
  let P : Vec →L[ℝ] ℝ := trainVecComponentCLM i
  have hP0 :
      P.compLpL 2 (cellVol c) (realBiotSavartKernelCLM hm wz) =ᵐ[cellMeasure c 0]
        fun x => P ((realBiotSavartKernelCLM hm wz : Lp Vec 2 (cellVol c)) x) := by
    rw [cellMeasure_zero_eq_cellVol]
    exact P.coeFn_compLpL (realBiotSavartKernelCLM hm wz)
  rw [weightedCellMultiplier_eq_mul E hE hCE hEBound]
  rw [physicalFluxX]
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp (memLp_physicalFlux hm v E w hcirc hCv hCE hv hE hvBound hEBound i),
    coeFn_mulRCell (by fun_prop)
      hCv (fun x hx => hvBound x i) w,
    (cellMeasure_ac_cellMeasure c m 0).ae_le hP0,
    MemLp.coeFn_toLp (memLp_cell_E_mul E hE hCE hEBound
      (P.compLpL 2 (cellVol c) (realBiotSavartKernelCLM hm wz))),
    Lp.coeFn_add
      (mulRCell c m (fun x => v x i) (by fun_prop) hCv (fun x hx => hvBound x i) w)
      ((memLp_cell_E_mul E hE hCE hEBound
        (P.compLpL 2 (cellVol c) (realBiotSavartKernelCLM hm wz))).toLp _)]
      with x hF hV hP hEterm hsum
  have hK : (realBiotSavartKernelCLM hm wz : Lp Vec 2 (cellVol c)) =
      realBiotSavart hm w hcirc := rfl
  have hPi : ∀ y : Vec, P y = y.ofLp i := by
    intro y
    rfl
  rw [hF, hsum, Pi.add_apply, hV, hEterm, hP, hK]
  rw [hPi]
  simp [physicalFlux, smul_eq_mul, mul_comm]

/-- Each component of the actual physical flux has the explicit fixed-cylinder bound. -/
theorem norm_physicalFluxX_component_le {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (i : Fin 2) :
    ‖physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound i‖ ≤
      (Cv + CE * (c / (2 * Real.pi) + 2)) * ‖w‖ := by
  let wz : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) :=
    ⟨w, (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w).2 hcirc⟩
  have hvi : Continuous fun x => v x i := by fun_prop
  rw [physicalFluxX_component_decomp hm v E w hcirc hCv hCE hv hE hvBound hEBound i]
  calc
    ‖mulRCell c m (fun x => v x i) hvi hCv (fun x hx => hvBound x i) w +
        weightedCellMultiplier E hE hCE hEBound
          ((trainVecComponentCLM i).compLpL 2 (cellVol c)
            (realBiotSavartKernelCLM hm wz))‖ ≤
      ‖mulRCell c m (fun x => v x i) hvi hCv (fun x hx => hvBound x i) w‖ +
        ‖weightedCellMultiplier E hE hCE hEBound
          ((trainVecComponentCLM i).compLpL 2 (cellVol c)
            (realBiotSavartKernelCLM hm wz))‖ := norm_add_le _ _
    _ ≤ Cv * ‖w‖ + CE * ((c / (2 * Real.pi) + 2) * ‖wz‖) :=
      add_le_add
        (norm_mulRCell_le hvi hCv (fun x hx => hvBound x i) w)
        (norm_weightedRealBiotSavartComponent_le hm E hE hCE hEBound i wz)
    _ = (Cv + CE * (c / (2 * Real.pi) + 2)) * ‖w‖ := by
      have hn : ‖wz‖ = ‖w‖ := rfl
      rw [hn]
      ring

/-- The actual train source has the corresponding fixed-parameter estimate. Its explicit factor
grows polynomially in `c`; it is not the uniform mixed-evolution exponent from the manuscript. -/
theorem norm_trainPhysicalSource_fixed_le {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c,
      |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    ‖trainPhysicalSource tr hs hm w hcirc hCv hCE hvBound hEBound‖ ≤
      2 * (Cv + CE * (c / (2 * Real.pi) + 2)) * ‖w‖ := by
  have hsum := norm_trainPhysicalSource_le tr hs hm w hcirc hCv hCE hvBound hEBound
  have hvsmooth := UnforcedLeray.B0238.contDiff_Vc tr hs
  have hv : Continuous (UnforcedLeray.B0238.Vc tr s) := hvsmooth.continuous
  have hE : Continuous (UnforcedLeray.B0238.Ec tr s) := by
    unfold UnforcedLeray.B0238.Ec
    exact UnforcedLeray.B0238.continuous_curl (hvsmooth.of_le (by norm_num))
  calc
    ‖trainPhysicalSource tr hs hm w hcirc hCv hCE hvBound hEBound‖ ≤
        ‖trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 0‖ +
          ‖trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1‖ := hsum
    _ ≤ (Cv + CE * (c / (2 * Real.pi) + 2)) * ‖w‖ +
          (Cv + CE * (c / (2 * Real.pi) + 2)) * ‖w‖ := by
      apply add_le_add
      · exact norm_physicalFluxX_component_le hm (UnforcedLeray.B0238.Vc tr s)
          (UnforcedLeray.B0238.Ec tr s) w hcirc hCv hCE hv hE hvBound hEBound 0
      · exact norm_physicalFluxX_component_le hm (UnforcedLeray.B0238.Vc tr s)
          (UnforcedLeray.B0238.Ec tr s) w hcirc hCv hCE hv hE hvBound hEBound 1
    _ = 2 * (Cv + CE * (c / (2 * Real.pi) + 2)) * ‖w‖ := by ring

#print axioms weightedCellMultiplier_eq_mul
#print axioms norm_weightedRealBiotSavartComponent_le
#print axioms physicalFluxX_component_decomp
#print axioms norm_physicalFluxX_component_le
#print axioms norm_trainPhysicalSource_fixed_le

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
