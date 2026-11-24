import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.NonzeroBiotSavart
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Circulation
import UnforcedLeray.Units.B0583.ZeroVel

/-!
# Additivity of the actual horizontal mean and zero-mode primitive

The horizontal mean is only linear almost everywhere in age: Lp inputs need not have integrable
horizontal sections at every point. The Fubini argument below keeps the representative issue
explicit, then the primitive inherits pointwise additivity from equality a.e. in the vertical
variable.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579 (X)
open UnforcedLeray.B0581 (cellVol μq cellVol_eq)
open UnforcedLeray.B0583 (omegaBar)
open UnforcedLeray.Train (Vec)

/-- The horizontal mean commutes with addition almost everywhere in `η`. -/
theorem omegaBar_add_ae {c m : ℝ} (hm : 1 ≤ m) (w z : X c m) :
    omegaBar c ((w + z : X c m) : B0579.Plane → ℝ) =ᵐ[volume]
      fun η => omegaBar c (w : B0579.Plane → ℝ) η + omegaBar c (z : B0579.Plane → ℝ) η := by
  have hw := UnforcedLeray.B0583.integrable_of_X hm w
  have hz := UnforcedLeray.B0583.integrable_of_X hm z
  rw [cellVol_eq] at hw hz
  have hsumCell : (fun x : B0579.Plane =>
      ((w + z : X c m) : B0579.Plane → ℝ) x) =ᵐ[cellVol c]
      fun x => (w : B0579.Plane → ℝ) x + (z : B0579.Plane → ℝ) x := by
    exact (UnforcedLeray.B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_add w z)
  rw [cellVol_eq] at hsumCell
  have hsum : (fun x : B0579.Plane =>
      ((w + z : X c m) : B0579.Plane → ℝ) x) =ᵐ[(μq c).prod (volume : Measure ℝ)]
      fun x => (w : B0579.Plane → ℝ) x + (z : B0579.Plane → ℝ) x := hsumCell
  have hsumSwap := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := μq c)).quasiMeasurePreserving.ae_eq_comp hsum
  have hsections := Measure.ae_ae_of_ae_prod hsumSwap
  filter_upwards [hsections, hw.prod_left_ae, hz.prod_left_ae] with η hsec hwη hzη
  have hsec' : (fun q : ℝ => ((w + z : X c m) : B0579.Plane → ℝ) (q, η)) =ᵐ[μq c]
      fun q => (w : B0579.Plane → ℝ) (q, η) + (z : B0579.Plane → ℝ) (q, η) := by
    filter_upwards [hsec] with q hq
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using hq
  have hInt : (∫ q in UnforcedLeray.B0581.qInt c,
        ((w + z : X c m) : B0579.Plane → ℝ) (q, η)) =
      (∫ q in UnforcedLeray.B0581.qInt c, (w : B0579.Plane → ℝ) (q, η)) +
        ∫ q in UnforcedLeray.B0581.qInt c, (z : B0579.Plane → ℝ) (q, η) := by
    calc
      _ = ∫ q in UnforcedLeray.B0581.qInt c,
          ((w : B0579.Plane → ℝ) (q, η) + (z : B0579.Plane → ℝ) (q, η)) :=
            integral_congr_ae hsec'
      _ = _ := integral_add hwη hzη
  change c⁻¹ * (∫ q in UnforcedLeray.B0581.qInt c,
      ((w + z : X c m) : B0579.Plane → ℝ) (q, η)) =
    c⁻¹ * (∫ q in UnforcedLeray.B0581.qInt c, (w : B0579.Plane → ℝ) (q, η)) +
      c⁻¹ * (∫ q in UnforcedLeray.B0581.qInt c, (z : B0579.Plane → ℝ) (q, η))
  rw [hInt]
  ring

/-- The Hardy primitive preserves addition when its integrands agree almost everywhere. -/
theorem zeroModePrimitive_add_of_ae {f g h : ℝ → ℝ}
    (hg : Integrable g) (hh : Integrable h)
    (hEq : f =ᵐ[volume] fun η => g η + h η) (η : ℝ) :
    UnforcedLeray.B0582.zeroModePrimitive f η =
      UnforcedLeray.B0582.zeroModePrimitive g η +
        UnforcedLeray.B0582.zeroModePrimitive h η := by
  rw [UnforcedLeray.B0582.zeroModePrimitive,
    UnforcedLeray.B0582.zeroModePrimitive,
    UnforcedLeray.B0582.zeroModePrimitive]
  have hEqη : f =ᵐ[volume.restrict (Set.Iic η)] (fun y => g y + h y) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
    filter_upwards [hEq] with y hy hyI
    exact hy
  calc
    _ = ∫ y in Set.Iic η, (g y + h y) := integral_congr_ae hEqη
    _ = _ := integral_add hg.integrableOn hh.integrableOn

/-- For zero-circulation data, the actual horizontal-mean primitive is additive. -/
theorem omegaBarPrimitive_add {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w z : X c m) (hw0 : ∫ x in B0579.cell c, w x = 0)
    (hz0 : ∫ x in B0579.cell c, z x = 0) (η : ℝ) :
    UnforcedLeray.B0582.zeroModePrimitive
        (omegaBar c ((w + z : X c m) : B0579.Plane → ℝ)) η =
      UnforcedLeray.B0582.zeroModePrimitive (omegaBar c w) η +
        UnforcedLeray.B0582.zeroModePrimitive (omegaBar c z) η := by
  apply zeroModePrimitive_add_of_ae
    (UnforcedLeray.B0583.zeroMode_facts (Fact.out : 0 < c) hm w hw0).1
    (UnforcedLeray.B0583.zeroMode_facts (Fact.out : 0 < c) hm z hz0).1
  exact omegaBar_add_ae hm w z

/-- The actual zero-mode Biot--Savart column is additive on zero-circulation inputs. -/
theorem zeroVelLp_add {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w z : X c m) (hw0 : ∫ x in B0579.cell c, w x = 0)
    (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    UnforcedLeray.B0583.zeroVelLp c hm (w + z) hwz0 =
      UnforcedLeray.B0583.zeroVelLp c hm w hw0 +
        UnforcedLeray.B0583.zeroVelLp c hm z hz0 := by
  apply Lp.ext
  filter_upwards [
    UnforcedLeray.B0583.coeFn_zeroVelLp c hm (w + z) hwz0,
    UnforcedLeray.B0583.coeFn_zeroVelLp c hm w hw0,
    UnforcedLeray.B0583.coeFn_zeroVelLp c hm z hz0,
    Lp.coeFn_add (UnforcedLeray.B0583.zeroVelLp c hm w hw0)
      (UnforcedLeray.B0583.zeroVelLp c hm z hz0)] with x hsum hw hz hadd
  rw [hsum, hadd, Pi.add_apply, hw, hz]
  change UnforcedLeray.B0583.zeroVel c ((w + z : X c m) : B0579.Plane → ℝ) x =
    UnforcedLeray.B0583.zeroVel c (w : B0579.Plane → ℝ) x +
      UnforcedLeray.B0583.zeroVel c (z : B0579.Plane → ℝ) x
  simp only [UnforcedLeray.B0583.zeroVel, UnforcedLeray.B0583.profField]
  rw [omegaBarPrimitive_add hm w z hw0 hz0 x.2]
  simp only [neg_add, Complex.ofReal_add, add_smul]

/-- The horizontal mean commutes with real scalar multiplication almost everywhere. -/
theorem omegaBar_smul_ae {c m : ℝ} (hm : 1 ≤ m) (a : ℝ) (w : X c m) :
    omegaBar c ((a • w : X c m) : B0579.Plane → ℝ) =ᵐ[volume]
      fun η => a * omegaBar c (w : B0579.Plane → ℝ) η := by
  have hw := UnforcedLeray.B0583.integrable_of_X hm w
  have haw := UnforcedLeray.B0583.integrable_of_X hm (a • w)
  rw [cellVol_eq] at hw haw
  have hmulCell : (fun x : B0579.Plane =>
      ((a • w : X c m) : B0579.Plane → ℝ) x) =ᵐ[cellVol c]
      fun x => a * (w : B0579.Plane → ℝ) x := by
    exact (UnforcedLeray.B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_smul a w)
  rw [cellVol_eq] at hmulCell
  have hmul : (fun x : B0579.Plane =>
      ((a • w : X c m) : B0579.Plane → ℝ) x) =ᵐ[(μq c).prod (volume : Measure ℝ)]
      fun x => a * (w : B0579.Plane → ℝ) x := hmulCell
  have hmulSwap := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := μq c)).quasiMeasurePreserving.ae_eq_comp hmul
  have hsections := Measure.ae_ae_of_ae_prod hmulSwap
  filter_upwards [hsections, haw.prod_left_ae, hw.prod_left_ae] with η hsec hawη hwη
  have hsec' : (fun q : ℝ => ((a • w : X c m) : B0579.Plane → ℝ) (q, η)) =ᵐ[μq c]
      fun q => a * (w : B0579.Plane → ℝ) (q, η) := by
    filter_upwards [hsec] with q hq
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using hq
  have hInt : (∫ q in UnforcedLeray.B0581.qInt c,
        ((a • w : X c m) : B0579.Plane → ℝ) (q, η)) =
      a * ∫ q in UnforcedLeray.B0581.qInt c, (w : B0579.Plane → ℝ) (q, η) := by
    calc
      _ = ∫ q in UnforcedLeray.B0581.qInt c,
          (a * (w : B0579.Plane → ℝ) (q, η)) := integral_congr_ae hsec'
      _ = _ := by simp only [integral_const_mul]
  change c⁻¹ * (∫ q in UnforcedLeray.B0581.qInt c,
      ((a • w : X c m) : B0579.Plane → ℝ) (q, η)) =
    a * (c⁻¹ * ∫ q in UnforcedLeray.B0581.qInt c, (w : B0579.Plane → ℝ) (q, η))
  rw [hInt]
  ring

/-- The Hardy primitive commutes with a scalar when its integrands agree almost everywhere. -/
theorem zeroModePrimitive_smul_of_ae {f g : ℝ → ℝ} (a : ℝ)
    (hEq : f =ᵐ[volume] fun η => a * g η) (η : ℝ) :
    UnforcedLeray.B0582.zeroModePrimitive f η =
      a * UnforcedLeray.B0582.zeroModePrimitive g η := by
  rw [UnforcedLeray.B0582.zeroModePrimitive, UnforcedLeray.B0582.zeroModePrimitive]
  have hEqη : f =ᵐ[volume.restrict (Set.Iic η)] (fun y => a * g y) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
    filter_upwards [hEq] with y hy hyI
    exact hy
  calc
    _ = ∫ y in Set.Iic η, a * g y := integral_congr_ae hEqη
    _ = _ := by simp only [integral_const_mul]

/-- The actual horizontal-mean primitive commutes with real scalar multiplication. -/
theorem omegaBarPrimitive_smul {c m : ℝ} (hm : 1 ≤ m)
    (a : ℝ) (w : X c m) (η : ℝ) :
    UnforcedLeray.B0582.zeroModePrimitive
        (omegaBar c ((a • w : X c m) : B0579.Plane → ℝ)) η =
      a * UnforcedLeray.B0582.zeroModePrimitive
        (omegaBar c (w : B0579.Plane → ℝ)) η := by
  apply zeroModePrimitive_smul_of_ae a
  exact omegaBar_smul_ae hm a w

/-- The actual zero-mode Biot--Savart column is real-linear on zero-circulation inputs. -/
theorem zeroVelLp_smul {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (a : ℝ) (w : X c m) (hw0 : ∫ x in B0579.cell c, w x = 0)
    (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    UnforcedLeray.B0583.zeroVelLp c hm (a • w) haw0 =
      a • UnforcedLeray.B0583.zeroVelLp c hm w hw0 := by
  apply Lp.ext
  filter_upwards [
    UnforcedLeray.B0583.coeFn_zeroVelLp c hm (a • w) haw0,
    UnforcedLeray.B0583.coeFn_zeroVelLp c hm w hw0,
    Lp.coeFn_smul a (UnforcedLeray.B0583.zeroVelLp c hm w hw0)] with x hscaled hw hsmul
  rw [hscaled, hsmul, Pi.smul_apply, hw]
  change UnforcedLeray.B0583.zeroVel c ((a • w : X c m) : B0579.Plane → ℝ) x =
    a • UnforcedLeray.B0583.zeroVel c (w : B0579.Plane → ℝ) x
  simp only [UnforcedLeray.B0583.zeroVel, UnforcedLeray.B0583.profField]
  rw [omegaBarPrimitive_smul hm a w x.2]
  ext i
  fin_cases i <;> simp [Complex.ofReal_mul, smul_eq_mul]

/-- The real B0583 velocity splits into its actual nonzero Fourier map and zero-mode primitive. -/
theorem realBiotSavart_eq_components {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w : X c m) (hw0 : ∫ x in B0579.cell c, w x = 0) :
    realBiotSavart hm w hw0 = nonzeroBiotSavartCLM hm w +
      realPartVelocityLp (UnforcedLeray.B0583.zeroVelLp c hm w hw0) := by
  change realPartVelocityLp (UnforcedLeray.B0583.velocity c hm w hw0) = _
  rw [UnforcedLeray.B0583.velocity]
  calc
    realPartVelocityLp
        (UnforcedLeray.B0581.velNe c
          (UnforcedLeray.B0581.nonzeroPart c
            (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w)) +
          UnforcedLeray.B0583.zeroVelLp c hm w hw0) =
        realPartVelocityLp (UnforcedLeray.B0581.velNe c
          (UnforcedLeray.B0581.nonzeroPart c
            (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w))) +
          realPartVelocityLp (UnforcedLeray.B0583.zeroVelLp c hm w hw0) := by
            change (realPartVelocityCLM.compLpL 2 (cellVol c)) _ = _
            exact (realPartVelocityCLM.compLpL 2 (cellVol c)).map_add _ _
    _ = nonzeroBiotSavartCLM hm w +
          realPartVelocityLp (UnforcedLeray.B0583.zeroVelLp c hm w hw0) := by
            rw [nonzeroBiotSavartCLM_apply]

/-- The actual real cylinder Biot--Savart reconstruction is additive on zero-circulation data. -/
theorem realBiotSavart_add {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w z : X c m) (hw0 : ∫ x in B0579.cell c, w x = 0)
    (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    realBiotSavart hm (w + z) hwz0 =
      realBiotSavart hm w hw0 + realBiotSavart hm z hz0 := by
  rw [realBiotSavart_eq_components hm (w + z) hwz0,
    realBiotSavart_eq_components hm w hw0,
    realBiotSavart_eq_components hm z hz0]
  have hN := (nonzeroBiotSavartCLM hm).map_add w z
  have hZ : realPartVelocityLp (UnforcedLeray.B0583.zeroVelLp c hm (w + z) hwz0) =
      realPartVelocityLp (UnforcedLeray.B0583.zeroVelLp c hm w hw0) +
        realPartVelocityLp (UnforcedLeray.B0583.zeroVelLp c hm z hz0) := by
    change (realPartVelocityCLM.compLpL 2 (cellVol c)) _ = _
    rw [zeroVelLp_add hm w z hw0 hz0 hwz0]
    exact (realPartVelocityCLM.compLpL 2 (cellVol c)).map_add _ _
  rw [hN, hZ]
  abel

/-- The actual real cylinder Biot--Savart reconstruction is homogeneous on zero-circulation data. -/
theorem realBiotSavart_smul {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (a : ℝ) (w : X c m) (hw0 : ∫ x in B0579.cell c, w x = 0)
    (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    realBiotSavart hm (a • w) haw0 = a • realBiotSavart hm w hw0 := by
  rw [realBiotSavart_eq_components hm (a • w) haw0,
    realBiotSavart_eq_components hm w hw0]
  have hN := (nonzeroBiotSavartCLM hm).map_smul a w
  have hZ : realPartVelocityLp (UnforcedLeray.B0583.zeroVelLp c hm (a • w) haw0) =
      a • realPartVelocityLp (UnforcedLeray.B0583.zeroVelLp c hm w hw0) := by
    change (realPartVelocityCLM.compLpL 2 (cellVol c)) _ = _
    rw [zeroVelLp_smul hm a w hw0 haw0]
    exact (realPartVelocityCLM.compLpL 2 (cellVol c)).map_smul a _
  rw [hN, hZ]
  rw [← smul_add]

/-- B0583's real-projected Biot--Savart map as a bounded real-linear map on the actual closed
zero-circulation subspace. Its global constant is explicit and is used only for fixed-cylinder
existence estimates; it is not a uniform localized-return estimate. -/
def realBiotSavartKernelCLM {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) :
    zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) →L[ℝ]
      Lp Vec 2 (cellVol c) := by
  let Z := zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)
  let L : Z →ₗ[ℝ] Lp Vec 2 (cellVol c) := {
    toFun := fun w => realBiotSavart hm w.1 ((mem_zeroCirculationSubmodule_iff
      (by linarith : 1 / 2 < m) w.1).1 w.2)
    map_add' := by
      intro w z
      exact realBiotSavart_add hm w.1 z.1
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) z.1).1 z.2)
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) (w + z).1).1
          (Z.add_mem w.2 z.2))
    map_smul' := by
      intro a w
      exact realBiotSavart_smul hm a w.1
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) (a • w).1).1
          (Z.smul_mem a w.2))
  }
  refine L.mkContinuous (c / (2 * Real.pi) + 2) ?_
  intro w
  have hcirc := (mem_zeroCirculationSubmodule_iff
    (by linarith : 1 / 2 < m) w.1).1 w.2
  calc
    ‖L w‖ = ‖realBiotSavart hm w.1 hcirc‖ := rfl
    _ ≤ ‖UnforcedLeray.B0583.velocity c hm w.1 hcirc‖ :=
      norm_realPartVelocityLp_le _
    _ ≤ (c / (2 * Real.pi) + 2) * ‖w.1‖ := by
      exact UnforcedLeray.B0583.norm_velocity_le c hm w.1 hcirc

/-- Operator norm of the actual real cylinder Biot--Savart CLM on `ker circulation`. -/
theorem norm_realBiotSavartKernelCLM_le {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)) :
    ‖realBiotSavartKernelCLM hm w‖ ≤ (c / (2 * Real.pi) + 2) * ‖w‖ := by
  change ‖realBiotSavart hm w.1
      ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)‖ ≤ _
  have hcirc := (mem_zeroCirculationSubmodule_iff
    (by linarith : 1 / 2 < m) w.1).1 w.2
  calc
    ‖realBiotSavart hm w.1 hcirc‖ ≤
        ‖UnforcedLeray.B0583.velocity c hm w.1 hcirc‖ := norm_realPartVelocityLp_le _
    _ ≤ (c / (2 * Real.pi) + 2) * ‖w.1‖ :=
      UnforcedLeray.B0583.norm_velocity_le c hm w.1 hcirc


#print axioms omegaBar_add_ae
#print axioms zeroModePrimitive_add_of_ae
#print axioms omegaBarPrimitive_add
#print axioms zeroVelLp_add
#print axioms omegaBar_smul_ae
#print axioms zeroModePrimitive_smul_of_ae
#print axioms omegaBarPrimitive_smul
#print axioms zeroVelLp_smul
#print axioms realBiotSavart_add
#print axioms realBiotSavart_smul
#print axioms realBiotSavartKernelCLM
#print axioms norm_realBiotSavartKernelCLM_le

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
