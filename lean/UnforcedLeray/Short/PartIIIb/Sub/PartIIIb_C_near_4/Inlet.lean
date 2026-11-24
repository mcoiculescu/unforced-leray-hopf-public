import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_4
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge

/-!
# `PartIII-b:C/near/4/1`: the chart coefficients of the inlet columns are measurable

Source of record: `the November 2 reference manuscript` lines 2347-2358, 5282-5295.
The inlet column is `p.inlet i = Nv p.R (p.inletProfile i)` with
`inletProfile i = ringStreamProfile p.R (p.cutStream i)`.

The argument is: `ringStreamProfile R φ m` depends on `φ m` (a value) and on the first
derivatives of `φ` at `m`, and every first derivative `m ↦ fderiv ℝ φ m v` is measurable for any
`φ` (`measurable_fderiv_apply_const`). So the inlet profile is measurable once the cut stream
`cutStream i = χ(s) · frozenStream i` is measurable. The cut stream is measurable because
`frozenStream i = ±2 Re/Im` of `periodicStream p.mode p.c`, and this periodization is measurable
for every planar profile by the leaves of `PartIII-a:T23/9/2` (`measurable_periodicStream`), with
no hypothesis on `p.mode`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIIa UnforcedLeray.Axi

/-- The chart coefficient vanishes for `s ≤ 0` (inlet version). -/
theorem chartCoeff_zero_of_le_inlet (R : ℝ)
    (V : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {pt : ℝ × (ℝ × ℝ)} (h : pt.1 ≤ 0) : chartCoeff R V pt = 0 := by
  unfold chartCoeff
  rw [Real.sqrt_eq_zero'.2 h, inv_zero, zero_smul]

/-- The normalized components of a ring profile are measurable when the value and the
first derivatives are: the value enters only through `φ m`. -/
theorem measurable_ringStreamProfile_of {R : ℝ} {φ : ℝ × (ℝ × ℝ) → ℝ}
    (hφ : Measurable φ) :
    Measurable (fun m : ℝ × (ℝ × ℝ) => ringStreamProfile R φ m) := by
  have hE : Measurable (fun m : ℝ × (ℝ × ℝ) => dEta φ m) :=
    measurable_fderiv_apply_const ℝ φ ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
  have hQ : Measurable (fun m : ℝ × (ℝ × ℝ) => dQ φ m) :=
    measurable_fderiv_apply_const ℝ φ ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
  have hS : Measurable (fun m : ℝ × (ℝ × ℝ) => dS φ m) :=
    measurable_fderiv_apply_const ℝ φ ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
  have hm1 : Measurable (fun m : ℝ × (ℝ × ℝ) => m.1) := measurable_fst
  have hm2 : Measurable (fun m : ℝ × (ℝ × ℝ) => m.2.2) := measurable_snd.comp measurable_snd
  have hA : Measurable (fun m : ℝ × (ℝ × ℝ) =>
      (-(dEta φ m)) • m0) :=
    hE.neg.smul_const m0
  have hB : Measurable (fun m : ℝ × (ℝ × ℝ) =>
      (dQ φ m + R⁻¹ * (φ m - 2 * m.1 * dS φ m - m.2.2 * dEta φ m)) • m1) := by
    refine Measurable.smul_const ?_ m1
    exact hQ.add (measurable_const.mul
      ((hφ.sub ((measurable_const.mul hm1).mul hS)).sub (hm2.mul hE)))
  unfold ringStreamProfile
  exact hA.add hB

/-- **`PartIII-b:C/near/4/1`: the inlet chart coefficients are measurable** (source 2347-2358). -/
theorem inletChartMeasurable : InletChartMeasurable := by
  classical
  intro p i
  have hg : UnforcedLeray.Short.IIIa.T23_9_Sub.GreenInverseMeasurable :=
    UnforcedLeray.Short.IIIa.T23_9_Sub.greenInverse_measurable_of
      UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_primitive_zero
      UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_integral_Ioi
  have hz : UnforcedLeray.Short.IIIa.T23_9_Sub.ZTsumMeasurable :=
    fun F hF => UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_ztsum F hF
  have hP : Measurable (fun x : ℝ × ℝ => UnforcedLeray.Blueprint.periodicStream p.mode p.c x) :=
    UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_periodicStream hg hz p.mode p.c
  have hF : Measurable (p.frozenStream i) := by
    fin_cases i
    · exact (Complex.measurable_re.comp hP).const_mul 2
    · exact (Complex.measurable_im.comp hP).const_mul (-2)
  have hC : Measurable (p.cutStream i) :=
    ((contDiff_ageCutoff p.H (n := 0)).continuous.measurable.comp measurable_fst).mul
      (hF.comp measurable_snd)
  have hprof : Measurable (p.inletProfile i) := by
    unfold Params.inletProfile
    exact measurable_ringStreamProfile_of hC
  have hU : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (isOpen_Ioi.prod isOpen_univ).measurableSet
  have heq : chartCoeff p.R (p.inlet i) = (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))).piecewise
      (p.inletProfile i) (fun _ => (0 : EuclideanSpace ℝ (Fin 2))) := by
    funext pt
    by_cases h : pt ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact chartCoeff_Nv p.R_pos (p.inletProfile i) (mem_prod.1 h).1
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]
      apply chartCoeff_zero_of_le_inlet
      by_contra hc
      exact h (mk_mem_prod (not_le.1 hc) (mem_univ _))
  rw [heq]
  exact Measurable.piecewise hU hprof measurable_const

end UnforcedLeray.Short.PartIIIb.NearInst
