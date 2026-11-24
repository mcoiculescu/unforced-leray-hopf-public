import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub1
import UnforcedLeray.Units.B0223.Semigroup
import UnforcedLeray.Lib.HeatR3.ConvOp
import UnforcedLeray.Lib.Gaussian.Kernel
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound

/-!
# `kf1 : KF1` (source 3613-3615, the free semigroup)

Source of record: `the November 2 reference manuscript`
(lines 3613-3615). The formula is `B0223.Sop_rep` (`Units/B0223/Semigroup.lean:119`) rewritten
through the dilation `z ↦ (e^{t/2} z.1, z.2)` (quasi-measure-preserving by `B0223.map_dil`) and the
heat kernel identifications `gaussKernel 3 = Heat.kernel = heatG`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Coordinate `i` of a Bochner integral in `SpaceC` is the integral of the coordinates. -/
theorem kf1_proj_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (i : Fin 3) (φ : α → UnforcedLeray.B0223.SpaceC) (hφ : Integrable φ μ) :
    (∫ y, φ y ∂μ) i = ∫ y, φ y i ∂μ :=
  (ContinuousLinearMap.integral_comp_comm
    (EuclideanSpace.proj i : UnforcedLeray.B0223.SpaceC →L[ℂ] ℂ) hφ).symm

/-- Coordinate `i` of a real scalar multiple. -/
theorem kf1_smul_apply (c : ℝ) (v : UnforcedLeray.B0223.SpaceC) (i : Fin 3) :
    (c • v) i = ((c : ℝ) : ℂ) * v i := by
  rw [PiLp.smul_apply, Complex.real_smul]

/-- **KF1** (3613-3615): the free semigroup formula, for `νε² > 0` and `t > 0`. -/
theorem kf1 : KF1 := by
  unfold KF1
  intro ν ε P hP F t hh ht
  have hθ : 0 < ν * ε ^ 2 * (Real.exp t - 1) :=
    mul_pos hh (by linarith [Real.add_one_lt_exp ht.ne'])
  have hg : MemLp (fun w : UnforcedLeray.B0223.PSpace P =>
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (w.1, w.2 - (t : AddCircle P)))
      2 volume := by
    have h := (Lp.memLp F).comp_measurePreserving (UnforcedLeray.B0223.mp_shiftT (P := P) t)
    have e : (fun w : UnforcedLeray.B0223.PSpace P =>
        (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (w.1, w.2 - (t : AddCircle P)))
        = ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) ∘
            UnforcedLeray.B0223.shiftT P t) := by
      funext w
      simp [UnforcedLeray.B0223.shiftT_apply]
    rw [e]
    exact h
  have hI := UnforcedLeray.Heat.ae_integrable_heatIntegrand (UnforcedLeray.B0223.ιx P)
    (UnforcedLeray.B0223.continuous_ιx (P := P)).measurable hθ one_le_two hg
  have hq : Measure.QuasiMeasurePreserving
      (fun z : UnforcedLeray.B0223.PSpace P => (Real.exp (t / 2) • z.1, z.2)) volume volume :=
    ⟨(measurable_fst.const_smul (Real.exp (t / 2))).prodMk measurable_snd, by
      rw [UnforcedLeray.B0223.map_dil (P := P) (Real.exp_pos _)]
      exact Measure.smul_absolutelyContinuous⟩
  have hae := hq.ae hI
  filter_upwards [UnforcedLeray.B0223.Sop_rep hh ht F, hae] with w h1 h2
  intro i
  rw [h1, kf1_smul_apply]
  congr 1
  rw [UnforcedLeray.Heat.heatConv, kf1_proj_integral i _ h2]
  congr 1
  funext y
  have hk : UnforcedLeray.Gaussian.gaussKernel 3 (ν * ε ^ 2 * (Real.exp t - 1)) y =
      UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y := by
    rw [UnforcedLeray.Gaussian.gaussKernel_three_eq,
      UnforcedLeray.Short.IIIa.heatG_eq_heatKernel]
  have harg : (Real.exp (t / 2) • w.1, w.2) - UnforcedLeray.B0223.ιx P y =
      (Real.exp (t / 2) • w.1 - y, w.2) := by
    ext <;> simp [UnforcedLeray.B0223.ιx_apply]
  rw [kf1_smul_apply, hk, harg]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
