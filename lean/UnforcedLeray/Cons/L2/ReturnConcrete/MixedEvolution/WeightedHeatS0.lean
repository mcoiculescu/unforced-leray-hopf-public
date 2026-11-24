import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualHeatSource
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelMoment
import UnforcedLeray.Units.B0296.Conv

/-!
# Weighted Gaussian heat family on the cylinder

This leaf develops the actual scalar heat operator needed for the `S₀` part of the physical
Volterra supplier. The Gaussian moment estimate here is a fixed-strip spatial bound; it does not
assert weighted strong continuity at zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open scoped NNReal ENNReal
open UnforcedLeray.B0284
open UnforcedLeray.B0296
open UnforcedLeray.B0579

/-- The axially weighted scalar heat-kernel moment density. -/
def axialHeatMomentDensity (θ m : ℝ) (w : Plane) : ℝ :=
  heatKernel2 θ w * axialWeight m w

theorem axialHeatMomentDensity_scale_le {r m : ℝ} (hr : 0 < r)
    (hr2 : r ^ 2 ≤ 1) (hm : 0 ≤ m) (w : Plane) :
    axialHeatMomentDensity (r ^ 2) m (r • w) ≤
      (r ^ 2)⁻¹ * axialHeatMomentDensity 1 m w := by
  have hgrad : heatKernel2 (r ^ 2) (r • w) = (r ^ 2)⁻¹ * heatKernel2 1 w := by
    rw [heatKernel2, heatKernel2]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [heatKernel_scale_sqr hr w.1, heatKernel_scale_sqr hr w.2]
    ring
  have hbase : 1 + (r * w.2) ^ 2 ≤ 1 + w.2 ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg w.2]
  have hweight : axialWeight m (r • w) ≤ axialWeight m w := by
    rw [axialWeight, axialBracket_rpow, Prod.smul_snd,
      axialWeight, axialBracket_rpow]
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hk : 0 ≤ heatKernel2 1 w := (heatKernel2_nonneg one_pos w)
  have hw : 0 ≤ axialWeight m (r • w) := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hscale : 0 ≤ (r ^ 2)⁻¹ := by positivity
  unfold axialHeatMomentDensity
  rw [hgrad]
  calc
    (r ^ 2)⁻¹ * heatKernel2 1 w * axialWeight m (r • w) =
        ((r ^ 2)⁻¹ * heatKernel2 1 w) * axialWeight m (r • w) := by ring
    _ ≤ ((r ^ 2)⁻¹ * heatKernel2 1 w) * axialWeight m w :=
      mul_le_mul_of_nonneg_left hweight (mul_nonneg hscale hk)
    _ = (r ^ 2)⁻¹ * (heatKernel2 1 w * axialWeight m w) := by ring

theorem integrable_axialHeatMomentDensity {θ m : ℝ} (hθ : 0 < θ)
    (hm : 0 ≤ m) : Integrable (axialHeatMomentDensity θ m) := by
  have hq : Integrable (UnforcedLeray.B0191.heatKernel 1 θ) :=
    UnforcedLeray.B0296.integrable_heatKernel1 hθ
  have hη : Integrable (fun x : ℝ => UnforcedLeray.B0191.heatKernel 1 θ x *
      (1 + x ^ 2) ^ (m / 2)) := integrable_heatKernel1_mul_axialWeight hθ hm
  have hprod : Integrable (fun w : Plane =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        (UnforcedLeray.B0191.heatKernel 1 θ w.2 * (1 + w.2 ^ 2) ^ (m / 2))) :=
    hq.mul_prod hη
  convert hprod using 1
  funext w
  simp [axialHeatMomentDensity, heatKernel2, axialWeight, axialBracket_rpow, mul_assoc]

theorem integral_axialHeatMomentDensity_le {θ m : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hm : 0 ≤ m) :
    ∫ w : Plane, axialHeatMomentDensity θ m w ≤
      ∫ w : Plane, axialHeatMomentDensity 1 m w := by
  let r := Real.sqrt θ
  have hr : 0 < r := by dsimp [r]; exact Real.sqrt_pos.2 hθ
  have hr2 : r ^ 2 = θ := by dsimp [r]; exact Real.sq_sqrt hθ.le
  have hr2le : r ^ 2 ≤ 1 := by rw [hr2]; exact hθ1
  have hθint : Integrable (axialHeatMomentDensity θ m) := integrable_axialHeatMomentDensity hθ hm
  have h1int : Integrable (axialHeatMomentDensity 1 m) :=
    integrable_axialHeatMomentDensity one_pos hm
  have hcomp : Integrable (fun w : Plane => axialHeatMomentDensity θ m (r • w)) := by
    exact (integrable_comp_smul_iff (volume : Measure Plane)
      (fun w : Plane => axialHeatMomentDensity θ m w) hr.ne').2 hθint
  have hmajor : Integrable (fun w : Plane => (r ^ 2)⁻¹ * axialHeatMomentDensity 1 m w) := by
    simpa [mul_comm] using h1int.const_mul ((r ^ 2)⁻¹)
  have hmono : ∫ w : Plane, axialHeatMomentDensity θ m (r • w) ≤
      ∫ w : Plane, (r ^ 2)⁻¹ * axialHeatMomentDensity 1 m w :=
    integral_mono hcomp hmajor (fun w => by
      simpa [hr2] using axialHeatMomentDensity_scale_le hr hr2le hm w)
  have hchange := MeasureTheory.Measure.integral_comp_smul (volume : Measure Plane)
    (fun w : Plane => axialHeatMomentDensity θ m w) r
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
  rw [hdim] at hchange
  have hchange' : ∫ w : Plane, axialHeatMomentDensity θ m (r • w) =
      (r ^ 2)⁻¹ * ∫ w : Plane, axialHeatMomentDensity θ m w := by
    simpa [abs_of_pos hr, smul_eq_mul, Real.rpow_neg hr.le, Real.rpow_natCast] using hchange
  have hsolve : ∫ w : Plane, axialHeatMomentDensity θ m w =
      r ^ 2 * ∫ w : Plane, axialHeatMomentDensity θ m (r • w) := by
    rw [hchange']
    field_simp
  calc
    ∫ w : Plane, axialHeatMomentDensity θ m w =
        r ^ 2 * ∫ w : Plane, axialHeatMomentDensity θ m (r • w) := hsolve
    _ ≤ r ^ 2 * ∫ w : Plane, (r ^ 2)⁻¹ * axialHeatMomentDensity 1 m w :=
      mul_le_mul_of_nonneg_left hmono (sq_nonneg r)
    _ = ∫ w : Plane, axialHeatMomentDensity 1 m w := by
      rw [integral_const_mul]
      field_simp

/-- ENNReal kernel for axial-weighted convolution with the actual scalar B0284 Gaussian. -/
def axialHeatKernel (m θ : ℝ) (w : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ (m / 2)) * ENNReal.ofReal (axialWeight m w) *
    ENNReal.ofReal (heatKernel2 θ w)

theorem axialHeatKernel_measurable (m θ : ℝ) : Measurable (axialHeatKernel m θ) := by
  unfold axialHeatKernel
  exact (measurable_const.mul ((continuous_axialWeight m).measurable.ennreal_ofReal)).mul
    (B0284.measurable_heatKernel2_right θ).ennreal_ofReal

theorem axialHeatKernel_ne_top (m θ : ℝ) (w : Plane) : axialHeatKernel m θ w ≠ ⊤ := by
  unfold axialHeatKernel
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

theorem axialHeatKernel_lintegral_le {θ m : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hm : 0 ≤ m) :
    ∫⁻ w : Plane, axialHeatKernel m θ w ≤
      ENNReal.ofReal (2 ^ (m / 2) * ∫ w : Plane, axialHeatMomentDensity 1 m w) := by
  let D := axialHeatMomentDensity θ m
  have hD : Integrable D := integrable_axialHeatMomentDensity hθ hm
  have hD₁ : Integrable (axialHeatMomentDensity 1 m) :=
    integrable_axialHeatMomentDensity one_pos hm
  have hD_nonneg : ∀ w, 0 ≤ D w := by
    intro w
    dsimp [D, axialHeatMomentDensity, axialWeight, axialBracket]
    exact mul_nonneg (heatKernel2_nonneg hθ w) (by positivity)
  have hD₁_nonneg : ∀ w, 0 ≤ axialHeatMomentDensity 1 m w := by
    intro w
    dsimp [axialHeatMomentDensity, axialWeight, axialBracket]
    exact mul_nonneg (heatKernel2_nonneg one_pos w) (by positivity)
  have hpoint : ∀ w, axialHeatKernel m θ w = ENNReal.ofReal ((2 : ℝ) ^ (m / 2) * D w) := by
    intro w
    have hW : 0 ≤ axialWeight m w := by
      dsimp [axialWeight, axialBracket]
      positivity
    have hC : 0 ≤ (2 : ℝ) ^ (m / 2) * axialWeight m w :=
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hW
    rw [axialHeatKernel, ← ENNReal.ofReal_mul (Real.rpow_nonneg
      (by norm_num : (0 : ℝ) ≤ 2) _), ← ENNReal.ofReal_mul hC]
    congr 1
    simp only [D, axialHeatMomentDensity, axialWeight, Real.norm_eq_abs]
    ring
  have hmass : ∫⁻ w : Plane, axialHeatKernel m θ w =
      ENNReal.ofReal ((2 : ℝ) ^ (m / 2) * ∫ w : Plane, D w) := by
    rw [show (fun w : Plane => axialHeatKernel m θ w) =
      (fun w => ENNReal.ofReal ((2 : ℝ) ^ (m / 2) * D w)) by
        funext w
        exact hpoint w]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hD.const_mul ((2 : ℝ) ^ (m / 2)))
      (Filter.Eventually.of_forall fun w =>
        mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (hD_nonneg w))]
    rw [integral_const_mul]
  have hmoment := integral_axialHeatMomentDensity_le hθ hθ1 hm
  rw [hmass]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left hmoment
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)

/-- Axial weighted Young estimate for the literal B0296 heat family on periodic planar fields. -/
theorem eLpNorm_axialHeat_le {c θ m : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hm : 0 ≤ m) {g : Plane → Plane} (hper : IsQPeriodic c g)
    (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (fun z => axialWeight m z • B0284.heat θ g z) p (B0284.cellMeasure c) ≤
      (∫⁻ w : Plane, axialHeatKernel m θ w) *
        eLpNorm (fun z => axialWeight m z • g z) p (B0284.cellMeasure c) := by
  have hweightedPer : IsQPeriodic c (fun z => axialWeight m z • g z) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • g (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket]]
    exact congrArg (fun v => axialWeight m z • v) (hper z)
  have hweightedMeas : AEStronglyMeasurable (fun z => axialWeight m z • g z) volume :=
    (continuous_axialWeight m).aestronglyMeasurable.smul hg
  have hkernelBound : ∀ w z x : Plane,
      ‖axialWeight m z • (heatKernel2 θ w • x)‖ₑ ≤
        axialHeatKernel m θ w * ‖axialWeight m (z - w) • x‖ₑ := by
    intro w z x
    have hpeetre := axialBracket_rpow_le_peetre hm z w
    have hwz : 0 ≤ axialWeight m z := by dsimp [axialWeight, axialBracket]; positivity
    have hwd : 0 ≤ axialWeight m (z - w) := by
      dsimp [axialWeight, axialBracket]
      positivity
    have hww : 0 ≤ axialWeight m w := by dsimp [axialWeight, axialBracket]; positivity
    have hk : 0 ≤ heatKernel2 θ w := heatKernel2_nonneg hθ w
    have hpeetreE : ENNReal.ofReal (axialWeight m z) ≤
        ENNReal.ofReal (2 ^ (m / 2)) * ENNReal.ofReal (axialWeight m (z - w)) *
          ENNReal.ofReal (axialWeight m w) := by
      calc
        ENNReal.ofReal (axialWeight m z) ≤
            ENNReal.ofReal (2 ^ (m / 2) * axialWeight m (z - w) * axialWeight m w) :=
          ENNReal.ofReal_le_ofReal (by simpa [axialWeight] using hpeetre)
        _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    have hleft : ‖axialWeight m z • (heatKernel2 θ w • x)‖ₑ =
        ENNReal.ofReal (axialWeight m z) *
          (ENNReal.ofReal (heatKernel2 θ w) * ‖x‖ₑ) := by
      rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hwz,
        enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hk]
    have hright : ‖axialWeight m (z - w) • x‖ₑ =
        ENNReal.ofReal (axialWeight m (z - w)) * ‖x‖ₑ := by
      rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hwd]
    calc
      ‖axialWeight m z • (heatKernel2 θ w • x)‖ₑ =
          ENNReal.ofReal (axialWeight m z) *
            (ENNReal.ofReal (heatKernel2 θ w) * ‖x‖ₑ) := hleft
      _ ≤ (ENNReal.ofReal (2 ^ (m / 2)) * ENNReal.ofReal (axialWeight m (z - w)) *
          ENNReal.ofReal (axialWeight m w)) *
          (ENNReal.ofReal (heatKernel2 θ w) * ‖x‖ₑ) :=
        mul_le_mul_of_nonneg_right hpeetreE (by positivity)
      _ = axialHeatKernel m θ w *
          (ENNReal.ofReal (axialWeight m (z - w)) * ‖x‖ₑ) := by
        unfold axialHeatKernel
        ring
      _ = axialHeatKernel m θ w *
          ‖axialWeight m (z - w) • x‖ₑ := by
        rw [← hright]
  have hpoint : ∀ z, ‖axialWeight m z • B0284.heat θ g z‖ₑ ≤
      ∫⁻ w : Plane, axialHeatKernel m θ w *
        ‖(fun x => axialWeight m x • g x) (z - w)‖ₑ := by
    intro z
    rw [B0296.heat_eq_integral hθ g]
    calc
      ‖axialWeight m z • ∫ w : Plane, heatKernel2 θ w • g (z - w)‖ₑ ≤
        ∫⁻ w : Plane, ‖axialWeight m z • (heatKernel2 θ w • g (z - w))‖ₑ := by
          rw [← integral_smul]
          exact enorm_integral_le_lintegral_enorm _
      _ ≤ _ := by
        refine lintegral_mono fun w => ?_
        simpa only [Pi.smul_apply] using hkernelBound w z (g (z - w))
  calc
    eLpNorm (fun z => axialWeight m z • B0284.heat θ g z) p (B0284.cellMeasure c) ≤
        eLpNorm (fun z => ∫⁻ w : Plane, axialHeatKernel m θ w *
          ‖(fun x => axialWeight m x • g x) (z - w)‖ₑ) p (B0284.cellMeasure c) :=
      eLpNorm_mono_enorm (fun z => hpoint z)
    _ ≤ (∫⁻ w : Plane, axialHeatKernel m θ w) *
        eLpNorm (fun z => axialWeight m z • g z) p (B0284.cellMeasure c) :=
      eLpNorm_kernelAbs_le' hc (axialHeatKernel_measurable m θ)
        (axialHeatKernel_ne_top m θ) hweightedPer hweightedMeas hp hp'

/-- Pointwise measurability of the actual heat convolution for a strongly measurable global
representative. -/
theorem measurable_heat_of_stronglyMeasurable {θ : ℝ} {g : Plane → Plane}
    (hg : StronglyMeasurable g) : Measurable (B0284.heat θ g) := by
  by_cases hθ : 0 < θ
  · have hshift : StronglyMeasurable (fun q : Plane × Plane => g (q.1 - q.2)) := by
      exact hg.comp_measurable (measurable_fst.sub measurable_snd)
    have hk : StronglyMeasurable (fun q : Plane × Plane =>
        heatKernel2 θ q.2 • g (q.1 - q.2)) := by
      exact ((B0284.measurable_heatKernel2_right θ).comp measurable_snd).stronglyMeasurable.smul
        hshift
    have hInt : Measurable (fun z : Plane =>
        ∫ w : Plane, heatKernel2 θ w • g (z - w)) := hk.integral_prod_right'.measurable
    have heq : B0284.heat θ g = fun z => ∫ w : Plane, heatKernel2 θ w • g (z - w) := by
      funext z
      exact B0284.heat_apply_of_pos hθ g z
    rw [heq]
    exact hInt
  · rw [B0284.heat_of_nonpos (not_lt.mp hθ)]
    exact hg.measurable

/-- Embed an actual real `X_m` column as the first component of a planar heat input. -/
def xColumnHeatLift {c m : ℝ} (hc : 0 < c) (f : X c m) : Plane → Plane :=
  fun z => (xColumnPeriodicRep hc f z, 0)

theorem periodic_xColumnHeatLift {c m : ℝ} (hc : 0 < c) (f : X c m) :
    B0284.IsQPeriodic c (xColumnHeatLift hc f) := by
  intro z
  simp only [xColumnHeatLift]
  rw [periodic_xColumnPeriodicRep hc f z]

theorem stronglyMeasurable_xColumnHeatLift {c m : ℝ} (hc : 0 < c) (f : X c m) :
    StronglyMeasurable (xColumnHeatLift hc f) := by
  exact ((stronglyMeasurable_xColumnPeriodicRep hc f).measurable.prodMk
    measurable_const).stronglyMeasurable

/-- The literal heat evolution of the chosen real periodic representative of an `X_m` column. -/
def xColumnHeatField {c m θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (f : X c m) : Plane → Plane :=
  B0284.heat θ (xColumnHeatLift hc f)

/-- Axial weighted `L²` membership for the actual Gaussian image of a weighted real column. -/
theorem memLp_xColumnHeatField_axial {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    MemLp (fun z => axialWeight m z • xColumnHeatField hc hθ f z) 2
      (B0284.cellMeasure c) := by
  let rep := xColumnPeriodicRep hc f
  let lift := xColumnHeatLift hc f
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  have hfRad : MemLp (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
      (volume.restrict (B0579.cell c)) :=
    (B0579.memLp_cellMeasure_iff c m).1 (Lp.memLp f)
  have hrepAE : rep =ᵐ[volume.restrict (B0579.cell c)] (f : Plane → ℝ) := by
    simpa only [hleft, rep] using xColumnPeriodicRep_ae_eq hc f
  have hfRadRep : MemLp (fun z => bracket z ^ m * rep z) 2
      (volume.restrict (B0579.cell c)) := by
    apply hfRad.congr_enorm
    · exact ((continuous_bracket_rpow m).aestronglyMeasurable.mul
        (stronglyMeasurable_xColumnPeriodicRep hc f).aestronglyMeasurable)
    · filter_upwards [hrepAE] with z hz
      simp [hz]
  have hLiftMeas : Measurable lift := by
    exact (stronglyMeasurable_xColumnPeriodicRep hc f).measurable.prodMk measurable_const
  have hAxialMeas : AEStronglyMeasurable (fun z => axialWeight m z • lift z)
      (Cyl.cellμ c) := by
    exact (continuous_axialWeight m).aestronglyMeasurable.smul
      (hLiftMeas.aestronglyMeasurable.mono_ac Measure.absolutelyContinuous_restrict)
  have hRadVec : MemLp (fun z => bracket z ^ m • lift z) 2 (Cyl.cellμ c) := by
    have hRadMeas : AEStronglyMeasurable (fun z => bracket z ^ m • lift z)
        (Cyl.cellμ c) := by
      exact (continuous_bracket_rpow m).aestronglyMeasurable.smul
        (hLiftMeas.aestronglyMeasurable.mono_ac Measure.absolutelyContinuous_restrict)
    have hRadRepCell : MemLp (fun z => bracket z ^ m * rep z) 2 (Cyl.cellμ c) := by
      simpa only [hleft] using hfRadRep
    refine hRadRepCell.of_le hRadMeas ?_
    filter_upwards [ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz
    have hz' : z ∈ B0579.cell c := by
      simp only [Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
      simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
      exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
    have hrad : 0 ≤ bracket z ^ m := (bracket_rpow_pos m z).le
    have hnormLift : ‖lift z‖ = ‖rep z‖ := by
      change ‖(rep z, (0 : ℝ))‖ = ‖rep z‖
      simp [Prod.norm_def]
    calc
      ‖bracket z ^ m • lift z‖ = bracket z ^ m * ‖rep z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrad, hnormLift]
      _ = bracket z ^ m * |rep z| := by rw [Real.norm_eq_abs]
      _ = |bracket z ^ m * rep z| := by
        rw [abs_mul, abs_of_nonneg hrad]
      _ = ‖bracket z ^ m * rep z‖ := by rw [← Real.norm_eq_abs]
      _ ≤ ‖bracket z ^ m * rep z‖ := le_rfl
  have hAxialCyl : MemLp (fun z => axialWeight m z • lift z) 2 (Cyl.cellμ c) := by
    have hbound : ∀ᵐ z ∂Cyl.cellμ c,
        ‖axialWeight m z • lift z‖ ≤ ‖bracket z ^ m • lift z‖ := by
      filter_upwards [ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz
      have hz' : z ∈ B0579.cell c := by
        simp only [Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
        simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
        exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
      have hweight := axialBracket_rpow_le_bracket (by linarith : 0 ≤ m) z
      have hax : 0 ≤ axialWeight m z := by dsimp [axialWeight, axialBracket]; positivity
      have hrad : 0 ≤ bracket z ^ m := (bracket_rpow_pos m z).le
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hax, abs_of_nonneg hrad]
      exact mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
    exact hRadVec.of_le hAxialMeas hbound
  have hAxialMeasB : Measurable (fun z => axialWeight m z • lift z) :=
    (continuous_axialWeight m).measurable.smul hLiftMeas
  have hAxialPer : B0284.IsQPeriodic (c := c) (fun z => axialWeight m z • lift z) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • lift (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket]]
    exact congrArg (fun v => axialWeight m z • v) (periodic_xColumnHeatLift hc f z)
  have hAxialNorm := HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc hAxialMeasB
    hAxialPer hAxialCyl
  have hheatMeas : AEStronglyMeasurable (B0284.heat θ lift) (B0284.cellMeasure c) :=
    B0296.aestronglyMeasurable_heat c θ
      (stronglyMeasurable_xColumnHeatLift hc f).aestronglyMeasurable
  have hheatAxialMeas : AEStronglyMeasurable
      (fun z => axialWeight m z • B0284.heat θ lift z) (B0284.cellMeasure c) :=
    (continuous_axialWeight m).aestronglyMeasurable.smul hheatMeas
  have hkernelTop : (∫⁻ w : Plane, axialHeatKernel m θ w) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact axialHeatKernel_lintegral_le hθ hθ1 (by linarith : 0 ≤ m)
  have hheatBound := eLpNorm_axialHeat_le hc hθ (by linarith : 0 ≤ m)
    (periodic_xColumnHeatLift hc f) (stronglyMeasurable_xColumnHeatLift hc f).aestronglyMeasurable
    (p := 2) (by norm_num) (by norm_num) 
  refine ⟨hheatAxialMeas, ?_⟩
  apply lt_top_iff_ne_top.mpr
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hkernelTop hAxialNorm.eLpNorm_ne_top)
  exact hheatBound

/-- Fixed-cylinder radial weighted membership of the actual first heat component. This is the
axial Gaussian estimate transferred back to the B0579 radial weight on the centered cell. -/
theorem memLp_xColumnHeatField_radial_cyl {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    MemLp (fun z => bracket z ^ m * (xColumnHeatField hc hθ f z).1) 2 (Cyl.cellμ c) := by
  let g := xColumnHeatField hc hθ f
  let Cc : ℝ := (1 + c ^ 2 / 4) ^ (m / 2)
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hgmeas : Measurable g := by
    exact measurable_heat_of_stronglyMeasurable
      (stronglyMeasurable_xColumnHeatLift hc f)
  have hgper : B0284.IsQPeriodic c g :=
    B0284.heat_periodic (periodic_xColumnHeatLift hc f)
  have haxial := memLp_xColumnHeatField_axial hc hm hθ hθ1 f
  have haxial' : MemLp (fun z => axialWeight m z • g z) 2
      (B0284.cellMeasure c) := by
    simpa [g, xColumnHeatField] using haxial
  have hweightedMeas : Measurable (fun z => axialWeight m z • g z) :=
    (continuous_axialWeight m).measurable.smul hgmeas
  have haxialCyl : MemLp (fun z => axialWeight m z • g z) 2 (Cyl.cellμ c) :=
    HeatCylinder.memLp_cyl_of_memLp_cellMeasure hc hweightedMeas
      (by
        intro z
        change axialWeight m (z.1 + c, z.2) • g (z.1 + c, z.2) = _
        rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
          simp [axialWeight, axialBracket], hgper z]) haxial'
  have hradMeas : AEStronglyMeasurable
      (fun z => bracket z ^ m * (g z).1) (Cyl.cellμ c) := by
    exact (continuous_bracket_rpow m).aestronglyMeasurable.mul
      ((hgmeas.fst).aestronglyMeasurable.mono_ac Measure.absolutelyContinuous_restrict)
  refine (haxialCyl.const_smul Cc).of_le hradMeas ?_
  filter_upwards [ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz
  have hz' : z ∈ B0579.cell c := by
    simp only [Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
    simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
    exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
  have hweight := bracket_le_centered_axial hc (by linarith : 0 ≤ m) hz'
  have hax : 0 ≤ axialWeight m z := by dsimp [axialWeight, axialBracket]; positivity
  have hrad : 0 ≤ bracket z ^ m := (bracket_rpow_pos m z).le
  have hreal : |bracket z ^ m * (g z).1| ≤ Cc * ‖axialWeight m z • g z‖ := by
    rw [abs_mul, abs_of_nonneg hrad]
    calc
      bracket z ^ m * |(g z).1| ≤ Cc * axialWeight m z * |(g z).1| :=
        mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
      _ ≤ Cc * ‖axialWeight m z • g z‖ := by
        calc
          Cc * axialWeight m z * |(g z).1| =
              Cc * (axialWeight m z * |(g z).1|) := by ring
          _ ≤ Cc * (axialWeight m z * ‖g z‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (norm_fst_le (g z)) hax) hCc
          _ = Cc * ‖axialWeight m z • g z‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hax]
  change ‖bracket z ^ m * (g z).1‖ ≤ ‖Cc • (axialWeight m z • g z)‖
  calc
    ‖bracket z ^ m * (g z).1‖ = |bracket z ^ m * (g z).1| := Real.norm_eq_abs _
    _ ≤ Cc * ‖axialWeight m z • g z‖ := hreal
    _ = ‖Cc • (axialWeight m z • g z)‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hCc, abs_of_nonneg hax]

/-- The actual first component of the positive-age Gaussian image belongs to the radial weighted
`X_m` measure on the centered cylinder. -/
theorem memLp_xColumnHeatField_first_X {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    MemLp (fun z => (xColumnHeatField hc hθ f z).1) 2 (B0579.cellMeasure c m) := by
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  have hrad := memLp_xColumnHeatField_radial_cyl hc hm hθ hθ1 f
  have hrad' : MemLp (fun z => bracket z ^ m * (xColumnHeatField hc hθ f z).1) 2
      (volume.restrict (B0579.cell c)) := by
    simpa only [hleft] using hrad
  exact (B0579.memLp_cellMeasure_iff c m).2 hrad'

/-- The positive-age, physically normalized first-coordinate heat image as a genuine `X c m`
element, built from the actual periodic representative and B0284 Gaussian convolution. -/
def xColumnHeatS0Positive {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) : X c m :=
  (memLp_xColumnHeatField_first_X hc hm hθ hθ1 f).toLp
    (fun z => (xColumnHeatField hc hθ f z).1)

theorem coeFn_xColumnHeatS0Positive {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) =ᵐ[cellMeasure c m]
      fun z => (B0284.heat θ (xColumnHeatLift hc f) z).1 := by
  exact (memLp_xColumnHeatField_first_X hc hm hθ hθ1 f).coeFn_toLp

#print axioms axialHeatMomentDensity_scale_le
#print axioms integrable_axialHeatMomentDensity
#print axioms integral_axialHeatMomentDensity_le
#print axioms axialHeatKernel_lintegral_le
#print axioms eLpNorm_axialHeat_le
#print axioms memLp_xColumnHeatField_axial
#print axioms memLp_xColumnHeatField_radial_cyl
#print axioms memLp_xColumnHeatField_first_X

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
