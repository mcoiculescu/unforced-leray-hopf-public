import UnforcedLeray.Units.B0284.Defs
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# B0284: heat contraction on the cylinder

Unit B0284 (`background:eq:2.24`, tex lines 5247–5250). The manuscript's bounds for the flat
inverse use that `e^{θΔ}` is a contraction of the normalized spatial `L^p` space
(tex lines 4967–4968: "Heat evolution ... is contractive on normalized spatial `L^p`";
tex line 5021: "heat contraction"). This file proves it for the definition of
`UnforcedLeray.B0284.heat`:

* `lintegral_cell_sub`: the cell integral of a `q`-periodic function is invariant under
  every translation of the plane (`ℝ/cℤ`-periodicity in `q`, translation invariance in `η`);
* `eLpNorm_heatAbs_le`, `eLpNorm_heat_le`: `‖e^{θΔ} g‖_{L^p(dq/c dη)} ≤ ‖g‖_{L^p(dq/c dη)}`
  for every periodic, almost everywhere strongly measurable `g` and `1 ≤ p < ∞`.

`heatAbs θ g z = ∫ G_θ(w) |g(z-w)| dw` is the absolute heat integral (a `[0,∞]`-valued lower
integral, so it has no junk value); `‖heat θ g z‖ₑ ≤ heatAbs θ g z` for `θ > 0`.

Minkowski's integral inequality is the vendored, compiled
`NonUniqueEuler.Conv.eLpNorm_lintegral_le` (`lean/NonUniqueEuler/P/Infra/ConvMinkowski/
Minkowski.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal

namespace UnforcedLeray.B0284

open UnforcedLeray.GaussianVortex (Plane)

/-! ## Measure-theoretic facts about the cell -/

theorem cellMeasure_ac (c : ℝ) : cellMeasure c ≪ volume :=
  (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _

instance (c : ℝ) : SigmaFinite (cellMeasure c) := by
  unfold cellMeasure; infer_instance

theorem volume_restrict_cell (c : ℝ) :
    volume.restrict (cell c) = (volume.restrict (Ioc (0:ℝ) c)).prod (volume : Measure ℝ) := by
  rw [cell, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- A `q`-periodic function on `ℝ`: the cell integral is invariant under translation. No
measurability is needed (the integral is the lower integral on `ℝ/cℤ`). -/
theorem lintegral_Ioc_sub_of_periodic {c : ℝ} (hc : 0 < c) {H : ℝ → ℝ≥0∞}
    (hH : Function.Periodic H c) (a : ℝ) :
    ∫⁻ q in Ioc 0 c, H (q - a) = ∫⁻ q in Ioc 0 c, H q := by
  have : Fact (0 < c) := ⟨hc⟩
  set Hh : AddCircle c → ℝ≥0∞ := hH.lift with hHh
  have h1 : ∀ q : ℝ, H (q - a) = (fun y : AddCircle c => Hh (y - (a : AddCircle c))) q := by
    intro q
    simp only [hHh]
    rw [← AddCircle.coe_sub, Function.Periodic.lift_coe]
  have h2 : ∀ q : ℝ, H q = Hh q := fun q => by simp [hHh]
  simp_rw [h1]
  conv_rhs => rw [show (fun q => H q) = fun q : ℝ => Hh q from funext h2]
  have e1 := AddCircle.lintegral_preimage c 0 (fun y : AddCircle c => Hh (y - (a : AddCircle c)))
  have e2 := AddCircle.lintegral_preimage c 0 Hh
  rw [zero_add] at e1 e2
  rw [e1, e2]
  exact lintegral_sub_right_eq_self Hh (a : AddCircle c)

/-- The integral of a `q`-periodic, almost everywhere measurable function over one cell is
invariant under every translation of the plane. -/
theorem lintegral_cell_sub {c : ℝ} (hc : 0 < c) {h : Plane → ℝ≥0∞} (hper : IsQPeriodic c h)
    (hmeas : AEMeasurable h volume) (w : Plane) :
    ∫⁻ z in cell c, h (z - w) = ∫⁻ z in cell c, h z := by
  have hmeas' : AEMeasurable (fun z => h (z - w)) volume :=
    hmeas.comp_quasiMeasurePreserving (measurePreserving_sub_right volume w).quasiMeasurePreserving
  rw [volume_restrict_cell] at *
  have hA : AEMeasurable h ((volume.restrict (Ioc (0:ℝ) c)).prod (volume : Measure ℝ)) := by
    rw [← volume_restrict_cell]; exact hmeas.restrict
  have hB : AEMeasurable (fun z => h (z - w))
      ((volume.restrict (Ioc (0:ℝ) c)).prod (volume : Measure ℝ)) := by
    rw [← volume_restrict_cell]; exact hmeas'.restrict
  rw [lintegral_prod _ hB, lintegral_prod _ hA]
  set H : ℝ → ℝ≥0∞ := fun q => ∫⁻ η, h (q, η) with hHdef
  have hHper : Function.Periodic H c := by
    intro q
    simp only [hHdef]
    congr 1
    funext η
    exact hper (q, η)
  have hin : ∀ q : ℝ, ∫⁻ η, h ((q, η) - w) = H (q - w.1) := by
    intro q
    simp only [hHdef]
    have : (fun η : ℝ => h ((q, η) - w)) = fun η => (fun y => h (q - w.1, y)) (η - w.2) := by
      funext η
      rfl
    rw [this, lintegral_sub_right_eq_self (fun y => h (q - w.1, y)) w.2]
  simp_rw [hin]
  exact lintegral_Ioc_sub_of_periodic hc hHper w.1

/-- Translation invariance for the normalized cell measure. -/
theorem lintegral_cellMeasure_sub {c : ℝ} (hc : 0 < c) {h : Plane → ℝ≥0∞}
    (hper : IsQPeriodic c h) (hmeas : AEMeasurable h volume) (w : Plane) :
    ∫⁻ z, h (z - w) ∂(cellMeasure c) = ∫⁻ z, h z ∂(cellMeasure c) := by
  rw [cellMeasure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_cell_sub hc hper hmeas w]

/-- Translation invariance of the normalized spatial `L^p` norm of a periodic field. -/
theorem eLpNorm_cellMeasure_sub {E : Type*} [NormedAddCommGroup E] {c : ℝ} (hc : 0 < c)
    {g : Plane → E} (hper : IsQPeriodic c g) (hg : AEStronglyMeasurable g volume)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) (w : Plane) :
    eLpNorm (fun z => g (z - w)) p (cellMeasure c) = eLpNorm g p (cellMeasure c) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  congr 1
  refine lintegral_cellMeasure_sub hc (h := fun z => ‖g z‖ₑ ^ p.toReal) ?_ ?_ w
  · intro z
    simp only
    rw [hper z]
  · exact hg.enorm.pow_const _

/-- `‖a · f‖_{L^p} = a ‖f‖_{L^p}` for `[0,∞]`-valued `f` and finite `a`; no measurability is
needed. -/
theorem eLpNorm_const_mul_ennreal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a : ℝ≥0∞} (ha : a ≠ ⊤) (f : α → ℝ≥0∞) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) :
    eLpNorm (fun x => a * f x) p μ = a * eLpNorm f p μ := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  simp only [enorm_eq_self, ENNReal.mul_rpow_of_nonneg _ _ hpr.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpr.le ha),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hpr.ne', ENNReal.rpow_one]

/-! ## The heat kernel as a probability density -/

theorem measurable_heatKernel2 : Measurable fun q : ℝ × Plane => heatKernel2 q.1 q.2 := by
  unfold heatKernel2 B0191.heatKernel
  fun_prop

theorem measurable_heatKernel2_right (θ : ℝ) : Measurable (heatKernel2 θ) :=
  measurable_heatKernel2.comp (measurable_const.prodMk measurable_id)

theorem integrable_heatKernel2 {θ : ℝ} (hθ : 0 < θ) : Integrable (heatKernel2 θ) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_heatKernel2 hθ]
  exact one_ne_zero

/-- The planar heat kernel has unit mass, as a lower integral. -/
theorem lintegral_heatKernel2 {θ : ℝ} (hθ : 0 < θ) :
    ∫⁻ w : Plane, ENNReal.ofReal (heatKernel2 θ w) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel2 hθ)
    (Eventually.of_forall fun w => heatKernel2_nonneg hθ w), integral_heatKernel2 hθ,
    ENNReal.ofReal_one]

/-! ## Heat contraction -/

/-- The absolute heat integral `∫ G_θ(w) |g(z-w)| dw ∈ [0,∞]`. -/
def heatAbs (θ : ℝ) (g : Plane → Plane) (z : Plane) : ℝ≥0∞ :=
  ∫⁻ w : Plane, ENNReal.ofReal (heatKernel2 θ w) * ‖g (z - w)‖ₑ

theorem enorm_heat_le {θ : ℝ} (hθ : 0 < θ) (g : Plane → Plane) (z : Plane) :
    ‖heat θ g z‖ₑ ≤ heatAbs θ g z := by
  rw [heat_apply_of_pos hθ]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun w => ?_
  rw [enorm_smul, Real.enorm_of_nonneg (heatKernel2_nonneg hθ w)]

/-- `heatAbs θ g` only depends on the almost-everywhere class of `g`. -/
theorem heatAbs_congr_ae {θ : ℝ} {g g' : Plane → Plane} (h : g =ᵐ[volume] g') :
    heatAbs θ g = heatAbs θ g' := by
  funext z
  refine lintegral_congr_ae ?_
  have h' := (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure Plane) z).ae h
  filter_upwards [h'] with w hw
  rw [hw]

/-- **Heat contraction** (absolute form): for `θ > 0`, `1 ≤ p < ∞` and a periodic, almost
everywhere strongly measurable field `g`,
`‖∫ G_θ(w) |g(·-w)| dw‖_{L^p(dq/c dη)} ≤ ‖g‖_{L^p(dq/c dη)}`. -/
theorem eLpNorm_heatAbs_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {g : Plane → Plane}
    (hper : IsQPeriodic c g) (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) :
    eLpNorm (heatAbs θ g) p (cellMeasure c) ≤ eLpNorm g p (cellMeasure c) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  set Fz : Plane → Plane → ℝ≥0∞ :=
    fun z w => ENNReal.ofReal (heatKernel2 θ w) * ‖g (z - w)‖ₑ with hFz
  have hK : Measurable fun w => ENNReal.ofReal (heatKernel2 θ w) :=
    ENNReal.measurable_ofReal.comp (measurable_heatKernel2_right θ)
  have hsub : AEStronglyMeasurable (fun q : Plane × Plane => g (q.1 - q.2))
      ((volume : Measure Plane).prod volume) :=
    hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure Plane) volume)
  have hF : AEMeasurable (Function.uncurry Fz) ((cellMeasure c).prod volume) := by
    have h1 : AEMeasurable (fun q : Plane × Plane => ‖g (q.1 - q.2)‖ₑ)
        ((cellMeasure c).prod volume) :=
      (hsub.enorm).mono_ac ((cellMeasure_ac c).prod Measure.AbsolutelyContinuous.rfl)
    exact (hK.comp measurable_snd).aemeasurable.mul h1
  calc eLpNorm (heatAbs θ g) p (cellMeasure c)
      = eLpNorm (fun z => ∫⁻ w, Fz z w) p (cellMeasure c) := rfl
    _ ≤ ∫⁻ w, eLpNorm (fun z => Fz z w) p (cellMeasure c) :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hF hp hp'
    _ = ∫⁻ w, ENNReal.ofReal (heatKernel2 θ w) * eLpNorm g p (cellMeasure c) := by
        refine lintegral_congr fun w => ?_
        rw [hFz]
        simp only
        rw [eLpNorm_const_mul_ennreal ENNReal.ofReal_ne_top _ hp0 hp', eLpNorm_enorm,
          eLpNorm_cellMeasure_sub hc hper hg hp0 hp' w]
    _ = eLpNorm g p (cellMeasure c) := by
        rw [lintegral_mul_const _ hK, lintegral_heatKernel2 hθ, one_mul]

/-- **Heat contraction**: `‖e^{θΔ} g‖_{L^p(dq/c dη)} ≤ ‖g‖_{L^p(dq/c dη)}` for every `θ`,
`1 ≤ p < ∞` and periodic, almost everywhere strongly measurable `g` (tex lines 4967–4968,
5021). -/
theorem eLpNorm_heat_le {c θ : ℝ} (hc : 0 < c) {g : Plane → Plane}
    (hper : IsQPeriodic c g) (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) :
    eLpNorm (heat θ g) p (cellMeasure c) ≤ eLpNorm g p (cellMeasure c) := by
  by_cases hθ : 0 < θ
  · refine le_trans ?_ (eLpNorm_heatAbs_le hc hθ hper hg hp hp')
    exact eLpNorm_mono_enorm fun z => (enorm_heat_le hθ g z).trans_eq (enorm_eq_self _).symm
  · rw [heat_of_nonpos (not_lt.mp hθ)]

end UnforcedLeray.B0284
