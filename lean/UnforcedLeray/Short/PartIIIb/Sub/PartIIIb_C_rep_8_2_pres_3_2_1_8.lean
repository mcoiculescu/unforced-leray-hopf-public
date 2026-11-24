import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

/-!
# `rbExt` (`PartIII-b:C/rep/8/2/pres/3/2/1/8`)

Source of record: `the November 2 reference manuscript`
2541-2561 (all spatial orders and time derivatives; `U` jointly smooth through the axis),
1219 (`U_raw` smooth through the axis), 2550 (the inlet cutoff vanishes near the axis),
2697-2713 (compact-age inlet), 4139-4141 (`div U = 0`), 1211-1214 (`U_raw` exactly solenoidal),
2570-2575 (the inlet is solenoidal).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

private theorem divergence_add {F G : Space → Space} {y : Space}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    Axi.divergence (fun z => F z + G z) y = Axi.divergence F y + Axi.divergence G y := by
  unfold Axi.divergence
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (fderiv ℝ (F + G) y (coordinateVector i)) i = _
  rw [fderiv_add hF hG]
  rfl

private theorem divergence_sub {F G : Space → Space} {y : Space}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    Axi.divergence (fun z => F z - G z) y = Axi.divergence F y - Axi.divergence G y := by
  unfold Axi.divergence
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (fderiv ℝ (F - G) y (coordinateVector i)) i = _
  rw [fderiv_sub hF hG]
  rfl

private theorem divergence_const_smul (c : ℝ) {F : Space → Space} {y : Space}
    (hF : DifferentiableAt ℝ F y) :
    Axi.divergence (fun z => c • F z) y = c * Axi.divergence F y := by
  unfold Axi.divergence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (fderiv ℝ (c • F) y (coordinateVector i)) i = _
  rw [fderiv_const_smul hF]
  rfl

private theorem divergence_linear (U R I0 I1 : Space → Space) (c0 c1 : ℝ) {y : Space}
    (hU : DifferentiableAt ℝ U y) (hR : DifferentiableAt ℝ R y)
    (hI0 : DifferentiableAt ℝ I0 y) (hI1 : DifferentiableAt ℝ I1 y) :
    Axi.divergence (fun w => U w - (R w + (c0 • I0 w + c1 • I1 w))) y =
      Axi.divergence U y -
        (Axi.divergence R y + (c0 * Axi.divergence I0 y + c1 * Axi.divergence I1 y)) := by
  have h1 : DifferentiableAt ℝ (fun w => c0 • I0 w) y := hI0.const_smul c0
  have h2 : DifferentiableAt ℝ (fun w => c1 • I1 w) y := hI1.const_smul c1
  have h3 : DifferentiableAt ℝ (fun w => c0 • I0 w + c1 • I1 w) y := h1.add h2
  have h4 : DifferentiableAt ℝ (fun w => R w + (c0 • I0 w + c1 • I1 w)) y := hR.add h3
  rw [divergence_sub hU h4, divergence_add hR h3, divergence_add h1 h2,
    divergence_const_smul c0 hI0, divergence_const_smul c1 hI1]

private theorem pf2_contDiff_slice (X : ℝ → Space → Space)
    (hX : ContDiff ℝ ∞ (fun x : ℝ × Space => X x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ∞ (X τ) :=
  hX.comp (contDiff_const.prodMk contDiff_id)

private theorem pf2_contDiff1_slice (X : ℝ → Space → Space)
    (hX : ContDiff ℝ ∞ (fun x : ℝ × Space => X x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ 1 (X τ) :=
  (pf2_contDiff_slice X hX τ).of_le (by simp)

private theorem pf2_differentiableAt_slice (X : ℝ → Space → Space)
    (hX : ContDiff ℝ ∞ (fun x : ℝ × Space => X x.1 x.2)) (τ : ℝ) (y : Space) :
    DifferentiableAt ℝ (X τ) y :=
  (pf2_contDiff_slice X hX τ).differentiable (by simp) y

private theorem rbExtAt_params (p : UnforcedLeray.Cons.C03.Concrete.Params)
    (V rb U : ℝ → Space → Space) (pres : ℝ → Space → ℝ)
    {lam : ℂ} {q : UnforcedLeray.Blueprint.Planar.Profile}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q)
    (hmode : p.mode = q)
    {d dm dp : ℝ} (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp)
    (hraw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    (hν1 : p.ν ≤ 1)
    {P : ℝ} (hprof : IsExactProfile p.ν P U pres)
    (hU_def : ∀ τ y, U τ y = V τ y + rb τ y)
    {ρ : ℝ} (hball : IsBallSplit p ρ V rb) :
    ∃ X : ℝ → Space → Space, ContDiff ℝ ∞ (fun q : ℝ × Space => X q.1 q.2) ∧
      (∀ τ (y : Space), ∑ j : Fin 3, physPd (X τ) j y j = 0) ∧
      ∀ τ (y : Space), y ∉ axis → X τ y = rb τ y := by
  have hin0 : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet 0 x.1 x.2) :=
    inlet_contDiff hq hreg hν1 hmode 0
  have hin1 : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet 1 x.1 x.2) :=
    inlet_contDiff hq hreg hν1 hmode 1
  obtain ⟨z, _, hV, _, _⟩ := hball
  have hV_eq : (fun x : ℝ × Space => V x.1 x.2) =
      fun x : ℝ × Space => p.raw x.1 x.2 +
        (p.coord z 0 • p.inlet 0 x.1 x.2 + p.coord z 1 • p.inlet 1 x.1 x.2) := by
    funext x
    rw [hV x.1 x.2, Fin.sum_univ_two]
  have hV_sm : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2) := by
    rw [hV_eq]
    exact hraw.add ((hin0.const_smul (p.coord z 0)).add (hin1.const_smul (p.coord z 1)))
  have hrb_eq : (fun x : ℝ × Space => rb x.1 x.2) =
      fun x : ℝ × Space => U x.1 x.2 - V x.1 x.2 := by
    funext x
    rw [hU_def x.1 x.2]
    abel
  have hU_sm : ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2) := hprof.smoothU
  refine ⟨rb, ?_, ?_, fun _ _ _ => rfl⟩
  · rw [hrb_eq]
    exact hU_sm.sub hV_sm
  · intro τ y
    have hraw_div : Axi.divergence (p.raw τ) y = 0 :=
      divergence_zero_of_offAxis (pf2_contDiff1_slice p.raw hraw τ)
        (fun w hw => raw_div_offAxis hreg τ hw) y
    have hin0_div : Axi.divergence (p.inlet 0 τ) y = 0 :=
      divergence_zero_of_offAxis (pf2_contDiff1_slice (p.inlet 0) hin0 τ)
        (fun w hw => inlet_div_offAxis hq hreg hν1 hmode 0 τ hw) y
    have hin1_div : Axi.divergence (p.inlet 1 τ) y = 0 :=
      divergence_zero_of_offAxis (pf2_contDiff1_slice (p.inlet 1) hin1 τ)
        (fun w hw => inlet_div_offAxis hq hreg hν1 hmode 1 τ hw) y
    have hU_div : Axi.divergence (U τ) y = 0 := hprof.div_free τ y
    have hU_diff : DifferentiableAt ℝ (U τ) y := pf2_differentiableAt_slice U hU_sm τ y
    have hraw_diff : DifferentiableAt ℝ (p.raw τ) y := pf2_differentiableAt_slice p.raw hraw τ y
    have hin0_diff : DifferentiableAt ℝ (p.inlet 0 τ) y :=
      pf2_differentiableAt_slice (p.inlet 0) hin0 τ y
    have hin1_diff : DifferentiableAt ℝ (p.inlet 1 τ) y :=
      pf2_differentiableAt_slice (p.inlet 1) hin1 τ y
    have hrb_sl : rb τ = fun w => U τ w -
        (p.raw τ w + (p.coord z 0 • p.inlet 0 τ w + p.coord z 1 • p.inlet 1 τ w)) := by
      funext w
      rw [hU_def τ w, hV τ w, Fin.sum_univ_two]
      abel
    change Axi.divergence (rb τ) y = 0
    rw [hrb_sl,
      divergence_linear (U τ) (p.raw τ) (p.inlet 0 τ) (p.inlet 1 τ) (p.coord z 0) (p.coord z 1)
        hU_diff hraw_diff hin0_diff hin1_diff,
      hU_div, hraw_div, hin0_div, hin1_div]
    ring

/-- **`rbExt`**: along the sequence, the repair `r_b = U - V` is jointly `C^∞` on `ℝ × ℝ³` and has
pointwise vanishing divergence (source 2541-2561, 1219, 2550, 2697-2713, 4139-4141, 1211-1214,
2570-2575). -/
theorem rbExt (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.RbExt := by
  obtain ⟨ν₀, hν₀, hraw_sm⟩ := rawJointSmooth dm dp hst.dm_pos
  have hmin : 0 < min ν₀ 1 := lt_min hν₀ one_pos
  filter_upwards [hst.actual, D.pf2_eventually_regime hst hmin] with n hact ⟨hν_lt, _⟩
  have hν0 : ((D.level n).params D.Pl).ν ≤ ν₀ := (hν_lt.trans_le (min_le_left _ _)).le
  have hν1 : ((D.level n).params D.Pl).ν ≤ 1 := (hν_lt.trans_le (min_le_right _ _)).le
  exact rbExtAt_params ((D.level n).params D.Pl) (D.V n) (D.rb n) (D.level n).U (D.pres n)
    hst.planar.eigenpair rfl hact.regime
    (hraw_sm ((D.level n).params D.Pl) _ hact.regime hν0)
    hν1 hact.profile (fun _ _ => rfl) hact.ball

end UnforcedLeray.Short.PartIIIb.Concrete
