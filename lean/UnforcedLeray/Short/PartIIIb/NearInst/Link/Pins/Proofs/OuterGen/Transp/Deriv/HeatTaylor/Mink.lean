import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2_4_13

/-!
# Minkowski step `ODHT_Mink` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/13`)

Source `the November 2 reference manuscript`
lines 3346-3352 and 1339-1362.

Proof route: with `G s z = heatConv (ιx P) s w z` and `‖G s‖_{L²} ≤ ‖w‖_{L²}` for `s > 0`
(`Heat.eLpNorm_heatConv_le`), Minkowski's integral inequality
(`PlanarBS.Conv.eLpNorm_integral_le`) applied first to the inner `s`-integral over `(0, t]` and then
to the outer `t`-integral over `(0, θ]` gives `‖∫_0^θ∫_0^t G‖_{L²} ≤ ∫_0^θ t‖w‖ dt = θ²/2 ‖w‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.B0223 (PSpace SpaceC ιx)

/-- Joint measurability of `(s, z) ↦ heatConv (ιx P) s w z` for measurable `w`. -/
theorem mink_joint (P : ℝ) [Fact (0 < P)] (w : PSpace P → SpaceC) (hw : Measurable w) :
    Measurable (fun q : ℝ × PSpace P => UnforcedLeray.Heat.heatConv (ιx P) q.1 w q.2) := by
  have hk : Measurable (fun p : (ℝ × PSpace P) × UnforcedLeray.Gaussian.Euc 3 =>
      UnforcedLeray.Gaussian.gaussKernel 3 p.1.1 p.2) := by
    unfold UnforcedLeray.Gaussian.gaussKernel
    fun_prop
  have hF : StronglyMeasurable (Function.uncurry
      fun (q : ℝ × PSpace P) (y : UnforcedLeray.Gaussian.Euc 3) =>
        UnforcedLeray.Gaussian.gaussKernel 3 q.1 y •
          w (q.2 - ιx P y)) :=
    (hk.smul (hw.comp ((measurable_snd.comp measurable_fst).sub
      (UnforcedLeray.B0223.continuous_ιx.measurable.comp measurable_snd)))).stronglyMeasurable
  exact hF.integral_prod_right.measurable

set_option maxHeartbeats 1000000 in
/-- Joint measurability of `(p, t) ↦ ∫ s in (0, t], heatConv (ιx P) s w p.1`. -/
theorem mink_inner_meas (P : ℝ) [Fact (0 < P)] (w : PSpace P → SpaceC) (hw : Measurable w) :
    Measurable (fun p : PSpace P × ℝ => ∫ s in Ioc (0 : ℝ) p.2,
      UnforcedLeray.Heat.heatConv (ιx P) s w p.1) := by
  have hG := mink_joint P w hw
  have h1 : Measurable (fun x : (PSpace P × ℝ) × ℝ => (x.2, x.1.1)) :=
    measurable_snd.prodMk (measurable_fst.comp measurable_fst)
  have hfm0 := hG.comp h1
  have hfm : Measurable (fun x : (PSpace P × ℝ) × ℝ =>
      UnforcedLeray.Heat.heatConv (ιx P) x.2 w x.1.1) := hfm0
  have hS : MeasurableSet {x : (PSpace P × ℝ) × ℝ | x.2 ∈ Ioc (0 : ℝ) x.1.2} := by
    have h1 : MeasurableSet {x : (PSpace P × ℝ) × ℝ | (0 : ℝ) < x.2} :=
      measurableSet_lt measurable_const measurable_snd
    have h2 : MeasurableSet {x : (PSpace P × ℝ) × ℝ | x.2 ≤ x.1.2} :=
      measurableSet_le measurable_snd (measurable_snd.comp measurable_fst)
    have : {x : (PSpace P × ℝ) × ℝ | x.2 ∈ Ioc (0 : ℝ) x.1.2}
        = {x : (PSpace P × ℝ) × ℝ | (0 : ℝ) < x.2} ∩ {x : (PSpace P × ℝ) × ℝ | x.2 ≤ x.1.2} := by
      ext x
      simp [Set.mem_Ioc]
    rw [this]
    exact h1.inter h2
  have hsm : StronglyMeasurable (fun x : (PSpace P × ℝ) × ℝ =>
      Set.indicator {x : (PSpace P × ℝ) × ℝ | x.2 ∈ Ioc (0 : ℝ) x.1.2}
        (fun x : (PSpace P × ℝ) × ℝ =>
          UnforcedLeray.Heat.heatConv (ιx P) x.2 w x.1.1) x) :=
    (hfm.indicator hS).stronglyMeasurable
  have hint := (hsm.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have hfun : (fun p : PSpace P × ℝ => ∫ s in Ioc (0 : ℝ) p.2,
      UnforcedLeray.Heat.heatConv (ιx P) s w p.1)
      = fun p => ∫ s, Set.indicator {x : (PSpace P × ℝ) × ℝ | x.2 ∈ Ioc (0 : ℝ) x.1.2}
        (fun x : (PSpace P × ℝ) × ℝ =>
          UnforcedLeray.Heat.heatConv (ιx P) x.2 w x.1.1) (p, s) := by
    funext p
    have hpt : ∀ s : ℝ, (Ioc (0 : ℝ) p.2).indicator
        (fun s => UnforcedLeray.Heat.heatConv (ιx P) s w p.1) s
        = Set.indicator {x : (PSpace P × ℝ) × ℝ | x.2 ∈ Ioc (0 : ℝ) x.1.2}
          (fun x : (PSpace P × ℝ) × ℝ =>
            UnforcedLeray.Heat.heatConv (ιx P) x.2 w x.1.1) (p, s) := by
      intro s
      by_cases h : s ∈ Ioc (0 : ℝ) p.2
      · have h' : (p, s) ∈ {x : (PSpace P × ℝ) × ℝ | x.2 ∈ Ioc (0 : ℝ) x.1.2} := h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      · have h' : (p, s) ∉ {x : (PSpace P × ℝ) × ℝ | x.2 ∈ Ioc (0 : ℝ) x.1.2} := h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    rw [← integral_indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := p.2))]
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [hfun]
  exact hint

/-- Inner Minkowski bound: `‖∫_0^t G_s ds‖_{L²} ≤ t ‖w‖_{L²}` for `t ≥ 0`. -/
theorem mink_inner_bound (P : ℝ) [Fact (0 < P)] (w : PSpace P → SpaceC) (hw : Measurable w)
    (t : ℝ) (ht : 0 ≤ t) :
    eLpNorm (fun z => ∫ s in Ioc (0 : ℝ) t, UnforcedLeray.Heat.heatConv (ιx P) s w z) 2
        (volume : Measure (PSpace P))
      ≤ ENNReal.ofReal t * eLpNorm w 2 (volume : Measure (PSpace P)) := by
  have hG := mink_joint P w hw
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (z : PSpace P) (s : ℝ) =>
        UnforcedLeray.Heat.heatConv (ιx P) s w z)
      ((volume : Measure (PSpace P)).prod (volume.restrict (Ioc (0 : ℝ) t))) :=
    (hG.comp measurable_swap).aestronglyMeasurable
  calc eLpNorm (fun z => ∫ s in Ioc (0 : ℝ) t, UnforcedLeray.Heat.heatConv (ιx P) s w z) 2
        (volume : Measure (PSpace P))
      ≤ ∫⁻ s in Ioc (0 : ℝ) t,
          eLpNorm (fun z => UnforcedLeray.Heat.heatConv (ιx P) s w z) 2
            (volume : Measure (PSpace P)) :=
        UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le hmeas (by norm_num) (by simp)
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) t, eLpNorm w 2 (volume : Measure (PSpace P)) := by
        refine setLIntegral_mono' measurableSet_Ioc (fun s hs => ?_)
        exact UnforcedLeray.Heat.eLpNorm_heatConv_le (ιx P) UnforcedLeray.B0223.continuous_ιx.measurable
          hs.1 hw.aestronglyMeasurable (by norm_num)
    _ = ENNReal.ofReal t * eLpNorm w 2 (volume : Measure (PSpace P)) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]

/-- Outer Minkowski bound: `‖∫_0^θ∫_0^t G_s ds dt‖_{L²} ≤ (θ²/2) ‖w‖_{L²}`. -/
theorem mink_outer_bound (P : ℝ) [Fact (0 < P)] (θ : ℝ) (hθ : 0 < θ)
    (w : PSpace P → SpaceC) (hw : Measurable w) :
    eLpNorm (fun z => ∫ t in (0 : ℝ)..θ, ∫ s in (0 : ℝ)..t,
        UnforcedLeray.Heat.heatConv (ιx P) s w z) 2 (volume : Measure (PSpace P))
      ≤ ENNReal.ofReal (θ ^ 2 / 2) * eLpNorm w 2 (volume : Measure (PSpace P)) := by
  have hfun : (fun z => ∫ t in (0 : ℝ)..θ, ∫ s in (0 : ℝ)..t,
        UnforcedLeray.Heat.heatConv (ιx P) s w z)
      = fun z => ∫ t in Ioc (0 : ℝ) θ, ∫ s in Ioc (0 : ℝ) t,
          UnforcedLeray.Heat.heatConv (ιx P) s w z := by
    funext z
    rw [intervalIntegral.integral_of_le hθ.le]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [intervalIntegral.integral_of_le ht.1.le]
  rw [hfun]
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (z : PSpace P) (t : ℝ) =>
        ∫ s in Ioc (0 : ℝ) t, UnforcedLeray.Heat.heatConv (ιx P) s w z)
      ((volume : Measure (PSpace P)).prod (volume.restrict (Ioc (0 : ℝ) θ))) :=
    (mink_inner_meas P w hw).aestronglyMeasurable
  have hint : ∫⁻ t in Ioc (0 : ℝ) θ, ENNReal.ofReal t = ENNReal.ofReal (θ ^ 2 / 2) := by
    have hi : MeasureTheory.IntegrableOn (fun t : ℝ => t) (Ioc (0 : ℝ) θ) :=
      (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioc (0 : ℝ) θ)] fun t : ℝ => t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact ht.1.le
    rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le hθ.le, integral_id]
    ring
  calc eLpNorm (fun z => ∫ t in Ioc (0 : ℝ) θ, ∫ s in Ioc (0 : ℝ) t,
          UnforcedLeray.Heat.heatConv (ιx P) s w z) 2 (volume : Measure (PSpace P))
      ≤ ∫⁻ t in Ioc (0 : ℝ) θ, eLpNorm (fun z => ∫ s in Ioc (0 : ℝ) t,
          UnforcedLeray.Heat.heatConv (ιx P) s w z) 2 (volume : Measure (PSpace P)) :=
        UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le hmeas (by norm_num) (by simp)
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) θ, ENNReal.ofReal t * eLpNorm w 2 (volume : Measure (PSpace P)) := by
        refine setLIntegral_mono' measurableSet_Ioc (fun t ht => ?_)
        exact mink_inner_bound P w hw t ht.1.le
    _ = (∫⁻ t in Ioc (0 : ℝ) θ, ENNReal.ofReal t) * eLpNorm w 2 (volume : Measure (PSpace P)) :=
        lintegral_mul_const _ ENNReal.measurable_ofReal
    _ = ENNReal.ofReal (θ ^ 2 / 2) * eLpNorm w 2 (volume : Measure (PSpace P)) := by
        rw [hint]

/-- **Minkowski step** (source 3346-3352). -/
theorem odhtMink : ODHT_Mink := by
  intro P _ θ hθ W R w hw hWw hR
  have hb := mink_outer_bound P θ hθ w hw
  have hN : eLpNorm w 2 (volume : Measure (PSpace P))
      = eLpNorm (W : PSpace P → SpaceC) 2 (volume : Measure (PSpace P)) :=
    eLpNorm_congr_ae hWw.symm
  rw [hN] at hb
  have hWfin : eLpNorm (W : PSpace P → SpaceC) 2 (volume : Measure (PSpace P)) < ⊤ :=
    (Lp.memLp W).eLpNorm_lt_top
  have hle : eLpNorm (R : PSpace P → SpaceC) 2 (volume : Measure (PSpace P))
      ≤ ENNReal.ofReal (θ ^ 2 / 2) * eLpNorm (W : PSpace P → SpaceC) 2 (volume : Measure (PSpace P)) := by
    rw [eLpNorm_congr_ae hR]
    exact hb
  have hfin : ENNReal.ofReal (θ ^ 2 / 2) * eLpNorm (W : PSpace P → SpaceC) 2
      (volume : Measure (PSpace P)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWfin.ne
  rw [Lp.norm_def, Lp.norm_def]
  calc (eLpNorm (R : PSpace P → SpaceC) 2 (volume : Measure (PSpace P))).toReal
      ≤ (ENNReal.ofReal (θ ^ 2 / 2) * eLpNorm (W : PSpace P → SpaceC) 2
          (volume : Measure (PSpace P))).toReal := ENNReal.toReal_mono hfin hle
    _ = θ ^ 2 / 2 * (eLpNorm (W : PSpace P → SpaceC) 2 (volume : Measure (PSpace P))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end UnforcedLeray.Short.PartIIIb.NearInst
