import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# Joint measurability of the heat-Leray derivatives (`PartIII-b:IIIb-D2/3/1/1/2/3/3`)

Source `the November 2 reference manuscript`
3604-3621.  On `t > 0`, `K_t(x) = t^{-3/2} K_1(x/√t)` (`HeatLerayScale`), so the `x`-derivative of
order `m` is `(t^{-3/2} (√t)^{-m}) · (D^m K_1)(x/√t)`, a continuous function of `(t, x)` on
`t > 0` times a measurable scalar.  The set `{t > 0}` is measurable, so the indicator is strongly
measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem heatLerayJointMeas_of (h : HeatLerayScale) (h2 : HeatLerayKSmooth) :
    HeatLerayJointMeas := by
  intro i j m hm
  have hK1 : ContDiff ℝ m (fun x => IIIa.heatLerayK 1 i j x) :=
    (h2 1 one_pos i j).of_le (by exact_mod_cast hm)
  -- continuity of the `m`-th derivative of `K_1`
  have hG : Continuous (fun y => iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK 1 i j x) y) :=
    ContDiff.continuous_iteratedFDeriv le_rfl hK1
  -- pointwise scaling identity for `t > 0`
  have hscal : ∀ t : ℝ, 0 < t → ∀ y : Space,
      iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK t i j x) y
        = (t ^ (-(3 / 2 : ℝ)) * ((Real.sqrt t)⁻¹) ^ m) •
          iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK 1 i j x) ((Real.sqrt t)⁻¹ • y) := by
    intro t ht y
    have hfun : (fun x => IIIa.heatLerayK t i j x)
        = fun x => t ^ (-(3 / 2 : ℝ)) * IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x) :=
      funext fun x => h t ht i j x
    rw [hfun]
    have hcomp : ContDiff ℝ m (fun x => IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x)) :=
      hK1.comp (contDiff_const_smul _)
    have key : iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x)) y
        = ((Real.sqrt t)⁻¹) ^ m • iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK 1 i j x)
            ((Real.sqrt t)⁻¹ • y) :=
      congrFun (iteratedFDeriv_comp_const_smul ((Real.sqrt t)⁻¹) hK1) y
    have hsc : (fun x => t ^ (-(3 / 2 : ℝ)) * IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x))
        = t ^ (-(3 / 2 : ℝ)) • (fun x => IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x)) := rfl
    rw [hsc, iteratedFDeriv_const_smul_apply hcomp.contDiffAt, key, smul_smul]
  -- measurability of the global candidate
  have hs : Measurable (fun q : ℝ × Space => (Real.sqrt q.1)⁻¹ • q.2) :=
    ((Real.continuous_sqrt.measurable.comp measurable_fst).inv).smul measurable_snd
  have hcomp2 : StronglyMeasurable
      (fun q : ℝ × Space => iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK 1 i j x)
        ((Real.sqrt q.1)⁻¹ • q.2)) :=
    hG.comp_stronglyMeasurable hs.stronglyMeasurable
  have hsc2 : StronglyMeasurable
      (fun q : ℝ × Space => q.1 ^ (-(3 / 2 : ℝ)) * ((Real.sqrt q.1)⁻¹) ^ m) :=
    ((measurable_fst.pow_const _).mul
      (((Real.continuous_sqrt.measurable.comp measurable_fst).inv).pow_const m)).stronglyMeasurable
  have hPsi : StronglyMeasurable
      (fun q : ℝ × Space => (q.1 ^ (-(3 / 2 : ℝ)) * ((Real.sqrt q.1)⁻¹) ^ m) •
        iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK 1 i j x) ((Real.sqrt q.1)⁻¹ • q.2)) :=
    hsc2.smul hcomp2
  have hS : MeasurableSet {q : ℝ × Space | 0 < q.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hF : (fun q : ℝ × Space =>
      if 0 < q.1 then iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK q.1 i j x) q.2 else 0)
      = {q : ℝ × Space | 0 < q.1}.indicator (fun q : ℝ × Space =>
          (q.1 ^ (-(3 / 2 : ℝ)) * ((Real.sqrt q.1)⁻¹) ^ m) •
            iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK 1 i j x) ((Real.sqrt q.1)⁻¹ • q.2)) := by
    funext q
    by_cases hq : 0 < q.1
    · have hmem : q ∈ {q : ℝ × Space | 0 < q.1} := hq
      rw [if_pos hq, Set.indicator_of_mem hmem, hscal q.1 hq q.2]
    · have hnmem : q ∉ {q : ℝ × Space | 0 < q.1} := hq
      rw [if_neg hq, Set.indicator_of_notMem hnmem]
  rw [hF]
  exact hPsi.indicator hS

end UnforcedLeray.Short.PartIIIb.Concrete
