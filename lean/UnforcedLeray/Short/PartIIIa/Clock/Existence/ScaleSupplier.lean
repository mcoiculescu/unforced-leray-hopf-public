import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip

/-!
# Part III-a, `PartIII-a:T21/3/3`: time rescaling of the weighted heat supplier

Source of record: `the November 2 reference manuscript`, lines 2823-2830.
Given the physical unit supplier `H0` (`ScaledHeatWeak hm 1 H0`) and `0 < ν ≤ 1`, the
supplier `H` with `S₀ t = H0.S₀ (ν t)` and `S t = H0.S (ν t)` satisfies `ScaledHeatWeak hm ν H`.
The conjunct (a) is the substitution `r ↦ ν r` in the viscous time integral; conjunct (b) is the
substitution in the Duhamel integral applied to the flux path `u ↦ ν⁻¹ • F (u/ν)` on `[νa, νb]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

namespace ScaleAux

variable {c m : ℝ} [Fact (0 < c)]

/-- Change of variables `u = ν r` on an interval, for a vector-valued integrand. -/
theorem scale_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) {ν : ℝ}
    (a t : ℝ) (hν : 0 < ν) :
    ∫ r in ν * a..ν * t, g r = ν • ∫ r in a..t, g (ν * r) := by
  rw [intervalIntegral.integral_comp_mul_left (f := g) hν.ne', smul_smul,
    mul_inv_cancel₀ hν.ne', one_smul]

/-- Change of variables from `[0, νt]` to `[0, t]`, real-valued. -/
theorem scale_int0 (g : ℝ → ℝ) {ν : ℝ} (t : ℝ) (hν : 0 < ν) :
    ∫ r in (0 : ℝ)..(ν * t), g r = ν * ∫ r in (0 : ℝ)..t, g (ν * r) := by
  have h := scale_int g (ν := ν) 0 t hν
  rw [mul_zero, smul_eq_mul] at h
  exact h

theorem mapsTo_scale_Icc {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    MapsTo (fun t : ℝ => ν * t) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
  fun t ht => ⟨mul_nonneg hν0.le ht.1, by nlinarith [ht.1, ht.2]⟩

theorem mapsTo_scale_Ioc {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    MapsTo (fun t : ℝ => ν * t) (Ioc (0 : ℝ) 1) (Ioc (0 : ℝ) 1) :=
  fun t ht => ⟨mul_pos hν0 ht.1, by nlinarith [ht.1, ht.2]⟩

theorem nu_add_le {ν a b : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) : ν * a + ν * b ≤ 1 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hν1) ha, mul_nonneg (sub_nonneg.2 hν1) hb]

/-- The rescaled weighted heat supplier `S₀^ν(t) = S₀(νt)`, `S^ν(t) = S(νt)`. -/
def scaleHeat (hm : 1 ≤ m) (H0 : WeightedHeatStripSupplier (c := c) (m := m) hm) (ν : ℝ)
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) : WeightedHeatStripSupplier (c := c) (m := m) hm where
  S₀ t := H0.S₀ (ν * t)
  S t := H0.S (ν * t)
  M₀ := H0.M₀
  C₀ := H0.C₀ * ν ^ (-(1 / 2 : ℝ))
  S₀_zero := by
    show H0.S₀ (ν * 0) = _
    rw [mul_zero]
    exact H0.S₀_zero
  norm_S₀_le t ht0 ht1 := H0.norm_S₀_le (ν * t) (mul_nonneg hν0.le ht0) (by nlinarith)
  norm_S_le t ht0 ht1 := by
    have h := H0.norm_S_le (ν * t) (mul_pos hν0 ht0) (by nlinarith)
    rw [Real.mul_rpow hν0.le ht0.le] at h
    show ‖H0.S (ν * t)‖ ≤ H0.C₀ * ν ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ))
    rw [mul_assoc]
    exact h
  continuousOn_S₀ x :=
    ContinuousOn.comp (H0.continuousOn_S₀ x)
      (by fun_prop : Continuous fun t : ℝ => ν * t).continuousOn (mapsTo_scale_Icc hν0 hν1)
  continuousOn_S y :=
    ContinuousOn.comp (H0.continuousOn_S y)
      (by fun_prop : Continuous fun t : ℝ => ν * t).continuousOn (mapsTo_scale_Ioc hν0 hν1)
  S₀_comp_S₀ a b ha hb hab := by
    show (H0.S₀ (ν * a)).comp (H0.S₀ (ν * b)) = H0.S₀ (ν * (a + b))
    rw [H0.S₀_comp_S₀ (ν * a) (ν * b) (mul_nonneg hν0.le ha) (mul_nonneg hν0.le hb)
      (nu_add_le hν0 hν1 ha hb hab), mul_add]
  S₀_comp_S a b ha hb hab := by
    show (H0.S₀ (ν * a)).comp (H0.S (ν * b)) = H0.S (ν * (a + b))
    rw [H0.S₀_comp_S (ν * a) (ν * b) (mul_nonneg hν0.le ha) (mul_pos hν0 hb)
      (nu_add_le hν0 hν1 ha hb.le hab), mul_add]

theorem scaleHeat_S₀ (hm : 1 ≤ m) (H0 : WeightedHeatStripSupplier (c := c) (m := m) hm)
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (t : ℝ) :
    (scaleHeat hm H0 ν hν0 hν1).S₀ t = H0.S₀ (ν * t) := rfl

theorem scaleHeat_S (hm : 1 ≤ m) (H0 : WeightedHeatStripSupplier (c := c) (m := m) hm)
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (t : ℝ) :
    (scaleHeat hm H0 ν hν0 hν1).S t = H0.S (ν * t) := rfl

/-- The rescaled flux path `u ↦ ν⁻¹ • F (u / ν)`. -/
def scaleFlux (ν : ℝ) (F : ℝ → ActualFlux (c := c) (m := m)) : ℝ → ActualFlux (c := c) (m := m) :=
  fun u => ν⁻¹ • F (u / ν)

theorem scaleFlux_apply {ν : ℝ} (hν0 : 0 < ν) (F : ℝ → ActualFlux (c := c) (m := m)) (s : ℝ) :
    scaleFlux ν F (ν * s) = ν⁻¹ • F s := by
  simp only [scaleFlux, mul_div_cancel_left₀ _ hν0.ne']

theorem scaleFlux_continuousOn {ν a b : ℝ} (hν0 : 0 < ν) (F : ℝ → ActualFlux (c := c) (m := m))
    (hF : ContinuousOn F (Icc a b)) :
    ContinuousOn (scaleFlux ν F) (Icc (ν * a) (ν * b)) := by
  have hmap : MapsTo (fun u : ℝ => u / ν) (Icc (ν * a) (ν * b)) (Icc a b) := by
    intro u hu
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hν0]
      linarith [hu.1, mul_comm a ν]
    · rw [div_le_iff₀ hν0]
      linarith [hu.2, mul_comm b ν]
  exact ContinuousOn.const_smul
    (ContinuousOn.comp hF ((continuousOn_id).div_const ν) hmap) ν⁻¹

/-- Element-level change of variables for the Duhamel integral. -/
theorem elem_scale (hm : 1 ≤ m) (H0 : WeightedHeatStripSupplier (c := c) (m := m) hm)
    {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (F : ℝ → ActualFlux (c := c) (m := m)) (a t : ℝ) :
    ∫ s in ν * a..ν * t, H0.S (ν * t - s) (scaleFlux ν F s) =
      ∫ s in a..t, H0.S (ν * (t - s)) (F s) := by
  have hpt : ∀ s : ℝ, H0.S (ν * t - ν * s) (scaleFlux ν F (ν * s)) =
      ν⁻¹ • H0.S (ν * (t - s)) (F s) := by
    intro s
    rw [scaleFlux_apply hν0 F s, map_smul, ← mul_sub]
  rw [scale_int (fun s => H0.S (ν * t - s) (scaleFlux ν F s)) a t hν0]
  simp only [hpt]
  rw [intervalIntegral.integral_smul, smul_smul, mul_inv_cancel₀ hν0.ne', one_smul]

/-- Pointwise flux scaling inside the cell integral. -/
theorem fluxFn_smul_int (k : ℝ) (F : ActualFlux (c := c) (m := m)) (ψ0 ψ1 : ℝ × ℝ → ℝ) :
    ∫ x in UnforcedLeray.B0579.cell c,
        (fluxFn (k • F) 0 x * ψ0 x + fluxFn (k • F) 1 x * ψ1 x) =
      k * ∫ x in UnforcedLeray.B0579.cell c, (fluxFn F 0 x * ψ0 x + fluxFn F 1 x * ψ1 x) := by
  have hae : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      fluxFn (k • F) i x = k * fluxFn F i x := by
    intro i
    apply (UnforcedLeray.B0579.ac_cellMeasure c m).ae_le
    filter_upwards [MeasureTheory.Lp.coeFn_smul k (F i)] with x hx
    simp only [fluxFn, Pi.smul_apply]
    rw [hx]
    simp [smul_eq_mul]
  calc ∫ x in UnforcedLeray.B0579.cell c,
          (fluxFn (k • F) 0 x * ψ0 x + fluxFn (k • F) 1 x * ψ1 x)
      = ∫ x in UnforcedLeray.B0579.cell c, k * (fluxFn F 0 x * ψ0 x + fluxFn F 1 x * ψ1 x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hae 0, hae 1] with x h0 h1
        rw [h0, h1]
        ring
    _ = k * ∫ x in UnforcedLeray.B0579.cell c, (fluxFn F 0 x * ψ0 x + fluxFn F 1 x * ψ1 x) :=
        MeasureTheory.integral_const_mul k _

/-- **Mild/weak transfer: conjunct (a) and (b) of `ScaledHeatWeak`** for the rescaled supplier. -/
theorem scaledHeatWeak_scale (hm : 1 ≤ m) (H0 : WeightedHeatStripSupplier (c := c) (m := m) hm)
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (h0 : ScaledHeatWeak hm 1 H0) :
    ScaledHeatWeak hm ν (scaleHeat hm H0 ν hν0 hν1) := by
  unfold ScaledHeatWeak at h0 ⊢
  obtain ⟨h0a, h0b⟩ := h0
  refine ⟨fun w φ hφ t ht => ?_, fun F a b hab hb hF φ hφ t ht => ?_⟩
  · -- conjunct (a): viscous substitution `r ↦ ν r`
    have hνt : ν * t ∈ Icc (0 : ℝ) 1 := mapsTo_scale_Icc hν0 hν1 ht
    have hA := h0a w φ hφ (ν * t) hνt
    have key := scale_int0 (fun r => ∫ x in UnforcedLeray.B0579.cell c,
      vortFn hm (H0.S₀ r w) x * lapP φ x) (ν := ν) t hν0
    simp only [scaleHeat_S₀]
    rw [hA, one_mul, key]
  · -- conjunct (b): Duhamel substitution `r ↦ ν r` with flux `scaleFlux ν F`
    have hab' : ν * a ≤ ν * b := mul_le_mul_of_nonneg_left hab hν0.le
    have hb' : ν * b ≤ ν * a + 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hν1 (sub_nonneg.2 hab)]
    have hU := h0b (scaleFlux ν F) (ν * a) (ν * b) hab' hb'
      (scaleFlux_continuousOn hν0 F hF) φ hφ (ν * t)
      ⟨mul_le_mul_of_nonneg_left ht.1 hν0.le, mul_le_mul_of_nonneg_left ht.2 hν0.le⟩
    rw [one_mul] at hU
    have e1 : ∫ r in a..t, (scaleHeat hm H0 ν hν0 hν1).S (t - r) (F r) =
        ∫ r in ν * a..ν * t, H0.S (ν * t - r) (scaleFlux ν F r) :=
      (elem_scale hm H0 hν0 hν1 F a t).symm
    have e2 : ∀ r : ℝ, ∫ s in a..r, (scaleHeat hm H0 ν hν0 hν1).S (r - s) (F s) =
        ∫ s in ν * a..ν * r, H0.S (ν * r - s) (scaleFlux ν F s) :=
      fun r => (elem_scale hm H0 hν0 hν1 F a r).symm
    have hΘ : ∫ r in ν * a..ν * t, ∫ x in UnforcedLeray.B0579.cell c,
          (fluxFn (scaleFlux ν F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
            fluxFn (scaleFlux ν F r) 1 x * UnforcedLeray.B0579.pd 1 φ x) =
        ∫ r in a..t, ∫ x in UnforcedLeray.B0579.cell c,
          (fluxFn (F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
            fluxFn (F r) 1 x * UnforcedLeray.B0579.pd 1 φ x) := by
      rw [scale_int (fun r => ∫ x in UnforcedLeray.B0579.cell c,
          (fluxFn (scaleFlux ν F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
            fluxFn (scaleFlux ν F r) 1 x * UnforcedLeray.B0579.pd 1 φ x)) a t hν0,
        smul_eq_mul, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      simp only
      rw [scaleFlux_apply hν0 F r, fluxFn_smul_int ν⁻¹ (F r)
        (UnforcedLeray.B0579.pd 0 φ) (UnforcedLeray.B0579.pd 1 φ)]
      rw [← mul_assoc, mul_inv_cancel₀ hν0.ne', one_mul]
    rw [e1, hU, hΘ]
    rw [scale_int _ a t hν0, smul_eq_mul]
    congr 2
    apply intervalIntegral.integral_congr
    intro r _
    simp only
    rw [← e2 r]

/-- The unit-to-rescaled transfer in the form of the `ScaleSupplier` leaf. -/
theorem scaleSupplier_aux (ν c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1)
    (h0 : ScaledHeatWeak hm 1 (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm)) :
    ∃ H : WeightedHeatStripSupplier (c := c) (m := m) hm, ScaledHeatWeak hm ν H :=
  ⟨scaleHeat hm _ ν hν0 hν1, scaledHeatWeak_scale hm _ ν hν0 hν1 h0⟩

end ScaleAux

open ScaleAux in
theorem scaleSupplier : UnforcedLeray.Short.IIIa.Exist.ScaleSupplier := by
  intro ν c m _ hc1 hm hν0 hν1 h0
  exact scaleSupplier_aux ν c m hc1 hm hν0 hν1 h0

end UnforcedLeray.Short.IIIa.Exist
