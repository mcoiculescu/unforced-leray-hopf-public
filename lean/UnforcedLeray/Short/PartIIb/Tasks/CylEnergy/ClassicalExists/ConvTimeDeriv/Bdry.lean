import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCont

/-!


`(t-τ)⁻¹ ∫_τ^t H_{ν(t-r)} F(r)(x) dr → F(τ)(x)`. Source:
`the November 2 reference manuscript`, lines 2074-2093.
Route: the scaled representation `H_a g(x) = ∫ heatK 1 w * g (x - √(max a 0) w)` (valid for all `a`,
by `HC.heatSG_pos_eq` and `∫ heatK 1 = 1`) makes `(t, r) ↦ H_{ν(t-r)} F(r)(x)` continuous on
`ℝ × [s,T]` by dominated continuity; its value at `(τ, τ)` is `F τ x`; the average over `r`
between `τ` and `t` is within `ε` of it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

namespace CTDB

lemma heatSG_scaled (a : ℝ) (g : Pl → ℝ) (x : Pl) :
    heatSG a g x = ∫ w : Pl, heatK 1 w * g (x - Real.sqrt (max a 0) • w) := by
  rcases lt_or_ge 0 a with ha | ha
  · rw [HC.heatSG_pos_eq ha g x, max_eq_left ha.le]
  · have hint := (heatKernelMoments 1 one_pos).2.2.1
    have hm : max a 0 = 0 := max_eq_right ha
    simp only [heatSG, ha, ite_true, hm, Real.sqrt_zero, zero_smul, sub_zero]
    rw [integral_mul_const, hint, one_mul]

lemma psi_continuousOn {ν s T : ℝ} {B : ℝ} {F : ℝ → Pl → ℝ} (hF : FReg s T F)
    (hB : ∀ r ∈ Icc s T, WB B (F r)) (x : Pl) :
    ContinuousOn (fun p : ℝ × ℝ => heatSG (ν * (p.1 - p.2)) (F p.2) x)
      (univ ×ˢ Icc s T) := by
  have hI := (heatKernelMoments 1 one_pos).2.1
  have hKc := HC.heatK1_continuous
  have key : ContinuousOn (fun p : ℝ × ℝ =>
      ∫ w : Pl, heatK 1 w * F p.2 (x - Real.sqrt (max (ν * (p.1 - p.2)) 0) • w))
      (univ ×ˢ Icc s T) := by
    refine continuousOn_of_dominated (bound := fun w => |heatK 1 w| * B) ?_ ?_ ?_ ?_
    · intro p hp
      have hc : Continuous (F p.2) := (hF.c1 p.2 hp.2).continuous
      exact (hKc.mul (hc.comp (by fun_prop))).aestronglyMeasurable
    · intro p hp
      refine ae_of_all _ fun w => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (HC.gbound (hB p.2 hp.2) _) (abs_nonneg _)
    · exact hI.abs.mul_const B
    · refine ae_of_all _ fun w => ?_
      refine continuousOn_const.mul ?_
      have hmap : ContinuousOn (fun p : ℝ × ℝ =>
          ((p.2 : ℝ), x - Real.sqrt (max (ν * (p.1 - p.2)) 0) • w))
          (univ ×ˢ Icc s T) := by
        apply Continuous.continuousOn
        fun_prop
      refine hF.contF.comp hmap ?_
      intro p hp
      exact ⟨hp.2, mem_univ _⟩
  refine key.congr ?_
  intro p _
  exact heatSG_scaled _ _ _

end CTDB

/-- **`T22/1/11/3`** The boundary term of the Duhamel difference quotient. -/
theorem convTD_Bdry : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Bdry := by
  intro ν s T hν hsT B F hF hB τ hτ x
  have hψ := CTDB.psi_continuousOn (ν := ν) hF hB x
  have hval : heatSG (ν * (τ - τ)) (F τ) x = F τ x := by
    simp [heatSG]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcw := hψ (τ, τ) ⟨mem_univ _, hτ⟩
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨δ, hδ, hδ'⟩ := hcw (ε / 2) (half_pos hε)
  have h1 : ∀ᶠ t in 𝓝[Icc s T \ {τ}] τ, t ∈ Metric.ball τ δ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)
  have h2 : ∀ᶠ t in 𝓝[Icc s T \ {τ}] τ, t ∈ Icc s T \ {τ} := self_mem_nhdsWithin
  filter_upwards [h1, h2] with t ht1 ht2
  obtain ⟨htI, htne⟩ := ht2
  have htne' : t - τ ≠ 0 := sub_ne_zero.2 htne
  have hsub : uIcc τ t ⊆ Icc s T := uIcc_subset_Icc hτ htI
  have hbound : ∀ r ∈ uIoc τ t, ‖heatSG (ν * (t - r)) (F r) x - F τ x‖ ≤ ε / 2 := by
    intro r hr
    have hr' : r ∈ uIcc τ t := uIoc_subset_uIcc hr
    have hrI : r ∈ Icc s T := hsub hr'
    have hrτ : |r - τ| ≤ |t - τ| := by
      rcases le_total τ t with h | h
      · rw [uIcc_of_le h] at hr'
        rw [abs_of_nonneg (sub_nonneg.2 hr'.1), abs_of_nonneg (sub_nonneg.2 h)]
        linarith [hr'.2]
      · rw [uIcc_of_ge h] at hr'
        rw [abs_of_nonpos (sub_nonpos.2 hr'.2), abs_of_nonpos (sub_nonpos.2 h)]
        linarith [hr'.1]
    have hd : dist (t, r) (τ, τ) < δ := by
      rw [Prod.dist_eq]
      have ht1' : |t - τ| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using ht1
      refine max_lt ?_ ?_
      · simpa [Real.dist_eq] using ht1'
      · rw [Real.dist_eq]; exact lt_of_le_of_lt hrτ ht1'
    have := hδ' (x := (t, r)) ⟨mem_univ _, hrI⟩ hd
    simp only [sub_self, mul_zero] at this
    have hv0 : heatSG 0 (F τ) x = F τ x := by simpa using hval
    rw [hv0] at this
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  have hint : IntervalIntegrable (fun r => heatSG (ν * (t - r)) (F r) x) volume τ t := by
    have hcon : ContinuousOn (fun r : ℝ => heatSG (ν * (t - r)) (F r) x) (uIcc τ t) := by
      have := hψ.comp (f := fun r : ℝ => (t, r)) (by fun_prop : Continuous fun r : ℝ => (t, r)).continuousOn
        (fun r hr => ⟨mem_univ _, hsub hr⟩)
      exact this
    exact hcon.intervalIntegrable
  have heq : (t - τ)⁻¹ * (∫ r in τ..t, heatSG (ν * (t - r)) (F r) x) - F τ x
      = (t - τ)⁻¹ * ∫ r in τ..t, (heatSG (ν * (t - r)) (F r) x - F τ x) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ htne', one_mul]
  rw [Real.dist_eq, heq, abs_mul, abs_inv]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at hn
  have hpos : 0 < |t - τ| := abs_pos.2 htne'
  calc |t - τ|⁻¹ * |∫ r in τ..t, (heatSG (ν * (t - r)) (F r) x - F τ x)|
      ≤ |t - τ|⁻¹ * (ε / 2 * |t - τ|) := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

end UnforcedLeray.Short.IIb.CylPDE
