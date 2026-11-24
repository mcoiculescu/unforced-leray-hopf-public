import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.SigmaToLambda
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Support
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Theta
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.VanishAbove
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_10

/-!
# `wardYPointDomUniform`: assembly of the pointwise domination of `Y`

Source `the November 2 reference manuscript` 5585-5589, 4161-4205.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma pu_fullKer_zero (ν μ R : ℝ) (χy : ℝ → ℝ) (h : ℝ) (y z : Space) :
    fullKer ν μ R χy h y z 0 = 0 := by
  have hg : ∀ t x, gradKCon t x 0 = 0 := by
    intro t x; unfold gradKCon; ext i; simp
  simp [fullKer, xKer, sKer, hg]

lemma pu_physDmu_zero (ν μ R : ℝ) (χy : ℝ → ℝ) (z : Space) (h : ℝ) (y : Space) :
    physDmu ν (μ + 1) (fun h' y' => fullKer ν μ R χy h' y' z 0) h y = 0 := by
  have : (fun h' y' => fullKer ν μ R χy h' y' z 0) = fun _ _ => (0 : Space) := by
    funext a b; exact pu_fullKer_zero ν μ R χy a b z
  rw [this]
  have hp : ∀ (j : Fin 3) (y : Space), physPd (fun _ => (0 : Space)) j y = 0 := by
    intro j y; simp [physPd]
  simp [physDmu, physLap, physPd2, hp]

theorem wardYPointDomUniform : WardYPointDomUniform := by
  intro χy hχ
  obtain ⟨C₀, hC₀, hK⟩ := pdYKerBound χy hχ
  refine ⟨2 * C₀ + 1, 0, ?_⟩
  intro ν μ R c δ hR hμ1 hν hR0 hc hμ _ hδ1 hδ0 g hg hgs τ y hϱ
  by_cases hage : 1 < ν * age R y
  · rw [wardY_eq_zero_of_one_lt hχ hR0 g τ y hϱ hage]; simp
  rw [not_lt] at hage
  set θ : ℝ := Real.exp (-(δ / 2)) with hθdef
  by_cases hfin : wardYKerMaj R c θ g τ y + wardYStreamMaj R c θ g τ y = ⊤
  · rw [hfin, ENNReal.mul_top]
    · exact le_top
    · simp only [pow_zero, mul_one, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
  have hfin' : wardYKerMaj R c (Real.exp (-(δ / 2))) g τ y +
      wardYStreamMaj R c (Real.exp (-(δ / 2))) g τ y < ⊤ := lt_top_iff_ne_top.2 hfin
  rw [pdYRep ν μ R c δ χy g hν hR hc hμ hμ1 hχ hδ0 hδ1 hg hgs τ y hϱ hage hfin']
  have hθ : Real.sqrt (5 / 6) < θ := pdTheta δ hδ1
  -- the two integrands
  let K1 : ℝ × Space → ℝ≥0∞ := fun e =>
    ENNReal.ofReal ((‖y - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
  let K2 : ℝ × Space → ℝ≥0∞ := fun e =>
    ENNReal.ofReal ((ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam (τ - e.1) * e.2 2) ^ 2))⁻¹)
  let N : ℝ × Space → ℝ≥0∞ := fun e => IIIa.srcNorm (oldPhys R c g) e.1 e.2
  let Φ1 : ℝ × Space → ℝ≥0∞ := fun e => if ϱ e.2 < θ * ϱ y then K1 e * N e else 0
  let Φ2 : ℝ × Space → ℝ≥0∞ := fun e => if ϱ e.2 < θ * ϱ y then K2 e * N e else 0
  have hN : Measurable N := measurable_srcNorm' R c g hg
  have hpd : Measurable (fun e : ℝ × Space => pdLam (τ - e.1)) := by
    unfold pdLam; fun_prop
  have hϱm : Measurable (fun z : Space => ϱ z) := by unfold ϱ; fun_prop
  have hS : MeasurableSet {e : ℝ × Space | ϱ e.2 < θ * ϱ y} :=
    measurableSet_lt (hϱm.comp measurable_snd) measurable_const
  have hK1 : Measurable K1 := by
    refine Measurable.ennreal_ofReal (Measurable.inv ?_)
    refine Measurable.pow_const ?_ 4
    refine Measurable.norm ?_
    exact measurable_const.sub (hpd.smul measurable_snd)
  have hK2 : Measurable K2 := by
    refine Measurable.ennreal_ofReal (Measurable.inv ?_)
    refine measurable_const.mul (measurable_const.add ?_)
    refine Measurable.pow_const ?_ 2
    exact measurable_const.sub (hpd.mul (by fun_prop))
  have hΦ1 : Measurable Φ1 := Measurable.ite hS (hK1.mul hN) measurable_const
  have hΦ2 : Measurable Φ2 := Measurable.ite hS (hK2.mul hN) measurable_const
  -- pointwise bound
  have hpt : ∀ e : ℝ × Space,
      ‖(if e.1 < τ then physDmu ν (μ + 1)
          (fun h y' => fullKer ν μ R χy h y' e.2 (oldPhys R c g e.1 e.2)) (τ - e.1) y
        else 0)‖ₑ ≤
        ENNReal.ofReal C₀ * ((if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1)) else 0) *
          (Φ1 e + Φ2 e)) := by
    intro e
    by_cases hσ : e.1 < τ
    · simp only [hσ, if_true]
      by_cases hM : oldPhys R c g e.1 e.2 = 0
      · rw [hM, pu_physDmu_zero]; simp
      · have hz : ϱ e.2 ≤ Real.sqrt (5 / 6) * ϱ y := by
          by_contra hc'
          exact hM (pdSupport ν R c g hν hR0 hgs y hϱ hage e.1 e.2 (not_le.1 hc'))
        have hzθ : ϱ e.2 < θ * ϱ y := by
          calc ϱ e.2 ≤ Real.sqrt (5 / 6) * ϱ y := hz
            _ < θ * ϱ y := by exact mul_lt_mul_of_pos_right hθ hϱ
        have hb := hK ν μ R hν hR hμ hμ1 (τ - e.1) (sub_pos.2 hσ) y e.2 (oldPhys R c g e.1 e.2) hϱ hage hz
        have hlam0 : 0 < pdLam (τ - e.1) := Real.exp_pos _
        have hlam1 : pdLam (τ - e.1) ≤ 1 := by
          unfold pdLam
          rw [Real.exp_le_one_iff]
          have := sub_pos.2 hσ; linarith
        have hpow : pdLam (τ - e.1) ^ (2 * μ + 3) ≤ pdLam (τ - e.1) := by
          have := Real.rpow_le_rpow_of_exponent_ge hlam0 hlam1
            (show (1 : ℝ) ≤ 2 * μ + 3 by linarith)
          simpa using this
        have ha : 0 ≤ (‖y - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ := by positivity
        have hb' : 0 ≤ (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam (τ - e.1) * e.2 2) ^ 2))⁻¹ := by
          positivity
        have htn : 0 ≤ IIIa.tensorNorm (oldPhys R c g e.1 e.2) := Real.sqrt_nonneg _
        rw [← ofReal_norm_eq_enorm]
        have hΦ : Φ1 e + Φ2 e = ENNReal.ofReal (((‖y - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ +
            (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam (τ - e.1) * e.2 2) ^ 2))⁻¹) *
              IIIa.tensorNorm (oldPhys R c g e.1 e.2)) := by
          simp only [Φ1, Φ2, hzθ, if_true, K1, K2, N, IIIa.srcNorm]
          rw [← add_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add ha hb']
        rw [hΦ, ← ENNReal.ofReal_mul hlam0.le, ← ENNReal.ofReal_mul hC₀]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsum : 0 ≤ ((‖y - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ +
            (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam (τ - e.1) * e.2 2) ^ 2))⁻¹) *
              IIIa.tensorNorm (oldPhys R c g e.1 e.2) := by positivity
        calc _ ≤ C₀ * pdLam (τ - e.1) ^ (2 * μ + 3) * ((‖y - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ +
            (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam (τ - e.1) * e.2 2) ^ 2))⁻¹) *
              IIIa.tensorNorm (oldPhys R c g e.1 e.2) := hb
          _ ≤ C₀ * pdLam (τ - e.1) * ((‖y - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ +
            (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam (τ - e.1) * e.2 2) ^ 2))⁻¹) *
              IIIa.tensorNorm (oldPhys R c g e.1 e.2) := by
              have := mul_le_mul_of_nonneg_left hpow hC₀
              have h2 := mul_le_mul_of_nonneg_right this
                (show 0 ≤ ((‖y - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ +
                  (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam (τ - e.1) * e.2 2) ^ 2))⁻¹) by positivity)
              exact mul_le_mul_of_nonneg_right h2 htn
          _ = _ := by ring
    · simp [hσ]
  have hSz : MeasurableSet {z : Space | ϱ z < θ * ϱ y} :=
    measurableSet_lt hϱm measurable_const
  have hind : Measurable (fun e : ℝ × Space =>
      (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1)) else 0)) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      hpd.ennreal_ofReal measurable_const
  have hlam : ∀ l : ℝ, 0 < l → pdLam (τ - (τ + 2 * Real.log l)) = l := by
    intro l hl
    unfold pdLam
    have : -((τ - (τ + 2 * Real.log l)) / 2) = Real.log l := by ring
    rw [this, Real.exp_log hl]
  have hA : ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, Φ1 (τ + 2 * Real.log l, z) =
      wardYKerMaj R c θ g τ y := by
    unfold wardYKerMaj
    refine setLIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
    rw [← lintegral_indicator hSz]
    apply lintegral_congr; intro z
    simp only [Φ1, K1, N, hlam l hl.1, Set.indicator_apply, Set.mem_setOf_eq]
  have hB : ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, Φ2 (τ + 2 * Real.log l, z) =
      wardYStreamMaj R c θ g τ y := by
    unfold wardYStreamMaj
    refine setLIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
    rw [← lintegral_indicator hSz]
    apply lintegral_congr; intro z
    simp only [Φ2, K2, N, hlam l hl.1, Set.indicator_apply, Set.mem_setOf_eq]
  calc _ ≤ ∫⁻ e : ℝ × Space, ‖(if e.1 < τ then physDmu ν (μ + 1)
          (fun h y' => fullKer ν μ R χy h y' e.2 (oldPhys R c g e.1 e.2)) (τ - e.1) y
        else 0)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ e : ℝ × Space, ENNReal.ofReal C₀ * ((if e.1 < τ then
          ENNReal.ofReal (pdLam (τ - e.1)) else 0) * (Φ1 e + Φ2 e)) := lintegral_mono hpt
    _ = ENNReal.ofReal C₀ * ((∫⁻ e : ℝ × Space, (if e.1 < τ then
          ENNReal.ofReal (pdLam (τ - e.1)) else 0) * Φ1 e) +
        (∫⁻ e : ℝ × Space, (if e.1 < τ then
          ENNReal.ofReal (pdLam (τ - e.1)) else 0) * Φ2 e)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        simp_rw [mul_add]
        have hm : Measurable (fun e : ℝ × Space => (if e.1 < τ then
          ENNReal.ofReal (pdLam (τ - e.1)) else 0) * Φ1 e) := hind.mul hΦ1
        exact lintegral_add_left hm _
    _ = ENNReal.ofReal C₀ * (2 * wardYKerMaj R c θ g τ y + 2 * wardYStreamMaj R c θ g τ y) := by
        rw [pdSigmaToLambda τ Φ1 hΦ1, pdSigmaToLambda τ Φ2 hΦ2, hA, hB]
    _ = ENNReal.ofReal (2 * C₀) * (wardYKerMaj R c θ g τ y + wardYStreamMaj R c θ g τ y) := by
        have h2 : ENNReal.ofReal 2 = 2 := by simp
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), h2]
        ring
    _ ≤ _ := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        simp only [pow_zero, mul_one]
        linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
