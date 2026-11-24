import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.AtomSupport
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.GapSpatialL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PhaseWeight

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/16`: the atom bound

Source `the November 2 reference manuscript` 5588-5591.  Proves `AtomBound`:
for an atom `a = (σ, z)`, `srcW(a) · ‖phKer(·; a)‖_{L²((0,P] × ybin)} ≤ 1_{age z > s₁/θ²} srcW(a)
· √gapA · √omega2(σ)`.

Route: `‖·‖²` of the kernel over the product is bounded by the iterated integral (Tonelli upper
bound `lintegral_prod_le`); the inner `y`-integral is at most `e^{σ-τ}/4 · gapA` on `σ < τ`
(`GapSpatialL2` with `l = e^{(σ-τ)/2}`) and zero otherwise; the `τ`-integral is `omega2 · gapA`
(`PhaseWeight`).  Where the source age is at most `s₁/θ²` the kernel vanishes (`AtomSupport`) or
the source weight vanishes (`ϱ z = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The age map is measurable. -/
theorem atomBound_age_meas (R : ℝ) : Measurable (fun y : Space => age R y) := by
  unfold age
  exact measurable_const.div (measurable_ϱ.pow_const 2)

/-- The output bin is measurable. -/
theorem atomBound_ybin_meas (R s1 s0 : ℝ) : MeasurableSet (ybin R s1 s0) :=
  (atomBound_age_meas R) (measurableSet_Ioc : MeasurableSet (Ioc s1 s0))

/-- The squared kernel, written out. -/
theorem atomBound_phKer_sq (θ τ : ℝ) (y : Space) (σ : ℝ) (z : Space) :
    phKer θ τ y σ z ^ (2 : ℝ) =
      if σ < τ ∧ ϱ z < θ * ϱ y then
        ENNReal.ofReal (Real.exp (σ - τ) / 4) *
          ENNReal.ofReal ((‖y - Real.exp ((σ - τ) / 2) • z‖ ^ 4)⁻¹) ^ (2 : ℝ)
      else 0 := by
  unfold phKer
  split_ifs with h
  · have hsq : Real.exp ((σ - τ) / 2) ^ 2 = Real.exp (σ - τ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hx : 0 ≤ Real.exp ((σ - τ) / 2) / 2 := by positivity
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, div_pow, hsq]
    norm_num
  · rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The inner `y`-integral of one atom over the output bin, for fixed phase `τ`. -/
theorem atomBound_inner (R θ s1 s0 : ℝ) (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs1 : 0 < s1) (hs1s0 : s1 ≤ s0) (σ τ : ℝ) (z : Space) :
    ∫⁻ y in ybin R s1 s0, phKer θ τ y σ z ^ (2 : ℝ) ≤
      (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0) *
        ENNReal.ofReal (gapA θ R s0) := by
  have hs0 : 0 < s0 := lt_of_lt_of_le hs1 hs1s0
  have hybin : MeasurableSet (ybin R s1 s0) := atomBound_ybin_meas R s1 s0
  by_cases hστ : σ < τ
  · rw [if_pos hστ]
    have h1 : MeasurableSet {y : Space | age R y ≤ s0} :=
      measurableSet_le (atomBound_age_meas R) measurable_const
    have h2 : MeasurableSet {y : Space | ϱ z < θ * ϱ y} :=
      measurableSet_lt measurable_const (measurable_ϱ.const_mul θ)
    have hSm : MeasurableSet {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y} := h1.inter h2
    have hl0 : 0 < Real.exp ((σ - τ) / 2) := Real.exp_pos _
    have hl1 : Real.exp ((σ - τ) / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have hpt : ∀ y ∈ ybin R s1 s0, phKer θ τ y σ z ^ (2 : ℝ) ≤
        Set.indicator {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y}
          (fun y => ENNReal.ofReal (Real.exp (σ - τ) / 4) *
            ENNReal.ofReal ((‖y - Real.exp ((σ - τ) / 2) • z‖ ^ 4)⁻¹) ^ (2 : ℝ)) y := by
      intro y hy
      have hy' : s1 < age R y ∧ age R y ≤ s0 := hy
      rw [atomBound_phKer_sq]
      by_cases hc : σ < τ ∧ ϱ z < θ * ϱ y
      · have hmem : y ∈ {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y} := ⟨hy'.2, hc.2⟩
        exact le_of_eq (by rw [if_pos hc, Set.indicator_of_mem hmem])
      · rw [if_neg hc]
        exact zero_le
    calc ∫⁻ y in ybin R s1 s0, phKer θ τ y σ z ^ (2 : ℝ)
        ≤ ∫⁻ y in ybin R s1 s0, Set.indicator {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y}
            (fun y => ENNReal.ofReal (Real.exp (σ - τ) / 4) *
              ENNReal.ofReal ((‖y - Real.exp ((σ - τ) / 2) • z‖ ^ 4)⁻¹) ^ (2 : ℝ)) y :=
          setLIntegral_mono' hybin hpt
      _ ≤ ∫⁻ y, Set.indicator {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y}
            (fun y => ENNReal.ofReal (Real.exp (σ - τ) / 4) *
              ENNReal.ofReal ((‖y - Real.exp ((σ - τ) / 2) • z‖ ^ 4)⁻¹) ^ (2 : ℝ)) y :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ y in {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y},
            ENNReal.ofReal (Real.exp (σ - τ) / 4) *
              ENNReal.ofReal ((‖y - Real.exp ((σ - τ) / 2) • z‖ ^ 4)⁻¹) ^ (2 : ℝ) :=
          lintegral_indicator hSm _
      _ = ENNReal.ofReal (Real.exp (σ - τ) / 4) *
            ∫⁻ y in {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y},
              ENNReal.ofReal ((‖y - Real.exp ((σ - τ) / 2) • z‖ ^ 4)⁻¹) ^ (2 : ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (σ - τ) / 4) * ENNReal.ofReal (gapA θ R s0) :=
          mul_le_mul_of_nonneg_left (gapSpatialL2 R θ s0 (Real.exp ((σ - τ) / 2)) z hR hθ hθ1 hs0 hl0 hl1)
            zero_le
  · rw [if_neg hστ, zero_mul]
    have h0 : ∫⁻ y in ybin R s1 s0, phKer θ τ y σ z ^ (2 : ℝ) ≤
        ∫⁻ y in ybin R s1 s0, (0 : ℝ≥0∞) :=
      setLIntegral_mono' hybin (fun y _ => le_of_eq (by
        rw [atomBound_phKer_sq,
          if_neg (show ¬ (σ < τ ∧ ϱ z < θ * ϱ y) from fun h => hστ h.1)]))
    exact h0.trans (by simp)

/-- The `L²` bound over the product `(0,P] × ybin` of one atom, through the Tonelli upper bound. -/
theorem atomBound_prod (θ R s1 s0 P σ : ℝ) (z : Space) (hR : 0 < R) (hθ : 0 < θ)
    (hθ1 : θ < 1) (hs1 : 0 < s1) (hs1s0 : s1 ≤ s0) (hP : 0 < P) :
    ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKer θ x.1 x.2 σ z ^ (2 : ℝ) ≤
      ENNReal.ofReal (omega2 P σ * gapA θ R s0) := by
  have hprod : ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKer θ x.1 x.2 σ z ^ (2 : ℝ) ≤
      ∫⁻ τ in Ioc 0 P, ∫⁻ y in ybin R s1 s0, phKer θ τ y σ z ^ (2 : ℝ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact lintegral_prod_le _
  have hω : 0 ≤ omega2 P σ := by
    unfold omega2
    split_ifs
    · exact mul_nonneg (by linarith) (le_min zero_le_one (Real.exp_pos σ).le)
    · exact le_rfl
  have hgap : 0 ≤ gapA θ R s0 := by
    have hs0 : 0 < s0 := lt_of_lt_of_le hs1 hs1s0
    have hD : 0 < (1 - θ) * R / Real.sqrt s0 :=
      div_pos (mul_pos (by linarith) hR) (Real.sqrt_pos.2 hs0)
    unfold gapA
    exact mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.2 hD.le) 5)
  calc ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKer θ x.1 x.2 σ z ^ (2 : ℝ)
      ≤ ∫⁻ τ in Ioc 0 P, ∫⁻ y in ybin R s1 s0, phKer θ τ y σ z ^ (2 : ℝ) := hprod
    _ ≤ ∫⁻ τ in Ioc 0 P,
          (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0) *
            ENNReal.ofReal (gapA θ R s0) :=
          setLIntegral_mono' measurableSet_Ioc
            (fun τ _ => atomBound_inner R θ s1 s0 hR hθ hθ1 hs1 hs1s0 σ τ z)
    _ = (∫⁻ τ in Ioc 0 P, (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0)) *
            ENNReal.ofReal (gapA θ R s0) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (omega2 P σ) * ENNReal.ofReal (gapA θ R s0) :=
          mul_le_mul_of_nonneg_right (phaseWeight P σ hP) zero_le
    _ = ENNReal.ofReal (omega2 P σ * gapA θ R s0) := (ENNReal.ofReal_mul hω).symm

/-- **Atom bound** (source 5588-5591). -/
theorem atomBound : AtomBound := by
  intro R c θ s1 s0 P G hR hθ hθ1 hs1 hs1s0 hP a
  obtain ⟨σ, z⟩ := a
  dsimp only
  have hs0 : 0 < s0 := lt_of_lt_of_le hs1 hs1s0
  have hω : 0 ≤ omega2 P σ := by
    unfold omega2
    split_ifs
    · exact mul_nonneg (by linarith) (le_min zero_le_one (Real.exp_pos σ).le)
    · exact le_rfl
  have hgap : 0 ≤ gapA θ R s0 := by
    have hD : 0 < (1 - θ) * R / Real.sqrt s0 :=
      div_pos (mul_pos (by linarith) hR) (Real.sqrt_pos.2 hs0)
    unfold gapA
    exact mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.2 hD.le) 5)
  have hX := atomBound_prod θ R s1 s0 P σ z hR hθ hθ1 hs1 hs1s0 hP
  have hroot : (∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKer θ x.1 x.2 σ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (gapA θ R s0) * Real.sqrt (omega2 P σ)) := by
    calc _ ≤ (ENNReal.ofReal (omega2 P σ * gapA θ R s0)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hX (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (omega2 P σ * gapA θ R s0)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hω hgap) (by norm_num),
            Real.sqrt_eq_rpow]
      _ = ENNReal.ofReal (Real.sqrt (gapA θ R s0) * Real.sqrt (omega2 P σ)) := by
          congr 1
          rw [Real.sqrt_mul hω]
          ring
  by_cases hc : s1 / θ ^ 2 < age R z
  · have hmem : (σ, z) ∈ {a : ℝ × Space | s1 / θ ^ 2 < age R a.2} := hc
    rw [Set.indicator_of_mem hmem]
    exact mul_le_mul_of_nonneg_left hroot zero_le
  · have hnmem : (σ, z) ∉ {a : ℝ × Space | s1 / θ ^ 2 < age R a.2} := hc
    rw [Set.indicator_of_notMem hnmem, zero_mul]
    rcases (ϱ_nonneg z).eq_or_lt with h0 | hpos
    · have hage0 : age R z = 0 := by
        unfold age
        rw [← h0]
        simp
      have hsrc : srcW R c G σ z = 0 := by
        unfold srcW
        rw [hage0]
        simp
      exact le_of_eq (by rw [hsrc, zero_mul])
    · have hmeas : MeasurableSet (Ioc 0 P ×ˢ ybin R s1 s0) :=
        (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) P)).prod (atomBound_ybin_meas R s1 s0)
      have hzero : ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKer θ x.1 x.2 σ z ^ (2 : ℝ) ≤
          ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, (0 : ℝ≥0∞) :=
        setLIntegral_mono' hmeas (fun x hx => le_of_eq (by
          rw [atomSupport R θ s1 s0 hR hθ hs1 x.1 x.2 σ z hx.2 hpos hc,
            ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]))
      have hX0 : ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKer θ x.1 x.2 σ z ^ (2 : ℝ) ≤ 0 :=
        hzero.trans (by simp)
      have hX0' : ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKer θ x.1 x.2 σ z ^ (2 : ℝ) = 0 :=
        le_antisymm hX0 zero_le
      exact le_of_eq (by
        rw [hX0', ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_zero])

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
