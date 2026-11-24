import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4.PsiSProps
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PhaseWeight
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4.StreamSpatial

/-!
# `PartIII-b:C/rep/5/1/2/4/1/4/4`: the stream atom bound and the stream constants

Source `the November 2 reference manuscript` 5585-5593, 4178-4186, 5592.
Proves `StreamConstAlgebra` (the θ-free constant `2π^{3/2}/√5 (1+c/R) R^{-3/2} s₀^{5/4}`) and,
in the rest of the file, `StreamAtomBound` (the atom bound for the stream kernel).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYStream

open UnforcedLeray.Short.PartIIIb.Concrete.WYCore (srcW omega2 ybin)

theorem sc_sqrt_pow5 (u : ℝ) (hu : 0 ≤ u) : Real.sqrt (u ^ 5) = u ^ (5 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu]
  norm_num

theorem sc_sqrt_rpow5 (s : ℝ) (hs : 0 ≤ s) :
    (Real.sqrt s) ^ (5 / 2 : ℝ) = s ^ (5 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs]
  norm_num

/-- `√gapS = (π/√5) R^{-5/2} s₀^{5/4}`. -/
theorem sc_sqrt_gapS (R s0 : ℝ) (hR : 0 < R) (hs0 : 0 < s0) :
    Real.sqrt (gapS R s0) = Real.pi / Real.sqrt 5 * (R ^ (5 / 2 : ℝ))⁻¹ * s0 ^ (5 / 4 : ℝ) := by
  unfold gapS
  have hu0 : 0 ≤ (R / Real.sqrt s0)⁻¹ := by positivity
  have hpi5 : Real.pi ^ 2 / 5 = (Real.pi / Real.sqrt 5) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  rw [hpi5, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), sc_sqrt_pow5 _ hu0,
    Real.inv_rpow (div_nonneg hR.le (Real.sqrt_nonneg _)),
    Real.div_rpow hR.le (Real.sqrt_nonneg _), sc_sqrt_rpow5 s0 hs0.le, inv_div]
  ring

/-- `R^{-3/2} = R (R^{5/2})^{-1}`. -/
theorem sc_rpow_neg32 (R : ℝ) (hR : 0 < R) :
    R ^ (-(3 / 2 : ℝ)) = R * (R ^ (5 / 2 : ℝ))⁻¹ := by
  rw [show (-(3 / 2 : ℝ)) = 1 + -(5 / 2 : ℝ) by norm_num, Real.rpow_add hR, Real.rpow_one,
    Real.rpow_neg hR.le]

/-- The algebraic identity behind the constant (variables `a = √P`, `b = √π`, `e = √5`). -/
theorem sc_alg (a b e R u t : ℝ) (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hR : 0 < R) :
    (a * b * R)⁻¹ * (b ^ 2 / e * u * t) * (a + 1 / a) * (a ^ 2 * (b ^ 2 * R ^ 2)) =
      (1 + a ^ 2) * (b ^ 3 * R * u * t / e) := by
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have he' : e ≠ 0 := he.ne'
  have hR' : R ≠ 0 := hR.ne'
  field_simp
  ring

theorem sc_ineq (R c s0 : ℝ) (hR : 0 < R) (hc : 0 < c) (hs0 : 0 < s0) :
    (2 * Real.pi * c * R) ⁻¹ ^ (1 / 2 : ℝ) * Real.sqrt (gapS R s0) *
        (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) * (2 * c / R * (Real.pi * R ^ 2)) ≤
      wyC0S * (1 + c / R) * R ^ (-(3 / 2 : ℝ)) * s0 ^ (5 / 4 : ℝ) := by
  have hPpos : 0 < 2 * c / R := by positivity
  have hD : (2 * Real.pi * c * R) ⁻¹ ^ (1 / 2 : ℝ) =
      (Real.sqrt (2 * c / R) * Real.sqrt Real.pi * R)⁻¹ := by
    rw [show 2 * Real.pi * c * R = (2 * c / R) * (Real.pi * R ^ 2) by field_simp,
      ← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_mul hPpos.le, Real.sqrt_mul Real.pi_pos.le,
      Real.sqrt_sq hR.le]
    ring
  rw [hD, sc_sqrt_gapS R s0 hR hs0, sc_rpow_neg32 R hR]
  unfold wyC0S
  have hu0 : 0 ≤ (R ^ (5 / 2 : ℝ))⁻¹ := by positivity
  have ht0 : 0 ≤ s0 ^ (5 / 4 : ℝ) := by positivity
  have hb0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have he0 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hπ : Real.pi = Real.sqrt Real.pi ^ 2 := (Real.sq_sqrt Real.pi_pos.le).symm
  have hPa0 : 0 < Real.sqrt (2 * c / R) := Real.sqrt_pos.2 hPpos
  have hPa : 2 * c / R = Real.sqrt (2 * c / R) ^ 2 := (Real.sq_sqrt hPpos.le).symm
  have hcR : c / R = Real.sqrt (2 * c / R) ^ 2 / 2 := by
    rw [← hPa]; ring
  rw [hcR]
  generalize Real.sqrt (2 * c / R) = a at hPa0 hPa ⊢
  generalize Real.sqrt Real.pi = b at hπ hb0 ⊢
  generalize Real.sqrt 5 = e at he0 ⊢
  generalize (R ^ (5 / 2 : ℝ))⁻¹ = u at hu0 ⊢
  generalize s0 ^ (5 / 4 : ℝ) = t at ht0 ⊢
  rw [hPa, hπ]
  have hK0 : 0 ≤ b ^ 3 * R * u * t / e :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hb0.le 3) hR.le) hu0) ht0) he0.le
  have e1 := sc_alg a b e R u t hPa0 hb0 he0 hR
  have e2 : 2 * b ^ 2 * b / e * (1 + a ^ 2 / 2) * (R * u) * t =
      (2 + a ^ 2) * (b ^ 3 * R * u * t / e) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by linarith) hK0

/-- **`StreamConstAlgebra`** (the θ-free constant). -/
theorem streamConstAlgebra : StreamConstAlgebra := by
  intro R c s0 hR hc hs0
  have hA : 0 ≤ (2 * Real.pi * c * R)⁻¹ := by positivity
  have h1 : 0 ≤ ((2 * Real.pi * c * R)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA _
  have h2 : 0 ≤ Real.sqrt (gapS R s0) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num), ← ENNReal.ofReal_mul h1,
    ← ENNReal.ofReal_mul (mul_nonneg h1 h2),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h1 h2) h3)]
  apply ENNReal.ofReal_le_ofReal
  exact sc_ineq R c s0 hR hc hs0

/-- The squared stream kernel, written out. -/
theorem sa_sq (θ τ : ℝ) (y z : Space) (σ : ℝ) :
    phKerS θ τ y σ z ^ (2 : ℝ) =
      if σ < τ ∧ ϱ z < θ * ϱ y then
        ENNReal.ofReal (Real.exp (σ - τ) / 4) *
          ENNReal.ofReal (sfPhi (ϱ y) (y 2 - Real.exp ((σ - τ) / 2) * z 2))
      else 0 := by
  unfold phKerS
  split_ifs with h
  · have hsq : Real.exp ((σ - τ) / 2) ^ 2 = Real.exp (σ - τ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hx : 0 ≤ Real.exp ((σ - τ) / 2) / 2 := by positivity
    have hK : 0 ≤ (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - Real.exp ((σ - τ) / 2) * z 2) ^ 2))⁻¹ := by
      positivity
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg hK (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two,
      Real.rpow_two, div_pow, hsq]
    unfold sfPhi
    norm_num
  · rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The stream kernel vanishes on the output bin away from the source's radial gap. -/
theorem sa_support (R θ s1 s0 : ℝ) (hR : 0 < R) (hθ : 0 < θ) (hs1 : 0 < s1)
    (τ : ℝ) (y : Space) (σ : ℝ) (z : Space) (hy : y ∈ ybin R s1 s0) (hz : 0 < ϱ z)
    (hnot : ¬ (s1 / θ ^ 2 < age R z)) : phKerS θ τ y σ z = 0 := by
  have hy' : s1 < age R y := by
    simp only [ybin, Set.mem_ofPred_eq, Set.mem_Ioc] at hy
    exact hy.1
  unfold phKerS
  split_ifs with h
  · exfalso
    obtain ⟨-, hzy⟩ := h
    unfold age at hy' hnot
    have hϱ0 : 0 ≤ ϱ y := ϱ_nonneg y
    have hy2 : 0 < ϱ y ^ 2 := by
      by_contra hneg
      have h0 : ϱ y ^ 2 = 0 := le_antisymm (not_lt.1 hneg) (sq_nonneg _)
      rw [h0, div_zero] at hy'
      linarith
    have ha : 0 < ϱ y := by nlinarith
    have hθy : 0 < θ * ϱ y := mul_pos hθ ha
    have hb2 : ϱ z ^ 2 < (θ * ϱ y) ^ 2 := by
      nlinarith [mul_pos (sub_pos.2 hzy) (add_pos hz hθy)]
    have h3 : s1 * ϱ z ^ 2 < s1 * (θ * ϱ y) ^ 2 := mul_lt_mul_of_pos_left hb2 hs1
    have hsa : s1 * ϱ y ^ 2 < R ^ 2 := (lt_div_iff₀ hy2).1 hy'
    have h4 : θ ^ 2 * (s1 * ϱ y ^ 2) < θ ^ 2 * R ^ 2 :=
      mul_lt_mul_of_pos_left hsa (pow_pos hθ 2)
    have key : s1 * ϱ z ^ 2 < R ^ 2 * θ ^ 2 := by nlinarith [h3, h4]
    have hfrac : s1 / θ ^ 2 < R ^ 2 / ϱ z ^ 2 :=
      (div_lt_div_iff₀ (pow_pos hθ 2) (pow_pos hz 2)).2 key
    exact hnot hfrac
  · rfl

/-- The inner `y`-integral of one stream atom over the output bin, for fixed phase `τ`. -/
theorem sa_inner (R θ s1 s0 : ℝ) (hR : 0 < R) (hθ : 0 < θ) (hs1 : 0 < s1) (hs1s0 : s1 ≤ s0)
    (σ τ : ℝ) (z : Space) :
    ∫⁻ y in ybin R s1 s0, phKerS θ τ y σ z ^ (2 : ℝ) ≤
      (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0) *
        ENNReal.ofReal (gapS R s0) := by
  have hs0 : 0 < s0 := lt_of_lt_of_le hs1 hs1s0
  have hybin : MeasurableSet (ybin R s1 s0) := by
    have hag : Measurable (fun y : Space => age R y) := by
      unfold age
      exact measurable_const.div (measurable_ϱ.pow_const 2)
    exact hag measurableSet_Ioc
  by_cases hστ : σ < τ
  · rw [if_pos hστ]
    have hpt : ∀ y ∈ ybin R s1 s0, phKerS θ τ y σ z ^ (2 : ℝ) ≤
        ENNReal.ofReal (Real.exp (σ - τ) / 4) *
          ENNReal.ofReal (sfPhi (ϱ y) (y 2 - Real.exp ((σ - τ) / 2) * z 2)) := by
      intro y _
      rw [sa_sq]
      split_ifs
      · exact le_rfl
      · exact zero_le
    have hsub : ybin R s1 s0 ⊆ {y : Space | 0 < age R y ∧ age R y ≤ s0} := by
      intro y hy
      have hy' : s1 < age R y ∧ age R y ≤ s0 := hy
      exact ⟨lt_trans hs1 hy'.1, hy'.2⟩
    calc ∫⁻ y in ybin R s1 s0, phKerS θ τ y σ z ^ (2 : ℝ)
        ≤ ∫⁻ y in ybin R s1 s0, ENNReal.ofReal (Real.exp (σ - τ) / 4) *
            ENNReal.ofReal (sfPhi (ϱ y) (y 2 - Real.exp ((σ - τ) / 2) * z 2)) :=
          setLIntegral_mono' hybin hpt
      _ = ENNReal.ofReal (Real.exp (σ - τ) / 4) * ∫⁻ y in ybin R s1 s0,
            ENNReal.ofReal (sfPhi (ϱ y) (y 2 - Real.exp ((σ - τ) / 2) * z 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (σ - τ) / 4) * ∫⁻ y in {y : Space | 0 < age R y ∧ age R y ≤ s0},
            ENNReal.ofReal (sfPhi (ϱ y) (y 2 - Real.exp ((σ - τ) / 2) * z 2)) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le
      _ ≤ ENNReal.ofReal (Real.exp (σ - τ) / 4) * ENNReal.ofReal (gapS R s0) :=
          mul_le_mul_of_nonneg_left (streamSpatial R s0 (Real.exp ((σ - τ) / 2) * z 2) hR hs0) zero_le
  · rw [if_neg hστ, zero_mul]
    have h0 : ∀ y : Space, phKerS θ τ y σ z ^ (2 : ℝ) = 0 := fun y => by
      rw [sa_sq, if_neg (show ¬ (σ < τ ∧ ϱ z < θ * ϱ y) from fun h => hστ h.1)]
    simp [h0]

/-- The `L²` bound over the product `(0,P] × ybin` of one stream atom. -/
theorem sa_prod (θ R s1 s0 P σ : ℝ) (z : Space) (hR : 0 < R) (hθ : 0 < θ) (hs1 : 0 < s1)
    (hs1s0 : s1 ≤ s0) (hP : 0 < P) :
    ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKerS θ x.1 x.2 σ z ^ (2 : ℝ) ≤
      ENNReal.ofReal (omega2 P σ * gapS R s0) := by
  have hprod : ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKerS θ x.1 x.2 σ z ^ (2 : ℝ) ≤
      ∫⁻ τ in Ioc 0 P, ∫⁻ y in ybin R s1 s0, phKerS θ τ y σ z ^ (2 : ℝ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact lintegral_prod_le _
  have hω : 0 ≤ omega2 P σ := by
    unfold omega2
    split_ifs
    · exact mul_nonneg (by linarith) (le_min zero_le_one (Real.exp_pos σ).le)
    · exact le_rfl
  have hgap : 0 ≤ gapS R s0 := by
    unfold gapS
    positivity
  calc ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKerS θ x.1 x.2 σ z ^ (2 : ℝ)
      ≤ ∫⁻ τ in Ioc 0 P, ∫⁻ y in ybin R s1 s0, phKerS θ τ y σ z ^ (2 : ℝ) := hprod
    _ ≤ ∫⁻ τ in Ioc 0 P,
          (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0) *
            ENNReal.ofReal (gapS R s0) :=
          setLIntegral_mono' measurableSet_Ioc
            (fun τ _ => sa_inner R θ s1 s0 hR hθ hs1 hs1s0 σ τ z)
    _ = (∫⁻ τ in Ioc 0 P, (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0)) *
            ENNReal.ofReal (gapS R s0) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (omega2 P σ) * ENNReal.ofReal (gapS R s0) :=
          mul_le_mul_of_nonneg_right (WYCore.phaseWeight P σ hP) zero_le
    _ = ENNReal.ofReal (omega2 P σ * gapS R s0) := (ENNReal.ofReal_mul hω).symm

/-- **`StreamAtomBound`** (source 5588-5592). -/
theorem streamAtomBound : StreamAtomBound := by
  intro R c θ s1 s0 P G hR hθ hθ1 hs1 hs1s0 hP a
  obtain ⟨σ, z⟩ := a
  dsimp only
  have hs0 : 0 < s0 := lt_of_lt_of_le hs1 hs1s0
  have hω : 0 ≤ omega2 P σ := by
    unfold omega2
    split_ifs
    · exact mul_nonneg (by linarith) (le_min zero_le_one (Real.exp_pos σ).le)
    · exact le_rfl
  have hgap : 0 ≤ gapS R s0 := by
    unfold gapS
    positivity
  have hX := sa_prod θ R s1 s0 P σ z hR hθ hs1 hs1s0 hP
  have hroot : (∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKerS θ x.1 x.2 σ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (gapS R s0) * Real.sqrt (omega2 P σ)) := by
    calc _ ≤ (ENNReal.ofReal (omega2 P σ * gapS R s0)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hX (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (omega2 P σ * gapS R s0)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hω hgap) (by norm_num), Real.sqrt_eq_rpow]
      _ = ENNReal.ofReal (Real.sqrt (gapS R s0) * Real.sqrt (omega2 P σ)) := by
          congr 1
          rw [Real.sqrt_mul hω]
          ring
  have hybin : MeasurableSet (ybin R s1 s0) := by
    have hag : Measurable (fun y : Space => age R y) := by
      unfold age
      exact measurable_const.div (measurable_ϱ.pow_const 2)
    exact hag measurableSet_Ioc
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
        (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) P)).prod hybin
      have hzero : ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, phKerS θ x.1 x.2 σ z ^ (2 : ℝ) = 0 := by
        apply le_antisymm _ zero_le
        calc _ ≤ ∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0, (0 : ℝ≥0∞) :=
              setLIntegral_mono' hmeas (fun x hx => le_of_eq (by
                rw [sa_support R θ s1 s0 hR hθ hs1 x.1 x.2 σ z hx.2 hpos hc,
                  ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]))
          _ = 0 := by simp
      exact le_of_eq (by
        rw [hzero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_zero])

/-- **`StreamAtomBound ∧ StreamConstAlgebra`** (the target of this file). -/
theorem streamAtomBoundConst : StreamAtomBound ∧ StreamConstAlgebra :=
  ⟨streamAtomBound, streamConstAlgebra⟩

end UnforcedLeray.Short.PartIIIb.Concrete.WYStream

end
