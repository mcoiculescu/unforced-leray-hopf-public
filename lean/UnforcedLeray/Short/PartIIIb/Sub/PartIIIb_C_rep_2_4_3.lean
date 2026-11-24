import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_fub

/-!
# `PartIII-b:C/rep/2/4/3` : Hölder over the old disk (`VprofHolder`)

Source `the November 2 reference manuscript` 5219-5221 (Hölder with the conjugate
exponent `22/3` of `p = 22/19`, area `π r_o²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem measurable_slab (s : ℝ) : Measurable fun q : ℝ × ℝ => (!₂[q.1, q.2, s] : Space) := by
  have : Continuous fun q : ℝ × ℝ => (!₂[q.1, q.2, s] : Space) := by fun_prop
  exact this.measurable

/-- Hölder on one horizontal slice. -/
theorem slice_holder (G : Space → ℝ≥0∞) (hG : Measurable G) (r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ z, r < ϱ z → G z = 0) (s : ℝ) :
    ∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s] ≤
      ENNReal.ofReal ((Real.pi * r ^ 2) ^ (3 / 22 : ℝ)) *
        (∫⁻ q : ℝ × ℝ, G !₂[q.1, q.2, s] ^ (22 / 19 : ℝ)) ^ (19 / 22 : ℝ) := by
  set Gs : ℝ × ℝ → ℝ≥0∞ := fun q => G !₂[q.1, q.2, s] with hGs
  have hGsm : Measurable Gs := hG.comp (measurable_slab s)
  set D : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2} with hD
  have hDm : MeasurableSet D := measurableSet_le (by fun_prop) measurable_const
  have h1 : ∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s] = ∫⁻ q : ℝ × ℝ, (Gs * D.indicator (1 : ℝ × ℝ → ℝ≥0∞)) q := by
    rw [Measure.volume_eq_prod, lintegral_prod _ (hGsm.mul (measurable_one.indicator hDm : Measurable (D.indicator (1 : ℝ × ℝ → ℝ≥0∞)))).aemeasurable]
    refine lintegral_congr fun x => lintegral_congr fun y => ?_
    simp only [Pi.mul_apply, hGs]
    by_cases hq : (x, y) ∈ D
    · simp [Set.indicator_of_mem hq]
    · have : r < ϱ !₂[x, y, s] := by
        unfold ϱ
        have hq' : r ^ 2 < x ^ 2 + y ^ 2 := by simpa [hD] using hq
        simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact (Real.lt_sqrt hr).2 hq'
      simp [Set.indicator_of_notMem hq, hs _ this]
  have hconj : (22 / 19 : ℝ).HolderConjugate (22 / 3) := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have hk : (∫⁻ q : ℝ × ℝ, (D.indicator (1 : ℝ × ℝ → ℝ≥0∞) q) ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ)) =
      ENNReal.ofReal ((Real.pi * r ^ 2) ^ (3 / 22 : ℝ)) := by
    have e : (fun q : ℝ × ℝ => (D.indicator (1 : ℝ × ℝ → ℝ≥0∞) q) ^ (22 / 3 : ℝ)) =
        D.indicator 1 := by
      funext q
      by_cases hq : q ∈ D
      · simp [Set.indicator_of_mem hq]
      · simp [Set.indicator_of_notMem hq]
    rw [e, lintegral_indicator_one hDm, hD, volume_disk r hr,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    norm_num
  rw [h1]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hGsm.aemeasurable
    (measurable_one.indicator hDm).aemeasurable).trans (le_of_eq ?_)
  rw [hk, mul_comm]
  norm_num
  rfl

/-- Hölder on `Space`, then integration in the vertical variable. -/
theorem slab_holder (G : Space → ℝ≥0∞) (hG : Measurable G) (r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ z, r < ϱ z → G z = 0) :
    (∫⁻ s : ℝ, (∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s]) ^ (22 / 19 : ℝ)) ^ (19 / 22 : ℝ) ≤
      ENNReal.ofReal ((Real.pi * r ^ 2) ^ (3 / 22 : ℝ)) *
        (∫⁻ z : Space, G z ^ (22 / 19 : ℝ)) ^ (19 / 22 : ℝ) := by
  set A := ENNReal.ofReal ((Real.pi * r ^ 2) ^ (3 / 22 : ℝ)) with hA
  set F : Space → ℝ≥0∞ := fun z => G z ^ (22 / 19 : ℝ) with hF
  have hFm : Measurable F := hG.pow_const _
  have hint : ∫⁻ s : ℝ, (∫⁻ q : ℝ × ℝ, F !₂[q.1, q.2, s]) = ∫⁻ z : Space, F z := by
    rw [lintegral_space_xys F hFm]
    have := lintegral_xys_swap (fun t => F !₂[t.1, t.2.1, t.2.2])
      (hFm.comp (by
        have : Continuous fun t : ℝ × ℝ × ℝ => (!₂[t.1, t.2.1, t.2.2] : Space) := by fun_prop
        exact this.measurable))
    simp only at this
    rw [this]
    refine lintegral_congr fun s => ?_
    rw [Measure.volume_eq_prod, lintegral_prod (fun q : ℝ × ℝ => F !₂[q.1, q.2, s]) ((hFm.comp (measurable_slab s)).aemeasurable)]
  have hpt : ∀ s : ℝ, (∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s]) ^ (22 / 19 : ℝ) ≤
      A ^ (22 / 19 : ℝ) * ∫⁻ q : ℝ × ℝ, F !₂[q.1, q.2, s] := by
    intro s
    have h := slice_holder G hG r hr hs s
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 22 / 19)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at h2
    norm_num at h2
    simpa [hF] using h2
  calc (∫⁻ s : ℝ, (∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s]) ^ (22 / 19 : ℝ)) ^ (19 / 22 : ℝ)
      ≤ (∫⁻ s : ℝ, A ^ (22 / 19 : ℝ) * ∫⁻ q : ℝ × ℝ, F !₂[q.1, q.2, s]) ^ (19 / 22 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by norm_num)
    _ = A * (∫⁻ z : Space, G z ^ (22 / 19 : ℝ)) ^ (19 / 22 : ℝ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          ENNReal.ofReal_ne_top)]
        have := hint
        simp only [hF] at this
        rw [this, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num [hA]

theorem vprofHolder : VprofHolder := by
  intro r P hr hP g hg hsupp
  set A := ENNReal.ofReal ((Real.pi * r ^ 2) ^ (3 / 22 : ℝ)) with hA
  have hmeas : ∀ τ, Measurable (g τ) := fun τ => hg.comp (measurable_const.prodMk measurable_id)
  have hpt : ∀ τ : ℝ, (∫⁻ s : ℝ, vprof g τ s ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) ≤
      A ^ (2 : ℝ) * (∫⁻ y : Space, g τ y ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) := by
    intro τ
    have h := slab_holder (g τ) (hmeas τ) r hr (hsupp τ)
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
    have e : (19 / 22 : ℝ) * 2 = 2 / (22 / 19 : ℝ) := by norm_num
    rw [e] at h2
    exact h2
  unfold ltauLq1 IIIa.ltauLq
  calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, (∫⁻ s : ℝ, vprof g τ s ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ^
        (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, A ^ (2 : ℝ) *
          (∫⁻ y : Space, g τ y ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (lintegral_mono hpt)) (by norm_num)
    _ = A * ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
          (∫⁻ y : Space, g τ y ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ^ (1 / 2 : ℝ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          ENNReal.ofReal_ne_top), mul_left_comm, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul]
        norm_num [hA]

end UnforcedLeray.Short.PartIIIb.Concrete
