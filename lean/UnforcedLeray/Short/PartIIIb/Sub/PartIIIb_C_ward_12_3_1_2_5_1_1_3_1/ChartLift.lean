import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ChartJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.LiftFactor
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg

/-!
# `ChartLiftJets` (organizer task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1/1`)

Source `the November 2 reference manuscript`,
lines 1206-1222 (ring lift), 2542-2546 (chart-to-Cartesian comparison).

`Nv R b τ y = liftFactor R y (b (chart R τ y))` off the axis. Leibniz (`norm_iteratedFDerivWithin_clm_apply`)
splits the `k`-th derivative into jets of `liftFactor` (`LiftFactorJet`) and of `b ∘ chart`, the latter by
Faà di Bruno (`norm_iteratedFDerivWithin_comp_le`) with the chart jets (`ChartJetBound`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem clf_chart_contDiffOn (R τ : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (Axi.chart R τ) Axi.axisᶜ := by
  have hA : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => R ^ 2 / Axi.ϱ z ^ 2) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2) (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
  have hAge : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ := hA
  have hLog : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => Real.log (Axi.age R z)) Axi.axisᶜ :=
    ContDiffOn.log hAge (fun z hz => (Axi.age_pos hR.ne' hz).ne')
  have hPhase : ContDiffOn ℝ ∞
      (fun z : UnforcedLeray.Space => R * τ / 2 - (R / 2) * Real.log (Axi.age R z)) Axi.axisᶜ :=
    contDiffOn_const.sub (contDiffOn_const.mul hLog)
  have hTrans : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => R * z 2 / Axi.ϱ z) Axi.axisᶜ :=
    ((show ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => R * z 2) by fun_prop).contDiffOn).div
      Axi.contDiffOn_ϱ (fun z hz => Axi.ϱ_ne_zero hz)
  exact hAge.prodMk (hPhase.prodMk hTrans)

theorem clf_chart_mapsTo (R τ : ℝ) (hR : 0 < R) :
    Set.MapsTo (Axi.chart R τ) Axi.axisᶜ {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
  fun z hz => Axi.age_pos hR.ne' hz

theorem clf_lift_contDiffOn (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (liftFactor R) Axi.axisᶜ := by
  have hR0 : R ≠ 0 := hR.ne'
  have hA : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => R ^ 2 / Axi.ϱ y ^ 2) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
      (fun y hy => pow_ne_zero 2 (Axi.ϱ_ne_zero hy))
  have hAge : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ := hA
  have hFr : ContDiffOn ℝ ∞ Axi.frameL Axi.axisᶜ := by
    show ContDiffOn ℝ ∞
      (fun y : UnforcedLeray.Space =>
        (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).smulRight (Axi.eR y) +
          (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).smulRight Axi.e3) Axi.axisᶜ
    exact (contDiffOn_const.smulRight Axi.contDiffOn_eR).add
      (contDiffOn_const.smulRight contDiffOn_const)
  have hS : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => √(Axi.age R y)) Axi.axisᶜ :=
    ContDiffOn.sqrt hAge (fun y hy => (Axi.age_pos hR0 hy).ne')
  unfold liftFactor
  exact hS.smul hFr

theorem clf_rpow (x : ℝ) (hx : 0 ≤ x) (i : ℕ) :
    x ^ (-(1 + (i : ℝ))) = (x ^ (1 + i))⁻¹ := by
  rw [Real.rpow_neg hx, show (1 + (i : ℝ)) = ((1 + i : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

theorem clf_inv_mul (x : ℝ) (i j k : ℕ) (h : 1 + i + j = 1 + k) :
    (x ^ (1 + i))⁻¹ * (x ^ j)⁻¹ = (x ^ (1 + k))⁻¹ := by
  rw [← mul_inv, ← pow_add, h]

theorem clf_choose_fact (k i : ℕ) (hk : k ≤ 3) (hi : i ≤ k) :
    k.choose i * (k - i).factorial ≤ 48 := by
  interval_cases k <;> interval_cases i <;> first | decide | norm_num [Nat.choose, Nat.factorial]

/-- Faà di Bruno for `b ∘ chart` on the axis complement, orders `j ≤ 3`. -/
theorem clf_comp_jet (R : ℝ) (hR : 0 < R) (K : ℝ)
    (hKb : ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y →
      ∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤ (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m)
    (b : ℝ × (ℝ × ℝ) → Axi.Merid) (hb : ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (τ : ℝ) (y : UnforcedLeray.Space) (hy : R ≤ Axi.ϱ y) (j : ℕ) (hj : j ≤ 3) (C : ℝ)
    (hC : ∀ l : ℕ, l ≤ j → ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ j (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
      (j.factorial : ℝ) * C * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ j := by
  have hyax : y ∉ Axi.axis := by
    intro h
    rw [Axi.mem_axis_iff] at h
    linarith
  have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
  have hT : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} := isOpen_lt continuous_const continuous_fst
  have hmaps := clf_chart_mapsTo R τ hR
  have hxT : Axi.chart R τ y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hmaps hyS
  have hCb : ∀ i : ℕ, i ≤ j →
      ‖iteratedFDerivWithin ℝ i b {m : ℝ × (ℝ × ℝ) | 0 < m.1} (Axi.chart R τ y)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hT hxT]
    exact hC i hi
  have hDb : ∀ i : ℕ, 1 ≤ i → i ≤ j →
      ‖iteratedFDerivWithin ℝ i (Axi.chart R τ) Axi.axisᶜ y‖ ≤
        (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ i := by
    intro i h1 hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i Axi.isOpen_compl_axis hyS]
    exact hKb τ y hy i h1 (le_trans hi hj)
  exact norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (N := ∞) hb (clf_chart_contDiffOn R τ hR)
    (hjLe j) hT.uniqueDiffOn Axi.isOpen_compl_axis.uniqueDiffOn hmaps hyS hCb hDb

/-- Leibniz for `Nv R b τ = liftFactor R · (b ∘ chart R τ)` on the axis complement. -/
theorem clf_nv_leib (R : ℝ) (hR : 0 < R) (τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid)
    (hgS : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ)
    (y : UnforcedLeray.Space) (hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖ ≤ ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ := by
  have hNv : Axi.Nv R b τ = fun z => liftFactor R z (b (Axi.chart R τ z)) :=
    funext fun z => Nv_eq_liftFactor R b τ z
  have hW : iteratedFDeriv ℝ k (Axi.Nv R b τ) y =
      iteratedFDerivWithin ℝ k (Axi.Nv R b τ) Axi.axisᶜ y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.Nv R b τ) k Axi.isOpen_compl_axis hyS).symm
  rw [hW, hNv]
  exact norm_iteratedFDerivWithin_clm_apply (N := ∞) (clf_lift_contDiffOn R hR) hgS
    Axi.isOpen_compl_axis.uniqueDiffOn hyS (hjLe k)

theorem chartLiftJets : ChartLiftJets := by
  intro R hR
  obtain ⟨K, hK0, hKb⟩ := chartJetBound R hR
  have hLF : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ m (liftFactor R) y‖ ≤ C * Axi.ϱ y ^ (-(1 + (m : ℝ))) :=
    fun m => liftFactorJet R hR m
  choose Cf hCf0 hCf using hLF
  set A : ℝ := ∑ i ∈ Finset.range 4, Cf i with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => hCf0 i)
  refine ⟨(1 + 48 * A) * (1 + K) ^ 3, mul_pos (by linarith) (pow_pos (by linarith) 3), ?_⟩
  intro b hb τ y hy k hk
  have hyax : y ∉ Axi.axis := by
    intro h
    rw [Axi.mem_axis_iff] at h
    linarith
  have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
  have ht0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have hgS : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
    hb.comp (clf_chart_contDiffOn R τ hR) (clf_chart_mapsTo R τ hR)
  -- the common sum of the chart-point derivatives of `b`
  set Sb : ℝ := ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ with hSbdef
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hCbk : ∀ l : ℕ, l ≤ k → ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ Sb := fun l hl =>
    Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hGj : ∀ j : ℕ, j ≤ k → ‖iteratedFDerivWithin ℝ j (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
      (j.factorial : ℝ) * Sb * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ j := fun j hj =>
    clf_comp_jet R hR K hKb b hb τ y hy j (by omega) Sb (fun l hl => hCbk l (le_trans hl hj))
  have hFi : ∀ i ∈ Finset.range (k + 1),
      ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ ≤ Cf i * Axi.ϱ y ^ (-(1 + (i : ℝ))) := by
    intro i _
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := liftFactor R) i Axi.isOpen_compl_axis hyS]
    exact hCf i y hyax
  -- the common constant `M`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (1 + K) ^ 3 * (1 + |y 2| / Axi.ϱ y) ^ k *
      (Axi.ϱ y ^ (1 + k))⁻¹ * Sb := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ (Axi.ϱ y ^ (1 + k))⁻¹ := inv_nonneg.2 (pow_nonneg hp.le _)
    positivity
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
        ≤ (48 * Cf i) * M := by
    intro i hi
    have hik : i ≤ k := by have := Finset.mem_range.1 hi; omega
    have h1 := hFi i hi
    have h2 := hGj (k - i) (by omega)
    have hc0 : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
    have hcf := hCf0 i
    have hcj : (k.choose i : ℝ) * ((k - i).factorial : ℝ) ≤ 48 := by
      exact_mod_cast clf_choose_fact k i hk hik
    have hj3 : k - i ≤ 3 := by omega
    have hjk : k - i ≤ k := by omega
    have hrp : 0 ≤ Axi.ϱ y ^ (-(1 + (i : ℝ))) := Real.rpow_nonneg hp.le _
    have hs0 : 0 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
    -- first step: Leibniz product bounded by the explicit expression
    have hstep1 : (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
        (k.choose i : ℝ) * (Cf i * Axi.ϱ y ^ (-(1 + (i : ℝ)))) *
          ((k - i).factorial * Sb * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ (k - i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 (norm_nonneg _)
        (mul_nonneg hc0 (mul_nonneg hcf hrp))
    -- rewrite into the product of the inverses
    have hid : (k.choose i : ℝ) * (Cf i * Axi.ϱ y ^ (-(1 + (i : ℝ)))) *
          ((k - i).factorial * Sb * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ (k - i)) =
        ((k.choose i : ℝ) * ((k - i).factorial : ℝ)) * Cf i * Sb *
          (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) * ((Axi.ϱ y ^ (1 + i))⁻¹ * (Axi.ϱ y ^ (k - i))⁻¹) := by
      rw [clf_rpow _ hp.le i, div_pow]
      ring
    have hinv : (Axi.ϱ y ^ (1 + i))⁻¹ * (Axi.ϱ y ^ (k - i))⁻¹ = (Axi.ϱ y ^ (1 + k))⁻¹ :=
      clf_inv_mul _ i (k - i) k (by omega)
    -- the power bound
    have hKs : (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) ≤ (1 + K) ^ 3 * (1 + |y 2| / Axi.ϱ y) ^ k := by
      rw [mul_pow]
      have hKj : K ^ (k - i) ≤ (1 + K) ^ 3 :=
        le_trans (pow_le_pow_left₀ hK0.le (by linarith : K ≤ 1 + K) (k - i))
          (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + K) hj3)
      have hsj : (1 + |y 2| / Axi.ϱ y) ^ (k - i) ≤ (1 + |y 2| / Axi.ϱ y) ^ k :=
        pow_le_pow_right₀ hs1 hjk
      exact mul_le_mul hKj hsj (pow_nonneg hs0 _) (by positivity)
    have hW0 : 0 ≤ Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹ := by
      have : 0 ≤ (Axi.ϱ y ^ (1 + k))⁻¹ := inv_nonneg.2 (pow_nonneg hp.le _)
      exact mul_nonneg (mul_nonneg hcf hSb0) this
    have hKs0 : 0 ≤ (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) :=
      pow_nonneg (mul_nonneg hK0.le hs0) _
    calc (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
        ≤ _ := hstep1
      _ = ((k.choose i : ℝ) * ((k - i).factorial : ℝ)) * (Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹) *
            (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) := by
          rw [hid, ← hinv]
          ring
      _ ≤ (48 * (Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹)) * ((1 + K) ^ 3 * (1 + |y 2| / Axi.ϱ y) ^ k) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcj hW0) hKs hKs0 (by positivity)
      _ = (48 * Cf i) * M := by rw [hM]; ring
  -- sum over the Leibniz terms
  have hsum : ∑ i ∈ Finset.range (k + 1), Cf i ≤ A :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun i _ _ => hCf0 i)
  have hfin : (1 + 48 * A) * (1 + K) ^ 3 * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
      (1 + |y 2| / Axi.ϱ y) ^ k * Sb = (1 + 48 * A) * M := by
    rw [clf_rpow _ hp.le k, hM]
    ring
  calc ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ :=
        clf_nv_leib R hR τ b hgS y hyS k
    _ ≤ ∑ i ∈ Finset.range (k + 1), (48 * Cf i) * M := Finset.sum_le_sum hterm
    _ = (48 * ∑ i ∈ Finset.range (k + 1), Cf i) * M := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (48 * A) * M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hM0
    _ ≤ (1 + 48 * A) * M := mul_le_mul_of_nonneg_right (by linarith) hM0
    _ = (1 + 48 * A) * (1 + K) ^ 3 * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          (1 + |y 2| / Axi.ϱ y) ^ k * Sb := hfin.symm

end UnforcedLeray.Short.PartIIIb.Concrete
