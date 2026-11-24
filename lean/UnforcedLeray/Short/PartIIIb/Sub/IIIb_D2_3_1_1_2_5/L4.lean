import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5

/-!
# Periodic block bound (`PartIII-b:IIIb-D2/3/1/1/2/5/4`)

For `P`-periodic `g` with `∫_0^P g² < ∞`, the integral `∫_{-∞}^0 e^{κs} g(τ+2s) ds` is finite.
Proof: `h(s) = g(τ+2s)` is `P/2`-periodic with `∫_0^{P/2} h² < ∞` (affine scaling and a
period shift). Split `(-∞,0)` into blocks `(-(m+1)Q, -mQ]`, `Q = P/2`. On block `m`, `e^{κs} ≤
ρ^m` with `ρ = e^{-κQ} < 1`, and `∫_block h ≤ ∫_block (1 + h²) = Q + ∫_{0}^{Q} h²`. Sum the
geometric series.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Integral over one period of a periodic function does not depend on the window start
(`AddCircle.lintegral_preimage`). -/
theorem l4_shift (P : ℝ) (hP : 0 < P) (f : ℝ → ℝ≥0∞) (hf : ∀ τ, f (τ + P) = f τ) (a : ℝ) :
    ∫⁻ u in Ioc a (a + P), f u = ∫⁻ u in Ioc 0 P, f u := by
  haveI : Fact (0 < P) := ⟨hP⟩
  have hper : Function.Periodic f P := hf
  have key : ∀ t : ℝ, ∫⁻ u in Ioc t (t + P), f u = ∫⁻ b : AddCircle P, hper.lift b := by
    intro t
    have h := AddCircle.lintegral_preimage P t hper.lift
    rw [← h]
    exact lintegral_congr fun u => (hper.lift_coe u).symm
  have h0 : ∫⁻ u in Ioc 0 P, f u = ∫⁻ b : AddCircle P, hper.lift b := by
    simpa using key 0
  rw [key a, h0]

/-- Linear scaling on `ℝ` for lower integrals. -/
theorem l4_scale (H : ℝ → ℝ≥0∞) (hH : Measurable H) (R : ℝ) (hR : 0 < R) :
    ∫⁻ s, H (R * s) = ENNReal.ofReal R⁻¹ * ∫⁻ u, H u := by
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hR.ne'
  rw [Module.finrank_self, pow_one, abs_of_pos (inv_pos.2 hR)] at hmap
  have h1 : ∫⁻ s, H (R * s) = ∫⁻ y, H y ∂(Measure.map (fun x : ℝ => R • x) volume) := by
    rw [lintegral_map hH (measurable_const_smul R)]
    simp only [smul_eq_mul]
  rw [h1, hmap, lintegral_smul_measure, smul_eq_mul]

/-- Translation plus linear scaling on `ℝ`. -/
theorem l4_scale_aff (H : ℝ → ℝ≥0∞) (hH : Measurable H) (c R : ℝ) (hR : 0 < R) :
    ∫⁻ s, H (c + R * s) = ENNReal.ofReal R⁻¹ * ∫⁻ u, H u := by
  have h := l4_scale (fun v => H (v + c)) (hH.comp (measurable_add_const c)) R hR
  calc ∫⁻ s, H (c + R * s) = ∫⁻ s, H (R * s + c) := lintegral_congr fun s => by rw [add_comm]
    _ = ENNReal.ofReal R⁻¹ * ∫⁻ u, H (u + c) := h
    _ = ENNReal.ofReal R⁻¹ * ∫⁻ u, H u := by rw [lintegral_add_right_eq_self H c]

/-- Affine change of variables on a window (`s ↦ c + R s`, `R > 0`). -/
theorem l4_affine (F : ℝ → ℝ≥0∞) (hF : Measurable F) (c R a b : ℝ) (hR : 0 < R) :
    ∫⁻ s in Ioc a b, F (c + R * s) =
      ENNReal.ofReal R⁻¹ * ∫⁻ u in Ioc (c + R * a) (c + R * b), F u := by
  have hI : ∀ s : ℝ, (Ioc a b).indicator (fun s => F (c + R * s)) s =
      (Ioc (c + R * a) (c + R * b)).indicator F (c + R * s) := by
    intro s
    by_cases hs : s ∈ Ioc a b
    · have hs' : c + R * s ∈ Ioc (c + R * a) (c + R * b) := by
        have h1 := mul_lt_mul_of_pos_left hs.1 hR
        have h2 := mul_le_mul_of_nonneg_left hs.2 hR.le
        exact ⟨by linarith, by linarith⟩
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs']
    · have hs' : c + R * s ∉ Ioc (c + R * a) (c + R * b) := by
        rintro ⟨h1, h2⟩
        apply hs
        constructor
        · by_contra hc
          push_neg at hc
          have := mul_le_mul_of_nonneg_left hc hR.le
          linarith
        · by_contra hc
          push_neg at hc
          have := mul_lt_mul_of_pos_left hc hR
          linarith
      rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs']
  have hm : Measurable ((Ioc (c + R * a) (c + R * b)).indicator F) :=
    hF.indicator measurableSet_Ioc
  calc ∫⁻ s in Ioc a b, F (c + R * s)
      = ∫⁻ s, (Ioc a b).indicator (fun s => F (c + R * s)) s :=
        (lintegral_indicator measurableSet_Ioc _).symm
    _ = ∫⁻ s, (Ioc (c + R * a) (c + R * b)).indicator F (c + R * s) :=
        lintegral_congr fun s => hI s
    _ = ENNReal.ofReal R⁻¹ * ∫⁻ u, (Ioc (c + R * a) (c + R * b)).indicator F u :=
        l4_scale_aff _ hm c R hR
    _ = ENNReal.ofReal R⁻¹ * ∫⁻ u in Ioc (c + R * a) (c + R * b), F u := by
        rw [lintegral_indicator measurableSet_Ioc]

/-- Core periodic block estimate. -/
theorem l4_core (Q : ℝ) (hQ : 0 < Q) (h : ℝ → ℝ≥0∞) (hper : ∀ s, h (s + Q) = h s)
    (hfin : ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ) < ⊤) (κ : ℝ) (hκ : 0 < κ) :
    ∫⁻ s in Iio (0 : ℝ), ENNReal.ofReal (Real.exp (κ * s)) * h s < ⊤ := by
  have hpt : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ (2 : ℝ) := by
    intro x
    rcases le_total x 1 with hx | hx
    · exact hx.trans le_self_add
    · calc x = x ^ (1 : ℝ) := (ENNReal.rpow_one x).symm
        _ ≤ x ^ (2 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hx (by norm_num)
        _ ≤ 1 + x ^ (2 : ℝ) := le_add_self
  have hsq : ∀ m : ℕ, ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q), h s ^ (2 : ℝ) =
      ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ) := by
    intro m
    have e : -((m : ℝ) + 1) * Q + Q = -((m : ℝ)) * Q := by ring
    have := l4_shift Q hQ (fun s => h s ^ (2 : ℝ)) (fun s => by simp only [hper])
      (-((m : ℝ) + 1) * Q)
    rw [e] at this
    exact this
  have hblock : ∀ m : ℕ, ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q), h s ≤
      ENNReal.ofReal Q + ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ) := by
    intro m
    have hconst : ∫⁻ _ in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q), (1 : ℝ≥0∞) =
        ENNReal.ofReal Q := by
      rw [setLIntegral_const, Real.volume_Ioc, one_mul]
      congr 1
      ring
    calc ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q), h s
        ≤ ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q), (1 + h s ^ (2 : ℝ)) :=
          lintegral_mono fun s => hpt (h s)
      _ = (∫⁻ _ in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q), (1 : ℝ≥0∞)) +
            ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q), h s ^ (2 : ℝ) :=
          lintegral_add_left measurable_const _
      _ = ENNReal.ofReal Q + ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ) := by rw [hconst, hsq m]
  have hrho : ENNReal.ofReal (Real.exp (-κ * Q)) < 1 :=
    ENNReal.ofReal_lt_one.2 (Real.exp_lt_one_iff.2 (by have := mul_pos hκ hQ; linarith))
  have hcov : Iio (0 : ℝ) ⊆ ⋃ m : ℕ, Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q) := by
    intro s hs
    have hs0 : s < 0 := hs
    have ht0 : 0 ≤ -s / Q := div_nonneg (by linarith) hQ.le
    simp only [mem_iUnion, mem_Ioc]
    refine ⟨⌊-s / Q⌋₊, ?_, ?_⟩
    · have h2 := Nat.lt_floor_add_one (-s / Q)
      have h3 : -s < ((⌊-s / Q⌋₊ : ℝ) + 1) * Q := by rwa [div_lt_iff₀ hQ] at h2
      linarith
    · have h1 := Nat.floor_le ht0
      have h3 : (⌊-s / Q⌋₊ : ℝ) * Q ≤ -s := by rwa [le_div_iff₀ hQ] at h1
      linarith
  have hblk : ∀ m : ℕ, ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q),
      ENNReal.ofReal (Real.exp (κ * s)) * h s ≤
        ENNReal.ofReal (Real.exp (-κ * Q)) ^ m *
          (ENNReal.ofReal Q + ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ)) := by
    intro m
    have hpt2 : ∀ s ∈ Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q),
        ENNReal.ofReal (Real.exp (κ * s)) ≤ ENNReal.ofReal (Real.exp (-κ * Q)) ^ m := by
      intro s hs
      rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have h4 := hs.2
      have h5 : κ * s ≤ κ * (-((m : ℝ)) * Q) := mul_le_mul_of_nonneg_left h4 hκ.le
      linarith
    calc ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q),
          ENNReal.ofReal (Real.exp (κ * s)) * h s
        ≤ ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q),
            ENNReal.ofReal (Real.exp (-κ * Q)) ^ m * h s :=
          setLIntegral_mono' measurableSet_Ioc fun s hs => by
            gcongr
            exact hpt2 s hs
      _ = ENNReal.ofReal (Real.exp (-κ * Q)) ^ m *
            ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q), h s :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      _ ≤ ENNReal.ofReal (Real.exp (-κ * Q)) ^ m *
            (ENNReal.ofReal Q + ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ)) :=
          by
            gcongr
            exact hblock m
  have hB : ENNReal.ofReal Q + ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ) < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hfin⟩
  calc ∫⁻ s in Iio (0 : ℝ), ENNReal.ofReal (Real.exp (κ * s)) * h s
      ≤ ∫⁻ s in ⋃ m : ℕ, Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q),
          ENNReal.ofReal (Real.exp (κ * s)) * h s := lintegral_mono_set hcov
    _ ≤ ∑' m : ℕ, ∫⁻ s in Ioc (-((m : ℝ) + 1) * Q) (-((m : ℝ)) * Q),
          ENNReal.ofReal (Real.exp (κ * s)) * h s := lintegral_iUnion_le _ _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (Real.exp (-κ * Q)) ^ m *
          (ENNReal.ofReal Q + ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ)) := ENNReal.tsum_le_tsum hblk
    _ = (∑' m : ℕ, ENNReal.ofReal (Real.exp (-κ * Q)) ^ m) *
          (ENNReal.ofReal Q + ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ)) := ENNReal.tsum_mul_right
    _ = (1 - ENNReal.ofReal (Real.exp (-κ * Q)))⁻¹ *
          (ENNReal.ofReal Q + ∫⁻ s in Ioc 0 Q, h s ^ (2 : ℝ)) := by
        rw [ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hrho)) hB

theorem l5PerSum : L5PerSum := by
  intro P hP g hg hper hfin κ hκ τ
  have hF2 : Measurable fun u => g u ^ (2 : ℝ) := hg.pow_const 2
  have hpF : ∀ u, g (u + P) ^ (2 : ℝ) = g u ^ (2 : ℝ) := fun u => by rw [hper u]
  apply l4_core (P / 2) (by positivity) (fun s => g (τ + 2 * s))
    (fun s => by
      show g (τ + 2 * (s + P / 2)) = g (τ + 2 * s)
      rw [show τ + 2 * (s + P / 2) = (τ + 2 * s) + P by ring]
      exact hper _) ?_ κ hκ
  show ∫⁻ s in Ioc 0 (P / 2), g (τ + 2 * s) ^ (2 : ℝ) < ⊤
  calc ∫⁻ s in Ioc 0 (P / 2), g (τ + 2 * s) ^ (2 : ℝ)
      = ENNReal.ofReal 2⁻¹ * ∫⁻ u in Ioc (τ + 2 * 0) (τ + 2 * (P / 2)), g u ^ (2 : ℝ) :=
        l4_affine (fun u => g u ^ (2 : ℝ)) hF2 τ 2 0 (P / 2) two_pos
    _ = ENNReal.ofReal 2⁻¹ * ∫⁻ u in Ioc τ (τ + P), g u ^ (2 : ℝ) := by
        rw [show τ + 2 * 0 = τ by ring, show τ + 2 * (P / 2) = τ + P by ring]
    _ = ENNReal.ofReal 2⁻¹ * ∫⁻ u in Ioc 0 P, g u ^ (2 : ℝ) := by
        congr 1
        exact l4_shift P hP (fun u => g u ^ (2 : ℝ)) hpF τ
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end UnforcedLeray.Short.PartIIIb.Concrete
