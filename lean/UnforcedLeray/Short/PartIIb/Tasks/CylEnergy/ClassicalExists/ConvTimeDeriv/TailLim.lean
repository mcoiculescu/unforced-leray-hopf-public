import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatWBounds

/-!


Source: `the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
On `r ∈ (c, τ)` with `c = max s (τ-η)` the age `a = ν(τ-r)` is positive and the heat-weight bound
`HeatWBounds` gives `|∂_i K_a * ∂_i F(r)(x)| ≤ 2 e^{ν(T-s)} B (1 + (ν(τ-r))^{-1/2})`. Integrating
the majorant over `[c, τ]` (length `≤ η`) gives a bound `C (η + √η)`, which is `≤ ε` for small `η`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

theorem convTD_Tail_Lim : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Tail_Lim := by
  intro ν s T hν hsT B F hF hb τ hτ x ε hε
  have hs0 : s ∈ Icc s T := ⟨le_rfl, hsT⟩
  have hB0 : 0 ≤ B := by
    have h0 := (hb s hs0).1 0
    simp only [Prod.snd_zero, Real.cosh_zero, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (ν * (T - s)) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ν ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact Real.rpow_nonneg hν.le _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * E * B := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg (by linarith) hB0
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * ν * K + 4 * ν * K * N := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL]
    have h1 : 0 ≤ ν * K := mul_nonneg hν.le hK0
    have h2 : 0 ≤ ν * K * N := mul_nonneg h1 hN0
    nlinarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = L + 1 := ⟨_, rfl⟩
  have hQpos : 0 < Q := by rw [hQ]; linarith
  have hLQ : L ≤ Q := by rw [hQ]; linarith
  refine ⟨min 1 ((ε / Q) ^ 2), lt_min one_pos (pow_pos (div_pos hε hQpos) 2), fun η hη hηle => ?_⟩
  have hη1 : η ≤ 1 := le_trans hηle (min_le_left _ _)
  have hηsq : η ≤ (ε / Q) ^ 2 := le_trans hηle (min_le_right _ _)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max s (τ - η) := ⟨_, rfl⟩
  rw [← hc]
  have hsc : s ≤ c := by rw [hc]; exact le_max_left _ _
  have hcτ : c ≤ τ := by rw [hc]; exact max_le hτ.1 (by linarith)
  have hd0 : 0 ≤ τ - c := by linarith
  have hdη : τ - c ≤ η := by
    have : τ - η ≤ c := by rw [hc]; exact le_max_right _ _
    linarith
  have hd1 : τ - c ≤ 1 := by linarith
  -- pointwise majorant on `(c, τ)`, away from the null set `{τ}`
  have hbound : ∀ i : Fin 2, ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc c τ →
      ‖heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x‖ ≤ K + (K * N) * (τ - r) ^ (-(1 / 2 : ℝ)) := by
    intro i
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ τ := by
      rw [ae_iff]; simp
    filter_upwards [hne] with r hrne hr
    have hrI : r ∈ Icc s T := ⟨le_trans hsc (le_of_lt hr.1), le_trans hr.2 hτ.2⟩
    have hrτ : r < τ := lt_of_le_of_ne hr.2 hrne
    have ha : 0 < ν * (τ - r) := mul_pos hν (by linarith)
    have h := (heatWBounds B (B0579.pd i (F r)) ((hb r hrI).2 i)).2 (ν * (τ - r)) ha i x
    have hcosh : 1 ≤ Real.cosh x.2 := Real.one_le_cosh _
    have habs : ‖heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x‖ ≤
        |heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x| * Real.cosh x.2 := by
      rw [Real.norm_eq_abs]; exact le_mul_of_one_le_right (abs_nonneg _) hcosh
    have hE' : Real.exp (ν * (τ - r)) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.2
      exact mul_le_mul_of_nonneg_left (by linarith [hr.1, hsc, hτ.2]) hν.le
    have hrpow : (ν * (τ - r)) ^ (-(1 / 2 : ℝ)) = N * (τ - r) ^ (-(1 / 2 : ℝ)) := by
      rw [hN, Real.mul_rpow hν.le (by linarith)]
    have ht0 : 0 ≤ (τ - r) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hNt : 0 ≤ N * (τ - r) ^ (-(1 / 2 : ℝ)) := mul_nonneg hN0 ht0
    have hP : 0 ≤ 1 + N * (τ - r) ^ (-(1 / 2 : ℝ)) := by linarith
    have hmain : 2 * Real.exp (ν * (τ - r)) * (1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B
        ≤ K + (K * N) * (τ - r) ^ (-(1 / 2 : ℝ)) := by
      rw [hrpow, hK]
      have h1 : 2 * Real.exp (ν * (τ - r)) * (1 + N * (τ - r) ^ (-(1 / 2 : ℝ))) * B
          ≤ 2 * E * (1 + N * (τ - r) ^ (-(1 / 2 : ℝ))) * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hP) hB0
      exact h1.trans (le_of_eq (by ring))
    calc ‖heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x‖
        ≤ |heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x| * Real.cosh x.2 := habs
      _ ≤ 2 * Real.exp (ν * (τ - r)) * (1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B := h
      _ ≤ K + (K * N) * (τ - r) ^ (-(1 / 2 : ℝ)) := hmain
  -- integrals of the majorant
  have hu0 : IntervalIntegrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) volume 0 (τ - c) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hgi : IntervalIntegrable (fun r : ℝ => (τ - r) ^ (-(1 / 2 : ℝ))) volume c τ := by
    have h := hu0.comp_sub_left τ
    rw [sub_zero, sub_sub_cancel] at h
    exact h.symm
  have hI : ∫ r in c..τ, (τ - r) ^ (-(1 / 2 : ℝ)) = 2 * (τ - c) ^ (1 / 2 : ℝ) := by
    have e := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-(1 / 2 : ℝ)))
      (a := c) (b := τ) τ
    simp only [sub_self] at e
    have h0 : (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
    have h1 : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
    rw [e, integral_rpow (Or.inl (by norm_num)), h0, h1]
    ring
  have hgint : ∫ r in c..τ, (K + (K * N) * (τ - r) ^ (-(1 / 2 : ℝ)))
      = K * (τ - c) + (K * N) * (2 * (τ - c) ^ (1 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hgi.const_mul (K * N)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hI, smul_eq_mul]
    ring
  have hmono : ∀ i : Fin 2, |∫ r in c..τ, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x|
      ≤ K * (τ - c) + (K * N) * (2 * (τ - c) ^ (1 / 2 : ℝ)) := by
    intro i
    rw [← hgint]
    have hgi' : IntervalIntegrable (fun r : ℝ => K + (K * N) * (τ - r) ^ (-(1 / 2 : ℝ)))
        volume c τ := intervalIntegrable_const.add (hgi.const_mul (K * N))
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hcτ (hbound i) hgi'
    rwa [Real.norm_eq_abs] at h
  -- conclusion
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (τ - c) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hu] at hmono
  have hu0' : 0 ≤ u := by rw [hu]; exact Real.rpow_nonneg hd0 _
  have hu2 : u ^ 2 = τ - c := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hd0]; norm_num
  have hu1 : u ≤ 1 := by nlinarith
  have hdu : τ - c ≤ u := by nlinarith
  have hQe : 0 ≤ ε / Q := div_nonneg hε.le hQpos.le
  have huQ : u ≤ ε / Q := by nlinarith
  have hA0 := hmono 0
  have hA1 := hmono 1
  rw [Fin.sum_univ_two, abs_mul, abs_of_pos hν]
  refine (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hA0 hA1)) hν.le).trans ?_
  have h2 : K * (τ - c) ≤ K * u := mul_le_mul_of_nonneg_left hdu hK0
  have h4 : ν * (K * (τ - c)) ≤ ν * (K * u) := mul_le_mul_of_nonneg_left h2 hν.le
  calc ν * ((K * (τ - c) + (K * N) * (2 * u)) + (K * (τ - c) + (K * N) * (2 * u)))
      ≤ L * u := by rw [hL]; nlinarith
    _ ≤ Q * u := mul_le_mul_of_nonneg_right hLQ hu0'
    _ ≤ Q * (ε / Q) := mul_le_mul_of_nonneg_left huQ hQpos.le
    _ = ε := by field_simp

end UnforcedLeray.Short.IIb.CylPDE
