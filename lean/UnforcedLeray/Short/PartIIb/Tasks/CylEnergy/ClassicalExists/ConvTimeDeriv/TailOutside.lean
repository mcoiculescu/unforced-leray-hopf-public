import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4_3.SmallTime
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.QuotInner

/-!


Source: `the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
On `r ≤ τ - 2h/ν` (`h = |t-τ|`) the age `v = ν(τ-r) ≥ 2h`.  If `v ≥ 2νh` the two ages are
comparable and the mean value theorem with `ConvTD_A` and `HeatWBounds` gives
`|diff| ≤ ν h · 4e^Λ(1 + (v/2)^{-1/2}) B`; if `v < 2νh` the small-time estimate gives
`|diff| ≤ 2MB √(3νh) ≲ h v^{-1/2}`.  In both cases `|diff| ≤ h K (1 + v^{-1/2})`, a majorant whose
integral over `(τ-η, τ)` is `O(η^{1/2})`, uniformly in `t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

namespace TOut

lemma rp {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]

lemma half_le {v : ℝ} (hv : 0 < v) : (v / 2) ^ (-(1 / 2 : ℝ)) ≤ 2 * v ^ (-(1 / 2 : ℝ)) := by
  rw [rp (by positivity), rp hv]
  have h4 : Real.sqrt v ≤ 2 * Real.sqrt (v / 2) := by
    have : Real.sqrt (4 * (v / 2)) = 2 * Real.sqrt (v / 2) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← this]
    exact Real.sqrt_le_sqrt (by linarith)
  have hp : 0 < Real.sqrt (v / 2) := Real.sqrt_pos.2 (by positivity)
  have hq : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hp hq]
  nlinarith

lemma dbd {B : ℝ} {g : Pl → ℝ} (hB : 0 ≤ B) (hg : ∀ j : Fin 2, WB B (B0579.pd j g)) (Λ : ℝ)
    {ξ : ℝ} (hξ : 0 < ξ) (hξΛ : ξ ≤ Λ) (x : Pl) :
    |∑ i : Fin 2, heatSGd i ξ (B0579.pd i g) x| ≤
      4 * Real.exp Λ * (1 + ξ ^ (-(1 / 2 : ℝ))) * B := by
  have hpow0 : 0 ≤ ξ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hξ.le _
  have hE : Real.exp ξ ≤ Real.exp Λ := Real.exp_le_exp.2 hξΛ
  have hc : 1 ≤ Real.cosh x.2 := Real.one_le_cosh _
  have hbi : ∀ i : Fin 2, |heatSGd i ξ (B0579.pd i g) x| ≤
      2 * Real.exp Λ * (1 + ξ ^ (-(1 / 2 : ℝ))) * B := by
    intro i
    have h := (heatWBounds B (B0579.pd i g) (hg i)).2 ξ hξ i x
    have habs : |heatSGd i ξ (B0579.pd i g) x| ≤
        |heatSGd i ξ (B0579.pd i g) x| * Real.cosh x.2 :=
      le_mul_of_one_le_right (abs_nonneg _) hc
    have hmono := CTDIn.mono_prod (A := Real.exp ξ) (A' := Real.exp Λ)
      (P := 1 + ξ ^ (-(1 / 2 : ℝ))) (P' := 1 + ξ ^ (-(1 / 2 : ℝ)))
      (B := B) (Real.exp_pos ξ).le hE (by linarith) le_rfl hB
    linarith
  rw [Fin.sum_univ_two]
  calc |heatSGd 0 ξ (B0579.pd 0 g) x + heatSGd 1 ξ (B0579.pd 1 g) x|
      ≤ |heatSGd 0 ξ (B0579.pd 0 g) x| + |heatSGd 1 ξ (B0579.pd 1 g) x| := abs_add_le _ _
    _ ≤ _ := by linarith [hbi 0, hbi 1]

/-- Pointwise estimate for the outside region. -/
lemma ptwise {ν M B Λ h u v : ℝ} {g : Pl → ℝ} {x : Pl} (hν : 0 < ν) (hM0 : 0 ≤ M) (hB : 0 ≤ B)
    (hg : ContDiff ℝ 1 g) (hW : WB B g) (hW1 : ∀ j : Fin 2, WB B (B0579.pd j g))
    (hMs : ∀ (a : ℝ) (x : Pl), |heatSG a g x - g x| ≤ M * B * Real.sqrt (max a 0))
    (hh : 0 < h) (hv : 2 * h ≤ v) (hvΛ : v ≤ Λ) (huΛ : u ≤ Λ) (huv : |u - v| = ν * h) :
    |heatSG u g x - heatSG v g x| ≤
      h * (8 * ν * Real.exp Λ * B + 2 * M * B * (Real.sqrt (3 * ν) * Real.sqrt (2 * ν))) *
        (1 + v ^ (-(1 / 2 : ℝ))) := by
  have hv0 : 0 < v := by linarith
  have hs0 : 0 ≤ v ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hv0.le _
  have hE : 0 < Real.exp Λ := Real.exp_pos Λ
  have hu1 := abs_le.1 (le_of_eq huv)
  by_cases hcase : 2 * ν * h ≤ v
  · -- comparable ages
    have hu2 : v / 2 ≤ u := by nlinarith [hu1.1, hu1.2]
    have hmv : ∀ ξ ∈ Set.uIcc u v, v / 2 ≤ ξ ∧ ξ ≤ Λ := by
      intro ξ hξ
      rcases Set.mem_uIcc.1 hξ with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    have hmain := CTDIn.mvt_bd (φ := fun b : ℝ => heatSG b g x)
      (φ' := fun ξ => ∑ i : Fin 2, heatSGd i ξ (B0579.pd i g) x)
      (M := 4 * Real.exp Λ * (1 + 2 * v ^ (-(1 / 2 : ℝ))) * B) (u := u) (v := v)
      (fun ξ hξ => convTD_A B g hg hW hW1 ξ (by linarith [(hmv ξ hξ).1]) x)
      (fun ξ hξ => by
        have h1 := dbd hB hW1 Λ (ξ := ξ) (by linarith [(hmv ξ hξ).1]) (hmv ξ hξ).2 x
        have hp : ξ ^ (-(1 / 2 : ℝ)) ≤ (v / 2) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (hmv ξ hξ).1 (by norm_num)
        have hp2 := half_le hv0
        have : 4 * Real.exp Λ * (1 + ξ ^ (-(1 / 2 : ℝ))) * B ≤
            4 * Real.exp Λ * (1 + 2 * v ^ (-(1 / 2 : ℝ))) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
        exact h1.trans this)
    have hvu : |v - u| = ν * h := by rw [abs_sub_comm]; exact huv
    rw [hvu] at hmain
    calc |heatSG u g x - heatSG v g x| = |heatSG v g x - heatSG u g x| := abs_sub_comm _ _
      _ ≤ 4 * Real.exp Λ * (1 + 2 * v ^ (-(1 / 2 : ℝ))) * B * (ν * h) := hmain
      _ ≤ h * (8 * ν * Real.exp Λ * B) * (1 + v ^ (-(1 / 2 : ℝ))) := by
          have : 0 ≤ ν * h * Real.exp Λ * B := by positivity
          nlinarith [mul_nonneg this hs0]
      _ ≤ _ := by
          have h1 : 0 ≤ 2 * M * B * (Real.sqrt (3 * ν) * Real.sqrt (2 * ν)) := by positivity
          have h2 : 0 ≤ 1 + v ^ (-(1 / 2 : ℝ)) := by linarith
          nlinarith [mul_nonneg (mul_nonneg hh.le h1) h2]
  · -- small-time regime
    have hlt : v < 2 * ν * h := not_le.1 hcase
    have hu3 : u ≤ 3 * ν * h := by nlinarith [hu1.1, hu1.2]
    have e1 := hMs u x
    have e2 := hMs v x
    have hmu : max u 0 ≤ 3 * ν * h := max_le hu3 (by positivity)
    have hmv' : max v 0 ≤ 3 * ν * h := max_le (by linarith) (by positivity)
    have s1 : Real.sqrt (max u 0) ≤ Real.sqrt (3 * ν) * Real.sqrt h := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by linarith)
    have s2 : Real.sqrt (max v 0) ≤ Real.sqrt (3 * ν) * Real.sqrt h := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsq : Real.sqrt h ≤ Real.sqrt (2 * ν) * h * v ^ (-(1 / 2 : ℝ)) := by
      rw [rp hv0]
      have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
      have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
      have hvv : Real.sqrt v ≤ Real.sqrt (2 * ν) * Real.sqrt h := by
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt (by linarith)
      have hhh : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
      rw [← div_eq_mul_inv, le_div_iff₀ hsv]
      calc Real.sqrt h * Real.sqrt v ≤ Real.sqrt h * (Real.sqrt (2 * ν) * Real.sqrt h) :=
            mul_le_mul_of_nonneg_left hvv hsh.le
        _ = Real.sqrt (2 * ν) * (Real.sqrt h * Real.sqrt h) := by ring
        _ = Real.sqrt (2 * ν) * h := by rw [hhh]
    calc |heatSG u g x - heatSG v g x|
        = |(heatSG u g x - g x) - (heatSG v g x - g x)| := by congr 1; ring
      _ ≤ |heatSG u g x - g x| + |heatSG v g x - g x| := abs_sub _ _
      _ ≤ M * B * (Real.sqrt (3 * ν) * Real.sqrt h) + M * B * (Real.sqrt (3 * ν) * Real.sqrt h) :=
          add_le_add (e1.trans (mul_le_mul_of_nonneg_left s1 (by positivity)))
            (e2.trans (mul_le_mul_of_nonneg_left s2 (by positivity)))
      _ ≤ 2 * M * B * Real.sqrt (3 * ν) * (Real.sqrt (2 * ν) * h * v ^ (-(1 / 2 : ℝ))) := by
          have : 0 ≤ 2 * M * B * Real.sqrt (3 * ν) := by positivity
          calc _ = 2 * M * B * Real.sqrt (3 * ν) * Real.sqrt h := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hsq this
      _ ≤ _ := by
          have h1 : 0 ≤ 8 * ν * Real.exp Λ * B := by positivity
          have h3 : 0 ≤ 2 * M * B * (Real.sqrt (3 * ν) * Real.sqrt (2 * ν)) := by positivity
          have h4 : 0 ≤ h * (8 * ν * Real.exp Λ * B) * (1 + v ^ (-(1 / 2 : ℝ))) := by positivity
          have e : 2 * M * B * Real.sqrt (3 * ν) * (Real.sqrt (2 * ν) * h * v ^ (-(1 / 2 : ℝ)))
              = h * (2 * M * B * (Real.sqrt (3 * ν) * Real.sqrt (2 * ν))) * v ^ (-(1 / 2 : ℝ)) := by
            ring
          rw [e]
          nlinarith [mul_nonneg (mul_nonneg hh.le h3) hs0, mul_nonneg hh.le h3,
            mul_nonneg (mul_nonneg hh.le h1) (add_nonneg zero_le_one hs0)]

end TOut

theorem convTD_Tail_Outside : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Tail_Outside := by
  intro ν s T hν hsT B F hF hb τ hτ x ε hε
  obtain ⟨M, hM0, hM⟩ := heatSG_small_time_sqrt
  have hB : 0 ≤ B := by
    have h0 := (hb s ⟨le_rfl, hsT⟩).1 0
    simp only [Prod.snd_zero, Real.cosh_zero, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  set Λ := ν * (T - s) with hΛ
  set K := 8 * ν * Real.exp Λ * B + 2 * M * B * (Real.sqrt (3 * ν) * Real.sqrt (2 * ν)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  set c := ν ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hν.le _
  have hD : 0 < K * (1 + 2 * c) + 1 := by positivity
  have hpos : 0 < (ε / (K * (1 + 2 * c) + 1)) ^ 2 := by positivity
  refine ⟨min 1 ((ε / (K * (1 + 2 * c) + 1)) ^ 2), lt_min one_pos hpos, ?_⟩
  intro η hη hηle t ht htne
  have hη1 : η ≤ 1 := hηle.trans (min_le_left _ _)
  have hη2 : η ≤ (ε / (K * (1 + 2 * c) + 1)) ^ 2 := hηle.trans (min_le_right _ _)
  have hsη : Real.sqrt η ≤ ε / (K * (1 + 2 * c) + 1) := by
    rw [Real.sqrt_le_left (by positivity)]; exact hη2
  have hηs : η ≤ Real.sqrt η := by
    have := Real.sqrt_le_sqrt hη1
    have h1 : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη.le
    have h2 : Real.sqrt η ≤ 1 := by simpa using this
    nlinarith [Real.sqrt_nonneg η]
  have hh : 0 < |t - τ| := abs_pos.2 (sub_ne_zero.2 htne)
  set h := |t - τ| with hhdef
  set a := max s (τ - η) with ha
  set b := max a (τ - 2 * h / ν) with hbdef
  have hsa : s ≤ a := le_max_left _ _
  have haτ : a ≤ τ := max_le hτ.1 (by linarith)
  have hab : a ≤ b := le_max_left _ _
  rcases hab.eq_or_lt with heq | hlt
  · rw [← heq]; simp [hε.le]
  have hb' : b = τ - 2 * h / ν := by
    rcases le_max_iff.1 (le_refl b) with h1 | h1
    · exact absurd h1 (not_le.2 hlt)
    · exact le_antisymm h1 (le_max_right _ _)
  have h2ν : 0 < 2 * h / ν := by positivity
  have hbτ : b ≤ τ := by linarith
  have hτb : τ - b = 2 * h / ν := by linarith
  -- pointwise bound
  have hpt : ∀ r ∈ Set.uIoc a b,
      ‖heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x‖ ≤
        h * K * (1 + c * (τ - r) ^ (-(1 / 2 : ℝ))) := by
    intro r hr
    rw [Set.uIoc_of_le hab] at hr
    obtain ⟨hr1, hr2⟩ := hr
    have hrF : r ∈ Icc s T := ⟨hsa.trans hr1.le, hr2.trans (hbτ.trans hτ.2)⟩
    have hFr := hF.c1 r hrF
    obtain ⟨hw, hw1⟩ := hb r hrF
    have hτr : 0 < τ - r := by linarith
    have hv : 2 * h ≤ ν * (τ - r) := by
      have : 2 * h / ν ≤ τ - r := by linarith
      rw [div_le_iff₀ hν] at this
      linarith
    have hvΛ : ν * (τ - r) ≤ Λ := by
      rw [hΛ]; exact mul_le_mul_of_nonneg_left (by linarith [hrF.1, hτ.2]) hν.le
    have huΛ : ν * (t - r) ≤ Λ := by
      rw [hΛ]; exact mul_le_mul_of_nonneg_left (by linarith [hrF.1, ht.2]) hν.le
    have huv : |ν * (t - r) - ν * (τ - r)| = ν * h := by
      rw [← mul_sub, abs_mul, abs_of_pos hν]; congr 1; congr 1; ring
    have key := TOut.ptwise (g := F r) (x := x) hν hM0 hB hFr hw hw1
      (fun a' x' => hM B (F r) hFr hw hw1 a' x') hh hv hvΛ huΛ huv
    rw [Real.norm_eq_abs]
    refine key.trans ?_
    have hmul : (ν * (τ - r)) ^ (-(1 / 2 : ℝ)) = c * (τ - r) ^ (-(1 / 2 : ℝ)) :=
      Real.mul_rpow hν.le hτr.le
    rw [hmul]
  -- integrability of the majorant
  have hint0 : IntervalIntegrable (fun r : ℝ => (τ - r) ^ (-(1 / 2 : ℝ))) volume a b := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := τ - a) (b := τ - b)
      (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left τ
    simpa using this
  have hgint : IntervalIntegrable
      (fun r : ℝ => h * K * (1 + c * (τ - r) ^ (-(1 / 2 : ℝ)))) volume a b :=
    (intervalIntegrable_const.add (hint0.const_mul c)).const_mul (h * K)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
    (ae_of_all _ fun r hr => hpt r (by rwa [Set.uIoc_of_le hab])) hgint
  -- the integral of the majorant
  have hI : ∫ r in a..b, (τ - r) ^ (-(1 / 2 : ℝ)) ≤ 2 * Real.sqrt η := by
    rw [intervalIntegral.integral_comp_sub_left (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) τ]
    rw [integral_rpow (Or.inl (by norm_num))]
    have hb0 : 0 ≤ τ - b := by linarith
    have h1 : 0 ≤ (τ - b) ^ (-(1 / 2 : ℝ) + 1) := Real.rpow_nonneg hb0 _
    have h2 : (τ - a) ^ (-(1 / 2 : ℝ) + 1) ≤ Real.sqrt η := by
      rw [Real.sqrt_eq_rpow]
      have : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
      rw [this]
      exact Real.rpow_le_rpow (by linarith) (by
        have : τ - η ≤ a := le_max_right _ _
        linarith) (by norm_num)
    have e : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
    rw [e] at h1 h2 ⊢
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hlen : b - a ≤ η := by
    have : τ - η ≤ a := le_max_right _ _
    linarith
  have hGint : ∫ r in a..b, h * K * (1 + c * (τ - r) ^ (-(1 / 2 : ℝ)))
      ≤ h * K * (η + c * (2 * Real.sqrt η)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const (hint0.const_mul c),
      intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left hI hc0
    linarith
  rw [Real.norm_eq_abs] at hnorm
  rw [abs_mul, abs_inv]
  have hfin : h⁻¹ * |∫ r in a..b, (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)|
      ≤ h⁻¹ * (h * K * (η + c * (2 * Real.sqrt η))) :=
    mul_le_mul_of_nonneg_left (hnorm.trans hGint) (by positivity)
  have hsimp : h⁻¹ * (h * K * (η + c * (2 * Real.sqrt η))) = K * (η + c * (2 * Real.sqrt η)) := by
    field_simp
  rw [hsimp] at hfin
  have hfin2 : K * (η + c * (2 * Real.sqrt η)) ≤ K * (1 + 2 * c) * Real.sqrt η := by
    have : η + c * (2 * Real.sqrt η) ≤ (1 + 2 * c) * Real.sqrt η := by nlinarith [Real.sqrt_nonneg η]
    calc _ ≤ K * ((1 + 2 * c) * Real.sqrt η) := mul_le_mul_of_nonneg_left this hK0
      _ = _ := by ring
  have hfin3 : K * (1 + 2 * c) * Real.sqrt η ≤ ε := by
    have h1 : K * (1 + 2 * c) * Real.sqrt η ≤ K * (1 + 2 * c) * (ε / (K * (1 + 2 * c) + 1)) :=
      mul_le_mul_of_nonneg_left hsη (by positivity)
    have h2 : K * (1 + 2 * c) * (ε / (K * (1 + 2 * c) + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hD]
      nlinarith
    exact h1.trans h2
  exact hfin.trans (hfin2.trans hfin3)

end UnforcedLeray.Short.IIb.CylPDE
