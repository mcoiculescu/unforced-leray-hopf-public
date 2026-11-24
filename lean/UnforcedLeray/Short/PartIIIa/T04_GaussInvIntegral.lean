import UnforcedLeray.Short.PartIIIa.Targets

/-!
# Part III-a: the Gaussian inverse-power integral (SP 3604-3606)

Proves `gaussInvIntegral : GaussInvIntegral` (`Targets.lean`). For `s > 1` and `r > 0`,
`∫_{(0,∞)} a^{-s} e^{-r²/(8a)} da = r^{2-2s} ∫_{(0,∞)} ρ^{-s} e^{-1/(8ρ)} dρ`, and the
right-hand integral is finite.

1. Scaling (SP 3604-3606, "substitution `a = |x|²r`"): the change of variables `a = r²ρ` on
   `(0,∞)` gives the identity, with Jacobian `r²`, `(r²ρ)^{-s} = r^{-2s}ρ^{-s}`, and
   `r²/(8r²ρ) = 1/(8ρ)`.
2. Finiteness: split `(0,∞) = (0,1] ∪ (1,∞)`. On `(1,∞)` the integrand is at most `ρ^{-s}`,
   integrable since `s > 1`. On `(0,1]`, `e^{-1/(8ρ)} ≤ k!(8ρ)^k` for `k ≥ s`, so the integrand
   is bounded by `k! 8^k`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Change of variables on `(0,∞)`: for `c > 0`, `∫_{(0,∞)} F(a) da = c ∫_{(0,∞)} F(cx) dx`. -/
lemma gInv_scale {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ a in Ioi (0 : ℝ), F a = ENNReal.ofReal c * ∫⁻ x in Ioi (0 : ℝ), F (c * x) := by
  set G : ℝ → ℝ≥0∞ := (Ioi (0 : ℝ)).indicator F with hG
  have hGm : Measurable G := hF.indicator measurableSet_Ioi
  have hmap : Measure.map (fun x : ℝ => c * x) volume = ENNReal.ofReal c⁻¹ • volume := by
    rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.2 hc)]
  have hsmul : ENNReal.ofReal c⁻¹ * ∫⁻ a, G a =
      ∫⁻ a, G a ∂(ENNReal.ofReal c⁻¹ • volume) := by
    rw [lintegral_smul_measure, smul_eq_mul]
  have hsub : ∫⁻ x, G (c * x) = ENNReal.ofReal c⁻¹ * ∫⁻ a, G a := by
    rw [hsmul, ← hmap, lintegral_map hGm (measurable_const_mul c)]
  have hind : ∀ x : ℝ, G (c * x) = (Ioi (0 : ℝ)).indicator (fun y => F (c * y)) x := by
    intro x
    simp only [hG, Set.indicator_apply, Set.mem_Ioi]
    by_cases hx : 0 < x
    · rw [if_pos (mul_pos hc hx), if_pos hx]
    · rw [if_neg (fun h => hx (pos_of_mul_pos_right h hc.le)), if_neg hx]
  have hsub2 : ∫⁻ x, G (c * x) = ∫⁻ x in Ioi (0 : ℝ), F (c * x) := by
    simp_rw [hind]
    exact lintegral_indicator measurableSet_Ioi _
  have hL : ∫⁻ a in Ioi (0 : ℝ), F a = ∫⁻ a, G a :=
    (lintegral_indicator measurableSet_Ioi F).symm
  rw [hL]
  calc ∫⁻ a, G a = ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * ∫⁻ a, G a) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
          one_mul]
    _ = ENNReal.ofReal c * ∫⁻ x, G (c * x) := by rw [hsub]
    _ = ENNReal.ofReal c * ∫⁻ x in Ioi (0 : ℝ), F (c * x) := by rw [hsub2]

/-- `exp(-1/(8ρ)) ≤ k! (8ρ)^k` for `ρ > 0`, from `x^k/k! ≤ e^x` at `x = 1/(8ρ)`. -/
lemma gInv_exp_le (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.exp (-1 / (8 * ρ)) ≤ (Nat.factorial k : ℝ) * (8 * ρ) ^ k := by
  have htpos : 0 < 1 / (8 * ρ) := by positivity
  have hneg : -1 / (8 * ρ) = -(1 / (8 * ρ)) := by ring
  rw [hneg]
  set t : ℝ := 1 / (8 * ρ) with ht
  have ht8 : t * (8 * ρ) = 1 := by
    rw [ht, one_div, inv_mul_cancel₀ (by positivity)]
  have h1 : t ^ k ≤ Real.exp t * (Nat.factorial k : ℝ) := by
    have h := Real.pow_div_factorial_le_exp t htpos.le k
    have hfpos : (0 : ℝ) < (Nat.factorial k : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos k)
    rw [div_le_iff₀ hfpos] at h
    exact h
  have h2 : t ^ k * (8 * ρ) ^ k = 1 := by
    rw [← mul_pow, ht8, one_pow]
  have h3 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  calc Real.exp (-t) = Real.exp (-t) * (t ^ k * (8 * ρ) ^ k) := by rw [h2, mul_one]
    _ = (Real.exp (-t) * t ^ k) * (8 * ρ) ^ k := by ring
    _ ≤ (Real.exp (-t) * (Real.exp t * (Nat.factorial k : ℝ))) * (8 * ρ) ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = (Nat.factorial k : ℝ) * (8 * ρ) ^ k := by
        have hkey : Real.exp (-t) * (Real.exp t * (Nat.factorial k : ℝ)) =
            (Nat.factorial k : ℝ) := by
          rw [← mul_assoc, h3, one_mul]
        rw [hkey]

/-- On `(0,1]` the integrand is bounded by `k! 8^k` with `k = ⌈s⌉₊ ≥ s`. -/
lemma gInv_integrand_le {s : ℝ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ (-s) * Real.exp (-1 / (8 * ρ)) ≤ (Nat.factorial ⌈s⌉₊ : ℝ) * 8 ^ ⌈s⌉₊ := by
  set k : ℕ := ⌈s⌉₊ with hk
  have hsk : s ≤ (k : ℝ) := Nat.le_ceil s
  have hpow : ρ ^ ((k : ℝ) - s) = ρ ^ (k : ℝ) * ρ ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add hρ0]
  have hnat : ρ ^ (k : ℝ) = ρ ^ k := Real.rpow_natCast ρ k
  have hle : ρ ^ ((k : ℝ) - s) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by linarith)
  calc ρ ^ (-s) * Real.exp (-1 / (8 * ρ))
      ≤ ρ ^ (-s) * ((Nat.factorial k : ℝ) * (8 * ρ) ^ k) :=
        mul_le_mul_of_nonneg_left (gInv_exp_le k hρ0) (Real.rpow_nonneg hρ0.le _)
    _ = ((Nat.factorial k : ℝ) * 8 ^ k) * ρ ^ ((k : ℝ) - s) := by
        rw [hpow, hnat, mul_pow]
        ring
    _ ≤ ((Nat.factorial k : ℝ) * 8 ^ k) * 1 :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (Nat.factorial k : ℝ) * 8 ^ k := mul_one _

/-- Finiteness of `∫_{(0,∞)} ρ^{-s} e^{-1/(8ρ)} dρ` for `s > 1`. -/
lemma gInv_finite {s : ℝ} (hs : 1 < s) :
    ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (-s) * Real.exp (-1 / (8 * ρ))) < ⊤ := by
  have hlow : IntegrableOn (fun ρ : ℝ => ρ ^ (-s) * Real.exp (-1 / (8 * ρ))) (Ioc (0 : ℝ) 1) := by
    have hvol : volume (Ioc (0 : ℝ) 1) ≠ ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have hconst : IntegrableOn (fun _ : ℝ => (Nat.factorial ⌈s⌉₊ : ℝ) * 8 ^ ⌈s⌉₊)
        (Ioc (0 : ℝ) 1) := integrableOn_const hvol
    refine Integrable.mono' hconst ?_ ?_
    · exact (by fun_prop :
        Measurable (fun ρ : ℝ => ρ ^ (-s) * Real.exp (-1 / (8 * ρ)))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun ρ hρ => ?_)
      obtain ⟨hρ0, hρ1⟩ := Set.mem_Ioc.1 hρ
      show ‖ρ ^ (-s) * Real.exp (-1 / (8 * ρ))‖ ≤ (Nat.factorial ⌈s⌉₊ : ℝ) * 8 ^ ⌈s⌉₊
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hρ0.le _) (Real.exp_pos _).le)]
      exact gInv_integrand_le hρ0 hρ1
  have hhigh : IntegrableOn (fun ρ : ℝ => ρ ^ (-s) * Real.exp (-1 / (8 * ρ))) (Ioi (1 : ℝ)) := by
    refine Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) (one_pos : (0 : ℝ) < 1)) ?_ ?_
    · exact (by fun_prop :
        Measurable (fun ρ : ℝ => ρ ^ (-s) * Real.exp (-1 / (8 * ρ)))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun ρ hρ => ?_)
      have hρ1 : 1 < ρ := Set.mem_Ioi.1 hρ
      have hρ0 : 0 < ρ := lt_trans one_pos hρ1
      have hexp1 : Real.exp (-1 / (8 * ρ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
      show ‖ρ ^ (-s) * Real.exp (-1 / (8 * ρ))‖ ≤ ρ ^ (-s)
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hρ0.le _) (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hρ0.le _) hexp1
  have hint : IntegrableOn (fun ρ : ℝ => ρ ^ (-s) * Real.exp (-1 / (8 * ρ))) (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hlow.union hhigh
  exact Integrable.lintegral_lt_top hint

/-- `gaussInvIntegral` (SP 3604-3606): the substitution `a = r²ρ` and finiteness. -/
theorem gaussInvIntegral : UnforcedLeray.Short.IIIa.GaussInvIntegral := by
  intro s r hs hr
  refine ⟨?_, gInv_finite hs⟩
  have hc : (0 : ℝ) < r ^ 2 := by positivity
  have hmeas : Measurable (fun a : ℝ => ENNReal.ofReal (a ^ (-s) * Real.exp (-r ^ 2 / (8 * a)))) := by
    fun_prop
  have hE : ∀ x : ℝ, 0 < x → -r ^ 2 / (8 * (r ^ 2 * x)) = -1 / (8 * x) := by
    intro x hx
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hpt : ∀ x : ℝ, 0 < x →
      ENNReal.ofReal ((r ^ 2 * x) ^ (-s) * Real.exp (-r ^ 2 / (8 * (r ^ 2 * x)))) =
        ENNReal.ofReal ((r ^ 2) ^ (-s)) * ENNReal.ofReal (x ^ (-s) * Real.exp (-1 / (8 * x))) := by
    intro x hx
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (sq_nonneg r) _)]
    congr 1
    rw [Real.mul_rpow (sq_nonneg r) hx.le, hE x hx]
    ring
  have hexp : r ^ 2 * (r ^ 2) ^ (-s) = r ^ (2 - 2 * s) := by
    rw [show (2 : ℝ) - 2 * s = 2 * (1 - s) by ring, Real.rpow_mul hr.le, Real.rpow_two,
      show (1 : ℝ) - s = 1 + -s by ring, Real.rpow_add hc, Real.rpow_one]
  have hL : ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (a ^ (-s) * Real.exp (-r ^ 2 / (8 * a))) =
      ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal ((r ^ 2) ^ (-s)) *
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (-s) * Real.exp (-1 / (8 * x)))) := by
    rw [gInv_scale hc _ hmeas,
      setLIntegral_congr_fun measurableSet_Ioi (by intro x hx; exact hpt x hx),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hL, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg r), hexp]

end UnforcedLeray.Short.IIIa
