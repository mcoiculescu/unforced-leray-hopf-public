import UnforcedLeray.Short.PartIIb.StatementsMixed

/-!
# Part II-b, task `PartII-b:T01`: the elementary Hardy `L¹` estimate

Source of record: `the November 2 reference manuscript`, lines 2240-2247 (the
`align` whose first display is `‖f‖_{L¹(0,T)} ≤ 14^{7/11}T^{1/22}‖f‖_{L^p(s^{13/8}ds)}` on
lines 2241-2242; the label `short-bg:hardy` is on line 2247).

Target: `hardyL1_proof : HardyL1` (statement in `StatementsMixed.lean`, not changed here).

Proof: on `(0, T]` write `g = (g s^{13/22}) (s^{-13/22})`, then apply Hölder with `p = 11/4`
and `q = 11/7`. The first factor is `∫ g^p s^{13/8} ds`. The second is
`∫₀ᵀ s^{-13/14} ds = 14 T^{1/14}`, and raising it to `1/q = 7/11` gives `14^{7/11} T^{1/22}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Integrals against `sMeas b` over `(0, T]` are integrals against the density `s ^ b`. -/
lemma hardyL1_sMeas_Ioc (b T : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s in Ioc 0 T, F s ∂sMeas b = ∫⁻ s in Ioc 0 T, F s * ENNReal.ofReal (s ^ b) := by
  have hφ : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ b)) := by fun_prop
  have hset : Ioc (0 : ℝ) T ∩ Ioi 0 = Ioc 0 T := Set.inter_eq_left.mpr (fun x hx => hx.1)
  unfold sMeas
  rw [restrict_withDensity measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc, hset,
    lintegral_withDensity_eq_lintegral_mul _ hφ hF]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

/-- The pointwise factorization `(x · s^{13/22})^{11/4} = x^{11/4} · s^{13/8}` for `s > 0`. -/
lemma hardyL1_bgp_factor (s : ℝ) (hs : 0 < s) (x : ℝ≥0∞) :
    (x * ENNReal.ofReal (s ^ (13 / 22 : ℝ))) ^ bgp
      = x ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) := by
  have hbgp : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have hmul : (13 / 22 : ℝ) * bgp = 13 / 8 := by norm_num [bgp]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hbgp,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs.le (13 / 22 : ℝ)) hbgp,
    ← Real.rpow_mul hs.le, hmul]

/-- `s^{13/22} · s^{-13/22} = 1` for `s > 0`. -/
lemma hardyL1_split_id (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (s ^ (13 / 22 : ℝ)) * ENNReal.ofReal (s ^ (-(13 / 22) : ℝ)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le (13 / 22 : ℝ)), ← Real.rpow_add hs]
  norm_num

/-- **`PartII-b:T01`** (`short-bg:hardy`, first line): the elementary Hardy `L¹` estimate. -/
theorem hardyL1_proof : UnforcedLeray.Short.IIb.HardyL1 := by
  intro T hT g hg
  have hpq : Real.HolderConjugate bgp (11 / 7 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num [bgp], by norm_num [bgp]⟩
  have hm1 : Measurable (fun s : ℝ => g s * ENNReal.ofReal (s ^ (13 / 22 : ℝ))) := by
    fun_prop
  have hm2 : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (-(13 / 22) : ℝ))) := by fun_prop
  -- step 1: `g = (g s^{13/22}) (s^{-13/22})` on `(0, T]`
  have hsplit : ∫⁻ s in Ioc 0 T, g s =
      ∫⁻ s in Ioc 0 T,
        (g s * ENNReal.ofReal (s ^ (13 / 22 : ℝ))) * ENNReal.ofReal (s ^ (-(13 / 22) : ℝ)) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    show g s = (g s * ENNReal.ofReal (s ^ (13 / 22 : ℝ))) * ENNReal.ofReal (s ^ (-(13 / 22) : ℝ))
    rw [mul_assoc, hardyL1_split_id s hs.1, mul_one]
  -- step 2: Hölder with `p = 11/4`, `q = 11/7`
  have hholder :
      ∫⁻ s in Ioc 0 T,
          (g s * ENNReal.ofReal (s ^ (13 / 22 : ℝ))) * ENNReal.ofReal (s ^ (-(13 / 22) : ℝ))
        ≤ (∫⁻ s in Ioc 0 T, (g s * ENNReal.ofReal (s ^ (13 / 22 : ℝ))) ^ bgp) ^ (1 / bgp) *
          (∫⁻ s in Ioc 0 T, ENNReal.ofReal (s ^ (-(13 / 22) : ℝ)) ^ (11 / 7 : ℝ)) ^
            (1 / (11 / 7 : ℝ)) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc 0 T)) hpq hm1.aemeasurable
      hm2.aemeasurable
  -- step 3: the first factor is the `s^{13/8}`-weighted `L^p` norm
  have hA : ∫⁻ s in Ioc 0 T, (g s * ENNReal.ofReal (s ^ (13 / 22 : ℝ))) ^ bgp
      = ∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8) := by
    rw [hardyL1_sMeas_Ioc (13 / 8) T (fun s => g s ^ bgp) (by fun_prop)]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    show (g s * ENNReal.ofReal (s ^ (13 / 22 : ℝ))) ^ bgp
      = g s ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))
    exact hardyL1_bgp_factor s hs.1 (g s)
  -- step 4: the second factor, `∫₀ᵀ s^{-13/14} ds = 14 T^{1/14}`
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-(13 / 14) : ℝ)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)), (0 : ℝ) ≤ s ^ (-(13 / 14) : ℝ) :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => Real.rpow_nonneg hs.1.le _)
  have hlint : ∫⁻ s in Ioc 0 T, ENNReal.ofReal (s ^ (-(13 / 14) : ℝ))
      = ENNReal.ofReal (∫ s in Ioc 0 T, s ^ (-(13 / 14) : ℝ)) :=
    (ofReal_integral_eq_lintegral_ofReal hint.1 hnn).symm
  have hval : ∫ s in Ioc 0 T, s ^ (-(13 / 14) : ℝ) = 14 * T ^ (1 / 14 : ℝ) := by
    have e : (-(13 / 14) : ℝ) + 1 = 1 / 14 := by norm_num
    rw [← intervalIntegral.integral_of_le hT.le,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(13 / 14))), e,
      Real.zero_rpow (by norm_num : (1 / 14 : ℝ) ≠ 0), sub_zero]
    ring
  -- step 5: the power `(·)^{11/7}` on the second factor
  have hpow : ∀ s : ℝ, 0 < s →
      ENNReal.ofReal (s ^ (-(13 / 22) : ℝ)) ^ (11 / 7 : ℝ)
        = ENNReal.ofReal (s ^ (-(13 / 14) : ℝ)) := by
    intro s hs
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs.le (-(13 / 22) : ℝ))
        (by norm_num : (0 : ℝ) ≤ 11 / 7), ← Real.rpow_mul hs.le]
    norm_num
  have hB : ∫⁻ s in Ioc 0 T, ENNReal.ofReal (s ^ (-(13 / 22) : ℝ)) ^ (11 / 7 : ℝ)
      = ENNReal.ofReal (14 * T ^ (1 / 14 : ℝ)) := by
    have hcongr : ∫⁻ s in Ioc 0 T, ENNReal.ofReal (s ^ (-(13 / 22) : ℝ)) ^ (11 / 7 : ℝ)
        = ∫⁻ s in Ioc 0 T, ENNReal.ofReal (s ^ (-(13 / 14) : ℝ)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact hpow s hs.1
    rw [hcongr, hlint, hval]
  -- step 6: raise to `1/q = 7/11`
  have hC : ENNReal.ofReal (14 * T ^ (1 / 14 : ℝ)) ^ (1 / (11 / 7 : ℝ))
      = ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * T ^ (1 / 22 : ℝ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 14) (Real.rpow_nonneg hT.le (1 / 14 : ℝ)))
        (by norm_num : (0 : ℝ) ≤ 1 / (11 / 7)),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 14) (Real.rpow_nonneg hT.le (1 / 14 : ℝ)),
      ← Real.rpow_mul hT.le]
    norm_num
  -- assemble
  have h1 : (1 / bgp : ℝ) = 4 / 11 := by norm_num [bgp]
  rw [hsplit]
  refine le_trans hholder (le_of_eq ?_)
  rw [hA, hB, hC, h1]
  exact mul_comm _ _

end UnforcedLeray.Short.IIb
