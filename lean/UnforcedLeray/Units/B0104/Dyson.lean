import UnforcedLeray.Units.B0104.Evolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# B0104, helper: the Dyson series of a bounded perturbation

Helper for blueprint unit `B0104` (`lem:compact-duhamel`, `paper/main.tex` lines 1586-1621).

Line 1597 says the full evolutions are "defined by bounded-perturbation Duhamel iteration", and the
proof (line 1608) begins "The Dyson series have uniform exponential majorants". This file makes
both statements precise.

* `dysonTerm F A k`: the Dyson iterates `V₀(t,s)x = F(t,s)x`,
  `V_{k+1}(t,s)x = ∫_s^t F(t,r) A(r) V_k(r,s)x dr` (line 1617 iterated).
* `DysonDefined B F A`: the iteration is defined on the blocks `s ≤ t ≤ s + B`, i.e. every
  iterated integrand is Bochner integrable (so no Lean integral below is the junk value `0`).
  This is what "defined by Duhamel iteration" presupposes; for strongly measurable `A`
  (line 1593) and strongly continuous free evolutions it is the measurability of the iterates.
* `IsDysonSum B F A U`: `U(t,s)x = Σ_k V_k(t,s)x` on blocks.
* `norm_dysonTerm_le`: the uniform exponential majorant
  `‖V_k(t,s)x‖ ≤ M (MK(t-s))^k / k! ‖x‖` (line 1608).
* `exists_isDysonSum`: the Dyson series converges to a bounded operator.
* `IsDysonSum.isDuhamelEvolution`: the Dyson sum is the Duhamel evolution of `B0104/Evolution.lean`;
  by `IsDuhamelEvolution.unique` it is the only one.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real MeasureTheory Finset
open scoped Nat Interval

namespace UnforcedLeray.B0104

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option linter.unusedSectionVars false

/-- The Dyson iterates of the free evolution `F` and the interaction `A`
(`paper/main.tex` lines 1597, 1608, 1617; unit `B0104`):
`V₀(t,s)x = F(t,s)x` and `V_{k+1}(t,s)x = ∫_s^t F(t,r) A(r) V_k(r,s) x dr`. -/
def dysonTerm (F : ι → ℝ → ℝ → H →L[ℂ] H) (A : ι → ℝ → H →L[ℂ] H) :
    ℕ → ι → ℝ → ℝ → H → H
  | 0, p, t, s, x => F p t s x
  | k + 1, p, t, s, x => ∫ r in s..t, F p t r (A p r (dysonTerm F A k p r s x))

/-- The Dyson iteration is defined on the blocks `s ≤ t ≤ s + B`: every iterated integrand
`r ↦ F(t,r) A(r) V_k(r,s) x` is integrable on `[s,t]` (`paper/main.tex` line 1597; unit
`B0104`). -/
def DysonDefined (B : ℝ) (F : ι → ℝ → ℝ → H →L[ℂ] H) (A : ι → ℝ → H →L[ℂ] H) : Prop :=
  ∀ k p s t, s ≤ t → t ≤ s + B → ∀ x : H,
    IntervalIntegrable (fun r => F p t r (A p r (dysonTerm F A k p r s x))) volume s t

/-- `U` is the sum of the Dyson series on the blocks `s ≤ t ≤ s + B`: the evolution "defined by
bounded-perturbation Duhamel iteration" (`paper/main.tex` line 1597; unit `B0104`). -/
def IsDysonSum (B : ℝ) (F : ι → ℝ → ℝ → H →L[ℂ] H) (A : ι → ℝ → H →L[ℂ] H)
    (U : ι → ℝ → ℝ → H →L[ℂ] H) : Prop :=
  ∀ p t s, s ≤ t → t ≤ s + B → ∀ x : H, HasSum (fun k => dysonTerm F A k p t s x) (U p t s x)

theorem integral_sub_pow (s t : ℝ) (k : ℕ) :
    ∫ r in s..t, (r - s) ^ k = (t - s) ^ (k + 1) / (k + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun r => r ^ k) s, integral_pow, sub_self,
    zero_pow (Nat.succ_ne_zero k), sub_zero]

theorem hasSum_pow_div_factorial (y : ℝ) : HasSum (fun k : ℕ => y ^ k / k !) (exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

/-- The exponential majorant series `Σ_k M (MKτ)^k / k! · c = M e^{MKτ} c`. -/
theorem hasSum_majorant (M K τ c : ℝ) :
    HasSum (fun k : ℕ => M * ((M * K * τ) ^ k / k !) * c) (M * exp (M * K * τ) * c) :=
  ((hasSum_pow_div_factorial (M * K * τ)).mul_left M).mul_right c

section

variable {B M K : ℝ} {F : ι → ℝ → ℝ → H →L[ℂ] H} {A : ι → ℝ → H →L[ℂ] H}

/-- **Uniform exponential majorant of the Dyson terms** (`paper/main.tex` line 1608):
if `‖F(t,s)‖ ≤ M` on blocks and `‖A(r)‖ ≤ K`, then `‖V_k(t,s)x‖ ≤ M (MK(t-s))^k / k! ‖x‖`. -/
theorem norm_dysonTerm_le (hF : ∀ p t s, s ≤ t → t ≤ s + B → ‖F p t s‖ ≤ M)
    (hA : ∀ p r, ‖A p r‖ ≤ K) (k : ℕ) :
    ∀ p t s, s ≤ t → t ≤ s + B → ∀ x : H,
      ‖dysonTerm F A k p t s x‖ ≤ M * ((M * K * (t - s)) ^ k / k !) * ‖x‖ := by
  induction k with
  | zero =>
    intro p t s h1 h2 x
    simpa [dysonTerm] using ((F p t s).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hF p t s h1 h2) (norm_nonneg _))
  | succ k ih =>
    intro p t s h1 h2 x
    have hM : 0 ≤ M := (norm_nonneg _).trans (hF p t s h1 h2)
    have hK : 0 ≤ K := (norm_nonneg _).trans (hA p 0)
    have hk : (k ! : ℝ) ≠ 0 := by positivity
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    show ‖∫ r in s..t, F p t r (A p r (dysonTerm F A k p r s x))‖ ≤ _
    calc ‖∫ r in s..t, F p t r (A p r (dysonTerm F A k p r s x))‖
        ≤ ∫ r in s..t, (M * K) * (M * ((M * K) ^ k / k !) * ‖x‖) * (r - s) ^ k := by
          refine intervalIntegral.norm_integral_le_of_norm_le h1 (ae_of_all _ fun r hr => ?_)
            ((continuous_const.mul ((continuous_id.sub continuous_const).pow k)).intervalIntegrable
              _ _)
          calc ‖F p t r (A p r (dysonTerm F A k p r s x))‖
              ≤ M * K * ‖dysonTerm F A k p r s x‖ :=
                norm_apply_apply_le (hF p t r hr.2 (by linarith [hr.1])) (hA p r) _
            _ ≤ M * K * (M * ((M * K * (r - s)) ^ k / k !) * ‖x‖) :=
                mul_le_mul_of_nonneg_left (ih p r s hr.1.le (by linarith [hr.2]) x)
                  (by positivity)
            _ = (M * K) * (M * ((M * K) ^ k / k !) * ‖x‖) * (r - s) ^ k := by
                rw [mul_pow]; ring
      _ = (M * K) * (M * ((M * K) ^ k / k !) * ‖x‖) * ((t - s) ^ (k + 1) / (k + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_sub_pow]
      _ = M * ((M * K * (t - s)) ^ (k + 1) / (k + 1) !) * ‖x‖ := by
          rw [Nat.factorial_succ, Nat.cast_mul, mul_pow, mul_pow]
          push_cast
          field_simp
          ring

theorem summable_dysonTerm (hF : ∀ p t s, s ≤ t → t ≤ s + B → ‖F p t s‖ ≤ M)
    (hA : ∀ p r, ‖A p r‖ ≤ K) {p : ι} {t s : ℝ} (h1 : s ≤ t)
    (h2 : t ≤ s + B) (x : H) : Summable fun k => dysonTerm F A k p t s x :=
  (hasSum_majorant M K (t - s) ‖x‖).summable.of_norm_bounded
    fun k => norm_dysonTerm_le hF hA k p t s h1 h2 x

theorem dysonTerm_add (hD : DysonDefined B F A) (k : ℕ) :
    ∀ p t s, s ≤ t → t ≤ s + B → ∀ x y : H,
      dysonTerm F A k p t s (x + y) = dysonTerm F A k p t s x + dysonTerm F A k p t s y := by
  induction k with
  | zero => intro p t s _ _ x y; simp [dysonTerm]
  | succ k ih =>
    intro p t s h1 h2 x y
    show (∫ r in s..t, F p t r (A p r (dysonTerm F A k p r s (x + y)))) =
      (∫ r in s..t, F p t r (A p r (dysonTerm F A k p r s x))) +
        ∫ r in s..t, F p t r (A p r (dysonTerm F A k p r s y))
    rw [← intervalIntegral.integral_add (hD k p s t h1 h2 x) (hD k p s t h1 h2 y)]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le h1] at hr
    simp only [ih p r s hr.1 (by linarith [hr.2]) x y, map_add]

theorem dysonTerm_smul (k : ℕ) :
    ∀ p t s, s ≤ t → t ≤ s + B → ∀ (c : ℂ) (x : H),
      dysonTerm F A k p t s (c • x) = c • dysonTerm F A k p t s x := by
  induction k with
  | zero => intro p t s _ _ c x; simp [dysonTerm]
  | succ k ih =>
    intro p t s h1 h2 c x
    show (∫ r in s..t, F p t r (A p r (dysonTerm F A k p r s (c • x)))) =
      c • ∫ r in s..t, F p t r (A p r (dysonTerm F A k p r s x))
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le h1] at hr
    simp only [ih p r s hr.1 (by linarith [hr.2]) c x, map_smul]

/-- **The Dyson series converges** to a bounded operator on every block
(`paper/main.tex` lines 1597, 1608; unit `B0104`). -/
theorem exists_isDysonSum (hF : ∀ p t s, s ≤ t → t ≤ s + B → ‖F p t s‖ ≤ M)
    (hA : ∀ p r, ‖A p r‖ ≤ K) (hD : DysonDefined B F A) :
    ∃ U : ι → ℝ → ℝ → H →L[ℂ] H, IsDysonSum B F A U := by
  have key : ∀ p t s, ∃ T : H →L[ℂ] H, s ≤ t → t ≤ s + B → ∀ x : H,
      HasSum (fun k => dysonTerm F A k p t s x) (T x) := by
    intro p t s
    by_cases h : s ≤ t ∧ t ≤ s + B
    · obtain ⟨h1, h2⟩ := h
      have hsum := summable_dysonTerm hF hA (p := p) h1 h2
      let L : H →ₗ[ℂ] H :=
        { toFun := fun x => ∑' k, dysonTerm F A k p t s x
          map_add' := fun x y => by
            simp only [dysonTerm_add hD _ p t s h1 h2 x y]
            exact (hsum x).tsum_add (hsum y)
          map_smul' := fun c x => by
            simp only [dysonTerm_smul _ p t s h1 h2 c x, RingHom.id_apply]
            exact ((hsum x).hasSum.const_smul c).tsum_eq }
      refine ⟨L.mkContinuous (M * exp (M * K * (t - s))) fun x => ?_, fun _ _ x => ?_⟩
      · exact (hsum x).hasSum.norm_le_of_bounded (hasSum_majorant M K (t - s) ‖x‖)
          fun k => norm_dysonTerm_le hF hA k p t s h1 h2 x
      · exact (hsum x).hasSum
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose U hU using key
  exact ⟨U, hU⟩

namespace IsDysonSum

variable {U : ι → ℝ → ℝ → H →L[ℂ] H}

/-- **Exponential majorant of the Dyson sum**: `‖U(t,s)x‖ ≤ M e^{MK(t-s)} ‖x‖`. -/
theorem norm_apply_le (hU : IsDysonSum B F A U)
    (hF : ∀ p t s, s ≤ t → t ≤ s + B → ‖F p t s‖ ≤ M) (hA : ∀ p r, ‖A p r‖ ≤ K)
    {p : ι} {t s : ℝ} (h1 : s ≤ t) (h2 : t ≤ s + B) (x : H) :
    ‖U p t s x‖ ≤ M * exp (M * K * (t - s)) * ‖x‖ :=
  (hU p t s h1 h2 x).norm_le_of_bounded (hasSum_majorant M K (t - s) ‖x‖)
    fun k => norm_dysonTerm_le hF hA k p t s h1 h2 x

/-- **Uniform exponential majorant**: `‖U(t,s)‖ ≤ M e^{MKB}` on blocks (line 1608). -/
theorem norm_le (hU : IsDysonSum B F A U)
    (hF : ∀ p t s, s ≤ t → t ≤ s + B → ‖F p t s‖ ≤ M) (hA : ∀ p r, ‖A p r‖ ≤ K)
    {p : ι} {t s : ℝ} (h1 : s ≤ t) (h2 : t ≤ s + B) :
    ‖U p t s‖ ≤ M * exp (M * K * B) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF p t s h1 h2)
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA p 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  refine (hU.norm_apply_le hF hA h1 h2 x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hM) (norm_nonneg _))
  exact exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

/-- **The Dyson sum is the Duhamel evolution** (`paper/main.tex` lines 1597, 1617; unit `B0104`):
its Duhamel integrand is integrable, it satisfies
`U(t,s)x = F(t,s)x + ∫_s^t F(t,r) A(r) U(r,s) x dr`, and it is bounded on blocks. -/
theorem isDuhamelEvolution (hU : IsDysonSum B F A U)
    (hF : ∀ p t s, s ≤ t → t ≤ s + B → ‖F p t s‖ ≤ M) (hA : ∀ p r, ‖A p r‖ ≤ K)
    (hD : DysonDefined B F A) : IsDuhamelEvolution B F A U := by
  have key : ∀ p s t, s ≤ t → t ≤ s + B → ∀ x : H,
      IntervalIntegrable (fun r => F p t r (A p r (U p r s x))) volume s t ∧
      HasSum (fun k => dysonTerm F A (k + 1) p t s x)
        (∫ r in s..t, F p t r (A p r (U p r s x))) := by
    intro p s t h1 h2 x
    have hM : 0 ≤ M := (norm_nonneg _).trans (hF p t s h1 h2)
    have hK : 0 ≤ K := (norm_nonneg _).trans (hA p 0)
    let c : ℕ → ℝ := fun k => M * K * (M * ((M * K * B) ^ k / k !) * ‖x‖)
    have hcsum : HasSum c (M * K * (M * exp (M * K * B) * ‖x‖)) :=
      (hasSum_majorant M K B ‖x‖).mul_left (M * K)
    have hbd : ∀ k, ∀ r ∈ Ι s t, ‖F p t r (A p r (dysonTerm F A k p r s x))‖ ≤ c k := by
      intro k r hr
      rw [uIoc_of_le h1] at hr
      have hrs : 0 ≤ r - s := by linarith [hr.1]
      calc ‖F p t r (A p r (dysonTerm F A k p r s x))‖
          ≤ M * K * ‖dysonTerm F A k p r s x‖ :=
            norm_apply_apply_le (hF p t r hr.2 (by linarith [hr.1])) (hA p r) _
        _ ≤ M * K * (M * ((M * K * (r - s)) ^ k / k !) * ‖x‖) :=
            mul_le_mul_of_nonneg_left
              (norm_dysonTerm_le hF hA k p r s hr.1.le (by linarith [hr.2]) x)
              (by positivity)
        _ ≤ c k := by
            have hpow : (M * K * (r - s)) ^ k ≤ (M * K * B) ^ k :=
              pow_le_pow_left₀ (by positivity)
                (mul_le_mul_of_nonneg_left (by linarith [hr.2]) (by positivity)) k
            have : (M * K * (r - s)) ^ k / k ! ≤ (M * K * B) ^ k / k ! :=
              div_le_div_of_nonneg_right hpow (by positivity)
            show _ ≤ M * K * (M * ((M * K * B) ^ k / k !) * ‖x‖)
            gcongr
    have hlim : ∀ r ∈ Ι s t, HasSum (fun k => F p t r (A p r (dysonTerm F A k p r s x)))
        (F p t r (A p r (U p r s x))) := by
      intro r hr
      rw [uIoc_of_le h1] at hr
      exact ((F p t r).comp (A p r)).hasSum (hU p r s hr.1.le (by linarith [hr.2]) x)
    have hmeask : ∀ k, AEStronglyMeasurable
        (fun r => F p t r (A p r (dysonTerm F A k p r s x))) (volume.restrict (Ι s t)) :=
      fun k => Integrable.aestronglyMeasurable (hD k p s t h1 h2 x).def'
    have hmeas : AEStronglyMeasurable (fun r => F p t r (A p r (U p r s x)))
        (volume.restrict (Ι s t)) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun N r => ∑ k ∈ range N, F p t r (A p r (dysonTerm F A k p r s x)))
        (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hmeask k) ?_
      exact ae_restrict_of_forall_mem measurableSet_uIoc fun r hr =>
        (hlim r hr).tendsto_sum_nat
    refine ⟨?_, ?_⟩
    · refine IntervalIntegrable.mono_fun (f := fun _ => M * K * (M * exp (M * K * B) * ‖x‖))
        intervalIntegrable_const hmeas
        (ae_restrict_of_forall_mem measurableSet_uIoc fun r hr => ?_)
      show ‖F p t r (A p r (U p r s x))‖ ≤ ‖M * K * (M * exp (M * K * B) * ‖x‖)‖
      rw [Real.norm_of_nonneg (by positivity)]
      exact (hlim r hr).norm_le_of_bounded hcsum fun k => hbd k r hr
    · have := intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => c k)
        hmeask (fun k => ae_of_all _ fun r hr => hbd k r hr)
        (ae_of_all _ fun _ _ => hcsum.summable) intervalIntegrable_const
        (ae_of_all _ fun r hr => hlim r hr)
      simpa only [dysonTerm] using this
  refine ⟨fun p s t h1 h2 x => (key p s t h1 h2 x).1, fun p s t h1 h2 x => ?_,
    fun p s => ⟨M * exp (M * K * B), fun t h1 h2 => hU.norm_le hF hA h1 h2⟩⟩
  have h0 := (hasSum_nat_add_iff' 1).2 (hU p t s h1 h2 x)
  simp only [Finset.sum_range_one] at h0
  have h3 := h0.unique (key p s t h1 h2 x).2
  rw [← h3]
  simp [dysonTerm]

end IsDysonSum

end

end UnforcedLeray.B0104
