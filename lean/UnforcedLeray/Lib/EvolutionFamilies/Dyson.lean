import UnforcedLeray.Lib.EvolutionFamilies.Integral
import UnforcedLeray.Infra.EvolutionContinuity.Abstract
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The Dyson evolution of a bounded perturbation (INF08 T8.2)

Scoping note `scoping/INF07-INF08-INF09-Evolution.md`, §5, Layer 3, target T8.2; frozen
interface `dyson` of decision D17. Manuscript: `paper/main.tex`, lines 1594-1621 ("the full
evolutions `U_n`, defined by bounded-perturbation Duhamel iteration", lemma
`lem:compact-duhamel`), 1655-1659 and 1828-1840; blueprint B0104, B0106, B0119, B0244, B0313,
B0329, B0657.

The drafted `Infra/VolterraEvolution` treats a convolution kernel `S₀(τ - s)`, `S(τ - r)`; a
general two-parameter free evolution `F(t,s)` does not fit it, so the Dyson series is built here.
The Dyson terms and their exponential majorant are adapted from the unit draft

`hasSum_majorant`, `IsDysonSum.isDuhamelEvolution`), with the integrability of the iterated
integrands proved here from strong measurability (`Integral.lean`) instead of assumed.

For an evolution family `F` on `[a,b]` and a bounded interaction `A`:
* `dysonTerm F A k t s x`: `V₀ = F`, `V_{k+1}(t,s) x = ∫_s^t F(t,r) A(r) V_k(r,s) x dr`;
* `norm_dysonTerm_le_of_le`: `‖V_k(t,s)x‖ ≤ M e^{ω(t-s)} (MC(t-s))^k/k! ‖x‖` when
  `‖F(t,s)‖ ≤ M e^{ω(t-s)}` and `‖A‖ ≤ C`;
* `dyson F A`: the sum of the series, an `EvolutionFamily` (evolution law by uniqueness);
* `dyson_left`: `U(t,s)x = F(t,s)x + ∫_s^t F(t,r) A(r) U(r,s) x dr`;
* `dyson_unique`: every solution of `dyson_left` continuous in `t` equals `dyson F A`;
* `norm_dyson_le`: `‖U(t,s)‖ ≤ M e^{(ω + MC)(t-s)}`;
* `dyson_commute`: an operator commuting with `F` and `A` commutes with `U`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Nat Interval

namespace UnforcedLeray.Evolution

theorem hasSum_pow_div_factorial (y : ℝ) : HasSum (fun k : ℕ => y ^ k / k !) (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

/-- The exponential majorant series `Σ_k M (MKτ)^k / k! · c = M e^{MKτ} c` (from
`Units/B0104/Dyson.lean`). -/
theorem hasSum_majorant (M K τ c : ℝ) :
    HasSum (fun k : ℕ => M * ((M * K * τ) ^ k / k !) * c) (M * Real.exp (M * K * τ) * c) :=
  ((hasSum_pow_div_factorial (M * K * τ)).mul_left M).mul_right c

theorem integral_sub_pow (s t : ℝ) (k : ℕ) :
    ∫ r in s..t, (r - s) ^ k = (t - s) ^ (k + 1) / (k + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun r => r ^ k) s, integral_pow, sub_self,
    zero_pow (Nat.succ_ne_zero k), sub_zero]

/-- Monotonicity of the majorant terms in the elapsed time. -/
theorem majorant_mono {M K τ τ' c : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hτ : 0 ≤ τ) (hττ' : τ ≤ τ')
    (hc : 0 ≤ c) (k : ℕ) :
    M * ((M * K * τ) ^ k / k !) * c ≤ M * ((M * K * τ') ^ k / k !) * c := by
  have h0 : 0 ≤ M * K * τ := by positivity
  have h1 : M * K * τ ≤ M * K * τ' := mul_le_mul_of_nonneg_left hττ' (by positivity)
  have h2 : (M * K * τ) ^ k / k ! ≤ (M * K * τ') ^ k / k ! :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h1 k) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hM) hc

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ}

theorem isCompact_triangle (a b : ℝ) : IsCompact (triangle a b) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_triangle a b)
    fun _ hp => ⟨⟨hp.1, hp.2.1.trans hp.2.2⟩, ⟨hp.1.trans hp.2.1, hp.2.2⟩⟩

namespace EvolutionFamily

/-! ### The Duhamel integrand -/

section Integrand

variable (L : EvolutionFamily X a b) (A : BoundedPert X a b)

/-- Strong measurability of the Duhamel integrand `r ↦ L(t,r) A(r) y(r)` on `(s,t]`. -/
theorem aestronglyMeasurable_integrand {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) {y : ℝ → X}
    (hy : AEStronglyMeasurable y (volume.restrict (Ioc s t))) :
    AEStronglyMeasurable (fun r => L.U t r (A.A r (y r))) (volume.restrict (Ioc s t)) := by
  have hsub : Ioc s t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc hs ht)
  refine aestronglyMeasurable_clm_apply (L := fun r => L.U t r) (fun v => ?_)
    (aestronglyMeasurable_clm_apply (L := A.A) (fun v => ?_) hy)
  · exact ((L.continuousOn_snd ht v).mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs le_rfl))).aestronglyMeasurable
      measurableSet_Ioc
  · exact (A.meas v).mono_measure (Measure.restrict_mono hsub le_rfl)

theorem norm_integrand_le {s t r : ℝ} (hs : a ≤ s) (ht : t ≤ b) (hr : r ∈ Icc s t) (v : X) :
    ‖L.U t r (A.A r v)‖ ≤ L.M * A.C * ‖v‖ := by
  calc ‖L.U t r (A.A r v)‖ ≤ L.M * ‖A.A r v‖ := L.norm_apply_le (hs.trans hr.1) hr.2 ht _
    _ ≤ L.M * (A.C * ‖v‖) :=
      mul_le_mul_of_nonneg_left (((A.A r).le_opNorm v).trans (mul_le_mul_of_nonneg_right
        (A.norm_le ⟨hs.trans hr.1, hr.2.trans ht⟩) (norm_nonneg _))) L.M_nonneg
    _ = L.M * A.C * ‖v‖ := by ring

/-- The Duhamel integrand is interval integrable for a continuous `y`. -/
theorem intervalIntegrable_integrand {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    {y : ℝ → X} (hy : ContinuousOn y (Icc s t)) :
    IntervalIntegrable (fun r => L.U t r (A.A r (y r))) volume s t := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  refine intervalIntegrable_of_bound (K := L.M * A.C * K) hst
    (L.aestronglyMeasurable_integrand A hs ht
      ((hy.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)) fun r hr => ?_
  exact (L.norm_integrand_le A hs ht (Ioc_subset_Icc_self hr) _).trans
    (mul_le_mul_of_nonneg_left (hK r (Ioc_subset_Icc_self hr))
      (mul_nonneg L.M_nonneg A.C_nonneg))

/-- **Continuity of a Duhamel integral on the triangle.** If `y (s,r)` is continuous on the
triangle, so is `(s,t) ↦ ∫_s^t L(t,r) A(r) y(s,r) dr`. -/
theorem continuousOn_integral_step {y : ℝ × ℝ → X} (hy : ContinuousOn y (triangle a b)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ r in p.1..p.2, L.U p.2 r (A.A r (y (p.1, r))))
      (triangle a b) := by
  obtain ⟨K, hK⟩ := (isCompact_triangle a b).exists_bound_of_continuousOn hy
  have hyr : ∀ p ∈ triangle a b, ContinuousOn (fun r => y (p.1, r)) (Icc p.1 p.2) := by
    intro p hp
    exact hy.comp (continuous_const.prodMk continuous_id).continuousOn
      fun r hr => ⟨hp.1, hr.1, hr.2.trans hp.2.2⟩
  refine continuousOn_integral_triangle (K := L.M * A.C * K) (fun p hp => ?_)
    (fun p hp r hr => ?_) (fun p hp r h1 h2 => ?_)
  · exact L.aestronglyMeasurable_integrand A hp.1 hp.2.2
      (((hyr p hp).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
  · exact (L.norm_integrand_le A hp.1 hp.2.2 (Ioc_subset_Icc_self hr) _).trans
      (mul_le_mul_of_nonneg_left (hK _ ⟨hp.1, hr.1.le, hr.2.trans hp.2.2⟩)
        (mul_nonneg L.M_nonneg A.C_nonneg))
  · have hpS : p ∈ {q : ℝ × ℝ | q ∈ triangle a b ∧ q.1 ≤ r ∧ r ≤ q.2} := ⟨hp, h1.le, h2.le⟩
    refine UnforcedLeray.Infra.EvolutionContinuity.continuousWithinAt_clm_apply
      (K := fun q : ℝ × ℝ => L.U q.2 r) (fun e => ?_) ⟨L.M, ?_⟩ ?_
    · have hc : ContinuousOn (fun q : ℝ × ℝ => L.U q.2 r e)
          {q : ℝ × ℝ | q ∈ triangle a b ∧ q.1 ≤ r ∧ r ≤ q.2} :=
        (L.U_cont e).comp (continuous_const.prodMk continuous_snd).continuousOn
          fun q hq => ⟨hq.1.1.trans hq.2.1, hq.2.2, hq.1.2.2⟩
      exact hc.continuousWithinAt hpS
    · exact eventually_nhdsWithin_of_forall fun q hq =>
        L.norm_le (hq.1.1.trans hq.2.1) hq.2.2 hq.1.2.2
    · have hc : ContinuousOn (fun q : ℝ × ℝ => y (q.1, r))
          {q : ℝ × ℝ | q ∈ triangle a b ∧ q.1 ≤ r ∧ r ≤ q.2} :=
        hy.comp (continuous_fst.prodMk continuous_const).continuousOn
          fun q hq => ⟨hq.1.1, hq.2.1, hq.2.2.trans hq.1.2.2⟩
      exact (A.A r).continuous.continuousAt.comp_continuousWithinAt (hc.continuousWithinAt hpS)

end Integrand

/-! ### Uniqueness for the homogeneous Volterra equation -/

section Unique

variable (L : EvolutionFamily X a b) (A : BoundedPert X a b)

/-- **Uniqueness (Gronwall).** A continuous solution of
`w(t) = ∫_r^t L(t,q) A(q) w(q) dq` on `[r,b]` vanishes. -/
theorem eq_zero_of_volterra {r : ℝ} (hr : a ≤ r) {w : ℝ → X} (hw : ContinuousOn w (Icc r b))
    (heq : ∀ t ∈ Icc r b, w t = ∫ q in r..t, L.U t q (A.A q (w q))) :
    ∀ t ∈ Icc r b, w t = 0 := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  obtain ⟨m, hm_def⟩ : ∃ m, m = L.M * A.C := ⟨_, rfl⟩
  have hm : 0 ≤ m := hm_def ▸ mul_nonneg L.M_nonneg A.C_nonneg
  have hind : ∀ n : ℕ, ∀ t ∈ Icc r b, ‖w t‖ ≤ K * ((m * (t - r)) ^ n / n !) := by
    intro n
    induction n with
    | zero => intro t ht; simpa using hK t ht
    | succ n ih =>
      intro t ht
      rw [heq t ht]
      calc ‖∫ q in r..t, L.U t q (A.A q (w q))‖
          ≤ ∫ q in r..t, (K * (m ^ (n + 1) / n !)) * (q - r) ^ n := by
            refine intervalIntegral.norm_integral_le_of_norm_le ht.1
              (ae_of_all _ fun q hq => ?_)
              ((continuous_const.mul ((continuous_id.sub continuous_const).pow n)).intervalIntegrable
                _ _)
            have hq' : q ∈ Icc r b := ⟨hq.1.le, hq.2.trans ht.2⟩
            calc ‖L.U t q (A.A q (w q))‖ ≤ m * ‖w q‖ :=
                  hm_def ▸ L.norm_integrand_le A hr ht.2 ⟨hq.1.le, hq.2⟩ _
              _ ≤ m * (K * ((m * (q - r)) ^ n / n !)) := mul_le_mul_of_nonneg_left (ih q hq') hm
              _ = (K * (m ^ (n + 1) / n !)) * (q - r) ^ n := by rw [mul_pow, pow_succ]; ring
        _ = (K * (m ^ (n + 1) / n !)) * ((t - r) ^ (n + 1) / (n + 1)) := by
            rw [intervalIntegral.integral_const_mul, integral_sub_pow]
        _ = K * ((m * (t - r)) ^ (n + 1) / (n + 1)!) := by
            rw [mul_pow m (t - r), Nat.factorial_succ]
            push_cast
            field_simp <;> ring
  intro t ht
  have hlim : Tendsto (fun n : ℕ => K * ((m * (t - r)) ^ n / n !)) atTop (𝓝 (K * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (m * (t - r))).const_mul K
  rw [mul_zero] at hlim
  have : ‖w t‖ ≤ 0 := ge_of_tendsto' hlim fun n => hind n t ht
  exact norm_le_zero_iff.mp this

end Unique

end EvolutionFamily

/-! ### The Dyson terms -/

section Terms

variable (F : EvolutionFamily X a b) (A : BoundedPert X a b)

/-- The Dyson iterates (`paper/main.tex`, lines 1597, 1608, 1617; B0104):
`V₀(t,s)x = F(t,s)x`, `V_{k+1}(t,s)x = ∫_s^t F(t,r) A(r) V_k(r,s) x dr`. -/
def dysonTerm : ℕ → ℝ → ℝ → X → X
  | 0, t, s, x => F.U t s x
  | k + 1, t, s, x => ∫ r in s..t, F.U t r (A.A r (dysonTerm k r s x))

theorem dysonTerm_zero (t s : ℝ) (x : X) : dysonTerm F A 0 t s x = F.U t s x := rfl

theorem dysonTerm_succ (k : ℕ) (t s : ℝ) (x : X) :
    dysonTerm F A (k + 1) t s x = ∫ r in s..t, F.U t r (A.A r (dysonTerm F A k r s x)) := rfl

/-- Each Dyson term is jointly continuous on the triangle. -/
theorem continuousOn_dysonTerm (k : ℕ) (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => dysonTerm F A k p.2 p.1 x) (triangle a b) := by
  induction k with
  | zero => exact F.U_cont x
  | succ k ih => exact F.continuousOn_integral_step A ih

theorem continuousOn_dysonTerm_fst (k : ℕ) (x : X) {s : ℝ} (hs : a ≤ s) :
    ContinuousOn (fun t => dysonTerm F A k t s x) (Icc s b) :=
  (continuousOn_dysonTerm F A k x).comp (continuous_const.prodMk continuous_id).continuousOn
    fun t ht => ⟨hs, ht.1, ht.2⟩

/-- **Weighted exponential majorant of the Dyson terms** (`paper/main.tex`, line 1608): if
`‖F(t,s)‖ ≤ M e^{ω(t-s)}` and `‖A(r)‖ ≤ C`, then
`‖V_k(t,s)x‖ ≤ M e^{ω(t-s)} (MC(t-s))^k / k! ‖x‖`. -/
theorem norm_dysonTerm_le_of_le {M ω C : ℝ}
    (hF : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ‖F.U t s‖ ≤ M * Real.exp (ω * (t - s)))
    (hA : ∀ r ∈ Icc a b, ‖A.A r‖ ≤ C) (k : ℕ) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → ∀ x : X,
      ‖dysonTerm F A k t s x‖ ≤
        M * Real.exp (ω * (t - s)) * ((M * C * (t - s)) ^ k / k !) * ‖x‖ := by
  induction k with
  | zero =>
    intro s t hs hst ht x
    simpa [dysonTerm] using ((F.U t s).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hF s t hs hst ht) (norm_nonneg _))
  | succ k ih =>
    intro s t hs hst ht x
    have hM : 0 ≤ M := by
      have h := hF s s hs le_rfl (hst.trans ht)
      simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at h
      exact (norm_nonneg _).trans h
    have hC : 0 ≤ C := (norm_nonneg _).trans (hA s ⟨hs, hst.trans ht⟩)
    rw [dysonTerm_succ]
    calc ‖∫ r in s..t, F.U t r (A.A r (dysonTerm F A k r s x))‖
        ≤ ∫ r in s..t, (M * Real.exp (ω * (t - s)) * ((M * C) ^ (k + 1) / k !) * ‖x‖) *
            (r - s) ^ k := by
          refine intervalIntegral.norm_integral_le_of_norm_le hst (ae_of_all _ fun r hr => ?_)
            ((continuous_const.mul ((continuous_id.sub continuous_const).pow k)).intervalIntegrable
              _ _)
          have he : Real.exp (ω * (t - r)) * Real.exp (ω * (r - s)) = Real.exp (ω * (t - s)) := by
            rw [← Real.exp_add]; ring_nf
          have h1 := hF r t (hs.trans hr.1.le) hr.2 ht
          have h2 := hA r ⟨hs.trans hr.1.le, hr.2.trans ht⟩
          have h3 := ih s r hs hr.1.le (hr.2.trans ht) x
          calc ‖F.U t r (A.A r (dysonTerm F A k r s x))‖
              ≤ ‖F.U t r‖ * (‖A.A r‖ * ‖dysonTerm F A k r s x‖) :=
                ((F.U t r).le_opNorm _).trans
                  (mul_le_mul_of_nonneg_left ((A.A r).le_opNorm _) (norm_nonneg _))
            _ ≤ (M * Real.exp (ω * (t - r))) * (C * (M * Real.exp (ω * (r - s)) *
                  ((M * C * (r - s)) ^ k / k !) * ‖x‖)) := by
                gcongr
            _ = (M * Real.exp (ω * (t - s)) * ((M * C) ^ (k + 1) / k !) * ‖x‖) *
                  (r - s) ^ k := by
                rw [← he, mul_pow, pow_succ]; ring
      _ = (M * Real.exp (ω * (t - s)) * ((M * C) ^ (k + 1) / k !) * ‖x‖) *
            ((t - s) ^ (k + 1) / (k + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_sub_pow]
      _ = M * Real.exp (ω * (t - s)) * ((M * C * (t - s)) ^ (k + 1) / (k + 1)!) * ‖x‖ := by
          rw [mul_pow (M * C), Nat.factorial_succ]
          push_cast
          field_simp <;> ring

/-- **Exponential majorant of the Dyson terms** with the bounds `F.M`, `A.C`:
`‖V_k(t,s)x‖ ≤ M (MC(t-s))^k / k! ‖x‖`. -/
theorem norm_dysonTerm_le (k : ℕ) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    ‖dysonTerm F A k t s x‖ ≤ F.M * ((F.M * A.C * (t - s)) ^ k / k !) * ‖x‖ := by
  have h := norm_dysonTerm_le_of_le F A (M := F.M) (ω := 0) (C := A.C)
    (fun s t hs hst ht => by simpa using F.norm_le hs hst ht) (fun r hr => A.norm_le hr) k s t hs
    hst ht x
  simpa using h

theorem dysonTerm_add (k : ℕ) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → ∀ x y : X,
      dysonTerm F A k t s (x + y) = dysonTerm F A k t s x + dysonTerm F A k t s y := by
  induction k with
  | zero => intro s t _ _ _ x y; simp [dysonTerm]
  | succ k ih =>
    intro s t hs hst ht x y
    simp only [dysonTerm_succ]
    rw [← intervalIntegral.integral_add
      (F.intervalIntegrable_integrand A hs hst ht
        ((continuousOn_dysonTerm_fst F A k x hs).mono (Icc_subset_Icc le_rfl ht)))
      (F.intervalIntegrable_integrand A hs hst ht
        ((continuousOn_dysonTerm_fst F A k y hs).mono (Icc_subset_Icc le_rfl ht)))]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hst] at hr
    simp only [ih s r hs hr.1 (hr.2.trans ht) x y, map_add]

theorem dysonTerm_smul (k : ℕ) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → ∀ (c : ℂ) (x : X),
      dysonTerm F A k t s (c • x) = c • dysonTerm F A k t s x := by
  induction k with
  | zero => intro s t _ _ _ c x; simp [dysonTerm]
  | succ k ih =>
    intro s t hs hst ht c x
    simp only [dysonTerm_succ]
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hst] at hr
    simp only [ih s r hs hr.1 (hr.2.trans ht) c x, map_smul]

end Terms

/-! ### The Dyson sum -/

section Sum

variable [CompleteSpace X] (F : EvolutionFamily X a b) (A : BoundedPert X a b)

theorem summable_dysonTerm {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    Summable fun k => dysonTerm F A k t s x :=
  (hasSum_majorant F.M A.C (t - s) ‖x‖).summable.of_norm_bounded
    fun k => norm_dysonTerm_le F A k hs hst ht x

/-- The Dyson sum `U(t,s) = Σ_k V_k(t,s)` on the triangle (and `F(t,s)` off it). -/
def dysonU (t s : ℝ) : X →L[ℂ] X :=
  if h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    LinearMap.mkContinuous
      { toFun := fun x => ∑' k, dysonTerm F A k t s x
        map_add' := fun x y => by
          simp only [dysonTerm_add F A _ s t h.1 h.2.1 h.2.2 x y]
          exact (summable_dysonTerm F A h.1 h.2.1 h.2.2 x).tsum_add
            (summable_dysonTerm F A h.1 h.2.1 h.2.2 y)
        map_smul' := fun c x => by
          simp only [dysonTerm_smul F A _ s t h.1 h.2.1 h.2.2 c x, RingHom.id_apply]
          exact ((summable_dysonTerm F A h.1 h.2.1 h.2.2 x).hasSum.const_smul c).tsum_eq }
      (F.M * Real.exp (F.M * A.C * (t - s))) fun x =>
        (summable_dysonTerm F A h.1 h.2.1 h.2.2 x).hasSum.norm_le_of_bounded
          (hasSum_majorant F.M A.C (t - s) ‖x‖)
          fun k => norm_dysonTerm_le F A k h.1 h.2.1 h.2.2 x
  else F.U t s

theorem dysonU_apply {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    dysonU F A t s x = ∑' k, dysonTerm F A k t s x := by
  rw [dysonU, dite_eq_left_of_eq_true (eq_true ⟨hs, hst, ht⟩)]
  rfl

theorem hasSum_dysonU {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    HasSum (fun k => dysonTerm F A k t s x) (dysonU F A t s x) := by
  rw [dysonU_apply F A hs hst ht]
  exact (summable_dysonTerm F A hs hst ht x).hasSum

theorem norm_dysonU_apply_le {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    ‖dysonU F A t s x‖ ≤ F.M * Real.exp (F.M * A.C * (t - s)) * ‖x‖ :=
  (hasSum_dysonU F A hs hst ht x).norm_le_of_bounded (hasSum_majorant F.M A.C (t - s) ‖x‖)
    fun k => norm_dysonTerm_le F A k hs hst ht x

theorem norm_dysonU_le {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    ‖dysonU F A t s‖ ≤ F.M * Real.exp (F.M * A.C * (b - a)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg F.M_nonneg (Real.exp_pos _).le)
    fun x => (norm_dysonU_apply_le F A hs hst ht x).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ F.M_nonneg) (norm_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith)
    (mul_nonneg F.M_nonneg A.C_nonneg))

theorem continuousOn_dysonU (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => dysonU F A p.2 p.1 x) (triangle a b) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => ∑' k, dysonTerm F A k p.2 p.1 x) (triangle a b) :=
    continuousOn_tsum (fun k => continuousOn_dysonTerm F A k x)
      (hasSum_majorant F.M A.C (b - a) ‖x‖).summable fun k p hp =>
        (norm_dysonTerm_le F A k hp.1 hp.2.1 hp.2.2 x).trans
          (majorant_mono F.M_nonneg A.C_nonneg (sub_nonneg.mpr hp.2.1)
            (by linarith [hp.1, hp.2.2]) (norm_nonneg _) k)
  exact hc.congr fun p hp => dysonU_apply F A hp.1 hp.2.1 hp.2.2 x

theorem continuousOn_dysonU_fst (x : X) {s : ℝ} (hs : a ≤ s) :
    ContinuousOn (fun t => dysonU F A t s x) (Icc s b) :=
  (continuousOn_dysonU F A x).comp (continuous_const.prodMk continuous_id).continuousOn
    fun t ht => ⟨hs, ht.1, ht.2⟩

theorem dysonU_diag {t : ℝ} (ht : t ∈ Icc a b) : dysonU F A t t = 1 := by
  ext x
  rw [dysonU_apply F A ht.1 le_rfl ht.2, tsum_eq_single 0]
  · simp [dysonTerm, F.apply_diag ht]
  · intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp [dysonTerm_succ]

/-- **Left Duhamel identity of the Dyson sum** (`paper/main.tex`, lines 1597, 1617):
`U(t,s)x = F(t,s)x + ∫_s^t F(t,r) A(r) U(r,s) x dr`. -/
theorem dysonU_eq {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    dysonU F A t s x = F.U t s x + ∫ r in s..t, F.U t r (A.A r (dysonU F A r s x)) := by
  set c : ℕ → ℝ := fun k => F.M * A.C * (F.M * ((F.M * A.C * (t - s)) ^ k / k !) * ‖x‖)
  have hMC : 0 ≤ F.M * A.C := mul_nonneg F.M_nonneg A.C_nonneg
  have hcsum : HasSum c (F.M * A.C * (F.M * Real.exp (F.M * A.C * (t - s)) * ‖x‖)) :=
    (hasSum_majorant F.M A.C (t - s) ‖x‖).mul_left (F.M * A.C)
  have hbd : ∀ k, ∀ r ∈ Ι s t, ‖F.U t r (A.A r (dysonTerm F A k r s x))‖ ≤ c k := by
    intro k r hr
    rw [uIoc_of_le hst] at hr
    calc ‖F.U t r (A.A r (dysonTerm F A k r s x))‖
        ≤ F.M * A.C * ‖dysonTerm F A k r s x‖ :=
          F.norm_integrand_le A hs ht (Ioc_subset_Icc_self hr) _
      _ ≤ c k := mul_le_mul_of_nonneg_left ((norm_dysonTerm_le F A k hs hr.1.le (hr.2.trans ht)
            x).trans (majorant_mono F.M_nonneg A.C_nonneg (by linarith [hr.1]) (by linarith [hr.2])
            (norm_nonneg _) k)) hMC
  have hlim : ∀ r ∈ Ι s t, HasSum (fun k => F.U t r (A.A r (dysonTerm F A k r s x)))
      (F.U t r (A.A r (dysonU F A r s x))) := by
    intro r hr
    rw [uIoc_of_le hst] at hr
    exact ((F.U t r).comp (A.A r)).hasSum (hasSum_dysonU F A hs hr.1.le (hr.2.trans ht) x)
  have hmeask : ∀ k, AEStronglyMeasurable (fun r => F.U t r (A.A r (dysonTerm F A k r s x)))
      (volume.restrict (Ι s t)) := by
    intro k
    rw [uIoc_of_le hst]
    exact F.aestronglyMeasurable_integrand A hs ht
      (((continuousOn_dysonTerm_fst F A k x hs).mono
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht))).aestronglyMeasurable
        measurableSet_Ioc)
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => c k)
    hmeask (fun k => ae_of_all _ fun r hr => hbd k r hr)
    (ae_of_all _ fun _ _ => hcsum.summable) intervalIntegrable_const
    (ae_of_all _ fun r hr => hlim r hr)
  have hint' : HasSum (fun k => dysonTerm F A (k + 1) t s x)
      (∫ r in s..t, F.U t r (A.A r (dysonU F A r s x))) := by
    simpa only [dysonTerm_succ] using hint
  have h0 := (hasSum_nat_add_iff' 1).2 (hasSum_dysonU F A hs hst ht x)
  simp only [Finset.sum_range_one] at h0
  have h3 := h0.unique hint'
  rw [← h3, dysonTerm_zero]
  abel

/-- The Duhamel integrand of the Dyson sum is interval integrable. -/
theorem intervalIntegrable_dysonU {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    IntervalIntegrable (fun r => F.U t r (A.A r (dysonU F A r s x))) volume s t :=
  F.intervalIntegrable_integrand A hs hst ht
    ((continuousOn_dysonU_fst F A x hs).mono (Icc_subset_Icc le_rfl ht))

/-- **Evolution law of the Dyson sum**, by uniqueness for the Volterra equation started at `r`. -/
theorem dysonU_comp {s r t : ℝ} (hs : a ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (ht : t ≤ b) :
    dysonU F A t r ∘L dysonU F A r s = dysonU F A t s := by
  ext x
  rw [ContinuousLinearMap.comp_apply]
  have hr : a ≤ r := hs.trans hsr
  have hrb : r ≤ b := hrt.trans ht
  -- the Duhamel identity of `U(·,s)x` restarted at `r`
  have hre : ∀ τ ∈ Icc r b, dysonU F A τ s x =
      F.U τ r (dysonU F A r s x) + ∫ q in r..τ, F.U τ q (A.A q (dysonU F A q s x)) := by
    intro τ hτ
    have hsτ : s ≤ τ := hsr.trans hτ.1
    rw [dysonU_eq F A hs hsτ hτ.2 x, ← intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_dysonU F A hs hsτ hτ.2 x).mono_set (by
        rw [uIcc_of_le hsr, uIcc_of_le hsτ]; exact Icc_subset_Icc le_rfl hτ.1))
      ((intervalIntegrable_dysonU F A hs hsτ hτ.2 x).mono_set (by
        rw [uIcc_of_le hτ.1, uIcc_of_le hsτ]; exact Icc_subset_Icc hsr le_rfl))]
    have hsplit : ∫ q in s..r, F.U τ q (A.A q (dysonU F A q s x)) =
        F.U τ r (∫ q in s..r, F.U r q (A.A q (dysonU F A q s x))) := by
      rw [← (F.U τ r).intervalIntegral_comp_comm (intervalIntegrable_dysonU F A hs hsr hrb x)]
      refine intervalIntegral.integral_congr fun q hq => ?_
      rw [uIcc_of_le hsr] at hq
      exact (F.apply_comp (hs.trans hq.1) hq.2 hτ.1 hτ.2 _).symm
    rw [hsplit, ← F.apply_comp hs hsr hτ.1 hτ.2 x, dysonU_eq F A hs hsr hrb x, map_add]
    abel
  have hw := F.eq_zero_of_volterra A hr
    (w := fun τ => dysonU F A τ s x - dysonU F A τ r (dysonU F A r s x))
    ((continuousOn_dysonU_fst F A x hs).mono (Icc_subset_Icc hsr le_rfl) |>.sub
      (continuousOn_dysonU_fst F A (dysonU F A r s x) hr)) (fun τ hτ => ?_) t ⟨hrt, ht⟩
  · exact (sub_eq_zero.mp hw).symm
  · rw [hre τ hτ, dysonU_eq F A hr hτ.1 hτ.2 (dysonU F A r s x), add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub
        (F.intervalIntegrable_integrand A hr hτ.1 hτ.2
          ((continuousOn_dysonU_fst F A x hs).mono (Icc_subset_Icc hsr hτ.2)))
        (intervalIntegrable_dysonU F A hr hτ.1 hτ.2 (dysonU F A r s x))]
    refine intervalIntegral.integral_congr fun q _ => ?_
    simp only [map_sub]

end Sum

/-! ### The Dyson evolution family -/

variable [CompleteSpace X]

/-- **The Dyson evolution** of the evolution family `F` perturbed by the bounded interaction `A`
(INF08 T8.2; `paper/main.tex`, lines 1597, 1617, 1655-1659; B0104, B0106): the
bounded-perturbation Duhamel iteration, an evolution family on `[a,b]`. -/
def dyson (F : EvolutionFamily X a b) (A : BoundedPert X a b) : EvolutionFamily X a b where
  U := dysonU F A
  U_diag _ ht := dysonU_diag F A ht
  U_comp _ _ _ hs hsr hrt ht := dysonU_comp F A hs hsr hrt ht
  U_cont x := continuousOn_dysonU F A x
  U_bdd := ⟨F.M * Real.exp (F.M * A.C * (b - a)), fun _ _ hs hst ht => norm_dysonU_le F A hs hst ht⟩

variable (F : EvolutionFamily X a b) (A : BoundedPert X a b)

theorem dyson_U : (dyson F A).U = dysonU F A := rfl

/-- **Left Duhamel identity** (INF08 T8.2 `dyson_left`; `paper/main.tex`, lines 1597, 1617):
`U(t,s)x = F(t,s)x + ∫_s^t F(t,r) A(r) U(r,s) x dr`. -/
theorem dyson_left {s t : ℝ} (h : a ≤ s ∧ s ≤ t ∧ t ≤ b) (x : X) :
    (dyson F A).U t s x = F.U t s x + ∫ r in s..t, F.U t r (A.A r ((dyson F A).U r s x)) :=
  dysonU_eq F A h.1 h.2.1 h.2.2 x

/-- The series form: `U(t,s)x = Σ_k V_k(t,s)x`. -/
theorem hasSum_dyson {s t : ℝ} (h : a ≤ s ∧ s ≤ t ∧ t ≤ b) (x : X) :
    HasSum (fun k => dysonTerm F A k t s x) ((dyson F A).U t s x) :=
  hasSum_dysonU F A h.1 h.2.1 h.2.2 x

/-- **Uniqueness** (INF08 T8.2 `dyson_unique`): a family `V` with `t ↦ V(t,s)x` continuous on
`[s,b]` that satisfies the left Duhamel identity on the triangle equals `dyson F A` there. -/
theorem dyson_unique (V : ℝ → ℝ → X →L[ℂ] X)
    (hcont : ∀ s, a ≤ s → s ≤ b → ∀ x, ContinuousOn (fun t => V t s x) (Icc s b))
    (heq : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ∀ x,
      V t s x = F.U t s x + ∫ r in s..t, F.U t r (A.A r (V r s x))) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → V t s = (dyson F A).U t s := by
  intro s t hs hst ht
  ext x
  have hsb : s ≤ b := hst.trans ht
  have hw := F.eq_zero_of_volterra A hs (w := fun τ => V τ s x - (dyson F A).U τ s x)
    ((hcont s hs hsb x).sub (continuousOn_dysonU_fst F A x hs)) (fun τ hτ => ?_) t ⟨hst, ht⟩
  · exact sub_eq_zero.mp hw
  · simp only [dyson_U]
    rw [heq s τ hs hτ.1 hτ.2 x, dysonU_eq F A hs hτ.1 hτ.2 x, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub
        (F.intervalIntegrable_integrand A hs hτ.1 hτ.2 ((hcont s hs hsb x).mono
          (Icc_subset_Icc le_rfl hτ.2)))
        (intervalIntegrable_dysonU F A hs hτ.1 hτ.2 x)]
    refine intervalIntegral.integral_congr fun q _ => ?_
    simp only [map_sub]

/-- **Exponential bound** (INF08 T8.2 `norm_dyson_le`; `paper/main.tex`, line 1608): if
`‖F(t,s)‖ ≤ M e^{ω(t-s)}` and `‖A(r)‖ ≤ C`, then `‖U(t,s)‖ ≤ M e^{(ω + MC)(t-s)}`. -/
theorem norm_dyson_le {M ω C : ℝ}
    (hF : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ‖F.U t s‖ ≤ M * Real.exp (ω * (t - s)))
    (hA : ∀ r ∈ Icc a b, ‖A.A r‖ ≤ C) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → ‖(dyson F A).U t s‖ ≤ M * Real.exp ((ω + M * C) * (t - s)) := by
  intro s t hs hst ht
  have hM : 0 ≤ M := by
    have h := hF s s hs le_rfl (hst.trans ht)
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (Real.exp_pos _).le) fun x => ?_
  have hmaj : HasSum (fun k : ℕ => M * Real.exp (ω * (t - s)) * ((M * C * (t - s)) ^ k / k !) * ‖x‖)
      (M * Real.exp ((ω + M * C) * (t - s)) * ‖x‖) := by
    have h := ((hasSum_pow_div_factorial (M * C * (t - s))).mul_left
      (M * Real.exp (ω * (t - s)))).mul_right ‖x‖
    have he : M * Real.exp (ω * (t - s)) * Real.exp (M * C * (t - s)) * ‖x‖ =
        M * Real.exp ((ω + M * C) * (t - s)) * ‖x‖ := by
      rw [mul_assoc M, ← Real.exp_add]
      ring_nf
    rw [← he]
    exact h
  exact (hasSum_dyson F A ⟨hs, hst, ht⟩ x).norm_le_of_bounded hmaj
    fun k => norm_dysonTerm_le_of_le F A hF hA k s t hs hst ht x

/-- **Commutation** (INF08 T8.2 `dyson_commute`): an operator commuting with every `F(t,s)` and
every `A(r)` commutes with every `U(t,s)` (symmetries, mass, sectors). -/
theorem dyson_commute (S : X →L[ℂ] X)
    (hSF : ∀ s t, a ≤ s → s ≤ t → t ≤ b → Commute S (F.U t s))
    (hSA : ∀ r ∈ Icc a b, Commute S (A.A r)) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → Commute S ((dyson F A).U t s) := by
  have hterm : ∀ k s t, a ≤ s → s ≤ t → t ≤ b → ∀ x,
      S (dysonTerm F A k t s x) = dysonTerm F A k t s (S x) := by
    intro k
    induction k with
    | zero =>
      intro s t hs hst ht x
      exact congrArg (fun T : X →L[ℂ] X => T x) (hSF s t hs hst ht)
    | succ k ih =>
      intro s t hs hst ht x
      simp only [dysonTerm_succ]
      rw [← S.intervalIntegral_comp_comm (F.intervalIntegrable_integrand A hs hst ht
        ((continuousOn_dysonTerm_fst F A k x hs).mono (Icc_subset_Icc le_rfl ht)))]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hst] at hr
      have h1 : S (F.U t r (A.A r (dysonTerm F A k r s x))) =
          F.U t r (S (A.A r (dysonTerm F A k r s x))) :=
        congrArg (fun T : X →L[ℂ] X => T (A.A r (dysonTerm F A k r s x)))
          (hSF r t (hs.trans hr.1) hr.2 ht)
      have h2 : S (A.A r (dysonTerm F A k r s x)) = A.A r (S (dysonTerm F A k r s x)) :=
        congrArg (fun T : X →L[ℂ] X => T (dysonTerm F A k r s x))
          (hSA r ⟨hs.trans hr.1, hr.2.trans ht⟩)
      simp only [h1, h2, ih s r hs hr.1 (hr.2.trans ht) x]
  intro s t hs hst ht
  ext x
  show S ((dyson F A).U t s x) = (dyson F A).U t s (S x)
  exact (S.hasSum (hasSum_dyson F A ⟨hs, hst, ht⟩ x)).unique
    ((hasSum_dyson F A ⟨hs, hst, ht⟩ (S x)).congr_fun fun k => hterm k s t hs hst ht x)

end UnforcedLeray.Evolution
