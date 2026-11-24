import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2_3

/-!
# Lemma 2 (`PeriodicFundamental`): fundamental lemma for periodic functions

Pure real analysis (used at source 1415-1424). A locally integrable `P`-periodic `ℂ`-valued
function that is orthogonal to every smooth periodic real function on one period vanishes a.e.

Proof. For `b ∈ C_c^∞(ℝ)` put `a t = ∑ₖ b (t + k P)` (a finite sum locally, so `a` is smooth and
`P`-periodic). On one period `a` is the finite sum over `|k| ≤ N`, and the translates of the
period cells `[kP, kP + P]` tile the window `[-NP, (N+1)P]` that contains the support of `b`, so
`∫ b F = ∫_{Ioc 0 P} a F = 0`. Then `ae_eq_zero_of_integral_contDiff_smul_eq_zero` concludes.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

/-- Locally finite periodic sum, restricted to a window of `k`. -/
lemma pf_sum_eq (P : ℝ) (hP : 0 < P) (b : ℝ → ℝ) (R : ℝ) (hR : ∀ x, b x ≠ 0 → |x| ≤ R)
    (t T : ℝ) (M : ℕ) (ht : |t| ≤ T) (hM : R + T ≤ M * P) :
    ∑ᶠ k : ℤ, b (t + k * P) = ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), b (t + k * P) := by
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  have h1 := hR _ hk
  have h2 : |(k : ℝ) * P| ≤ R + T := by
    have e : (k : ℝ) * P = (t + k * P) - t := by ring
    rw [e]
    calc |(t + k * P) - t| ≤ |t + k * P| + |t| := abs_sub _ _
      _ ≤ R + T := by linarith
  have h3 := abs_le.1 h2
  have hk1 : (k : ℝ) ≤ (M : ℝ) := by
    have : (k : ℝ) * P ≤ (M : ℝ) * P := by linarith [h3.2]
    exact le_of_mul_le_mul_right this hP
  have hk2 : -(M : ℝ) ≤ (k : ℝ) := by
    have : -(M : ℝ) * P ≤ (k : ℝ) * P := by linarith [h3.1]
    exact le_of_mul_le_mul_right this hP
  rw [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · exact_mod_cast hk2
  · exact_mod_cast hk1

/-- Periodicity of the periodic sum. -/
lemma pf_periodic (P : ℝ) (b : ℝ → ℝ) (t : ℝ) :
    ∑ᶠ k : ℤ, b (t + P + k * P) = ∑ᶠ k : ℤ, b (t + k * P) := by
  calc ∑ᶠ k : ℤ, b (t + P + k * P)
      = ∑ᶠ k : ℤ, b (t + ((Equiv.addRight (1 : ℤ) k : ℤ) : ℝ) * P) :=
        finsum_congr fun k => by
          rw [show t + P + k * P = t + ((Equiv.addRight (1 : ℤ) k : ℤ) : ℝ) * P by
            simp only [Equiv.coe_addRight]; push_cast; ring]
    _ = ∑ᶠ k : ℤ, b (t + k * P) :=
        finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun k : ℤ => b (t + k * P))

/-- Telescoping of the period cells `[kP, kP + P]`, `|k| ≤ N`, into the window
`[-NP, (N+1)P]`. -/
lemma pf_sum_intervals (P : ℝ) (N : ℕ) (G : ℝ → ℂ)
    (hG : ∀ a c : ℝ, IntervalIntegrable G volume a c) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in ((k : ℝ) * P)..((k : ℝ) * P + P), G x =
      ∫ x in (-((N : ℝ) * P))..(((N : ℝ) + 1) * P), G x := by
  have hsum : ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in ((k : ℝ) * P)..((k : ℝ) * P + P), G x
      = ∑ j ∈ Finset.range (2 * N + 1),
          ∫ x in ((((j : ℕ) : ℝ) - N) * P)..(((((j + 1 : ℕ)) : ℝ) - N) * P), G x := by
    refine Finset.sum_bij' (fun k _ => (k + N).toNat) (fun j _ => (j : ℤ) - N) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]
      have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ k + N by omega)
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ k + N by omega)
      omega
    · intro j hj
      simp
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have e1 : ((((k + N).toNat : ℕ)) : ℝ) = (k : ℝ) + N := by
        have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ k + N by omega)
        have h' : (((k + N).toNat : ℕ) : ℤ) = k + N := h
        exact_mod_cast h'
      have h1 : (((((k + N).toNat : ℕ)) : ℝ) - N) * P = (k : ℝ) * P := by
        rw [e1]; ring
      have h2 : (((((k + N).toNat + 1 : ℕ)) : ℝ) - N) * P = (k : ℝ) * P + P := by
        push_cast
        rw [e1]; ring
      rw [h1, h2]
  rw [hsum, intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (((j : ℕ) : ℝ) - N) * P) (f := G) (fun k _ => hG _ _)]
  congr 1
  · push_cast; ring
  · push_cast; ring

/-- One period-cell term: `∫₀ᴾ b(x + kP) F(x) dx = ∫_{kP}^{kP+P} b F`. -/
lemma pf_term (P : ℝ) (b : ℝ → ℝ) (F : ℝ → ℂ) (hper : Function.Periodic F P) (k : ℤ) :
    ∫ x in (0 : ℝ)..P, b (x + k * P) • F x
      = ∫ x in ((k : ℝ) * P)..((k : ℝ) * P + P), b x • F x := by
  have h1 : ∫ x in (0 : ℝ)..P, b (x + k * P) • F x
      = ∫ x in (0 : ℝ)..P, b (x + k * P) • F (x + k * P) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [(hper.int_mul k) x]
  rw [h1]
  have h2 : ∫ x in (0 : ℝ)..P, b (x + k * P) • F (x + k * P)
      = ∫ x in ((0 : ℝ) + k * P)..(P + k * P), b x • F x :=
    intervalIntegral.integral_comp_add_right (fun x => b x • F x) ((k : ℝ) * P)
  rw [h2, zero_add, add_comm P]

theorem periodicFundamental : PeriodicFundamental := by
  intro P hPfact F hper hF hH
  have hP : 0 < P := hPfact.out
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hF
  intro b hb hbc
  obtain ⟨R, hR⟩ := hbc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hsupp : ∀ x, b x ≠ 0 → |x| ≤ R := by
    intro x hx
    have h1 : x ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport b (Function.mem_support.2 hx))
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    exact h1
  obtain ⟨N, hN⟩ := exists_nat_ge ((R + P) / P)
  have hNP : R + P ≤ (N : ℝ) * P := by rwa [div_le_iff₀ hP] at hN
  -- the periodic sum is smooth
  have ha_sm : ContDiff ℝ ∞ (fun t : ℝ => ∑ᶠ k : ℤ, b (t + k * P)) := by
    rw [contDiff_iff_contDiffAt]
    intro t₀
    obtain ⟨M, hM⟩ := exists_nat_ge ((R + (|t₀| + 1)) / P)
    have hM' : R + (|t₀| + 1) ≤ (M : ℝ) * P := by rwa [div_le_iff₀ hP] at hM
    have hfin : ContDiffAt ℝ ∞
        (fun t : ℝ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), b (t + k * P)) t₀ :=
      (ContDiff.sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ))
        (f := fun (k : ℤ) (t : ℝ) => b (t + (k : ℝ) * P))
        (fun k _ => hb.comp (contDiff_id.add contDiff_const))).contDiffAt
    apply hfin.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (show t₀ - 1 < t₀ by linarith) (show t₀ < t₀ + 1 by linarith)]
      with t ht
    have hle : |t| ≤ |t₀| + 1 := by
      have := neg_abs_le t₀
      have := le_abs_self t₀
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    exact pf_sum_eq P hP b R hsupp t (|t₀| + 1) M hle hM'
  -- the periodic sum is `P`-periodic
  have ha_per : Function.Periodic (fun t : ℝ => ∑ᶠ k : ℤ, b (t + k * P)) P := by
    intro t
    exact pf_periodic P b t
  have hHa : ∫ t in Ioc (0 : ℝ) P, (∑ᶠ k : ℤ, b (t + k * P)) • F t = 0 :=
    hH (fun t : ℝ => ∑ᶠ k : ℤ, b (t + k * P)) ha_sm ha_per
  -- the integrability of `b • F` on compact intervals
  have hGint : ∀ a c : ℝ, IntervalIntegrable (fun x => b x • F x) volume a c := by
    intro a c
    exact IntervalIntegrable.continuousOn_smul
      ((hF.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)
      hb.continuous.continuousOn
  -- step 1: the integral over `ℝ` is an integral over the window
  have hA : ∫ x, b x • F x = ∫ x in (-((N : ℝ) * P))..(((N : ℝ) + 1) * P), b x • F x := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [intervalIntegral.integral_of_le (by nlinarith)]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra hne
    have hbx : b x ≠ 0 := fun h => hne (by simp [h])
    have h1 := abs_le.1 (hsupp x hbx)
    apply hx
    constructor <;> nlinarith
  -- step 2: the window splits into period cells
  have hB := pf_sum_intervals P N (fun x => b x • F x) hGint
  -- step 3: each cell is a period integral of the periodic sum
  have hC : ∫ x in (0 : ℝ)..P, (∑ᶠ k : ℤ, b (x + k * P)) • F x
      = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in (0 : ℝ)..P, b (x + k * P) • F x := by
    have hcongr : ∫ x in (0 : ℝ)..P, (∑ᶠ k : ℤ, b (x + k * P)) • F x
        = ∫ x in (0 : ℝ)..P, ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), b (x + k * P) • F x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hP.le] at hx
      have hxP : |x| ≤ P := abs_le.2 ⟨by linarith [hx.1], hx.2⟩
      show (∑ᶠ k : ℤ, b (x + k * P)) • F x = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), b (x + k * P) • F x
      rw [pf_sum_eq P hP b R hsupp x P N hxP hNP, Finset.sum_smul]
    have hint : ∀ k : ℤ, IntervalIntegrable (fun x => b (x + k * P) • F x) volume 0 P := by
      intro k
      exact IntervalIntegrable.continuousOn_smul
        ((hF.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)
        (hb.continuous.comp (continuous_id.add continuous_const)).continuousOn
    rw [hcongr, intervalIntegral.integral_finsetSum (fun k _ => hint k)]
  -- assemble
  calc ∫ x, b x • F x
      = ∫ x in (-((N : ℝ) * P))..(((N : ℝ) + 1) * P), b x • F x := hA
    _ = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in ((k : ℝ) * P)..((k : ℝ) * P + P), b x • F x :=
        hB.symm
    _ = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in (0 : ℝ)..P, b (x + k * P) • F x :=
        Finset.sum_congr rfl (fun k _ => (pf_term P b F hper k).symm)
    _ = ∫ x in (0 : ℝ)..P, (∑ᶠ k : ℤ, b (x + k * P)) • F x := hC.symm
    _ = ∫ x in Ioc (0 : ℝ) P, (∑ᶠ k : ℤ, b (x + k * P)) • F x :=
        intervalIntegral.integral_of_le hP.le
    _ = 0 := hHa

end UnforcedLeray.Short.PartIIIb.Concrete
