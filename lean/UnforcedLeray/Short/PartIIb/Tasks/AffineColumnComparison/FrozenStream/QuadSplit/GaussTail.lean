import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GaussMulPoly
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.PolyZpow

/-!
# Part II-b, task `PartII-b:G4/2/2/2/2`: `GaussTail`

Source of record: `the November 2 reference manuscript`, lines 2349-2352 (as cited by the
task spec). Route: `T r = ∫_{Ioi r} s^k q s` is `C^∞` on `(0,∞)` with `T' = -(r^k q)` (improper
tail, FTC on a base point `r/2`); the order-zero Gaussian bound comes from `s^N e^{-κ s²}` domination
and an exponential tail integral; higher orders come from `iteratedDeriv_succ'` and `GaussMulPoly`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- Derivative of a tail integral of a continuous, locally integrable-at-infinity function. -/
theorem gt_hasDerivAt_tail {f : ℝ → ℂ} (hfc : ContinuousOn f (Ioi 0))
    (hint : ∀ ρ : ℝ, 0 < ρ → IntegrableOn f (Ioi ρ)) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun ρ => ∫ s in Ioi ρ, f s) (-f r) r := by
  have h1 : (0 : ℝ) < r / 2 := by linarith
  have h2 : r / 2 < r := by linarith
  have hsub : uIcc (r / 2) r ⊆ Ioi 0 := by
    rw [uIcc_of_le h2.le]
    intro x hx
    exact lt_of_lt_of_le h1 hx.1
  have hii : IntervalIntegrable f volume (r / 2) r := (hfc.mono hsub).intervalIntegrable
  have hd : HasDerivAt (fun u => ∫ x in (r / 2)..u, f x) (f r) r :=
    intervalIntegral.integral_hasDerivAt_right hii
      (hfc.stronglyMeasurableAtFilter isOpen_Ioi r hr)
      (hfc.continuousAt (isOpen_Ioi.mem_nhds hr))
  have hd' := (hasDerivAt_const r (∫ s in Ioi (r / 2), f s)).sub hd
  rw [zero_sub] at hd'
  refine hd'.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds h2] with ρ hρ
  have hle : r / 2 ≤ ρ := le_of_lt hρ
  have e := intervalIntegral.integral_Ioi_sub_Ioi (hint (r / 2) h1) hle
  show ∫ s in Ioi ρ, f s = (∫ s in Ioi (r / 2), f s) - ∫ x in (r / 2)..ρ, f x
  rw [← e]
  ring

/-- Integrability of `f` on every `Ioi ρ`, `ρ > 0`, from continuity on `(0,∞)` and a polynomial-times-
Gaussian bound on `[1,∞)`. -/
theorem gt_integrable {f : ℝ → ℂ} (hfc : ContinuousOn f (Ioi 0)) (N : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (D : ℝ) (hb : ∀ s : ℝ, 1 ≤ s → ‖f s‖ ≤ D * (s ^ N * Real.exp (-(κ * s ^ 2)))) :
    ∀ ρ : ℝ, 0 < ρ → IntegrableOn f (Ioi ρ) := by
  have hN : (-1 : ℝ) < (N : ℝ) := by
    have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    linarith
  have hg : Integrable (fun s : ℝ => D * (s ^ (N : ℝ) * Real.exp (-κ * s ^ 2))) :=
    (integrable_rpow_mul_exp_neg_mul_sq hκ hN).const_mul D
  have hG1 : IntegrableOn f (Ioi 1) := by
    refine Integrable.mono' (g := fun s : ℝ => D * (s ^ (N : ℝ) * Real.exp (-κ * s ^ 2)))
      hg.integrableOn ?_ ?_
    · exact (hfc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
      have hs1 : 1 ≤ s := le_of_lt hs
      have := hb s hs1
      simp only [Real.rpow_natCast, neg_mul]
      exact this
  intro ρ hρ
  have hm : 0 < min ρ 1 := lt_min hρ one_pos
  have hmon : Ioi ρ ⊆ Ioi (min ρ 1) := Ioi_subset_Ioi (min_le_left _ _)
  have hm1 : min ρ 1 ≤ 1 := min_le_right _ _
  refine IntegrableOn.mono_set ?_ hmon
  rw [← Ioc_union_Ioi_eq_Ioi hm1]
  refine IntegrableOn.union ?_ hG1
  have hcont : ContinuousOn f (Icc (min ρ 1) 1) :=
    hfc.mono (fun x hx => lt_of_lt_of_le hm hx.1)
  exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self

/-- Order-zero Gaussian tail bound for the tail integral. -/
theorem gt_tail0 {f : ℝ → ℂ} (hfc : ContinuousOn f (Ioi 0)) (N : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (D : ℝ) (hb : ∀ s : ℝ, 1 ≤ s → ‖f s‖ ≤ D * (s ^ N * Real.exp (-(κ * s ^ 2)))) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖∫ s in Ioi r, f s‖ ≤ C * Real.exp (-(κ / 2 * r ^ 2)) := by
  have hint := gt_integrable hfc N κ hκ D hb
  have hκne : κ ≠ 0 := hκ.ne'
  have hpt : ∀ s : ℝ, 1 ≤ s →
      s ^ N * Real.exp (-(κ * s ^ 2)) ≤
        ((N.factorial : ℝ) * (2 / κ) ^ N) * Real.exp (-(κ / 2 * s ^ 2)) := by
    intro s hs
    have hs0 : 0 ≤ s := by linarith
    have hx : 0 ≤ κ / 2 * s ^ 2 := mul_nonneg (div_nonneg hκ.le two_pos.le) (sq_nonneg s)
    have h1 := Real.pow_div_factorial_le_exp _ hx N
    have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
    have h1' : (κ / 2 * s ^ 2) ^ N ≤ Real.exp (κ / 2 * s ^ 2) * (N.factorial : ℝ) := by
      rw [div_le_iff₀ hfac] at h1
      linarith
    have h2 : s ^ N ≤ (s ^ 2) ^ N := pow_le_pow_left₀ hs0 (by nlinarith) N
    have h3 : (s ^ 2) ^ N = (2 / κ) ^ N * (κ / 2 * s ^ 2) ^ N := by
      rw [← mul_pow]
      congr 1
      field_simp
    have hexp : Real.exp (-(κ * s ^ 2)) * Real.exp (κ / 2 * s ^ 2) =
        Real.exp (-(κ / 2 * s ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hpos : 0 ≤ Real.exp (-(κ * s ^ 2)) := (Real.exp_pos _).le
    have hK : 0 ≤ (2 / κ) ^ N := pow_nonneg (div_nonneg two_pos.le hκ.le) N
    calc s ^ N * Real.exp (-(κ * s ^ 2)) ≤ (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right h2 hpos
      _ = (2 / κ) ^ N * ((κ / 2 * s ^ 2) ^ N * Real.exp (-(κ * s ^ 2))) := by
          rw [h3]
          ring
      _ ≤ (2 / κ) ^ N * ((Real.exp (κ / 2 * s ^ 2) * (N.factorial : ℝ)) *
            Real.exp (-(κ * s ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1' hpos) hK
      _ = ((N.factorial : ℝ) * (2 / κ) ^ N) * Real.exp (-(κ / 2 * s ^ 2)) := by
          rw [← hexp]
          ring
  refine ⟨|D| * ((N.factorial : ℝ) * (2 / κ) ^ N) * (2 / κ), fun r hr => ?_⟩
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : r ≠ 0 := hr0.ne'
  have hC'nn : 0 ≤ |D| * ((N.factorial : ℝ) * (2 / κ) ^ N) :=
    mul_nonneg (abs_nonneg D)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg two_pos.le hκ.le) N))
  have hE : ∀ s ∈ Ioi r, ‖f s‖ ≤
      (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) * Real.exp (-(κ * r / 2) * s) := by
    intro s hs
    have hsr : r < s := hs
    have hs1 : 1 ≤ s := by linarith
    have hs0 : 0 ≤ s := by linarith
    have hpos : 0 ≤ s ^ N * Real.exp (-(κ * s ^ 2)) :=
      mul_nonneg (pow_nonneg hs0 N) (Real.exp_pos _).le
    have step1 : ‖f s‖ ≤ |D| * (s ^ N * Real.exp (-(κ * s ^ 2))) :=
      (hb s hs1).trans (mul_le_mul_of_nonneg_right (le_abs_self D) hpos)
    have step2 : |D| * (s ^ N * Real.exp (-(κ * s ^ 2))) ≤
        |D| * (((N.factorial : ℝ) * (2 / κ) ^ N) * Real.exp (-(κ / 2 * s ^ 2))) :=
      mul_le_mul_of_nonneg_left (hpt s hs1) (abs_nonneg D)
    have hexp : Real.exp (-(κ / 2 * s ^ 2)) ≤ Real.exp (-(κ * r / 2) * s) := by
      apply Real.exp_le_exp.2
      have h3 : 0 ≤ κ * (s * (s - r)) := mul_nonneg hκ.le (mul_nonneg hs0 (by linarith))
      nlinarith [h3]
    have step3 : |D| * (((N.factorial : ℝ) * (2 / κ) ^ N) * Real.exp (-(κ / 2 * s ^ 2))) ≤
        |D| * ((N.factorial : ℝ) * (2 / κ) ^ N) * Real.exp (-(κ * r / 2) * s) := by
      have hmul := mul_le_mul_of_nonneg_left hexp hC'nn
      calc |D| * (((N.factorial : ℝ) * (2 / κ) ^ N) * Real.exp (-(κ / 2 * s ^ 2)))
          = (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) * Real.exp (-(κ / 2 * s ^ 2)) := by ring
        _ ≤ (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) * Real.exp (-(κ * r / 2) * s) := hmul
    exact step1.trans (step2.trans step3)
  have hIntG : IntegrableOn (fun s : ℝ => Real.exp (-(κ * r / 2) * s)) (Ioi r) :=
    exp_neg_integrableOn_Ioi r (div_pos (mul_pos hκ hr0) two_pos)
  have hnorm : ‖∫ s in Ioi r, f s‖ ≤
      ∫ s in Ioi r, (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) * Real.exp (-(κ * r / 2) * s) := by
    calc ‖∫ s in Ioi r, f s‖ ≤ ∫ s in Ioi r, ‖f s‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s in Ioi r, (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) *
            Real.exp (-(κ * r / 2) * s) :=
          setIntegral_mono_on (Integrable.norm (hint r hr0)) (hIntG.const_mul _) measurableSet_Ioi hE
  have hcalc : ∫ s in Ioi r, (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) *
        Real.exp (-(κ * r / 2) * s) =
      (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) *
        (Real.exp (-(κ / 2 * r ^ 2)) * (2 / (κ * r))) := by
    have ha : -(κ * r / 2) < 0 := by
      have : 0 < κ * r / 2 := div_pos (mul_pos hκ hr0) two_pos
      linarith
    rw [integral_const_mul, integral_exp_mul_Ioi ha r]
    have hE2 : Real.exp (-(κ * r / 2) * r) = Real.exp (-(κ / 2 * r ^ 2)) := by
      congr 1
      ring
    rw [hE2, neg_div_neg_eq]
    field_simp
  rw [hcalc] at hnorm
  have hq1 : 2 / (κ * r) ≤ 2 / κ := by
    rw [div_le_div_iff₀ (mul_pos hκ hr0) hκ]
    nlinarith
  calc ‖∫ s in Ioi r, f s‖ ≤ (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) *
        (Real.exp (-(κ / 2 * r ^ 2)) * (2 / (κ * r))) := hnorm
    _ ≤ (|D| * ((N.factorial : ℝ) * (2 / κ) ^ N)) *
        (Real.exp (-(κ / 2 * r ^ 2)) * (2 / κ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq1 (Real.exp_pos _).le) hC'nn
    _ = |D| * ((N.factorial : ℝ) * (2 / κ) ^ N) * (2 / κ) * Real.exp (-(κ / 2 * r ^ 2)) := by
          ring

/-- Main theorem: tails of Gaussian-decaying smooth functions. -/
theorem gaussTail : UnforcedLeray.Short.IIb.GaussTail := by
  intro q k hq hG
  have hP : UnforcedLeray.Short.IIb.PolyZpow := polyZpow
  have hM : UnforcedLeray.Short.IIb.GaussMulPoly := gaussMulPoly
  have hkS : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ) ^ k) (Ioi 0) := (hP k).1
  have hfS : ContDiffOn ℝ ∞ (fun s : ℝ => (s : ℂ) ^ k * q s) (Ioi 0) := hkS.mul hq
  have hfc : ContinuousOn (fun s : ℝ => (s : ℂ) ^ k * q s) (Ioi 0) := hfS.continuousOn
  obtain ⟨Cp, N, hCp⟩ := (hP k).2 0
  obtain ⟨C0, κ, hκ, hq0⟩ := hG 0
  simp only [iteratedDeriv_zero] at hCp hq0
  have hb : ∀ s : ℝ, 1 ≤ s →
      ‖(s : ℂ) ^ k * q s‖ ≤ (Cp * C0) * (s ^ N * Real.exp (-(κ * s ^ 2))) := by
    intro s hs
    have h1 := hCp s hs
    have h2 := hq0 s hs
    calc ‖(s : ℂ) ^ k * q s‖ = ‖(s : ℂ) ^ k‖ * ‖q s‖ := norm_mul _ _
      _ ≤ (Cp * s ^ N) * (C0 * Real.exp (-(κ * s ^ 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = (Cp * C0) * (s ^ N * Real.exp (-(κ * s ^ 2))) := by ring
  have hint := gt_integrable hfc N κ hκ (Cp * C0) hb
  have hderiv : ∀ r : ℝ, 0 < r →
      HasDerivAt (fun ρ => ∫ s : ℝ in Ioi ρ, (s : ℂ) ^ k * q s) (-((r : ℂ) ^ k * q r)) r :=
    fun r hr => gt_hasDerivAt_tail hfc hint hr
  have hT : ContDiffOn ℝ ∞ (fun ρ => ∫ s : ℝ in Ioi ρ, (s : ℂ) ^ k * q s) (Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt, ?_⟩
    refine ContDiffOn.congr hfS.neg (fun r hr => ?_)
    exact (hderiv r hr).deriv
  have hGauss : ∀ j : ℕ, GaussAt (fun r : ℝ => ∫ s : ℝ in Ioi r, (s : ℂ) ^ k * q s) j := by
    intro j
    induction j with
    | zero =>
      obtain ⟨C1, hC1⟩ := gt_tail0 hfc N κ hκ (Cp * C0) hb
      refine ⟨C1, κ / 2, half_pos hκ, fun r hr => ?_⟩
      rw [iteratedDeriv_zero]
      exact hC1 r hr
    | succ j _ =>
      have h0 : GaussAt (fun r : ℝ => q r * (r : ℂ) ^ k) j :=
        hM q (fun r : ℝ => (r : ℂ) ^ k) (j + 1) hq hkS (fun i _ => hG i)
          (fun i _ => (hP k).2 i) j (Nat.lt_succ_self j)
      have hfun : (fun r : ℝ => q r * (r : ℂ) ^ k) = (fun s : ℝ => (s : ℂ) ^ k * q s) :=
        funext fun r => mul_comm _ _
      rw [hfun] at h0
      obtain ⟨Cg, κg, hκg, hgb⟩ := h0
      refine ⟨Cg, κg, hκg, fun r hr => ?_⟩
      have hr0 : (0 : ℝ) < r := by linarith
      have hev : deriv (fun ρ => ∫ s : ℝ in Ioi ρ, (s : ℂ) ^ k * q s) =ᶠ[𝓝 r]
          (fun x => -((x : ℂ) ^ k * q x)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hr0] with x hx
        exact (hderiv x hx).deriv
      rw [iteratedDeriv_succ', hev.iteratedDeriv_eq j]
      have hneg : iteratedDeriv j (fun x : ℝ => -((x : ℂ) ^ k * q x)) r =
          -(iteratedDeriv j (fun s : ℝ => (s : ℂ) ^ k * q s) r) :=
        iteratedDeriv_neg j (fun s : ℝ => (s : ℂ) ^ k * q s) r
      rw [hneg, norm_neg]
      exact hgb r hr
  exact ⟨hT, fun j => hGauss j⟩

end UnforcedLeray.Short.IIb
