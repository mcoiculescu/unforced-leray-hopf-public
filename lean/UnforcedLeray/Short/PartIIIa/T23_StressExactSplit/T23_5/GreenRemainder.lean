import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# `GreenRemainder` (SP 2349-2352)

Proof of the leaf `GreenRemainder`: for the growing eigenpair `(λ, q)`, `M = ∫₀^∞ s³ q`, and
`G = greenRem q M` satisfies `|G| + |G'| ≤ C e^{-r²/16}` on `r ≥ 1/2`.  The tails
`∫_r^∞ s³q`, `∫_r^∞ q/s` are bounded by Cauchy-Schwarz (in the AM-GM form) against the Gaussian
weight of `MemXG`, giving the rate `e^{-r²/12}`; the derivative is computed by the fundamental
theorem of calculus (the `r q(r)` terms cancel).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Blueprint

theorem grAmgm (a g W t : ℝ) (hW : 0 < W) (ht : 0 < t) :
    a * |g| ≤ t / 2 * (a ^ 2 * W) + 1 / (2 * t) * (g ^ 2 / W) := by
  have hg : g ^ 2 = |g| ^ 2 := (sq_abs g).symm
  rw [← sub_nonneg]
  have : t / 2 * (a ^ 2 * W) + 1 / (2 * t) * (g ^ 2 / W) - a * |g| =
      (t * W * a - |g|) ^ 2 / (2 * t * W) := by
    rw [hg]; field_simp; ring
  rw [this]; positivity

theorem grPow5 (s : ℝ) (hs : 0 ≤ s) : s ^ 5 * Real.exp (-(s ^ 2 / 12)) ≤ 10369 := by
  have hx : 0 ≤ s ^ 2 / 12 := by positivity
  have h := Real.pow_div_factorial_le_exp (s ^ 2 / 12) hx 3
  have h6 : s ^ 6 ≤ 10368 * Real.exp (s ^ 2 / 12) := by
    have : (s ^ 2 / 12) ^ 3 / (Nat.factorial 3 : ℝ) = s ^ 6 / 10368 := by
      simp [Nat.factorial]; ring
    rw [this] at h; linarith
  have e1 : Real.exp (s ^ 2 / 12) * Real.exp (-(s ^ 2 / 12)) = 1 := by
    rw [← Real.exp_add]; simp
  have e2 : Real.exp (-(s ^ 2 / 12)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hE := Real.exp_pos (-(s ^ 2 / 12))
  have h5 : s ^ 5 ≤ 1 + s ^ 6 := by
    rcases le_total s 1 with h1 | h1
    · have : s ^ 5 ≤ 1 := pow_le_one₀ hs h1
      nlinarith [pow_nonneg hs 6]
    · nlinarith [pow_nonneg hs 5]
  calc s ^ 5 * Real.exp (-(s ^ 2 / 12)) ≤ (1 + s ^ 6) * Real.exp (-(s ^ 2 / 12)) :=
        mul_le_mul_of_nonneg_right h5 hE.le
    _ = Real.exp (-(s ^ 2 / 12)) + s ^ 6 * Real.exp (-(s ^ 2 / 12)) := by ring
    _ ≤ 1 + 10368 := by
        have : s ^ 6 * Real.exp (-(s ^ 2 / 12)) ≤ 10368 := by
          calc s ^ 6 * Real.exp (-(s ^ 2 / 12))
              ≤ 10368 * Real.exp (s ^ 2 / 12) * Real.exp (-(s ^ 2 / 12)) :=
                mul_le_mul_of_nonneg_right h6 hE.le
            _ = 10368 := by rw [mul_assoc, e1]; ring
        linarith
    _ = 10369 := by norm_num

theorem grW_pos {s : ℝ} (hs : 0 < s) : 0 < Planar.gaussianWeightInv s * s := by
  unfold Planar.gaussianWeightInv; positivity

theorem grPt3 (s : ℝ) (hs : 0 < s) :
    ((s ^ 3) ^ 2) / (Planar.gaussianWeightInv s * s) ≤ 10369 * Real.exp (-(s ^ 2 / 6)) := by
  have h1 := grPow5 s hs.le
  have hpi : 1 ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  calc ((s ^ 3) ^ 2) / (Planar.gaussianWeightInv s * s)
      = s ^ 5 * Real.exp (-(s ^ 2 / 4)) / (4 * Real.pi) := by
        unfold Planar.gaussianWeightInv; rw [Real.exp_neg]; field_simp
    _ ≤ s ^ 5 * Real.exp (-(s ^ 2 / 4)) := div_le_self (by positivity) hpi
    _ = (s ^ 5 * Real.exp (-(s ^ 2 / 12))) * Real.exp (-(s ^ 2 / 6)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 10369 * Real.exp (-(s ^ 2 / 6)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

theorem grPt1 (a s : ℝ) (ha : 0 < a) (hs : a ≤ s) :
    ((s⁻¹) ^ 2) / (Planar.gaussianWeightInv s * s) ≤ (a ^ 3)⁻¹ * Real.exp (-(s ^ 2 / 6)) := by
  have hs0 : 0 < s := lt_of_lt_of_le ha hs
  have hpi : 1 ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  have hi : (s ^ 3)⁻¹ ≤ (a ^ 3)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hs 3)
  have he : Real.exp (-(s ^ 2 / 4)) ≤ Real.exp (-(s ^ 2 / 6)) := by
    apply Real.exp_le_exp.2; nlinarith [sq_nonneg s]
  calc ((s⁻¹) ^ 2) / (Planar.gaussianWeightInv s * s)
      = (s ^ 3)⁻¹ * Real.exp (-(s ^ 2 / 4)) / (4 * Real.pi) := by
        unfold Planar.gaussianWeightInv; rw [Real.exp_neg]; field_simp
    _ ≤ (s ^ 3)⁻¹ * Real.exp (-(s ^ 2 / 4)) := div_le_self (by positivity) hpi
    _ ≤ (a ^ 3)⁻¹ * Real.exp (-(s ^ 2 / 6)) :=
        mul_le_mul hi he (Real.exp_pos _).le (by positivity)

/-- Core Cauchy-Schwarz (AM-GM) estimate against the Gaussian weight. -/
theorem grCore (q : Planar.Profile) (hq : Planar.MemXG q) (g : ℝ → ℝ) (hgm : Measurable g)
    (r : ℝ) (hr : 0 ≤ r) (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi r))
    (hbd : ∀ s ∈ Ioi r, (g s) ^ 2 / (Planar.gaussianWeightInv s * s) ≤ B s) :
    IntegrableOn (fun s => ((g s : ℝ) : ℂ) * q s) (Ioi r) ∧
    ∀ t : ℝ, 0 < t → ‖∫ s in Ioi r, ((g s : ℝ) : ℂ) * q s‖ ≤
      t / 2 * (∫ s in Ioi (0 : ℝ), ‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s) +
        1 / (2 * t) * ∫ s in Ioi r, B s := by
  have hF : IntegrableOn (fun s => ‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s) (Ioi r) :=
    hq.integrable.mono_set (Ioi_subset_Ioi hr)
  have hmeas : AEStronglyMeasurable (fun s => ((g s : ℝ) : ℂ) * q s) (volume.restrict (Ioi r)) := by
    have h1 : AEStronglyMeasurable q (volume.restrict (Ioi r)) :=
      hq.measurable.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hr) le_rfl)
    exact ((Complex.measurable_ofReal.comp hgm).aestronglyMeasurable).mul h1
  have hptw : ∀ t : ℝ, 0 < t → ∀ s ∈ Ioi r,
      ‖((g s : ℝ) : ℂ) * q s‖ ≤ t / 2 * (‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s) +
        1 / (2 * t) * B s := by
    intro t ht s hs
    have hs0 : 0 < s := lt_of_le_of_lt hr hs
    have h1 := grAmgm ‖q s‖ (g s) (Planar.gaussianWeightInv s * s) t (grW_pos hs0) ht
    have h2 : (g s) ^ 2 / (Planar.gaussianWeightInv s * s) ≤ B s := hbd s hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    have h3 : 1 / (2 * t) * ((g s) ^ 2 / (Planar.gaussianWeightInv s * s)) ≤ 1 / (2 * t) * B s :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc _ ≤ _ := h1
      _ = t / 2 * (‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s) +
            1 / (2 * t) * ((g s) ^ 2 / (Planar.gaussianWeightInv s * s)) := by ring
      _ ≤ _ := by linarith
  have hint : ∀ t : ℝ, 0 < t → IntegrableOn
      (fun s => t / 2 * (‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s) + 1 / (2 * t) * B s)
      (Ioi r) := fun t _ => (hF.const_mul (t / 2)).add (hB.const_mul (1 / (2 * t)))
  have hmain : ∀ t : ℝ, 0 < t → IntegrableOn (fun s => ((g s : ℝ) : ℂ) * q s) (Ioi r) :=
    fun t ht => Integrable.mono' (hint t ht) hmeas
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ (hptw t ht)))
  refine ⟨hmain 1 one_pos, fun t ht => ?_⟩
  have hA : ∫ s in Ioi r, ‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s ≤
      ∫ s in Ioi (0 : ℝ), ‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s := by
    apply setIntegral_mono_set hq.integrable
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => by
        have := grW_pos hs; simp only [Pi.zero_apply]
        have h0 : 0 < s := hs
        unfold Planar.gaussianWeightInv; positivity)
    · exact Eventually.of_forall (Ioi_subset_Ioi hr)
  calc ‖∫ s in Ioi r, ((g s : ℝ) : ℂ) * q s‖
      ≤ ∫ s in Ioi r, (t / 2 * (‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s) +
          1 / (2 * t) * B s) :=
        norm_integral_le_of_norm_le (hint t ht)
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ (hptw t ht)))
    _ = t / 2 * (∫ s in Ioi r, ‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s) +
          1 / (2 * t) * ∫ s in Ioi r, B s := by
        rw [integral_add (hF.const_mul (t / 2)) (hB.const_mul (1 / (2 * t))),
          integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ t / 2)
        linarith

theorem grExpTail (r : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-(1 / 6) * (s - r))) (Ioi r) ∧
    ∫ s in Ioi r, Real.exp (-(1 / 6) * (s - r)) = 6 := by
  have hd : ∀ x ∈ Ioi r, HasDerivAt (fun s : ℝ => -6 * Real.exp (-(1 / 6) * (s - r)))
      (Real.exp (-(1 / 6) * (x - r))) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => -(1 / 6) * (s - r)) (-(1 / 6)) x := by
      simpa using ((hasDerivAt_id x).sub_const r).const_mul (-(1 / 6 : ℝ))
    have := (h1.exp).const_mul (-6)
    exact this.congr_deriv (by ring)
  have hc : ContinuousWithinAt (fun s : ℝ => -6 * Real.exp (-(1 / 6) * (s - r))) (Ici r) r := by
    fun_prop
  have ht : Tendsto (fun s : ℝ => -6 * Real.exp (-(1 / 6) * (s - r))) atTop (𝓝 0) := by
    have hf : Tendsto (fun s : ℝ => s - r) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-r) tendsto_id
    have h1 : Tendsto (fun s : ℝ => -(1 / 6) * (s - r)) atTop atBot :=
      hf.const_mul_atTop_of_neg (by norm_num)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (-6)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd (fun x _ => (Real.exp_pos _).le) ht, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd (fun x _ => (Real.exp_pos _).le) ht]
  simp

theorem grExpInt : Integrable (fun s : ℝ => Real.exp (-(s ^ 2 / 6))) := by
  have e : (fun s : ℝ => Real.exp (-(s ^ 2 / 6))) = fun s => Real.exp (-(1 / 6) * s ^ 2) := by
    funext s; congr 1; ring
  rw [e]; exact integrable_exp_neg_mul_sq (by norm_num)

theorem grTail (q : Planar.Profile) (hq : Planar.MemXG q) (g : ℝ → ℝ) (hgm : Measurable g)
    (hK : ∀ s : ℝ, 1 / 2 ≤ s → (g s) ^ 2 / (Planar.gaussianWeightInv s * s) ≤
      10369 * Real.exp (-(s ^ 2 / 6)))
    (r : ℝ) (hr : 1 / 2 ≤ r) :
    IntegrableOn (fun s => ((g s : ℝ) : ℂ) * q s) (Ioi r) ∧
    ‖∫ s in Ioi r, ((g s : ℝ) : ℂ) * q s‖ ≤
      ((∫ s in Ioi (0 : ℝ), ‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s) / 2 + 3 * 10369) *
        Real.exp (-(r ^ 2 / 12)) := by
  obtain ⟨hTi, hTv⟩ := grExpTail r
  set B : ℝ → ℝ := fun s => 10369 * Real.exp (-(r ^ 2 / 6)) * Real.exp (-(1 / 6) * (s - r)) with hBdef
  have hB : IntegrableOn B (Ioi r) := hTi.const_mul _
  have hbd : ∀ s ∈ Ioi r, (g s) ^ 2 / (Planar.gaussianWeightInv s * s) ≤ B s := by
    intro s hs
    have hs' : r < s := hs
    refine (hK s (by linarith)).trans ?_
    rw [hBdef]; dsimp only
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.2
    nlinarith
  obtain ⟨hI, hbound⟩ := grCore q hq g hgm r (by linarith) B hB hbd
  refine ⟨hI, ?_⟩
  have ht := Real.exp_pos (-(r ^ 2 / 12))
  have hb := hbound _ ht
  have hBint : ∫ s in Ioi r, B s = 6 * (10369 * Real.exp (-(r ^ 2 / 6))) := by
    rw [hBdef]; dsimp only
    rw [integral_const_mul, hTv]; ring
  rw [hBint] at hb
  have e1 : 1 / (2 * Real.exp (-(r ^ 2 / 12))) * (6 * (10369 * Real.exp (-(r ^ 2 / 6)))) =
      3 * 10369 * Real.exp (-(r ^ 2 / 12)) := by
    have : Real.exp (-(r ^ 2 / 6)) = Real.exp (-(r ^ 2 / 12)) * Real.exp (-(r ^ 2 / 12)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; field_simp; ring
  rw [e1] at hb
  linarith

theorem grPoly (r : ℝ) :
    r ^ 2 * Real.exp (-(r ^ 2 / 12)) ≤ 48 * Real.exp (-(r ^ 2 / 16)) := by
  have h : r ^ 2 / 48 ≤ Real.exp (r ^ 2 / 48) := by
    linarith [Real.add_one_le_exp (r ^ 2 / 48)]
  have e : Real.exp (-(r ^ 2 / 12)) = Real.exp (-(r ^ 2 / 16)) * Real.exp (-(r ^ 2 / 48)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e1 : Real.exp (r ^ 2 / 48) * Real.exp (-(r ^ 2 / 48)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-(r ^ 2 / 48))
  have hq := Real.exp_pos (-(r ^ 2 / 16))
  have : r ^ 2 * Real.exp (-(r ^ 2 / 48)) ≤ 48 := by
    have := mul_le_mul_of_nonneg_right h hp.le
    nlinarith
  rw [e]
  calc r ^ 2 * (Real.exp (-(r ^ 2 / 16)) * Real.exp (-(r ^ 2 / 48)))
      = (r ^ 2 * Real.exp (-(r ^ 2 / 48))) * Real.exp (-(r ^ 2 / 16)) := by ring
    _ ≤ 48 * Real.exp (-(r ^ 2 / 16)) := mul_le_mul_of_nonneg_right this hq.le

theorem greenRemainder : GreenRemainder := by
  intro lam q hq
  have hqc : ContinuousOn q (Ioi 0) := hq.smooth.continuousOn
  set A := ∫ s in Ioi (0 : ℝ), ‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s with hA
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_Ioi (fun s hs => by
    have h0 : 0 < s := hs
    unfold Planar.gaussianWeightInv; positivity)
  -- integrability of s^3 q on (0, ∞)
  have hI3 : IntegrableOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi 0) := by
    have := (grCore q hq.memXG (fun s => s ^ 3) (by fun_prop) 0 le_rfl
      (fun s => 10369 * Real.exp (-(s ^ 2 / 6)))
      (grExpInt.const_mul 10369).integrableOn
      (fun s hs => grPt3 s hs)).1
    simpa using this
  have hI1 : ∀ a : ℝ, 0 < a → IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioi a) := by
    intro a ha
    have := (grCore q hq.memXG (fun s => s⁻¹) (by fun_prop) a ha.le _
      (grExpInt.const_mul ((a ^ 3)⁻¹)).integrableOn
      (fun s hs => grPt1 a s ha hs.le)).1
    simpa using this
  have hcont3 : ContinuousOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi 0) :=
    (by fun_prop : Continuous fun s : ℝ => (s : ℂ) ^ 3).continuousOn.mul hqc
  have hcont1 : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioi 0) :=
    (ContinuousOn.inv₀ Complex.continuous_ofReal.continuousOn
      (fun s hs => by exact_mod_cast (show (0 : ℝ) < s from hs).ne')).mul hqc
  obtain ⟨M, hM⟩ : ∃ M : ℂ, M = ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ 3 * q s := ⟨_, rfl⟩
  refine ⟨M, 65 * (A / 2 + 3 * 10369), fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  obtain ⟨hJ3i', hJ3'⟩ := grTail q hq.memXG (fun s => s ^ 3) (by fun_prop)
    (fun s hs => grPt3 s (by linarith)) r hr
  obtain ⟨hJ1i', hJ1'⟩ := grTail q hq.memXG (fun s => s⁻¹) (by fun_prop)
    (fun s hs => (grPt1 (1 / 2) s (by norm_num) hs).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le)) r hr
  have hJ3i : IntegrableOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi r) := by simpa using hJ3i'
  have hJ3 : ‖∫ s in Ioi r, (s : ℂ) ^ 3 * q s‖ ≤ (A / 2 + 3 * 10369) * Real.exp (-(r ^ 2 / 12)) := by
    simpa using hJ3'
  have hJ1 : ‖∫ s in Ioi r, (s : ℂ)⁻¹ * q s‖ ≤ (A / 2 + 3 * 10369) * Real.exp (-(r ^ 2 / 12)) := by
    simpa using hJ1'
  have hM3 : (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) + (∫ s in Ioi r, (s : ℂ) ^ 3 * q s) = M := by
    rw [hM]; exact intervalIntegral.integral_interval_add_Ioi hI3 hJ3i
  -- derivatives
  have hP : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, (s : ℂ) ^ 3 * q s)
      ((r : ℂ) ^ 3 * q r) r :=
    intervalIntegral.integral_hasDerivAt_right
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hr0.le).2 (hI3.mono_set Ioc_subset_Ioi_self))
      (hcont3.stronglyMeasurableAtFilter isOpen_Ioi r hr0)
      (hcont3.continuousAt (Ioi_mem_nhds hr0))
  have ha : 0 < r / 2 := by linarith
  have hD : HasDerivAt (fun u : ℝ => ∫ s in (r / 2)..u, (s : ℂ)⁻¹ * q s)
      ((r : ℂ)⁻¹ * q r) r :=
    intervalIntegral.integral_hasDerivAt_right
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
        ((hI1 (r / 2) ha).mono_set Ioc_subset_Ioi_self))
      (hcont1.stronglyMeasurableAtFilter isOpen_Ioi r hr0)
      (hcont1.continuousAt (Ioi_mem_nhds hr0))
  have hQ : HasDerivAt (fun u : ℝ => ∫ s in Ioi u, (s : ℂ)⁻¹ * q s)
      (-((r : ℂ)⁻¹ * q r)) r := by
    refine (hD.const_sub (∫ s in Ioi (r / 2), (s : ℂ)⁻¹ * q s)).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds (by linarith : r / 2 < r)) (fun u hu => ?_)
    have := intervalIntegral.integral_Ioi_sub_Ioi (hI1 (r / 2) ha) (le_of_lt (show r / 2 < u from hu))
    beta_reduce
    rw [← this]; ring
  have hc : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) ^ 2) (2 * (r : ℂ)) r := by
    have h := hc.mul hc
    have e : (fun u : ℝ => (u : ℂ) ^ 2) = fun u : ℝ => (u : ℂ) * (u : ℂ) := by
      funext u; ring
    rw [e]; exact h.congr_deriv (by ring)
  have hi : HasDerivAt (fun u : ℝ => ((u : ℂ) ^ 2)⁻¹) (-(2 * (r : ℂ)) / ((r : ℂ) ^ 2) ^ 2) r :=
    h2.inv (pow_ne_zero 2 hrne)
  have hG0 := (((hi.mul hP).add (h2.mul hQ)).const_mul (-(1 / 4 : ℂ))).add (hi.const_mul (M / 4))
  have hGfun : greenRem q M = fun u : ℝ => -(1 / 4 : ℂ) * (((u : ℂ) ^ 2)⁻¹ *
      (∫ s in (0 : ℝ)..u, (s : ℂ) ^ 3 * q s) + (u : ℂ) ^ 2 * ∫ s in Ioi u, (s : ℂ)⁻¹ * q s)
      + (M / 4) * ((u : ℂ) ^ 2)⁻¹ := rfl
  have hG : HasDerivAt (greenRem q M)
      (-(1 / 2 : ℂ) * ((r : ℂ) ^ 3)⁻¹ * (∫ s in Ioi r, (s : ℂ) ^ 3 * q s) -
        (1 / 2 : ℂ) * (r : ℂ) * (∫ s in Ioi r, (s : ℂ)⁻¹ * q s)) r := by
    rw [hGfun]
    refine hG0.congr_deriv ?_
    have hMe : M = (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) + (∫ s in Ioi r, (s : ℂ) ^ 3 * q s) :=
      hM3.symm
    beta_reduce
    rw [hMe]
    field_simp
    ring
  have hGr : greenRem q M r = (1 / 4 : ℂ) * ((r : ℂ) ^ 2)⁻¹ * (∫ s in Ioi r, (s : ℂ) ^ 3 * q s) -
      (1 / 4 : ℂ) * (r : ℂ) ^ 2 * (∫ s in Ioi r, (s : ℂ)⁻¹ * q s) := by
    have hMe : M = (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) + (∫ s in Ioi r, (s : ℂ) ^ 3 * q s) :=
      hM3.symm
    show -(1 / 4 : ℂ) * (((r : ℂ) ^ 2)⁻¹ * (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) +
      (r : ℂ) ^ 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * q s) + (M / 4) * ((r : ℂ) ^ 2)⁻¹ = _
    rw [hMe]
    field_simp
    ring
  refine ⟨hG.differentiableAt, ?_⟩
  rw [hG.deriv, hGr]
  set C : ℝ := A / 2 + 3 * 10369 with hC
  have hC0 : 0 ≤ C := by rw [hC]; linarith
  set E : ℝ := Real.exp (-(r ^ 2 / 12)) with hE
  set F : ℝ := Real.exp (-(r ^ 2 / 16)) with hF
  have hE0 : 0 < E := Real.exp_pos _
  have hF0 : 0 < F := Real.exp_pos _
  have hEF : E ≤ F := Real.exp_le_exp.2 (by nlinarith [sq_nonneg r])
  have hpoly : r ^ 2 * E ≤ 48 * F := grPoly r
  have hu : (r ^ 2)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have hv : (r ^ 3)⁻¹ ≤ 8 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg r]
  have hrE : r * E ≤ 96 * F := by nlinarith
  set J3 := ∫ s in Ioi r, (s : ℂ) ^ 3 * q s with hJ3d
  set Q := ∫ s in Ioi r, (s : ℂ)⁻¹ * q s with hQd
  have n1 : ‖(1 / 4 : ℂ) * ((r : ℂ) ^ 2)⁻¹ * J3 - (1 / 4 : ℂ) * (r : ℂ) ^ 2 * Q‖ ≤
      (1 / 4) * (r ^ 2)⁻¹ * ‖J3‖ + (1 / 4) * r ^ 2 * ‖Q‖ := by
    refine (norm_sub_le _ _).trans ?_
    simp [norm_inv, abs_of_pos hr0]
  have n2 : ‖-(1 / 2 : ℂ) * ((r : ℂ) ^ 3)⁻¹ * J3 - (1 / 2 : ℂ) * (r : ℂ) * Q‖ ≤
      (1 / 2) * (r ^ 3)⁻¹ * ‖J3‖ + (1 / 2) * r * ‖Q‖ := by
    refine (norm_sub_le _ _).trans ?_
    simp [norm_inv, abs_of_pos hr0]
  have p1 : (r ^ 2)⁻¹ * ‖J3‖ ≤ 4 * (C * E) :=
    mul_le_mul hu hJ3 (norm_nonneg _) (by norm_num)
  have p3 : (r ^ 3)⁻¹ * ‖J3‖ ≤ 8 * (C * E) :=
    mul_le_mul hv hJ3 (norm_nonneg _) (by norm_num)
  have p2 : r ^ 2 * ‖Q‖ ≤ r ^ 2 * (C * E) := mul_le_mul_of_nonneg_left hJ1 (sq_nonneg r)
  have p4 : r * ‖Q‖ ≤ r * (C * E) := mul_le_mul_of_nonneg_left hJ1 hr0.le
  have q1 : C * (r ^ 2 * E) ≤ C * (48 * F) := mul_le_mul_of_nonneg_left hpoly hC0
  have q2 : C * (r * E) ≤ C * (96 * F) := mul_le_mul_of_nonneg_left hrE hC0
  have q3 : C * E ≤ C * F := mul_le_mul_of_nonneg_left hEF hC0
  nlinarith

end UnforcedLeray.Short.IIIa
