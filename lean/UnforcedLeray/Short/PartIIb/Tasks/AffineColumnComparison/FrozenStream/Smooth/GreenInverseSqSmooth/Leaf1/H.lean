import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseOrderTwo

/-!
# Part II-b, task `PartII-b:G4/2/1/2/1/1` (`greenSqH`)

Source: `the November 2 reference manuscript`, lines 2347-2352.

`sqH lam q v = sqCoeff lam v * (G(√v)/v)` with `G = greenInverse q`.  The bound on `G(√v)/v` is
uniform on `(0,∞)`: for `v ≤ 1` the hypothesis `‖G r‖ ≤ C r²` gives `‖G(√v)/v‖ ≤ |C|`; for
`v ≥ 1` the head/tail estimates (`GreenOrderTwoAux`) give `‖G r‖ ≤ M₀ r²`.  The coefficient is
bounded by `4(1+v)e^{-v/4}/Re λ ≤ (32/Re λ) e^{-v/8}`, an integrable majorant.  Continuity of `G`
on `(0,∞)` comes from continuity of the two primitives `∫₀^r s³q` and `∫_r^∞ s⁻¹q`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- Continuity of a primitive `u ↦ ∫₀^u f` on `(0,∞)`. -/
lemma greenH_prim_contOn {f : ℝ → ℂ} (hf : ∀ R : ℝ, IntegrableOn f (Ioc 0 R)) :
    ContinuousOn (fun u : ℝ => ∫ v in (0 : ℝ)..u, f v) (Ioi 0) := by
  intro u0 hu0
  have hu0' : (0 : ℝ) < u0 := hu0
  have hR : u0 < u0 + 1 := by linarith
  have hint : IntegrableOn f (uIcc 0 (u0 + 1)) := by
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ u0 + 1), integrableOn_Icc_iff_integrableOn_Ioc]
    exact hf _
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) hint
  have hmem : uIcc 0 (u0 + 1) ∈ 𝓝 u0 := by
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ u0 + 1)]
    exact Icc_mem_nhds hu0' hR
  exact (hc.continuousAt hmem).continuousWithinAt

/-- Splitting a tail: `∫_{(r,∞)} f = ∫_{(a,∞)} f - ∫_a^r f` for `a ≤ r`. -/
lemma greenH_tail_split {f : ℝ → ℂ} {a r : ℝ} (har : a ≤ r) (hf : IntegrableOn f (Ioi a)) :
    ∫ s in Ioi r, f s = (∫ s in Ioi a, f s) - ∫ s in a..r, f s := by
  have hdisj : Disjoint (Ioc a r) (Ioi r) :=
    Set.disjoint_left.2 (fun x hx hx' => absurd hx.2 (not_le.2 hx'))
  have hsplit : ∫ s in Ioi a, f s = (∫ s in Ioc a r, f s) + ∫ s in Ioi r, f s := by
    rw [← Ioc_union_Ioi_eq_Ioi har]
    exact setIntegral_union hdisj measurableSet_Ioi (hf.mono_set Ioc_subset_Ioi_self)
      (hf.mono_set (Ioi_subset_Ioi har))
  rw [hsplit, intervalIntegral.integral_of_le har]
  ring

/-- Continuity of a tail `r ↦ ∫_{(r,∞)} f` on `(0,∞)`. -/
lemma greenH_tail_contOn {f : ℝ → ℂ} (hf : ∀ a : ℝ, 0 < a → IntegrableOn f (Ioi a)) :
    ContinuousOn (fun r : ℝ => ∫ s in Ioi r, f s) (Ioi 0) := by
  intro r0 hr0
  have hr0' : (0 : ℝ) < r0 := hr0
  have hap : (0 : ℝ) < r0 / 2 := by linarith
  have hint : IntegrableOn f (uIcc (r0 / 2) (r0 + 1)) := by
    rw [uIcc_of_le (by linarith : r0 / 2 ≤ r0 + 1), integrableOn_Icc_iff_integrableOn_Ioc]
    exact (hf _ hap).mono_set Ioc_subset_Ioi_self
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) hint
  have hmem : uIcc (r0 / 2) (r0 + 1) ∈ 𝓝 r0 := by
    rw [uIcc_of_le (by linarith : r0 / 2 ≤ r0 + 1)]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hcA : ContinuousAt (fun x : ℝ => ∫ t in r0 / 2..x, f t) r0 := hc.continuousAt hmem
  have key : ContinuousAt (fun r : ℝ => (∫ s in Ioi (r0 / 2), f s) - ∫ t in r0 / 2..r, f t) r0 :=
    continuousAt_const.sub hcA
  apply ContinuousAt.continuousWithinAt
  refine key.congr ?_
  filter_upwards [Ioi_mem_nhds (show r0 / 2 < r0 by linarith)] with r hr
  exact (greenH_tail_split (show r0 / 2 ≤ r from (show r0 / 2 < r from hr).le) (hf _ hap)).symm

/-- The cube-weighted integrand is locally integrable up to `0`. -/
lemma greenH_cube_integrableOn {f : Planar.Profile} (hf : Planar.MemXG f) (R : ℝ) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ 3 * f s) (Ioc 0 R) := by
  have hfin : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s) (Ioc 0 R) :=
    hf.integrable.mono_set Ioc_subset_Ioi_self
  have hc : Continuous fun s : ℝ => s ^ 5 / (8 * Real.pi) := by fun_prop
  have hP : IntegrableOn (fun s : ℝ => s ^ 5 / (8 * Real.pi)) (Ioc 0 R) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmaj : IntegrableOn (fun s : ℝ => 1 / 2 * (‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s)
      + s ^ 5 / (8 * Real.pi)) (Ioc 0 R) :=
    (Integrable.const_mul hfin _).add hP
  refine Integrable.mono' hmaj ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ => (s : ℂ) ^ 3).aestronglyMeasurable.mul
      (hf.measurable.mono_set Ioc_subset_Ioi_self)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 < s := hs.1
    have hamgm := GreenOrderTwoAux.amgm_head (L := 1) (w := Planar.gaussianWeightInv s)
      (s := s) (u := ‖f s‖) one_pos (GreenOrderTwoAux.weight_pos s) hs0.le (norm_nonneg _)
    have h2 : s ^ 5 / (2 * 1 * Planar.gaussianWeightInv s) ≤ s ^ 5 / (8 * Real.pi) :=
      div_le_div_of_nonneg_left (pow_nonneg hs0.le 5) (by positivity)
        (by linarith [GreenOrderTwoAux.weight_ge s])
    show ‖(s : ℂ) ^ 3 * f s‖ ≤ _
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    linarith

/-- The Green inverse of an `X_G` profile is continuous on `(0,∞)` when `q` is. -/
lemma greenH_green_contOn {q : Planar.Profile} (hq : Planar.MemXG q)
    (hs : ContinuousOn q (Ioi 0)) :
    ContinuousOn (fun r : ℝ => Planar.greenInverse q r) (Ioi 0) := by
  have hA : ContinuousOn (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) (Ioi 0) :=
    greenH_prim_contOn (fun R => greenH_cube_integrableOn hq R)
  have hB : ContinuousOn (fun r : ℝ => ∫ s in Ioi r, (s : ℂ)⁻¹ * q s) (Ioi 0) :=
    greenH_tail_contOn (fun a ha => GreenOrderTwoAux.integrableOn_tail hq ha)
  have hsq : ContinuousOn (fun r : ℝ => (r : ℂ) ^ 2) (Ioi 0) :=
    (by fun_prop : Continuous fun r : ℝ => (r : ℂ) ^ 2).continuousOn
  have hsqi : ContinuousOn (fun r : ℝ => ((r : ℂ) ^ 2)⁻¹) (Ioi 0) :=
    hsq.inv₀ (fun r hr => pow_ne_zero _ (Complex.ofReal_ne_zero.2 (show (0 : ℝ) < r from hr).ne'))
  unfold Planar.greenInverse
  exact continuousOn_const.mul ((hsqi.mul hA).add (hsq.mul hB))

/-- Growth bound at infinity: `‖G r‖ ≤ M₀ r²` for `r ≥ 1`. -/
lemma greenH_green_le_of_one_le {f : Planar.Profile} (hf : Planar.MemXG f) {r : ℝ} (hr : 1 ≤ r) :
    ‖Planar.greenInverse f r‖ ≤ (GreenOrderTwoAux.wMass f + 1 / (48 * Real.pi)
      + 1 / (16 * Real.pi)) / 4 * r ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hsplit := GreenOrderTwoAux.norm_greenInverse_le_split f hr0
  have hA := GreenOrderTwoAux.norm_head_le hf hr0
  have hB := GreenOrderTwoAux.norm_tail_le hf hr0
  have hw := GreenOrderTwoAux.wMass_nonneg f
  have hp1 : 0 ≤ 1 / (48 * Real.pi) := by positivity
  have hp2 : 0 ≤ 1 / (16 * Real.pi) := by positivity
  have hc1 : 0 ≤ GreenOrderTwoAux.wMass f / 2 + 1 / (48 * Real.pi) := by linarith
  have hc2 : 0 ≤ GreenOrderTwoAux.wMass f / 2 + 1 / (16 * Real.pi) := by linarith
  have hAr : ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s‖ / r ^ 2
      ≤ r ^ 2 * (GreenOrderTwoAux.wMass f / 2 + 1 / (48 * Real.pi)) := by
    rw [div_le_iff₀ (pow_pos hr0 2)]
    have e : r ^ 3 / 2 * GreenOrderTwoAux.wMass f + r ^ 3 / (48 * Real.pi)
        = r ^ 3 * (GreenOrderTwoAux.wMass f / 2 + 1 / (48 * Real.pi)) := by ring
    have h34 : r ^ 3 ≤ r ^ 2 * r ^ 2 := by nlinarith
    have h3 : r ^ 3 * (GreenOrderTwoAux.wMass f / 2 + 1 / (48 * Real.pi))
        ≤ r ^ 2 * r ^ 2 * (GreenOrderTwoAux.wMass f / 2 + 1 / (48 * Real.pi)) :=
      mul_le_mul_of_nonneg_right h34 hc1
    nlinarith [hA, e, h3]
  have hBr : r ^ 2 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * f s‖
      ≤ r ^ 2 * (GreenOrderTwoAux.wMass f / 2 + 1 / (16 * Real.pi)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0.le 2)
    have hd : (GreenOrderTwoAux.wMass f / 2 + 1 / (16 * Real.pi)) / r
        ≤ GreenOrderTwoAux.wMass f / 2 + 1 / (16 * Real.pi) :=
      div_le_self hc2 hr
    exact hB.trans hd
  have e2 : (1 / 4 : ℝ) * (r ^ 2 * (GreenOrderTwoAux.wMass f / 2 + 1 / (48 * Real.pi))
      + r ^ 2 * (GreenOrderTwoAux.wMass f / 2 + 1 / (16 * Real.pi)))
      = (GreenOrderTwoAux.wMass f + 1 / (48 * Real.pi) + 1 / (16 * Real.pi)) / 4 * r ^ 2 := by
    ring
  have hfin := mul_le_mul_of_nonneg_left (add_le_add hAr hBr) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  nlinarith [hsplit, hfin, e2]

/-- Coefficient bound: `‖sqCoeff λ u‖ ≤ 4(1+u)e^{-u/4}/Re λ` for `u ≥ 0`. -/
lemma greenH_coeff_norm_le {lam : ℂ} (hlam : 0 < lam.re) {u : ℝ} (hu : 0 ≤ u) :
    ‖sqCoeff lam u‖ ≤ 4 * (1 + u) * Real.exp (-u / 4) / lam.re := by
  unfold sqCoeff
  have hre : (lam + 2 * Complex.I * ((Real.exp (-u / 4) : ℝ) : ℂ)).re = lam.re := by
    simp [-Complex.ofReal_exp]
  have hden := Complex.re_le_norm (lam + 2 * Complex.I * ((Real.exp (-u / 4) : ℝ) : ℂ))
  rw [hre] at hden
  have hnum : ‖2 * Complex.I * (((u / 4 - 2) * Real.exp (-u / 4) : ℝ) : ℂ)‖
      ≤ 4 * (1 + u) * Real.exp (-u / 4) := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have habs : |u / 4 - 2| ≤ 2 * (1 + u) := by
      rw [abs_le]
      constructor <;> linarith
    have := mul_le_mul_of_nonneg_right habs (Real.exp_pos (-u / 4)).le
    nlinarith
  rw [norm_div]
  refine (div_le_div_of_nonneg_left (norm_nonneg _) hlam hden).trans ?_
  exact div_le_div_of_nonneg_right hnum hlam.le

/-- Continuity of the coefficient `u ↦ sqCoeff λ u` when `Re λ > 0`. -/
lemma greenH_sqCoeff_cont {lam : ℂ} (hl : 0 < lam.re) : Continuous (sqCoeff lam) := by
  unfold sqCoeff
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro u h0
  have := congrArg Complex.re h0
  simp [-Complex.ofReal_exp] at this
  linarith

/-- **Sub 1** (SP 2347-2352): `sqH` is integrable on `(0,∞)`, continuous there and bounded on
`(0,1]`. -/
theorem greenSqH : UnforcedLeray.Short.IIb.GreenSqH := by
  intro lam q hE hO
  obtain ⟨C, hC⟩ := hO
  have hlam : 0 < lam.re := hE.re_pos
  have hq : Planar.MemXG q := hE.memXG
  have hcG := greenH_green_contOn hq hE.smooth.continuousOn
  obtain ⟨M0, hM0def⟩ : ∃ M0 : ℝ, M0 = (GreenOrderTwoAux.wMass q + 1 / (48 * Real.pi)
      + 1 / (16 * Real.pi)) / 4 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M0 := by
    rw [hM0def]
    have hw := GreenOrderTwoAux.wMass_nonneg q
    have hp1 : 0 ≤ 1 / (48 * Real.pi) := by positivity
    have hp2 : 0 ≤ 1 / (16 * Real.pi) := by positivity
    apply div_nonneg _ (by norm_num)
    linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = |C| + M0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact add_nonneg (abs_nonneg C) hM0
  have hK : ∀ u : ℝ, 0 < u →
      ‖Planar.greenInverse q (Real.sqrt u) / (u : ℂ)‖ ≤ K := by
    intro u hu
    have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu.le, div_le_iff₀ hu, hKdef]
    rcases le_total u 1 with h1 | h1
    · have hr1 : Real.sqrt u ≤ 1 := by simpa using Real.sqrt_le_sqrt h1
      have hr0 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
      have h := hC (Real.sqrt u) hr0 hr1
      rw [hsq] at h
      calc ‖Planar.greenInverse q (Real.sqrt u)‖ ≤ C * u := h
        _ ≤ |C| * u := mul_le_mul_of_nonneg_right (le_abs_self C) hu.le
        _ ≤ (|C| + M0) * u := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM0) hu.le
    · have hr1 : 1 ≤ Real.sqrt u := by simpa using Real.sqrt_le_sqrt h1
      have h := greenH_green_le_of_one_le hq hr1
      rw [hsq, ← hM0def] at h
      calc ‖Planar.greenInverse q (Real.sqrt u)‖ ≤ M0 * u := h
        _ ≤ (|C| + M0) * u := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg C)) hu.le
  have hcont : ContinuousOn (sqH lam q) (Ioi 0) := by
    have hc1 : ContinuousOn (sqCoeff lam) (Ioi 0) := (greenH_sqCoeff_cont hlam).continuousOn
    have hcomp : ContinuousOn (fun v : ℝ => Planar.greenInverse q (Real.sqrt v)) (Ioi 0) :=
      hcG.comp Real.continuous_sqrt.continuousOn (fun v hv => Real.sqrt_pos.2 hv)
    have hc2 : ContinuousOn (fun v : ℝ => Planar.greenInverse q (Real.sqrt v) / (v : ℂ)) (Ioi 0) :=
      hcomp.div Complex.continuous_ofReal.continuousOn
        (fun v hv => Complex.ofReal_ne_zero.2 (show (0 : ℝ) < v from hv).ne')
    unfold sqH
    exact hc1.mul hc2
  have hbound : ∀ u : ℝ, 0 < u →
      ‖sqH lam q u‖ ≤ (32 * K / lam.re) * Real.exp (-(1 / 8) * u) := by
    intro u hu
    have hEpos : 0 < Real.exp (-(1 / 8) * u) := Real.exp_pos _
    have hexp1 : Real.exp (-u / 4) = Real.exp (-(1 / 8) * u) * Real.exp (-(1 / 8) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp2 : Real.exp ((1 / 8) * u) * Real.exp (-(1 / 8) * u) = 1 := by
      rw [← Real.exp_add, show (1 / 8 : ℝ) * u + -(1 / 8) * u = 0 by ring, Real.exp_zero]
    have h1 : 1 + u ≤ 8 * Real.exp ((1 / 8) * u) := by
      have := Real.add_one_le_exp ((1 / 8) * u)
      linarith
    have h8' : (1 + u) * Real.exp (-(1 / 8) * u) ≤ 8 * Real.exp ((1 / 8) * u) * Real.exp (-(1 / 8) * u) :=
      mul_le_mul_of_nonneg_right h1 hEpos.le
    rw [mul_assoc, hexp2, mul_one] at h8'
    have hcoef2 : 4 * (1 + u) * Real.exp (-u / 4) / lam.re
        ≤ 32 * Real.exp (-(1 / 8) * u) / lam.re := by
      apply div_le_div_of_nonneg_right _ hlam.le
      rw [hexp1]
      have := mul_le_mul_of_nonneg_right h8' hEpos.le
      nlinarith
    have hsqH : sqH lam q u = sqCoeff lam u * (Planar.greenInverse q (Real.sqrt u) / (u : ℂ)) := rfl
    rw [hsqH, norm_mul]
    have hcoefnn : 0 ≤ 4 * (1 + u) * Real.exp (-u / 4) / lam.re := by
      apply div_nonneg _ hlam.le
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.exp_pos _).le
    calc ‖sqCoeff lam u‖ * ‖Planar.greenInverse q (Real.sqrt u) / (u : ℂ)‖
        ≤ (4 * (1 + u) * Real.exp (-u / 4) / lam.re) * K :=
          mul_le_mul (greenH_coeff_norm_le hlam hu.le) (hK u hu) (norm_nonneg _) hcoefnn
      _ ≤ (32 * Real.exp (-(1 / 8) * u) / lam.re) * K :=
          mul_le_mul_of_nonneg_right hcoef2 hK0
      _ = (32 * K / lam.re) * Real.exp (-(1 / 8) * u) := by ring
  have hmaj : Integrable (fun u : ℝ => (32 * K / lam.re) * Real.exp (-(1 / 8) * u))
      (volume.restrict (Ioi 0)) :=
    (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 8)).const_mul _
  have hint : IntegrableOn (sqH lam q) (Ioi 0) := by
    refine Integrable.mono' hmaj (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hbound u hu
  refine ⟨hint, hcont, 32 * K / lam.re, fun u hu0 _ => ?_⟩
  have hu : (0 : ℝ) < u := hu0
  refine (hbound u hu).trans ?_
  have hE1 : Real.exp (-(1 / 8) * u) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  exact mul_le_of_le_one_right (div_nonneg (mul_nonneg (by norm_num) hK0) hlam.le) hE1

end UnforcedLeray.Short.IIb
