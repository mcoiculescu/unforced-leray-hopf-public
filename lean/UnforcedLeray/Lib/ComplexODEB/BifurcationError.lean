import UnforcedLeray.Lib.ComplexODEB.Cauchy
import UnforcedLeray.Lib.ComplexODEB.Dependence
import UnforcedLeray.Lib.ComplexODE.NeutralSolution

/-!
# B0034 helper: the affine approximation of the Evans function near a neutral mode

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Step of the local bifurcation behind B0034 (`paper/main.tex`, lines 1012–1021; Lin
2003, Theorem 5.9; whole-line analogue: (3.7b) of the Lin-free route, commit 4dd0a82).
Let `α` be a neutral wavenumber of `[a, b]` with real neutral solution `g`
(`g(a) = g(b) = 0`), `F = normalizedF β a c` with `c = a_* + z`, `ε = α² - β²`, and
`M = ∫ g²`. The Wronskian identity (`evansFunction_critical_perturbation`) gives

`D(β, c) G'(b) = ε ∫ G F + z ∫ W G F / (J - z)`.

Writing `F = G + R`, the `L¹` dependence (`Dependence`) bounds `R` and `R'` by
`C_R · L₁`, `L₁ = ∫ |V_{β,c} - V_α|`; splitting `R = R(t_*) + (R - R(t_*))` and using
`|t - t_*| ≤ |J|/m ≤ (2C+1)‖J - z‖/m` in the cone gives (`bifurcation_error`)

`‖D G'(b) - (ε M + z I(z))‖ ≤ C_R L₁ (|ε| (b-a) B + ‖z‖ (‖I₁(z)‖ + 8 B (b-a)(2C+1)/m))`,

where `I(z) = ∫ W g²/(J - z)` and `I₁(z) = ∫ W g/(J - z)`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Sturm
open UnforcedLeray.GaussianPotential NonUniqueEuler.LinODE

/-- Adapted from the draft `Analysis/Rayleigh/Evans/CriticalPerturbationIdentity.lean`
(which does not compile: missing `open`). -/
theorem rayleighPotential_sub_neutral' (α β t : ℝ) {c : ℂ} (hc : 0 < c.im) :
    rayleighPotential β t c - neutralPotential α t =
      ((β : ℂ) ^ 2 - (α : ℂ) ^ 2) - (Wlog t : ℂ) *
        (c - (gaussianCriticalSpeed : ℂ)) / ((neutralOmega t : ℂ) - c) := by
  have hd := rayleigh_denominator_ne_zero hc t
  unfold rayleighPotential neutralPotential gaussianRayleighCoefficient gaussianOffset
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sub]
  field_simp
  ring

/-- The Wronskian perturbation identity (adapted from the same draft). -/
theorem evansFunction_critical_perturbation' (α β a b : ℝ) {c : ℂ}
    (hc : 0 < c.im) (hb : neutralEvansFunction α a b = 0) :
    evansFunction β a b c * neutralNormalizedDerivative α a b =
      ((α : ℂ) ^ 2 - (β : ℂ) ^ 2) *
        (∫ t in a..b, neutralNormalizedF α a t * normalizedF β a c t) +
      (c - (gaussianCriticalSpeed : ℂ)) *
        (∫ t in a..b, (Wlog t : ℂ) * neutralNormalizedF α a t * normalizedF β a c t /
          ((neutralOmega t : ℂ) - c)) := by
  have hN := (neutralNormalizedF_smooth α a).continuous
  have hF := (normalizedF_smooth β a hc).continuous
  have hΩ : Continuous (fun t => (neutralOmega t : ℂ) - c) :=
    (Complex.continuous_ofReal.comp continuous_neutralOmega).sub continuous_const
  have hW : Continuous (fun t => (Wlog t : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_Wlog
  have hI : IntervalIntegrable
      (fun t => neutralNormalizedF α a t * normalizedF β a c t) volume a b :=
    (hN.mul hF).intervalIntegrable a b
  have hJ : IntervalIntegrable
      (fun t => (Wlog t : ℂ) * neutralNormalizedF α a t * normalizedF β a c t /
        ((neutralOmega t : ℂ) - c)) volume a b :=
    (((hW.mul hN).mul hF).div hΩ (fun t => rayleigh_denominator_ne_zero hc t)).intervalIntegrable a b
  rw [evansFunction_mul_neutralDerivative α β a b hc hb]
  have hid : (fun t => (rayleighPotential β t c - neutralPotential α t) *
      neutralNormalizedF α a t * normalizedF β a c t) =
      (fun t => ((β : ℂ) ^ 2 - (α : ℂ) ^ 2) *
          (neutralNormalizedF α a t * normalizedF β a c t) -
        (c - (gaussianCriticalSpeed : ℂ)) *
          ((Wlog t : ℂ) * neutralNormalizedF α a t * normalizedF β a c t /
            ((neutralOmega t : ℂ) - c))) := by
    funext t
    rw [rayleighPotential_sub_neutral' α β t hc]
    ring
  rw [hid, intervalIntegral.integral_sub (hI.const_mul _) (hJ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- The Cauchy integral `∫ φ/(J - z)`. -/
def cauchyInt (a b : ℝ) (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in a..b, (φ t : ℂ) / ((gaussianOffset t : ℂ) - z)

/-- `L¹` distance of the coefficients. -/
def coeffDist (a b α β : ℝ) (c : ℂ) : ℝ :=
  ∫ t in a..b, ‖rayleighPotential β t c - neutralPotential α t‖

theorem criticalShift_denominator (t : ℝ) (z : ℂ) :
    (neutralOmega t : ℂ) - criticalShiftSpeed z = (gaussianOffset t : ℂ) - z := by
  simp [criticalShiftSpeed, gaussianOffset]
  ring

/-- The error bound of the affine approximation. -/
theorem bifurcation_error {a b α β : ℝ} (hcrit : neutralCriticalTime ∈ Ioo a b)
    (hb : neutralReal α a b = 0) {C B : ℝ} (hC : 0 < C)
    (hB : ∀ t ∈ Icc a b, |neutralReal α a t| ≤ B) {z : ℂ}
    (hz : z ∈ criticalApproachCone C)
    (hL : coeffDist a b α β (criticalShiftSpeed z) ≤ 1) :
    ‖evansFunction β a b (criticalShiftSpeed z) * neutralNormalizedDerivative α a b -
        (((α ^ 2 - β ^ 2 : ℝ) : ℂ) * ((∫ t in a..b, neutralReal α a t ^ 2 : ℝ) : ℂ) +
          z * cauchyInt a b (fun t => Wlog t * neutralReal α a t ^ 2) z)‖ ≤
      (B * Real.exp ((b - a) + (∫ t in a..b, ‖neutralPotential α t‖) + 1)) *
        coeffDist a b α β (criticalShiftSpeed z) *
        (|α ^ 2 - β ^ 2| * (b - a) * B +
          ‖z‖ * (‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ +
            8 * B * (b - a) * (2 * C + 1) / offsetLower a b)) := by
  have hab : a < b := hcrit.1.trans hcrit.2
  have hcritI : neutralCriticalTime ∈ Icc a b := Ioo_subset_Icc_self hcrit
  obtain ⟨c, hcdef⟩ : ∃ c, c = criticalShiftSpeed z := ⟨_, rfl⟩
  rw [← hcdef] at hL ⊢
  have hc : 0 < c.im := by rw [hcdef]; simpa using hz.1
  set g := neutralReal α a with hg
  obtain ⟨L₁, hL₁⟩ : ∃ L, L = coeffDist a b α β c := ⟨_, rfl⟩
  rw [← hL₁] at hL ⊢
  obtain ⟨Va, hVa⟩ : ∃ V, V = ∫ t in a..b, ‖neutralPotential α t‖ := ⟨_, rfl⟩
  rw [← hVa]
  obtain ⟨CR, hCR⟩ : ∃ K, K = B * Real.exp ((b - a) + Va + 1) := ⟨_, rfl⟩
  rw [← hCR]
  obtain ⟨m, hm⟩ : ∃ m, m = offsetLower a b := ⟨_, rfl⟩
  rw [← hm]
  have hmpos : 0 < m := by rw [hm]; exact offsetLower_pos a b
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a (left_mem_Icc.mpr hab.le))
  have hL0 : 0 ≤ L₁ := by
    rw [hL₁]; exact intervalIntegral.integral_nonneg hab.le (fun _ _ => norm_nonneg _)
  have hCRL : 0 ≤ CR * L₁ := by
    rw [hCR]; exact mul_nonneg (mul_nonneg hB0 (Real.exp_pos _).le) hL0
  -- the two solutions
  set F := normalizedF β a c with hF
  set F' := normalizedDerivative β a c with hF'
  set G := neutralNormalizedF α a with hG
  set G' := neutralNormalizedDerivative α a with hG'
  have hGg : ∀ t, G t = (g t : ℂ) := fun t => (neutralNormalizedF_eq_ofReal α a t).1
  have hsolF := (normalizedPair_spec β a hc).1.mono (subset_univ (Icc a b))
  have hsolG := (neutralNormalizedPair_spec α a).1.mono (subset_univ (Icc a b))
  have hVc : Continuous (fun t => rayleighPotential β t c) := continuous_rayleighPotential β hc
  have hVα : Continuous (neutralPotential α) := continuous_neutralPotential α
  -- the L¹ dependence bound
  have hdep := norm_sub_le_integral_of_isSolOn' hab.le hVc.continuousOn hVα.continuousOn
    hsolF hsolG (by rw [normalizedF_initial β a hc, neutralNormalizedF_initial])
    (by rw [normalizedDerivative_initial β a hc, neutralNormalizedDerivative_initial])
    (B := B) (fun t ht => by
      rw [(neutralNormalizedF_eq_ofReal α a t).1, Complex.norm_real, Real.norm_eq_abs]
      exact hB t ht)
  have j1 : IntervalIntegrable (fun t => ‖neutralPotential α t‖) volume a b :=
    hVα.norm.intervalIntegrable a b
  have j2 : IntervalIntegrable (fun t => ‖rayleighPotential β t c - neutralPotential α t‖)
      volume a b := (hVc.sub hVα).norm.intervalIntegrable a b
  have j3 : IntervalIntegrable (fun t => ‖rayleighPotential β t c‖) volume a b :=
    hVc.norm.intervalIntegrable a b
  have hL₁eq : (∫ s in a..b, ‖rayleighPotential β s c - neutralPotential α s‖) = L₁ := by
    rw [hL₁]; rfl
  have hVint : (∫ s in a..b, ‖rayleighPotential β s c‖) ≤ Va + L₁ := by
    rw [hVa, ← hL₁eq, ← intervalIntegral.integral_add j1 j2]
    apply intervalIntegral.integral_mono_on hab.le j3 (j1.add j2)
    intro t _
    have := norm_add_le (neutralPotential α t) (rayleighPotential β t c - neutralPotential α t)
    simp only [add_sub_cancel] at this
    exact this
  have hRpair : ∀ t ∈ Icc a b, ‖(F t - G t, F' t - G' t)‖ ≤ CR * L₁ := by
    intro t ht
    refine (hdep t ht).trans ?_
    rw [hL₁eq, hCR]
    have hexp : Real.exp ((b - a) + ∫ s in a..b, ‖rayleighPotential β s c‖) ≤
        Real.exp ((b - a) + Va + 1) := Real.exp_le_exp.mpr (by linarith)
    have hBL : 0 ≤ B * L₁ := mul_nonneg hB0 hL0
    calc (B * L₁) * Real.exp ((b - a) + ∫ s in a..b, ‖rayleighPotential β s c‖)
        ≤ (B * L₁) * Real.exp ((b - a) + Va + 1) := mul_le_mul_of_nonneg_left hexp hBL
      _ = B * Real.exp ((b - a) + Va + 1) * L₁ := by ring
  set R : ℝ → ℂ := fun t => F t - G t with hR
  have hRb : ∀ t ∈ Icc a b, ‖R t‖ ≤ CR * L₁ := fun t ht =>
    (norm_fst_le (F t - G t, F' t - G' t)).trans (hRpair t ht)
  have hR'b : ∀ t ∈ Icc a b, ‖F' t - G' t‖ ≤ CR * L₁ := fun t ht =>
    (norm_snd_le (F t - G t, F' t - G' t)).trans (hRpair t ht)
  have hRlip : ∀ t ∈ Icc a b, ‖R t - R neutralCriticalTime‖ ≤
      CR * L₁ * |t - neutralCriticalTime| := by
    intro t ht
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := R) (f' := fun s => F' s - G' s)
      (fun x _ => ((hasDerivAt_normalizedF β a hc x).sub
        (hasDerivAt_neutralNormalizedF α a x)).hasDerivWithinAt) hR'b hcritI ht
    rwa [Real.norm_eq_abs] at h
  -- continuity facts
  have hdenne : ∀ t, ((gaussianOffset t : ℂ) - z) ≠ 0 := fun t => criticalDenominator_ne_zero _ hz.1
  have hdenc : Continuous (fun t => (gaussianOffset t : ℂ) - z) :=
    (Complex.continuous_ofReal.comp continuous_gaussianOffset').sub continuous_const
  have hdeq : ∀ t, (neutralOmega t : ℂ) - c = (gaussianOffset t : ℂ) - z := fun t => by
    rw [hcdef]; exact criticalShift_denominator t z
  have hFc : Continuous F := (normalizedF_smooth β a hc).continuous
  have hGc : Continuous G := (neutralNormalizedF_smooth α a).continuous
  have hWc : Continuous (fun t => (Wlog t : ℂ)) := Complex.continuous_ofReal.comp continuous_Wlog
  -- the identity
  have hneutral : neutralEvansFunction α a b = 0 := by
    rw [neutralEvansFunction_eq_zero_iff]; exact hb
  have hid := evansFunction_critical_perturbation' α β a b hc hneutral
  have hcz : c - (gaussianCriticalSpeed : ℂ) = z := by simp [hcdef, criticalShiftSpeed]
  rw [hcz] at hid
  set ε : ℂ := ((α ^ 2 - β ^ 2 : ℝ) : ℂ) with hε
  have hεc : (α : ℂ) ^ 2 - (β : ℂ) ^ 2 = ε := by rw [hε]; push_cast; ring
  rw [hεc] at hid
  -- integrability of all pieces
  have i1 : IntervalIntegrable (fun t => G t * F t) volume a b := (hGc.mul hFc).intervalIntegrable a b
  have i2 : IntervalIntegrable (fun t => (Wlog t : ℂ) * G t * F t / ((gaussianOffset t : ℂ) - z)) volume a b :=
    (((hWc.mul hGc).mul hFc).div hdenc hdenne).intervalIntegrable a b
  have i3 : IntervalIntegrable (fun t => G t * G t) volume a b := (hGc.mul hGc).intervalIntegrable a b
  have i4 : IntervalIntegrable (fun t => (Wlog t : ℂ) * G t * G t / ((gaussianOffset t : ℂ) - z)) volume a b :=
    (((hWc.mul hGc).mul hGc).div hdenc hdenne).intervalIntegrable a b
  have i5 : IntervalIntegrable (fun t => (Wlog t : ℂ) * G t / ((gaussianOffset t : ℂ) - z)) volume a b :=
    ((hWc.mul hGc).div hdenc hdenne).intervalIntegrable a b
  -- rewrite `M`, `I(z)` and `I₁(z)` as integrals of `G`
  have hM : ((∫ t in a..b, g t ^ 2 : ℝ) : ℂ) = ∫ t in a..b, G t * G t := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hGg]
    push_cast
    ring
  have hI : cauchyInt a b (fun t => Wlog t * g t ^ 2) z =
      ∫ t in a..b, (Wlog t : ℂ) * G t * G t / ((gaussianOffset t : ℂ) - z) := by
    unfold cauchyInt
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hGg]
    push_cast
    ring
  have hI₁ : cauchyInt a b (fun t => Wlog t * g t) z =
      ∫ t in a..b, (Wlog t : ℂ) * G t / ((gaussianOffset t : ℂ) - z) := by
    unfold cauchyInt
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hGg]
    push_cast
    ring
  have hid2 : (∫ t in a..b, (Wlog t : ℂ) * neutralNormalizedF α a t * normalizedF β a c t /
      ((neutralOmega t : ℂ) - c)) = ∫ t in a..b, (Wlog t : ℂ) * G t * F t / ((gaussianOffset t : ℂ) - z) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hdeq]
    rfl
  rw [hid2] at hid
  -- the remainder as one integral
  set Rs := R neutralCriticalTime with hRs
  have hsplit : evansFunction β a b c * neutralNormalizedDerivative α a b -
      (ε * ((∫ t in a..b, g t ^ 2 : ℝ) : ℂ) + z * cauchyInt a b (fun t => Wlog t * g t ^ 2) z) -
      z * Rs * cauchyInt a b (fun t => Wlog t * g t) z =
      ∫ t in a..b, (ε * (G t * R t) + z * ((Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z))) := by
    rw [hid, hM, hI, hI₁]
    have i6 : IntervalIntegrable (fun t => ε * (G t * R t)) volume a b :=
      ((hGc.mul (hFc.sub hGc)).intervalIntegrable a b).const_mul ε
    have i7 : IntervalIntegrable (fun t => z * ((Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z)))
        volume a b :=
      ((((hWc.mul hGc).mul ((hFc.sub hGc).sub continuous_const)).div hdenc hdenne
        ).intervalIntegrable a b).const_mul z
    rw [intervalIntegral.integral_add i6 i7, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have e1 : (∫ t in a..b, G t * R t) = (∫ t in a..b, G t * F t) - ∫ t in a..b, G t * G t := by
      rw [← intervalIntegral.integral_sub i1 i3]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hR]
      ring
    have e2 : (∫ t in a..b, (Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z)) =
        (∫ t in a..b, (Wlog t : ℂ) * G t * F t / ((gaussianOffset t : ℂ) - z)) -
          (∫ t in a..b, (Wlog t : ℂ) * G t * G t / ((gaussianOffset t : ℂ) - z)) -
          Rs * ∫ t in a..b, (Wlog t : ℂ) * G t / ((gaussianOffset t : ℂ) - z) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub i2 i4,
        ← intervalIntegral.integral_sub (i2.sub i4) (i5.const_mul Rs)]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hR]
      field_simp [hdenne t]
    rw [e1, e2]
    ring
  -- pointwise bound of the remainder integrand
  have hpt : ∀ t ∈ Icc a b,
      ‖ε * (G t * R t) + z * ((Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z))‖ ≤
        |α ^ 2 - β ^ 2| * B * (CR * L₁) +
          ‖z‖ * (8 * B * (CR * L₁) * (2 * C + 1) / m) := by
    intro t ht
    have hGt : ‖G t‖ ≤ B := by rw [hGg, Complex.norm_real, Real.norm_eq_abs]; exact hB t ht
    have hW8 : ‖(Wlog t : ℂ)‖ ≤ 8 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Wlog_pos t)]; exact Wlog_le_eight t
    have hdpos : 0 < ‖((gaussianOffset t : ℂ) - z)‖ := norm_pos_iff.mpr (hdenne t)
    have hcone := abs_add_norm_le_cone hC hz (gaussianOffset t)
    have hJ := offsetLower_mul_le_critical ht hcritI
    rw [← hm] at hJ
    have hdist : |t - neutralCriticalTime| ≤ (2 * C + 1) * ‖((gaussianOffset t : ℂ) - z)‖ / m := by
      rw [le_div_iff₀ hmpos]
      have : m * |t - neutralCriticalTime| ≤ (2 * C + 1) * ‖((gaussianOffset t : ℂ) - z)‖ := by
        linarith [norm_nonneg z]
      linarith
    have h1 : ‖ε * (G t * R t)‖ ≤ |α ^ 2 - β ^ 2| * B * (CR * L₁) := by
      rw [norm_mul, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs]
      have := mul_le_mul hGt (hRb t ht) (norm_nonneg _) hB0
      calc |α ^ 2 - β ^ 2| * (‖G t‖ * ‖R t‖) ≤ |α ^ 2 - β ^ 2| * (B * (CR * L₁)) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := by ring
    have h2 : ‖(Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z)‖ ≤ 8 * B * (CR * L₁) * (2 * C + 1) / m := by
      rw [norm_div, norm_mul, norm_mul, div_le_iff₀ hdpos]
      have hlip := hRlip t ht
      have e1 : ‖R t - Rs‖ ≤ CR * L₁ * ((2 * C + 1) * ‖((gaussianOffset t : ℂ) - z)‖ / m) :=
        hlip.trans (mul_le_mul_of_nonneg_left hdist hCRL)
      have e2 : ‖(Wlog t : ℂ)‖ * ‖G t‖ ≤ 8 * B :=
        mul_le_mul hW8 hGt (norm_nonneg _) (by norm_num)
      calc ‖(Wlog t : ℂ)‖ * ‖G t‖ * ‖R t - Rs‖ ≤ 8 * B * (CR * L₁ * ((2 * C + 1) * ‖((gaussianOffset t : ℂ) - z)‖ / m)) :=
            mul_le_mul e2 e1 (norm_nonneg _) (by positivity)
        _ = 8 * B * (CR * L₁) * (2 * C + 1) / m * ‖((gaussianOffset t : ℂ) - z)‖ := by ring
    calc ‖ε * (G t * R t) + z * ((Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z))‖
        ≤ ‖ε * (G t * R t)‖ + ‖z * ((Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z))‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul z]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg z))
  have hint_bound : ‖∫ t in a..b, (ε * (G t * R t) + z * ((Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z)))‖
      ≤ (|α ^ 2 - β ^ 2| * B * (CR * L₁) + ‖z‖ * (8 * B * (CR * L₁) * (2 * C + 1) / m)) *
        |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hab.le] at ht
    exact hpt t (Ioc_subset_Icc_self ht)
  have hRs : ‖Rs‖ ≤ CR * L₁ := hRb _ hcritI
  -- assemble
  have htri : ‖evansFunction β a b c * neutralNormalizedDerivative α a b -
      (ε * ((∫ t in a..b, g t ^ 2 : ℝ) : ℂ) + z * cauchyInt a b (fun t => Wlog t * g t ^ 2) z)‖ ≤
      ‖∫ t in a..b, (ε * (G t * R t) + z * ((Wlog t : ℂ) * G t * (R t - Rs) / ((gaussianOffset t : ℂ) - z)))‖ +
        ‖z * Rs * cauchyInt a b (fun t => Wlog t * g t) z‖ := by
    rw [← hsplit]
    have := norm_add_le (evansFunction β a b c * neutralNormalizedDerivative α a b -
      (ε * ((∫ t in a..b, g t ^ 2 : ℝ) : ℂ) + z * cauchyInt a b (fun t => Wlog t * g t ^ 2) z) -
      z * Rs * cauchyInt a b (fun t => Wlog t * g t) z)
      (z * Rs * cauchyInt a b (fun t => Wlog t * g t) z)
    simpa using this
  refine htri.trans ?_
  rw [abs_of_pos (sub_pos.mpr hab)] at hint_bound
  rw [norm_mul, norm_mul]
  have hz0 := norm_nonneg z
  have hI0 := norm_nonneg (cauchyInt a b (fun t => Wlog t * g t) z)
  have e3 : ‖z‖ * ‖Rs‖ * ‖cauchyInt a b (fun t => Wlog t * g t) z‖ ≤
      ‖z‖ * (CR * L₁) * ‖cauchyInt a b (fun t => Wlog t * g t) z‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRs hz0) hI0
  calc _ ≤ (|α ^ 2 - β ^ 2| * B * (CR * L₁) + ‖z‖ * (8 * B * (CR * L₁) * (2 * C + 1) / m)) *
          (b - a) + ‖z‖ * (CR * L₁) * ‖cauchyInt a b (fun t => Wlog t * g t) z‖ := by
        linarith [hint_bound]
    _ = _ := by ring

end UnforcedLeray.ComplexODEB
