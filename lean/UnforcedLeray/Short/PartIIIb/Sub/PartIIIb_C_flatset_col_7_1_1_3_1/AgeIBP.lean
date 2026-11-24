import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3_1.Pointwise

/-!
# Age (`s`) integration by parts for the scalar resolvent pairing
(helper of `PartIII-b:C/flatset/col/7/1/1/3/1`)

For a smooth scalar profile `f` vanishing for `p.1 < s0` (`s0 > 0`), integrates `ageIntegrand μ S R f`
over `Ioi 0 ×ˢ B0579.cell c` by parts in `s`, using `deriv (thetaS S) ≤ 0` to drop the upper-cutoff
derivative term with the good sign.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi intervalIntegral
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.Short.IIIa (flatDt)
open UnforcedLeray.Short.PartIIa (pdS)

theorem pdS_eq_deriv_slice {ψ : Profile → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p : Profile) :
    pdS ψ p = deriv (fun s' => ψ (s', p.2)) p.1 :=
  pdS_eq_flatDt' (Φ := fun s x _ => ψ (s, x)) (i := 0) hψ p

theorem hasDerivAt_slice_pdS {ψ : Profile → ℝ} (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s' => ψ (s', x)) (pdS ψ (s, x)) s := by
  have hs : ContDiff ℝ ∞ (fun s' : ℝ => ψ (s', x)) :=
    hψ.comp (contDiff_id.prodMk contDiff_const)
  rw [pdS_eq_deriv_slice hψ (s, x)]
  exact (hs.differentiable (by simp) s).hasDerivAt

theorem pdS_fCut (S R : ℝ) {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (p : Profile) :
    pdS (fCut S R f) p =
      (deriv (thetaS S) p.1 * f p + thetaS S p.1 * pdS f p) * chiR R p.2.2 := by
  have h1 := hasDerivAt_slice_pdS (contDiff_fCut S R hf) p.1 p.2
  have hθ : HasDerivAt (thetaS S) (deriv (thetaS S) p.1) p.1 :=
    ((contDiff_thetaS S).differentiable (by simp) p.1).hasDerivAt
  have hf' := hasDerivAt_slice_pdS hf p.1 p.2
  have h2 : HasDerivAt (fun s' => (thetaS S s' * f (s', p.2)) * chiR R p.2.2)
      ((deriv (thetaS S) p.1 * f p + thetaS S p.1 * pdS f p) * chiR R p.2.2) p.1 :=
    (hθ.mul hf').mul_const (chiR R p.2.2)
  have hfun : (fun s' => fCut S R f (s', p.2)) =
      fun s' => (thetaS S s' * f (s', p.2)) * chiR R p.2.2 := by
    funext s'; unfold fCut; ring
  rw [hfun] at h1
  exact h1.unique h2

/-- Antiderivative in `s` of the `s ∂_s` integration by parts:
`H(s, x) = (1/2) s^{-1/2} θ_S(s) χ_R(η) f(s, x)²`. -/
def ageH (S R : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ :=
  (1 / 2) * p.1 ^ (-(1 / 2 : ℝ)) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2

/-- Formal `s`-derivative of `ageH S R f`. -/
def ageHDeriv (S R : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ :=
  p.1 ^ (-(3 / 2 : ℝ)) * (-(1 / 4) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2) +
  p.1 ^ (-(1 / 2 : ℝ)) * ((1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2 +
    thetaS S p.1 * chiR R p.2.2 * pdS f p * f p)

theorem hasDerivAt_ageH (S R : ℝ) {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f)
    {s : ℝ} (hs : 0 < s) (x : ℝ × ℝ) :
    HasDerivAt (fun s' => ageH S R f (s', x)) (ageHDeriv S R f (s, x)) s := by
  have hr : HasDerivAt (fun s' : ℝ => s' ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ))) s := by
    have h := Real.hasDerivAt_rpow_const (x := s) (p := -(1 / 2 : ℝ)) (Or.inl hs.ne')
    have he : -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) := by ring
    rw [he] at h
    exact h
  have hθ : HasDerivAt (thetaS S) (deriv (thetaS S) s) s :=
    ((contDiff_thetaS S).differentiable (by simp) s).hasDerivAt
  have hf' := hasDerivAt_slice_pdS hf s x
  have hfsq : HasDerivAt (fun s' => (f (s', x)) ^ 2)
      ((2 : ℕ) * f (s, x) ^ (2 - 1) * pdS f (s, x)) s := hf'.pow 2
  have hprod := (((hr.const_mul (1 / 2)).mul hθ).mul_const (chiR R x.2)).mul hfsq
  refine hprod.congr_deriv ?_
  unfold ageHDeriv
  simp only [Pi.mul_apply, Nat.cast_ofNat]
  ring

theorem ageIntegrand_eq_split (μ S R : ℝ) {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f)
    {p : Profile} (hp : 0 < p.1) :
    ageIntegrand μ S R f p =
      p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2) +
      p.1 ^ (-(1 / 2 : ℝ)) * (-(1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2) -
      ageHDeriv S R f p := by
  have hr : p.1 ^ (-(3 / 2 : ℝ)) * p.1 = p.1 ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add_one hp.ne']
    congr 1; ring
  unfold ageIntegrand ageHDeriv
  rw [pdS_fCut S R hf p]
  unfold fCut
  linear_combination -(hr * ((deriv (thetaS S) p.1 * f p + thetaS S p.1 * pdS f p) * chiR R p.2.2 * f p))

theorem pdS_zero_of_lt {s0 : ℝ} {f : Profile → ℝ} (hz : ∀ p : Profile, p.1 < s0 → f p = 0)
    {p : Profile} (hp : p.1 < s0) : pdS f p = 0 := by
  unfold pdS
  rw [fderiv_zero_of_lt hz hp]
  simp

theorem deriv_thetaS_eq_zero {S s : ℝ} (h : S + 1 < s) : deriv (thetaS S) s = 0 := by
  have hU : IsOpen {t : ℝ | S + 1 < t} := isOpen_lt continuous_const continuous_id
  have hev : thetaS S =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds h) fun t ht => thetaS_eq_zero ht.le
  rw [hev.deriv_eq, deriv_const]

theorem integral_ageHDeriv_slice_eq_zero {s0 S R : ℝ} (hs0 : 0 < s0) {f : Profile → ℝ}
    (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) (x : ℝ × ℝ) :
    ∫ s in Ioi (0 : ℝ), ageHDeriv S R f (s, x) = 0 := by
  set a : ℝ := s0 / 2
  set b : ℝ := max s0 (S + 1) + 1
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by
    have : a ≤ s0 := by unfold a; linarith
    have : s0 ≤ b := by unfold b; linarith [le_max_left s0 (S + 1)]
    linarith
  have hsub : Ioc a b ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le ha0 hs.1.le
  have hz_out : ∀ s : ℝ, s ∉ Ioc a b → ageHDeriv S R f (s, x) = 0 := by
    intro s hsab
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hsab
    unfold ageHDeriv
    rcases hsab with hle | hgt
    · have hslt : s < s0 := by unfold a at hle; linarith
      rw [hz (s, x) hslt, pdS_zero_of_lt hz hslt]
      ring
    · have hS1 : S + 1 < s := by
        have : S + 1 ≤ max s0 (S + 1) := le_max_right s0 (S + 1)
        unfold b at hgt; linarith
      rw [thetaS_eq_zero hS1.le, deriv_thetaS_eq_zero hS1]
      ring
  have hz_ioi : ∀ s : ℝ, s ∉ Ioi (0 : ℝ) → ageHDeriv S R f (s, x) = 0 :=
    fun s hs => hz_out s (fun h => hs (hsub h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz_ioi,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hz_out]
  rw [← intervalIntegral.integral_of_le hab]
  have hcont : Continuous (fun s => ageHDeriv S R f (s, x)) := by
    have h1 : Continuous (fun s : ℝ => ((s, x) : Profile)) :=
      continuous_id.prodMk continuous_const
    have hpd : Continuous (pdS f) :=
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hfc := hf.continuous
    have hthc : Continuous (fun p : Profile => thetaS S p.1) :=
      (contDiff_thetaS S).continuous.comp continuous_fst
    have hdthc : Continuous (fun p : Profile => deriv (thetaS S) p.1) :=
      ((contDiff_thetaS S).continuous_deriv (by simp)).comp continuous_fst
    have hchc : Continuous (fun p : Profile => chiR R p.2.2) :=
      (contDiff_chiR R).continuous.comp (continuous_snd.comp continuous_snd)
    have hG1 : Continuous (fun p : Profile => -(1 / 4) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2) :=
      ((continuous_const.mul hthc).mul hchc).mul (hfc.pow 2)
    have hG2 : Continuous (fun p : Profile =>
        (1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2 +
        thetaS S p.1 * chiR R p.2.2 * pdS f p * f p) :=
      (((continuous_const.mul hdthc).mul hchc).mul (hfc.pow 2)).add
        (((hthc.mul hchc).mul hpd).mul hfc)
    have hA1 := continuous_rpow_mul_of_zero_below hs0 (-(3 / 2 : ℝ)) hG1
      (fun p hp => by rw [hz p hp]; ring)
    have hA2 := continuous_rpow_mul_of_zero_below hs0 (-(1 / 2 : ℝ)) hG2
      (fun p hp => by rw [hz p hp, pdS_zero_of_lt hz hp]; ring)
    exact (hA1.add hA2).comp h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_ageH S R hf (lt_of_lt_of_le ha0 (by rw [uIcc_of_le hab] at hs; exact hs.1)) x)
    (hcont.intervalIntegrable a b)]
  have hba : ageH S R f (a, x) = 0 := by
    unfold ageH
    have : a < s0 := by unfold a; linarith
    rw [hz (a, x) this]
    ring
  have hbb : ageH S R f (b, x) = 0 := by
    unfold ageH
    have : S + 1 ≤ b := by
      have : S + 1 ≤ max s0 (S + 1) := le_max_right s0 (S + 1)
      unfold b; linarith
    rw [thetaS_eq_zero this]
    ring
  rw [hbb, hba, sub_self]

theorem integrableOn_agePiece1 {c s0 S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R) (a : ℝ)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    IntegrableOn (fun p : Chart =>
        p.1 ^ (-(3 / 2 : ℝ)) * (a * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hG : Continuous (fun p : Chart => a * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2) :=
    (((continuous_const.mul ((contDiff_thetaS S).continuous.comp continuous_fst)).mul
      ((contDiff_chiR R).continuous.comp (continuous_snd.comp continuous_snd))).mul
      (hf.continuous.pow 2))
  refine integrableOn_of_band (s0 := s0) (s1 := max s0 (S + 1)) (L := 2 * R)
    (continuous_rpow_mul_of_zero_below hs0 _ hG (fun p hp => by rw [hz p hp]; ring)) ?_
  intro p hp
  rcases hp with h | h | h
  · rw [hz p h]; ring
  · rw [thetaS_eq_zero (le_trans (le_max_right s0 (S + 1)) h.le)]; ring
  · rw [chiR_eq_zero hR h.le]; ring

theorem integrableOn_agePiece2 {c s0 S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    IntegrableOn (fun p : Chart =>
        p.1 ^ (-(1 / 2 : ℝ)) * (-(1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hG : Continuous (fun p : Chart =>
      -(1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2) :=
    (((continuous_const.mul (((contDiff_thetaS S).continuous_deriv (by simp)).comp continuous_fst)).mul
      ((contDiff_chiR R).continuous.comp (continuous_snd.comp continuous_snd))).mul
      (hf.continuous.pow 2))
  refine integrableOn_of_band (s0 := s0) (s1 := max s0 (S + 1)) (L := 2 * R)
    (continuous_rpow_mul_of_zero_below hs0 _ hG (fun p hp => by rw [hz p hp]; ring)) ?_
  intro p hp
  rcases hp with h | h | h
  · rw [hz p h]; ring
  · rw [deriv_thetaS_eq_zero (lt_of_le_of_lt (le_max_right s0 (S + 1)) h)]; ring
  · rw [chiR_eq_zero hR h.le]; ring

theorem integrableOn_ageHDeriv {c s0 S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    IntegrableOn (ageHDeriv S R f) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have h1 := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (-(1 / 4)) hf hz
  have hG2 : Continuous (fun p : Chart =>
      (1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2 +
      thetaS S p.1 * chiR R p.2.2 * pdS f p * f p) := by
    have hfc := hf.continuous
    have hthc : Continuous (fun p : Chart => thetaS S p.1) :=
      (contDiff_thetaS S).continuous.comp continuous_fst
    have hdthc : Continuous (fun p : Chart => deriv (thetaS S) p.1) :=
      ((contDiff_thetaS S).continuous_deriv (by simp)).comp continuous_fst
    have hchc : Continuous (fun p : Chart => chiR R p.2.2) :=
      (contDiff_chiR R).continuous.comp (continuous_snd.comp continuous_snd)
    have hpd : Continuous (pdS f) :=
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact (((continuous_const.mul hdthc).mul hchc).mul (hfc.pow 2)).add
      (((hthc.mul hchc).mul hpd).mul hfc)
  have h2 : IntegrableOn (fun p : Chart =>
      p.1 ^ (-(1 / 2 : ℝ)) * ((1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2 +
        thetaS S p.1 * chiR R p.2.2 * pdS f p * f p)) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
    refine integrableOn_of_band (s0 := s0) (s1 := max s0 (S + 1)) (L := 2 * R)
      (continuous_rpow_mul_of_zero_below hs0 _ hG2
        (fun p hp => by rw [hz p hp, pdS_zero_of_lt hz hp]; ring)) ?_
    intro p hp
    rcases hp with h | h | h
    · rw [hz p h, pdS_zero_of_lt hz h]; ring
    · have hS1 := lt_of_le_of_lt (le_max_right s0 (S + 1)) h
      rw [thetaS_eq_zero hS1.le, deriv_thetaS_eq_zero hS1]; ring
    · rw [chiR_eq_zero hR h.le]; ring
  exact Integrable.add h1 h2

theorem integrableOn_ageIntegrand {c s0 μ S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    IntegrableOn (ageIntegrand μ S R f) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hI : IntegrableOn (fun p : Chart =>
      p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2) +
      p.1 ^ (-(1 / 2 : ℝ)) * (-(1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2) -
      ageHDeriv S R f p) (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    ((integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) hf hz).add
      (integrableOn_agePiece2 (c := c) (S := S) hs0 hR hf hz)).sub
      (integrableOn_ageHDeriv (c := c) (S := S) hs0 hR hf hz)
  refine hI.congr_fun (fun p hp => ?_) (measurableSet_Ioi.prod (B0579.measurableSet_cell c))
  exact (ageIntegrand_eq_split μ S R hf hp.1).symm

/-- **Main age IBP inequality**: the `s`-integral of `ageIntegrand μ S R f` is bounded below by
`(μ + 1/4) ∫ s^{-3/2} θ_S(s) χ_R(η) f²`. -/
theorem integral_ageIntegrand_ge {c s0 μ S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2) ≤
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ageIntegrand μ S R f p := by
  have h1 := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) hf hz
  have h2 := integrableOn_agePiece2 (c := c) (S := S) hs0 hR hf hz
  have h12 : IntegrableOn (fun p : Chart =>
      p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2) +
      p.1 ^ (-(1 / 2 : ℝ)) * (-(1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := h1.add h2
  have h3 := integrableOn_ageHDeriv (c := c) (S := S) hs0 hR hf hz
  have hcongr : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ageIntegrand μ S R f p =
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        (p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2) +
         p.1 ^ (-(1 / 2 : ℝ)) * (-(1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2) -
         ageHDeriv S R f p) :=
    setIntegral_congr_fun (measurableSet_Ioi.prod (B0579.measurableSet_cell c))
      (fun p hp => ageIntegrand_eq_split μ S R hf hp.1)
  have h0 : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ageHDeriv S R f p = 0 := by
    have hprod : (volume : Measure Chart).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) =
        (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c)) := by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rw [IntegrableOn, hprod] at h3
    rw [hprod, integral_prod_symm _ h3]
    simp only [integral_ageHDeriv_slice_eq_zero hs0 hf hz, integral_zero]
  rw [hcongr, integral_sub h12 h3, integral_add h1 h2, h0, sub_zero]
  have hnonneg : 0 ≤ ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      p.1 ^ (-(1 / 2 : ℝ)) * (-(1 / 2) * deriv (thetaS S) p.1 * chiR R p.2.2 * (f p) ^ 2) := by
    refine setIntegral_nonneg (measurableSet_Ioi.prod (B0579.measurableSet_cell c)) fun p hp => ?_
    have hp0 : (0 : ℝ) < p.1 := hp.1
    have hr0 : 0 ≤ p.1 ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
    have hd0 : 0 ≤ -(1 / 2) * deriv (thetaS S) p.1 := by
      linarith [deriv_thetaS_nonpos S p.1]
    exact mul_nonneg hr0 (mul_nonneg (mul_nonneg hd0 (chiR_nonneg R p.2.2)) (sq_nonneg _))
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
