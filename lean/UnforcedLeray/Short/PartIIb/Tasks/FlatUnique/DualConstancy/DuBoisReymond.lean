import UnforcedLeray.Short.PartIIb.Sub.T11_2

/-!
# Part II-b, leaf `PartII-b:T11/2/3` (du Bois-Reymond lemma)

Pure real analysis: a locally integrable `F` on `(0, s)` with `∫ χ' F = 0` for all
`χ ∈ C_c^∞(0,s)` is a.e. constant on `(0,s)`.

Proof idea: fix a normalised bump `χ0` with `∫ χ0 = 1` supported in `(0,s)` and put
`κ = ∫ χ0 F`.  For a test `g` put `v = g - (∫ g) χ0`, which has mean zero.  Its primitive
`Φ(x) = ∫_0^x v` is smooth with compact support in `(0,s)` and `Φ' = v`, so the hypothesis
gives `∫ v F = 0`, i.e. `∫ g (F - κ) = 0`.  Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` finishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace DuBoisReymondHelp

lemma exists_bump (s : ℝ) (hs : 0 < s) :
    ∃ χ0 : ℝ → ℝ, ContDiff ℝ ∞ χ0 ∧ HasCompactSupport χ0 ∧
      tsupport χ0 ⊆ Ioo (0 : ℝ) s ∧ ∫ x, χ0 x = 1 := by
  let B : ContDiffBump (s / 2) :=
    { rIn := s / 8, rOut := s / 4, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  have hr : B.rOut = s / 4 := rfl
  refine ⟨B.normed volume, B.contDiff_normed, B.hasCompactSupport_normed, ?_, B.integral_normed⟩
  rw [B.tsupport_normed_eq (μ := volume), hr]
  intro t ht
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
  exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩

lemma exists_Ioo_contain (s : ℝ) (hs : 0 < s) (K : Set ℝ) (hK : IsCompact K)
    (hKU : K ⊆ Ioo (0 : ℝ) s) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < s ∧ K ⊆ Ioo a b := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨s / 4, s / 2, by linarith, by linarith, by linarith, by rw [h]; exact empty_subset _⟩
  · obtain ⟨m, hmK, hm⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M, hMK, hM⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
    have hm0 : 0 < m := (hKU hmK).1
    have hMs : M < s := (hKU hMK).2
    have hmM : m ≤ M := isMinOn_iff.mp hm M hMK
    refine ⟨m / 2, (M + s) / 2, by linarith, by linarith, by linarith, ?_⟩
    intro t ht
    have h1 : m ≤ t := isMinOn_iff.mp hm t ht
    have h2 : t ≤ M := isMaxOn_iff.mp hM t ht
    exact ⟨by linarith, by linarith⟩

lemma primitive_support (a b : ℝ) (ha : 0 < a) (hab : a < b) (v : ℝ → ℝ)
    (hv0 : ∀ t, t ∉ Ioo a b → v t = 0) (hint : ∫ t, v t = 0) :
    tsupport (fun x => ∫ t in (0 : ℝ)..x, v t) ⊆ Icc a b := by
  have hzero_left : ∀ x, x ≤ a → (∫ t in (0 : ℝ)..x, v t) = 0 := by
    intro x hx
    have h : ∫ t in (0 : ℝ)..x, v t = ∫ t in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      show v t = 0
      apply hv0 t
      intro hh
      rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith [hh.1]
    rw [h]
    simp
  have hzero_right : ∀ x, b ≤ x → (∫ t in (0 : ℝ)..x, v t) = 0 := by
    intro x hx
    have hcompl : ∀ t, t ∉ Ioc (0 : ℝ) x → v t = 0 := by
      intro t ht
      apply hv0 t
      intro hh
      rcases le_or_gt t 0 with h0 | h0
      · linarith [hh.1]
      · exact ht ⟨h0, by linarith [hh.2]⟩
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ x by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero (f := v) hcompl]
    exact hint
  have hsupp : Function.support (fun x => ∫ t in (0 : ℝ)..x, v t) ⊆ Icc a b := by
    intro x hx
    rcases lt_or_ge x a with h1 | h1
    · exact absurd (hzero_left x h1.le) (Function.mem_support.mp hx)
    · rcases lt_or_ge b x with h2 | h2
      · exact absurd (hzero_right x h2.le) (Function.mem_support.mp hx)
      · exact ⟨h1, h2⟩
  exact closure_minimal hsupp isClosed_Icc

end DuBoisReymondHelp

open DuBoisReymondHelp in
theorem duBoisReymond_proof : UnforcedLeray.Short.IIb.DuBoisReymond := by
  intro s F hs hF htest
  obtain ⟨χ0, hχc, hχs, hχU, hχint⟩ := exists_bump s hs
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = ∫ σ in Ioo (0 : ℝ) s, (χ0 σ : ℂ) * F σ := ⟨_, rfl⟩
  -- integrability of `φ F` on `(0,s)` for a continuous test `φ` supported in `(0,s)`
  have hloc : ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) s → IntegrableOn (fun σ => (φ σ : ℂ) * F σ) (Ioo (0 : ℝ) s) := by
    intro φ hφc hφs hφU
    have h1 : IntegrableOn F (tsupport φ) := hF.integrableOn_compact_subset hφU hφs.isCompact
    have hc : ContinuousOn (fun σ => (φ σ : ℂ)) (tsupport φ) :=
      (Complex.continuous_ofReal.comp hφc).continuousOn
    have h2 : IntegrableOn (fun σ => (φ σ : ℂ) * F σ) (tsupport φ) :=
      IntegrableOn.continuousOn_mul hc h1 hφs.isCompact
    refine IntegrableOn.of_forall_sdiff_eq_zero h2 measurableSet_Ioo ?_
    intro x hx
    have hφx : φ x = 0 := by
      by_contra hne
      exact hx.2 (subset_tsupport φ (Function.mem_support.mpr hne))
    simp [hφx]
  have hzeroOut : ∀ φ : ℝ → ℝ, tsupport φ ⊆ Ioo (0 : ℝ) s → ∀ x, x ∉ Ioo (0 : ℝ) s →
      φ x = 0 := by
    intro φ h x hx
    by_contra hne
    exact hx (h (subset_tsupport φ (Function.mem_support.mpr hne)))
  -- the key identity for each test function
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo (0 : ℝ) s → ∫ σ in Ioo (0 : ℝ) s, (g σ : ℂ) * (F σ - κ) = 0 := by
    intro g hg hgs hgU
    have hgc : Continuous g := hg.continuous
    obtain ⟨cg, hcg⟩ : ∃ c : ℝ, c = ∫ x, g x := ⟨_, rfl⟩
    have hχi : Integrable χ0 := hχc.continuous.integrable_of_hasCompactSupport hχs
    have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
    have hvc : ContDiff ℝ ∞ (fun x => g x - cg * χ0 x) :=
      hg.sub (contDiff_const.mul hχc)
    have hvsub : tsupport (fun x => g x - cg * χ0 x) ⊆ tsupport g ∪ tsupport χ0 := by
      refine closure_minimal ?_ ((isClosed_tsupport g).union (isClosed_tsupport χ0))
      intro x hx
      by_contra h
      have hg0 : g x = 0 := by
        by_contra hne
        exact h (Or.inl (subset_tsupport g (Function.mem_support.mpr hne)))
      have hχ0 : χ0 x = 0 := by
        by_contra hne
        exact h (Or.inr (subset_tsupport χ0 (Function.mem_support.mpr hne)))
      exact Function.mem_support.mp hx (by simp [hg0, hχ0])
    have hvU : tsupport (fun x => g x - cg * χ0 x) ⊆ Ioo (0 : ℝ) s :=
      hvsub.trans (union_subset hgU hχU)
    have hvK : IsCompact (tsupport (fun x => g x - cg * χ0 x)) :=
      (IsCompact.union hgs hχs).of_isClosed_subset (isClosed_tsupport _) hvsub
    obtain ⟨a, b, ha, hab, hbs, hKab⟩ := exists_Ioo_contain s hs _ hvK hvU
    have hv0 : ∀ t, t ∉ Ioo a b → (fun x => g x - cg * χ0 x) t = 0 := by
      intro t ht
      by_contra hne
      exact ht (hKab (subset_tsupport _ (Function.mem_support.mpr hne)))
    have hint : ∫ t, (g t - cg * χ0 t) = 0 := by
      rw [integral_sub hgi (Integrable.const_mul hχi cg), integral_const_mul, hχint, ← hcg,
        mul_one, sub_self]
    have hΦsupp := primitive_support a b ha hab _ hv0 hint
    have hdΦ : ∀ σ, deriv (fun u => ∫ t in (0 : ℝ)..u, (g t - cg * χ0 t)) σ
        = g σ - cg * χ0 σ :=
      fun σ => ((hvc.continuous.integral_hasStrictDerivAt 0 σ).hasDerivAt).deriv
    have hΦc : ContDiff ℝ ∞ (fun u => ∫ t in (0 : ℝ)..u, (g t - cg * χ0 t)) := by
      rw [contDiff_infty_iff_deriv]
      refine ⟨fun x => ((hvc.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt).differentiableAt,
        ?_⟩
      have hfun : deriv (fun u => ∫ t in (0 : ℝ)..u, (g t - cg * χ0 t))
          = fun σ => g σ - cg * χ0 σ := funext hdΦ
      rw [hfun]
      exact hvc
    have hΦcs : HasCompactSupport (fun u => ∫ t in (0 : ℝ)..u, (g t - cg * χ0 t)) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hΦsupp
    have hΦU : tsupport (fun u => ∫ t in (0 : ℝ)..u, (g t - cg * χ0 t)) ⊆ Ioo (0 : ℝ) s :=
      hΦsupp.trans (Icc_subset_Ioo ha hbs)
    have hφ := htest _ hΦc hΦcs hΦU
    simp only [hdΦ] at hφ
    have hI1 : IntegrableOn (fun σ => (g σ : ℂ) * F σ) (Ioo (0 : ℝ) s) :=
      hloc g hgc hgs hgU
    have hI2 : IntegrableOn (fun σ => (χ0 σ : ℂ) * F σ) (Ioo (0 : ℝ) s) :=
      hloc χ0 hχc.continuous hχs hχU
    have hgI : IntegrableOn (fun σ => (g σ : ℂ)) (Ioo (0 : ℝ) s) :=
      (hgi.ofReal).integrableOn
    have hz1 : ∀ x, x ∉ Ioo (0 : ℝ) s → (g x : ℂ) = 0 := fun x hx => by
      rw [hzeroOut g hgU x hx]
      simp
    have hgU_int : ∫ σ in Ioo (0 : ℝ) s, (g σ : ℂ) = (cg : ℂ) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun σ => (g σ : ℂ)) hz1]
      rw [integral_complex_ofReal, ← hcg]
    have hsplit : ∫ σ in Ioo (0 : ℝ) s, ((g σ - cg * χ0 σ : ℝ) : ℂ) * F σ
        = (∫ σ in Ioo (0 : ℝ) s, (g σ : ℂ) * F σ) - (cg : ℂ) * κ := by
      have hfun : (fun σ => ((g σ - cg * χ0 σ : ℝ) : ℂ) * F σ)
          = fun σ => (g σ : ℂ) * F σ - (cg : ℂ) * ((χ0 σ : ℂ) * F σ) := by
        funext σ
        push_cast
        ring
      rw [hfun, integral_sub hI1 (Integrable.const_mul hI2 (cg : ℂ)), integral_const_mul, ← hκ]
        <;> rfl
    have hgκ : ∫ σ in Ioo (0 : ℝ) s, (g σ : ℂ) * (F σ - κ)
        = (∫ σ in Ioo (0 : ℝ) s, (g σ : ℂ) * F σ) - (cg : ℂ) * κ := by
      have hfun : (fun σ => (g σ : ℂ) * (F σ - κ))
          = fun σ => (g σ : ℂ) * F σ - (g σ : ℂ) * κ := by
        funext σ
        ring
      rw [hfun, integral_sub hI1 (Integrable.mul_const hgI κ), integral_mul_const, hgU_int]
        <;> rfl
    rw [hgκ]
    rw [hsplit] at hφ
    exact hφ
  -- conclude from Mathlib's du Bois-Reymond lemma
  have hfloc : LocallyIntegrableOn (fun x => F x - κ) (Ioo (0 : ℝ) s) volume :=
    hF.sub (locallyIntegrableOn_const κ)
  have hD : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo (0 : ℝ) s → ∫ x, g x • (F x - κ) = 0 := by
    intro g hg hgs hgU
    have hz : ∀ x, x ∉ Ioo (0 : ℝ) s → g x • (F x - κ) = 0 := fun x hx => by
      rw [hzeroOut g hgU x hx, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun x => g x • (F x - κ)) hz]
    simp only [Complex.real_smul]
    exact key g hg hgs hgU
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfloc hD
  refine ⟨κ, (ae_restrict_iff' measurableSet_Ioo).mpr ?_⟩
  filter_upwards [hae] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

#print axioms duBoisReymond_proof
