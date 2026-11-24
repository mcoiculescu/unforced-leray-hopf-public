import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced

/-!
# `WindowCutoffExists` (source 1695-1702, 3962-3967)

Product cutoffs `χ(s,q,η) = A(s) B(η)` built from `Real.smoothTransition`, independent of `q`
(so `q`-periodic), with `C⁸` norm bounded by a fixed power of `σ⁻¹ + H + L + 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

namespace WindowCutoff

open Real

/-- Iterated derivatives of order `≥ 1` of `smoothTransition` vanish outside `[0,1]`. -/
lemma iterDeriv_zero_outside (k : ℕ) (hk : k ≠ 0) (x : ℝ) (hx : x ∉ Icc (0 : ℝ) 1) :
    iteratedDeriv k smoothTransition x = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · have : smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.iteratedDeriv_eq k, iteratedDeriv_const]; simp [hk]
  · have : smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      exact smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.iteratedDeriv_eq k, iteratedDeriv_const]; simp [hk]

lemma iterDeriv_bdd (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedDeriv k smoothTransition x‖ ≤ M := by
  have hc : Continuous (iteratedDeriv k smoothTransition) :=
    (smoothTransition.contDiff (n := ⊤)).continuous_iteratedDeriv k (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := iteratedDeriv k smoothTransition)
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact le_trans (hM x hx) (le_max_left _ _)
  · by_cases hk : k = 0
    · subst hk
      simp only [iteratedDeriv_zero, Real.norm_eq_abs]
      rw [abs_of_nonneg (smoothTransition.nonneg x)]
      exact le_trans (smoothTransition.le_one x) (le_max_right _ _)
    · rw [iterDeriv_zero_outside k hk x hx]; simp

/-- A uniform constant `C0 ≥ 1` bounding the first eight iterated derivatives. -/
lemma iterDeriv_bdd8 : ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ k, k ≤ 8 → ∀ x,
    ‖iteratedDeriv k smoothTransition x‖ ≤ C0 := by
  choose M hM0 hM using iterDeriv_bdd
  refine ⟨1 + ∑ k ∈ Finset.range 9, M k, ?_, fun k hk x => ?_⟩
  · have : 0 ≤ ∑ k ∈ Finset.range 9, M k := Finset.sum_nonneg fun k _ => hM0 k
    linarith
  · have h1 : M k ≤ ∑ j ∈ Finset.range 9, M j :=
      Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_range.2 (by omega))
    linarith [hM k x]

/-- The class of functions on the profile space with `C⁸` bounds `D N^k`. -/
def Good (N D : ℝ) (F : Profile → ℝ) : Prop :=
  ContDiff ℝ ∞ F ∧ ∀ k, k ≤ 8 → ∀ p, ‖iteratedFDeriv ℝ k F p‖ ≤ D * N ^ k

lemma good_factor (C0 : ℝ) (hC0 : ∀ k, k ≤ 8 → ∀ x, ‖iteratedDeriv k smoothTransition x‖ ≤ C0)
    (ℓ : Profile →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (a b N : ℝ) (hN : |a| ≤ N) :
    Good N C0 (fun p => smoothTransition (a * ℓ p + b)) := by
  set φ : ℝ → ℝ := fun x => smoothTransition (a * x + b) with hφ
  have hφs : ContDiff ℝ ∞ φ :=
    (smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hF : (fun p => smoothTransition (a * ℓ p + b)) = φ ∘ ℓ := rfl
  rw [hF]
  refine ⟨hφs.comp ℓ.contDiff, fun k hk p => ?_⟩
  rw [ℓ.iteratedFDeriv_comp_right hφs (x := p) (i := k) (by exact_mod_cast le_top)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hprod : ∏ _i : Fin k, ‖ℓ‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hℓ)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hd : iteratedDeriv k φ (ℓ p) = a ^ k * iteratedDeriv k smoothTransition (a * ℓ p + b) := by
    have h1 : φ = fun x => (fun y => smoothTransition (y + b)) (a * x) := rfl
    have hg : ContDiff ℝ ∞ (fun y : ℝ => smoothTransition (y + b)) :=
      (smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.add contDiff_const)
    have hg' : ContDiff ℝ (k : ℕ) (fun y : ℝ => smoothTransition (y + b)) :=
      hg.of_le (by exact_mod_cast le_top)
    rw [h1, iteratedDeriv_comp_const_mul hg', iteratedDeriv_comp_add_const]
  have hb : ‖iteratedDeriv k φ (ℓ p)‖ ≤ C0 * N ^ k := by
    rw [hd, norm_mul, norm_pow, Real.norm_eq_abs]
    calc |a| ^ k * ‖iteratedDeriv k smoothTransition (a * ℓ p + b)‖ ≤ N ^ k * C0 :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hN k) (hC0 k hk _) (norm_nonneg _)
            (le_trans (abs_nonneg _) hN |> fun h => pow_nonneg h k)
      _ = C0 * N ^ k := mul_comm _ _
  exact le_trans (mul_le_of_le_one_right (norm_nonneg _) hprod) hb

lemma good_mul {N D1 D2 : ℝ} (hN : 0 ≤ N) {F G : Profile → ℝ} (hF : Good N D1 F)
    (hG : Good N D2 G) : Good N (2 ^ 8 * D1 * D2) (fun p => F p * G p) := by
  have hD1 : 0 ≤ D1 := by
    have := hF.2 0 (by omega) 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  have hD2 : 0 ≤ D2 := by
    have := hG.2 0 (by omega) 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨hF.1.mul hG.1, fun k hk p => ?_⟩
  refine le_trans (norm_iteratedFDeriv_mul_le hF.1 hG.1 p (n := k) (by exact_mod_cast le_top)) ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i F p‖ * ‖iteratedFDeriv ℝ (k - i) G p‖ ≤
        (k.choose i : ℝ) * (D1 * D2 * N ^ k) := by
    intro i hi
    have hi' : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
    have h1 := hF.2 i (by omega) p
    have h2 := hG.2 (k - i) (by omega) p
    have hpow : N ^ i * N ^ (k - i) = N ^ k := by rw [← pow_add]; congr 1; omega
    calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i F p‖ * ‖iteratedFDeriv ℝ (k - i) G p‖
        = (k.choose i : ℝ) * (‖iteratedFDeriv ℝ i F p‖ * ‖iteratedFDeriv ℝ (k - i) G p‖) := by ring
      _ ≤ (k.choose i : ℝ) * ((D1 * N ^ i) * (D2 * N ^ (k - i))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg hD1 (pow_nonneg hN _))) (Nat.cast_nonneg _)
      _ = (k.choose i : ℝ) * (D1 * D2 * N ^ k) := by rw [← hpow]; ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have hs : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hs]
  have hnn : 0 ≤ D1 * D2 * N ^ k := mul_nonneg (mul_nonneg hD1 hD2) (pow_nonneg hN _)
  calc (2 : ℝ) ^ k * (D1 * D2 * N ^ k) ≤ 2 ^ 8 * (D1 * D2 * N ^ k) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hnn
    _ = 2 ^ 8 * D1 * D2 * N ^ k := by ring

lemma cNorm8_le {N D : ℝ} (hN : 1 ≤ N) {F : Profile → ℝ} (hF : Good N D F) :
    UnforcedLeray.Short.PartIIa.cNorm8 F ≤ 9 * D * N ^ 8 := by
  have hD : 0 ≤ D := by
    have := hF.2 0 (by omega) 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  unfold UnforcedLeray.Short.PartIIa.cNorm8
  have : ∀ k ∈ Finset.range 9, (⨆ p, ‖iteratedFDeriv ℝ k F p‖) ≤ D * N ^ 8 := by
    intro k hk
    have hk' : k ≤ 8 := by simpa [Nat.lt_succ_iff] using hk
    refine ciSup_le fun p => le_trans (hF.2 k hk' p) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN hk') hD
  refine le_trans (Finset.sum_le_sum this) ?_
  simp [Finset.sum_const]
  nlinarith [mul_nonneg hD (pow_nonneg (le_trans zero_le_one hN) 8)]

/-- The coordinate projections. -/
def ℓs : Profile →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
def ℓη : Profile →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

lemma ℓs_apply (p : Profile) : ℓs p = p.1 := rfl
lemma ℓη_apply (p : Profile) : ℓη p = p.2.2 := rfl
lemma ℓs_norm : ‖ℓs‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)
lemma ℓη_norm : ‖ℓη‖ ≤ 1 :=
  le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
    (by
      have h1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
      have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
      nlinarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ ℝ),
        norm_nonneg (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))])

/-- The window cutoff with parameters `(m1, m2, e)`:
`φ(m1 s/σ - 1) φ(2 - m2 s/H) φ(e - η) φ(e + η)`. -/
def W (σ H m1 m2 e : ℝ) (p : Profile) : ℝ :=
  smoothTransition (m1 * σ⁻¹ * ℓs p + (-1)) * smoothTransition ((-(m2 * H⁻¹)) * ℓs p + 2) *
    smoothTransition ((-1) * ℓη p + e) * smoothTransition (1 * ℓη p + e)

lemma W_good (C0 : ℝ) (hC0 : ∀ k, k ≤ 8 → ∀ x, ‖iteratedDeriv k smoothTransition x‖ ≤ C0)
    (σ H m1 m2 e N : ℝ) (h1 : |m1 * σ⁻¹| ≤ N) (h2 : |-(m2 * H⁻¹)| ≤ N) (h3 : 1 ≤ N) :
    Good N (2 ^ 8 * (2 ^ 8 * (2 ^ 8 * C0 * C0) * C0) * C0) (W σ H m1 m2 e) := by
  have hN : 0 ≤ N := le_trans zero_le_one h3
  have f1 := good_factor C0 hC0 ℓs ℓs_norm (m1 * σ⁻¹) (-1) N h1
  have f2 := good_factor C0 hC0 ℓs ℓs_norm (-(m2 * H⁻¹)) 2 N h2
  have f3 := good_factor C0 hC0 ℓη ℓη_norm (-1) e N (by simpa using h3)
  have f4 := good_factor C0 hC0 ℓη ℓη_norm 1 e N (by simpa using h3)
  exact good_mul hN (good_mul hN (good_mul hN f1 f2) f3) f4

lemma W_ne_zero {σ H m1 m2 e : ℝ} (hσ : 0 < σ) (hH : 0 < H) (hm1 : 0 < m1) (hm2 : 0 < m2)
    {p : Profile} (hp : W σ H m1 m2 e p ≠ 0) :
    σ / m1 < p.1 ∧ p.1 < 2 * H / m2 ∧ |p.2.2| < e := by
  unfold W at hp
  simp only [ne_eq, mul_eq_zero, not_or, smoothTransition.zero_iff_nonpos, not_le] at hp
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hp
  rw [ℓs_apply] at a b
  rw [ℓη_apply] at c d
  refine ⟨?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hm1]
    have : m1 * σ⁻¹ * p.1 + -1 = σ⁻¹ * (m1 * p.1 - σ) := by field_simp; ring
    rw [this] at a
    have := (mul_pos_iff_of_pos_left (inv_pos.2 hσ)).1 a
    linarith
  · rw [lt_div_iff₀ hm2]
    have : -(m2 * H⁻¹) * p.1 + 2 = H⁻¹ * (2 * H - m2 * p.1) := by field_simp; ring
    rw [this] at b
    have := (mul_pos_iff_of_pos_left (inv_pos.2 hH)).1 b
    linarith
  · rw [abs_lt]; constructor <;> linarith

lemma W_eq_one {σ H m1 m2 e : ℝ} (hσ : 0 < σ) (hH : 0 < H) (hm1 : 0 < m1) (hm2 : 0 < m2)
    {p : Profile} (h1 : 2 * σ / m1 ≤ p.1) (h2 : p.1 ≤ H / m2) (h3 : |p.2.2| ≤ e - 1) :
    W σ H m1 m2 e p = 1 := by
  unfold W
  rw [ℓs_apply, ℓη_apply]
  rw [abs_le] at h3
  have a : 1 ≤ m1 * σ⁻¹ * p.1 + -1 := by
    rw [div_le_iff₀ hm1] at h1
    have : m1 * σ⁻¹ * p.1 + -1 - 1 = σ⁻¹ * (m1 * p.1 - 2 * σ) := by field_simp; ring
    have h0 : 0 ≤ σ⁻¹ * (m1 * p.1 - 2 * σ) :=
      mul_nonneg (inv_pos.2 hσ).le (by linarith)
    linarith
  have b : 1 ≤ -(m2 * H⁻¹) * p.1 + 2 := by
    rw [le_div_iff₀ hm2] at h2
    have : -(m2 * H⁻¹) * p.1 + 2 - 1 = H⁻¹ * (H - m2 * p.1) := by field_simp; ring
    have h0 : 0 ≤ H⁻¹ * (H - m2 * p.1) :=
      mul_nonneg (inv_pos.2 hH).le (by linarith)
    linarith
  rw [smoothTransition.one_of_one_le a, smoothTransition.one_of_one_le b,
    smoothTransition.one_of_one_le (by linarith), smoothTransition.one_of_one_le (by linarith)]
  norm_num

lemma W_abs_le_one (σ H m1 m2 e : ℝ) (p : Profile) : |W σ H m1 m2 e p| ≤ 1 := by
  unfold W
  rw [abs_of_nonneg (by
    have := smoothTransition.nonneg (m1 * σ⁻¹ * ℓs p + (-1))
    have := smoothTransition.nonneg ((-(m2 * H⁻¹)) * ℓs p + 2)
    have := smoothTransition.nonneg ((-1) * ℓη p + e)
    have := smoothTransition.nonneg (1 * ℓη p + e)
    positivity)]
  have := smoothTransition.le_one (m1 * σ⁻¹ * ℓs p + (-1))
  have := smoothTransition.le_one ((-(m2 * H⁻¹)) * ℓs p + 2)
  have := smoothTransition.le_one ((-1) * ℓη p + e)
  have := smoothTransition.le_one (1 * ℓη p + e)
  have := smoothTransition.nonneg (m1 * σ⁻¹ * ℓs p + (-1))
  have := smoothTransition.nonneg ((-(m2 * H⁻¹)) * ℓs p + 2)
  have := smoothTransition.nonneg ((-1) * ℓη p + e)
  have := smoothTransition.nonneg (1 * ℓη p + e)
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (by assumption) (by assumption) (by assumption))
    (by assumption) (by assumption)) (by assumption) (by assumption)

lemma W_periodic (c σ H m1 m2 e : ℝ) : UnforcedLeray.B0220.QPeriodic c (W σ H m1 m2 e) := by
  intro p; rfl

lemma W_smooth (σ H m1 m2 e : ℝ) : ContDiff ℝ ∞ (W σ H m1 m2 e) := by
  obtain ⟨C0, -, hC0⟩ := iterDeriv_bdd8
  exact (W_good C0 hC0 σ H m1 m2 e (max 1 (max |m1 * σ⁻¹| |-(m2 * H⁻¹)|))
    (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) le_rfl)) (le_max_left _ _)).1

end WindowCutoff

open WindowCutoff in
theorem windowCutoffExists : WindowCutoffExists := by
  obtain ⟨C0, hC01, hC0⟩ := iterDeriv_bdd8
  set D : ℝ := 2 ^ 8 * (2 ^ 8 * (2 ^ 8 * C0 * C0) * C0) * C0 with hD
  refine ⟨18 * D * 8 ^ 8, 8, fun c σ H L hc hσ hσH hL => ?_⟩
  have hH : 0 < H := lt_of_lt_of_le hσ hσH
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hHi : H⁻¹ ≤ σ⁻¹ := inv_anti₀ hσ hσH
  have hHi0 : 0 < H⁻¹ := inv_pos.2 hH
  set X : ℝ := σ⁻¹ + H + L + 2 with hX
  have hX2 : 2 ≤ X := by linarith
  set N : ℝ := 8 * X with hNdef
  have hN1 : 1 ≤ N := by linarith
  have hg1 : Good N D (W σ H 2 1 (L + 1)) :=
    W_good C0 hC0 σ H 2 1 (L + 1) N
      (by rw [abs_of_nonneg (by positivity)]; linarith)
      (by rw [abs_neg, abs_of_nonneg (by positivity)]; linarith) hN1
  have hg2 : Good N D (W σ H 8 (1 / 4) (L + 3)) :=
    W_good C0 hC0 σ H 8 (1 / 4) (L + 3) N
      (by rw [abs_of_nonneg (by positivity)]; linarith)
      (by rw [abs_neg, abs_of_nonneg (by positivity)]; linarith) hN1
  refine ⟨W σ H 2 1 (L + 1), W σ H 8 (1 / 4) (L + 3), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨W_smooth _ _ _ _ _, W_periodic _ _ _ _ _ _, fun p hp => ?_⟩
    obtain ⟨h1, h2, h3⟩ := W_ne_zero hσ hH (by norm_num) (by norm_num) hp
    refine ⟨by linarith, by linarith, by linarith⟩
  · refine ⟨W_smooth _ _ _ _ _, W_periodic _ _ _ _ _ _, ⟨σ / 8, 8 * H, L + 3, by positivity, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := W_ne_zero hσ hH (by norm_num) (by norm_num) hp
      refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · refine ⟨{p : Profile | σ / 4 < p.1 ∧ p.1 < 4 * H ∧ |p.2.2| < L + 2}, ?_, ?_, ?_⟩
      · exact (isOpen_lt continuous_const continuous_fst).inter
          ((isOpen_lt continuous_fst continuous_const).inter
            (isOpen_lt (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const))
      · have hcl : IsClosed {p : Profile | σ / 2 ≤ p.1 ∧ p.1 ≤ 2 * H ∧ |p.2.2| ≤ L + 1} :=
          (isClosed_le continuous_const continuous_fst).inter
            ((isClosed_le continuous_fst continuous_const).inter
              (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd))
                continuous_const))
        have hsub : Function.support (W σ H 2 1 (L + 1)) ⊆
            {p : Profile | σ / 2 ≤ p.1 ∧ p.1 ≤ 2 * H ∧ |p.2.2| ≤ L + 1} := by
          intro p hp
          obtain ⟨h1, h2, h3⟩ := W_ne_zero hσ hH (by norm_num) (by norm_num) hp
          exact ⟨by linarith, by linarith, by linarith⟩
        refine le_trans (closure_minimal hsub hcl) ?_
        intro p hp
        exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩
      · intro p hp
        exact W_eq_one hσ hH (by norm_num) (by norm_num) (by linarith [hp.1])
          (by linarith [hp.2.1]) (by have := hp.2.2.le; linarith)
  · exact (W_smooth _ _ _ _ _).continuous.measurable
  · exact fun p => W_abs_le_one _ _ _ _ _ p
  · intro p h1 h2 h3
    exact W_eq_one hσ hH (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  · have e1 := cNorm8_le hN1 hg1
    have e2 := cNorm8_le hN1 hg2
    have hDn : 0 ≤ D := by
      have := hg1.2 0 (by omega) 0
      simp only [pow_zero, mul_one] at this
      exact le_trans (norm_nonneg _) this
    have : N ^ 8 = 8 ^ 8 * X ^ 8 := by rw [hNdef, mul_pow]
    rw [this] at e1 e2
    linarith

end UnforcedLeray.Short.PartIIIb.NearInst.Body
