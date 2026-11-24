import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BrkDerivSClosed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BkMajSummable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt

/-!
# `PartIII-b:C/asrc/ra/8/1/8` : tsum leaf (T3) `HpASumS`

Source of record: `the November 2 reference manuscript` (73 pages), 4978 and
4741-4745 (`A^y = χ_f A` is `C¹` on `(0,∞)`).

Termwise `s`-differentiation of `h^p_A = Σ_j b_j`. For `τ ∈ (s/2, 2s)` the summand derivative
`∂_τ b_j` is given by `brkDerivSClosed`, and it is bounded by `C · bkMaj ν (ageA ν (2s)) j x`
(the age is at most `ageA ν (2s)` on this window, and `Ay`, `deriv Ay` are bounded on `[s/2, 2s]`).
`hasDerivAt_tsum_of_isPreconnected` on `Ioo (s/2) (2s)` then gives the termwise derivative.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The entry sum of a `3 × 3` matrix. -/
def bkT3_Kc (M : Mat3) : ℝ := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|

/-- The `s`-derivative profile of the bracket summand (`brkDerivSClosed`). -/
def bkT3_dg (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (τ : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  bkG (ageA ν τ) (xj ν j x) •
    (bkP (deriv (Ay ν χ A) τ) (ageA ν τ) (xj ν j x) +
      ν • bkPa (Ay ν χ A τ) (ageA ν τ) (xj ν j x))

lemma bkT3_entry_le (M : Mat3) (i j : Fin 3) : |M i j| ≤ ‖M‖ := by
  have h1 := norm_le_pi_norm M i
  have h2 := norm_le_pi_norm (M i) j
  rw [Real.norm_eq_abs] at h2
  exact h2.trans h1

lemma bkT3_Kc_le (M : Mat3) (K : ℝ) (hK : ∀ i j, |M i j| ≤ K) : bkT3_Kc M ≤ 4 * K := by
  unfold bkT3_Kc
  linarith [hK 0 0, hK 0 2, hK 2 0, hK 2 2]

lemma bkT3_Kc_nonneg (M : Mat3) : 0 ≤ bkT3_Kc M := by
  unfold bkT3_Kc
  positivity

lemma bkT3_dot_le (u w : ℝ × ℝ) : |bkDot u w| ≤ 2 * ‖u‖ * ‖w‖ := by
  have h1 : |u.1| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le u
  have h2 : |u.2| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le u
  have h3 : |w.1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le w
  have h4 : |w.2| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le w
  unfold bkDot
  have e1 : |u.1 * w.1| ≤ ‖u‖ * ‖w‖ := by
    rw [abs_mul]; exact mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _)
  have e2 : |u.2 * w.2| ≤ ‖u‖ * ‖w‖ := by
    rw [abs_mul]; exact mul_le_mul h2 h4 (abs_nonneg _) (norm_nonneg _)
  calc |u.1 * w.1 + u.2 * w.2| ≤ |u.1 * w.1| + |u.2 * w.2| := abs_add_le _ _
    _ ≤ 2 * ‖u‖ * ‖w‖ := by nlinarith [e1, e2]

lemma bkT3_bkP_norm (M : Mat3) (a : ℝ) (ha : 1 ≤ a) (y : ℝ × ℝ) :
    ‖bkP M a y‖ ≤ 4 * bkT3_Kc M * (1 + ‖y‖) ^ 3 := by
  have ha0 : 0 < a := by linarith
  have hKc : 0 ≤ bkT3_Kc M := bkT3_Kc_nonneg M
  have hMy : ‖merApply M y‖ ≤ bkT3_Kc M * ‖y‖ := gp_merApply_norm_le M y
  have hJ : ‖merApply M (Jrot y)‖ ≤ bkT3_Kc M * ‖y‖ := by
    have h := gp_merApply_norm_le M (Jrot y)
    rw [gp_jrot_norm] at h
    exact h
  have hB : ‖Jrot (merApply M y)‖ ≤ bkT3_Kc M * ‖y‖ := by
    rw [gp_jrot_norm]
    exact hMy
  have hdot : |bkDot y (merApply M y)| ≤ 2 * ‖y‖ * (bkT3_Kc M * ‖y‖) := by
    have h := bkT3_dot_le y (merApply M y)
    have h2 : 2 * ‖y‖ * ‖merApply M y‖ ≤ 2 * ‖y‖ * (bkT3_Kc M * ‖y‖) :=
      mul_le_mul_of_nonneg_left hMy (by positivity)
    linarith
  have hterm : ‖(bkDot y (merApply M y) / (2 * a)) • Jrot y‖ ≤ bkT3_Kc M * ‖y‖ ^ 3 := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * a)]
    have h1 : |bkDot y (merApply M y)| / (2 * a) ≤ |bkDot y (merApply M y)| / 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by linarith)
    have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
    have h3 := mul_le_mul_of_nonneg_right hdot (norm_nonneg y)
    nlinarith [h2, h3]
  have hPsi : ‖bkP M a y‖ ≤
      ‖merApply M (Jrot y)‖ + ‖Jrot (merApply M y)‖ +
        ‖(bkDot y (merApply M y) / (2 * a)) • Jrot y‖ := by
    unfold bkP
    exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have ht1 : ‖y‖ ≤ (1 + ‖y‖) ^ 3 := by
    nlinarith [norm_nonneg y, sq_nonneg ‖y‖, pow_nonneg (norm_nonneg y) 3]
  have ht2 : ‖y‖ ^ 3 ≤ (1 + ‖y‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg y) (by linarith) 3
  have k1 := mul_le_mul_of_nonneg_left ht1 hKc
  have k2 := mul_le_mul_of_nonneg_left ht2 hKc
  have k4 : 0 ≤ bkT3_Kc M * (1 + ‖y‖) ^ 3 := mul_nonneg hKc (by positivity)
  linarith [hPsi, hJ, hB, hterm, k1, k2, k4]

lemma bkT3_bkPa_norm (M : Mat3) (a : ℝ) (ha : 1 ≤ a) (y : ℝ × ℝ) :
    ‖bkPa M a y‖ ≤ 9 * bkT3_Kc M * (1 + ‖y‖) ^ 5 := by
  have ha0 : 0 < a := by linarith
  have hKc : 0 ≤ bkT3_Kc M := bkT3_Kc_nonneg M
  have hMy : ‖merApply M y‖ ≤ bkT3_Kc M * ‖y‖ := gp_merApply_norm_le M y
  have hsq0 : 0 ≤ sq2 y := by unfold sq2; positivity
  have hy1 : y.1 ^ 2 ≤ ‖y‖ ^ 2 := by
    have h := norm_fst_le y
    rw [Real.norm_eq_abs] at h
    have := pow_le_pow_left₀ (abs_nonneg y.1) h 2
    rwa [sq_abs] at this
  have hy2 : y.2 ^ 2 ≤ ‖y‖ ^ 2 := by
    have h := norm_snd_le y
    rw [Real.norm_eq_abs] at h
    have := pow_le_pow_left₀ (abs_nonneg y.2) h 2
    rwa [sq_abs] at this
  have hsq2 : sq2 y ≤ 2 * ‖y‖ ^ 2 := by unfold sq2; linarith
  have hpoly1 : 1 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
  have hpoly2 : ‖y‖ ^ 2 ≤ 2 * (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
  have hc1 : |(-2 / a + sq2 y / (4 * a ^ 2))| ≤ 2 * (1 + ‖y‖) ^ 2 := by
    have hq0 : 0 ≤ sq2 y / (4 * a ^ 2) := div_nonneg hsq0 (by positivity)
    have hq1 : sq2 y / (4 * a ^ 2) ≤ sq2 y / 4 :=
      div_le_div_of_nonneg_left hsq0 (by norm_num) (by nlinarith)
    have hn1 : 2 / a ≤ 2 := by rw [div_le_iff₀ ha0]; linarith
    have hn0 : 0 ≤ 2 / a := by positivity
    have hnn : -2 / a = -(2 / a) := by ring
    rw [abs_le]
    constructor
    · rw [hnn]; linarith
    · rw [hnn]; linarith
  have hc2 : |bkDot y (merApply M y) / (2 * a ^ 2)| ≤ bkT3_Kc M * ‖y‖ ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * a ^ 2)]
    have h1 : |bkDot y (merApply M y)| / (2 * a ^ 2) ≤ |bkDot y (merApply M y)| / 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by nlinarith)
    have h2 := bkT3_dot_le y (merApply M y)
    have h3 : 2 * ‖y‖ * ‖merApply M y‖ ≤ 2 * ‖y‖ * (bkT3_Kc M * ‖y‖) :=
      mul_le_mul_of_nonneg_left hMy (by positivity)
    nlinarith [h1, h2, h3]
  have hP := bkT3_bkP_norm M a ha y
  have hdec : ‖bkPa M a y‖ ≤
      |(-2 / a + sq2 y / (4 * a ^ 2))| * ‖bkP M a y‖ +
        |bkDot y (merApply M y) / (2 * a ^ 2)| * ‖y‖ := by
    unfold bkPa
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, gp_jrot_norm]
  have k1 := mul_le_mul hc1 hP (norm_nonneg _) (by positivity)
  have k2 := mul_le_mul_of_nonneg_right hc2 (norm_nonneg y)
  have hu : ‖y‖ ^ 3 ≤ (1 + ‖y‖) ^ 5 := by
    nlinarith [norm_nonneg y, pow_nonneg (norm_nonneg y) 2, pow_nonneg (norm_nonneg y) 4,
      pow_nonneg (norm_nonneg y) 5]
  have k3 := mul_le_mul_of_nonneg_left hu hKc
  nlinarith [hdec, k1, k2, k3]

lemma bkT3_G_le (a A2 : ℝ) (ha : 1 ≤ a) (haA : a ≤ A2) (y : ℝ × ℝ) :
    0 ≤ bkG a y ∧ bkG a y ≤ Real.exp (-(sq2 y) / (4 * A2)) := by
  have ha0 : 0 < a := by linarith
  have hsq0 : 0 ≤ sq2 y := by unfold sq2; positivity
  have hc : (a ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hq : sq2 y / (4 * A2) ≤ sq2 y / (4 * a) :=
    div_le_div_of_nonneg_left hsq0 (by linarith) (by linarith)
  have e1 : -(sq2 y) / (4 * a) = -(sq2 y / (4 * a)) := by ring
  have e2 : -(sq2 y) / (4 * A2) = -(sq2 y / (4 * A2)) := by ring
  have hexp : -(sq2 y) / (4 * a) ≤ -(sq2 y) / (4 * A2) := by
    rw [e1, e2]; linarith
  constructor
  · unfold bkG; positivity
  · unfold bkG
    calc (a ^ 2)⁻¹ * Real.exp (-(sq2 y) / (4 * a))
        ≤ 1 * Real.exp (-(sq2 y) / (4 * a)) := by gcongr
      _ = Real.exp (-(sq2 y) / (4 * a)) := one_mul _
      _ ≤ Real.exp (-(sq2 y) / (4 * A2)) := Real.exp_le_exp.mpr hexp

lemma bkT3_dg_norm (M M' : Mat3) (K1 K2 ν a A2 : ℝ) (hν : 0 ≤ ν)
    (hK1 : ∀ i j, |M i j| ≤ K1) (hK2 : ∀ i j, |M' i j| ≤ K2) (hK1nn : 0 ≤ K1) (hK2nn : 0 ≤ K2)
    (ha : 1 ≤ a) (haA : a ≤ A2) (y : ℝ × ℝ) :
    ‖bkG a y • (bkP M' a y + ν • bkPa M a y)‖ ≤
      (16 * K2 + 36 * ν * K1) * ((1 + ‖y‖) ^ 6 * Real.exp (-(sq2 y) / (4 * A2))) := by
  obtain ⟨hG0, hGle⟩ := bkT3_G_le a A2 ha haA y
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hG0]
  have hP : ‖bkP M' a y‖ ≤ 16 * K2 * (1 + ‖y‖) ^ 3 := by
    have h := bkT3_bkP_norm M' a ha y
    have hK := bkT3_Kc_le M' K2 hK2
    have h4 : 4 * bkT3_Kc M' * (1 + ‖y‖) ^ 3 ≤ 16 * K2 * (1 + ‖y‖) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith
  have hPa : ‖ν • bkPa M a y‖ ≤ 36 * ν * K1 * (1 + ‖y‖) ^ 5 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hν]
    have h := bkT3_bkPa_norm M a ha y
    have hK := bkT3_Kc_le M K1 hK1
    have h' := mul_le_mul_of_nonneg_left h hν
    have h4 : ν * (9 * bkT3_Kc M * (1 + ‖y‖) ^ 5) ≤ ν * (9 * (4 * K1) * (1 + ‖y‖) ^ 5) := by
      apply mul_le_mul_of_nonneg_left _ hν
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    nlinarith [h', h4]
  have hX : ‖bkP M' a y + ν • bkPa M a y‖ ≤ 16 * K2 * (1 + ‖y‖) ^ 3 + 36 * ν * K1 * (1 + ‖y‖) ^ 5 :=
    (norm_add_le _ _).trans (by linarith)
  have hXC : 16 * K2 * (1 + ‖y‖) ^ 3 + 36 * ν * K1 * (1 + ‖y‖) ^ 5 ≤
      (16 * K2 + 36 * ν * K1) * (1 + ‖y‖) ^ 6 := by
    have h3 : (1 + ‖y‖) ^ 3 ≤ (1 + ‖y‖) ^ 6 :=
      pow_le_pow_right₀ (by linarith [norm_nonneg y]) (by norm_num)
    have h5 : (1 + ‖y‖) ^ 5 ≤ (1 + ‖y‖) ^ 6 :=
      pow_le_pow_right₀ (by linarith [norm_nonneg y]) (by norm_num)
    have hc2 : (0:ℝ) ≤ 16 * K2 := by linarith
    have hc5 : (0:ℝ) ≤ 36 * ν * K1 := by nlinarith [mul_nonneg hν hK1nn]
    nlinarith [mul_le_mul_of_nonneg_left h3 hc2, mul_le_mul_of_nonneg_left h5 hc5]
  calc bkG a y * ‖bkP M' a y + ν • bkPa M a y‖
      ≤ Real.exp (-(sq2 y) / (4 * A2)) * ‖bkP M' a y + ν • bkPa M a y‖ :=
        mul_le_mul_of_nonneg_right hGle (norm_nonneg _)
    _ ≤ Real.exp (-(sq2 y) / (4 * A2)) * ((16 * K2 + 36 * ν * K1) * (1 + ‖y‖) ^ 6) :=
        mul_le_mul_of_nonneg_left (hX.trans hXC) (Real.exp_pos _).le
    _ = (16 * K2 + 36 * ν * K1) * ((1 + ‖y‖) ^ 6 * Real.exp (-(sq2 y) / (4 * A2))) := by ring

lemma bkT3_brk_norm (M : Mat3) (K1 : ℝ) (hK1 : ∀ i j, |M i j| ≤ K1) (a A2 : ℝ) (ha : 1 ≤ a)
    (haA : a ≤ A2) (y : ℝ × ℝ) :
    ‖bkG a y • bkP M a y‖ ≤ 16 * K1 * ((1 + ‖y‖) ^ 6 * Real.exp (-(sq2 y) / (4 * A2))) := by
  obtain ⟨hG0, hGle⟩ := bkT3_G_le a A2 ha haA y
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hG0]
  have hP : ‖bkP M a y‖ ≤ 16 * K1 * (1 + ‖y‖) ^ 6 := by
    have h := bkT3_bkP_norm M a ha y
    have hK := bkT3_Kc_le M K1 hK1
    have hK1' : 0 ≤ K1 := by linarith [hK1 0 0, abs_nonneg (M 0 0)]
    have h3 : (1 + ‖y‖) ^ 3 ≤ (1 + ‖y‖) ^ 6 :=
      pow_le_pow_right₀ (by linarith [norm_nonneg y]) (by norm_num)
    have a1 : bkT3_Kc M * (1 + ‖y‖) ^ 3 ≤ 4 * K1 * (1 + ‖y‖) ^ 3 :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    have a2 : 16 * K1 * (1 + ‖y‖) ^ 3 ≤ 16 * K1 * (1 + ‖y‖) ^ 6 :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    linarith
  calc bkG a y * ‖bkP M a y‖
      ≤ Real.exp (-(sq2 y) / (4 * A2)) * ‖bkP M a y‖ :=
        mul_le_mul_of_nonneg_right hGle (norm_nonneg _)
    _ ≤ Real.exp (-(sq2 y) / (4 * A2)) * (16 * K1 * (1 + ‖y‖) ^ 6) :=
        mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
    _ = 16 * K1 * ((1 + ‖y‖) ^ 6 * Real.exp (-(sq2 y) / (4 * A2))) := by ring

/-- **(T3)** Termwise `s`-differentiation of `h^p_A` (source 4978, 4741-4745). -/
theorem hpASumS (as : ℝ) (χf : ℝ → ℝ) : HpASumS as χf := by
  unfold HpASumS
  intro hχ ν hν A hA s hs x
  have hMd : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (Ay ν χf A) t :=
    fun t ht => ayDiffAt as χf hχ ν A hA t ht
  have hC1 : ContDiffOn ℝ 1 (Ay ν χf A) (Ioi 0) := by
    have hc : ContDiffOn ℝ 1 (fun t : ℝ => χf (ν * t)) (Ioi 0) :=
      ((hχ.smooth.comp (contDiff_const.mul contDiff_id)).contDiffOn).of_le (by norm_num)
    have ha : ContDiffOn ℝ 1 A (Ioi 0) := hA.smooth.of_le (by norm_num)
    unfold Ay
    exact hc.smul ha
  have hDC : ContinuousOn (deriv (Ay ν χf A)) (Ioi 0) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hJpos : ∀ t ∈ Icc (s / 2) (2 * s), 0 < t := fun t ht => by linarith [ht.1]
  have hsJ : s ∈ Icc (s / 2) (2 * s) := ⟨by linarith, by linarith⟩
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := Ay ν χf A) (fun t ht => (hMd t (hJpos t ht)).continuousAt.continuousWithinAt)
  obtain ⟨K2, hK2⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := deriv (Ay ν χf A)) (hDC.mono (fun t ht => hJpos t ht))
  have hK1nn : 0 ≤ K1 := (norm_nonneg _).trans (hK1 s hsJ)
  have hK2nn : 0 ≤ K2 := (norm_nonneg _).trans (hK2 s hsJ)
  have hMb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |Ay ν χf A t i j| ≤ K1 :=
    fun t ht i j => (bkT3_entry_le _ i j).trans (hK1 t ht)
  have hDb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |deriv (Ay ν χf A) t i j| ≤ K2 :=
    fun t ht i j => (bkT3_entry_le _ i j).trans (hK2 t ht)
  have hA2 : 0 < ageA ν (2 * s) := by
    have := bk_one_le_ageA hν (by linarith : (0:ℝ) < 2 * s)
    linarith
  have hτa1 : ∀ τ ∈ Ioo (s / 2) (2 * s), 1 ≤ ageA ν τ := fun τ hτ =>
    bk_one_le_ageA hν (by linarith [hτ.1] : (0:ℝ) < τ)
  have hτA2 : ∀ τ ∈ Ioo (s / 2) (2 * s), ageA ν τ ≤ ageA ν (2 * s) := by
    intro τ hτ
    unfold ageA
    have := mul_le_mul_of_nonneg_left hτ.2.le hν.le
    linarith
  have hsI : s ∈ Ioo (s / 2) (2 * s) := ⟨by linarith, by linarith⟩
  have hbd : ∀ (j : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      ‖bkT3_dg ν χf A τ j x‖ ≤ (16 * K2 + 36 * ν * K1) * bkMaj ν (ageA ν (2 * s)) j x := by
    intro j τ hτ
    have hτJ : τ ∈ Icc (s / 2) (2 * s) := ⟨hτ.1.le, hτ.2.le⟩
    have h := bkT3_dg_norm (Ay ν χf A τ) (deriv (Ay ν χf A) τ) K1 K2 ν (ageA ν τ)
      (ageA ν (2 * s)) hν.le (hMb τ hτJ) (hDb τ hτJ) hK1nn hK2nn (hτa1 τ hτ) (hτA2 τ hτ)
      (xj ν j x)
    unfold bkT3_dg bkMaj
    exact h
  have hbrk : ∀ j : ℤ, ‖brk ν χf A s j x‖ ≤ 16 * K1 * bkMaj ν (ageA ν (2 * s)) j x := by
    intro j
    rw [brkClosed ν χf A s j x]
    have h := bkT3_brk_norm (Ay ν χf A s) K1 (hMb s hsJ) (ageA ν s) (ageA ν (2 * s))
      (bk_one_le_ageA hν hs) (hτA2 s hsI) (xj ν j x)
    unfold bkMaj
    exact h
  have hsum0 : Summable (fun j : ℤ => brk ν χf A s j x) := by
    have hU0 : Summable (fun j : ℤ => 16 * K1 * bkMaj ν (ageA ν (2 * s)) j x) :=
      (bkMajSummable ν (ageA ν (2 * s)) x hν hA2).mul_left (16 * K1)
    exact (Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbrk hU0).of_norm
  have hU : Summable (fun j : ℤ => (16 * K2 + 36 * ν * K1) * bkMaj ν (ageA ν (2 * s)) j x) :=
    (bkMajSummable ν (ageA ν (2 * s)) x hν hA2).mul_left (16 * K2 + 36 * ν * K1)
  have hgd : ∀ (j : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      HasDerivAt (fun τ' => brk ν χf A τ' j x) (bkT3_dg ν χf A τ j x) τ := by
    intro j τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have hA0 : 0 < ageA ν τ := by linarith [hτa1 τ hτ]
    exact brkDerivSClosed ν χf A τ j x (deriv (Ay ν χf A) τ) hA0
      (ayDiffAt as χf hχ ν A hA τ hτ0).hasDerivAt
  have hH := hasDerivAt_tsum_of_isPreconnected (g := fun j τ => brk ν χf A τ j x)
    (g' := fun j τ => bkT3_dg ν χf A τ j x) (u := fun j : ℤ =>
      (16 * K2 + 36 * ν * K1) * bkMaj ν (ageA ν (2 * s)) j x)
    hU isOpen_Ioo isPreconnected_Ioo (fun n τ hτ => hgd n τ hτ)
    (fun n τ hτ => hbd n τ hτ) hsI hsum0 hsI
  have hH' : HasDerivAt (fun z => hpA ν χf A z x) (∑' n : ℤ, bkT3_dg ν χf A s n x) s := by
    simp only [hpA_eq_tsum_brk]
    exact hH
  have hfd : (fun j : ℤ => deriv (fun s' => brk ν χf A s' j x) s) =
      fun j => bkT3_dg ν χf A s j x :=
    funext fun j => (hgd j s hsI).deriv
  rw [hfd, hH'.deriv]
  have hsumD : Summable (fun j : ℤ => bkT3_dg ν χf A s j x) :=
    (Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hbd j s hsI) hU).of_norm
  exact hsumD.hasSum

end UnforcedLeray.Short.PartIIIb.Concrete
