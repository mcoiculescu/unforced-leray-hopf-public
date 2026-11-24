import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_2.Calc3

/-!
# `PartIII-b:C/asrc/ra/9/1/2/8/2` : `geoRingRemBound`

Source `the November 2 reference manuscript`
lines 5034-5039, 4979-4980.  `ringRem ν ε b = ν[2(𝒦+1)∂_q b - ε(𝒦+1)²b + ε b_r e_r]`,
`b = h^p_A + εΘ`, `Θ = (0, (1-𝒦)ψ^p_A)`.  Calc2: `‖ringRem‖ ≤ 18 (1+|η|)² Σ_{|w|≤2}‖wordW w b‖`;
Calc3: words of `Θ` of length `≤ 2` are words of `ψ^p_A` of length `≤ 3` with weight `(1+|η|)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wordsLE_two_card : (wordsLE 2).card ≤ 13 := by decide

theorem word_theta_bound (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hψ : ContDiffOn ℝ 3 (psiM ν χf A) UC) {q : Chart} (hq : q ∈ UC)
    {w : List (Fin 3)} (hw : w.length ≤ 2) :
    ‖wordW w (thetaM ν χf A) q‖ ≤ 5 * (1 + |q.2.2|) * SW 3 (psiM ν χf A) q := by
  have hψ1 : ContDiffOn ℝ 1 (psiM ν χf A) UC := cd_mono (by norm_num) hψ
  have hg : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (psiM ν χf A - Kc (psiM ν χf A)) UC := by
    have h1 : ContDiffOn ℝ 2 (psiM ν χf A) UC := cd_mono (by norm_num) hψ
    have h2 : ContDiffOn ℝ 2 (Kc (psiM ν χf A)) UC := cd_Kc (n := 2) (by simpa using hψ)
    exact cd_mono hw (h1.sub h2)
  have e1 := wordW_congr w (thetaM_eq ν χf A hψ1) q hq
  have e2 := wordW_clm Lth w (f := psiM ν χf A - Kc (psiM ν χf A)) hg q hq
  have h1 : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (psiM ν χf A) UC := cd_mono hw (cd_mono (by norm_num) hψ)
  have h2 : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (Kc (psiM ν χf A)) UC :=
    cd_mono hw (cd_Kc (n := 2) (by simpa using hψ))
  have e3 := wordW_sub w h1 h2 q hq
  rw [e1]
  rw [e2, e3, norm_Lth]
  have b1 : ‖wordW w (psiM ν χf A) q‖ ≤ SW 3 (psiM ν χf A) q := norm_le_SW (by omega) _ q
  have b2 := Kc_word_bound hψ hq hw
  have hx := abs_nonneg q.2.2
  have hT := SW_nonneg 3 (psiM ν χf A) q
  have : |wordW w (psiM ν χf A) q - wordW w (Kc (psiM ν χf A)) q|
      ≤ |wordW w (psiM ν χf A) q| + |wordW w (Kc (psiM ν χf A)) q| := abs_sub _ _
  rw [Real.norm_eq_abs] at b1 b2
  nlinarith

theorem word_hb_bound (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (hε1 : ε ≤ 1) (hε : 0 < ε)
    (hh : ContDiffOn ℝ 4 (hpM ν χf A) UC) (hψ : ContDiffOn ℝ 3 (psiM ν χf A) UC)
    {q : Chart} (hq : q ∈ UC) {w : List (Fin 3)} (hw : w.length ≤ 2) :
    ‖wordW w (hbM ν ε χf A) q‖
      ≤ ‖wordW w (hpM ν χf A) q‖ + 5 * (1 + |q.2.2|) * SW 3 (psiM ν χf A) q := by
  have hhw : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (hpM ν χf A) UC := cd_mono (show w.length ≤ 4 by omega) hh
  have hψ1 : ContDiffOn ℝ 1 (psiM ν χf A) UC := cd_mono (by norm_num) hψ
  have hθ : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (thetaM ν χf A) UC := by
    have h1 : ContDiffOn ℝ 2 (psiM ν χf A) UC := cd_mono (by norm_num) hψ
    have h2 : ContDiffOn ℝ 2 (Kc (psiM ν χf A)) UC := cd_Kc (n := 2) (by simpa using hψ)
    have hg := h1.sub h2
    have := (Lth.contDiff.comp_contDiffOn hg).congr (fun x hx => thetaM_eq ν χf A hψ1 x hx)
    exact cd_mono hw this
  have e1 : wordW w (hbM ν ε χf A) q = wordW w (hpM ν χf A) q + ε • wordW w (thetaM ν χf A) q := by
    show wordW w (hpM ν χf A + ε • thetaM ν χf A) q = _
    have hεθ : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (ε • thetaM ν χf A) UC := hθ.const_smul ε
    rw [wordW_add w hhw hεθ q hq, wordW_smul ε w hθ q hq]
  rw [e1]
  have b := word_theta_bound ν χf A hψ hq hw
  have : ‖ε • wordW w (thetaM ν χf A) q‖ ≤ ‖wordW w (thetaM ν χf A) q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith [norm_nonneg (wordW w (thetaM ν χf A) q)]
  refine (norm_add_le _ _).trans ?_
  linarith

theorem SW_hb_bound (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (hε1 : ε ≤ 1) (hε : 0 < ε)
    (hh : ContDiffOn ℝ 4 (hpM ν χf A) UC) (hψ : ContDiffOn ℝ 3 (psiM ν χf A) UC)
    {q : Chart} (hq : q ∈ UC) :
    SW 2 (hbM ν ε χf A) q
      ≤ SW 2 (hpM ν χf A) q + 13 * (5 * (1 + |q.2.2|) * SW 3 (psiM ν χf A) q) := by
  have e : ∑ w ∈ wordsLE 2, ‖wordW w (hpM ν χf A) q‖ = SW 2 (hpM ν χf A) q := rfl
  show ∑ w ∈ wordsLE 2, ‖wordW w (hbM ν ε χf A) q‖ ≤ _
  calc ∑ w ∈ wordsLE 2, ‖wordW w (hbM ν ε χf A) q‖
      ≤ ∑ w ∈ wordsLE 2, (‖wordW w (hpM ν χf A) q‖ + 5 * (1 + |q.2.2|) * SW 3 (psiM ν χf A) q) :=
        Finset.sum_le_sum fun w hw => word_hb_bound ν ε χf A hε1 hε hh hψ hq (mem_wordsLE.1 hw)
    _ = ∑ w ∈ wordsLE 2, ‖wordW w (hpM ν χf A) q‖
        + (wordsLE 2).card * (5 * (1 + |q.2.2|) * SW 3 (psiM ν χf A) q) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        rw [e]
        have hc : ((wordsLE 2).card : ℝ) ≤ 13 := by exact_mod_cast wordsLE_two_card
        have hx := abs_nonneg q.2.2
        have hT := SW_nonneg 3 (psiM ν χf A) q
        have : 0 ≤ 5 * (1 + |q.2.2|) * SW 3 (psiM ν χf A) q := by positivity
        nlinarith

theorem arith_final (R Tb T2 T3 P Q x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) (hT2 : 0 ≤ T2)
    (hT3 : 0 ≤ T3) (s1 : T2 ≤ P) (s2 : T3 ≤ Q) (r1 : R ≤ 18 * (1 + x) ^ 2 * Tb)
    (r2 : Tb ≤ T2 + 13 * (5 * (1 + x) * T3)) :
    R ≤ 1170 * y * (1 + x) ^ 3 * (P + Q) := by
  have hP : 0 ≤ P := le_trans hT2 s1
  have hQ : 0 ≤ Q := le_trans hT3 s2
  have h1x : 1 ≤ 1 + x := by linarith
  have hx2 : (1 + x) ^ 2 ≤ (1 + x) ^ 3 := pow_le_pow_right₀ h1x (by norm_num)
  have hx3 : 0 ≤ (1 + x) ^ 3 := by positivity
  have hx2' : 0 ≤ (1 + x) ^ 2 := by positivity
  have a : Tb ≤ P + 65 * (1 + x) * Q := by nlinarith [mul_le_mul_of_nonneg_left s2 (by positivity : (0:ℝ) ≤ 65 * (1 + x))]
  have b : 18 * (1 + x) ^ 2 * Tb ≤ 18 * (1 + x) ^ 2 * (P + 65 * (1 + x) * Q) := by
    apply mul_le_mul_of_nonneg_left a; positivity
  have e1 : (1 + x) ^ 2 * P ≤ (1 + x) ^ 3 * P := mul_le_mul_of_nonneg_right hx2 hP
  have e2 : (1 + x) ^ 2 * ((1 + x) * Q) = (1 + x) ^ 3 * Q := by ring
  have e3 : 0 ≤ (1 + x) ^ 3 * P := by positivity
  have e4 : 0 ≤ (1 + x) ^ 3 * Q := by positivity
  have c : 18 * (1 + x) ^ 2 * (P + 65 * (1 + x) * Q) ≤ 1170 * (1 + x) ^ 3 * (P + Q) := by
    nlinarith
  have d : 0 ≤ 1170 * (1 + x) ^ 3 * (P + Q) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hy d]

/-- **Bound of `ringRem ν ε (hbM)`** (source 5034-5039). -/
theorem geoRingRemBound (as : ℝ) (χf : ℝ → ℝ) : GeoRingRemBound as χf := by
  refine ⟨1170, by norm_num, fun hχ ν μ ε hν hν1 hμ hε hε1 A hA hh hp q hq => ?_⟩
  have hqU : q ∈ UC := mem_UC hq
  have hψ3 : ContDiffOn ℝ 3 (psiM ν χf A) UC := cd_mono (by norm_num) hp
  have hψ1 : ContDiffOn ℝ 1 (psiM ν χf A) UC := cd_mono (by norm_num) hp
  have hh2 : ContDiffOn ℝ 2 (hpM ν χf A) UC := cd_mono (by norm_num) hh
  have hθ : ContDiffOn ℝ 2 (thetaM ν χf A) UC := by
    have h1 : ContDiffOn ℝ 2 (psiM ν χf A) UC := cd_mono (by norm_num) hp
    have h2 : ContDiffOn ℝ 2 (Kc (psiM ν χf A)) UC := cd_Kc (n := 2) (by simpa using hψ3)
    have hg := h1.sub h2
    exact (Lth.contDiff.comp_contDiffOn hg).congr (fun x hx => thetaM_eq ν χf A hψ1 x hx)
  have hb2 : ContDiffOn ℝ 2 (hbM ν ε χf A) UC := hh2.add (hθ.const_smul ε)
  have r1 := ringRem_pt hb2 hqU hν hν1 hε hε1
  have r2 := SW_hb_bound ν ε χf A hε1 hε hh hψ3 hqU
  have s1 : SW 2 (hpM ν χf A) q ≤ ∑ w ∈ budgetWords, ‖wordW w (hpM ν χf A) q‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (wordsLE_mono (by norm_num : 2 ≤ 4))
      (fun _ _ _ => norm_nonneg _)
  have s2 : SW 3 (psiM ν χf A) q ≤ ∑ w ∈ budgetWords, |wordW w (psiM ν χf A) q| := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (wordsLE_mono (by norm_num : 3 ≤ 4)) ?_
    intro _ _ _; exact abs_nonneg _
  have hq1 : 1 ≤ 1 + q.1⁻¹ := by
    have : 0 ≤ q.1⁻¹ := inv_nonneg.2 hq.le
    linarith
  have := arith_final _ _ _ _ _ _ _ _ (abs_nonneg q.2.2) hq1 (SW_nonneg 2 _ q) (SW_nonneg 3 _ q)
    s1 s2 r1 r2
  rw [Finset.sum_add_distrib]
  calc _ ≤ _ := this
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
