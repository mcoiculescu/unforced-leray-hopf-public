import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11

/-!
# `PartIII-b:C/rep/5/2/2/11/8` : the cutoff coefficient bounds `TCCoeff`

Source `the November 2 reference manuscript`
3684-3712. Pure one-variable calculus. With `t = νR²/r²` (`νR² = t r²`) and `L = R√ν`,
on the annulus `L ≤ r ≤ L√(5/4)` one has `t ∈ [4/5,1]` and `ν ≤ r²`, and the four coefficients are
explicit in `t`, `r⁻¹`, `w = ν r⁻²` and the derivatives `χ', χ'', χ'''` of the cutoff on `[4/5,1]`:
`A₁ = t χ' - w(4tχ' + 4t²χ'')`, `A₂ = 4(ν r⁻¹) tχ'`,
`B₁ = -(2tχ'+2t²χ'')r⁻² + w r⁻²(32tχ'+40t²χ''+8t³χ''')`, `B₂ = -2w(6tχ'+4t²χ'')`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

macro "tcc_fsr" : tactic =>
  `(tactic| first | (field_simp; ring) | field_simp | ring)

lemma tcc_hasDerivAt_T (ν R s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun s : ℝ => ν * (R ^ 2 / s ^ 2)) (-2 * ν * R ^ 2 / s ^ 3) s := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have h2 := ((hasDerivAt_const s (R ^ 2)).div h1 (pow_ne_zero 2 hs)).const_mul ν
  exact h2.congr_deriv (by tcc_fsr)

lemma tcc_hasDerivAt_comp (g : ℝ → ℝ) (hg : Differentiable ℝ g) (ν R s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun s : ℝ => g (ν * (R ^ 2 / s ^ 2)))
      (deriv g (ν * (R ^ 2 / s ^ 2)) * (-2 * ν * R ^ 2 / s ^ 3)) s :=
  (hg _).hasDerivAt.comp s (tcc_hasDerivAt_T ν R s hs)

lemma tcc_smooth (χ : ℝ → ℝ) (hχ : IsStreamCutoff χ) :
    Differentiable ℝ χ ∧ Differentiable ℝ (deriv χ) ∧ Differentiable ℝ (deriv (deriv χ)) ∧
      Continuous (deriv χ) ∧ Continuous (deriv (deriv χ)) ∧
      Continuous (deriv (deriv (deriv χ))) := by
  obtain ⟨d0, c1⟩ := contDiff_infty_iff_deriv.1 hχ.smooth
  obtain ⟨d1, c2⟩ := contDiff_infty_iff_deriv.1 c1
  obtain ⟨d2, c3⟩ := contDiff_infty_iff_deriv.1 c2
  exact ⟨d0, d1, d2, c1.continuous, c2.continuous, c3.continuous⟩

lemma tcc_bounded (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ M : ℝ, ∀ t ∈ Icc (4 / 5 : ℝ) 1, |f t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (4 / 5 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨M, fun t ht => by simpa [Real.norm_eq_abs] using hM t ht⟩

lemma tcc_deriv_C0 (χ : ℝ → ℝ) (hd : Differentiable ℝ χ) (ν R r : ℝ) (hr : r ≠ 0) :
    deriv (tcC0 ν R χ) r = -2 * (ν * (R ^ 2 / r ^ 2)) * deriv χ (ν * (R ^ 2 / r ^ 2)) / r := by
  have h := tcc_hasDerivAt_comp χ hd ν R r hr
  have e : deriv (tcC0 ν R χ) r = deriv (fun s : ℝ => χ (ν * (R ^ 2 / s ^ 2))) r := rfl
  rw [e, h.deriv]
  tcc_fsr

lemma tcc_deriv_deriv_C0 (χ : ℝ → ℝ) (hd : Differentiable ℝ χ)
    (hd1 : Differentiable ℝ (deriv χ)) (ν R r : ℝ) (hr : 0 < r) :
    deriv (deriv (tcC0 ν R χ)) r =
      (6 * (ν * (R ^ 2 / r ^ 2)) * deriv χ (ν * (R ^ 2 / r ^ 2)) +
        4 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χ) (ν * (R ^ 2 / r ^ 2))) / r ^ 2 := by
  have hr0 : r ≠ 0 := hr.ne'
  have hev : deriv (tcC0 ν R χ) =ᶠ[𝓝 r]
      fun s : ℝ => -2 * (ν * (R ^ 2 / s ^ 2)) * deriv χ (ν * (R ^ 2 / s ^ 2)) / s := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact tcc_deriv_C0 χ hd ν R s (ne_of_gt hs)
  rw [hev.deriv_eq]
  have hT := tcc_hasDerivAt_T ν R r hr0
  have hg := tcc_hasDerivAt_comp (deriv χ) hd1 ν R r hr0
  have hnum := ((hT.const_mul (-2)).mul hg).div (hasDerivAt_id' r) hr0
  refine (hnum.deriv).trans ?_
  have hu : -2 * ν * R ^ 2 / r ^ 3 = -2 * (ν * (R ^ 2 / r ^ 2)) / r := by ring
  rw [hu]
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply, Pi.sub_apply]
  tcc_fsr

lemma tcc_tcF0_eq (χ : ℝ → ℝ) (ν R s : ℝ) :
    tcF0 ν R χ s = -2 * (ν * (R ^ 2 / s ^ 2)) * deriv χ (ν * (R ^ 2 / s ^ 2)) / s ^ 2 := by
  unfold tcF0
  have hu : -2 * ν * R ^ 2 / s ^ 3 = -2 * (ν * (R ^ 2 / s ^ 2)) / s := by ring
  rw [hu]
  ring

lemma tcc_deriv_F0 (χ : ℝ → ℝ) (hd1 : Differentiable ℝ (deriv χ)) (ν R s : ℝ) (hs : 0 < s) :
    deriv (tcF0 ν R χ) s =
      (8 * (ν * (R ^ 2 / s ^ 2)) * deriv χ (ν * (R ^ 2 / s ^ 2)) +
        4 * ((ν * (R ^ 2 / s ^ 2)) * (ν * (R ^ 2 / s ^ 2))) * deriv (deriv χ) (ν * (R ^ 2 / s ^ 2)))
        / s ^ 3 := by
  have hs0 : s ≠ 0 := hs.ne'
  have hev : tcF0 ν R χ =ᶠ[𝓝 s]
      fun r : ℝ => -2 * (ν * (R ^ 2 / r ^ 2)) * deriv χ (ν * (R ^ 2 / r ^ 2)) / r ^ 2 := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    exact tcc_tcF0_eq χ ν R r
  rw [hev.deriv_eq]
  have hT := tcc_hasDerivAt_T ν R s hs0
  have hg := tcc_hasDerivAt_comp (deriv χ) hd1 ν R s hs0
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hnum := ((hT.const_mul (-2)).mul hg).div hp (pow_ne_zero 2 hs0)
  refine (hnum.deriv).trans ?_
  have hu : -2 * ν * R ^ 2 / s ^ 3 = -2 * (ν * (R ^ 2 / s ^ 2)) / s := by ring
  rw [hu]
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply, Pi.sub_apply]
  tcc_fsr

lemma tcc_deriv_deriv_F0 (χ : ℝ → ℝ) (hd1 : Differentiable ℝ (deriv χ))
    (hd2 : Differentiable ℝ (deriv (deriv χ))) (ν R r : ℝ) (hr : 0 < r) :
    deriv (deriv (tcF0 ν R χ)) r =
      -(40 * (ν * (R ^ 2 / r ^ 2)) * deriv χ (ν * (R ^ 2 / r ^ 2)) +
        44 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χ) (ν * (R ^ 2 / r ^ 2)) +
        8 * (ν * (R ^ 2 / r ^ 2)) ^ 3 * deriv (deriv (deriv χ)) (ν * (R ^ 2 / r ^ 2))) / r ^ 4 := by
  have hr0 : r ≠ 0 := hr.ne'
  have hev : deriv (tcF0 ν R χ) =ᶠ[𝓝 r]
      fun s : ℝ => (8 * (ν * (R ^ 2 / s ^ 2)) * deriv χ (ν * (R ^ 2 / s ^ 2)) +
        4 * ((ν * (R ^ 2 / s ^ 2)) * (ν * (R ^ 2 / s ^ 2))) * deriv (deriv χ) (ν * (R ^ 2 / s ^ 2)))
        / s ^ 3 := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact tcc_deriv_F0 χ hd1 ν R s hs
  rw [hev.deriv_eq]
  have hT := tcc_hasDerivAt_T ν R r hr0
  have hg1 := tcc_hasDerivAt_comp (deriv χ) hd1 ν R r hr0
  have hg2 := tcc_hasDerivAt_comp (deriv (deriv χ)) hd2 ν R r hr0
  have hp : HasDerivAt (fun x : ℝ => x ^ 3) (3 * r ^ 2) r := by
    simpa using hasDerivAt_pow 3 r
  have hN := ((hT.const_mul 8).mul hg1).add
    (((hT.mul hT).const_mul 4).mul hg2)
  have hnum := hN.div hp (pow_ne_zero 3 hr0)
  refine (hnum.deriv).trans ?_
  have hu : -2 * ν * R ^ 2 / r ^ 3 = -2 * (ν * (R ^ 2 / r ^ 2)) / r := by ring
  rw [hu]
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply, Pi.sub_apply]
  tcc_fsr

lemma tcc_coeff_bounds (t x1 x2 x3 w a v L M : ℝ) (ht0 : 4 / 5 ≤ t) (ht1 : t ≤ 1)
    (hx1 : |x1| ≤ M) (hx2 : |x2| ≤ M) (hx3 : |x3| ≤ M) (hM : 1 ≤ M)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha0 : 0 ≤ a) (haL : a ≤ L⁻¹) (hL : 0 < L)
    (hv : |v| ≤ L⁻¹) :
    |t * x1 - w * (4 * t * x1 + 4 * t ^ 2 * x2)| ≤ 100 * M ∧
    |4 * v * t * x1| ≤ 100 * M * L⁻¹ ∧
    |-(2 * t * x1 + 2 * t ^ 2 * x2) * a ^ 2 + w * a ^ 2 * (32 * t * x1 + 40 * t ^ 2 * x2 + 8 * t ^ 3 * x3)|
      ≤ 100 * M * (L⁻¹) ^ 2 ∧
    |-2 * w * (6 * t * x1 + 4 * t ^ 2 * x2)| ≤ 100 * M := by
  have ht0' : 0 ≤ t := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hLinv : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  have hpt2 : |t ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg t)]
    nlinarith
  have hpt3 : |t ^ 3| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg ht0' 3)]
    have h2 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hp1 : |t * x1| ≤ M := by
    rw [abs_mul, abs_of_nonneg ht0']
    have h := mul_le_mul_of_nonneg_right ht1 (abs_nonneg x1)
    linarith
  have hp2 : |t ^ 2 * x2| ≤ M := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right hpt2 (abs_nonneg x2)
    linarith
  have hp3 : |t ^ 3 * x3| ≤ M := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right hpt3 (abs_nonneg x3)
    linarith
  obtain ⟨hp1l, hp1u⟩ := abs_le.1 hp1
  obtain ⟨hp2l, hp2u⟩ := abs_le.1 hp2
  obtain ⟨hp3l, hp3u⟩ := abs_le.1 hp3
  have hX : |4 * t * x1 + 4 * t ^ 2 * x2| ≤ 8 * M := by
    rw [abs_le]; constructor <;> linarith
  have hY : |6 * t * x1 + 4 * t ^ 2 * x2| ≤ 10 * M := by
    rw [abs_le]; constructor <;> linarith
  have hQ : |2 * t * x1 + 2 * t ^ 2 * x2| ≤ 4 * M := by
    rw [abs_le]; constructor <;> linarith
  have hR3 : |32 * t * x1 + 40 * t ^ 2 * x2 + 8 * t ^ 3 * x3| ≤ 80 * M := by
    rw [abs_le]; constructor <;> linarith
  have hwX : |w * (4 * t * x1 + 4 * t ^ 2 * x2)| ≤ 8 * M := by
    rw [abs_mul, abs_of_nonneg hw0]
    have h := mul_le_mul_of_nonneg_right hw1 (abs_nonneg (4 * t * x1 + 4 * t ^ 2 * x2))
    linarith
  have hwY : |w * (6 * t * x1 + 4 * t ^ 2 * x2)| ≤ 10 * M := by
    rw [abs_mul, abs_of_nonneg hw0]
    have h := mul_le_mul_of_nonneg_right hw1 (abs_nonneg (6 * t * x1 + 4 * t ^ 2 * x2))
    linarith
  obtain ⟨hwXl, hwXu⟩ := abs_le.1 hwX
  obtain ⟨hwYl, hwYu⟩ := abs_le.1 hwY
  have ha2 : a ^ 2 ≤ (L⁻¹) ^ 2 := by
    have h := mul_le_mul haL haL ha0 hLinv
    linarith
  have ha2' : 0 ≤ a ^ 2 := sq_nonneg a
  have hML : 0 ≤ M * L⁻¹ := mul_nonneg hM0 hLinv
  have hML2 : 0 ≤ M * (L⁻¹) ^ 2 := mul_nonneg hM0 (sq_nonneg _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · have hv2 : |v| * |t * x1| ≤ L⁻¹ * M := mul_le_mul hv hp1 (abs_nonneg _) hLinv
    have key : |4 * v * t * x1| = 4 * (|v| * |t * x1|) := by
      rw [show (4 : ℝ) * v * t * x1 = 4 * (v * (t * x1)) by ring, abs_mul, abs_mul]
      norm_num
    rw [key]
    linarith
  · have e1 : |(2 * t * x1 + 2 * t ^ 2 * x2) * a ^ 2| ≤ 4 * M * (L⁻¹) ^ 2 := by
      rw [abs_mul, abs_of_nonneg ha2']
      exact mul_le_mul hQ ha2 ha2' (by linarith)
    have hwa : w * a ^ 2 ≤ (L⁻¹) ^ 2 :=
      (mul_le_of_le_one_left ha2' hw1).trans ha2
    have e2 : |w * a ^ 2 * (32 * t * x1 + 40 * t ^ 2 * x2 + 8 * t ^ 3 * x3)| ≤
        80 * M * (L⁻¹) ^ 2 := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hw0 ha2')]
      have h := mul_le_mul hwa hR3 (abs_nonneg _) (by positivity)
      linarith [h]
    obtain ⟨e1l, e1u⟩ := abs_le.1 e1
    obtain ⟨e2l, e2u⟩ := abs_le.1 e2
    rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

theorem tcCoeff : TCCoeff := by
  intro χy hχ
  obtain ⟨d0, d1, d2, c1, c2, c3⟩ := tcc_smooth χy hχ
  obtain ⟨M1, hM1⟩ := tcc_bounded _ c1
  obtain ⟨M2, hM2⟩ := tcc_bounded _ c2
  obtain ⟨M3, hM3⟩ := tcc_bounded _ c3
  obtain ⟨M, hM, hMb⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ t ∈ Icc (4 / 5 : ℝ) 1,
      |deriv χy t| ≤ M ∧ |deriv (deriv χy) t| ≤ M ∧ |deriv (deriv (deriv χy)) t| ≤ M := by
    refine ⟨|M1| + |M2| + |M3| + 1, ?_, fun t ht => ⟨?_, ?_, ?_⟩⟩
    · have := abs_nonneg M1; have := abs_nonneg M2; have := abs_nonneg M3; linarith
    · have := hM1 t ht; have := le_abs_self M1; have := abs_nonneg M2; have := abs_nonneg M3
      linarith
    · have := hM2 t ht; have := le_abs_self M2; have := abs_nonneg M1; have := abs_nonneg M3
      linarith
    · have := hM3 t ht; have := le_abs_self M3; have := abs_nonneg M1; have := abs_nonneg M2
      linarith
  refine ⟨100 * M, by linarith, ?_⟩
  intro ν R hν hν1 hR1 r hr1 hr2
  have hL : 0 < R * Real.sqrt ν := mul_pos (by linarith) (Real.sqrt_pos.2 hν)
  have hr : 0 < r := lt_of_lt_of_le hL hr1
  have hr0 : r ≠ 0 := hr.ne'
  have hsq1 : (R * Real.sqrt ν) ^ 2 = R ^ 2 * ν := by
    rw [mul_pow, Real.sq_sqrt hν.le]
  have hsq2 : (R * Real.sqrt (5 * ν / 4)) ^ 2 = R ^ 2 * (5 * ν / 4) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hLr2 : (R * Real.sqrt ν) ^ 2 ≤ r ^ 2 := by
    have h := mul_le_mul hr1 hr1 hL.le hr.le
    linarith [h, sq (R * Real.sqrt ν), sq r]
  have hr2' : r ^ 2 ≤ (R * Real.sqrt (5 * ν / 4)) ^ 2 := by
    have h := mul_le_mul hr2 hr2 hr.le (le_trans hr.le hr2)
    linarith [h, sq (R * Real.sqrt (5 * ν / 4)), sq r]
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have ht_def : ν * (R ^ 2 / r ^ 2) = (R ^ 2 * ν) / r ^ 2 := by ring
  have ht1 : ν * (R ^ 2 / r ^ 2) ≤ 1 := by
    rw [ht_def, div_le_one (by positivity)]
    linarith
  have ht0 : 4 / 5 ≤ ν * (R ^ 2 / r ^ 2) := by
    rw [ht_def, le_div_iff₀ (by positivity)]
    rw [hsq2] at hr2'
    linarith
  have hw0 : 0 ≤ ν * (r⁻¹) ^ 2 := by positivity
  have hw1 : ν * (r⁻¹) ^ 2 ≤ 1 := by
    have e : ν * (r⁻¹) ^ 2 = ν / r ^ 2 := by rw [inv_pow]; ring
    rw [e, div_le_one (by positivity)]
    have h := le_mul_of_one_le_left hν.le hR2
    linarith
  have ha0 : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
  have haL : r⁻¹ ≤ (R * Real.sqrt ν)⁻¹ := inv_anti₀ hL hr1
  have hv : |ν * r⁻¹| ≤ (R * Real.sqrt ν)⁻¹ := by
    rw [abs_of_nonneg (mul_nonneg hν.le ha0)]
    have h := mul_le_mul_of_nonneg_right hν1 ha0
    linarith
  have hm := hMb _ ⟨ht0, ht1⟩
  -- derivative identities
  have hdC0 := tcc_deriv_C0 χy d0 ν R r hr0
  have hdd := tcc_deriv_deriv_C0 χy d0 d1 ν R r hr
  have hF := tcc_tcF0_eq χy ν R r
  have hF1 := tcc_deriv_F0 χy d1 ν R r hr
  have hF2 := tcc_deriv_deriv_F0 χy d1 d2 ν R r hr
  have eA1 : tcA1 ν R χy r =
      (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) -
        (ν * r⁻¹ ^ 2) * (4 * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) +
          4 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χy) (ν * (R ^ 2 / r ^ 2))) := by
    unfold tcA1
    rw [hdC0, hdd]
    tcc_fsr
  have eA2 : tcA2 ν R χy r =
      4 * (ν * r⁻¹) * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) := by
    unfold tcA2
    rw [hdC0]
    tcc_fsr
  have eB1 : tcB1 ν R χy r =
      -(2 * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) +
          2 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χy) (ν * (R ^ 2 / r ^ 2))) * (r⁻¹) ^ 2 +
        (ν * (r⁻¹) ^ 2) * (r⁻¹) ^ 2 *
          (32 * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) +
            40 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χy) (ν * (R ^ 2 / r ^ 2)) +
            8 * (ν * (R ^ 2 / r ^ 2)) ^ 3 * deriv (deriv (deriv χy)) (ν * (R ^ 2 / r ^ 2))) := by
    unfold tcB1
    rw [hF, hF1, hF2]
    tcc_fsr
  have eB2 : tcB2 ν R χy r =
      -2 * (ν * (r⁻¹) ^ 2) *
        (6 * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) +
          4 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χy) (ν * (R ^ 2 / r ^ 2))) := by
    unfold tcB2
    rw [hF, hF1]
    tcc_fsr
  obtain ⟨b1, b2, b3, b4⟩ := tcc_coeff_bounds (ν * (R ^ 2 / r ^ 2))
    (deriv χy (ν * (R ^ 2 / r ^ 2))) (deriv (deriv χy) (ν * (R ^ 2 / r ^ 2)))
    (deriv (deriv (deriv χy)) (ν * (R ^ 2 / r ^ 2))) (ν * (r⁻¹) ^ 2) r⁻¹ (ν * r⁻¹)
    (R * Real.sqrt ν) M ht0 ht1 hm.1 hm.2.1 hm.2.2 hM hw0 hw1 ha0 haL hL hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eA1]
    exact b1
  · rw [eA2]
    exact b2
  · rw [eB1]
    exact b3
  · rw [eB2]
    exact b4

end UnforcedLeray.Short.PartIIIb.Concrete
