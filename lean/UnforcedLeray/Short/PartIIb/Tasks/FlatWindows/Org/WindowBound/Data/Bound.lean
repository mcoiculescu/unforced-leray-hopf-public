import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7_1

/-!
# `PartII-b:T13/1/7/1/2`: the two weighted window bounds (`WbdDBound`)

Source: `the November 2 reference manuscript` lines 1928-1933.

Pointwise, `|winCut a s| ≤ 1`, `|winCut a s / s| ≤ 2/a` and `|deriv (winCut a) s| ≤ M/a`, and both
window functions vanish off `winSet2 a`. So the cylinder norms of the windowed functions are the
norms on `winSet2 a` (`eLpNorm_restrict_eq_of_support_subset`), and the first and second parts of
`WindowWeightCompare` (applied to the vector lift of a scalar window function) reduce them to the
`H_r` norms on `winSet2 a`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

open UnforcedLeray.Short.IIb

/-- Off `[a/2, 4a]` the cutoff and its derivative vanish. -/
theorem wbdb_zero_off {M a : ℝ} (ha : 0 < a) (hcut : WinCutBd M) {s : ℝ}
    (hs : s ∉ Icc (a / 2) (4 * a)) : winCut a s = 0 ∧ deriv (winCut a) s = 0 := by
  have hns : s ∉ tsupport (winCut a) := fun h => hs ((hcut a ha).2.2.1 h)
  exact ⟨image_eq_zero_of_notMem_tsupport hns, deriv_of_notMem_tsupport hns⟩

/-- `|winCut a s / s| ≤ 2/a` for every `s`. -/
theorem wbdb_w_bound {M a : ℝ} (ha : 0 < a) (hcut : WinCutBd M) (s : ℝ) :
    |winCut a s / s| ≤ 2 / a := by
  by_cases hz : winCut a s = 0
  · rw [hz, zero_div, abs_zero]
    positivity
  · have hs : s ∈ Icc (a / 2) (4 * a) := by
      by_contra hn
      exact hz (wbdb_zero_off ha hcut hn).1
    obtain ⟨h1, -⟩ := hs
    have hs0 : 0 < s := lt_of_lt_of_le (show (0 : ℝ) < a / 2 by linarith) h1
    have hb1 : |winCut a s| ≤ 1 := by
      have h := (hcut a ha).2.2.2.1 s
      rw [abs_le]
      constructor <;> linarith [h.1, h.2]
    rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    have hge : 1 ≤ 2 / a * s := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      linarith
    linarith

/-- The vector lift of a scalar function on the first coordinate of `EuclideanSpace`. -/
def wbdb_e0 : CMerid := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

def wbdb_vec (g : Coord → ℂ) : CProf := fun x => g x • wbdb_e0

theorem wbdb_vec_norm (g : Coord → ℂ) (x : Coord) : ‖wbdb_vec g x‖ = ‖g x‖ := by
  simp [wbdb_vec, wbdb_e0, norm_smul]

theorem wbdb_vec_aesm {g : Coord → ℂ} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (wbdb_vec g) volume :=
  hg.smul_const wbdb_e0

theorem wbdb_eLpNorm_vec (μ : Measure Coord) (p : ℝ≥0∞) (g : Coord → ℂ) :
    eLpNorm (wbdb_vec g) p μ = eLpNorm g p μ := by
  rw [← eLpNorm_norm (wbdb_vec g), ← eLpNorm_norm g]
  simp only [wbdb_vec_norm]

/-- Pointwise norm comparison gives the `eLpNorm` comparison. -/
theorem wbdb_le_norm {f : Coord → ℂ} {g : Coord → CMerid} {μ : Measure Coord} {p : ℝ≥0∞}
    (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : eLpNorm f p μ ≤ eLpNorm g p μ := by
  calc eLpNorm f p μ = eLpNorm (fun x => ‖f x‖) p μ := by rw [eLpNorm_norm]
    _ ≤ eLpNorm (fun x => ‖g x‖) p μ := eLpNorm_mono_real (fun x => by simpa using h x)
    _ = eLpNorm g p μ := by rw [eLpNorm_norm]

/-- Scalar multiple of a norm, in `eLpNorm`. -/
theorem wbdb_smul_eLpNorm {K : ℝ} (hK : 0 ≤ K) (G : Coord → CMerid) (p : ℝ≥0∞)
    (μ : Measure Coord) :
    eLpNorm (fun x => K * ‖G x‖) p μ = ENNReal.ofReal K * eLpNorm G p μ := by
  have e : (fun x => K * ‖G x‖) = K • (fun x => ‖G x‖) := by
    funext x
    simp [smul_eq_mul]
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hK, eLpNorm_norm]

/-- Pointwise linear norm bound gives a linear `eLpNorm` bound. -/
theorem wbdb_bound_lin {f : Coord → ℂ} {G b : CProf} {μ : Measure Coord} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {K1 K2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hG : AEStronglyMeasurable G μ) (hb : AEStronglyMeasurable b μ)
    (h : ∀ x, ‖f x‖ ≤ K1 * ‖G x‖ + K2 * ‖b x‖) :
    eLpNorm f p μ ≤ ENNReal.ofReal K1 * eLpNorm G p μ + ENNReal.ofReal K2 * eLpNorm b p μ := by
  have hG' : AEStronglyMeasurable (fun x => K1 * ‖G x‖) μ := hG.norm.const_mul K1
  have hb' : AEStronglyMeasurable (fun x => K2 * ‖b x‖) μ := hb.norm.const_mul K2
  calc eLpNorm f p μ = eLpNorm (fun x => ‖f x‖) p μ := by rw [eLpNorm_norm]
    _ ≤ eLpNorm (fun x => K1 * ‖G x‖ + K2 * ‖b x‖) p μ :=
        eLpNorm_mono_real (fun x => by simpa using h x)
    _ = eLpNorm ((fun x => K1 * ‖G x‖) + (fun x => K2 * ‖b x‖)) p μ := rfl
    _ ≤ eLpNorm (fun x => K1 * ‖G x‖) p μ + eLpNorm (fun x => K2 * ‖b x‖) p μ :=
        eLpNorm_add_le hG' hb' hp
    _ = ENNReal.ofReal K1 * eLpNorm G p μ + ENNReal.ofReal K2 * eLpNorm b p μ := by
        rw [wbdb_smul_eLpNorm hK1, wbdb_smul_eLpNorm hK2]

/-- Pointwise bound on the windowed profile by the profile itself. -/
theorem wbdb_pt_profile {M a : ℝ} (ha : 0 < a) (hcut : WinCutBd M) (b : CProf) (i : Fin 2)
    (x : Coord) : ‖windowProfile a b x i‖ ≤ ‖b x‖ := by
  have hw1 : |winCut a x.1| ≤ 1 := by
    have h := (hcut a ha).2.2.2.1 x.1
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hbi : ‖b x i‖ ≤ ‖b x‖ := PiLp.norm_apply_le (b x) i
  have e : windowProfile a b x i = ((winCut a x.1 : ℝ) : ℂ) * b x i := by
    simp only [windowProfile, PiLp.smul_apply, smul_eq_mul]
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |winCut a x.1| * ‖b x i‖ ≤ 1 * ‖b x i‖ := mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
    _ = ‖b x i‖ := one_mul _
    _ ≤ ‖b x‖ := hbi

/-- Pointwise bound on the windowed source by `G` and `b`. -/
theorem wbdb_pt_source {M a : ℝ} (ha : 0 < a) (hM0 : 0 ≤ M) (hcut : WinCutBd M) (μ : ℂ)
    (G b : CProf) (i : Fin 2) (x : Coord) :
    ‖windowSource a μ G b x i‖ ≤ 2 / a * ‖G x‖ + 2 / a * (‖μ‖ + M / 2) * ‖b x‖ := by
  have hw : |winCut a x.1 / x.1| ≤ 2 / a := wbdb_w_bound ha hcut x.1
  have hd : |deriv (winCut a) x.1| ≤ M / a := (hcut a ha).2.2.2.2 x.1
  have hexp : windowSource a μ G b x i =
      ((winCut a x.1 / x.1 : ℝ) : ℂ) * (G x i - μ * b x i) +
        ((deriv (winCut a) x.1 : ℝ) : ℂ) * b x i := by
    simp only [windowSource, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have hGi : ‖G x i‖ ≤ ‖G x‖ := PiLp.norm_apply_le (G x) i
  have hbi : ‖b x i‖ ≤ ‖b x‖ := PiLp.norm_apply_le (b x) i
  have hsub : ‖G x i - μ * b x i‖ ≤ ‖G x i‖ + ‖μ‖ * ‖b x i‖ := by
    have := norm_sub_le (G x i) (μ * b x i)
    rw [norm_mul] at this
    exact this
  have hX : ‖G x i‖ + ‖μ‖ * ‖b x i‖ ≤ ‖G x‖ + ‖μ‖ * ‖b x‖ :=
    add_le_add hGi (mul_le_mul_of_nonneg_left hbi (norm_nonneg μ))
  have h2a : 0 ≤ 2 / a := by positivity
  have hMa : 0 ≤ M / a := div_nonneg hM0 ha.le
  rw [hexp]
  calc ‖((winCut a x.1 / x.1 : ℝ) : ℂ) * (G x i - μ * b x i) +
          ((deriv (winCut a) x.1 : ℝ) : ℂ) * b x i‖
      ≤ ‖((winCut a x.1 / x.1 : ℝ) : ℂ) * (G x i - μ * b x i)‖ +
          ‖((deriv (winCut a) x.1 : ℝ) : ℂ) * b x i‖ := norm_add_le _ _
    _ = |winCut a x.1 / x.1| * ‖G x i - μ * b x i‖ + |deriv (winCut a) x.1| * ‖b x i‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 / a * (‖G x‖ + ‖μ‖ * ‖b x‖) + M / a * ‖b x‖ :=
        add_le_add (mul_le_mul hw (hsub.trans hX) (norm_nonneg _) h2a)
          (mul_le_mul hd hbi (norm_nonneg _) hMa)
    _ = 2 / a * ‖G x‖ + 2 / a * (‖μ‖ + M / 2) * ‖b x‖ := by ring

/-- The windowed profile is supported in `winSet2 a`. -/
theorem wbdb_supp_profile {M a : ℝ} (ha : 0 < a) (hcut : WinCutBd M) (b : CProf) (i : Fin 2) :
    Function.support (fun x : Coord => windowProfile a b x i) ⊆ winSet2 a := by
  intro x hx
  have h1 : x.1 ∈ Icc (a / 2) (4 * a) := by
    by_contra hn
    apply Function.mem_support.1 hx
    simp [windowProfile, (wbdb_zero_off ha hcut hn).1]
  unfold winSet2
  exact Set.mem_prod.2 ⟨h1, Set.mem_univ _⟩

/-- The windowed source is supported in `winSet2 a`. -/
theorem wbdb_supp_source {M a : ℝ} (ha : 0 < a) (hcut : WinCutBd M) (μ : ℂ) (G b : CProf)
    (i : Fin 2) :
    Function.support (fun x : Coord => windowSource a μ G b x i) ⊆ winSet2 a := by
  intro x hx
  have h1 : x.1 ∈ Icc (a / 2) (4 * a) := by
    by_contra hn
    apply Function.mem_support.1 hx
    obtain ⟨h0, h0'⟩ := wbdb_zero_off ha hcut hn
    simp [windowSource, h0, h0']
  unfold winSet2
  exact Set.mem_prod.2 ⟨h1, Set.mem_univ _⟩

theorem wbddBound : UnforcedLeray.Short.IIb.WbdDBound := by
  unfold UnforcedLeray.Short.IIb.WbdDBound
  intro M hM0 hcut hW c r hc h1 h3 μ G b hG hb a ha i hum hfm
  have hA : MeasurableSet (winSet2 a) := measurableSet_Icc.prod MeasurableSet.univ
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h1.le
  have hsupU := wbdb_supp_profile (M := M) ha hcut b i
  have hsupF := wbdb_supp_source (M := M) ha hcut μ G b i
  have hVu := wbdb_vec_aesm hum
  have hVf := wbdb_vec_aesm hfm
  constructor
  · calc ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => windowProfile a b x i) (ENNReal.ofReal r) (cylMeas c)
        = ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => windowProfile a b x i) (ENNReal.ofReal r)
            ((cylMeas c).restrict (winSet2 a)) := by
          rw [eLpNorm_restrict_eq_of_support_subset hsupU]
      _ = ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (wbdb_vec (fun x => windowProfile a b x i)) (ENNReal.ofReal r)
            ((cylMeas c).restrict (winSet2 a)) := by
          rw [wbdb_eLpNorm_vec]
      _ ≤ 16 * hNormOn c r (winSet2 a) (wbdb_vec (fun x => windowProfile a b x i)) :=
          (hW c r a hc h1 h3 ha (winSet2 a) hA subset_rfl _ hVu).2
      _ = 16 * eLpNorm (fun x => windowProfile a b x i) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winSet2 a)) := by
          unfold hNormOn
          rw [wbdb_eLpNorm_vec]
      _ ≤ 16 * hNormOn c r (winSet2 a) b := by
          unfold hNormOn
          exact mul_le_mul_of_nonneg_left (wbdb_le_norm (fun x => wbdb_pt_profile ha hcut b i x)) zero_le
  · have hK1 : (0 : ℝ) ≤ 2 / a := by positivity
    have hK2 : (0 : ℝ) ≤ 2 / a * (‖μ‖ + M / 2) :=
      mul_nonneg hK1 (by linarith [norm_nonneg μ])
    have e1 : ENNReal.ofReal (2 / a * (‖μ‖ + M / 2)) =
        ENNReal.ofReal (2 / a) * ENNReal.ofReal (‖μ‖ + M / 2) :=
      ENNReal.ofReal_mul hK1
    have e2 : ENNReal.ofReal (32 / a) = 16 * ENNReal.ofReal (2 / a) := by
      rw [show (32 : ℝ) / a = 16 * (2 / a) by ring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
        ENNReal.ofReal_ofNat]
    calc ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => windowSource a μ G b x i) (ENNReal.ofReal r) (cylMeas c)
        = ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => windowSource a μ G b x i) (ENNReal.ofReal r)
            ((cylMeas c).restrict (winSet2 a)) := by
          rw [eLpNorm_restrict_eq_of_support_subset hsupF]
      _ = ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (wbdb_vec (fun x => windowSource a μ G b x i)) (ENNReal.ofReal r)
            ((cylMeas c).restrict (winSet2 a)) := by
          rw [wbdb_eLpNorm_vec]
      _ ≤ 16 * hNormOn c r (winSet2 a) (wbdb_vec (fun x => windowSource a μ G b x i)) :=
          (hW c r a hc h1 h3 ha (winSet2 a) hA subset_rfl _ hVf).2
      _ = 16 * eLpNorm (fun x => windowSource a μ G b x i) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winSet2 a)) := by
          unfold hNormOn
          rw [wbdb_eLpNorm_vec]
      _ ≤ 16 * (ENNReal.ofReal (2 / a) * eLpNorm G (ENNReal.ofReal r)
            ((hMeas c r).restrict (winSet2 a)) +
          ENNReal.ofReal (2 / a * (‖μ‖ + M / 2)) * eLpNorm b (ENNReal.ofReal r)
            ((hMeas c r).restrict (winSet2 a))) :=
          mul_le_mul_of_nonneg_left (wbdb_bound_lin hp1 hK1 hK2 hG.meas.restrict hb.meas.restrict
            (fun x => wbdb_pt_source ha hM0 hcut μ G b i x)) zero_le
      _ = ENNReal.ofReal (32 / a) * (hNormOn c r (winSet2 a) G +
            ENNReal.ofReal (‖μ‖ + M / 2) * hNormOn c r (winSet2 a) b) := by
          unfold hNormOn
          rw [e1, e2]
          ring

#print axioms wbddBound
