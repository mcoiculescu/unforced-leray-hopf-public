import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.GreenSup
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.CoefSmoothBand
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.ModeDataBounds
import UnforcedLeray.Short.PartIIa.Sub.N02_4_5.Cond
import UnforcedLeray.Short.PartIIa.Sub.N02_4_5
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.GenHyp
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.ConvFderiv

/-!
# `LerayModeBound` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/15`)

Source of record `the November 2 reference manuscript`
lines 1713-1727. For `n ≠ 0` with `k = k_n`, the solenoidal mode `(-∂_η ψ_n, i k ψ_n)` is bounded by
`(|k| + 1)² E / k⁴`, where `E` bounds the mode data (`ModeDataBounds`). Since `|k| ≥ 2π/c` and
`1/k² ≤ c²/(2π²(1+n²))`, this is a summable bound `C/(1+n²)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-- Norm of a two-component `MeridC` vector. -/
theorem lmb_norm_two (u v : ℂ) : ‖(!₂[u, v] : MeridC)‖ ≤ ‖u‖ + ‖v‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  nlinarith [norm_nonneg u, norm_nonneg v]

/-- Core bound for one mode in the abstract form `(k, a, b)`. -/
theorem lmb_core (k : ℝ) (hk : k ≠ 0) (E : ℝ) (a b : ℝ × ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hGcs : HasCompactSupport (nzmsH2 k a b))
    (hZ : ∀ y, ‖b y‖ ≤ E / k ^ 2) (hA : ∀ y, ‖fderiv ℝ a y (0, 1)‖ ≤ E / k ^ 2)
    (hBZ : ∀ y, ‖fderiv ℝ b y (0, 1)‖ ≤ E / k ^ 2)
    (hAA : ∀ y, ‖fderiv ℝ (fun z => fderiv ℝ a z (0, 1)) y (0, 1)‖ ≤ E / k ^ 2)
    (x : ℝ × ℝ) :
    ‖(!₂[-dEta2 (nzConv k (nzmsH2 k a b)) x,
        Complex.I * ((k : ℂ) * nzConv k (nzmsH2 k a b) x)] : MeridC)‖
      ≤ (|k| + 1) ^ 2 * E / k ^ 4 := by
  have hG : ContDiff ℝ ∞ (nzmsH2 k a b) := nzmsH2_smooth ha hb
  have hGc : Continuous (nzmsH2 k a b) := hG.continuous
  have hH : Continuous (fun q => fderiv ℝ (nzmsH2 k a b) q (0, 1)) :=
    (nzms_dEta_smooth hG).continuous
  have hk0 : 0 < |k| := abs_pos.mpr hk
  -- sup bound on the source `h₂`
  have hGb : ∀ y, ‖nzmsH2 k a b y‖ ≤ (|k| + 1) * E / k ^ 2 := by
    intro y
    show ‖Complex.I * (k : ℂ) * b y - fderiv ℝ a y (0, 1)‖ ≤ _
    calc ‖Complex.I * (k : ℂ) * b y - fderiv ℝ a y (0, 1)‖
        ≤ ‖Complex.I * (k : ℂ) * b y‖ + ‖fderiv ℝ a y (0, 1)‖ := norm_sub_le _ _
      _ = |k| * ‖b y‖ + ‖fderiv ℝ a y (0, 1)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |k| * (E / k ^ 2) + E / k ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hZ y) hk0.le) (hA y)
      _ = (|k| + 1) * E / k ^ 2 := by ring
  -- sup bound on `∂_η h₂`
  have hHb : ∀ q, ‖fderiv ℝ (nzmsH2 k a b) q (0, 1)‖ ≤ (|k| + 1) * E / k ^ 2 := by
    intro q
    rw [nzmsH2_dEta ha hb q]
    calc ‖Complex.I * (k : ℂ) * fderiv ℝ b q (0, 1)
          - fderiv ℝ (fun y => fderiv ℝ a y (0, 1)) q (0, 1)‖
        ≤ ‖Complex.I * (k : ℂ) * fderiv ℝ b q (0, 1)‖
          + ‖fderiv ℝ (fun y => fderiv ℝ a y (0, 1)) q (0, 1)‖ := norm_sub_le _ _
      _ = |k| * ‖fderiv ℝ b q (0, 1)‖
          + ‖fderiv ℝ (fun y => fderiv ℝ a y (0, 1)) q (0, 1)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |k| * (E / k ^ 2) + E / k ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hBZ q) hk0.le) (hAA q)
      _ = (|k| + 1) * E / k ^ 2 := by ring
  -- sup bound on the Green convolution `ψ = G_k * h₂`
  have hpsi : ∀ x, ‖nzConv k (nzmsH2 k a b) x‖ ≤ (|k| + 1) * E / k ^ 2 / k ^ 2 :=
    fun x => greenSup k hk _ _ hGc hGb x
  -- `∂_η ψ = G_k * ∂_η h₂`, bounded the same way
  have hdeta : ∀ x, ‖dEta2 (nzConv k (nzmsH2 k a b)) x‖ ≤ (|k| + 1) * E / k ^ 2 / k ^ 2 := by
    intro x
    have hcomm : fderiv ℝ (nzConv k (nzmsH2 k a b)) x (0, 1)
        = nzConv k (fun q => fderiv ℝ (nzmsH2 k a b) q (0, 1)) x :=
      nzConvFderiv_of nzConvGenHyp_proof k hk (nzmsH2 k a b) hG hGcs x
    show ‖fderiv ℝ (nzConv k (nzmsH2 k a b)) x (0, 1)‖ ≤ _
    rw [hcomm]
    exact greenSup k hk _ _ hH hHb x
  -- assemble the two components
  have hv : ‖Complex.I * ((k : ℂ) * nzConv k (nzmsH2 k a b) x)‖
      = |k| * ‖nzConv k (nzmsH2 k a b) x‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hu : ‖-dEta2 (nzConv k (nzmsH2 k a b)) x‖ = ‖dEta2 (nzConv k (nzmsH2 k a b)) x‖ :=
    norm_neg _
  calc ‖(!₂[-dEta2 (nzConv k (nzmsH2 k a b)) x,
        Complex.I * ((k : ℂ) * nzConv k (nzmsH2 k a b) x)] : MeridC)‖
      ≤ ‖-dEta2 (nzConv k (nzmsH2 k a b)) x‖
        + ‖Complex.I * ((k : ℂ) * nzConv k (nzmsH2 k a b) x)‖ :=
          lmb_norm_two _ _
    _ = ‖dEta2 (nzConv k (nzmsH2 k a b)) x‖ + |k| * ‖nzConv k (nzmsH2 k a b) x‖ := by
          rw [hu, hv]
    _ ≤ (|k| + 1) * E / k ^ 2 / k ^ 2
        + |k| * ((|k| + 1) * E / k ^ 2 / k ^ 2) :=
          add_le_add (hdeta x) (mul_le_mul_of_nonneg_left (hpsi x) hk0.le)
    _ = (|k| + 1) ^ 2 * E / k ^ 4 := by
          field_simp
          ring

/-- The final real-number comparison: for `n ≠ 0`, `(|k|+1)² E/k⁴ ≤ C E/(1+n²)` with `k = k_n`. -/
theorem lmb_final (c : ℝ) (hc : 0 < c) (n : ℤ) (hn : n ≠ 0) (E : ℝ) (hE : 0 ≤ E) :
    (|nzk c n| + 1) ^ 2 * E / nzk c n ^ 4
      ≤ E * (1 + c / (2 * Real.pi)) ^ 2 * (c ^ 2 / (2 * Real.pi ^ 2)) / (1 + (n : ℝ) ^ 2) := by
  have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by
    have h := Int.one_le_abs hn
    exact_mod_cast h
  have hk2 : nzk c n ^ 2 = 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 / c ^ 2 := by
    unfold nzk
    field_simp
    ring
  -- |k| ≥ 2π/c
  have habs : |nzk c n| = 2 * Real.pi * |(n : ℝ)| / c := by
    unfold nzk
    rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hc]
  have hKc : 2 * Real.pi ≤ |nzk c n| * c := by
    rw [habs, div_mul_cancel₀ _ hc.ne']
    nlinarith [Real.pi_pos]
  have hk0 : nzk c n ≠ 0 := by
    intro h
    rw [h, abs_zero, zero_mul] at hKc
    linarith [Real.pi_pos]
  have hK2 : |nzk c n| ^ 2 = nzk c n ^ 2 := sq_abs _
  set K := |nzk c n| with hKdef
  set k := nzk c n with hkdef
  set p := c / (2 * Real.pi) with hpdef
  have hK0 : 0 ≤ K := abs_nonneg _
  have hp : 0 < p := div_pos hc (by positivity)
  -- Step A
  have h1 : 1 ≤ K * p := by
    have e : K * p = K * c / (2 * Real.pi) := by rw [hpdef]; ring
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have h2 : K + 1 ≤ K * (1 + p) := by nlinarith
  have hA : (K + 1) ^ 2 / k ^ 4 ≤ (1 + p) ^ 2 * (1 / k ^ 2) := by
    have hk4 : (0 : ℝ) < k ^ 4 := by positivity
    rw [div_le_iff₀ hk4]
    have e : (1 + p) ^ 2 * (1 / k ^ 2) * k ^ 4 = (1 + p) ^ 2 * k ^ 2 := by
      field_simp
    rw [e, ← hK2]
    nlinarith [mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ K + 1) h2, sq_nonneg (K + 1)]
  -- Step B
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ)]
  have hX : c ^ 2 / (2 * Real.pi ^ 2) * k ^ 2 = 2 * (n : ℝ) ^ 2 := by
    rw [hk2]
    field_simp
    ring
  have hB : 1 / k ^ 2 ≤ (c ^ 2 / (2 * Real.pi ^ 2)) / (1 + (n : ℝ) ^ 2) := by
    have hk2pos : (0 : ℝ) < k ^ 2 := by positivity
    rw [div_le_div_iff₀ hk2pos (by positivity)]
    nlinarith [hX]
  have hfin : (K + 1) ^ 2 / k ^ 4
      ≤ (1 + p) ^ 2 * ((c ^ 2 / (2 * Real.pi ^ 2)) / (1 + (n : ℝ) ^ 2)) :=
    le_trans hA (mul_le_mul_of_nonneg_left hB (by positivity))
  calc (K + 1) ^ 2 * E / k ^ 4 = E * ((K + 1) ^ 2 / k ^ 4) := by ring
    _ ≤ E * ((1 + p) ^ 2 * ((c ^ 2 / (2 * Real.pi ^ 2)) / (1 + (n : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hfin hE
    _ = E * (1 + p) ^ 2 * (c ^ 2 / (2 * Real.pi ^ 2)) / (1 + (n : ℝ) ^ 2) := by ring

theorem lerayModeBound : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray.LerayModeBound := by
  intro c hc f hf
  obtain ⟨D, hD⟩ := modeDataBounds c hc f hf
  obtain ⟨s0, s1, L, hs0, hb⟩ := coefSmoothBand c hc f hf
  refine ⟨|D| * (1 + c / (2 * Real.pi)) ^ 2 * (c ^ 2 / (2 * Real.pi ^ 2)), fun n x => ?_⟩
  by_cases hn : n = 0
  · subst hn
    have h0 : lerayMode c f 0 x = 0 := by
      unfold lerayMode
      rw [if_pos rfl]
    rw [h0, norm_zero]
    exact div_nonneg (by positivity) (by positivity)
  · have hl : lerayMode c f n x
        = (!₂[-dEta2 (nzConv (nzk c n) (nzmsH2 (nzk c n) (coefR c f n) (coefZ c f n))) x,
            Complex.I * ((nzk c n : ℂ) *
              nzConv (nzk c n) (nzmsH2 (nzk c n) (coefR c f n) (coefZ c f n)) x)] : MeridC) := by
      unfold lerayMode psiN
      rw [if_neg hn]
    rw [hl]
    have hk : nzk c n ≠ 0 := mdb_nzk_ne hc hn
    have hGcs : HasCompactSupport (nzmsH2 (nzk c n) (coefR c f n) (coefZ c f n)) :=
      (nzmsH2_band (hb n).2.2.1 (hb n).2.2.2).hasCompactSupport
    have hcore := lmb_core (nzk c n) hk (|D|) (coefR c f n) (coefZ c f n)
      (hb n).1 (hb n).2.1 hGcs
      (fun y => le_trans ((hD n hn y).1) (div_le_div_of_nonneg_right (le_abs_self D) (sq_nonneg _)))
      (fun y => le_trans ((hD n hn y).2.1) (div_le_div_of_nonneg_right (le_abs_self D) (sq_nonneg _)))
      (fun y => le_trans ((hD n hn y).2.2.1) (div_le_div_of_nonneg_right (le_abs_self D) (sq_nonneg _)))
      (fun y => le_trans ((hD n hn y).2.2.2) (div_le_div_of_nonneg_right (le_abs_self D) (sq_nonneg _)))
      x
    exact le_trans hcore (lmb_final c hc n hn (|D|) (abs_nonneg D))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
