import UnforcedLeray.Short.PartIIa.Sub.N02_4_7_B
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Commute
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Decay
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Band
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.IntegrableWeight
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.WeightedEnergy
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.EtaMul
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.EtaModeEq
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.J0

/-!
# Part II-a, task `PartII-a:N02/4/7/9`: the `j = 1` moment bound `NzmbJ1`

Source: `the November 2 reference manuscript`, lines 1722-1727.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem j1_norm_mul (t : ℝ) (z : ℂ) : ‖(t : ℂ) * z‖ ^ 2 = t ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem j1_sub_sq (u v : ℂ) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  nlinarith [norm_sub_le u v, norm_nonneg (u - v), norm_nonneg u, norm_nonneg v,
    sq_nonneg (‖u‖ - ‖v‖)]

theorem j1_add_sq (u v : ℂ) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  nlinarith [norm_add_le u v, norm_nonneg (u + v), norm_nonneg u, norm_nonneg v,
    sq_nonneg (‖u‖ - ‖v‖)]

theorem j1_sq_le (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  nlinarith

theorem j1_ae_pos : ∀ᵐ x ∂(volume.restrict (Ioi 0 ×ˢ univ) : Measure (ℝ × ℝ)), 0 < x.1 := by
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with x hx
  exact hx.1

theorem j1_sq (j α : ℕ) (g : ℝ × ℝ → ℂ) :
    (nzMom2 j α g) ^ 2 = ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
      (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
  have hnn : 0 ≤ ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
      (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
    apply setIntegral_nonneg (measurableSet_Ioi.prod MeasurableSet.univ)
    intro x hx
    have h1 : 0 < x.1 := hx.1
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg h1.le _)
  have key : ∀ y : ℝ, 0 ≤ y → (y ^ (1 / 2 : ℝ)) ^ 2 = y := by
    intro y hy
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  unfold nzMom2
  exact key _ hnn

theorem j1_const_sq (k : ℝ) (j α : ℕ) (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    (nzMom2 j α (fun x => (k : ℂ) * φ x)) ^ 2 = k ^ 2 * (nzMom2 j α φ) ^ 2 := by
  rw [j1_sq, j1_sq, j0_iter_const (k : ℂ) α φ hφ, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [j1_norm_mul]
  ring

theorem j1_t_exp (κ u : ℝ) (hκ : 0 < κ) (hu : 0 ≤ u) :
    u * Real.exp (-κ * u) ≤ (2 / κ) * Real.exp (-(κ / 2) * u) := by
  have hc : 0 < κ / 2 := half_pos hκ
  have hp : 0 < Real.exp (-(κ / 2) * u) := Real.exp_pos _
  have hpq : Real.exp (-(κ / 2) * u) * Real.exp ((κ / 2) * u) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  have hq : 1 + (κ / 2) * u ≤ Real.exp ((κ / 2) * u) := by
    have := Real.add_one_le_exp ((κ / 2) * u)
    linarith
  have key : (κ / 2) * u * Real.exp (-(κ / 2) * u) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hq hp.le]
  have hup : u * Real.exp (-(κ / 2) * u) ≤ 2 / κ := by
    rw [le_div_iff₀ hκ]
    nlinarith
  have hexp : Real.exp (-κ * u) = Real.exp (-(κ / 2) * u) * Real.exp (-(κ / 2) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc u * (Real.exp (-(κ / 2) * u) * Real.exp (-(κ / 2) * u))
      = (u * Real.exp (-(κ / 2) * u)) * Real.exp (-(κ / 2) * u) := by ring
    _ ≤ (2 / κ) * Real.exp (-(κ / 2) * u) := mul_le_mul_of_nonneg_right hup hp.le

theorem j1_eta_dec (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (κ C : ℝ) (hκ : 0 < κ)
    (hd : ∀ x : ℝ × ℝ, ‖H x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ H x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|)) :
    ∃ κ' C' : ℝ, 0 < κ' ∧ ∀ x : ℝ × ℝ,
      ‖(x.2 : ℂ) * H x‖ ≤ C' * Real.exp (-κ' * |x.2|) ∧
      ‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * H y) x (0, 1)‖ ≤ C' * Real.exp (-κ' * |x.2|) := by
  have hC0 : 0 ≤ |C| := abs_nonneg C
  refine ⟨κ / 2, (2 / κ + 1) * |C|, half_pos hκ, fun x => ?_⟩
  have hEE : Real.exp (-κ * |x.2|) ≤ Real.exp (-(κ / 2) * |x.2|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg x.2]
  have hE'pos : 0 ≤ Real.exp (-(κ / 2) * |x.2|) := (Real.exp_pos _).le
  have hHn : ‖H x‖ ≤ |C| * Real.exp (-κ * |x.2|) :=
    (hd x).1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have hHd : ‖fderiv ℝ H x (0, 1)‖ ≤ |C| * Real.exp (-κ * |x.2|) :=
    (hd x).2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have hmul : ∀ z : ℂ, ‖z‖ ≤ |C| * Real.exp (-κ * |x.2|) →
      ‖(x.2 : ℂ) * z‖ ≤ |C| * ((2 / κ) * Real.exp (-(κ / 2) * |x.2|)) := by
    intro z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |x.2| * ‖z‖ ≤ |x.2| * (|C| * Real.exp (-κ * |x.2|)) :=
          mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = |C| * (|x.2| * Real.exp (-κ * |x.2|)) := by ring
      _ ≤ |C| * ((2 / κ) * Real.exp (-(κ / 2) * |x.2|)) :=
          mul_le_mul_of_nonneg_left (j1_t_exp κ |x.2| hκ (abs_nonneg _)) hC0
  have hfac : |C| * ((2 / κ) * Real.exp (-(κ / 2) * |x.2|)) + |C| * Real.exp (-(κ / 2) * |x.2|)
      ≤ (2 / κ + 1) * |C| * Real.exp (-(κ / 2) * |x.2|) := le_of_eq (by ring)
  constructor
  · calc ‖(x.2 : ℂ) * H x‖ ≤ |C| * ((2 / κ) * Real.exp (-(κ / 2) * |x.2|)) := hmul _ hHn
      _ ≤ (2 / κ + 1) * |C| * Real.exp (-(κ / 2) * |x.2|) := by
          nlinarith [mul_nonneg hC0 hE'pos]
  · rw [(nzmbEtaMul H hH x).1]
    calc ‖(x.2 : ℂ) * fderiv ℝ H x (0, 1) + H x‖
        ≤ ‖(x.2 : ℂ) * fderiv ℝ H x (0, 1)‖ + ‖H x‖ := norm_add_le _ _
      _ ≤ |C| * ((2 / κ) * Real.exp (-(κ / 2) * |x.2|)) + |C| * Real.exp (-(κ / 2) * |x.2|) :=
          add_le_add (hmul _ hHd) (hHn.trans (mul_le_mul_of_nonneg_left hEE hC0))
      _ ≤ (2 / κ + 1) * |C| * Real.exp (-(κ / 2) * |x.2|) := hfac

theorem j1_eta_contDiff (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => (y.2 : ℂ) * H y) :=
  (Complex.ofRealCLM.contDiff.comp contDiff_snd).mul hH

theorem j1_eta_deriv_ptw (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (x : ℝ × ℝ) :
    (|x.2| ^ 1) ^ 2 * ‖fderiv ℝ H x (0, 1)‖ ^ 2 ≤
      2 * ‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * H y) x (0, 1)‖ ^ 2 +
        2 * ((|x.2| ^ 0) ^ 2 * ‖H x‖ ^ 2) := by
  rw [(nzmbEtaMul H hH x).1]
  have h := j1_sub_sq ((x.2 : ℂ) * fderiv ℝ H x (0, 1) + H x) (H x)
  rw [add_sub_cancel_right, j1_norm_mul] at h
  have e : (|x.2| ^ 1) ^ 2 = x.2 ^ 2 := by simp [sq_abs]
  have e0 : (|x.2| ^ 0) ^ 2 = 1 := by simp
  rw [e, e0, one_mul]
  linarith

/-- The weighted integrand of the `j = 1` data bound, as a real function. -/
def j1Up (α : ℕ) (a b φ ψ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℝ :=
  2 * ((|x.2| ^ 1) ^ 2 * ‖(nzS2^[α] a) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) +
  2 * ((|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] ψ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) +
  2 * ((|x.2| ^ 1) ^ 2 * ‖(nzS2^[α] b) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) +
  2 * ((|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] φ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))

theorem j1_int4 (f1 f2 f3 f4 : ℝ × ℝ → ℝ) (h1 : Integrable f1 (volume.restrict (Ioi 0 ×ˢ univ)))
    (h2 : Integrable f2 (volume.restrict (Ioi 0 ×ˢ univ)))
    (h3 : Integrable f3 (volume.restrict (Ioi 0 ×ˢ univ)))
    (h4 : Integrable f4 (volume.restrict (Ioi 0 ×ˢ univ))) :
    ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (2 * f1 x + 2 * f2 x + 2 * f3 x + 2 * f4 x) =
      2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, f1 x) + 2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, f2 x) +
        2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, f3 x) + 2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, f4 x) := by
  have i1 : Integrable (fun x => 2 * f1 x) (volume.restrict (Ioi 0 ×ˢ univ)) := h1.const_mul 2
  have i2 : Integrable (fun x => 2 * f2 x) (volume.restrict (Ioi 0 ×ˢ univ)) := h2.const_mul 2
  have i3 : Integrable (fun x => 2 * f3 x) (volume.restrict (Ioi 0 ×ˢ univ)) := h3.const_mul 2
  have i4 : Integrable (fun x => 2 * f4 x) (volume.restrict (Ioi 0 ×ˢ univ)) := h4.const_mul 2
  have i12 : Integrable (fun x => 2 * f1 x + 2 * f2 x) (volume.restrict (Ioi 0 ×ˢ univ)) :=
    i1.add i2
  have i123 : Integrable (fun x => 2 * f1 x + 2 * f2 x + 2 * f3 x)
      (volume.restrict (Ioi 0 ×ˢ univ)) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]


theorem j1_energy (k : ℝ) (A B G1 G2 : ℝ × ℝ → ℂ) (U : ℝ × ℝ → ℝ)
    (hG1 : ContDiff ℝ ∞ G1) (hG2 : ContDiff ℝ ∞ G2) (hAB : NzModeEq k A B G1 G2)
    (s0 s1 κ C : ℝ) (hs0 : 0 < s0) (hκ : 0 < κ)
    (hb1 : ∀ x, G1 x ≠ 0 → x.1 ∈ Icc s0 s1) (hb2 : ∀ x, G2 x ≠ 0 → x.1 ∈ Icc s0 s1)
    (hdec : ∀ x : ℝ × ℝ, ‖G1 x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ G1 x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖G2 x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ G2 x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|))
    (hU : Integrable U (volume.restrict (Ioi 0 ×ˢ univ)))
    (hUp : ∀ x : ℝ × ℝ, 0 < x.1 →
      (‖A x‖ ^ 2 + ‖B x‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) ≤ U x) :
    k ^ 2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ≤
        ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, U x ∧
    (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ≤
        ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, U x ∧
    k ^ 2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ≤
        ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, U x ∧
    (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖fderiv ℝ G2 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ≤
        ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, U x := by
  have hEn := nzmbWeightedEnergy k A B G1 G2 hG1 hG2 hAB
    ⟨s0, s1, hs0, fun x hx => hx.elim (hb1 x) (hb2 x)⟩ ⟨κ, C, hκ, hdec⟩
  have i1 : Integrable (fun x : ℝ × ℝ => ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int G1 hG1 s0 s1 κ C hs0 hκ hb1 (fun x => (hdec x).1)
  have i2 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int (fun x => fderiv ℝ G1 x (0, 1)) (nzmb_contDiff_snd G1 hG1 (0, 1)) s0 s1 κ C hs0 hκ
      (j0_deriv_band G1 s0 s1 hb1) (fun x => (hdec x).2.1)
  have i3 : Integrable (fun x : ℝ × ℝ => ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int G2 hG2 s0 s1 κ C hs0 hκ hb2 (fun x => (hdec x).2.2.1)
  have i4 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ G2 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int (fun x => fderiv ℝ G2 x (0, 1)) (nzmb_contDiff_snd G2 hG2 (0, 1)) s0 s1 κ C hs0 hκ
      (j0_deriv_band G2 s0 s1 hb2) (fun x => (hdec x).2.2.2)
  have iF : Integrable (fun x : ℝ × ℝ => (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
      k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) := by
    have e := (((i1.const_mul (k ^ 2)).add i2).add (i3.const_mul (k ^ 2))).add i4
    refine e.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hw : ∀ᵐ x ∂(volume.restrict (Ioi 0 ×ˢ univ) : Measure (ℝ × ℝ)), 0 < x.1 := j1_ae_pos
  have hR : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (‖A x‖ ^ 2 + ‖B x‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, U x := by
    refine integral_mono_of_nonneg ?_ hU ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact hUp x hx
  have E1' : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, k ^ 2 * ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
        k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine integral_mono_of_nonneg ?_ iF ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact (j0_pt (k ^ 2 * ‖G1 x‖ ^ 2) (‖fderiv ℝ G1 x (0, 1)‖ ^ 2) (k ^ 2 * ‖G2 x‖ ^ 2)
        (‖fderiv ℝ G2 x (0, 1)‖ ^ 2) (x.1 ^ (-(3 / 2 : ℝ)))
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (Real.rpow_nonneg hx.le _)).1
  have E2' : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
        k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine integral_mono_of_nonneg ?_ iF ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact (j0_pt (k ^ 2 * ‖G1 x‖ ^ 2) (‖fderiv ℝ G1 x (0, 1)‖ ^ 2) (k ^ 2 * ‖G2 x‖ ^ 2)
        (‖fderiv ℝ G2 x (0, 1)‖ ^ 2) (x.1 ^ (-(3 / 2 : ℝ)))
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (Real.rpow_nonneg hx.le _)).2.1
  have E3' : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, k ^ 2 * ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
        k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine integral_mono_of_nonneg ?_ iF ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact (j0_pt (k ^ 2 * ‖G1 x‖ ^ 2) (‖fderiv ℝ G1 x (0, 1)‖ ^ 2) (k ^ 2 * ‖G2 x‖ ^ 2)
        (‖fderiv ℝ G2 x (0, 1)‖ ^ 2) (x.1 ^ (-(3 / 2 : ℝ)))
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (Real.rpow_nonneg hx.le _)).2.2.1
  have E4' : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖fderiv ℝ G2 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
        k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine integral_mono_of_nonneg ?_ iF ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact (j0_pt (k ^ 2 * ‖G1 x‖ ^ 2) (‖fderiv ℝ G1 x (0, 1)‖ ^ 2) (k ^ 2 * ‖G2 x‖ ^ 2)
        (‖fderiv ℝ G2 x (0, 1)‖ ^ 2) (x.1 ^ (-(3 / 2 : ℝ)))
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (Real.rpow_nonneg hx.le _)).2.2.2
  have q1 : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, k ^ 2 * ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) =
      k ^ 2 * ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have q3 : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, k ^ 2 * ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) =
      k ^ 2 * ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← q1]; linarith
  · linarith
  · rw [← q3]; linarith
  · linarith


theorem j1_arith (t c S X P u u' mk : ℝ) (ht : 0 ≤ t) (hc : c = 1 + t) (hS : 0 ≤ S)
    (hX0 : 0 ≤ X) (hXS : X ≤ S) (hP0 : 0 ≤ P) (hPS : P ≤ c * S)
    (hu : u ≤ t * (2 * X + 2 * P)) (hu' : u' ≤ 2 * X + 4 * P) (hmk : mk ≤ 2 * X + 2 * P) :
    u ≤ 6 * c ^ 2 * S ∧ u' ≤ 6 * c ^ 2 * S ∧ mk ≤ 6 * c ^ 2 * S := by
  have hc1 : 1 ≤ c := by linarith
  have htc : t ≤ c := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hcS : c * S ≤ c ^ 2 * S := by nlinarith
  have hc2S : 0 ≤ c ^ 2 * S := by positivity
  have hS1 : S ≤ c ^ 2 * S := by nlinarith
  have h1 : t * (2 * X + 2 * P) ≤ c * (2 * S + 2 * (c * S)) := by
    apply mul_le_mul htc _ (by linarith) hc0
    linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

theorem j1_real (k : ℝ) (hk : k ≠ 0) (m0a m0b m1a m1b p q u v u' v' mk mk' I : ℝ)
    (h0a : 0 ≤ m0a) (h0b : 0 ≤ m0b) (h1a : 0 ≤ m1a) (h1b : 0 ≤ m1b)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hpP : p ≤ (1 + |k|⁻¹) * (m0a + m0b)) (hqP : q ≤ (1 + |k|⁻¹) * (m0a + m0b))
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu'0 : 0 ≤ u') (hv'0 : 0 ≤ v')
    (hmk0 : 0 ≤ mk) (hmk0' : 0 ≤ mk')
    (hI : I = 2 * m1a ^ 2 + 2 * q ^ 2 + 2 * m1b ^ 2 + 2 * p ^ 2)
    (hu : k ^ 2 * u ^ 2 ≤ I) (hv : k ^ 2 * v ^ 2 ≤ I)
    (hu' : u' ^ 2 ≤ 2 * I + 2 * p ^ 2) (hv' : v' ^ 2 ≤ 2 * I + 2 * q ^ 2)
    (hmk : mk ^ 2 ≤ I) (hmk' : mk' ^ 2 ≤ I) :
    u ≤ 6 * (1 + |k|⁻¹) ^ 2 * (m0a + m0b + (m1a + m1b)) ∧
    v ≤ 6 * (1 + |k|⁻¹) ^ 2 * (m0a + m0b + (m1a + m1b)) ∧
    u' ≤ 6 * (1 + |k|⁻¹) ^ 2 * (m0a + m0b + (m1a + m1b)) ∧
    v' ≤ 6 * (1 + |k|⁻¹) ^ 2 * (m0a + m0b + (m1a + m1b)) ∧
    mk ≤ 6 * (1 + |k|⁻¹) ^ 2 * (m0a + m0b + (m1a + m1b)) ∧
    mk' ≤ 6 * (1 + |k|⁻¹) ^ 2 * (m0a + m0b + (m1a + m1b)) := by
  have hk0 : 0 < |k| := abs_pos.mpr hk
  have ht0 : 0 ≤ |k|⁻¹ := inv_nonneg.mpr hk0.le
  have hX0 : 0 ≤ m1a + m1b := by linarith
  have hS0 : 0 ≤ m0a + m0b + (m1a + m1b) := by linarith
  have hXS : m1a + m1b ≤ m0a + m0b + (m1a + m1b) := by linarith
  have hP0 : 0 ≤ (1 + |k|⁻¹) * (m0a + m0b) := mul_nonneg (by linarith) (by linarith)
  have hPS : (1 + |k|⁻¹) * (m0a + m0b) ≤ (1 + |k|⁻¹) * (m0a + m0b + (m1a + m1b)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  generalize hPd : (1 + |k|⁻¹) * (m0a + m0b) = P at hpP hqP hP0 hPS
  have hq2 : q ^ 2 ≤ P ^ 2 := by
    rw [sq, sq]; exact mul_le_mul hqP hqP hq0 (hq0.trans hqP)
  have hp2 : p ^ 2 ≤ P ^ 2 := by
    rw [sq, sq]; exact mul_le_mul hpP hpP hp0 (hp0.trans hpP)
  have hX2 : m1a ^ 2 + m1b ^ 2 ≤ (m1a + m1b) ^ 2 := by
    have e : (m1a + m1b) ^ 2 = m1a ^ 2 + m1b ^ 2 + 2 * (m1a * m1b) := by ring
    rw [e]; linarith [mul_nonneg h1a h1b]
  have hXP : 0 ≤ (m1a + m1b) * P := mul_nonneg hX0 hP0
  have hXX : 0 ≤ (m1a + m1b) ^ 2 := sq_nonneg _
  have hPP : 0 ≤ P ^ 2 := sq_nonneg _
  have e2 : (2 * (m1a + m1b) + 2 * P) ^ 2
      = 4 * (m1a + m1b) ^ 2 + 8 * ((m1a + m1b) * P) + 4 * P ^ 2 := by ring
  have e4 : (2 * (m1a + m1b) + 4 * P) ^ 2
      = 4 * (m1a + m1b) ^ 2 + 16 * ((m1a + m1b) * P) + 16 * P ^ 2 := by ring
  have hIle : I ≤ 2 * (m1a + m1b) ^ 2 + 4 * P ^ 2 := by linarith
  have hI2 : I ≤ (2 * (m1a + m1b) + 2 * P) ^ 2 := by rw [e2]; linarith
  have hu'2 : u' ^ 2 ≤ (2 * (m1a + m1b) + 4 * P) ^ 2 := by rw [e4]; linarith
  have hv'2 : v' ^ 2 ≤ (2 * (m1a + m1b) + 4 * P) ^ 2 := by rw [e4]; linarith
  have hu_s : |k| * u ≤ 2 * (m1a + m1b) + 2 * P := by
    apply j1_sq_le _ _ (mul_nonneg hk0.le hu0) (by linarith)
    rw [mul_pow, sq_abs]
    linarith
  have hv_s : |k| * v ≤ 2 * (m1a + m1b) + 2 * P := by
    apply j1_sq_le _ _ (mul_nonneg hk0.le hv0) (by linarith)
    rw [mul_pow, sq_abs]
    linarith
  have hu_t : u ≤ |k|⁻¹ * (2 * (m1a + m1b) + 2 * P) := by
    calc u = |k|⁻¹ * (|k| * u) := by rw [← mul_assoc, inv_mul_cancel₀ hk0.ne', one_mul]
      _ ≤ |k|⁻¹ * (2 * (m1a + m1b) + 2 * P) := mul_le_mul_of_nonneg_left hu_s ht0
  have hv_t : v ≤ |k|⁻¹ * (2 * (m1a + m1b) + 2 * P) := by
    calc v = |k|⁻¹ * (|k| * v) := by rw [← mul_assoc, inv_mul_cancel₀ hk0.ne', one_mul]
      _ ≤ |k|⁻¹ * (2 * (m1a + m1b) + 2 * P) := mul_le_mul_of_nonneg_left hv_s ht0
  have hu'_l : u' ≤ 2 * (m1a + m1b) + 4 * P :=
    j1_sq_le _ _ hu'0 (by linarith) hu'2
  have hv'_l : v' ≤ 2 * (m1a + m1b) + 4 * P :=
    j1_sq_le _ _ hv'0 (by linarith) hv'2
  have hmk_l : mk ≤ 2 * (m1a + m1b) + 2 * P :=
    j1_sq_le _ _ hmk0 (by linarith) (hmk.trans hI2)
  have hmk'_l : mk' ≤ 2 * (m1a + m1b) + 2 * P :=
    j1_sq_le _ _ hmk0' (by linarith) (hmk'.trans hI2)
  obtain ⟨A1, A2, A3⟩ := j1_arith |k|⁻¹ (1 + |k|⁻¹) (m0a + m0b + (m1a + m1b)) (m1a + m1b)
    P u u' mk ht0 rfl hS0 hX0 hXS hP0 hPS hu_t hu'_l hmk_l
  obtain ⟨B1, B2, B3⟩ := j1_arith |k|⁻¹ (1 + |k|⁻¹) (m0a + m0b + (m1a + m1b)) (m1a + m1b)
    P v v' mk' ht0 rfl hS0 hX0 hXS hP0 hPS hv_t hv'_l hmk'_l
  exact ⟨A1, B1, A2, B2, A3, B3⟩


theorem nzmbJ1 : UnforcedLeray.Short.PartIIa.NzmbJ1 := by
  refine ⟨6, by norm_num, ?_⟩
  intro k hk a b φ ψ ha hb hBa hBb hφ hψ hE α hα g hg
  have hα2 : α < 2 := Finset.mem_range.mp hα
  have hφs : ContDiff ℝ ∞ φ := hφ.1
  have hψs : ContDiff ℝ ∞ ψ := hψ.1
  have J0 := nzmbJ0 k hk a b φ ψ ha hb hBa hBb hφ hψ hE α hα
  have hJφ := J0 φ (by simp)
  have hJψ := J0 ψ (by simp)
  have hAB := nzmb_modeEq_iter k α a b φ ψ ha hb hφs hψs hE
  have hEta := nzmbEtaModeEq k _ _ _ _ (nzmb_iter_contDiff α φ hφs)
    (nzmb_iter_contDiff α ψ hψs) hAB
  obtain ⟨s0φ, s1φ, hs0φ, hbφ⟩ := hφ.2.1
  obtain ⟨s0ψ, s1ψ, hs0ψ, hbψ⟩ := hψ.2.1
  obtain ⟨s0, s1, hs0, hb1, hb2⟩ : ∃ s0 s1 : ℝ, 0 < s0 ∧ (∀ x, φ x ≠ 0 → x.1 ∈ Icc s0 s1) ∧
      (∀ x, ψ x ≠ 0 → x.1 ∈ Icc s0 s1) :=
    ⟨min s0φ s0ψ, max s1φ s1ψ, lt_min hs0φ hs0ψ,
      j0_weaken hbφ (min_le_left _ _) (le_max_left _ _),
      j0_weaken hbψ (min_le_right _ _) (le_max_right _ _)⟩
  obtain ⟨κ1, C1, hκ1, hd1⟩ := j0_decay_S φ hφ s0 s1 hb1 α hα2
  obtain ⟨κ2, C2, hκ2, hd2⟩ := j0_decay_S ψ hψ s0 s1 hb2 α hα2
  obtain ⟨κ1', C1', hκ1', hG1d⟩ :=
    j1_eta_dec (nzS2^[α] φ) (nzmb_iter_contDiff α φ hφs) κ1 C1 hκ1 hd1
  obtain ⟨κ2', C2', hκ2', hG2d⟩ :=
    j1_eta_dec (nzS2^[α] ψ) (nzmb_iter_contDiff α ψ hψs) κ2 C2 hκ2 hd2
  obtain ⟨κ, C, hκ, hdec⟩ := j0_pair (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] φ) y)
    (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] ψ) y) κ1' C1' κ2' C2' hκ1' hκ2'
    (fun x => ⟨(hG1d x).1, (hG1d x).2⟩) (fun x => ⟨(hG2d x).1, (hG2d x).2⟩)
  have hG1 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] φ) y) :=
    j1_eta_contDiff _ (nzmb_iter_contDiff α φ hφs)
  have hG2 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] ψ) y) :=
    j1_eta_contDiff _ (nzmb_iter_contDiff α ψ hψs)
  have hb1G : ∀ x : ℝ × ℝ, (x.2 : ℂ) * (nzS2^[α] φ) x ≠ 0 → x.1 ∈ Icc s0 s1 := by
    intro x hx
    apply j0_iter_band φ s0 s1 hb1 α x
    intro h0
    apply hx
    rw [h0, mul_zero]
  have hb2G : ∀ x : ℝ × ℝ, (x.2 : ℂ) * (nzS2^[α] ψ) x ≠ 0 → x.1 ∈ Icc s0 s1 := by
    intro x hx
    apply j0_iter_band ψ s0 s1 hb2 α x
    intro h0
    apply hx
    rw [h0, mul_zero]
  -- integrability of the weighted pieces
  have iA : Integrable (fun x : ℝ × ℝ => (|x.2| ^ 1) ^ 2 * ‖(nzS2^[α] a) x‖ ^ 2 *
      x.1 ^ (-(3 / 2 : ℝ))) (volume.restrict (Ioi 0 ×ˢ univ)) := by
    obtain ⟨sa0, sa1, κa, Ca, hsa0, hκa, hbA, hdA⟩ :=
      j0_data_decay (nzS2^[α] a) (nzmb_iter_contDiff α a ha) (j0_iter_NzBand2 α a ha hBa)
    exact nzmbIntegrableWeight _ (nzmb_iter_contDiff α a ha) sa0 sa1 κa Ca hsa0 hκa hbA hdA 1
  have iB : Integrable (fun x : ℝ × ℝ => (|x.2| ^ 1) ^ 2 * ‖(nzS2^[α] b) x‖ ^ 2 *
      x.1 ^ (-(3 / 2 : ℝ))) (volume.restrict (Ioi 0 ×ˢ univ)) := by
    obtain ⟨sb0, sb1, κb, Cb, hsb0, hκb, hbB, hdB⟩ :=
      j0_data_decay (nzS2^[α] b) (nzmb_iter_contDiff α b hb) (j0_iter_NzBand2 α b hb hBb)
    exact nzmbIntegrableWeight _ (nzmb_iter_contDiff α b hb) sb0 sb1 κb Cb hsb0 hκb hbB hdB 1
  have iφ0 : Integrable (fun x : ℝ × ℝ => (|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] φ) x‖ ^ 2 *
      x.1 ^ (-(3 / 2 : ℝ))) (volume.restrict (Ioi 0 ×ˢ univ)) :=
    nzmbIntegrableWeight _ (nzmb_iter_contDiff α φ hφs) s0 s1 κ1 C1 hs0 hκ1
      (j0_iter_band φ s0 s1 hb1 α) (fun x => (hd1 x).1) 0
  have iψ0 : Integrable (fun x : ℝ × ℝ => (|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] ψ) x‖ ^ 2 *
      x.1 ^ (-(3 / 2 : ℝ))) (volume.restrict (Ioi 0 ×ˢ univ)) :=
    nzmbIntegrableWeight _ (nzmb_iter_contDiff α ψ hψs) s0 s1 κ2 C2 hs0 hκ2
      (j0_iter_band ψ s0 s1 hb2 α) (fun x => (hd2 x).1) 0
  have hUpInt : Integrable (j1Up α a b φ ψ) (volume.restrict (Ioi 0 ×ˢ univ)) :=
    (((iA.const_mul 2).add (iψ0.const_mul 2)).add (iB.const_mul 2)).add (iφ0.const_mul 2)
  have hIval : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, j1Up α a b φ ψ x =
      2 * (nzMom2 1 α a) ^ 2 + 2 * (nzMom2 0 α ψ) ^ 2 + 2 * (nzMom2 1 α b) ^ 2 +
        2 * (nzMom2 0 α φ) ^ 2 := by
    unfold j1Up
    rw [j1_int4 _ _ _ _ iA iψ0 iB iφ0, j1_sq 1 α a, j1_sq 0 α ψ, j1_sq 1 α b, j1_sq 0 α φ]
  have hUp : ∀ x : ℝ × ℝ, 0 < x.1 →
      (‖(x.2 : ℂ) * (nzS2^[α] a) x - (nzS2^[α] ψ) x‖ ^ 2 +
        ‖(x.2 : ℂ) * (nzS2^[α] b) x + (nzS2^[α] φ) x‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) ≤
        j1Up α a b φ ψ x := by
    intro x hx
    have hw : 0 ≤ x.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
    have e1 := j1_sub_sq ((x.2 : ℂ) * (nzS2^[α] a) x) ((nzS2^[α] ψ) x)
    have e2 := j1_add_sq ((x.2 : ℂ) * (nzS2^[α] b) x) ((nzS2^[α] φ) x)
    have f1 : ‖(x.2 : ℂ) * (nzS2^[α] a) x‖ ^ 2 = (|x.2| ^ 1) ^ 2 * ‖(nzS2^[α] a) x‖ ^ 2 := by
      rw [j1_norm_mul]; simp [sq_abs]
    have f2 : ‖(x.2 : ℂ) * (nzS2^[α] b) x‖ ^ 2 = (|x.2| ^ 1) ^ 2 * ‖(nzS2^[α] b) x‖ ^ 2 := by
      rw [j1_norm_mul]; simp [sq_abs]
    have f3 : ‖(nzS2^[α] ψ) x‖ ^ 2 = (|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] ψ) x‖ ^ 2 := by simp
    have f4 : ‖(nzS2^[α] φ) x‖ ^ 2 = (|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] φ) x‖ ^ 2 := by simp
    have hsum := add_le_add e1 e2
    calc (‖(x.2 : ℂ) * (nzS2^[α] a) x - (nzS2^[α] ψ) x‖ ^ 2 +
          ‖(x.2 : ℂ) * (nzS2^[α] b) x + (nzS2^[α] φ) x‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ))
        ≤ ((2 * ‖(x.2 : ℂ) * (nzS2^[α] a) x‖ ^ 2 + 2 * ‖(nzS2^[α] ψ) x‖ ^ 2) +
            (2 * ‖(x.2 : ℂ) * (nzS2^[α] b) x‖ ^ 2 + 2 * ‖(nzS2^[α] φ) x‖ ^ 2)) *
            x.1 ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hsum hw
      _ = j1Up α a b φ ψ x := by
          rw [f1, f2, f3, f4]
          unfold j1Up
          ring
  have hEnergy := j1_energy k (fun x => (x.2 : ℂ) * (nzS2^[α] a) x - (nzS2^[α] ψ) x)
    (fun x => (x.2 : ℂ) * (nzS2^[α] b) x + (nzS2^[α] φ) x)
    (fun y => (y.2 : ℂ) * (nzS2^[α] φ) y) (fun y => (y.2 : ℂ) * (nzS2^[α] ψ) y)
    (j1Up α a b φ ψ) hG1 hG2 hEta s0 s1 κ C hs0 hκ hb1G hb2G hdec hUpInt hUp
  beta_reduce at hEnergy
  obtain ⟨EG1, EG1d, EG2, EG2d⟩ := hEnergy
  have hw := j1_ae_pos
  have iDG1 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] φ) y) x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int (fun x => fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] φ) y) x (0, 1))
      (nzmb_contDiff_snd _ hG1 (0, 1)) s0 s1 κ C hs0 hκ
      (j0_deriv_band (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] φ) y) s0 s1 hb1G)
      (fun x => (hdec x).2.1)
  have iDG2 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] ψ) y) x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int (fun x => fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] ψ) y) x (0, 1))
      (nzmb_contDiff_snd _ hG2 (0, 1)) s0 s1 κ C hs0 hκ
      (j0_deriv_band (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] ψ) y) s0 s1 hb2G)
      (fun x => (hdec x).2.2.2)
  have hG1sq : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖(x.2 : ℂ) * (nzS2^[α] φ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))
      = (nzMom2 1 α φ) ^ 2 := by
    rw [j1_sq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [j1_norm_mul]
    simp [sq_abs]
  have hG2sq : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖(x.2 : ℂ) * (nzS2^[α] ψ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))
      = (nzMom2 1 α ψ) ^ 2 := by
    rw [j1_sq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [j1_norm_mul]
    simp [sq_abs]
  have R1 : k ^ 2 * (nzMom2 1 α φ) ^ 2 ≤ ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, j1Up α a b φ ψ x := by
    rw [← hG1sq]; exact EG1
  have R2 : k ^ 2 * (nzMom2 1 α ψ) ^ 2 ≤ ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, j1Up α a b φ ψ x := by
    rw [← hG2sq]; exact EG2
  have hDφ : (nzMom2 1 α (fun x => fderiv ℝ φ x (0, 1))) ^ 2 ≤
      2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, j1Up α a b φ ψ x) + 2 * (nzMom2 0 α φ) ^ 2 := by
    rw [j1_sq 1 α (fun x => fderiv ℝ φ x (0, 1)), j0_iter_fderiv_fun α φ hφs, j1_sq 0 α φ]
    have hmono : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
        (|x.2| ^ 1) ^ 2 * ‖fderiv ℝ (nzS2^[α] φ) x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
        ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
          (2 * (‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] φ) y) x (0, 1)‖ ^ 2 *
              x.1 ^ (-(3 / 2 : ℝ))) +
            2 * ((|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] φ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))) := by
      refine integral_mono_of_nonneg ?_ ((iDG1.const_mul 2).add (iφ0.const_mul 2)) ?_
      · filter_upwards [hw] with x hx
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hx.le _)
      · filter_upwards [hw] with x hx
        exact le_trans (mul_le_mul_of_nonneg_right
          (j1_eta_deriv_ptw (nzS2^[α] φ) (nzmb_iter_contDiff α φ hφs) x)
          (Real.rpow_nonneg hx.le _)) (le_of_eq (by ring))
    have hint : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
          (2 * (‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] φ) y) x (0, 1)‖ ^ 2 *
              x.1 ^ (-(3 / 2 : ℝ))) +
            2 * ((|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] φ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))) =
        2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
            ‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] φ) y) x (0, 1)‖ ^ 2 *
              x.1 ^ (-(3 / 2 : ℝ))) +
        2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] φ) x‖ ^ 2 *
              x.1 ^ (-(3 / 2 : ℝ))) := by
      rw [integral_add (iDG1.const_mul 2) (iφ0.const_mul 2), integral_const_mul, integral_const_mul]
    linarith [hmono, hint, EG1d]
  have hDψ : (nzMom2 1 α (fun x => fderiv ℝ ψ x (0, 1))) ^ 2 ≤
      2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, j1Up α a b φ ψ x) + 2 * (nzMom2 0 α ψ) ^ 2 := by
    rw [j1_sq 1 α (fun x => fderiv ℝ ψ x (0, 1)), j0_iter_fderiv_fun α ψ hψs, j1_sq 0 α ψ]
    have hmono : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
        (|x.2| ^ 1) ^ 2 * ‖fderiv ℝ (nzS2^[α] ψ) x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
        ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
          (2 * (‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] ψ) y) x (0, 1)‖ ^ 2 *
              x.1 ^ (-(3 / 2 : ℝ))) +
            2 * ((|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] ψ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))) := by
      refine integral_mono_of_nonneg ?_ ((iDG2.const_mul 2).add (iψ0.const_mul 2)) ?_
      · filter_upwards [hw] with x hx
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hx.le _)
      · filter_upwards [hw] with x hx
        exact le_trans (mul_le_mul_of_nonneg_right
          (j1_eta_deriv_ptw (nzS2^[α] ψ) (nzmb_iter_contDiff α ψ hψs) x)
          (Real.rpow_nonneg hx.le _)) (le_of_eq (by ring))
    have hint : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
          (2 * (‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] ψ) y) x (0, 1)‖ ^ 2 *
              x.1 ^ (-(3 / 2 : ℝ))) +
            2 * ((|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] ψ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))) =
        2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
            ‖fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * (nzS2^[α] ψ) y) x (0, 1)‖ ^ 2 *
              x.1 ^ (-(3 / 2 : ℝ))) +
        2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (|x.2| ^ 0) ^ 2 * ‖(nzS2^[α] ψ) x‖ ^ 2 *
              x.1 ^ (-(3 / 2 : ℝ))) := by
      rw [integral_add (iDG2.const_mul 2) (iψ0.const_mul 2), integral_const_mul, integral_const_mul]
    linarith [hmono, hint, EG2d]
  have hmkφ : (nzMom2 1 α (fun x => (k : ℂ) * φ x)) ^ 2 ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, j1Up α a b φ ψ x := by
    rw [j1_const_sq k 1 α φ hφs]; exact R1
  have hmkψ : (nzMom2 1 α (fun x => (k : ℂ) * ψ x)) ^ 2 ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, j1Up α a b φ ψ x := by
    rw [j1_const_sq k 1 α ψ hψs]; exact R2
  have hmain := j1_real k hk (nzMom2 0 α a) (nzMom2 0 α b) (nzMom2 1 α a) (nzMom2 1 α b)
    (nzMom2 0 α φ) (nzMom2 0 α ψ) (nzMom2 1 α φ) (nzMom2 1 α ψ)
    (nzMom2 1 α (fun x => fderiv ℝ φ x (0, 1))) (nzMom2 1 α (fun x => fderiv ℝ ψ x (0, 1)))
    (nzMom2 1 α (fun x => (k : ℂ) * φ x)) (nzMom2 1 α (fun x => (k : ℂ) * ψ x))
    (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, j1Up α a b φ ψ x)
    (nzMom2_nonneg 0 α a) (nzMom2_nonneg 0 α b) (nzMom2_nonneg 1 α a) (nzMom2_nonneg 1 α b)
    (nzMom2_nonneg 0 α φ) (nzMom2_nonneg 0 α ψ) hJφ hJψ
    (nzMom2_nonneg 1 α φ) (nzMom2_nonneg 1 α ψ)
    (nzMom2_nonneg 1 α (fun x => fderiv ℝ φ x (0, 1)))
    (nzMom2_nonneg 1 α (fun x => fderiv ℝ ψ x (0, 1)))
    (nzMom2_nonneg 1 α (fun x => (k : ℂ) * φ x)) (nzMom2_nonneg 1 α (fun x => (k : ℂ) * ψ x))
    hIval R1 R2 hDφ hDψ hmkφ hmkψ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h | h | h | h <;> rw [h]
  · exact hmain.1
  · exact hmain.2.2.1
  · exact hmain.2.2.2.2.1
  · exact hmain.2.1
  · exact hmain.2.2.2.1
  · exact hmain.2.2.2.2.2

end UnforcedLeray.Short.PartIIa
