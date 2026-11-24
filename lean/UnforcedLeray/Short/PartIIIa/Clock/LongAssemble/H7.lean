import UnforcedLeray.Short.PartIIIa.Clock.Moving

/-!
# Part III-a long assembly, H7: ENNReal algebra for the final constant

Pure algebra: the chain `‖W(s)‖ ≤ ‖compl(s)‖ + k·amplNorm(s)`, the normalisation by `N`, the
Gronwall output and the bounds at the initial age combine to `‖W(s)‖ ≤ C N ‖W(t)‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma algebra_step (k g N Ws Ys As aS ρS At Yt Wt : ℝ≥0∞) (hW1 : Ws ≤ Ys + k * As)
    (hYs : Ys = ρS * N) (hAs : As = aS * N) (hAt : At ≤ 2 * (k * Wt))
    (hYt : Yt ≤ Wt + k * At) (hG : aS + ρS ≤ g * (At + Yt)) :
    Ws ≤ (1 + k) * (g * ((1 + 2 * k + 2 * k * k) * Wt)) * N := by
  have hsum : At + Yt ≤ (1 + 2 * k + 2 * k * k) * Wt := by
    calc At + Yt ≤ 2 * (k * Wt) + (Wt + k * (2 * (k * Wt))) :=
          add_le_add hAt (hYt.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hAt zero_le)))
      _ = (1 + 2 * k + 2 * k * k) * Wt := by ring
  have hgt : aS + ρS ≤ g * ((1 + 2 * k + 2 * k * k) * Wt) :=
    hG.trans (mul_le_mul_of_nonneg_left hsum zero_le)
  have h1 : ρS + k * aS ≤ (1 + k) * (aS + ρS) := by
    have e : (1 + k) * (aS + ρS) = (aS + ρS) + k * (aS + ρS) := by ring
    rw [e]
    exact add_le_add le_add_self (mul_le_mul_of_nonneg_left le_self_add zero_le)
  calc Ws ≤ Ys + k * As := hW1
    _ = (ρS + k * aS) * N := by rw [hYs, hAs]; ring
    _ ≤ ((1 + k) * (aS + ρS)) * N := mul_le_mul_of_nonneg_right h1 zero_le
    _ ≤ ((1 + k) * (g * ((1 + 2 * k + 2 * k * k) * Wt))) * N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgt zero_le) zero_le

lemma ofReal_cout (Kp Gp x : ℝ) (hK : 0 ≤ Kp) (hG : 0 ≤ Gp) (hx : 0 ≤ x) :
    ENNReal.ofReal ((1 + Kp) * Gp * (1 + 2 * Kp + 2 * Kp * Kp) * x) =
      (1 + ENNReal.ofReal Kp) * ENNReal.ofReal Gp *
        (1 + 2 * ENNReal.ofReal Kp + 2 * ENNReal.ofReal Kp * ENNReal.ofReal Kp) *
          ENNReal.ofReal x := by
  have h1 : ENNReal.ofReal (1 + Kp) = 1 + ENNReal.ofReal Kp := by
    rw [ENNReal.ofReal_add zero_le_one hK, ENNReal.ofReal_one]
  have h2 : ENNReal.ofReal (1 + 2 * Kp + 2 * Kp * Kp) =
      1 + 2 * ENNReal.ofReal Kp + 2 * ENNReal.ofReal Kp * ENNReal.ofReal Kp := by
    have e2 : ENNReal.ofReal (2 * Kp) = 2 * ENNReal.ofReal Kp := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have e3 : ENNReal.ofReal (2 * Kp * Kp) = 2 * ENNReal.ofReal Kp * ENNReal.ofReal Kp := by
      rw [ENNReal.ofReal_mul (by positivity), e2]
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add zero_le_one (by positivity),
      ENNReal.ofReal_one, e2, e3]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), h1, h2]

end UnforcedLeray.Short.IIIa
