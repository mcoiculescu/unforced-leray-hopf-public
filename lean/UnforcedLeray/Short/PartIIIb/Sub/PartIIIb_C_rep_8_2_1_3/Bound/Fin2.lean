import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Fin1

/-!
# The nine entries of the ring-chart Hessian table against the flat Hessian
(`PartIII-b:C/rep/8/2/1/3/b`, helper 8)

Source lines 5460-5465, 5036-5045.  At `p = φ(z)`, `z = (σ, (q, η))`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIIb.Concrete.RingChartRawD2Sub

/-- The jet quantity `J₂ ṽ + J₃ ψ̃`. -/
def Mz (L : ReturnLevel) (z : Zc) : ℝ := J 2 (trainFv L) z + J 3 (trainFpsi L) z

theorem Mz_nonneg (L : ReturnLevel) (z : Zc) : 0 ≤ Mz L z := by
  unfold Mz
  have := J_nonneg 2 (trainFv L) z
  have := J_nonneg 3 (trainFpsi L) z
  linarith

theorem hJ2h (L : ReturnLevel) (z : Zc) :
    J 2 (hTil L) z ≤ 7 * (1 + |z.2.2|) * J 3 (trainFpsi L) z :=
  (J_hTil L 2 z).trans (J_rawH L (by norm_num) z)

theorem hJ1b (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    J 1 (rawPhi L) z ≤ 7 * (1 + |z.2.2|) * Mz L z := by
  have a := J_rawPhi L h1 1 z
  have b := J_rawH L (n := 1) (by norm_num) z
  have c := J_mono (show 1 ≤ 2 by norm_num) (trainFv L) z
  have d := J_mono (show 2 ≤ 3 by norm_num) (trainFpsi L) z
  have hω : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  have e1 := J_nonneg 2 (trainFv L) z
  have e2 := J_nonneg 3 (trainFpsi L) z
  unfold Mz
  nlinarith [mul_le_mul_of_nonneg_left d (by positivity : (0:ℝ) ≤ 7 * (1 + |z.2.2|))]

theorem fb_P (L : ReturnLevel) (h1 : L.ε ≤ 1) (m : ℝ) (hm : |m| ≤ 2) (z : Zc) :
    ‖Pm L.ε m (rawPhi L) z‖ ≤ 49 * (1 + |z.2.2|) ^ 2 * Mz L z := by
  have a := norm_le_J 0 (Pm L.ε m (rawPhi L)) z
  have b := J_Pm L.ε_pos.le h1 hm (n := 0) (by norm_num) (contDiff_rawPhi L) z
  have c := hJ1b L h1 z
  have hω : 0 ≤ 1 + |z.2.2| := by positivity
  have := mul_le_mul_of_nonneg_left c (by positivity : (0:ℝ) ≤ 7 * (1 + |z.2.2|))
  norm_num at b this ⊢
  nlinarith

theorem fb_Z (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖Zo (rawPhi L) z‖ ≤ 7 * (1 + |z.2.2|) * Mz L z := by
  have a := norm_le_J 0 (Zo (rawPhi L)) z
  have b := J_Zo (n := 0) (contDiff_rawPhi L) z
  have c := hJ1b L h1 z
  norm_num at b ⊢
  linarith

theorem Pm_step (ε : ℝ) (F : Zc → Merid) (z : Zc) :
    Pm ε 2 F z = Pm ε 1 F z - ε • F z := by
  unfold Pm Gop
  module

theorem comp_le (m : Merid) (i : Fin 2) : |m i| ≤ ‖m‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le m i

/-! ### Numerics -/

theorem num1 {w ε a c d : ℝ} (hw : 1 ≤ w) (hε : 0 ≤ ε) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hd : d ≤ 7 * w * c) :
    ε * (49 * w ^ 2 + 7 * w) * a + ε * (49 * w ^ 2) * d ≤ 343 * ε * w ^ 3 * (a + c) := by
  have h2 : w ^ 2 ≤ w ^ 3 := pow_le_pow_right₀ hw (by norm_num)
  have h1 : w ≤ w ^ 3 := by nlinarith
  have hw0 : 0 ≤ w := by linarith
  have e1 : ε * (49 * w ^ 2) * d ≤ ε * (49 * w ^ 2) * (7 * w * c) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have e2 : ε * (49 * w ^ 2 + 7 * w) * a ≤ ε * (343 * w ^ 3) * a := by
    apply mul_le_mul_of_nonneg_right _ ha
    apply mul_le_mul_of_nonneg_left _ hε
    nlinarith
  nlinarith [mul_nonneg hε hc, mul_nonneg hε ha, pow_nonneg hw0 3]

theorem num2 {w ε a c d : ℝ} (hw : 1 ≤ w) (hε : 0 ≤ ε) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hd : d ≤ 7 * w * c) :
    ε * (7 * w) * a + ε * (7 * w) * d ≤ 343 * ε * w ^ 3 * (a + c) := by
  have h2 : w ^ 2 ≤ w ^ 3 := pow_le_pow_right₀ hw (by norm_num)
  have h1 : w ≤ w ^ 2 := by nlinarith
  have hw0 : 0 ≤ w := by linarith
  have e1 : ε * (7 * w) * d ≤ ε * (7 * w) * (7 * w * c) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  nlinarith [mul_nonneg hε hc, mul_nonneg hε ha, pow_nonneg hw0 3, mul_nonneg hε hw0,
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hε ha), mul_le_mul_of_nonneg_left h2 (mul_nonneg hε ha),
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hε hc)]

theorem num3 {w ε a c d : ℝ} (hw : 1 ≤ w) (hε : 0 ≤ ε) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hd : d ≤ 7 * w * c) :
    ε * d ≤ 343 * ε * w ^ 3 * (a + c) := by
  have h2 : w ^ 2 ≤ w ^ 3 := pow_le_pow_right₀ hw (by norm_num)
  have h1 : w ≤ w ^ 2 := by nlinarith
  have hw0 : 0 ≤ w := by linarith
  have e1 : ε * d ≤ ε * (7 * w * c) := mul_le_mul_of_nonneg_left hd hε
  nlinarith [mul_nonneg hε hc, mul_nonneg hε ha, pow_nonneg hw0 3,
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hε hc), mul_le_mul_of_nonneg_left h2 (mul_nonneg hε hc)]

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
