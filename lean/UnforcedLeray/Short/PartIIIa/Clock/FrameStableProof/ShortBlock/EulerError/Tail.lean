import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b_4
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad.Curl
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F1

/-!
# Gaussian lattice tails and kernel bounds (helper for `PartIII-a:T21/c3/3/3`)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2888
("the rescaled train differs from the periodized Gaussian by `C e^{-b θ/e_c}`", "the source tail
... the separated far kernel costs `O(d⁻¹)` ... the observation outside `d/8` is
Gaussian-small").

* `tail_gauss`, `tail_gauss'`: the periodization error `P_d L - L` of a profile with
  `|L(z)| ≤ C e^{-|z|²/8}` is `≤ C' d⁻² e^{-|y|²/16}` on the cell (both summation conventions).
* `jb_sq_exp_le`, `integrable_gauss`, `one_add_mul_exp_le`, `exp_neg_le_inv`: Gaussian facts.
* `cellKer_bound`: for `jb² |G| ≤ M` on the cell, `∫_cell G(w) K_d(y - w) dw` converges and is
  `≤ C_K M` (near/far split of `K_d`, `kerNearFar`).
* `kerVelPlanarCx_eq`, `integrable_kernel_planar`, `norm_biotSavart_le`: the planar Biot-Savart
  velocity as an integral over `ℝ × ℝ`, its integrand, and its uniform bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace EulerErrorTail

/-! ## 1. Lattice sums -/

/-- `S = ∑_{n ∈ ℤ} (1 + |n|)^{-2}`. -/
def sZ : ℝ := ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ))

theorem summable_sZ : Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
  Gaussian.summable_one_add_abs_int_rpow (by norm_num)

theorem sZ_nonneg : 0 ≤ sZ :=
  tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _

theorem norm_tsum_sub_zero_le {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {g : ℤ → E} {A : ℝ} (hg : Summable g) (hA : 0 ≤ A)
    (hb : ∀ n : ℤ, n ≠ 0 → ‖g n‖ ≤ A * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :
    ‖(∑' n, g n) - g 0‖ ≤ A * sZ := by
  classical
  have h2 : HasSum (fun n => g n - (if n = 0 then g 0 else 0)) ((∑' n, g n) - g 0) :=
    hg.hasSum.sub (hasSum_ite_eq 0 (g 0))
  refine h2.norm_le_of_bounded (summable_sZ.hasSum.mul_left A) fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp only [ite_true, sub_self, norm_zero]
    exact mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  · simp only [hn, ite_false, sub_zero]
    exact hb n hn

/-! ## 2. Gaussian facts -/

theorem one_le_abs_int {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ |(n : ℝ)| := by
  rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn

/-- For `|t| ≤ d/2` and `n ≠ 0`: `t²/2 + n²d²/8 ≤ (t + n d)²`. -/
theorem shift_sq_ge {d t : ℝ} (hd : 0 ≤ d) (ht : |t| ≤ d / 2) {n : ℤ} (hn : n ≠ 0) :
    t ^ 2 / 2 + (n : ℝ) ^ 2 * d ^ 2 / 8 ≤ (t + n * d) ^ 2 := by
  have hn1 := one_le_abs_int hn
  have ha0 : 0 ≤ |t| := abs_nonneg t
  have hb2a : 2 * |t| ≤ |(n : ℝ)| * d := by nlinarith
  have hrev : |(n : ℝ)| * d - |t| ≤ |t + n * d| := by
    have h1 := abs_sub_abs_le_abs_sub ((n : ℝ) * d) (-t)
    rw [abs_neg, sub_neg_eq_add, abs_mul, abs_of_nonneg hd, add_comm] at h1
    exact h1
  have hba : 0 ≤ |(n : ℝ)| * d - |t| := by linarith
  have hsq : (|(n : ℝ)| * d - |t|) ^ 2 ≤ (t + n * d) ^ 2 := by
    rw [← sq_abs (t + n * d)]; exact pow_le_pow_left₀ hba hrev 2
  have hb2 : (|(n : ℝ)| * d) ^ 2 = (n : ℝ) ^ 2 * d ^ 2 := by rw [mul_pow, sq_abs]
  have ha2 : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [mul_nonneg (by linarith : 0 ≤ 7 * (|(n : ℝ)| * d) - 2 * |t|)
    (by linarith : 0 ≤ |(n : ℝ)| * d - 2 * |t|)]

theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hx (by linarith [Real.add_one_le_exp x])

theorem exp_shift_le {d : ℝ} (hd : 1 ≤ d) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-((n : ℝ) ^ 2 * d ^ 2 / 64)) ≤ 256 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
  have hn1 := one_le_abs_int hn
  have hd0 : 0 < d := by linarith
  have hn2 : 0 < (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
  have hx : 0 < (n : ℝ) ^ 2 * d ^ 2 / 64 := by positivity
  have h1 := exp_neg_le_inv hx
  have hrp : (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) = 1 / (1 + |(n : ℝ)|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  rw [hrp]
  have hsq : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
  have h64 : 1 / ((n : ℝ) ^ 2 * d ^ 2 / 64) = 64 / ((n : ℝ) ^ 2 * d ^ 2) := by
    field_simp
  rw [h64] at h1
  refine h1.trans ?_
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (mul_pos hn2 (by positivity)) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 64 * d ^ 2)]

/-- **Gaussian lattice tail** (`perSum` convention). -/
theorem tail_gauss {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {L : ℝ × ℝ → E}
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8))
    {d : ℝ} (hd : 1 ≤ d) {y : ℝ × ℝ} (hy : |y.1| ≤ d / 2) :
    ‖(∑' n : ℤ, L (y.1 + n * d, y.2)) - L y‖ ≤
      256 * C * sZ / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
  have hd0 : 0 < d := by linarith
  have hs : Summable (fun n : ℤ => L (y.1 + n * d, y.2)) := by
    refine Summable.of_norm_bounded ((Gaussian.summable_translate (s := 2) (c := -d)
      (by norm_num) (neg_ne_zero.2 hd0.ne') y.1).mul_left (16 * C)) (fun n => ?_)
    have h1 := hL (y.1 + n * d, y.2)
    simp only at h1
    have h2 := perCont_exp_le_translate_weight (y.1 + n * d) y.2
    calc ‖L (y.1 + n * d, y.2)‖ ≤ C * Real.exp (-((y.1 + n * d) ^ 2 + y.2 ^ 2) / 8) := h1
      _ ≤ C * (16 * (1 + |y.1 + n * d|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left h2 hC
      _ = 16 * C * (1 + |y.1 - n * -d|) ^ (-(2 : ℝ)) := by
          rw [show y.1 - (n : ℝ) * -d = y.1 + n * d by ring]; ring
  set A : ℝ := 256 * C / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) with hA
  have hA0 : 0 ≤ A := by positivity
  have h := norm_tsum_sub_zero_le hs hA0 (fun n hn => by
    have h1 := hL (y.1 + n * d, y.2)
    simp only at h1
    have hsq := shift_sq_ge hd0.le hy hn
    have hexp : Real.exp (-((y.1 + n * d) ^ 2 + y.2 ^ 2) / 8) ≤
        Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) * Real.exp (-((n : ℝ) ^ 2 * d ^ 2 / 64)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg y.2]
    have hsh := exp_shift_le hd hn
    calc ‖L (y.1 + n * d, y.2)‖ ≤ C * Real.exp (-((y.1 + n * d) ^ 2 + y.2 ^ 2) / 8) := h1
      _ ≤ C * (Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) *
            Real.exp (-((n : ℝ) ^ 2 * d ^ 2 / 64))) := mul_le_mul_of_nonneg_left hexp hC
      _ ≤ C * (Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) *
            (256 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)))) := by gcongr
      _ = A * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by rw [hA]; ring)
  simp only [Int.cast_zero, zero_mul, add_zero, Prod.mk.eta] at h
  calc ‖(∑' n : ℤ, L (y.1 + n * d, y.2)) - L y‖ ≤ A * sZ := h
    _ = 256 * C * sZ / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by rw [hA]; ring

/-- **Gaussian lattice tail** (`Gaussian.periodize` convention). -/
theorem tail_gauss' {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {L : ℝ × ℝ → E}
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8))
    {d : ℝ} (hd : 1 ≤ d) {y : ℝ × ℝ} (hy : |y.1| ≤ d / 2) :
    ‖(∑' n : ℤ, L (y.1 - n * d, y.2)) - L y‖ ≤
      256 * C * sZ / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
  have heq : (∑' n : ℤ, L (y.1 - n * d, y.2)) = ∑' n : ℤ, L (y.1 + n * d, y.2) := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => L (y.1 + n * d, y.2))]
    congr 1
    funext n
    simp only [Equiv.neg_apply, Int.cast_neg, neg_mul, ← sub_eq_add_neg]
  rw [heq]
  exact tail_gauss hC hL hd hy

theorem abs_fst_le_of_mem_cell {d : ℝ} {x : ℝ × ℝ} (hx : x ∈ B0579.cell d) : |x.1| ≤ d / 2 := by
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hx
  rw [abs_le]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem jb_sq_exp_le (z : ℝ × ℝ) :
    B0579.jb z ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) ≤ 1024 := by
  set s := z.1 ^ 2 + z.2 ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hjb : B0579.jb z = 1 + s := by unfold B0579.jb; rw [hs]; ring
  have h1 : (1 + s) / 32 ≤ Real.exp (s / 32) := by linarith [Real.add_one_le_exp (s / 32)]
  have h2 : ((1 + s) / 32) ^ 2 ≤ Real.exp (s / 32) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : Real.exp (s / 32) ^ 2 = Real.exp (s / 16) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h4 : Real.exp (-s / 16) * Real.exp (s / 16) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [hjb]
  have hE : 0 < Real.exp (-s / 16) := Real.exp_pos _
  have h5 : (1 + s) ^ 2 ≤ 1024 * Real.exp (s / 16) := by nlinarith
  calc (1 + s) ^ 2 * Real.exp (-s / 16) ≤ (1024 * Real.exp (s / 16)) * Real.exp (-s / 16) :=
        mul_le_mul_of_nonneg_right h5 hE.le
    _ = 1024 := by rw [mul_assoc, mul_comm (Real.exp (s / 16)), h4, mul_one]

theorem integrable_gauss {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / a)) := by
  have h1 : Integrable (fun t : ℝ => Real.exp (-(1 / a) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  refine (h1.mul_prod h1).congr (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem one_add_mul_exp_le {r : ℝ} (hr : 0 ≤ r) : (1 + r) * Real.exp (-(r ^ 2) / 16) ≤ 4 := by
  have h1 : r ^ 2 / 16 + 1 ≤ Real.exp (r ^ 2 / 16) := Real.add_one_le_exp _
  have h2 : Real.exp (-(r ^ 2) / 16) * Real.exp (r ^ 2 / 16) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE := Real.exp_pos (-(r ^ 2) / 16)
  have h3 : 1 + r ≤ 4 * Real.exp (r ^ 2 / 16) := by nlinarith [sq_nonneg (r - 2)]
  calc (1 + r) * Real.exp (-(r ^ 2) / 16) ≤
        4 * Real.exp (r ^ 2 / 16) * Real.exp (-(r ^ 2) / 16) :=
        mul_le_mul_of_nonneg_right h3 hE.le
    _ = 4 := by rw [mul_assoc, mul_comm (Real.exp (r ^ 2 / 16)), h2, mul_one]

/-! ## 3. The cylinder kernel against `jb⁻²` sources -/

theorem lintegral_cell_le_of_jb_sq {d M : ℝ} (hM : 0 ≤ M) {G : ℝ × ℝ → ℂ}
    (hG : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖G w‖ ≤ M) :
    (∫⁻ w in B0579.cell d, ‖G w‖ₑ) ≤
      ENNReal.ofReal (M * ∫ z : ℝ × ℝ, B0579.jb z ^ (-(2 : ℝ))) := by
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  have hint : Integrable (fun z : ℝ × ℝ => M * B0579.jb z ^ (-(2 : ℝ))) :=
    Lam0B.integrable_jb_neg_two.const_mul M
  have hnn : ∀ z : ℝ × ℝ, 0 ≤ M * B0579.jb z ^ (-(2 : ℝ)) :=
    fun z => mul_nonneg hM (Real.rpow_nonneg (B0579.jb_pos z).le _)
  calc ∫⁻ w in B0579.cell d, ‖G w‖ₑ
      ≤ ∫⁻ w in B0579.cell d, ENNReal.ofReal (M * B0579.jb w ^ (-(2 : ℝ))) := by
        refine setLIntegral_mono' hmeas_cell (fun w hw => ?_)
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        have hjb_pos : 0 < B0579.jb w := B0579.jb_pos w
        rw [Real.rpow_neg hjb_pos.le, Real.rpow_two, ← div_eq_mul_inv,
          le_div_iff₀ (sq_pos_of_pos hjb_pos), mul_comm]
        exact hG w hw
    _ ≤ ∫⁻ w : ℝ × ℝ, ENNReal.ofReal (M * B0579.jb w ^ (-(2 : ℝ))) :=
        setLIntegral_le_lintegral (B0579.cell d) _
    _ = ENNReal.ofReal (∫ z : ℝ × ℝ, M * B0579.jb z ^ (-(2 : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm
    _ = ENNReal.ofReal (M * ∫ z : ℝ × ℝ, B0579.jb z ^ (-(2 : ℝ))) := by
        rw [integral_const_mul]

/-- **Cylinder kernel bound**: for `jb² |G| ≤ M` on the cell, the cell integral
`∫_cell G(w) K_d(y - w)_l dw` converges and has norm `≤ C_K M`, uniformly in `d ≥ 1` and `y`. -/
theorem cellKer_bound :
    ∃ C_K : ℝ, 0 ≤ C_K ∧
      ∀ {d M : ℝ}, 1 ≤ d → 0 ≤ M →
      ∀ {G : ℝ × ℝ → ℂ},
        AEStronglyMeasurable G (volume.restrict (B0579.cell d)) →
        (∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖G w‖ ≤ M) →
        ∀ (y : ℝ × ℝ) (l : Fin 2),
          IntegrableOn (fun w => G w * ((kerD d (y - w) l : ℝ) : ℂ)) (B0579.cell d) ∧
          ‖∫ w in B0579.cell d, G w * ((kerD d (y - w) l : ℝ) : ℂ)‖ ≤ C_K * M := by
  obtain ⟨C_NF, hCNF_pos, hNF⟩ := kerNearFar
  set I_jb : ℝ := ∫ z : ℝ × ℝ, B0579.jb z ^ (-(2 : ℝ))
  have hIjb_pos : 0 ≤ I_jb :=
    integral_nonneg (fun z => Real.rpow_nonneg (B0579.jb_pos z).le _)
  set C_K : ℝ := C_NF * (1 + I_jb)
  refine ⟨C_K, by positivity, fun {d M} hd hM {G} hGm hG_bd y l => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  obtain ⟨hK_meas, hK_per, _, hK_near, hK_far⟩ := hNF d hd
  have hcell_eq : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  have hmeas_ball : MeasurableSet (Metric.ball (0 : ℝ × ℝ) 1) := Metric.isOpen_ball.measurableSet
  set near : Set (ℝ × ℝ) := B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1
  set far : Set (ℝ × ℝ) := B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1
  have hmeas_near : MeasurableSet near := hmeas_cell.inter hmeas_ball
  have hmeas_far : MeasurableSet far := hmeas_cell.diff hmeas_ball
  set p : ℝ × ℝ → ℝ × ℝ := fun z => (toIcoMod hd0 (-(d / 2)) z.1, z.2)
  set Gp : ℝ × ℝ → ℂ := fun z => G (p z)
  have hp_mem : ∀ z : ℝ × ℝ, p z ∈ B0579.cell d := by
    intro z
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, p]
    have hm := toIcoMod_mem_Ico hd0 (-(d / 2)) z.1
    refine ⟨by linarith [hm.1, neg_div d 2], by linarith [hm.2, neg_div d 2]⟩
  have hp_id : ∀ w ∈ B0579.cell d, p w = w := by
    intro w hw
    have hw1 : -(d / 2) ≤ w.1 ∧ w.1 < -(d / 2) + d := by
      refine ⟨by linarith [hw.1.1, neg_div d 2], by linarith [hw.1.2, neg_div d 2]⟩
    ext
    · exact (toIcoMod_eq_self hd0).2 hw1
    · rfl
  have hGp_sup : ∀ z : ℝ × ℝ, ‖Gp z‖ ≤ M := by
    intro z
    have hz := hG_bd (p z) (hp_mem z)
    have hjb1 : 1 ≤ B0579.jb (p z) ^ 2 := one_le_pow₀ (Lam0B.jb_ge_one (p z))
    exact (le_mul_of_one_le_left (norm_nonneg _) hjb1).trans hz
  have hGp_int : (∫⁻ w in B0579.cell d, ‖Gp w‖ₑ) ≤ ENNReal.ofReal (M * I_jb) := by
    have heq : ∫⁻ w in B0579.cell d, ‖Gp w‖ₑ = ∫⁻ w in B0579.cell d, ‖G w‖ₑ := by
      refine setLIntegral_congr_fun hmeas_cell (fun w hw => ?_)
      dsimp [Gp]
      rw [hp_id w hw]
    rw [heq]
    exact lintegral_cell_le_of_jb_sq hM hG_bd
  have hH_per : UnforcedLeray.Cyl.IsPeriodic d
      (fun z : ℝ × ℝ => ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) := by
    intro z
    dsimp only [Gp, p]
    have hadd1 : (y - z).1 = (y - (z.1 + d, z.2)).1 + d := by dsimp; ring
    have hmod : toIcoMod hd0 (-(d / 2)) (y - (z.1 + d, z.2)).1 =
        toIcoMod hd0 (-(d / 2)) (y - z).1 := by
      rw [hadd1, toIcoMod_add_right]
    have hsub2 : (y - (z.1 + d, z.2)).2 = (y - z).2 := rfl
    rw [hmod, hsub2, hK_per z l]
  have hconv_eq :
      (∫⁻ w in B0579.cell d, ‖G w * ((kerD d (y - w) l : ℝ) : ℂ)‖ₑ) =
      (∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) := by
    have hcongr : (∫⁻ w in B0579.cell d, ‖G w * ((kerD d (y - w) l : ℝ) : ℂ)‖ₑ) =
        (∫⁻ w in B0579.cell d, ‖Gp (y - (y - w))‖ₑ * ‖kerD d (y - w) l‖ₑ) := by
      refine setLIntegral_congr_fun hmeas_cell (fun w hw => ?_)
      have hker : ‖((kerD d (y - w) l : ℝ) : ℂ)‖ₑ = ‖kerD d (y - w) l‖ₑ := by
        rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
      rw [enorm_mul, sub_sub_cancel, hker]
      dsimp [Gp]
      rw [hp_id w hw]
    rw [hcongr, hcell_eq]
    exact UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hH_per y
  have hnear_le :
      (∫⁻ z in near, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) ≤ ENNReal.ofReal (C_NF * M) := by
    calc ∫⁻ z in near, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ
        ≤ ∫⁻ z in near, ENNReal.ofReal M * ‖kerD d z l‖ₑ := by
          refine setLIntegral_mono' hmeas_near (fun z _ => ?_)
          have hle : ‖Gp (y - z)‖ₑ ≤ ENNReal.ofReal M := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hGp_sup (y - z))
          gcongr
      _ = ENNReal.ofReal M * ∫⁻ z in near, ‖kerD d z l‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M * ∫⁻ z in near, ∑ j', ‖kerD d z j'‖ₑ := by
          gcongr with z
          exact Finset.single_le_sum (f := fun j' => ‖kerD d z j'‖ₑ)
            (fun _ _ => bot_le) (Finset.mem_univ l)
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal C_NF := by gcongr
      _ = ENNReal.ofReal (C_NF * M) := by rw [← ENNReal.ofReal_mul hM, mul_comm]
  have hfar_le :
      (∫⁻ z in far, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) ≤ ENNReal.ofReal (C_NF * (M * I_jb)) := by
    have hGp_per : UnforcedLeray.Cyl.IsPeriodic d (fun w : ℝ × ℝ => ‖Gp w‖ₑ) := by
      intro w
      dsimp only [Gp, p]
      rw [toIcoMod_add_right]
    have hshift : (∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ) =
        (∫⁻ w in B0579.cell d, ‖Gp w‖ₑ) := by
      rw [hcell_eq]
      exact UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hGp_per y
    calc ∫⁻ z in far, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ
        ≤ ∫⁻ z in far, ‖Gp (y - z)‖ₑ * ENNReal.ofReal C_NF := by
          refine setLIntegral_mono' hmeas_far (fun z hz => ?_)
          have hle : ‖kerD d z l‖ₑ ≤ ENNReal.ofReal C_NF := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hK_far z hz.1 hz.2 l)
          gcongr
      _ ≤ ∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ * ENNReal.ofReal C_NF :=
          lintegral_mono_set sdiff_subset
      _ = (∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ) * ENNReal.ofReal C_NF :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = (∫⁻ w in B0579.cell d, ‖Gp w‖ₑ) * ENNReal.ofReal C_NF := by rw [hshift]
      _ ≤ ENNReal.ofReal (M * I_jb) * ENNReal.ofReal C_NF := by gcongr
      _ = ENNReal.ofReal (C_NF * (M * I_jb)) := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  have htot_le :
      (∫⁻ w in B0579.cell d, ‖G w * ((kerD d (y - w) l : ℝ) : ℂ)‖ₑ) ≤
        ENNReal.ofReal (C_K * M) := by
    calc ∫⁻ w in B0579.cell d, ‖G w * ((kerD d (y - w) l : ℝ) : ℂ)‖ₑ
        = ∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ := hconv_eq
      _ = (∫⁻ z in near, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) +
            (∫⁻ z in far, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) := by
          rw [← lintegral_inter_add_sdiff _ (B0579.cell d) hmeas_ball]
      _ ≤ ENNReal.ofReal (C_NF * M) + ENNReal.ofReal (C_NF * (M * I_jb)) :=
          add_le_add hnear_le hfar_le
      _ = ENNReal.ofReal (C_K * M) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp [C_K]
          ring
  have hker_sm : AEStronglyMeasurable (fun w : ℝ × ℝ => ((kerD d (y - w) l : ℝ) : ℂ))
      (volume.restrict (B0579.cell d)) :=
    (Complex.continuous_ofReal.measurable.comp
      ((hK_meas l).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hint : IntegrableOn (fun w => G w * ((kerD d (y - w) l : ℝ) : ℂ)) (B0579.cell d) :=
    ⟨hGm.mul hker_sm, lt_of_le_of_lt htot_le ENNReal.ofReal_lt_top⟩
  have hnorm_le : ‖∫ w in B0579.cell d, G w * ((kerD d (y - w) l : ℝ) : ℂ)‖ ≤ C_K * M := by
    have h1 : ‖∫ w in B0579.cell d, G w * ((kerD d (y - w) l : ℝ) : ℂ)‖ₑ ≤
        ENNReal.ofReal (C_K * M) :=
      (enorm_integral_le_lintegral_enorm _).trans htot_le
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  exact ⟨hint, hnorm_le⟩

/-! ## 4. The planar Biot-Savart velocity -/

theorem planarBSKernel_apply (w : ℝ × ℝ) (k : Fin 2) :
    (IIb.planarBSKernel w k : ℝ) = (B0009.kernel k (planeToC w)).re := by
  fin_cases k <;> rfl

theorem kernel_planeToC_eq (w : ℝ × ℝ) (k : Fin 2) :
    B0009.kernel k (planeToC w) = ((IIb.planarBSKernel w k : ℝ) : ℂ) := by
  rw [planarBSKernel_apply]
  unfold B0009.kernel
  rw [Complex.ofReal_re]

theorem planeToC_sub (x y : ℝ × ℝ) : planeToC (x - y) = planeToC x - planeToC y :=
  Complex.ext (by simp [planeToC]) (by simp [planeToC])

theorem integral_planeToC (g : ℂ → ℂ) :
    ∫ x : ℝ × ℝ, g (planeToC x) = ∫ z : ℂ, g z :=
  (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding g

/-- The planar velocity as an integral over `ℝ × ℝ`. -/
theorem kerVelPlanarCx_eq (e : ℝ × ℝ → ℂ) (y : ℝ × ℝ) (k : Fin 2) :
    kerVelPlanarCx e y k = ∫ z : ℝ × ℝ, B0009.kernel k (planeToC (y - z)) * e z := by
  unfold kerVelPlanarCx
  rw [B0009.biotSavart_apply,
    ← integral_planeToC (fun z => B0009.kernel k (planeToC y - z) * e (B0009.toPlane z))]
  congr 1

theorem integrable_toPlane {e : ℝ × ℝ → ℂ} (hi : Integrable e) :
    Integrable (fun w : ℂ => e (B0009.toPlane w)) :=
  (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding).2 hi

theorem integrable_kernel_planar {e : ℝ × ℝ → ℂ} (hc : Continuous e) {K : ℝ}
    (hK : ∀ z, ‖e z‖ ≤ K) (hi : Integrable e) (k : Fin 2) (y : ℝ × ℝ) :
    Integrable (fun z : ℝ × ℝ => B0009.kernel k (planeToC (y - z)) * e z) := by
  have hc' : Continuous (fun w : ℂ => e (B0009.toPlane w)) :=
    hc.comp (Complex.continuous_re.prodMk Complex.continuous_im)
  have h1 := PartI.BiotSavartCurlAux.integrable_conv_kernel (i := k) (planeToC y) hc'
    (fun w => hK _) (integrable_toPlane hi)
  have h2 := (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding).2 h1
  refine h2.congr (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  rw [planeToC_sub]
  rfl

/-- **Uniform bound of the planar Biot-Savart velocity**. -/
theorem norm_biotSavart_le {f : ℂ → ℂ} (hc : Continuous f) {K : ℝ} (hK : ∀ z, ‖f z‖ ≤ K)
    (hi : Integrable f) (i : Fin 2) (Y : ℂ) :
    ‖B0009.biotSavart f i Y‖ ≤
      K * (∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel i t‖) +
        (2 * Real.pi)⁻¹ * ∫ t, ‖f t‖ := by
  rw [B0009.biotSavart_apply]
  set F : ℂ → ℂ := fun t => B0009.kernel i t * f (Y - t) with hFdef
  have hF : (fun z => B0009.kernel i (Y - z) * f z) = fun z => F (Y - z) := by
    funext z; simp only [hFdef, sub_sub_cancel]
  rw [hF, integral_sub_left_eq_self F volume Y]
  have hfY : Integrable (fun t => f (Y - t)) := hi.comp_sub_left Y
  have hFi : Integrable F :=
    PartI.BiotSavartCurlAux.integrable_kernel_mul (hc.comp (continuous_const.sub continuous_id))
      (fun t => hK _) hfY
  refine (norm_integral_le_integral_norm F).trans ?_
  have hB : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  rw [← integral_add_compl hB hFi.norm]
  have h1 : ∫ t in Metric.ball (0 : ℂ) 1, ‖F t‖ ≤
      ∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel i t‖ * K := by
    refine setIntegral_mono_on hFi.norm.integrableOn
      ((B0009.integrableOn_kernel_ball i).norm.mul_const K) hB (fun t _ => ?_)
    rw [hFdef, norm_mul]
    exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
  have h2 : ∫ t in (Metric.ball (0 : ℂ) 1)ᶜ, ‖F t‖ ≤
      ∫ t in (Metric.ball (0 : ℂ) 1)ᶜ, (2 * Real.pi)⁻¹ * ‖f (Y - t)‖ := by
    refine setIntegral_mono_on hFi.norm.integrableOn (hfY.norm.const_mul _).integrableOn
      hB.compl (fun t ht => ?_)
    rw [hFdef, norm_mul]
    exact mul_le_mul_of_nonneg_right (B0009.norm_kernel_le_of_notMem_ball i ht) (norm_nonneg _)
  have h3 : ∫ t in (Metric.ball (0 : ℂ) 1)ᶜ, (2 * Real.pi)⁻¹ * ‖f (Y - t)‖ ≤
      ∫ t, (2 * Real.pi)⁻¹ * ‖f (Y - t)‖ :=
    setIntegral_le_integral (hfY.norm.const_mul _)
      (Eventually.of_forall fun t => by positivity)
  have h4 : ∫ t, (2 * Real.pi)⁻¹ * ‖f (Y - t)‖ = (2 * Real.pi)⁻¹ * ∫ t, ‖f t‖ := by
    rw [integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self (fun t => ‖f t‖) volume Y
  have h5 : ∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel i t‖ * K =
      K * ∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel i t‖ := by
    rw [integral_mul_const, mul_comm]
  linarith

end EulerErrorTail

end UnforcedLeray.Short.IIIa
