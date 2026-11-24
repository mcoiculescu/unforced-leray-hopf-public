import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCont

/-!
# Small-time estimate for the heat semigroup

For `g ∈ C¹` with `g` and `∇g` bounded in the weight, `|H_a g - g| ≤ C √a` (`a ≥ 0`), by the
Lipschitz bound `|g(x-√a w) - g(x)| ≤ 2B √a ‖w‖` and the first moment of the Gaussian.
Source: `the November 2 reference manuscript`, lines 2103-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

namespace STS

lemma lip {B : ℝ} {g : Pl → ℝ} (hg : ContDiff ℝ 1 g) (h0 : WB B (B0579.pd 0 g))
    (h1 : WB B (B0579.pd 1 g)) (y z : Pl) : |g y - g z| ≤ 2 * B * ‖y - z‖ := by
  have hb : ∀ (j : Fin 2) (p : Pl), |B0579.pd j g p| ≤ B := by
    intro j p
    have hh : WB B (B0579.pd j g) := by fin_cases j; exacts [h0, h1]
    have h := hh p
    have hc : 1 ≤ Real.cosh p.2 := Real.one_le_cosh _
    have h0' : 0 ≤ |B0579.pd j g p| := abs_nonneg _
    nlinarith [mul_nonneg h0' (sub_nonneg.2 hc)]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb 0 0)
  have hder : ∀ p : Pl, ‖fderiv ℝ g p‖ ≤ 2 * B := by
    intro p
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun v => ?_
    have hv : v = v.1 • B0579.dir 0 + v.2 • B0579.dir 1 := by
      ext <;> simp [B0579.dir]
    have hl : fderiv ℝ g p v = v.1 * B0579.pd 0 g p + v.2 * B0579.pd 1 g p := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul]
      simp [B0579.pd]
    rw [hl, Real.norm_eq_abs]
    have a1 : |v.1| ≤ ‖v‖ := by simpa using norm_fst_le v
    have a2 : |v.2| ≤ ‖v‖ := by simpa using norm_snd_le v
    calc |v.1 * B0579.pd 0 g p + v.2 * B0579.pd 1 g p|
        ≤ |v.1 * B0579.pd 0 g p| + |v.2 * B0579.pd 1 g p| := abs_add_le _ _
      _ = |v.1| * |B0579.pd 0 g p| + |v.2| * |B0579.pd 1 g p| := by rw [abs_mul, abs_mul]
      _ ≤ ‖v‖ * B + ‖v‖ * B := add_le_add
          (mul_le_mul a1 (hb 0 p) (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul a2 (hb 1 p) (abs_nonneg _) (norm_nonneg _))
      _ = 2 * B * ‖v‖ := by ring
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := g) (s := univ)
    (fun p _ => hg.differentiable one_ne_zero p) (fun p _ => hder p) convex_univ
    (mem_univ z) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

/-- Majorant of `K_1(w) ‖w‖`. -/
def G (w : Pl) : ℝ := 2 * (|heatKd 0 1 w| + |heatKd 1 1 w|) * Real.cosh w.2

lemma G_int : Integrable G := by
  obtain ⟨-, -, -, -, -, hd⟩ := heatKernelMoments 1 one_pos
  have a := (hd 0).1
  have b := (hd 1).1
  have := (a.add b).const_mul 2
  refine this.congr (ae_of_all _ fun w => ?_)
  simp only [G, Pi.add_apply]
  ring

lemma K_norm_le (w : Pl) : heatK 1 w * ‖w‖ ≤ G w := by
  have hK : 0 < heatK 1 w := by
    unfold heatK; positivity
  have h0 : |heatKd 0 1 w| = |w.1| / 2 * heatK 1 w := by
    simp only [heatKd, Matrix.cons_val_zero]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hK]
    norm_num
  have h1 : |heatKd 1 1 w| = |w.2| / 2 * heatK 1 w := by
    simp only [heatKd, Matrix.cons_val_one]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hK]
    norm_num
  have hn : ‖w‖ ≤ |w.1| + |w.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (by linarith [abs_nonneg w.2]) (by linarith [abs_nonneg w.1])
  have hc : 1 ≤ Real.cosh w.2 := Real.one_le_cosh _
  have hS : 0 ≤ 2 * (|heatKd 0 1 w| + |heatKd 1 1 w|) := by positivity
  unfold G
  rw [h0, h1]
  calc heatK 1 w * ‖w‖ ≤ heatK 1 w * (|w.1| + |w.2|) := mul_le_mul_of_nonneg_left hn hK.le
    _ = 2 * (|w.1| / 2 * heatK 1 w + |w.2| / 2 * heatK 1 w) := by ring
    _ ≤ 2 * (|w.1| / 2 * heatK 1 w + |w.2| / 2 * heatK 1 w) * Real.cosh w.2 := by
        have : 0 ≤ 2 * (|w.1| / 2 * heatK 1 w + |w.2| / 2 * heatK 1 w) := by positivity
        nlinarith

end STS

/-- Small-time estimate: `|H_a g - g| ≤ C √a` for `g ∈ C¹` with `g`, `∇g` bounded in the weight. -/
theorem heatSG_small_time_sqrt : ∃ M : ℝ, 0 ≤ M ∧ ∀ (B : ℝ) (g : Pl → ℝ), ContDiff ℝ 1 g →
    WB B g → (∀ j : Fin 2, WB B (B0579.pd j g)) →
    ∀ a : ℝ, ∀ x : Pl, |heatSG a g x - g x| ≤ M * B * Real.sqrt (max a 0) := by
  have hGnn : 0 ≤ ∫ w : Pl, STS.G w := integral_nonneg fun w => by
    unfold STS.G; positivity
  refine ⟨2 * ∫ w : Pl, STS.G w, by positivity, fun B g hg hW hW1 a x => ?_⟩
  have hB : 0 ≤ B := by
    have h0 := hW 0
    simp only [Prod.snd_zero, Real.cosh_zero, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  rcases le_or_gt a 0 with ha | ha
  · simp [heatSG, ha, max_eq_right ha]
  rw [max_eq_left ha.le, HC.heatSG_pos_eq ha]
  obtain ⟨-, hI, hint, -⟩ := heatKernelMoments 1 one_pos
  have hgc : Continuous g := hg.continuous
  have hs0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hf : Integrable (fun w : Pl => heatK 1 w * g (x - Real.sqrt a • w)) := by
    refine Integrable.mono' (hI.mul_const B) ?_ (ae_of_all _ fun w => ?_)
    · exact (HC.heatK1_continuous.mul (hgc.comp (by fun_prop))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by unfold heatK; positivity)]
      exact mul_le_mul_of_nonneg_left (HC.gbound hW _) (by unfold heatK; positivity)
  have hx : g x = ∫ w : Pl, heatK 1 w * g x := by
    rw [integral_mul_const, hint, one_mul]
  have hdiff : (∫ w : Pl, heatK 1 w * g (x - Real.sqrt a • w)) - g x
      = ∫ w : Pl, heatK 1 w * (g (x - Real.sqrt a • w) - g x) := by
    conv_lhs => rw [hx]
    rw [← integral_sub hf (hI.mul_const (g x))]
    congr 1; funext w; ring
  rw [hdiff]
  have hbd : Integrable (fun w : Pl => 2 * B * Real.sqrt a * STS.G w) := STS.G_int.const_mul _
  have hpt : ∀ w : Pl, ‖heatK 1 w * (g (x - Real.sqrt a • w) - g x)‖ ≤ 2 * B * Real.sqrt a * STS.G w := by
    intro w
    have hK : 0 < heatK 1 w := by unfold heatK; positivity
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hK, Real.norm_eq_abs]
    have hl := STS.lip hg (hW1 0) (hW1 1) (x - Real.sqrt a • w) x
    have hnn : ‖x - Real.sqrt a • w - x‖ = Real.sqrt a * ‖w‖ := by
      rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    rw [hnn] at hl
    have hKG := STS.K_norm_le w
    calc heatK 1 w * |g (x - Real.sqrt a • w) - g x|
        ≤ heatK 1 w * (2 * B * (Real.sqrt a * ‖w‖)) := mul_le_mul_of_nonneg_left hl hK.le
      _ = 2 * B * Real.sqrt a * (heatK 1 w * ‖w‖) := by ring
      _ ≤ 2 * B * Real.sqrt a * STS.G w :=
          mul_le_mul_of_nonneg_left hKG (by positivity)

  have key := norm_integral_le_of_norm_le hbd (ae_of_all _ hpt)
  rw [Real.norm_eq_abs] at key
  calc _ ≤ ∫ w : Pl, 2 * B * Real.sqrt a * STS.G w := key
    _ = _ := by rw [integral_const_mul]; ring

end UnforcedLeray.Short.IIb.CylPDE
