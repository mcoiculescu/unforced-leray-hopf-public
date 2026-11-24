import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatMoments

/-!


Proves `HeatCont` (`Sub/T22_1/Stages.lean`). For `a > 0`, the substitution `y = x - √a w` and the
scaling identity `heatK a (√a w) * a = heatK 1 w` give
`heatSG a g x = ∫ w, heatK 1 w * g (x - √a w)`. The right side, with `a` replaced by `max a 0`,
is continuous on the whole of `ℝ × Pl` by dominated continuity (domination `|heatK 1 w| * B`),
and it agrees with `heatSG` on `[0, ∞) × Pl` (at `a = 0` because `∫ heatK 1 = 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

namespace HC

lemma finrank_pl : Module.finrank ℝ Pl = 2 := by
  show Module.finrank ℝ (ℝ × ℝ) = 2
  simp [Module.finrank_prod]

/-- Scaling identity for the Gaussian kernel. -/
lemma heatK_scale {a : ℝ} (ha : 0 < a) (w : Pl) :
    heatK a (Real.sqrt a • w) * a = heatK 1 w := by
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hexp : -((Real.sqrt a * w.1) ^ 2 + (Real.sqrt a * w.2) ^ 2) / (4 * a)
      = -(w.1 ^ 2 + w.2 ^ 2) / (4 * 1) := by
    rw [mul_pow, mul_pow, hs]
    field_simp
  unfold heatK
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [hexp]
  field_simp

/-- Scaled representation of the semigroup for `a > 0`. -/
lemma heatSG_pos_eq {a : ℝ} (ha : 0 < a) (g : Pl → ℝ) (x : Pl) :
    heatSG a g x = ∫ w : Pl, heatK 1 w * g (x - Real.sqrt a • w) := by
  unfold heatSG
  rw [if_neg (not_le.2 ha)]
  have h1 : ∫ y : Pl, heatK a (x - y) * g y = ∫ u : Pl, heatK a u * g (x - u) := by
    rw [← integral_sub_left_eq_self (fun u : Pl => heatK a u * g (x - u)) volume x]
    congr 1
    funext y
    simp
  have hpt : ∀ w : Pl, heatK a (Real.sqrt a • w) * g (x - Real.sqrt a • w)
      = a⁻¹ * (heatK 1 w * g (x - Real.sqrt a • w)) := by
    intro w
    rw [← heatK_scale ha w]
    field_simp
  have h2 := MeasureTheory.Measure.integral_comp_smul (volume : Measure Pl)
    (fun u : Pl => heatK a u * g (x - u)) (Real.sqrt a)
  simp_rw [hpt] at h2
  rw [integral_const_mul, finrank_pl] at h2
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have habs : |(Real.sqrt a ^ 2)⁻¹| = a⁻¹ := by
    rw [hs]
    exact abs_of_pos (inv_pos.2 ha)
  rw [habs, smul_eq_mul] at h2
  rw [h1]
  have ha' : a⁻¹ ≠ 0 := inv_ne_zero ha.ne'
  exact (mul_left_cancel₀ ha' h2).symm

lemma gbound {B : ℝ} {g : Pl → ℝ} (hg : WB B g) (y : Pl) : |g y| ≤ B := by
  have h := hg y
  have hc : 1 ≤ Real.cosh y.2 := Real.one_le_cosh _
  have h0 : 0 ≤ |g y| := abs_nonneg _
  nlinarith [mul_nonneg h0 (sub_nonneg.2 hc)]

lemma heatK1_continuous : Continuous (heatK 1) := by
  unfold heatK
  fun_prop

/-- Continuity of the scaled integral on all of `ℝ × Pl`. -/
lemma phi_continuous {B : ℝ} {g : Pl → ℝ} (hgc : Continuous g) (hg : WB B g) :
    Continuous (fun p : ℝ × Pl =>
      ∫ w : Pl, heatK 1 w * g (p.2 - Real.sqrt (max p.1 0) • w)) := by
  obtain ⟨-, hI, -, -⟩ := UnforcedLeray.Short.IIb.CylPDE.heatKernelMoments 1 one_pos
  have hKc := heatK1_continuous
  refine continuous_of_dominated (bound := fun w => |heatK 1 w| * B) ?_ ?_ ?_ ?_
  · intro p
    exact (hKc.mul (hgc.comp (by fun_prop))).aestronglyMeasurable
  · intro p
    refine ae_of_all _ fun w => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (gbound hg _) (abs_nonneg _)
  · exact hI.abs.mul_const B
  · refine ae_of_all _ fun w => ?_
    exact continuous_const.mul (hgc.comp (by fun_prop))

end HC

/-- **`T22/1/9`** Joint continuity of the heat semigroup on `[0, ∞) × Pl` (Stages.lean `HeatCont`). -/
theorem heatCont : UnforcedLeray.Short.IIb.CylPDE.HeatCont := by
  intro B g hgc hg
  have hC := HC.phi_continuous hgc hg
  apply ContinuousOn.congr hC.continuousOn
  rintro ⟨a, x⟩ hz
  simp only [Set.mem_prod, Set.mem_Ici, Set.mem_univ, and_true] at hz
  rcases hz.lt_or_eq with ha | ha
  · show heatSG a g x = ∫ w : Pl, heatK 1 w * g (x - Real.sqrt (max a 0) • w)
    rw [HC.heatSG_pos_eq ha g x, max_eq_left ha.le]
  · subst ha
    have hint := (UnforcedLeray.Short.IIb.CylPDE.heatKernelMoments 1 one_pos).2.2.1
    show heatSG 0 g x = ∫ w : Pl, heatK 1 w * g (x - Real.sqrt (max 0 0) • w)
    simp only [heatSG, le_refl, if_true, max_self, Real.sqrt_zero, zero_smul, sub_zero]
    rw [integral_mul_const, hint, one_mul]

end UnforcedLeray.Short.IIb.CylPDE
