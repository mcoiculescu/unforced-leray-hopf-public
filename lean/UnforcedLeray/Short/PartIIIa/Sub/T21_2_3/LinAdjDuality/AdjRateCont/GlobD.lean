import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.LocalizedSourceBounds
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# Part III-a: the decaying shear weight `jb^{-1}(|u₀| + |u₁|)` is in `L²` of the cell

For a kernel Biot-Savart velocity `u` (`u - meanShear ∈ L²`, `meanShear` bounded), the function
`jb^{-1}(|u₀| + |u₁|)` lies in `L²(C_c)` since `jb^{-1} ∈ L²(ℝ²)` (`∫ jb^{-2} < ∞`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace GlobDAux

lemma jb_ge_one (x : ℝ × ℝ) : 1 ≤ B0579.jb x := by
  unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]

lemma memLp_jb_inv : MemLp (fun x : ℝ × ℝ => B0579.jb x ^ (-1 : ℝ)) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    (B0579.continuous_jb_rpow _).aestronglyMeasurable).2 ?_
  refine integrable_jb_rpow_neg_two'.congr (Filter.Eventually.of_forall fun x => ?_)
  show B0579.jb x ^ (-(2 : ℝ)) = ‖B0579.jb x ^ (-1 : ℝ)‖ ^ 2
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _), ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos x).le]
  norm_num

lemma abs_meanShear_le (c Γ : ℝ) (x : ℝ × ℝ) (j : Fin 2) : |meanShear c Γ x j| ≤ |Γ / (2 * c)| := by
  unfold meanShear
  split_ifs
  · rw [abs_mul, abs_neg]
    have h : |Real.sign x.2| ≤ 1 := by
      rcases Real.sign_apply_eq x.2 with h | h | h <;> simp [h]
    calc |Γ / (2 * c)| * |Real.sign x.2| ≤ |Γ / (2 * c)| * 1 :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = _ := mul_one _
  · simp

lemma measurable_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

lemma measurable_meanShear (c Γ : ℝ) (j : Fin 2) : Measurable fun x : ℝ × ℝ => meanShear c Γ x j := by
  unfold meanShear
  split_ifs
  · exact measurable_const.mul (measurable_sign.comp measurable_snd)
  · exact measurable_const

lemma aesm_vel (c Γ : ℝ) (u : ℝ × ℝ → Fin 2 → ℝ)
    (hu : ∀ j, MemLp (fun x => u x j - meanShear c Γ x j) 2 (volume.restrict (B0579.cell c)))
    (j : Fin 2) : AEStronglyMeasurable (fun x => u x j) (volume.restrict (B0579.cell c)) := by
  have := (hu j).1.add (measurable_meanShear c Γ j).aestronglyMeasurable
  exact this.congr (Filter.Eventually.of_forall fun x => by simp)

end GlobDAux

/-- `jb^{-1}(|u₀| + |u₁|) ∈ L²(C_c)` for `u - meanShear ∈ L²(C_c)`. -/
theorem memLp_decayShear (c Γ : ℝ) (u : ℝ × ℝ → Fin 2 → ℝ)
    (hu : ∀ j, MemLp (fun x => u x j - meanShear c Γ x j) 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun x => B0579.jb x ^ (-1 : ℝ) * (|u x 0| + |u x 1|)) 2
      (volume.restrict (B0579.cell c)) := by
  set K : ℝ := |Γ / (2 * c)| with hK
  have hk0 : MemLp (fun x : ℝ × ℝ => B0579.jb x ^ (-1 : ℝ)) 2 (volume.restrict (B0579.cell c)) :=
    GlobDAux.memLp_jb_inv.restrict _
  have hg : MemLp (fun x => ‖u x 0 - meanShear c Γ x 0‖ + ‖u x 1 - meanShear c Γ x 1‖ +
      (2 * K) * B0579.jb x ^ (-1 : ℝ)) 2 (volume.restrict (B0579.cell c)) :=
    (((hu 0).norm).add ((hu 1).norm)).add (hk0.const_mul (2 * K))
  have hum : ∀ j, AEStronglyMeasurable (fun x => u x j) (volume.restrict (B0579.cell c)) :=
    GlobDAux.aesm_vel c Γ u hu
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (B0579.continuous_jb_rpow _).aestronglyMeasurable.mul
      ((hum 0).norm.add (hum 1).norm)
  · have hj1 : 1 ≤ B0579.jb x := GlobDAux.jb_ge_one x
    have hp : 0 < B0579.jb x ^ (-1 : ℝ) := Real.rpow_pos_of_pos (B0579.jb_pos x) _
    have hle : B0579.jb x ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hj1 (by norm_num)
    have hj : ∀ j : Fin 2, B0579.jb x ^ (-1 : ℝ) * |u x j| ≤
        ‖u x j - meanShear c Γ x j‖ + K * B0579.jb x ^ (-1 : ℝ) := by
      intro j
      have h1 : |u x j| ≤ ‖u x j - meanShear c Γ x j‖ + K := by
        have := GlobDAux.abs_meanShear_le c Γ x j
        rw [Real.norm_eq_abs]
        calc |u x j| = |(u x j - meanShear c Γ x j) + meanShear c Γ x j| := by ring_nf
          _ ≤ |u x j - meanShear c Γ x j| + |meanShear c Γ x j| := abs_add_le _ _
          _ ≤ _ := by linarith
      have hn := norm_nonneg (u x j - meanShear c Γ x j)
      calc B0579.jb x ^ (-1 : ℝ) * |u x j|
          ≤ B0579.jb x ^ (-1 : ℝ) * (‖u x j - meanShear c Γ x j‖ + K) :=
            mul_le_mul_of_nonneg_left h1 hp.le
        _ = B0579.jb x ^ (-1 : ℝ) * ‖u x j - meanShear c Γ x j‖ + K * B0579.jb x ^ (-1 : ℝ) := by
            ring
        _ ≤ 1 * ‖u x j - meanShear c Γ x j‖ + K * B0579.jb x ^ (-1 : ℝ) := by
            gcongr
        _ = _ := by rw [one_mul]
    have h0 := hj 0
    have h1 := hj 1
    have hnn : 0 ≤ B0579.jb x ^ (-1 : ℝ) * (|u x 0| + |u x 1|) :=
      mul_nonneg hp.le (add_nonneg (abs_nonneg _) (abs_nonneg _))
    rw [Real.norm_of_nonneg hnn]
    nlinarith

end UnforcedLeray.Short.IIIa
