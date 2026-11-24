import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique

/-!
# Part III-a, `PartIII-a:T21/2/1/2/10`: uniqueness of the kernel Biot-Savart velocity

Source of record: `the November 2 reference manuscript` (SP), lines 3230-3240
(uniqueness of the Biot-Savart velocity) and 3052-3057 (the kernel of the cylinder).

Proof of `kernelBiotSavartUnique`. Let `u, v` satisfy `IsKernelBiotSavart d ψ` with the same
`ψ`, so they have the same mean shear, and put `a = u_q - v_q`, `b = u_η - v_η`.
* `a, b ∈ L²(C_d)` (the mean shear cancels in the difference).
* For a test `φ`, the three clauses of `IsKernelBiotSavart` (div and curl of `u` and `v`) make
  `∫ (∂_η φ a - ∂_q φ b) = 0` and `∫ (∂_q φ a + ∂_η φ b) = 0`, because each product
  `u_j ∂_iφ` is integrable (`L²` times `L²`, plus the bounded mean shear times an integrable
  factor).
* `T20_2.liouville_real` gives `a = b = 0` a.e. on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The real sign function is measurable. -/
theorem measurable_realSign : Measurable Real.sign := by
  have e : Real.sign = fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0 := by
    funext r
    rfl
  rw [e]
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

/-- The mean shear is bounded by `|Γ| / |2d|`. -/
theorem abs_meanShear_le (d Γ : ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    |meanShear d Γ x j| ≤ |Γ| / |2 * d| := by
  unfold meanShear
  split_ifs
  · have hs : |Real.sign x.2| ≤ 1 := by
      rcases Real.sign_apply_eq x.2 with h | h | h <;> rw [h] <;> norm_num
    rw [abs_mul, abs_neg, abs_div]
    exact mul_le_of_le_one_right (by positivity) hs
  · rw [abs_zero]
    positivity

/-- The mean shear is measurable in `x`. -/
theorem measurable_meanShear (d Γ : ℝ) (j : Fin 2) :
    Measurable (fun x : ℝ × ℝ => meanShear d Γ x j) := by
  by_cases h : j = 0
  · have e : (fun x : ℝ × ℝ => meanShear d Γ x j) =
        fun x => -(Γ / (2 * d)) * Real.sign x.2 := by
      funext x
      simp [meanShear, h]
    rw [e]
    exact measurable_const.mul (measurable_realSign.comp measurable_snd)
  · have e : (fun x : ℝ × ℝ => meanShear d Γ x j) = fun _ => (0 : ℝ) := by
      funext x
      simp [meanShear, h]
    rw [e]
    exact measurable_const

/-- The derivative of a kernel test is `L²` on the cell. -/
theorem pd_memLp_cell {d : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest d φ) (i : Fin 2) :
    MemLp (B0579.pd i φ) 2 (volume.restrict (B0579.cell d)) := by
  obtain ⟨R, hR⟩ := (hφ.pd i).vanish
  exact B0579.memLp_cell_of_continuous (hφ.pd i).continuous (B0579.isCompact_box d R)
    (fun x hx hxK => hR x hx hxK)

/-- A product `w · p` is integrable on the cell when `w - meanShear` is `L²`, and `p` is an `L²`
test derivative. -/
theorem integrable_mean_mul {d Γ : ℝ} {j : Fin 2} {w p : ℝ × ℝ → ℝ}
    (hw : MemLp (fun x => w x - meanShear d Γ x j) 2 (volume.restrict (B0579.cell d)))
    (hp2 : MemLp p 2 (volume.restrict (B0579.cell d)))
    (hp1 : IntegrableOn p (B0579.cell d)) :
    Integrable (fun x => w x * p x) (volume.restrict (B0579.cell d)) := by
  have h1 : Integrable (fun x => (w x - meanShear d Γ x j) * p x)
      (volume.restrict (B0579.cell d)) :=
    MemLp.integrable_mul hw hp2
  have h2 : Integrable (fun x => meanShear d Γ x j * p x) (volume.restrict (B0579.cell d)) :=
    Integrable.bdd_mul (c := |Γ| / |2 * d|) hp1
      (measurable_meanShear d Γ j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact abs_meanShear_le d Γ x j)
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
  show (w x - meanShear d Γ x j) * p x + meanShear d Γ x j * p x = w x * p x
  ring

/-- **Uniqueness of the kernel Biot-Savart velocity** (SP 3230-3240): two fields with
`IsKernelBiotSavart d ψ` agree a.e. on the cell. -/
theorem kernelBiotSavartUnique : KernelBiotSavartUnique := by
  intro d hd ψ u v hu hv
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have hint_u : ∀ (i j : Fin 2) (φ : ℝ × ℝ → ℝ), B0579.IsCylTest d φ →
      Integrable (fun x => u x j * B0579.pd i φ x) (volume.restrict (B0579.cell d)) :=
    fun i j φ hφ => integrable_mean_mul (w := fun x => u x j) (hu1 j) (pd_memLp_cell hφ i)
      (hφ.pd i).integrableOn
  have hint_v : ∀ (i j : Fin 2) (φ : ℝ × ℝ → ℝ), B0579.IsCylTest d φ →
      Integrable (fun x => v x j * B0579.pd i φ x) (volume.restrict (B0579.cell d)) :=
    fun i j φ hφ => integrable_mean_mul (w := fun x => v x j) (hv1 j) (pd_memLp_cell hφ i)
      (hφ.pd i).integrableOn
  -- the difference `u - v` is `L²` on the cell
  have hL2 : ∀ j, MemLp (fun x => u x j - v x j) 2 (volume.restrict (B0579.cell d)) := by
    intro j
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun x => ?_) ((hu1 j).sub (hv1 j))
    simp only [Pi.sub_apply]
    ring
  have hcurl : ∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest d φ →
      ∫ z in UnforcedLeray.Cyl.cell d,
        (fderiv ℝ φ z (0, 1) * (u z 0 - v z 0) - fderiv ℝ φ z (1, 0) * (u z 1 - v z 1)) = 0 := by
    intro φ hφS
    have hφ : B0579.IsCylTest d φ := CTE.T20_2.B0579_of_sob hφS
    rw [← CTE.T20_2.cell_eq]
    show ∫ z in B0579.cell d,
        (B0579.pd 1 φ z * (u z 0 - v z 0) - B0579.pd 0 φ z * (u z 1 - v z 1)) = 0
    have e : ∫ z in B0579.cell d,
        (B0579.pd 1 φ z * (u z 0 - v z 0) - B0579.pd 0 φ z * (u z 1 - v z 1)) =
        ∫ z in B0579.cell d,
          ((u z 0 * B0579.pd 1 φ z - u z 1 * B0579.pd 0 φ z) -
            (v z 0 * B0579.pd 1 φ z - v z 1 * B0579.pd 0 φ z)) := by
      congr 1
      funext z
      ring
    have hIu : Integrable (fun z => u z 0 * B0579.pd 1 φ z - u z 1 * B0579.pd 0 φ z)
        (volume.restrict (B0579.cell d)) :=
      (hint_u 1 0 φ hφ).sub (hint_u 0 1 φ hφ)
    have hIv : Integrable (fun z => v z 0 * B0579.pd 1 φ z - v z 1 * B0579.pd 0 φ z)
        (volume.restrict (B0579.cell d)) :=
      (hint_v 1 0 φ hφ).sub (hint_v 0 1 φ hφ)
    rw [e, integral_sub hIu hIv]
    linarith [hu3 φ hφ, hv3 φ hφ]
  have hdiv : ∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest d φ →
      ∫ z in UnforcedLeray.Cyl.cell d,
        (fderiv ℝ φ z (1, 0) * (u z 0 - v z 0) + fderiv ℝ φ z (0, 1) * (u z 1 - v z 1)) = 0 := by
    intro φ hφS
    have hφ : B0579.IsCylTest d φ := CTE.T20_2.B0579_of_sob hφS
    rw [← CTE.T20_2.cell_eq]
    show ∫ z in B0579.cell d,
        (B0579.pd 0 φ z * (u z 0 - v z 0) + B0579.pd 1 φ z * (u z 1 - v z 1)) = 0
    have e : ∫ z in B0579.cell d,
        (B0579.pd 0 φ z * (u z 0 - v z 0) + B0579.pd 1 φ z * (u z 1 - v z 1)) =
        ∫ z in B0579.cell d,
          ((u z 0 * B0579.pd 0 φ z + u z 1 * B0579.pd 1 φ z) -
            (v z 0 * B0579.pd 0 φ z + v z 1 * B0579.pd 1 φ z)) := by
      congr 1
      funext z
      ring
    have hIu : Integrable (fun z => u z 0 * B0579.pd 0 φ z + u z 1 * B0579.pd 1 φ z)
        (volume.restrict (B0579.cell d)) :=
      (hint_u 0 0 φ hφ).add (hint_u 1 1 φ hφ)
    have hIv : Integrable (fun z => v z 0 * B0579.pd 0 φ z + v z 1 * B0579.pd 1 φ z)
        (volume.restrict (B0579.cell d)) :=
      (hint_v 0 0 φ hφ).add (hint_v 1 1 φ hφ)
    rw [e, integral_sub hIu hIv]
    linarith [hu2 φ hφ, hv2 φ hφ]
  have ha : MemLp (fun x => u x 0 - v x 0) 2 (UnforcedLeray.Cyl.cellμ d) := by
    rw [CTE.T20_2.cellμ_eq_B0579]
    exact hL2 0
  have hb : MemLp (fun x => u x 1 - v x 1) 2 (UnforcedLeray.Cyl.cellμ d) := by
    rw [CTE.T20_2.cellμ_eq_B0579]
    exact hL2 1
  obtain ⟨ha0, hb0⟩ := CTE.T20_2.liouville_real hd ha hb hcurl hdiv
  rw [CTE.T20_2.cellμ_eq_B0579] at ha0 hb0
  filter_upwards [ha0, hb0] with x h0 h1
  have h0' : u x 0 = v x 0 := by simpa [sub_eq_zero] using h0
  have h1' : u x 1 = v x 1 := by simpa [sub_eq_zero] using h1
  funext j
  fin_cases j
  · exact h0'
  · exact h1'

end UnforcedLeray.Short.IIIa
