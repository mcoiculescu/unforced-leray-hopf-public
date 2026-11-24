import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.FieldBound

/-!
# `PartIII-a:T21/2/7/1/7/3`: integrability of the pairing `∫ w (u_ψ·∇E(r))` (`locPairInt`)

For a kernel Biot-Savart velocity `u = K_c ψ` (`IsKernelBiotSavart`), `u_j = m_j + v_j` with the
mean shear `m_j = meanShear` (bounded and measurable) and `v_j ∈ L²(cell)`. The fields
`F_j = w ∂_jE(r)` are integrable on the cell and in `L²(cell)` (`locFieldBound`), so each of the
four products `v_j F_j` (an `L² × L²` product) and `m_j F_j` (a bounded factor times an integrable
function) is integrable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace PairIntAux

theorem sign_measurable' : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

theorem abs_sign_le' (r : ℝ) : |Real.sign r| ≤ 1 := by
  unfold Real.sign
  split_ifs <;> norm_num

theorem ms_measurable (c Γ : ℝ) (j : Fin 2) :
    Measurable (fun x : ℝ × ℝ => meanShear c Γ x j) := by
  by_cases hj : j = 0
  · simp only [meanShear, hj, ite_true]
    exact measurable_const.mul (sign_measurable'.comp measurable_snd)
  · simp only [meanShear, hj, ite_false]
    exact measurable_const

theorem ms_abs_le (c Γ : ℝ) (j : Fin 2) (x : ℝ × ℝ) :
    |meanShear c Γ x j| ≤ |Γ / (2 * c)| := by
  unfold meanShear
  split_ifs
  · rw [abs_mul, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_sign_le' _)
  · simp

end PairIntAux

open PairIntAux in
/-- **(L3') Pairing integrability** (SP 3052-3058): `∫ w (K_cψ·∇E(r))` is absolutely convergent on
the cell for `w ∈ X_{-m,c}`, `r ∈ [0, T]` and a kernel Biot-Savart velocity `K_cψ`. -/
theorem locPairInt (m : ℝ) (hm : 8 < m) : LocPairInt m := by
  intro ν hν hν1 tr T C hT hb r hr w ψ uψ hψ hu
  obtain ⟨_, _, hF⟩ := locFieldBound m hm ν hν hν1 tr T C hT hb
  obtain ⟨hv, -, -⟩ := hu
  set Γ : ℝ := ∫ y in UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)), ψ y with hΓ
  have hint0 := (hF r hr w 0).1
  have hmem0 := (hF r hr w 0).2.1
  have hint1 := (hF r hr w 1).1
  have hmem1 := (hF r hr w 1).2.1
  have hI1 : Integrable (fun x => ((uψ x 0 - meanShear (ν ^ (-2 : ℝ)) Γ x 0 : ℝ) : ℂ) *
      (w x * ((UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)))
      (volume.restrict (UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))) :=
    MemLp.integrable_mul (hv 0).ofReal hmem0
  have hI2 : Integrable (fun x => ((uψ x 1 - meanShear (ν ^ (-2 : ℝ)) Γ x 1 : ℝ) : ℂ) *
      (w x * ((UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)))
      (volume.restrict (UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))) :=
    MemLp.integrable_mul (hv 1).ofReal hmem1
  have hI3 : Integrable (fun x => ((meanShear (ν ^ (-2 : ℝ)) Γ x 0 : ℝ) : ℂ) *
      (w x * ((UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)))
      (volume.restrict (UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))) :=
    Integrable.bdd_mul hint0
      (Complex.measurable_ofReal.comp (ms_measurable (ν ^ (-2 : ℝ)) Γ 0)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact ms_abs_le _ _ _ _)
  have hI4 : Integrable (fun x => ((meanShear (ν ^ (-2 : ℝ)) Γ x 1 : ℝ) : ℂ) *
      (w x * ((UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)))
      (volume.restrict (UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))) :=
    Integrable.bdd_mul hint1
      (Complex.measurable_ofReal.comp (ms_measurable (ν ^ (-2 : ℝ)) Γ 1)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact ms_abs_le _ _ _ _)
  have key := ((hI1.add hI2).add hI3).add hI4
  refine key.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  push_cast
  ring

end UnforcedLeray.Short.IIIa
