import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.Split.Scale

/-!
# Mean part helper: the horizontal rescaling `Space → (ℝ × ℝ) × ℝ` as a Bochner change of
variables (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem mp_mapS (ε : ℝ) (hε : 0 < ε) :
    Measure.map (Prod.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a)) (id : ℝ → ℝ))
      (volume : Measure ((ℝ × ℝ) × ℝ)) = ENNReal.ofReal (ε⁻¹) ^ 2 • volume := by
  have hm : Measurable (fun a : ℝ => ε * a) := measurable_const.mul measurable_id
  have h1 : Measure.map (fun a : ℝ => ε * a) volume = ENNReal.ofReal |ε⁻¹| • volume :=
    Real.map_volume_mul_left hε.ne'
  rw [abs_of_pos (inv_pos.2 hε)] at h1
  set c := ENNReal.ofReal ε⁻¹ with hc
  have h2 : Measure.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a))
      (volume : Measure (ℝ × ℝ)) = c ^ 2 • volume := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ hm hm, h1, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul, sq]
  rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (hm.prodMap hm) measurable_id, h2,
    Measure.map_id, Measure.prod_smul_left, ← Measure.volume_eq_prod]

/-- The rescaling homeomorphism `z ↦ ((εz₀, εz₁), z₂)`. -/
def mpPsi (ε : ℝ) (hε : 0 < ε) : Space ≃ₜ (ℝ × ℝ) × ℝ where
  toFun z := ((ε * z 0, ε * z 1), z 2)
  invFun w := !₂[ε⁻¹ * w.1.1, ε⁻¹ * w.1.2, w.2]
  left_inv z := by
    ext i
    fin_cases i <;> simp [hε.ne']
  right_inv w := by
    simp [hε.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem mp_psi_integral (ε : ℝ) (hε : 0 < ε) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (ℝ × ℝ) × ℝ → E) :
    ∫ z : Space, g ((ε * z 0, ε * z 1), z 2) = (ε⁻¹) ^ 2 • ∫ w, g w := by
  have hmp : Measure.map (mpPsi ε hε) (volume : Measure Space) =
      ENNReal.ofReal (ε⁻¹) ^ 2 • volume := by
    have e1 : (mpPsi ε hε : Space → (ℝ × ℝ) × ℝ) =
        Prod.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a)) (id : ℝ → ℝ) ∘
          (fun y : Space => ((y 0, y 1), y 2)) := rfl
    have hS : Measurable (Prod.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a)) (id : ℝ → ℝ)) :=
      ((measurable_const.mul measurable_id).prodMap (measurable_const.mul measurable_id)).prodMap
        measurable_id
    rw [e1, ← Measure.map_map hS t17s_spaceProd.measurable, t17s_spaceProd.map_eq, mp_mapS ε hε]
  have h := (mpPsi ε hε).measurableEmbedding.integral_map (μ := (volume : Measure Space)) g
  rw [hmp, integral_smul_measure] at h
  have : (ENNReal.ofReal (ε⁻¹) ^ 2).toReal = (ε⁻¹) ^ 2 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_nonneg.2 hε.le)]
  rw [this] at h
  exact h.symm

end UnforcedLeray.Short.IIIa

end
