import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3

/-!
# `KcGradSlice` (leaf C of `PartIII-b:C/flatset/col/4/3`)

Source of record `the November 2 reference manuscript` 3426-3430.
For fixed `ξ`, the cell energy `∫_cell |K_cξ|² + |∇K_cξ|²` is the sum of three `L²(cell)` squared
norms, `‖kcLp ξ‖²`, `‖kcGQ ξ‖²`, `‖kcGE ξ‖²`, by the pointwise identity `sum_sq_identity` and
`kcMer_ae`.  The norms are bounded by `B0583.norm_velocity_le`, `norm_velGradQ_le`,
`norm_velGradEta_le` and `‖reX f‖ ≤ ‖f‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- Pointwise energy identity for a velocity `v` and two gradient columns `a`, `b`. -/
theorem sum_sq_identity (a b v : Merid) :
    vnorm2 (fun i => ((v i : ℝ) : ℂ)) ^ 2 + tnorm2 (gradC a b) ^ 2 =
      ‖v‖ ^ 2 + ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have hv : ‖v‖ ^ 2 = ∑ i, (v i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  have ha : ‖a‖ ^ 2 = ∑ i, (a i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  have hb : ‖b‖ ^ 2 = ∑ i, (b i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  unfold vnorm2 tnorm2
  rw [Real.sq_sqrt, Real.sq_sqrt, hv, ha, hb]
  · simp [Fin.sum_univ_two, gradC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  all_goals positivity

/-- The `L²(cell)` squared norm as a cell lintegral. -/
theorem lintegral_cell_sq_eq_norm {c : ℝ} (f : Lp Merid 2 (B0581.cellVol c)) :
    ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖(f : ℝ × ℝ → Merid) x‖ ^ 2) =
      ENNReal.ofReal (‖f‖ ^ 2) := by
  have hE : eLpNorm (f : ℝ × ℝ → Merid) 2 (B0581.cellVol c) ^ (2 : ℝ) =
      ∫⁻ x, ‖(f : ℝ × ℝ → Merid) x‖ₑ ^ (2 : ℝ) ∂(B0581.cellVol c) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (μ := B0581.cellVol c)
      (f := (f : ℝ × ℝ → Merid)) (p := 2) (by norm_num)
    simpa using h
  have hfin : eLpNorm (f : ℝ × ℝ → Merid) 2 (B0581.cellVol c) ≠ ⊤ := Lp.eLpNorm_ne_top f
  have h3 : ENNReal.ofReal (‖f‖ ^ 2) =
      eLpNorm (f : ℝ × ℝ → Merid) 2 (B0581.cellVol c) ^ (2 : ℝ) := by
    rw [Lp.norm_def, ENNReal.rpow_two, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hfin]
  have hpt : ∀ x, ENNReal.ofReal (‖(f : ℝ × ℝ → Merid) x‖ ^ 2) =
      ‖(f : ℝ × ℝ → Merid) x‖ₑ ^ (2 : ℝ) := by
    intro x
    rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h3, hE]
  exact lintegral_congr hpt

/-- `‖reX f‖ ≤ ‖f‖` (the real part is a norm-one map). -/
theorem norm_reX_le' {c m : ℝ} (f : XAmb c m) : ‖reX f‖ ≤ ‖f‖ := by
  have hL : ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun z => by simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm z)
  calc ‖reX f‖ ≤ ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ * ‖f‖ :=
        ContinuousLinearMap.norm_compLp_le _ f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖f‖ := one_mul _

theorem norm_kcLp_le' {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :
    ‖kcLp ξ‖ ≤ (c / (2 * Real.pi) + 2) * ‖ξ‖ := by
  have hξ : ‖ξ.1‖ = ‖ξ‖ := (Submodule.norm_coe ξ).symm
  have hC : 0 ≤ c / (2 * Real.pi) + 2 :=
    add_nonneg (div_nonneg (Fact.out : (0:ℝ) < c).le (by positivity)) zero_le_two
  calc ‖kcLp ξ‖ ≤ ‖UnforcedLeray.B0583.velocity c one_le_of_fact (reX ξ.1) (reX_circ ξ)‖ :=
        UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_realPartVelocityLp_le _
    _ ≤ (c / (2 * Real.pi) + 2) * ‖reX ξ.1‖ :=
        UnforcedLeray.B0583.norm_velocity_le c one_le_of_fact (reX ξ.1) (reX_circ ξ)
    _ ≤ (c / (2 * Real.pi) + 2) * ‖ξ‖ := by
        rw [← hξ]
        exact mul_le_mul_of_nonneg_left (norm_reX_le' ξ.1) hC

theorem norm_kcGQ_le' {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :
    ‖kcGQ ξ‖ ≤ ‖ξ‖ := by
  have hξ : ‖ξ.1‖ = ‖ξ‖ := (Submodule.norm_coe ξ).symm
  calc ‖kcGQ ξ‖ ≤ ‖UnforcedLeray.B0583.velGradQ c one_le_of_fact (reX ξ.1)‖ :=
        UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_realPartVelocityLp_le _
    _ ≤ ‖reX ξ.1‖ := UnforcedLeray.B0583.norm_velGradQ_le c one_le_of_fact (reX ξ.1)
    _ ≤ ‖ξ‖ := by rw [← hξ]; exact norm_reX_le' ξ.1

theorem norm_kcGE_le' {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :
    ‖kcGE ξ‖ ≤ 2 * ‖ξ‖ := by
  have hξ : ‖ξ.1‖ = ‖ξ‖ := (Submodule.norm_coe ξ).symm
  calc ‖kcGE ξ‖ ≤ ‖UnforcedLeray.B0583.velGradEta c one_le_of_fact (reX ξ.1) (reX_circ ξ)‖ :=
        UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_realPartVelocityLp_le _
    _ ≤ 2 * ‖reX ξ.1‖ := UnforcedLeray.B0583.norm_velGradEta_le c one_le_of_fact (reX ξ.1)
        (reX_circ ξ)
    _ ≤ 2 * ‖ξ‖ := by
        rw [← hξ]
        exact mul_le_mul_of_nonneg_left (norm_reX_le' ξ.1) zero_le_two

/-- **Leaf C** (source 3426-3430): the slice energy bound for the velocity and its gradient. -/
theorem kcGradSlice : KcGradSlice := by
  intro c m _ _
  refine ⟨(c / (2 * Real.pi) + 2) ^ 2 + 5, ?_⟩
  intro ξ G1 G2 hG1 hG2
  refine le_trans (le_of_eq (lintegral_congr fun x =>
    congrArg ENNReal.ofReal (sum_sq_identity (G1 x) (G2 x) (kcMer ξ x)))) ?_
  have hm1 : AEMeasurable (fun x => ENNReal.ofReal (‖(kcLp ξ : ℝ × ℝ → Merid) x‖ ^ 2))
      (volume.restrict (B0579.cell c)) :=
    (((Lp.aestronglyMeasurable (kcLp ξ)).norm.pow 2).aemeasurable).ennreal_ofReal
  have hm3 : AEMeasurable (fun x => ENNReal.ofReal (‖(kcGE ξ : ℝ × ℝ → Merid) x‖ ^ 2))
      (volume.restrict (B0579.cell c)) :=
    (((Lp.aestronglyMeasurable (kcGE ξ)).norm.pow 2).aemeasurable).ennreal_ofReal
  have hae : (fun x => ENNReal.ofReal (‖kcMer ξ x‖ ^ 2 + ‖G1 x‖ ^ 2 + ‖G2 x‖ ^ 2)) =ᵐ[volume.restrict (B0579.cell c)]
      (fun x => ENNReal.ofReal (‖(kcLp ξ : ℝ × ℝ → Merid) x‖ ^ 2) +
        ENNReal.ofReal (‖(kcGQ ξ : ℝ × ℝ → Merid) x‖ ^ 2) +
        ENNReal.ofReal (‖(kcGE ξ : ℝ × ℝ → Merid) x‖ ^ 2)) := by
    filter_upwards [kcMer_ae ξ, hG1, hG2] with x h1 h2 h3
    rw [h1, h2, h3, ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity
  rw [lintegral_congr_ae hae, lintegral_add_right' _ hm3, lintegral_add_left' hm1,
    lintegral_cell_sq_eq_norm (kcLp ξ), lintegral_cell_sq_eq_norm (kcGQ ξ),
    lintegral_cell_sq_eq_norm (kcGE ξ)]
  have hkc := norm_kcLp_le' ξ
  have hgq := norm_kcGQ_le' ξ
  have hge := norm_kcGE_le' ξ
  have hA : ‖kcLp ξ‖ ^ 2 ≤ ((c / (2 * Real.pi) + 2) * ‖ξ‖) ^ 2 := by gcongr
  have hB : ‖kcGQ ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by gcongr
  have hC : ‖kcGE ξ‖ ^ 2 ≤ (2 * ‖ξ‖) ^ 2 := by gcongr
  have key : ‖kcLp ξ‖ ^ 2 + ‖kcGQ ξ‖ ^ 2 + ‖kcGE ξ‖ ^ 2 ≤
      ((c / (2 * Real.pi) + 2) ^ 2 + 5) * ‖ξ‖ ^ 2 := by
    nlinarith [hA, hB, hC]
  calc ENNReal.ofReal (‖kcLp ξ‖ ^ 2) + ENNReal.ofReal (‖kcGQ ξ‖ ^ 2) +
        ENNReal.ofReal (‖kcGE ξ‖ ^ 2)
      = ENNReal.ofReal (‖kcLp ξ‖ ^ 2 + ‖kcGQ ξ‖ ^ 2 + ‖kcGE ξ‖ ^ 2) := by
        rw [ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity
    _ ≤ ENNReal.ofReal (((c / (2 * Real.pi) + 2) ^ 2 + 5) * ‖ξ‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal key

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
