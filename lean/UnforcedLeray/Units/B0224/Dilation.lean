import UnforcedLeray.Units.B0224.FiberHeat

/-!
# B0224 helper: the age dilation `f ↦ f(a s)` on `H`

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379; proof outline
"the substitution `σ = s e^{-t}` gives `‖f(s e^{-t})‖²_H = e^{-t/2}‖f‖²_H`" (infrastructure
"weighted L² substitution in s"). For `a > 0` let `(D_a f)(s, q, η) = f(a s, q, η)` (`dil`).
Since `∫_{s>0} s^{-3/2} h(a s) ds = a^{1/2} ∫_{σ>0} σ^{-3/2} h(σ) dσ` (`lintegral_Ioi_dilate`),

* `‖D_a f‖_H = a^{1/4} ‖f‖_H` (`norm_dilH_apply`);
* `⟨D_a f, g⟩_H = a^{1/2} ⟨f, D_{1/a} g⟩_H` (`inner_dilH`), so `D_a^* = a^{1/2} D_{1/a}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.B0224

open UnforcedLeray.B0220

/-! ### The one-variable substitution -/

/-- `∫_{s>0} s^{-3/2} h(a s) ds = a^{1/2} ∫_{σ>0} σ^{-3/2} h(σ) dσ` for `a > 0`. -/
theorem lintegral_Ioi_dilate {a : ℝ} (ha : 0 < a) (h : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * h (a * s) =
      ENNReal.ofReal (a ^ (1 / 2 : ℝ)) *
        ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * h σ := by
  set K : ℝ → ℝ≥0∞ :=
    (Ioi (0 : ℝ)).indicator fun σ => ENNReal.ofReal ((σ / a) ^ (-(3 / 2 : ℝ))) * h σ with hK
  have h1 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * h (a * s) =
      ∫⁻ s, K (s / a⁻¹) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun s => ?_
    have hsa : s / a⁻¹ = a * s := by rw [div_inv_eq_mul, mul_comm]
    have hsa' : a * s / a = s := by field_simp
    rw [hsa, hK]
    by_cases hs : 0 < s
    · rw [indicator_of_mem (mem_Ioi.2 hs), indicator_of_mem (mem_Ioi.2 (mul_pos ha hs)), hsa']
    · have hs' : ¬ 0 < a * s := fun h' => hs (pos_of_mul_pos_right h' ha.le)
      rw [indicator_of_notMem (fun h' => hs (mem_Ioi.1 h')),
        indicator_of_notMem (fun h' => hs' (mem_Ioi.1 h'))]
  have h2 : ∫⁻ σ, K σ = ENNReal.ofReal (a ^ (3 / 2 : ℝ)) *
      ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * h σ := by
    rw [hK, lintegral_indicator measurableSet_Ioi, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
    have hσ' : 0 < σ := hσ
    rw [Real.div_rpow hσ'.le ha.le, Real.rpow_neg ha.le, div_inv_eq_mul,
      ENNReal.ofReal_mul (Real.rpow_nonneg hσ'.le _), mul_comm (ENNReal.ofReal (σ ^ _)), mul_assoc]
  rw [h1, lintegral_comp_div_pos (inv_pos.2 ha), h2, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le)]
  congr 2
  rw [← Real.rpow_neg_one, ← Real.rpow_add ha]
  norm_num

variable {c : ℝ}

/-- The dilation identity on `H`: `∫ Φ(a s, q, η) dH = a^{1/2} ∫ Φ dH`. -/
theorem lintegral_measureH_dil {a : ℝ} (ha : 0 < a) {Φ : Profile → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ p, Φ (a * p.1, p.2) ∂measureH c = ENNReal.ofReal (a ^ (1 / 2 : ℝ)) * ∫⁻ p, Φ p ∂measureH c := by
  have hT : Measurable fun p : Profile => ((a * p.1, p.2) : Profile) :=
    (measurable_fst.const_mul a).prodMk measurable_snd
  have hw : Measurable fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  rw [lintegral_measureH_eq (fun p : Profile => Φ (a * p.1, p.2)) (hΦ.comp hT),
    lintegral_measureH_eq _ hΦ, cellMeasure_eq_prod',
    lintegral_prod (fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * Φ (a * p.1, p.2))
      (hw.mul (hΦ.comp hT)).aemeasurable,
    lintegral_prod (fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * Φ p)
      (hw.mul hΦ).aemeasurable]
  set h : ℝ → ℝ≥0∞ := fun σ => ∫⁻ x in strip c, Φ (σ, x) with hh
  have e1 : ∀ s : ℝ, ∫⁻ x in strip c, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
      Φ (a * s, x) = ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * h (a * s) := by
    intro s
    have hm : Measurable fun x : ℝ × ℝ => Φ (a * s, x) := hΦ.comp measurable_prodMk_left
    exact lintegral_const_mul _ hm
  have e2 : ∀ s : ℝ, ∫⁻ x in strip c, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * Φ (s, x) =
      ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * h s := by
    intro s
    have hm : Measurable fun x : ℝ × ℝ => Φ (s, x) := hΦ.comp measurable_prodMk_left
    exact lintegral_const_mul _ hm
  dsimp only
  simp only [e1, e2]
  exact lintegral_Ioi_dilate ha h

/-! ### The dilation operator -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The age dilation `(D_a F)(s, q, η) = F(a s, q, η)`. -/
def dil (a : ℝ) (F : Profile → E) (p : Profile) : E := F (a * p.1, p.2)

theorem stronglyMeasurable_dil (a : ℝ) {F : Profile → E} (hF : StronglyMeasurable F) :
    StronglyMeasurable (dil a F) :=
  hF.comp_measurable ((measurable_fst.const_mul a).prodMk measurable_snd)

theorem eLpNorm_dil {a : ℝ} (ha : 0 < a) {F : Profile → E} (hF : StronglyMeasurable F) :
    eLpNorm (dil a F) 2 (measureH c) =
      ENNReal.ofReal (a ^ (1 / 4 : ℝ)) * eLpNorm F 2 (measureH c) := by
  have h := lintegral_measureH_dil (c := c) ha (hF.enorm.pow_const 2)
  rw [eLpNorm_two_eq, eLpNorm_two_eq]
  simp only [dil]
  rw [h, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ha.le _) (by norm_num), ← Real.rpow_mul ha.le]
  norm_num

theorem dil_congr_ae {a : ℝ} (ha : 0 < a) {F G : Profile → E} (hF : StronglyMeasurable F)
    (hG : StronglyMeasurable G) (h : F =ᵐ[measureH c] G) :
    dil a F =ᵐ[measureH c] dil a G := by
  have hΦm : Measurable fun p => ‖F p - G p‖ₑ := (hF.sub hG).enorm
  have h0 : ∫⁻ p, ‖F p - G p‖ₑ ∂measureH c = 0 := by
    rw [lintegral_eq_zero_iff hΦm]
    filter_upwards [h] with p hp
    simp [hp]
  have h1 := lintegral_measureH_dil (c := c) ha hΦm
  have hm2 : Measurable fun p : Profile => ‖F (a * p.1, p.2) - G (a * p.1, p.2)‖ₑ :=
    hΦm.comp ((measurable_fst.const_mul a).prodMk measurable_snd)
  rw [h0, mul_zero, lintegral_eq_zero_iff hm2] at h1
  filter_upwards [h1] with p hp
  simpa [dil, sub_eq_zero] using hp

theorem memLp_dil {a : ℝ} (ha : 0 < a) (f : HSpace c E) : MemLp (dil a f) 2 (measureH c) :=
  ⟨(stronglyMeasurable_dil a (Lp.stronglyMeasurable f)).aestronglyMeasurable, by
    rw [eLpNorm_dil ha (Lp.stronglyMeasurable f)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp f).2⟩

/-- The age dilation `D_a` as a bounded operator on `H` (`a > 0`). -/
def dilH {a : ℝ} (ha : 0 < a) : HSpace c E →L[ℝ] HSpace c E :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_dil ha f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        refine (dil_congr_ae ha (Lp.stronglyMeasurable _)
          ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable g)) (Lp.coeFn_add f g)).trans ?_
        exact Eventually.of_forall fun p => rfl
      map_smul' := fun r f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        refine (dil_congr_ae ha (Lp.stronglyMeasurable _)
          ((Lp.stronglyMeasurable f).const_smul r) (Lp.coeFn_smul r f)).trans ?_
        exact Eventually.of_forall fun p => rfl }
    (a ^ (1 / 4 : ℝ)) (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, eLpNorm_dil ha (Lp.stronglyMeasurable f), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _), Lp.norm_def])

theorem coeFn_dilH {a : ℝ} (ha : 0 < a) (f : HSpace c E) :
    dilH ha f =ᵐ[measureH c] dil a f :=
  MemLp.coeFn_toLp (memLp_dil ha f)

theorem norm_dilH_apply {a : ℝ} (ha : 0 < a) (f : HSpace c E) :
    ‖dilH ha f‖ = a ^ (1 / 4 : ℝ) * ‖f‖ := by
  change ‖(memLp_dil ha f).toLp _‖ = _
  rw [Lp.norm_toLp, eLpNorm_dil ha (Lp.stronglyMeasurable f), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _), Lp.norm_def]

theorem norm_dilH_le {a : ℝ} (ha : 0 < a) :
    ‖(dilH ha : HSpace c E →L[ℝ] HSpace c E)‖ ≤ a ^ (1 / 4 : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg ha.le _) _

/-! ### The adjoint of the dilation -/

/-- The image of `H`'s measure under `(s, q, η) ↦ (a s, q, η)` is `a^{1/2}` times itself. -/
theorem map_measureH_dil {a : ℝ} (ha : 0 < a) :
    (measureH c).map (fun p : Profile => ((a * p.1, p.2) : Profile)) =
      ENNReal.ofReal (a ^ (1 / 2 : ℝ)) • measureH c := by
  have hT : Measurable fun p : Profile => ((a * p.1, p.2) : Profile) :=
    (measurable_fst.const_mul a).prodMk measurable_snd
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [lintegral_map hΦ hT, lintegral_smul_measure, lintegral_measureH_dil ha hΦ, smul_eq_mul]

/-- The dilation identity for Bochner integrals: `∫ φ(a s, q, η) dH = a^{1/2} ∫ φ dH`. -/
theorem integral_measureH_dil {a : ℝ} (ha : 0 < a) {φ : Profile → ℝ}
    (hφ : StronglyMeasurable φ) :
    ∫ p, φ (a * p.1, p.2) ∂measureH c = a ^ (1 / 2 : ℝ) * ∫ p, φ p ∂measureH c := by
  have hT : Measurable fun p : Profile => ((a * p.1, p.2) : Profile) :=
    (measurable_fst.const_mul a).prodMk measurable_snd
  rw [← integral_map hT.aemeasurable hφ.aestronglyMeasurable, map_measureH_dil ha,
    integral_smul_measure, ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _), smul_eq_mul]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- `⟨D_a f, g⟩_H = a^{1/2} ⟨f, D_{1/a} g⟩_H`. -/
theorem inner_dilH {a : ℝ} (ha : 0 < a) (f g : HSpace c F) :
    ⟪dilH ha f, g⟫_ℝ = a ^ (1 / 2 : ℝ) * ⟪f, dilH (inv_pos.2 ha) g⟫_ℝ := by
  have hf := Lp.stronglyMeasurable f
  have hg := Lp.stronglyMeasurable g
  rw [L2.inner_def, L2.inner_def]
  have e1 : (fun p => ⟪dilH ha f p, g p⟫_ℝ) =ᵐ[measureH c]
      fun p => ⟪f (a * p.1, p.2), g (a⁻¹ * (a * p.1), p.2)⟫_ℝ := by
    filter_upwards [coeFn_dilH ha f] with p hp
    rw [hp, inv_mul_cancel_left₀ ha.ne']
    rfl
  have e2 : (fun p => ⟪f p, dilH (inv_pos.2 ha) g p⟫_ℝ) =ᵐ[measureH c]
      fun p => ⟪f p, g (a⁻¹ * p.1, p.2)⟫_ℝ := by
    filter_upwards [coeFn_dilH (inv_pos.2 ha) g] with p hp
    rw [hp]
    rfl
  rw [integral_congr_ae e1, integral_congr_ae e2]
  have hφ : StronglyMeasurable fun p : Profile => ⟪f p, g (a⁻¹ * p.1, p.2)⟫_ℝ :=
    hf.inner (stronglyMeasurable_dil a⁻¹ hg)
  exact integral_measureH_dil (φ := fun p : Profile => ⟪f p, g (a⁻¹ * p.1, p.2)⟫_ℝ) ha hφ

end UnforcedLeray.B0224
