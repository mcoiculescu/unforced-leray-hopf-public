import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.CellPairBound

/-!
# Proof of `FcvEllCLM` (source 2819-2836)

`ℓ_r(ω) = ∫_cell flowIntegrand tr (xFn ω) (K_c ω) r φ`.  The integrand is
`xFn ω · g0 - ((K_c ω)_0 · g1 + (K_c ω)_1 · g2)` with coefficients `g0, g1, g2` that are continuous
(`tr` is smooth for `r > 0`, `φ` is a cylinder test) and vanish outside the band `|η| > |R|`.
Each of the three integrals is a bounded `ℝ`-linear functional of `ω`: the first by the cell `L¹`
bound of `xFn`, the other two by the `L²` bound of the real Biot–Savart velocity on the box
`[-c/2, c/2] × [-|R|, |R|]` (Hölder on a set of finite measure).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff


namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-! ### Calculus: the coefficients -/

theorem partialQ_eq_fderiv_ {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialQ f z = fderiv ℝ f z (1, 0) := by
  unfold UnforcedLeray.Cyl.partialQ
  have h1 : HasDerivAt (fun q : ℝ => (q, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  exact ((hf (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h1).deriv

theorem partialEta_eq_fderiv_ {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialEta f z = fderiv ℝ f z (0, 1) := by
  unfold UnforcedLeray.Cyl.partialEta
  have h1 : HasDerivAt (fun η : ℝ => (z.1, η)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  exact ((hf (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2 h1).deriv

theorem Ec_eq_fderiv_ {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r)
    (z : ℝ × ℝ) :
    UnforcedLeray.B0238.Ec tr r z =
      fderiv ℝ (fun w => tr.v r w 1) z (1, 0) - fderiv ℝ (fun w => tr.v r w 0) z (0, 1) := by
  have hv := UnforcedLeray.B0238.contDiff_Vc tr hr.le
  have h1 : ContDiff ℝ ∞ (fun w => tr.v r w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have h0 : ContDiff ℝ ∞ (fun w => tr.v r w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have d1 : Differentiable ℝ (fun w => tr.v r w 1) := h1.differentiable (by simp)
  have d0 : Differentiable ℝ (fun w => tr.v r w 0) := h0.differentiable (by simp)
  unfold UnforcedLeray.B0238.Ec UnforcedLeray.Cyl.curl
  rw [partialQ_eq_fderiv_ d1, partialEta_eq_fderiv_ d0]

theorem contDiff_Ec_ {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ 1 (UnforcedLeray.B0238.Ec tr r) := by
  have hv := UnforcedLeray.B0238.contDiff_Vc tr hr.le
  have h1 : ContDiff ℝ ∞ (fun w => tr.v r w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have h0 : ContDiff ℝ ∞ (fun w => tr.v r w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have d1 : ContDiff ℝ 1 (fderiv ℝ (fun w => tr.v r w 1)) := h1.fderiv_right (by simp)
  have d0 : ContDiff ℝ 1 (fderiv ℝ (fun w => tr.v r w 0)) := h0.fderiv_right (by simp)
  have e : UnforcedLeray.B0238.Ec tr r = fun z =>
      fderiv ℝ (fun w => tr.v r w 1) z (1, 0) - fderiv ℝ (fun w => tr.v r w 0) z (0, 1) :=
    funext (Ec_eq_fderiv_ tr hr)
  rw [e]
  exact (d1.clm_apply contDiff_const).sub (d0.clm_apply contDiff_const)

theorem continuous_pd_Ec_ {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r)
    (j : Fin 2) : Continuous (UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr r)) := by
  have hE := contDiff_Ec_ tr hr
  have hc : Continuous (fderiv ℝ (UnforcedLeray.B0238.Ec tr r)) :=
    hE.continuous_fderiv (by norm_num)
  unfold UnforcedLeray.B0579.pd
  exact hc.clm_apply continuous_const

theorem pd_eq_zero_of_band {f : ℝ × ℝ → ℝ} {Rb : ℝ}
    (hf : ∀ x : ℝ × ℝ, Rb < |x.2| → f x = 0) (j : Fin 2) (x : ℝ × ℝ) (hx : Rb < |x.2|) :
    UnforcedLeray.B0579.pd j f x = 0 := by
  have hopen : IsOpen {y : ℝ × ℝ | Rb < |y.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hx) (fun y hy => hf y hy)
  unfold UnforcedLeray.B0579.pd
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

theorem lapP_eq_zero_of_band {φ : ℝ × ℝ → ℝ} {Rb : ℝ}
    (hφ : ∀ x : ℝ × ℝ, Rb < |x.2| → φ x = 0) (x : ℝ × ℝ) (hx : Rb < |x.2|) :
    UnforcedLeray.Short.IIIa.lapP φ x = 0 := by
  have h0 := pd_eq_zero_of_band (f := UnforcedLeray.B0579.pd 0 φ)
    (fun y hy => pd_eq_zero_of_band hφ 0 y hy) 0 x hx
  have h1 := pd_eq_zero_of_band (f := UnforcedLeray.B0579.pd 1 φ)
    (fun y hy => pd_eq_zero_of_band hφ 1 y hy) 1 x hx
  unfold UnforcedLeray.Short.IIIa.lapP
  rw [h0, h1]
  simp

/-- A continuous function vanishing outside the band `|η| ≤ Rb` is bounded on the cell. -/
theorem bdd_cell_of_band {c Rb : ℝ} {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    (hz : ∀ x : ℝ × ℝ, Rb < |x.2| → g x = 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ UnforcedLeray.B0579.cell c, ‖g x‖ ≤ A := by
  have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-Rb) Rb) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max A 0, le_max_right _ _, fun x hx => ?_⟩
  simp only [UnforcedLeray.B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hx
  by_cases h : |x.2| ≤ Rb
  · exact (hA x ⟨⟨hx.1, hx.2.le⟩, abs_le.1 h⟩).trans (le_max_left _ _)
  · push_neg at h
    rw [hz x h, norm_zero]
    exact le_max_right _ _

/-! ### The real Biot–Savart velocity of `X_{m,c}` elements -/

section Kc

variable {c m : ℝ} [hm : Fact (1 < m)] [hc : Fact (0 < c)]

theorem norm_reX_le (f : XAmb c m) : ‖reX f‖ ≤ ‖f‖ := by
  have h := ContinuousLinearMap.norm_compLp_le (Complex.reCLM : ℂ →L[ℝ] ℝ) f
  rw [Complex.reCLM_norm, one_mul] at h
  exact h

theorem rbs_congr {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) {u v : UnforcedLeray.B0579.X c m}
    (h : u = v) (hu : ∫ x in UnforcedLeray.B0579.cell c, u x = 0)
    (hv : ∫ x in UnforcedLeray.B0579.cell c, v x = 0) :
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm u hu =
      UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm v hv := by
  subst h
  rfl

theorem kcLp_add (w z : Xmc c m) : kcLp (w + z) = kcLp w + kcLp z := by
  unfold kcLp
  have hR : reX (w + z).1 = reX w.1 + reX z.1 := by
    unfold reX
    exact (Complex.reCLM.compLpL 2 (UnforcedLeray.B0579.cellMeasure c m)).map_add _ _
  have hsum : ∫ x in UnforcedLeray.B0579.cell c, (reX w.1 + reX z.1) x = 0 := by
    rw [← hR]
    exact reX_circ (w + z)
  exact (rbs_congr one_le_of_fact hR (reX_circ (w + z)) hsum).trans
    (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart_add
      one_le_of_fact (reX w.1) (reX z.1) (reX_circ w) (reX_circ z) hsum)

theorem kcLp_smul (a : ℝ) (w : Xmc c m) : kcLp (a • w) = a • kcLp w := by
  unfold kcLp
  have hR : reX (a • w).1 = a • reX w.1 := by
    unfold reX
    exact (Complex.reCLM.compLpL 2 (UnforcedLeray.B0579.cellMeasure c m)).map_smul a _
  have hsmul : ∫ x in UnforcedLeray.B0579.cell c, (a • reX w.1) x = 0 := by
    rw [← hR]
    exact reX_circ (a • w)
  exact (rbs_congr one_le_of_fact hR (reX_circ (a • w)) hsmul).trans
    (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart_smul
      one_le_of_fact a (reX w.1) (reX_circ w) hsmul)

theorem norm_kcLp_le (w : Xmc c m) : ‖kcLp w‖ ≤ 5 * (1 + c) * ‖w‖ := by
  unfold kcLp
  have hc0 : 0 < c := hc.out
  have h1 := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_realBiotSavart_le
    one_le_of_fact (reX w.1) (reX_circ w)
  have h2 : ‖reX w.1‖ ≤ ‖w‖ := norm_reX_le (w : XAmb c m)
  have h3 : 0 ≤ 5 * (1 + c) := by linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h3)

theorem kcC_add_ae (w z : Xmc c m) (j : Fin 2) :
    ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      kcC (w + z) x j = kcC w x j + kcC z x j := by
  filter_upwards [kcMer_ae (w + z), kcMer_ae w, kcMer_ae z,
    Lp.coeFn_add (kcLp w) (kcLp z)] with x h1 h2 h3 h4
  have e : kcMer (w + z) x = kcMer w x + kcMer z x := by
    rw [h1, kcLp_add, h2, h3]
    simpa using h4
  unfold kcC
  rw [e]
  simp

theorem kcC_smul_ae (a : ℝ) (w : Xmc c m) (j : Fin 2) :
    ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      kcC (a • w) x j = (a : ℂ) * kcC w x j := by
  filter_upwards [kcMer_ae (a • w), kcMer_ae w, Lp.coeFn_smul a (kcLp w)] with x h1 h2 h3
  have e : kcMer (a • w) x = a • kcMer w x := by
    rw [h1, kcLp_smul, h2]
    simpa using h3
  unfold kcC
  rw [e]
  simp [Complex.ofReal_mul]

end Kc


/-! ### Hölder on a set of finite measure, for `L²(Merid)` -/

theorem holder_box {μ : Measure (ℝ × ℝ)} (f : Lp Merid 2 μ) {S : Set (ℝ × ℝ)} (hS : μ S < ⊤) :
    ∫ x in S, ‖f x‖ ∂μ ≤ (μ S).toReal ^ (1 - 1 / (2 : ℝ≥0∞).toReal) * ‖f‖ := by
  haveI hp1 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  haveI : Fact (μ S < ⊤) := ⟨hS⟩
  have hfS : MemLp (f : ℝ × ℝ → Merid) 2 (μ.restrict S) := (Lp.memLp f).restrict S
  have hint : IntegrableOn (f : ℝ × ℝ → Merid) S μ := hfS.integrable hp1.out
  have h1 : ∫ x in S, ‖f x‖ ∂μ = (eLpNorm f 1 (μ.restrict S)).toReal := by
    rw [integral_norm_eq_lintegral_enorm hint.1, eLpNorm_one_eq_lintegral_enorm]
  rw [h1]
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict S) (p := 1) (q := 2)
    hp1.out (Lp.aestronglyMeasurable f).restrict
  rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one] at h2
  have h3 : eLpNorm f 2 (μ.restrict S) ≤ eLpNorm f 2 μ :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hfin : eLpNorm f 2 μ * μ S ^ (1 - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS.ne)
  calc (eLpNorm f 1 (μ.restrict S)).toReal
      ≤ (eLpNorm f 2 μ * μ S ^ (1 - 1 / (2 : ℝ≥0∞).toReal)).toReal :=
        ENNReal.toReal_mono hfin (h2.trans (by gcongr))
    _ = (μ S).toReal ^ (1 - 1 / (2 : ℝ≥0∞).toReal) * ‖f‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, Lp.norm_def, mul_comm]

/-! ### The box and bounded-coefficient integrals -/

/-- The finite box `[-c/2, c/2] × [-Rb, Rb]` inside the cell. -/
def cellBox (c Rb : ℝ) : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-Rb) Rb

theorem cellBox_compact (c Rb : ℝ) : IsCompact (cellBox c Rb) :=
  isCompact_Icc.prod isCompact_Icc

section Gen

variable {c m : ℝ} [hm : Fact (1 < m)] [hc : Fact (0 < c)]

theorem integrableOn_xFn_mul_bdd {g : ℝ × ℝ → ℂ} {A : ℝ} (hgm : Continuous g)
    (hgb : ∀ x ∈ UnforcedLeray.B0579.cell c, ‖g x‖ ≤ A) (w : Xmc c m) :
    IntegrableOn (fun x => xFn w x * g x) (UnforcedLeray.B0579.cell c) := by
  unfold IntegrableOn
  refine Integrable.mono' ((xFn_integrableOn w).norm.const_mul A)
    ((xFn_integrableOn w).1.mul hgm.aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem (UnforcedLeray.B0579.measurableSet_cell c) fun x hx => ?_
  rw [norm_mul, mul_comm A]
  exact mul_le_mul_of_nonneg_left (hgb x hx) (norm_nonneg _)

theorem exists_clm_xFn {g : ℝ × ℝ → ℂ} {A : ℝ} (hA0 : 0 ≤ A) (hgm : Continuous g)
    (hgb : ∀ x ∈ UnforcedLeray.B0579.cell c, ‖g x‖ ≤ A) :
    ∃ Λ : Xmc c m →L[ℝ] ℂ, ∀ w : Xmc c m,
      ∫ x in UnforcedLeray.B0579.cell c, xFn w x * g x = Λ w := by
  let L : Xmc c m →ₗ[ℝ] ℂ :=
    { toFun := fun w => ∫ x in UnforcedLeray.B0579.cell c, xFn w x * g x
      map_add' := fun w z => by
        rw [← integral_add (integrableOn_xFn_mul_bdd hgm hgb w)
          (integrableOn_xFn_mul_bdd hgm hgb z)]
        refine integral_congr_ae ?_
        filter_upwards [xFn_add w z] with x hx
        rw [hx]
        ring
      map_smul' := fun a w => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [xFn_rsmul a w] with x hx
        rw [hx, Complex.real_smul]
        ring }
  refine ⟨L.mkContinuous (A * (UnforcedLeray.B0592.weightConst m).toReal) ?_, fun w => rfl⟩
  intro w
  have hI : Integrable (fun y => A * ‖xFn w y‖) (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    (xFn_integrableOn w).norm.const_mul A
  have hle : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      ‖xFn w x * g x‖ ≤ A * ‖xFn w x‖ := by
    refine ae_restrict_of_forall_mem (UnforcedLeray.B0579.measurableSet_cell c) fun x hx => ?_
    rw [norm_mul, mul_comm A]
    exact mul_le_mul_of_nonneg_left (hgb x hx) (norm_nonneg _)
  calc ‖L w‖ = ‖∫ x in UnforcedLeray.B0579.cell c, xFn w x * g x‖ := rfl
    _ ≤ ∫ x in UnforcedLeray.B0579.cell c, ‖xFn w x * g x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in UnforcedLeray.B0579.cell c, A * ‖xFn w x‖ :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hI hle
    _ = A * ∫ x in UnforcedLeray.B0579.cell c, ‖xFn w x‖ := integral_const_mul A _
    _ ≤ A * ((UnforcedLeray.B0592.weightConst m).toReal * ‖w‖) :=
        mul_le_mul_of_nonneg_left (lintegral_norm_cell_le w) hA0
    _ = A * (UnforcedLeray.B0592.weightConst m).toReal * ‖w‖ := by ring

/-- Pointwise bound of the Biot–Savart integrand by an indicator of the box. -/
theorem kcC_ae_bound {g : ℝ × ℝ → ℂ} {Rb A : ℝ} (j : Fin 2)
    (hgb : ∀ x ∈ UnforcedLeray.B0579.cell c, ‖g x‖ ≤ A)
    (hgz : ∀ x : ℝ × ℝ, Rb < |x.2| → g x = 0) (w : Xmc c m) :
    ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      ‖kcC w x j * g x‖ ≤
        (cellBox c Rb).indicator (fun x => A * ‖(kcLp w : ℝ × ℝ → Merid) x‖) x := by
  filter_upwards [kcMer_ae w, ae_restrict_mem (UnforcedLeray.B0579.measurableSet_cell c)]
    with x hx hxc
  by_cases hb : x ∈ cellBox c Rb
  · rw [Set.indicator_of_mem hb]
    have hkc : ‖kcC w x j‖ ≤ ‖(kcLp w : ℝ × ℝ → Merid) x‖ := by
      have e : kcC w x j = (((kcLp w : ℝ × ℝ → Merid) x j : ℝ) : ℂ) := by
        unfold kcC
        rw [hx]
      rw [e, Complex.norm_real]
      exact PiLp.norm_apply_le _ j
    calc ‖kcC w x j * g x‖ = ‖kcC w x j‖ * ‖g x‖ := norm_mul _ _
      _ ≤ ‖(kcLp w : ℝ × ℝ → Merid) x‖ * A :=
          mul_le_mul hkc (hgb x hxc) (norm_nonneg _) (norm_nonneg _)
      _ = A * ‖(kcLp w : ℝ × ℝ → Merid) x‖ := mul_comm _ _
  · rw [Set.indicator_of_notMem hb]
    have hRb : Rb < |x.2| := by
      by_contra hcon
      push_neg at hcon
      apply hb
      simp only [UnforcedLeray.B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hxc
      exact ⟨⟨hxc.1, hxc.2.le⟩, abs_le.1 hcon⟩
    simp [hgz x hRb]

theorem integrableOn_kcC_mul_bdd {g : ℝ × ℝ → ℂ} {Rb A : ℝ} (j : Fin 2)
    (hgm : Continuous g) (hgb : ∀ x ∈ UnforcedLeray.B0579.cell c, ‖g x‖ ≤ A)
    (hgz : ∀ x : ℝ × ℝ, Rb < |x.2| → g x = 0) (w : Xmc c m) :
    IntegrableOn (fun x => kcC w x j * g x) (UnforcedLeray.B0579.cell c) := by
  have hboxm : MeasurableSet (cellBox c Rb) := (cellBox_compact c Rb).isClosed.measurableSet
  have hcellbox : (volume.restrict (UnforcedLeray.B0579.cell c)) (cellBox c Rb) < ⊤ :=
    lt_of_le_of_lt (Measure.le_iff'.1 Measure.restrict_le_self _) (cellBox_compact c Rb).measure_lt_top
  have hmem : MemLp (kcLp w : ℝ × ℝ → Merid) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    Lp.memLp (kcLp w)
  have hfinite : IsFiniteMeasure ((volume.restrict (UnforcedLeray.B0579.cell c)).restrict
      (cellBox c Rb)) := ⟨by rw [Measure.restrict_apply_univ]; exact hcellbox⟩
  have hL0 : Integrable (kcLp w : ℝ × ℝ → Merid)
      ((volume.restrict (UnforcedLeray.B0579.cell c)).restrict (cellBox c Rb)) :=
    (hmem.restrict (cellBox c Rb)).integrable one_le_two
  have hL : Integrable (fun x => ‖(kcLp w : ℝ × ℝ → Merid) x‖)
      ((volume.restrict (UnforcedLeray.B0579.cell c)).restrict (cellBox c Rb)) := hL0.norm
  have hI : Integrable ((cellBox c Rb).indicator (fun x => A * ‖(kcLp w : ℝ × ℝ → Merid) x‖))
      (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    (integrable_indicator_iff hboxm).2 (hL.const_mul A)
  have hmeas : AEStronglyMeasurable (fun x => kcC w x j * g x)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    have hp : Continuous (fun y : Merid => (((EuclideanSpace.proj j : Merid →L[ℝ] ℝ) y : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (EuclideanSpace.proj j : Merid →L[ℝ] ℝ).continuous
    have h1 : AEStronglyMeasurable (fun x => (((kcLp w : ℝ × ℝ → Merid) x j : ℝ) : ℂ))
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      hp.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (kcLp w))
    have h2 : AEStronglyMeasurable (fun x => kcC w x j)
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      h1.congr (by
        filter_upwards [kcMer_ae w] with x hx
        unfold kcC
        rw [hx])
    exact h2.mul hgm.aestronglyMeasurable
  unfold IntegrableOn
  exact Integrable.mono' hI hmeas (kcC_ae_bound j hgb hgz w)

theorem exists_clm_kcC {g : ℝ × ℝ → ℂ} {Rb A : ℝ} (j : Fin 2) (hA0 : 0 ≤ A)
    (hgm : Continuous g) (hgb : ∀ x ∈ UnforcedLeray.B0579.cell c, ‖g x‖ ≤ A)
    (hgz : ∀ x : ℝ × ℝ, Rb < |x.2| → g x = 0) :
    ∃ Λ : Xmc c m →L[ℝ] ℂ, ∀ w : Xmc c m,
      ∫ x in UnforcedLeray.B0579.cell c, kcC w x j * g x = Λ w := by
  let L : Xmc c m →ₗ[ℝ] ℂ :=
    { toFun := fun w => ∫ x in UnforcedLeray.B0579.cell c, kcC w x j * g x
      map_add' := fun w z => by
        rw [← integral_add (integrableOn_kcC_mul_bdd j hgm hgb hgz w)
          (integrableOn_kcC_mul_bdd j hgm hgb hgz z)]
        refine integral_congr_ae ?_
        filter_upwards [kcC_add_ae w z j] with x hx
        rw [hx]
        ring
      map_smul' := fun a w => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [kcC_smul_ae a w j] with x hx
        rw [hx, Complex.real_smul]
        ring }
  have hK0 : 0 ≤ ((volume.restrict (UnforcedLeray.B0579.cell c)) (cellBox c Rb)).toReal ^
      (1 - 1 / (2 : ℝ≥0∞).toReal) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hcellbox : (volume.restrict (UnforcedLeray.B0579.cell c)) (cellBox c Rb) < ⊤ :=
    lt_of_le_of_lt (Measure.le_iff'.1 Measure.restrict_le_self _) (cellBox_compact c Rb).measure_lt_top
  have hboxm : MeasurableSet (cellBox c Rb) := (cellBox_compact c Rb).isClosed.measurableSet
  refine ⟨L.mkContinuous (A * (((volume.restrict (UnforcedLeray.B0579.cell c)) (cellBox c Rb)).toReal ^
      (1 - 1 / (2 : ℝ≥0∞).toReal)) * (5 * (1 + c))) ?_, fun w => rfl⟩
  intro w
  have hbound := kcC_ae_bound (c := c) (m := m) (Rb := Rb) (A := A) (g := g) j hgb hgz w
  have hI : Integrable ((cellBox c Rb).indicator (fun x => A * ‖(kcLp w : ℝ × ℝ → Merid) x‖))
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    have hmem : MemLp (kcLp w : ℝ × ℝ → Merid) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      Lp.memLp (kcLp w)
    have hfinite : IsFiniteMeasure ((volume.restrict (UnforcedLeray.B0579.cell c)).restrict
        (cellBox c Rb)) := ⟨by rw [Measure.restrict_apply_univ]; exact hcellbox⟩
    have hL0 : Integrable (kcLp w : ℝ × ℝ → Merid)
        ((volume.restrict (UnforcedLeray.B0579.cell c)).restrict (cellBox c Rb)) :=
      (hmem.restrict (cellBox c Rb)).integrable one_le_two
    exact (integrable_indicator_iff hboxm).2 (hL0.norm.const_mul A)
  calc ‖L w‖ = ‖∫ x in UnforcedLeray.B0579.cell c, kcC w x j * g x‖ := rfl
    _ ≤ ∫ x in UnforcedLeray.B0579.cell c, ‖kcC w x j * g x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in UnforcedLeray.B0579.cell c,
          (cellBox c Rb).indicator (fun x => A * ‖(kcLp w : ℝ × ℝ → Merid) x‖) x :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hI hbound
    _ = ∫ x in cellBox c Rb, A * ‖(kcLp w : ℝ × ℝ → Merid) x‖
          ∂(volume.restrict (UnforcedLeray.B0579.cell c)) := by
        rw [integral_indicator hboxm]
    _ = A * ∫ x in cellBox c Rb, ‖(kcLp w : ℝ × ℝ → Merid) x‖
          ∂(volume.restrict (UnforcedLeray.B0579.cell c)) := integral_const_mul A _
    _ ≤ A * ((((volume.restrict (UnforcedLeray.B0579.cell c)) (cellBox c Rb)).toReal ^
          (1 - 1 / (2 : ℝ≥0∞).toReal)) * ‖kcLp w‖) :=
        mul_le_mul_of_nonneg_left (holder_box (kcLp w) hcellbox) hA0
    _ ≤ A * ((((volume.restrict (UnforcedLeray.B0579.cell c)) (cellBox c Rb)).toReal ^
          (1 - 1 / (2 : ℝ≥0∞).toReal)) * (5 * (1 + c) * ‖w‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_kcLp_le w) hK0) hA0
    _ = A * (((volume.restrict (UnforcedLeray.B0579.cell c)) (cellBox c Rb)).toReal ^
          (1 - 1 / (2 : ℝ≥0∞).toReal)) * (5 * (1 + c)) * ‖w‖ := by ring

end Gen

/-! ### The theorem -/

theorem fcvEllCLM : FcvEllCLM := by
  intro ν c m _ _ tr φ hφ r hr
  obtain ⟨R, hR⟩ := hφ.band
  have hφR : ∀ x : ℝ × ℝ, |R| < |x.2| → φ x = 0 :=
    fun x hx => hR x (lt_of_le_of_lt (le_abs_self R) hx)
  have hvc : Continuous (tr.v r) := (UnforcedLeray.B0238.contDiff_Vc tr hr.le).continuous
  have hv0 : Continuous (fun x => tr.v r x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp hvc
  have hv1 : Continuous (fun x => tr.v r x 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp hvc
  have hφc : Continuous φ := hφ.continuous
  have hd0 : Continuous (UnforcedLeray.B0579.pd 0 φ) := (hφ.pd 0).continuous
  have hd1 : Continuous (UnforcedLeray.B0579.pd 1 φ) := (hφ.pd 1).continuous
  have hdd : Continuous (UnforcedLeray.Short.IIIa.lapP φ) := by
    unfold UnforcedLeray.Short.IIIa.lapP
    exact ((hφ.pd 0).pd 0).continuous.add ((hφ.pd 1).pd 1).continuous
  -- the coefficients of `flowIntegrand`
  set g0 : ℝ × ℝ → ℂ := fun x => ((ν * UnforcedLeray.Short.IIIa.lapP φ x +
      (tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x) : ℝ) : ℂ)
    with hg0
  set g1 : ℝ × ℝ → ℂ := fun x =>
    ((UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x * φ x : ℝ) : ℂ) with hg1
  set g2 : ℝ × ℝ → ℂ := fun x =>
    ((UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x * φ x : ℝ) : ℂ) with hg2
  have hg0c : Continuous g0 := by
    refine Complex.continuous_ofReal.comp ?_
    exact (continuous_const.mul hdd).add ((hv0.mul hd0).add (hv1.mul hd1))
  have hg1c : Continuous g1 := by
    refine Complex.continuous_ofReal.comp ?_
    exact (continuous_pd_Ec_ tr hr 0).mul hφc
  have hg2c : Continuous g2 := by
    refine Complex.continuous_ofReal.comp ?_
    exact (continuous_pd_Ec_ tr hr 1).mul hφc
  have hg0z : ∀ x : ℝ × ℝ, |R| < |x.2| → g0 x = 0 := by
    intro x hx
    rw [hg0]
    simp only
    rw [lapP_eq_zero_of_band hφR x hx, pd_eq_zero_of_band hφR 0 x hx,
      pd_eq_zero_of_band hφR 1 x hx]
    simp
  have hg1z : ∀ x : ℝ × ℝ, |R| < |x.2| → g1 x = 0 := by
    intro x hx
    rw [hg1]
    simp only
    rw [hφR x hx]
    simp
  have hg2z : ∀ x : ℝ × ℝ, |R| < |x.2| → g2 x = 0 := by
    intro x hx
    rw [hg2]
    simp only
    rw [hφR x hx]
    simp
  obtain ⟨A0, hA0, hA0b⟩ := bdd_cell_of_band (c := c) hg0c hg0z
  obtain ⟨A1, hA1, hA1b⟩ := bdd_cell_of_band (c := c) hg1c hg1z
  obtain ⟨A2, hA2, hA2b⟩ := bdd_cell_of_band (c := c) hg2c hg2z
  obtain ⟨Λ0, hΛ0⟩ := exists_clm_xFn (c := c) (m := m) hA0 hg0c hA0b
  obtain ⟨Λ1, hΛ1⟩ := exists_clm_kcC (c := c) (m := m) (Rb := |R|) 0 hA1 hg1c hA1b hg1z
  obtain ⟨Λ2, hΛ2⟩ := exists_clm_kcC (c := c) (m := m) (Rb := |R|) 1 hA2 hg2c hA2b hg2z
  refine ⟨Λ0 - Λ1 - Λ2, fun w => ?_⟩
  have hfun : (fun y => IIIa.flowIntegrand tr (xFn w) (kcC w) r φ y) =
      fun y => xFn w y * g0 y - (kcC w y 0 * g1 y + kcC w y 1 * g2 y) := by
    funext y
    simp only [IIIa.flowIntegrand, hg0, hg1, hg2]
    push_cast
    ring
  have i0 := integrableOn_xFn_mul_bdd (c := c) (m := m) hg0c hA0b w
  have i1 := integrableOn_kcC_mul_bdd (c := c) (m := m) (Rb := |R|) 0 hg1c hA1b hg1z w
  have i2 := integrableOn_kcC_mul_bdd (c := c) (m := m) (Rb := |R|) 1 hg2c hA2b hg2z w
  have i12 : IntegrableOn (fun y => kcC w y 0 * g1 y + kcC w y 1 * g2 y)
      (UnforcedLeray.B0579.cell c) := i1.add i2
  show ∫ y in UnforcedLeray.B0579.cell c, IIIa.flowIntegrand tr (xFn w) (kcC w) r φ y = _
  rw [hfun, integral_sub i0 i12, integral_add i1 i2, hΛ0 w, hΛ1 w, hΛ2 w]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
