import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.Coef

/-!
# `FcvEllFixed`: continuity of `r ↦ ℓ_r(ω)` for fixed `ω` (source 2819-2836)

For fixed `ω`, `ℓ_r ω = ∫_cell flowIntegrand tr (xFn ω) (kcC ω) r φ y`.  The integrand is
continuous in `r` on `(0,∞)` for each `y` (`IIIa.train_joint_cont`), and on `0 ≤ r ≤ T` it is
dominated by `A |xFn ω y| + B 1_{|y.2| ≤ R} (|kcC ω y 0| + |kcC ω y 1|)` (`fcvEllCoef`, the band
radius `R` of `φ`).  The `kcC` term is integrable on the cell because `φ` is supported in the band
`|η| ≤ R`, which has finite measure intersected with the cell, and `kcLp ω` is in `L²`.
Dominated convergence (`continuousWithinAt_of_dominated`) gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `x ↦ kcC ω x j` is a.e.-strongly measurable on any `S ⊆ cell`. -/
theorem fxF_kcC_aesm {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ω : Xmc c m) (j : Fin 2)
    {S : Set (ℝ × ℝ)} (hS : S ⊆ B0579.cell c) :
    AEStronglyMeasurable (fun x => kcC ω x j) (volume.restrict S) := by
  have hle : volume.restrict S ≤ B0581.cellVol c := Measure.restrict_mono hS le_rfl
  have hf : MemLp (kcLp ω : ℝ × ℝ → Merid) 2 (volume.restrict S) :=
    (Lp.memLp (kcLp ω)).mono_measure hle
  have hae : (fun x => kcC ω x j) =ᵐ[volume.restrict S]
      fun x => (((kcLp ω : ℝ × ℝ → Merid) x j : ℝ) : ℂ) := by
    have h := ae_restrict_of_ae_restrict_of_subset hS (kcMer_ae ω)
    filter_upwards [h] with x hx
    show ((kcMer ω x j : ℝ) : ℂ) = _
    rw [hx]
  refine AEStronglyMeasurable.congr ?_ hae.symm
  exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj j : Merid →L[ℝ] ℝ).continuous
    ).comp_aestronglyMeasurable hf.1

/-- `x ↦ ‖kcC ω x j‖` is integrable on any `S ⊆ cell` of finite measure. -/
theorem fxF_kcC_norm_integrable {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ω : Xmc c m)
    (j : Fin 2) {S : Set (ℝ × ℝ)} (hS : S ⊆ B0579.cell c) (hSfin : volume S ≠ ⊤) :
    Integrable (fun x => ‖kcC ω x j‖) (volume.restrict S) := by
  have hle : volume.restrict S ≤ B0581.cellVol c := Measure.restrict_mono hS le_rfl
  have hf : MemLp (kcLp ω : ℝ × ℝ → Merid) 2 (volume.restrict S) :=
    (Lp.memLp (kcLp ω)).mono_measure hle
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSfin
  have hg : Integrable (fun x => ‖(kcLp ω : ℝ × ℝ → Merid) x‖) (volume.restrict S) :=
    hf.norm.integrable one_le_two
  refine Integrable.mono' hg (fxF_kcC_aesm ω j hS).norm ?_
  have h := ae_restrict_of_ae_restrict_of_subset hS (kcMer_ae ω)
  filter_upwards [h] with x hx
  have e1 : ‖kcC ω x j‖ = ‖kcMer ω x j‖ := by
    simp [kcC, Complex.norm_real]
  rw [Real.norm_of_nonneg (norm_nonneg _), e1, hx]
  exact PiLp.norm_apply_le _ j

/-- The finite-measure band `cell ∩ {|η| ≤ R}`. -/
theorem fxF_band_fin (c R : ℝ) : volume (B0579.cell c ∩ {z : ℝ × ℝ | |z.2| ≤ R}) ≠ ⊤ := by
  have hK : B0579.cell c ∩ {z : ℝ × ℝ | |z.2| ≤ R} ⊆
      Icc (-(c / 2)) (c / 2) ×ˢ Icc (-|R|) |R| := by
    intro y hy
    have h1 := hy.1
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at h1
    have h2 : |y.2| ≤ |R| := (show |y.2| ≤ R from hy.2).trans (le_abs_self R)
    exact ⟨⟨h1.1, h1.2.le⟩, abs_le.1 h2⟩
  exact ((measure_mono hK).trans_lt
    ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)).ne

/-- Pointwise domination of the flow integrand on the cell, for `r ∈ [0,T]` with the bounds of
`fcvEllCoef`. -/
theorem fxF_point_bound {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℝ) (R : ℝ)
    (hR : ∀ z : ℝ × ℝ, R < |z.2| → φ z = 0) (ω : Xmc c m) (A B : ℝ) (r : ℝ) (y : ℝ × ℝ)
    (hA : |ν * IIIa.lapP φ y + (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y)| ≤ A)
    (hB : ∀ k : Fin 2, |B0579.pd k (UnforcedLeray.B0238.Ec tr r) y * φ y| ≤ B) :
    ‖IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y‖ ≤ A * ‖xFn ω y‖ +
      B * ({z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖) y) := by
  unfold IIIa.flowIntegrand
  have h1 : ‖xFn ω y * (((ν * IIIa.lapP φ y +
      (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y) : ℝ)) : ℂ)‖ ≤
      A * ‖xFn ω y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm A]
    exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)
  have h2 : ‖(kcC ω y 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) y : ℂ) +
      kcC ω y 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) y : ℂ)) * (φ y : ℂ)‖ ≤
      B * ({z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖) y) := by
    by_cases hb : |y.2| ≤ R
    · have hind : {z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖) y =
          ‖kcC ω y 0‖ + ‖kcC ω y 1‖ :=
        Set.indicator_of_mem (show y ∈ {z : ℝ × ℝ | |z.2| ≤ R} from hb) _
      rw [hind]
      calc ‖(kcC ω y 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) y : ℂ) +
            kcC ω y 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) y : ℂ)) * (φ y : ℂ)‖
          = ‖kcC ω y 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) y * φ y : ℝ) : ℂ) +
              kcC ω y 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) y * φ y : ℝ) : ℂ)‖ := by
            congr 1
            push_cast
            ring
        _ ≤ ‖kcC ω y 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) y * φ y : ℝ) : ℂ)‖ +
              ‖kcC ω y 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) y * φ y : ℝ) : ℂ)‖ :=
            norm_add_le _ _
        _ = ‖kcC ω y 0‖ * |B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) y * φ y| +
              ‖kcC ω y 1‖ * |B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) y * φ y| := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ‖kcC ω y 0‖ * B + ‖kcC ω y 1‖ * B :=
            add_le_add (mul_le_mul_of_nonneg_left (hB 0) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (hB 1) (norm_nonneg _))
        _ = B * (‖kcC ω y 0‖ + ‖kcC ω y 1‖) := by ring
    · have hind : {z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖) y = 0 :=
        Set.indicator_of_notMem (show y ∉ {z : ℝ × ℝ | |z.2| ≤ R} from hb) _
      have hp : φ y = 0 := hR y (not_le.1 hb)
      rw [hind, hp]
      simp
  calc _ ≤ ‖xFn ω y * (((ν * IIIa.lapP φ y +
          (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y) : ℝ)) : ℂ)‖ +
        ‖(kcC ω y 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) y : ℂ) +
          kcC ω y 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) y : ℂ)) * (φ y : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- Continuity in `r` on `(0,∞)` of the flow integrand, for each fixed `y`. -/
theorem fxF_cont_r {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℝ) (ω : Xmc c m) (y : ℝ × ℝ) :
    ContinuousOn (fun r => IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y) (Ioi 0) := by
  have hv : ∀ k : Fin 2, ContinuousOn (fun r : ℝ => tr.v r y k) (Ioi 0) := fun k => by
    have h1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) (Ici 0 ×ˢ univ) :=
      train_coord_cont_aux tr k
    exact h1.comp (f := fun r : ℝ => (r, y)) (s := Ioi 0)
      (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => mk_mem_prod (mem_Ici.2 (le_of_lt hr)) (mem_univ _))
  have hD : ∀ k : Fin 2, ContinuousOn
      (fun r : ℝ => B0579.pd k (UnforcedLeray.B0238.Ec tr r) y) (Ioi 0) := fun k => by
    have h1 := (IIIa.train_joint_cont tr).2 k
    exact h1.comp (f := fun r : ℝ => (r, y)) (s := Ioi 0)
      (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => mk_mem_prod (mem_Ici.2 (le_of_lt hr)) (mem_univ _))
  have hA : ContinuousOn (fun r : ℝ => ((ν * IIIa.lapP φ y +
      (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y) : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.add (((hv 0).mul continuousOn_const).add
        ((hv 1).mul continuousOn_const)))
  unfold IIIa.flowIntegrand
  exact (continuousOn_const.mul hA).sub
    (((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hD 0))).add
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hD 1)))).mul
      continuousOn_const)

/-- Strong measurability on the cell of the flow integrand, for `r > 0`. -/
theorem fxF_aesm {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℝ) (hφ : B0579.IsCylTest c φ)
    (ω : Xmc c m) (r : ℝ) (hr : 0 < r) :
    AEStronglyMeasurable (fun y => IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y)
      (volume.restrict (B0579.cell c)) := by
  have hvc : ∀ k : Fin 2, Continuous (fun y : ℝ × ℝ => tr.v r y k) := fun k => by
    have h1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) (Ici 0 ×ˢ univ) :=
      train_coord_cont_aux tr k
    have h2 := h1.comp (f := fun y : ℝ × ℝ => (r, y)) (s := univ)
      (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => mk_mem_prod (mem_Ici.2 (le_of_lt hr)) (mem_univ _))
    exact continuousOn_univ.1 h2
  have hdc : ∀ k : Fin 2, Continuous (fun y : ℝ × ℝ => B0579.pd k (UnforcedLeray.B0238.Ec tr r) y) :=
    fun k => by
    have h1 := (IIIa.train_joint_cont tr).2 k
    have h2 := h1.comp (f := fun y : ℝ × ℝ => (r, y)) (s := univ)
      (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => mk_mem_prod (mem_Ici.2 (le_of_lt hr)) (mem_univ _))
    exact continuousOn_univ.1 h2
  have hlap : Continuous (IIIa.lapP φ) :=
    ((hφ.pd 0).pd 0).continuous.add ((hφ.pd 1).pd 1).continuous
  have hPc : Continuous (fun y => ((ν * IIIa.lapP φ y +
      (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_const.mul hlap).add
      (((hvc 0).mul (hφ.pd 0).continuous).add ((hvc 1).mul (hφ.pd 1).continuous)))
  have hφc : Continuous (fun y => ((φ y : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hx : AEStronglyMeasurable (xFn ω) (volume.restrict (B0579.cell c)) :=
    (xFn_integrableOn ω).1
  have hu0 := fxF_kcC_aesm ω 0 (subset_refl (B0579.cell c))
  have hu1 := fxF_kcC_aesm ω 1 (subset_refl (B0579.cell c))
  unfold IIIa.flowIntegrand
  exact (hx.mul hPc.aestronglyMeasurable).sub
    (((hu0.mul (Complex.continuous_ofReal.comp (hdc 0)).aestronglyMeasurable).add
      (hu1.mul (Complex.continuous_ofReal.comp (hdc 1)).aestronglyMeasurable)).mul
      hφc.aestronglyMeasurable)

/-- **`r ↦ ℓ_r(ω)` is continuous for fixed `ω`** on `(0,∞)` (dominated convergence over the cell
with the bounds of `fcvEllCoef`; joint continuity `IIIa.train_joint_cont`). -/
theorem fcvEllFixed : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FcvEllFixed := by
  intro ν c m _ _ tr φ hφ ω r0 hr0
  obtain ⟨R, hR⟩ := hφ.band
  obtain ⟨A, B, hAB⟩ := (fcvEllCoef : FcvEllCoef) ν c tr φ hφ (r0 + 1)
  have hband : MeasurableSet {z : ℝ × ℝ | |z.2| ≤ R} :=
    measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const
  have hind : Integrable
      ({z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖))
      (volume.restrict (B0579.cell c)) := by
    rw [integrable_indicator_iff hband]
    unfold IntegrableOn
    rw [Measure.restrict_restrict hband]
    have hS : {z : ℝ × ℝ | |z.2| ≤ R} ∩ B0579.cell c ⊆ B0579.cell c := inter_subset_right
    have hfin' : volume ({z : ℝ × ℝ | |z.2| ≤ R} ∩ B0579.cell c) ≠ ⊤ := by
      rw [inter_comm]
      exact fxF_band_fin c R
    exact (fxF_kcC_norm_integrable ω 0 hS hfin').add (fxF_kcC_norm_integrable ω 1 hS hfin')
  have hbnd : Integrable (fun y => A * ‖xFn ω y‖ +
      B * {z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖) y)
      (volume.restrict (B0579.cell c)) :=
    ((xFn_integrableOn ω).norm.const_mul A).add (hind.const_mul B)
  have hT : ∀ᶠ r in 𝓝[Ioi 0] r0, r ∈ Iio (r0 + 1) :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (lt_add_one r0))
  have hbound : ∀ᶠ r in 𝓝[Ioi 0] r0, ∀ᵐ y ∂(volume.restrict (B0579.cell c)),
      ‖IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y‖ ≤ A * ‖xFn ω y‖ +
        B * ({z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖) y) := by
    filter_upwards [hT, self_mem_nhdsWithin] with r hr1 hr2
    have hr1' : r < r0 + 1 := hr1
    have hr2' : (0 : ℝ) < r := hr2
    refine cell_ae_of_mem fun y hy => ?_
    have hb := hAB r ⟨hr2'.le, hr1'.le⟩ y hy
    exact fxF_point_bound tr φ R hR ω A B r y hb.1 hb.2
  have hmeas : ∀ᶠ r in 𝓝[Ioi 0] r0, AEStronglyMeasurable
      (fun y => IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y) (volume.restrict (B0579.cell c)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact fxF_aesm tr φ hφ ω r (show (0 : ℝ) < r from hr)
  have hcont : ∀ᵐ y ∂(volume.restrict (B0579.cell c)),
      ContinuousWithinAt (fun r => IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y) (Ioi 0) r0 :=
    ae_of_all _ (fun y => fxF_cont_r tr φ ω y r0 hr0)
  unfold ellFn
  exact continuousWithinAt_of_dominated (F := fun r y => IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y)
    hmeas hbound hbnd hcont

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
