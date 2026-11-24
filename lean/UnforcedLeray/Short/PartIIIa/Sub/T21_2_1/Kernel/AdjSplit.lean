import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# Part III-a, `PartIII-a:T21/2/1/2/2`: the near/far split of the adjoint `K_d^T F`

Source of record: `the November 2 reference manuscript` lines 3052-3056
("split the Biot-Savart kernel into its integrable near part and bounded far part").

Proof of `kerAdjSplit_of` from `KerNearFar`: replace `F j` by its `d`-periodic, strongly
measurable representative `Fp j`; by oddness and the periodic reflection
`∫_cell G(y - w) dw = ∫_cell G`, `K_d^T F (y) = -∑_j ∫_cell K_j(w) Fp_j(y - w) dw`; split
`K_j = kN_j + kF_j` (near/far); the near convolution is bounded in `L²` by Minkowski
(`Cyl.eLpNorm_conv_periodic_le`), the far one pointwise by `‖F‖_{L¹}`, and the near convolution
integrals converge for a.e. `y` by Tonelli.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace AdjSplitAux

open UnforcedLeray

theorem cell_eq (d : ℝ) : B0579.cell d = Cyl.cell d := by
  unfold B0579.cell Cyl.cell
  rw [neg_div]

theorem measurable_toIcoMod {d : ℝ} (hd : 0 < d) (a : ℝ) : Measurable (toIcoMod hd a) := by
  have : toIcoMod hd a = fun b => b - (⌊(b - a) / d⌋ : ℤ) • d := by
    funext b
    rw [toIcoMod, toIcoDiv_eq_floor]
  rw [this]
  exact measurable_id.sub ((Int.measurable_floor.comp ((measurable_id.sub_const a).div_const d)).smul_const d)

/-- A strongly measurable periodic representative on the cell. -/
theorem periodic_rep {d : ℝ} (hd : 0 < d) {f : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Cyl.cell d))) :
    ∃ g : ℝ × ℝ → ℂ, StronglyMeasurable g ∧ Cyl.IsPeriodic d g ∧
      g =ᵐ[volume.restrict (Cyl.cell d)] f := by
  set fm := hf.mk f with hfm
  have hφ : Measurable fun x : ℝ × ℝ => (toIcoMod hd (-(d / 2)) x.1, x.2) :=
    ((measurable_toIcoMod hd _).comp measurable_fst).prodMk measurable_snd
  refine ⟨fun x => fm (toIcoMod hd (-(d / 2)) x.1, x.2),
    hf.stronglyMeasurable_mk.comp_measurable hφ, ?_, ?_⟩
  · intro z
    show fm (toIcoMod hd (-(d / 2)) (z.1 + d), z.2) = fm (toIcoMod hd (-(d / 2)) z.1, z.2)
    rw [toIcoMod_add_right]
  · have h1 : ∀ x ∈ Cyl.cell d, (fun x : ℝ × ℝ => fm (toIcoMod hd (-(d / 2)) x.1, x.2)) x = fm x := by
      intro x hx
      have hx' := Cyl.mem_cell.1 hx
      have : toIcoMod hd (-(d / 2)) x.1 = x.1 := by
        rw [toIcoMod_eq_self]
        refine ⟨by linarith [neg_div d 2], by linarith [hx'.2]⟩
      simp only [this]
    have h2 : (fun x : ℝ × ℝ => fm (toIcoMod hd (-(d / 2)) x.1, x.2)) =ᵐ[volume.restrict (Cyl.cell d)] fm :=
      (ae_restrict_iff' (Cyl.measurableSet_cell d)).2 (Eventually.of_forall h1)
    exact h2.trans hf.ae_eq_mk.symm

theorem conv_meas {k : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} (hk : StronglyMeasurable k)
    (hg : StronglyMeasurable g) (ν : Measure (ℝ × ℝ)) [SFinite ν] :
    StronglyMeasurable (fun y => ∫ w, k w • g (y - w) ∂ν) :=
  StronglyMeasurable.integral_prod_right'
    (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 • g (z.1 - z.2))
    ((hk.comp_measurable measurable_snd).smul (hg.comp_measurable (measurable_fst.sub measurable_snd)))

theorem far_pt {d : ℝ} (hd : 0 < d) {k : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {Ck : ℝ≥0∞} (hCk : Ck ≠ ⊤)
    (hk : ∀ w, ‖k w‖ₑ ≤ Ck) (hper : Cyl.IsPeriodic d g) (y : ℝ × ℝ) :
    ‖∫ w in Cyl.cell d, k w • g (y - w)‖ₑ ≤ Ck * ∫⁻ w in Cyl.cell d, ‖g w‖ₑ := by
  calc ‖∫ w in Cyl.cell d, k w • g (y - w)‖ₑ
      ≤ ∫⁻ w in Cyl.cell d, ‖k w • g (y - w)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ w in Cyl.cell d, Ck * ‖g (y - w)‖ₑ := by
        refine lintegral_mono fun w => ?_
        rw [enorm_smul]
        exact mul_le_mul' (hk w) le_rfl
    _ = Ck * ∫⁻ w in Cyl.cell d, ‖g (y - w)‖ₑ := lintegral_const_mul' _ _ hCk
    _ = Ck * ∫⁻ w in Cyl.cell d, ‖g w‖ₑ := by
        rw [Cyl.lintegral_cell_comp_sub_left hd (G := fun w => ‖g w‖ₑ)
          (fun z => by simp only [hper z]) y]

theorem far_int {d : ℝ} (hd : 0 < d) {k : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {Ck : ℝ≥0∞}
    (hCk : Ck ≠ ⊤) (hkm : StronglyMeasurable k) (hgm : StronglyMeasurable g)
    (hk : ∀ w, ‖k w‖ₑ ≤ Ck) (hper : Cyl.IsPeriodic d g) (hg1 : ∫⁻ w in Cyl.cell d, ‖g w‖ₑ < ⊤)
    (y : ℝ × ℝ) : Integrable (fun w => k w • g (y - w)) (volume.restrict (Cyl.cell d)) := by
  refine ⟨(hkm.smul (hgm.comp_measurable (measurable_const.sub measurable_id))).aestronglyMeasurable,
    ?_⟩
  have := far_pt hd hCk hk hper y
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hCk.lt_top hg1)
  calc ∫⁻ w in Cyl.cell d, ‖k w • g (y - w)‖ₑ
      ≤ ∫⁻ w in Cyl.cell d, Ck * ‖g (y - w)‖ₑ := by
        refine lintegral_mono fun w => ?_
        rw [enorm_smul]
        exact mul_le_mul' (hk w) le_rfl
    _ = Ck * ∫⁻ w in Cyl.cell d, ‖g (y - w)‖ₑ := lintegral_const_mul' _ _ hCk
    _ = Ck * ∫⁻ w in Cyl.cell d, ‖g w‖ₑ := by
        rw [Cyl.lintegral_cell_comp_sub_left hd (G := fun w => ‖g w‖ₑ)
          (fun z => by simp only [hper z]) y]

theorem near_int {d : ℝ} (hd : 0 < d) {k : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hkm : StronglyMeasurable k) (hgm : StronglyMeasurable g) (hper : Cyl.IsPeriodic d g)
    (hk1 : ∫⁻ w in Cyl.cell d, ‖k w‖ₑ < ⊤) (hg1 : ∫⁻ w in Cyl.cell d, ‖g w‖ₑ < ⊤) :
    ∀ᵐ y ∂(volume.restrict (Cyl.cell d)),
      Integrable (fun w => k w • g (y - w)) (volume.restrict (Cyl.cell d)) := by
  set μ : Measure (ℝ × ℝ) := volume.restrict (Cyl.cell d) with hμ
  have hsm : StronglyMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 • g (z.1 - z.2)) :=
    (hkm.comp_measurable measurable_snd).smul (hgm.comp_measurable (measurable_fst.sub measurable_snd))
  have hint : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 • g (z.1 - z.2)) (μ.prod μ) := by
    refine ⟨hsm.aestronglyMeasurable, ?_⟩
    show ∫⁻ z, ‖k z.2 • g (z.1 - z.2)‖ₑ ∂(μ.prod μ) < ⊤
    rw [lintegral_prod_symm _ hsm.measurable.enorm.aemeasurable]
    have hin : ∀ w : ℝ × ℝ, ∫⁻ y, ‖k w • g (y - w)‖ₑ ∂μ = ‖k w‖ₑ * ∫⁻ y in Cyl.cell d, ‖g y‖ₑ := by
      intro w
      simp_rw [enorm_smul]
      rw [lintegral_const_mul' _ _ ?_]
      · congr 1
        have := Cyl.lintegral_cell_comp_add hd (f := fun z => ‖g z‖ₑ)
          (fun z => by simp only [hper z]) (-w)
        simpa [sub_eq_add_neg] using this
      · exact enorm_ne_top
    simp_rw [hin]
    rw [lintegral_mul_const' _ _ hg1.ne]
    exact ENNReal.mul_lt_top hk1 hg1
  exact hint.prod_right_ae

end AdjSplitAux

open UnforcedLeray in
/-- **The near/far split of the adjoint** `KerAdjSplit` from the near/far bounds `KerNearFar`
(SP 3052-3056). -/
theorem kerAdjSplit_of (h : UnforcedLeray.Short.IIIa.KerNearFar) :
    UnforcedLeray.Short.IIIa.KerAdjSplit := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun d hd F hF => ?_⟩
  have hd0 : 0 < d := by linarith
  obtain ⟨hmeas, hper, hodd, hnear, hfar⟩ := hC d hd
  have hce := AdjSplitAux.cell_eq d
  rw [hce] at hnear hfar
  have hF' : ∀ j, IntegrableOn (F j) (Cyl.cell d) ∧ MemLp (F j) 2 (volume.restrict (Cyl.cell d)) := by
    intro j; rw [← hce]; exact hF j
  rw [hce]
  set μ : Measure (ℝ × ℝ) := volume.restrict (Cyl.cell d) with hμ
  have hFp : ∀ j, ∃ g : ℝ × ℝ → ℂ, StronglyMeasurable g ∧ Cyl.IsPeriodic d g ∧ g =ᵐ[μ] F j :=
    fun j => AdjSplitAux.periodic_rep hd0 (hF' j).1.aestronglyMeasurable
  choose Fp hFpm hFpp hFpe using hFp
  have hF1 : ∀ j, ∫⁻ w in Cyl.cell d, ‖Fp j w‖ₑ = eLpNorm (F j) 1 μ := by
    intro j
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_congr_ae ((hFpe j).fun_comp enorm)
  have hF1top : ∀ j, ∫⁻ w in Cyl.cell d, ‖Fp j w‖ₑ < ⊤ := by
    intro j
    rw [hF1 j]
    exact (memLp_one_iff_integrable.2 (hF' j).1).eLpNorm_lt_top
  have hF2 : ∀ j, eLpNorm (Fp j) 2 μ = eLpNorm (F j) 2 μ := fun j => eLpNorm_congr_ae (hFpe j)
  -- kernel pieces
  have hS1 : MeasurableSet (Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1) :=
    (Cyl.measurableSet_cell d).inter Metric.isOpen_ball.measurableSet
  have hS2 : MeasurableSet (Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1) :=
    (Cyl.measurableSet_cell d).diff Metric.isOpen_ball.measurableSet
  set kN : Fin 2 → ℝ × ℝ → ℝ := fun j => (Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1).indicator
    (fun z => kerD d z j) with hkN
  set kF : Fin 2 → ℝ × ℝ → ℝ := fun j => (Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1).indicator
    (fun z => kerD d z j) with hkF
  have hkNm : ∀ j, StronglyMeasurable (kN j) := fun j => ((hmeas j).indicator hS1).stronglyMeasurable
  have hkFm : ∀ j, StronglyMeasurable (kF j) := fun j => ((hmeas j).indicator hS2).stronglyMeasurable
  have hkN1 : ∀ j, ∫⁻ w in Cyl.cell d, ‖kN j w‖ₑ ≤ ENNReal.ofReal C := by
    intro j
    calc ∫⁻ w in Cyl.cell d, ‖kN j w‖ₑ
        ≤ ∫⁻ w in Cyl.cell d, (Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1).indicator
            (fun z => ∑ i, ‖kerD d z i‖ₑ) w := by
          refine lintegral_mono fun w => ?_
          by_cases hw : w ∈ Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1
          · simp only [hkN, indicator_of_mem hw]
            exact Finset.single_le_sum (f := fun i => ‖kerD d w i‖ₑ) (fun _ _ => bot_le)
              (Finset.mem_univ j)
          · simp only [hkN, indicator_of_notMem hw]; simp
      _ = ∫⁻ w in Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ i, ‖kerD d w i‖ₑ := by
          rw [lintegral_indicator hS1, Measure.restrict_restrict hS1,
            inter_eq_left.2 (inter_subset_left : Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1 ⊆ Cyl.cell d)]
      _ ≤ ENNReal.ofReal C := hnear
  have hkN1top : ∀ j, ∫⁻ w in Cyl.cell d, ‖kN j w‖ₑ < ⊤ := fun j =>
    lt_of_le_of_lt (hkN1 j) ENNReal.ofReal_lt_top
  have hkFb : ∀ j w, ‖kF j w‖ₑ ≤ ENNReal.ofReal C := by
    intro j w
    by_cases hw : w ∈ Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1
    · simp only [hkF, indicator_of_mem hw]
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (hfar w hw.1 hw.2 j)
    · simp only [hkF, indicator_of_notMem hw]; simp
  have hkdec : ∀ j, ∀ w ∈ Cyl.cell d, kerD d w j = kN j w + kF j w := by
    intro j w hw
    by_cases hb : w ∈ Metric.ball (0 : ℝ × ℝ) 1
    · simp only [hkN, hkF, indicator_of_mem (show w ∈ Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1 from ⟨hw, hb⟩),
        indicator_of_notMem (show w ∉ Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1 from fun h => h.2 hb), add_zero]
    · simp only [hkN, hkF, indicator_of_notMem (show w ∉ Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1 from fun h => hb h.2),
        indicator_of_mem (show w ∈ Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1 from ⟨hw, hb⟩), zero_add]
  set ga : Fin 2 → ℝ × ℝ → ℂ := fun j y => ∫ w, kN j w • Fp j (y - w) ∂μ with hga
  set gb : Fin 2 → ℝ × ℝ → ℂ := fun j y => ∫ w, kF j w • Fp j (y - w) ∂μ with hgb
  have hgam : ∀ j, StronglyMeasurable (ga j) := fun j => AdjSplitAux.conv_meas (hkNm j) (hFpm j) μ
  have hgbm : ∀ j, StronglyMeasurable (gb j) := fun j => AdjSplitAux.conv_meas (hkFm j) (hFpm j) μ
  have hsumm : ∀ g : Fin 2 → ℝ × ℝ → ℂ, (∀ j, StronglyMeasurable (g j)) →
      StronglyMeasurable (fun y => -∑ j, g j y) := fun g hg =>
    (Finset.stronglyMeasurable_fun_sum _ fun j _ => hg j).neg
  have hB : eLpNorm (fun y => -∑ j, ga j y) 2 μ ≤
      ENNReal.ofReal C * ∑ j, eLpNorm (F j) 2 μ := by
    calc eLpNorm (fun y => -∑ j, ga j y) 2 μ = eLpNorm (∑ j, ga j) 2 μ := by
          have : (fun y => ∑ j, ga j y) = ∑ j, ga j := by
            funext y; simp [Finset.sum_apply]
          rw [← this]
          exact eLpNorm_neg (fun y => ∑ j, ga j y) 2 μ
      _ ≤ ∑ j, eLpNorm (ga j) 2 μ :=
          eLpNorm_sum_le (fun j _ => (hgam j).aestronglyMeasurable) (by norm_num)
      _ ≤ ∑ j, ENNReal.ofReal C * eLpNorm (F j) 2 μ := Finset.sum_le_sum fun j _ => by
          calc eLpNorm (ga j) 2 μ ≤ (∫⁻ w, ‖kN j w‖ₑ ∂μ) * eLpNorm (Fp j) 2 μ :=
                Cyl.eLpNorm_conv_periodic_le hd0 (ν := μ) (hkNm j) (hFpm j) (hFpp j)
                  (by norm_num) (by norm_num)
            _ ≤ ENNReal.ofReal C * eLpNorm (F j) 2 μ := by
                rw [hF2 j]; gcongr; exact hkN1 j
      _ = ENNReal.ofReal C * ∑ j, eLpNorm (F j) 2 μ := (Finset.mul_sum _ _ _).symm
  have hb : ∀ y, ‖-∑ j, gb j y‖ₑ ≤ ENNReal.ofReal C * ∑ j, eLpNorm (F j) 1 μ := by
    intro y
    calc ‖-∑ j, gb j y‖ₑ = ‖∑ j, gb j y‖ₑ := enorm_neg _
      _ ≤ ∑ j, ‖gb j y‖ₑ := enorm_sum_le _ _
      _ ≤ ∑ j, ENNReal.ofReal C * eLpNorm (F j) 1 μ := Finset.sum_le_sum fun j _ =>
          (AdjSplitAux.far_pt hd0 ENNReal.ofReal_ne_top (hkFb j) (hFpp j) y).trans (by rw [hF1 j])
      _ = ENNReal.ofReal C * ∑ j, eLpNorm (F j) 1 μ := (Finset.mul_sum _ _ _).symm
  refine ⟨fun y => -∑ j, ga j y, fun y => -∑ j, gb j y, ?_, ?_, ?_, ?_, ?_⟩
  · -- the identity
    have hnearAE : ∀ᵐ y ∂μ, ∀ j, Integrable (fun w => kN j w • Fp j (y - w)) μ :=
      ae_all_iff.2 fun j => AdjSplitAux.near_int hd0 (hkNm j) (hFpm j) (hFpp j) (hkN1top j) (hF1top j)
    filter_upwards [hnearAE] with y hy
    have hfi : ∀ j, Integrable (fun w => kF j w • Fp j (y - w)) μ := fun j =>
      AdjSplitAux.far_int hd0 ENNReal.ofReal_ne_top (hkFm j) (hFpm j) (hkFb j) (hFpp j) (hF1top j) y
    set G : ℝ × ℝ → ℂ := fun x => ∑ j, Fp j x * ((kerD d (x - y) j : ℝ) : ℂ) with hG
    have hGper : Cyl.IsPeriodic d G := by
      intro z
      have e : ((z.1 + d, z.2) : ℝ × ℝ) - y = ((z - y).1 + d, (z - y).2) := by
        ext <;> simp; ring
      simp only [hG, e, hper (z - y), hFpp _ z]
    have step1 : kerAdj d F y = ∫ x in Cyl.cell d, G x := by
      unfold kerAdj
      rw [hce]
      refine integral_congr_ae ?_
      have hae : ∀ᵐ x ∂μ, ∀ j, Fp j x = F j x := ae_all_iff.2 fun j => hFpe j
      filter_upwards [hae] with x hx
      simp only [hG, hx]
    have step2 : ∫ x in Cyl.cell d, G x = ∫ w in Cyl.cell d, G (y - w) :=
      (Cyl.integral_cell_comp_sub_left hd0 hGper y).symm
    have step3 : ∫ w in Cyl.cell d, G (y - w) =
        ∫ w, -∑ j, (kN j w • Fp j (y - w) + kF j w • Fp j (y - w)) ∂μ := by
      refine setIntegral_congr_fun (Cyl.measurableSet_cell d) fun w hw => ?_
      simp only [hG]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_sub_cancel_left, hodd w j, hkdec j w hw, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    have step4 : ∫ w, -∑ j, (kN j w • Fp j (y - w) + kF j w • Fp j (y - w)) ∂μ =
        -∑ j, ga j y + -∑ j, gb j y := by
      have hI : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
          Integrable (fun w => kN j w • Fp j (y - w) + kF j w • Fp j (y - w)) μ :=
        fun j _ => (hy j).add (hfi j)
      rw [integral_neg, integral_finsetSum _ hI]
      simp only [integral_add (hy _) (hfi _), Finset.sum_add_distrib, neg_add]
      rfl
    show kerAdj d F y = -∑ j, ga j y + -∑ j, gb j y
    rw [step1, step2, step3, step4]
  · exact ⟨(hsumm ga hgam).aestronglyMeasurable, lt_of_le_of_lt hB
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.2 fun j _ => (hF' j).2.eLpNorm_lt_top))⟩
  · exact hB
  · exact (hsumm gb hgbm).aestronglyMeasurable
  · exact hb

end UnforcedLeray.Short.IIIa
