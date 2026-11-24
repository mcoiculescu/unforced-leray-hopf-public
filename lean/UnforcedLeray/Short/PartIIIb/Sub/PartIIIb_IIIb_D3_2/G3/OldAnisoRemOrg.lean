import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2_G1_5_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.DatumNorm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed

/-!
# `PartIII-b:IIIb-D3/2/G3/1/3/org`: decomposition of `G3.LaterOutputRem` and `G3.LaterOutputAbsOp`

Source of record: `the November 2 reference manuscript` (73 pages):
* lines 4432-4460 (`eq:young-later-output` 4454: propagation of a state at `H = 2/ν` to the
  long-clock age `b` by `eq:short-causal-long-forward` 4440-4448, uniform Biot-Savart embedding at
  `d(b) ≥ 1`, and the impulse estimates at `r = b` 4449-4455);
* lines 314-317 (`sct:integrated`: BUC train cell `L²` velocity decay before and after overlap);
* lines 3228-3240 (`eq:ct-embeddings`) and 3242-3251, 3272-3289 (`eq:ct-kinetic-impulse`,
  `eq:ct-tested-impulse`, and `eq:ct-absolute-impulse` at `r = b`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open ConcreteYF FlatSettingInst

/-! ## 1. Extension of `xiFromH` and measurability of `tailAbsIntegrand` and `itOldDens` -/

/-- Extension of `xiFromH` to all `s : ℝ` that is `0` for `s ≤ 0`, continuous on `(0, ∞)`, and
agrees with `xiFromH (levelFlat hν FI χo ε) ν μ w` on `[2/ν, ∞)`. -/
def xiFromHExt {κ : IIIa.PlanarFrameKernels} {ν m : ℝ} [Fact (1 < m)] [Fact (0 < cOf ν)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (FI : FlatInstData κ ν (cOf ν) m tr)
    (μ : ℝ) (w : Xmc (cOf ν) m) (s : ℝ) : Xmc (cOf ν) m :=
  if s ≤ 0 then 0 else ((s : ℂ) ^ (-(μ : ℂ))) • FI.ev.U (max s (2 / ν)) (2 / ν) w

theorem xiFromHExt_of_nonpos {κ : IIIa.PlanarFrameKernels} {ν m : ℝ} [Fact (1 < m)]
    [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (μ : ℝ) (w : Xmc (cOf ν) m) {s : ℝ} (hs : s ≤ 0) :
    xiFromHExt FI μ w s = 0 := by
  simp [xiFromHExt, hs]

theorem xiFromHExt_eq_of_ge {κ : IIIa.PlanarFrameKernels} {ν m : ℝ} [Fact (1 < m)] (hν : 0 < ν)
    [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ) (ε μ : ℝ) (w : Xmc (cOf ν) m)
    {s : ℝ} (hs : 2 / ν ≤ s) :
    xiFromHExt FI μ w s = xiFromH (levelFlat hν FI χo ε) ν μ w s := by
  have hspos : 0 < s := (div_pos two_pos hν).trans_le hs
  have hnot : ¬ s ≤ 0 := not_le.2 hspos
  simp [xiFromHExt, hnot, max_eq_left hs, xiFromH, levelFlat, actualFlatSetting, actualPk]
  rfl

theorem continuousOn_xiFromHExt {κ : IIIa.PlanarFrameKernels} {ν m : ℝ} [Fact (1 < m)]
    (hν : 0 < ν) [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (μ : ℝ) (w : Xmc (cOf ν) m) :
    ContinuousOn (xiFromHExt FI μ w) (Ioi 0) := by
  have hU_cont : Continuous (fun s : ℝ => FI.ev.U (max s (2 / ν)) (2 / ν) w) :=
    (FI.ev.jointCont w).comp_continuous
      ((continuous_id.max continuous_const).prodMk continuous_const)
      (fun s => ⟨div_nonneg zero_le_two hν.le, le_max_right s (2 / ν)⟩)
  have hpow : ContinuousOn (fun s : ℝ => (s : ℂ) ^ (-(μ : ℂ))) (Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun s hs => Complex.ofReal_mem_slitPlane.2 hs)
  refine (hpow.smul hU_cont.continuousOn).congr fun s hs => ?_
  have hnot : ¬ s ≤ 0 := not_le.2 hs
  simp [xiFromHExt, hnot]

private theorem measurable_symOuter_xiFromHExt {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) [Fact (0 < cOf ν)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (FI : FlatInstData κ ν (cOf ν) m tr)
    (μ : ℝ) (w : Xmc (cOf ν) m) (i j : Fin 3) :
    Measurable fun p : Chart =>
      IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiFromHExt FI μ w p.1) p.2) i j := by
  have hK := kcJointMeasurable (cOf ν) m (xiFromHExt FI μ w)
    (continuousOn_xiFromHExt hν FI μ w) (fun _ hs => xiFromHExt_of_nonpos FI μ w hs)
  have hKi : ∀ k : Fin 2, Measurable fun p : Chart => kcMer (xiFromHExt FI μ w p.1) p.2 k :=
    fun k => Complex.measurable_re.comp (hK k)
  have hT : Measurable (NearInst.trainMer tr) := NearInst.trainMerMeasurable ν (cOf ν) tr
  have hP : ∀ k : Fin 2, Measurable fun v : Merid => v k := fun k =>
    (EuclideanSpace.proj k : Merid →L[ℝ] ℝ).continuous.measurable
  have hemb : ∀ l : Fin 3, Measurable fun v : Merid => IIIa.embedMerid v l := by
    intro l; fin_cases l
    · exact hP 0
    · exact measurable_const
    · exact hP 1
  have hTe : ∀ l : Fin 3, Measurable fun p : Chart => IIIa.embedMerid (NearInst.trainMer tr p) l :=
    fun l => (hemb l).comp hT
  have hKe : ∀ l : Fin 3, Measurable fun p : Chart =>
      IIIa.embedMerid (kcMer (xiFromHExt FI μ w p.1) p.2) l := by
    intro l; fin_cases l
    · exact hKi 0
    · exact measurable_const
    · exact hKi 1
  exact ((hTe i).mul (hKe j)).add ((hKe i).mul (hTe j))

/-- Measurability of the extended `tailAbsIntegrand` on `ℝ`. -/
theorem measurable_tailAbsIntegrandExt {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) [Fact (0 < cOf ν)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (FI : FlatInstData κ ν (cOf ν) m tr)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (k : ℕ) (μ : ℝ) (w : Xmc (cOf ν) m) :
    Measurable fun s : ℝ =>
      χo (ν * s) * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
        cellInt (cOf ν) (fun p =>
          matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer (xiFromHExt FI μ w s) p))) := by
  have hF : Measurable fun p : Chart =>
      matNorm (IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiFromHExt FI μ w p.1) p.2)) := by
    unfold matNorm
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp (measurable_symOuter_xiFromHExt hν FI μ w i j)
  have hInt : Measurable fun s : ℝ =>
      ∫ x in (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ),
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x)) :=
    (hF.stronglyMeasurable.integral_prod_right').measurable
  have hCell : Measurable fun s : ℝ =>
      cellInt (cOf ν) (fun x =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x))) :=
    measurable_const.mul hInt
  have hChi : Measurable fun s : ℝ => χo (ν * s) :=
    (hχo.smooth.continuous.comp (continuous_const.mul continuous_id)).measurable
  have hPow : Measurable fun s : ℝ => s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) :=
    measurable_id.pow_const _
  exact (hChi.mul hPow).mul hCell

/-- Measurability of `itOldDens (levelFlat hν FI χo ε) ν (xiFromH ... w)` when `0 < ν ≤ 1 / 4`. -/
theorem measurable_itOldDens_xiFromH {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) (hν4 : ν ≤ 1 / 4) [Fact (0 < cOf ν)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (FI : FlatInstData κ ν (cOf ν) m tr)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε μ : ℝ) (w : Xmc (cOf ν) m) :
    Measurable (itOldDens (levelFlat hν FI χo ε) ν
      (xiFromH (levelFlat hν FI χo ε) ν μ w)) := by
  have h22 := measurable_symOuter_xiFromHExt hν FI μ w 2 2
  have h00 := measurable_symOuter_xiFromHExt hν FI μ w 0 0
  have hF : Measurable fun p : Chart =>
      2 * IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiFromHExt FI μ w p.1) p.2) 2 2 -
        IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiFromHExt FI μ w p.1) p.2) 0 0 :=
    (measurable_const.mul h22).sub h00
  have hInt : Measurable fun s : ℝ =>
      ∫ x in (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ),
        (2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x) 2 2 -
          IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x) 0 0) :=
    (hF.stronglyMeasurable.integral_prod_right').measurable
  have hCell : Measurable fun s : ℝ =>
      cellInt (cOf ν) (fun x =>
        2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x) 2 2 -
          IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x) 0 0) :=
    measurable_const.mul hInt
  have hChi : Measurable fun s : ℝ => χo (ν * s) :=
    (hχo.smooth.continuous.comp (continuous_const.mul continuous_id)).measurable
  have hPow : Measurable fun s : ℝ => s ^ (-(3 / 2 : ℝ)) :=
    measurable_id.pow_const _
  have hMain : Measurable fun s : ℝ =>
      (Ici (ν ^ (-(3 / 2 : ℝ)))).indicator (fun s =>
        χo (ν * s) * s ^ (-(3 / 2 : ℝ)) *
          cellInt (cOf ν) (fun x =>
            2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x) 2 2 -
              IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x) 0 0)) s :=
    ((hChi.mul hPow).mul hCell).indicator measurableSet_Ici
  have huo : 2 / ν ≤ ν ^ (-(3 / 2 : ℝ)) := two_div_le_uo hν hν4
  have heq : itOldDens (levelFlat hν FI χo ε) ν (xiFromH (levelFlat hν FI χo ε) ν μ w) =
      fun s : ℝ =>
        (Ici (ν ^ (-(3 / 2 : ℝ)))).indicator (fun s =>
          χo (ν * s) * s ^ (-(3 / 2 : ℝ)) *
            cellInt (cOf ν) (fun x =>
              2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x) 2 2 -
                IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiFromHExt FI μ w s) x) 0 0)) s := by
    funext s
    unfold itOldDens FlatSetting.ITdens
    by_cases hs : ν ^ (-(3 / 2 : ℝ)) ≤ s
    · rw [Set.indicator_of_mem (mem_Ici.2 hs)]
      simp only [ite_eq_left_iff.2 fun h => (h hs).elim]
      rw [xiFromHExt_eq_of_ge hν FI χo ε μ w (huo.trans hs)]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hs (mem_Ici.1 h))]
      simp only [ite_eq_right_iff.2 fun h => (hs h).elim, cellInt, Matrix.zero_apply,
        mul_zero, sub_self, integral_zero]
  rw [heq]
  exact hMain

/-! ## 2. Reduction of `LaterOutputAbsOp` and `LaterOutputRem` to `UnforcedTailImpulseBound` -/

private theorem matNorm_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    matNorm (r • M) = r * matNorm M := by
  unfold matNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change |r * M i j| = r * |M i j|
  rw [abs_mul, abs_of_nonneg hr]

/-- On `s ≥ 2 / ν`, `tailAbsIntegrand` of `levelFlat` equals `G1.LaterOutput.unforcedTailDens`. -/
theorem tailAbsIntegrand_levelFlat_eq_unforcedTailDens {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) [Fact (0 < cOf ν)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (FI : FlatInstData κ ν (cOf ν) m tr)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε μ : ℝ) (k : ℕ) (w : Xmc (cOf ν) m)
    {s : ℝ} (hs : 2 / ν ≤ s) :
    tailAbsIntegrand (levelFlat hν FI χo ε) ν μ k w s =
      G1.LaterOutput.unforcedTailDens FI k μ w s := by
  have hχ1 : (levelFlat hν FI χo ε).chiO s = 1 := by
    change χo (ν * s) = 1
    apply hχo.one
    have h2 : (2 : ℝ) ≤ ν * s := by
      calc (2 : ℝ) = ν * (2 / ν) := (mul_div_cancel₀ 2 hν.ne').symm
        _ ≤ ν * s := mul_le_mul_of_nonneg_left hs hν.le
    linarith
  set y := FI.ev.U s (2 / ν) w
  set r : ℝ := s ^ (-μ)
  have hspos : 0 < s := (div_pos two_pos hν).trans_le hs
  have hr0 : 0 ≤ r := Real.rpow_nonneg hspos.le _
  have hxi : xiFromH (levelFlat hν FI χo ε) ν μ w s = (r : ℂ) • y := by
    unfold xiFromH r y
    rw [← Complex.ofReal_neg, Complex.ofReal_cpow hspos.le]
    rfl
  have hK_avg : kcMer ((r : ℂ) • y) =ᵐ[Cyl.avgμ (cOf ν)] r • kcMer y :=
    (kcMerLinear m ν hν y y r).2
  have hcpos : 0 < cOf ν := cOf_pos hν
  have hne : ENNReal.ofReal (cOf ν)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hcpos)).ne'
  have hcell_eq : Cyl.cell (cOf ν) = B0579.cell (cOf ν) := by
    simp only [Cyl.cell, B0579.cell, neg_div]
  have hK_cell : kcMer ((r : ℂ) • y) =ᵐ[volume.restrict (B0579.cell (cOf ν))] r • kcMer y := by
    unfold Cyl.avgμ Cyl.cellμ Filter.EventuallyEq at hK_avg
    rw [hcell_eq, Measure.ae_ennreal_smul_measure_eq hne] at hK_avg
    exact hK_avg
  have hsub : (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ) ⊆ B0579.cell (cOf ν) := by
    rintro ⟨q, η⟩ ⟨hq, _⟩
    exact ⟨⟨by linarith [hq.1], hq.2⟩, trivial⟩
  have hK_open :
      kcMer ((r : ℂ) • y) =ᵐ[volume.restrict ((Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ))]
        r • kcMer y :=
    ae_restrict_of_ae_restrict_of_subset hsub hK_cell
  have hCell_eq : cellInt (cOf ν) (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p))
          (kcMer (xiFromH (levelFlat hν FI χo ε) ν μ w s) p))) =
      r * cellInt (cOf ν) (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p))) := by
    unfold cellInt
    rw [hxi]
    have hint_eq : (∫ p in (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ),
          matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ((r : ℂ) • y) p))) =
        ∫ p in (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ),
          r * matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p)) := by
      refine integral_congr_ae ?_
      filter_upwards [hK_open] with p hp
      have hp' : kcMer ((r : ℂ) • y) p = r • kcMer y p := hp
      rw [hp', symOuter_smul_right', matNorm_smul_of_nonneg hr0]
    rw [hint_eq, integral_const_mul]
    ring
  unfold tailAbsIntegrand G1.LaterOutput.unforcedTailDens
  change (levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
      cellInt (cOf ν) (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p))
          (kcMer (xiFromH (levelFlat hν FI χo ε) ν μ w s) p))) =
    s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
      (r * cellInt (cOf ν) (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p))))
  rw [hχ1, one_mul, hCell_eq]

private theorem unforcedTailDens_nonneg' {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (k : ℕ) (μ : ℝ) (w : Xmc (cOf ν) m)
    {s : ℝ} (hs : 0 < s) :
    0 ≤ G1.LaterOutput.unforcedTailDens FI k μ w s := by
  have hc : 0 < cOf ν := Fact.out
  unfold G1.LaterOutput.unforcedTailDens cellInt
  refine mul_nonneg (Real.rpow_nonneg hs.le _) (mul_nonneg (Real.rpow_nonneg hs.le _) ?_)
  refine mul_nonneg (inv_nonneg.2 hc.le) (setIntegral_nonneg
    (measurableSet_Ioo.prod MeasurableSet.univ) fun p _ => ?_)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **`LaterOutputAbsOp` from `G1.LaterOutput.UnforcedTailImpulseBound`**
(source 4440-4457, `eq:young-later-output`). -/
theorem laterOutputAbsOp_of_unforcedTailImpulseBound (D : SeqData)
    (hImp : G1.LaterOutput.UnforcedTailImpulseBound D) : LaterOutputAbsOp D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨C, N1, hC0, hC⟩ := hImp dm dp hst κ hκ m hm
  obtain ⟨N2, hAct⟩ := Filter.eventually_atTop.mp hS
  refine ⟨C, max N1 N2, hC0, fun n hn k hk z hz => ?_⟩
  obtain ⟨FI, hSn⟩ := hAct n (le_trans (le_max_right _ _) hn)
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have : Fact (0 < cOf (nu D n)) := ⟨cOf_pos hν⟩
  rw [hSn]
  intro (w : Xmc (cOf (nu D n)) m)
  set S₀ := levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)
  have hbd_u := hC n (le_trans (le_max_left _ _) hn) FI k hk z hz w
  have heq_on : EqOn (tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w)
      (G1.LaterOutput.unforcedTailDens FI k (D.mu n z) w) (Ioi (2 / nu D n)) := by
    intro s hs
    exact tailAbsIntegrand_levelFlat_eq_unforcedTailDens hν FI D.K.hχo (retEps D.Pl D.σ₀ n)
      (D.mu n z) k w (mem_Ioi.1 hs).le
  have heq_ext : EqOn (tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w)
      (fun s : ℝ =>
        D.K.χo (nu D n * s) * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
          cellInt (cOf (nu D n)) (fun p =>
            matNorm (IIIa.symOuter (NearInst.trainMer (D.train n) (s, p))
              (kcMer (xiFromHExt FI (D.mu n z) w s) p))))
      (Ioi (2 / nu D n)) := by
    intro s hs
    have hxi := xiFromHExt_eq_of_ge hν FI D.K.χo (retEps D.Pl D.σ₀ n) (D.mu n z) w (mem_Ioi.1 hs).le
    dsimp only [tailAbsIntegrand, S₀, levelFlat, actualFlatSetting]
    rw [hxi]
    rfl
  have hmeas_ext := measurable_tailAbsIntegrandExt hν FI D.K.hχo k (D.mu n z) w
  have haesm : AEStronglyMeasurable (tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w)
      (volume.restrict (Ioi (2 / nu D n))) :=
    hmeas_ext.aestronglyMeasurable.congr
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => (heq_ext hs).symm))
  have hnn_on : ∀ s ∈ Ioi (2 / nu D n), 0 ≤ tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w s := by
    intro s hs
    rw [heq_on hs]
    exact unforcedTailDens_nonneg' FI k (D.mu n z) w ((div_pos two_pos hν).trans hs)
  have hlint_eq : (∫⁻ s in Ioi (2 / nu D n),
        ‖tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w s‖ₑ) =
      ∫⁻ s in Ioi (2 / nu D n),
        ENNReal.ofReal (G1.LaterOutput.unforcedTailDens FI k (D.mu n z) w s) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [Real.enorm_eq_ofReal (hnn_on s hs), heq_on hs]
  have hint : IntegrableOn (tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w) (Ioi (2 / nu D n)) := by
    refine ⟨haesm, ?_⟩
    show (∫⁻ s in Ioi (2 / nu D n), ‖tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w s‖ₑ) < ⊤
    rw [hlint_eq]
    exact lt_of_le_of_lt hbd_u ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Ioi (2 / nu D n))]
      tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn_on)
  rw [integral_eq_lintegral_of_nonneg_ae hnn_ae haesm]
  have hlint_eq' : (∫⁻ s in Ioi (2 / nu D n),
        ENNReal.ofReal (tailAbsIntegrand S₀ (nu D n) (D.mu n z) k w s)) =
      ∫⁻ s in Ioi (2 / nu D n),
        ENNReal.ofReal (G1.LaterOutput.unforcedTailDens FI k (D.mu n z) w s) :=
    setLIntegral_congr_fun measurableSet_Ioi fun s hs => by rw [heq_on hs]
  rw [hlint_eq']
  have hrhs0 : 0 ≤ C * oldScaleA D S₀ n z * nu D n ^ k *
      (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖) := by
    unfold oldScaleA S₀
    have hc : 0 < (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).c := cOf_pos hν
    positivity
  have hrhs_eq : C * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
        nu D n ^ (3 + 2 * D.mu n z) / cOf (nu D n)) * nu D n ^ k *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖)) =
      C * oldScaleA D S₀ n z * nu D n ^ k *
        (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖) := by
    unfold oldScaleA S₀
    change C * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
        nu D n ^ (3 + 2 * D.mu n z) / cOf (nu D n)) * nu D n ^ k *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖)) =
      C * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
        nu D n ^ (3 + 2 * D.mu n z) / cOf (nu D n)) * nu D n ^ k *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖)
    ring
  rw [hrhs_eq] at hbd_u
  exact ENNReal.toReal_le_of_le_ofReal hrhs0 hbd_u

/-- **`LaterOutputAbsOp` from the three tail leaves** (source 4440-4457). -/
theorem laterOutputAbsOp_of_parts (D : SeqData)
    (hVel : G1.LaterOutput.TrainVelTailBound D)
    (hCore : G1.LaterOutput.UnforcedFlowKcCoreBound D)
    (hImp : G1.LaterOutput.UnforcedFlowKcImpulseBound D) : LaterOutputAbsOp D :=
  laterOutputAbsOp_of_unforcedTailImpulseBound D
    (G1.LaterOutput.unforcedTailImpulseBound_of D hVel hCore hImp)

private theorem abs_entry_le_matNorm (A : Mat3) (i j : Fin 3) : |A i j| ≤ matNorm A := by
  unfold matNorm
  calc |A i j| ≤ ∑ j' : Fin 3, |A i j'| :=
        Finset.single_le_sum (f := fun j' => |A i j'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, |A i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, |A i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)

private theorem abs_readout_le_three_matNorm (A : Mat3) :
    |2 * A 2 2 - A 0 0| ≤ 3 * matNorm A := by
  have h22 := abs_entry_le_matNorm A 2 2
  have h00 := abs_entry_le_matNorm A 0 0
  have htri : |2 * A 2 2 - A 0 0| ≤ |2 * A 2 2| + |A 0 0| := abs_sub _ _
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
  linarith

private theorem memLp_embedMerid {μm : Measure (ℝ × ℝ)} {v : ℝ × ℝ → Merid}
    (hv : MemLp v 2 μm) (i : Fin 3) :
    MemLp (fun p => IIIa.embedMerid (v p) i) 2 μm := by
  have hcont : Continuous (fun x : Merid => IIIa.embedMerid x i) := by
    fin_cases i
    · exact (EuclideanSpace.proj 0 : Merid →L[ℝ] ℝ).continuous
    · exact continuous_const
    · exact (EuclideanSpace.proj 1 : Merid →L[ℝ] ℝ).continuous
  refine hv.norm.mono' (hcont.comp_aestronglyMeasurable hv.1) (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  have hsq : (IIIa.embedMerid (v p) i) ^ 2 ≤ ‖v p‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    fin_cases i <;> simp [IIIa.embedMerid] <;> linarith [sq_nonneg (v p 0), sq_nonneg (v p 1)]
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (norm_nonneg _))

private theorem train_v_memLp_cell {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {s : ℝ} (hs0 : 0 ≤ s) :
    MemLp (tr.v s) 2 (volume.restrict (B0579.cell c)) := by
  have hset : UnforcedLeray.Cyl.cell c = B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell B0579.cell
    rw [neg_div]
  have hcont : Continuous (fun x : ℝ × ℝ => tr.v s x) := by
    have hc := tr.isTrain.smooth_v.continuousOn
    refine continuousOn_univ.1 (hc.comp (continuousOn_const.prodMk continuousOn_id) ?_)
    exact fun x _ => ⟨Set.mem_Ici.2 hs0, Set.mem_univ _⟩
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  rw [← hset]
  exact tr.isTrain.finite_energy s hs0

private theorem integrable_matNorm_symOuter_cell {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (y : Xmc c m) :
    Integrable (fun p => matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p)))
      (volume.restrict (B0579.cell c)) := by
  set μcell := volume.restrict (B0579.cell c)
  have hmer : ∀ p : ℝ × ℝ, NearInst.trainMer tr (s, p) = tr.v s p := by
    intro p; ext i; simp [NearInst.trainMer, IIIa.trainVel, hs]
  have hv : MemLp (fun p => NearInst.trainMer tr (s, p)) 2 μcell := by
    rw [show (fun p => NearInst.trainMer tr (s, p)) = tr.v s from funext hmer]
    exact train_v_memLp_cell tr hs
  have hk : MemLp (kcMer y) 2 μcell := (Lp.memLp (kcLp y)).ae_eq (kcMer_ae y).symm
  have h_ij : ∀ i j : Fin 3,
      Integrable (fun p => IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p) i j) μcell :=
    fun i j =>
      ((memLp_embedMerid hv i).integrable_mul (memLp_embedMerid hk j)).add
        ((memLp_embedMerid hk i).integrable_mul (memLp_embedMerid hv j))
  unfold matNorm
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (h_ij i j).norm

private theorem abs_cellInt_readout_le_three_matNorm {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (y : Xmc c m) :
    |cellInt c (fun p =>
        2 * IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p) 2 2 -
          IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p) 0 0)| ≤
      3 * cellInt c (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p))) := by
  have hc : 0 < c := Fact.out
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Ioo (-c / 2) (c / 2) ×ˢ univ) =
      (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c) := by
    rw [B0579.cell, neg_div, Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ico]
  set μcell := (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c)
  set M : ℝ × ℝ → Mat3 := fun p => IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p)
  have hInt := (integrable_matNorm_symOuter_cell tr hs y).const_mul 3
  have h1 : |∫ p, (2 * M p 2 2 - M p 0 0) ∂μcell| ≤ ∫ p, |2 * M p 2 2 - M p 0 0| ∂μcell :=
    abs_integral_le_integral_abs
  have h2 : (∫ p, |2 * M p 2 2 - M p 0 0| ∂μcell) ≤ ∫ p, 3 * matNorm (M p) ∂μcell :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hInt
      (Eventually.of_forall fun p => abs_readout_le_three_matNorm (M p))
  rw [integral_const_mul] at h2
  unfold cellInt
  rw [hmeas, abs_mul, abs_of_pos (inv_pos.2 hc), ← mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.2 hc.le)

/-- `2 / ν < ν ^ (-(3 / 2 : ℝ))` when `0 < ν < 1 / 4`. -/
theorem two_div_lt_uo {ν : ℝ} (hν : 0 < ν) (hν4 : ν < 1 / 4) :
    2 / ν < ν ^ (-(3 / 2 : ℝ)) := by
  have hsq : Real.sqrt ν < 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by norm_num]
    exact Real.sqrt_lt_sqrt hν.le hν4
  have hsqpos : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have h2 : 2 < (Real.sqrt ν)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hsqpos]
    exact hsq.trans_eq (by norm_num)
  have heq : ν ^ (-(3 / 2 : ℝ)) = (Real.sqrt ν)⁻¹ / ν := by
    calc ν ^ (-(3 / 2 : ℝ)) = ν ^ (-(1 / 2 : ℝ) + (-1 : ℝ)) := by congr 1; norm_num
      _ = ν ^ (-(1 / 2 : ℝ)) * ν ^ (-1 : ℝ) := Real.rpow_add hν _ _
      _ = (Real.sqrt ν)⁻¹ / ν := by
        rw [Real.rpow_neg hν.le, Real.sqrt_eq_rpow, Real.rpow_neg_one, ← div_eq_mul_inv]
  rw [heq]
  exact div_lt_div_of_pos_right h2 hν

/-- Pointwise bound `|itOldDens| ≤ 3 * indicator (Ioi (2/ν)) (tailAbsIntegrand ... 0 w)`
when `0 < ν < 1 / 4`. -/
theorem abs_itOldDens_le_three_tailAbsIntegrand {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) (hν4 : ν < 1 / 4) [Fact (0 < cOf ν)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (FI : FlatInstData κ ν (cOf ν) m tr)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε μ : ℝ) (w : Xmc (cOf ν) m) (s : ℝ) :
    |itOldDens (levelFlat hν FI χo ε) ν (xiFromH (levelFlat hν FI χo ε) ν μ w) s| ≤
      3 * (Ioi (2 / ν)).indicator
        (tailAbsIntegrand (levelFlat hν FI χo ε) ν μ 0 w) s := by
  have hc : 0 < cOf ν := Fact.out
  have huo : 2 / ν < ν ^ (-(3 / 2 : ℝ)) := two_div_lt_uo hν hν4
  by_cases hs : ν ^ (-(3 / 2 : ℝ)) ≤ s
  · have hs2 : 2 / ν < s := huo.trans_le hs
    have hs0 : 0 ≤ s := (div_pos two_pos hν).le.trans hs2.le
    rw [Set.indicator_of_mem (mem_Ioi.2 hs2)]
    unfold itOldDens FlatSetting.ITdens tailAbsIntegrand
    simp only [ite_eq_left_iff.2 fun h => (h hs).elim, Nat.cast_zero, zero_div, sub_zero]
    have hχ0 : 0 ≤ (levelFlat hν FI χo ε).chiO s := (hχo.range (ν * s)).1
    have hpow0 : 0 ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs0 _
    rw [abs_mul, abs_mul, abs_of_nonneg hχ0, abs_of_nonneg hpow0]
    have hcell := abs_cellInt_readout_le_three_matNorm tr hs0
      (xiFromH (levelFlat hν FI χo ε) ν μ w s)
    calc (levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ)) *
          |cellInt (cOf ν) (fun p =>
            2 * IIIa.symOuter (NearInst.trainMer tr (s, p))
                (kcMer (xiFromH (levelFlat hν FI χo ε) ν μ w s) p) 2 2 -
              IIIa.symOuter (NearInst.trainMer tr (s, p))
                (kcMer (xiFromH (levelFlat hν FI χo ε) ν μ w s) p) 0 0)|
        ≤ (levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ)) *
            (3 * cellInt (cOf ν) (fun p =>
              matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p))
                (kcMer (xiFromH (levelFlat hν FI χo ε) ν μ w s) p)))) :=
          mul_le_mul_of_nonneg_left hcell (mul_nonneg hχ0 hpow0)
      _ = 3 * ((levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ)) *
            cellInt (cOf ν) (fun p =>
              matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p))
                (kcMer (xiFromH (levelFlat hν FI χo ε) ν μ w s) p)))) := by ring
  · have hzero : itOldDens (levelFlat hν FI χo ε) ν
        (xiFromH (levelFlat hν FI χo ε) ν μ w) s = 0 := by
      unfold itOldDens FlatSetting.ITdens
      simp only [ite_eq_right_iff.2 fun h => (hs h).elim, cellInt, Matrix.zero_apply,
        mul_zero, sub_self, integral_zero]
    rw [hzero, abs_zero]
    refine mul_nonneg (by norm_num) ?_
    by_cases hs2 : 2 / ν < s
    · rw [Set.indicator_of_mem (mem_Ioi.2 hs2)]
      have hs0 : 0 ≤ s := (div_pos two_pos hν).le.trans hs2.le
      unfold tailAbsIntegrand cellInt
      refine mul_nonneg (mul_nonneg (hχo.range (ν * s)).1 (Real.rpow_nonneg hs0 _)) ?_
      refine mul_nonneg (inv_nonneg.2 hc.le) (setIntegral_nonneg
        (measurableSet_Ioo.prod MeasurableSet.univ) fun p _ => ?_)
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    · rw [Set.indicator_of_notMem (fun h => hs2 (mem_Ioi.1 h))]

/-- **`LaterOutputRem` from `LaterOutputAbsOp`** (source 4440-4457, 4509-4514). -/
theorem laterOutputRem_of_laterOutputAbsOp (D : SeqData) (hOp : LaterOutputAbsOp D) :
    LaterOutputRem D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨C, N1, hC0, hC⟩ := hOp dm dp hst κ hκ m hm S hS
  have hν_ev : ∀ᶠ n : ℕ in atTop, nu D n < 1 / 4 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hS.and hν_ev)
  refine ⟨3 * C, max N1 N2, by positivity, fun n hn z hz => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨⟨FI, hSn⟩, hν4⟩ := hN2 n hn2
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have : Fact (0 < cOf (nu D n)) := ⟨cOf_pos hν⟩
  have h0_sub : Ioi (2 / nu D n) ⊆ Ioi (0 : ℝ) :=
    Ioi_subset_Ioi (div_pos two_pos hν).le
  intro x
  have hmeas : Measurable (itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x)) := by
    revert x
    rw [hSn]
    intro (w : Xmc (cOf (nu D n)) m)
    exact measurable_itOldDens_xiFromH hν hν4.le FI D.K.hχo (retEps D.Pl D.σ₀ n) (D.mu n z) w
  have hpt : ∀ s : ℝ,
      ‖itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x) s‖ ≤
        3 * (Ioi (2 / nu D n)).indicator
          (tailAbsIntegrand (S n) (nu D n) (D.mu n z) 0 x) s := by
    clear hmeas
    revert x
    rw [hSn]
    intro (w : Xmc (cOf (nu D n)) m) s
    rw [Real.norm_eq_abs]
    exact abs_itOldDens_le_three_tailAbsIntegrand hν hν4 FI D.K.hχo (retEps D.Pl D.σ₀ n)
      (D.mu n z) w s
  obtain ⟨hint0, hbd0⟩ := hC n hn1 0 (Nat.zero_le 1) z hz x
  rw [pow_zero, mul_one] at hbd0
  have hint_ind : Integrable
      ((Ioi (2 / nu D n)).indicator (tailAbsIntegrand (S n) (nu D n) (D.mu n z) 0 x))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hint0 |>.mono_measure Measure.restrict_le_self
  have hint_rem : Integrable (itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (hint_ind.const_mul 3).mono' hmeas.aestronglyMeasurable (Eventually.of_forall hpt)
  refine ⟨hint_rem, ?_⟩
  change |∫ s in Ioi (0 : ℝ), itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x) s| ≤ _
  have h1 : |∫ s in Ioi (0 : ℝ),
        itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x) s| ≤
      ∫ s in Ioi (0 : ℝ),
        |itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x) s| :=
    abs_integral_le_integral_abs
  have h2 : (∫ s in Ioi (0 : ℝ),
        |itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x) s|) ≤
      ∫ s in Ioi (0 : ℝ),
        3 * (Ioi (2 / nu D n)).indicator (tailAbsIntegrand (S n) (nu D n) (D.mu n z) 0 x) s :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (hint_ind.const_mul 3)
      (Eventually.of_forall hpt)
  have h3 : (∫ s in Ioi (0 : ℝ),
        3 * (Ioi (2 / nu D n)).indicator (tailAbsIntegrand (S n) (nu D n) (D.mu n z) 0 x) s) =
      3 * ∫ s in Ioi (2 / nu D n), tailAbsIntegrand (S n) (nu D n) (D.mu n z) 0 x s := by
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioi,
      inter_eq_self_of_subset_right h0_sub]
  calc |∫ s in Ioi (0 : ℝ), itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x) s|
      ≤ 3 * ∫ s in Ioi (2 / nu D n), tailAbsIntegrand (S n) (nu D n) (D.mu n z) 0 x s :=
        (h1.trans h2).trans_eq h3
    _ ≤ 3 * (C * oldScaleA D (S n) n z *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖x‖)) :=
        mul_le_mul_of_nonneg_left hbd0 (by norm_num)
    _ = 3 * C * oldScaleA D (S n) n z *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖x‖) := by ring

/-- **`LaterOutputRem` from the three tail leaves** (source 4440-4457, 4509-4514). -/
theorem laterOutputRem_of_parts (D : SeqData)
    (hVel : G1.LaterOutput.TrainVelTailBound D)
    (hCore : G1.LaterOutput.UnforcedFlowKcCoreBound D)
    (hImp : G1.LaterOutput.UnforcedFlowKcImpulseBound D) : LaterOutputRem D :=
  laterOutputRem_of_laterOutputAbsOp D (laterOutputAbsOp_of_parts D hVel hCore hImp)

/-! ## 3. Bridge helper for Leaf 1 (`TrainVelTailBound D` from `PartI.TrainL2Decay`) -/

/-- From `PartI.TrainL2Decay` at `ρ = 2` (`c = ν⁻²`), the pre-overlap and post-overlap `L²(cell)`
velocity bounds hold on `[2/ν, ∞)` for `0 < ν ≤ min ν₁ (1/2)`. -/
theorem trainVelTail_exists_of_l2Decay (hL2 : UnforcedLeray.Short.PartI.TrainL2Decay) :
    ∃ (Cv ν₀ : ℝ), 0 ≤ Cv ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ s : ℝ, 2 / ν ≤ s →
          (s ≤ ν ^ (-2 : ℝ) →
            UnforcedLeray.Train.cellL2 (cOf ν) (tr.v s) ≤
              ENNReal.ofReal (Cv * (ν * s)⁻¹)) ∧
          UnforcedLeray.Train.cellL2 (cOf ν) (tr.v s) ≤
            ENNReal.ofReal (Cv * ((ν * s)⁻¹ + ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)))) := by
  obtain ⟨C, ν₁, hC, hν₁, h⟩ := hL2 2 (by norm_num)
  refine ⟨C, min ν₁ (1 / 2), hC.le, lt_min hν₁ (by norm_num), ?_⟩
  intro ν hν hνle tr htr s hs
  have hν₁' : ν ≤ ν₁ := hνle.trans (min_le_left _ _)
  have hν2 : ν ≤ 1 / 2 := hνle.trans (min_le_right _ _)
  have hcν : cOf ν = UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    unfold cOf UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν.le, Real.rpow_two]
  let P2 := UnforcedLeray.Short.PartI.trainPeriod 2 ν
  have hP2_def : P2 = ν ^ (-2 : ℝ) := rfl
  have key : ∀ tr' : UnforcedLeray.B0140.TrainSol ν P2,
      UnforcedLeray.Short.PartI.IsBUCTrain tr' →
        (s ≤ ν ^ (-2 : ℝ) →
          UnforcedLeray.Train.cellL2 P2 (tr'.v s) ≤
            ENNReal.ofReal (C * (ν * s)⁻¹)) ∧
        UnforcedLeray.Train.cellL2 P2 (tr'.v s) ≤
          ENNReal.ofReal (C * ((ν * s)⁻¹ + ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)))) := by
    intro tr' htr'
    have hP2_inv : P2 = (ν ^ 2)⁻¹ := by
      rw [hP2_def, Real.rpow_neg hν.le, Real.rpow_two]
    have hνsq : ν ^ 2 ≤ 1 / 4 := by nlinarith
    have hP2_ge4 : 4 ≤ P2 := by
      rw [hP2_inv, le_inv_comm₀ (by norm_num) (sq_pos_of_pos hν)]
      exact hνsq.trans_eq (by norm_num)
    have hP2_pos : 0 < P2 := by linarith
    have hs_pos : 0 < s := (div_pos two_pos hν).trans_le hs
    have hνs_pos : 0 < ν * s := mul_pos hν hs_pos
    obtain ⟨h1, h2⟩ := h ν hν hν₁' tr' htr' s hs_pos.le
    have hsc_ge_P2 : P2 ≤ UnforcedLeray.B0146.overlapAge ν P2 := by
      unfold UnforcedLeray.B0146.overlapAge
      rw [le_div_iff₀ hν]
      nlinarith
    have hw_inv : (UnforcedLeray.Train.width ν s)⁻¹ ≤ (ν * s)⁻¹ :=
      inv_anti₀ hνs_pos (by unfold UnforcedLeray.Train.width; linarith)
    refine ⟨fun hs_le => ?_, ?_⟩
    · refine (h1 (hs_le.trans hsc_ge_P2)).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left hw_inv hC.le
    · rcases le_total s (UnforcedLeray.B0146.overlapAge ν P2) with hsle | hsge
      · refine (h1 hsle).trans (ENNReal.ofReal_le_ofReal ?_)
        have hnn : 0 ≤ ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)) := by positivity
        exact mul_le_mul_of_nonneg_left (hw_inv.trans (le_add_of_nonneg_right hnn)) hC.le
      · refine (h2 hsge).trans (ENNReal.ofReal_le_ofReal ?_)
        set sc := UnforcedLeray.B0146.overlapAge ν P2
        have hsc_pos : 0 < sc := hP2_pos.trans_le hsc_ge_P2
        have hsc_le : sc ≤ P2 ^ 2 / ν := by
          unfold sc UnforcedLeray.B0146.overlapAge
          exact div_le_div_of_nonneg_right (by linarith) hν.le
        have hP2_sq_div : P2 ^ 2 / ν = ν ^ (-5 : ℝ) := by
          rw [hP2_inv]
          have hpow5 : ν ^ (-5 : ℝ) = (ν ^ 5)⁻¹ := by
            rw [Real.rpow_neg hν.le]
            exact congrArg Inv.inv (Real.rpow_natCast ν 5)
          rw [hpow5]
          have hν_ne : ν ≠ 0 := hν.ne'
          field_simp
        have hsc_le' : sc ≤ ν ^ (-5 : ℝ) := hsc_le.trans_eq hP2_sq_div
        have hdiv_rpow : (s / sc) ^ (-(3 / 4 : ℝ)) = s ^ (-(3 / 4 : ℝ)) * sc ^ (3 / 4 : ℝ) := by
          rw [Real.div_rpow hs_pos.le hsc_pos.le, div_eq_mul_inv, ← Real.rpow_neg hsc_pos.le,
            neg_neg]
        have hsc_rpow : sc ^ (3 / 4 : ℝ) ≤ ν ^ (-(15 / 4 : ℝ)) := by
          calc sc ^ (3 / 4 : ℝ) ≤ (ν ^ (-5 : ℝ)) ^ (3 / 4 : ℝ) :=
                Real.rpow_le_rpow hsc_pos.le hsc_le' (by norm_num)
            _ = ν ^ (-(15 / 4 : ℝ)) := by
                rw [← Real.rpow_mul hν.le]
                congr 1; norm_num
        have hP2_rpow : P2 ^ (-2 : ℝ) = ν ^ (4 : ℝ) := by
          rw [hP2_def, ← Real.rpow_mul hν.le]
          congr 1; norm_num
        have hprod : P2 ^ (-2 : ℝ) * (s / sc) ^ (-(3 / 4 : ℝ)) ≤
            ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)) := by
          rw [hP2_rpow, hdiv_rpow]
          calc ν ^ (4 : ℝ) * (s ^ (-(3 / 4 : ℝ)) * sc ^ (3 / 4 : ℝ))
              ≤ ν ^ (4 : ℝ) * (s ^ (-(3 / 4 : ℝ)) * ν ^ (-(15 / 4 : ℝ))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hsc_rpow (Real.rpow_nonneg hs_pos.le _))
                  (Real.rpow_nonneg hν.le _)
            _ = (ν ^ (4 : ℝ) * ν ^ (-(15 / 4 : ℝ))) * s ^ (-(3 / 4 : ℝ)) := by ring
            _ = ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)) := by
                rw [← Real.rpow_add hν]
                congr 2; norm_num
        have hnn : 0 ≤ (ν * s)⁻¹ := by positivity
        calc C * P2 ^ (-2 : ℝ) * (s / sc) ^ (-(3 / 4 : ℝ))
            = C * (P2 ^ (-2 : ℝ) * (s / sc) ^ (-(3 / 4 : ℝ))) := by ring
          _ ≤ C * (ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ))) :=
              mul_le_mul_of_nonneg_left hprod hC.le
          _ ≤ C * ((ν * s)⁻¹ + ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ))) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hnn) hC.le
  revert tr htr
  rw [hcν]
  exact key

/-- **`G1.LaterOutput.TrainVelTailBound D` from `PartI.TrainL2Decay`** (source 314-317, 4445-4450). -/
theorem trainVelTailBound_of_l2Decay (D : SeqData)
    (hL2 : UnforcedLeray.Short.PartI.TrainL2Decay) :
    G1.LaterOutput.TrainVelTailBound D := by
  intro dm dp hst
  obtain ⟨Cv, ν₀, hCv0, hν₀, h⟩ := trainVelTail_exists_of_l2Decay hL2
  have hev : ∀ᶠ n : ℕ in atTop, nu D n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨Cv, N, hCv0, fun n hn s hs =>
    h (nu D n) (retNu_pos D.Pl D.σ₀ n) (hN n hn).le (D.train n) (D.train_buc n) s hs⟩

/-! ## 4. Bridge helpers and proof of Leaf 2 (`UnforcedFlowKcCoreBound D`) -/

/-- Refined `TFKKcEmbed` retaining the dilation factor `a` on the left-hand side
(source 3176-3184, 3228-3240 `eq:ct-embeddings`). -/
theorem kcLp_mul_clockA_le_xNorm (m : ℝ) [Fact (1 < m)] (h8 : 8 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ c : ℝ, c = ν ^ (-2 : ℝ) → ∀ [Fact (0 < c)],
      ∀ a : ℝ, 1 ≤ a → a ≤ ν⁻¹ → ∀ ξ : Xmc c m,
        ENNReal.ofReal a * ENNReal.ofReal ‖kcLp ξ‖ ≤
          ENNReal.ofReal C *
            IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ)) := by
  obtain ⟨C1, hC1⟩ := IIIa.ctEmbeddings m h8
  obtain ⟨C2, hC2⟩ := IIIa.CTE.biotSavart_exists_uniform m h8
  refine ⟨max C1 0, le_max_right _ _, fun ν hν hν1 c hc _ a ha1 haν ξ => ?_⟩
  have hc0 : 0 < c := Fact.out
  have hc1 : 1 ≤ c := by
    have := one_le_cellLen_short hν hν1 hc le_rfl ((one_le_inv₀ hν).2 hν1)
    simpa [IIIa.cellLen] using this
  have ha0 : 0 < a := one_pos.trans_le ha1
  have hd1 : 1 ≤ IIIa.cellLen c a := one_le_cellLen_short hν hν1 hc ha1 haν
  obtain ⟨g, hg1, hg2, hge, hgz⟩ := rePart_evenRep_zeroCirc ξ
  have hrM : MemLp (fun x => (((xFn ξ x).re : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    (xFn_memLp ξ).re.ofReal
  have hgM : MemLp g 2 (B0579.cellMeasure c m) := hrM.ae_eq hg2.symm
  obtain ⟨u, hu, -⟩ := hC2 c hc1 g hgM hgz hge
  have hur : IIIa.IsBiotSavart c (fun x => (((xFn ξ x).re : ℝ) : ℂ)) u :=
    isBiotSavart_congr_ae hu hg1
  have hu' := isBiotSavart_jscaleInv c a hc0 ha0 g u hu
  obtain ⟨hGe, hGz⟩ := jscaleInv_even_zeroCirc c a hc0 ha0 g hge hgz
  obtain ⟨hMr, hNr⟩ := jscaleInv_rePart_memLp_le a ha1 ξ
  have hGr := jscaleInv_ae_cellMeasure c a m ha0 hg1
  have hGM : MemLp (IIIa.JscaleInv a g) 2 (B0579.cellMeasure (IIIa.cellLen c a) m) :=
    hMr.ae_eq hGr.symm
  have hEmb := hC1 _ hd1 _ hGM hGz hGe _ hu'
  have hxn : IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a g) =
      IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) :=
    eLpNorm_congr_ae hGr
  have hvel := IIIa.velNorm_scale c a hc0 ha0 u
  have hk := kcLp_norm_le_velNorm ξ u hur
  calc ENNReal.ofReal a * ENNReal.ofReal ‖kcLp ξ‖
      ≤ ENNReal.ofReal a * IIIa.velNorm c u := mul_le_mul_of_nonneg_left hk bot_le
    _ = IIIa.velNorm (IIIa.cellLen c a)
          (fun y j => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
            u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := hvel.symm
    _ ≤ ENNReal.ofReal ‖IIIa.quadQ (IIIa.cellLen c a) (IIIa.JscaleInv a g)‖ +
          IIIa.velNorm (IIIa.cellLen c a)
            (fun y j => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
              u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := le_add_self
    _ ≤ ENNReal.ofReal C1 * IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a g) := hEmb
    _ ≤ ENNReal.ofReal (max C1 0) * IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a g) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl
    _ = ENNReal.ofReal (max C1 0) * IIIa.xNorm (IIIa.cellLen c a) m
          (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) := by rw [hxn]
    _ ≤ ENNReal.ofReal (max C1 0) * IIIa.xNorm (IIIa.cellLen c a) m
          (IIIa.JscaleInv a (xFn ξ)) := mul_le_mul' le_rfl hNr

/-- Exact scale identity at `H = 2 / ν`:
`exp(Re λ · θ₀) θ₀^{Re κ} = ‖N_ν‖ ‖F_+(2/ν, 0)‖⁻¹` for `θ₀ = clockTheta ν (2/ν)`
(source 4442-4446). -/
theorem exp_theta0_mul_rpow_eq_nnu_div_fpm (lam κ : ℂ) {ν : ℝ} (hν : 0 < ν) :
    Real.exp (lam.re * IIIa.clockTheta ν (2 / ν)) *
        (IIIa.clockTheta ν (2 / ν)) ^ κ.re =
      ‖Nnu lam κ ν‖ * ‖Fpm true lam κ ν (2 / ν) 0‖⁻¹ := by
  set s₀ : ℝ := 2 / ν
  have hs₀ : 0 ≤ s₀ := div_nonneg zero_le_two hν.le
  set θ₀ : ℝ := IIIa.clockTheta ν s₀
  have hθ₀_pos : 0 < θ₀ := IIIa.theta_pos hν hs₀
  have hθ0_eq : IIIa.clockTheta ν 0 = ν⁻¹ := by
    unfold IIIa.clockTheta IIIa.clockA
    simp
  have hFpm : ‖Fpm true lam κ ν s₀ 0‖ =
      Real.exp (lam.re * (ν⁻¹ - θ₀)) * (ν⁻¹ / θ₀) ^ κ.re := by
    rw [fpm_true_eq]
    have has' : 0 < aOf ν s₀ := aOf_pos_of_nonneg ν s₀ hν hs₀
    have hat' : 0 < aOf ν 0 := aOf_pos_of_nonneg ν 0 hν le_rfl
    rw [fpm_norm_formula lam κ ν s₀ 0 (div_pos has' hat')]
    unfold θ₀ IIIa.clockTheta zOf aOf IIIa.clockA
    have hνne : ν ≠ 0 := hν.ne'
    have hasne : 1 + ν * s₀ ≠ 0 := has'.ne'
    have hdiff : s₀ / (1 + ν * s₀) - 0 / (1 + ν * 0) =
        ν⁻¹ - (ν * (1 + ν * s₀))⁻¹ := by
      field_simp
      ring
    have hrat : (1 + ν * s₀) / (1 + ν * 0) = ν⁻¹ / (ν * (1 + ν * s₀))⁻¹ := by
      field_simp
      ring
    rw [hdiff, hrat]
  have hNnu : ‖Nnu lam κ ν‖ = Real.exp (lam.re * ν⁻¹) * (ν⁻¹) ^ κ.re := by
    unfold Nnu
    rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hν]
    have hre : (lam / (ν : ℂ)).re = lam.re * ν⁻¹ := by
      rw [Complex.div_ofReal_re, div_eq_mul_inv]
    rw [hre, Complex.neg_re, Real.rpow_neg hν.le, ← Real.inv_rpow hν.le]
  have hFne : ‖Fpm true lam κ ν s₀ 0‖ ≠ 0 := by
    rw [hFpm]
    exact mul_ne_zero (Real.exp_pos _).ne'
      (Real.rpow_pos_of_pos (div_pos (inv_pos.2 hν) hθ₀_pos) _).ne'
  rw [eq_mul_inv_iff_mul_eq₀ hFne, hFpm, hNnu]
  have hexp : Real.exp (lam.re * θ₀) * Real.exp (lam.re * (ν⁻¹ - θ₀)) =
      Real.exp (lam.re * ν⁻¹) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrpow : θ₀ ^ κ.re * (ν⁻¹ / θ₀) ^ κ.re = (ν⁻¹) ^ κ.re := by
    rw [← Real.mul_rpow hθ₀_pos.le (div_nonneg (inv_nonneg.2 hν.le) hθ₀_pos.le),
      mul_div_cancel₀ _ hθ₀_pos.ne']
  calc Real.exp (lam.re * θ₀) * θ₀ ^ κ.re * (Real.exp (lam.re * (ν⁻¹ - θ₀)) * (ν⁻¹ / θ₀) ^ κ.re)
      = (Real.exp (lam.re * θ₀) * Real.exp (lam.re * (ν⁻¹ - θ₀))) *
          (θ₀ ^ κ.re * (ν⁻¹ / θ₀) ^ κ.re) := by ring
    _ = Real.exp (lam.re * ν⁻¹) * (ν⁻¹) ^ κ.re := by rw [hexp, hrpow]

/-- Elementary exponential-polynomial bound on `[1, ∞)`: for `γ > 0` and `θ ≥ 1`,
`θ ^ r * exp (-γ θ) ≤ γ⁻¹ ^ ⌈max r 0⌉₊ * (⌈max r 0⌉₊)!`. -/
private theorem rpow_mul_exp_neg_le {γ r θ : ℝ} (hγ : 0 < γ) (hθ : 1 ≤ θ) :
    θ ^ r * Real.exp (-γ * θ) ≤
      γ⁻¹ ^ ⌈max r 0⌉₊ * (Nat.factorial ⌈max r 0⌉₊ : ℝ) := by
  set n : ℕ := ⌈max r 0⌉₊
  have hθ0 : 0 < θ := one_pos.trans_le hθ
  have hrn : r ≤ (n : ℝ) := (le_max_left r 0).trans (Nat.le_ceil _)
  have hpow1 : θ ^ r ≤ θ ^ n := by
    rw [← Real.rpow_natCast θ n]
    exact Real.rpow_le_rpow_of_exponent_le hθ hrn
  have hfac_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos n)
  have hexp_le := Real.pow_div_factorial_le_exp (γ * θ) (mul_nonneg hγ.le hθ0.le) n
  have hmul_exp : (γ * θ) ^ n * Real.exp (-γ * θ) ≤ (Nat.factorial n : ℝ) := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    exact (div_le_iff₀ hfac_pos).1 hexp_le |>.trans_eq (mul_comm _ _)
  have hθn_eq : θ ^ n * Real.exp (-γ * θ) =
      γ⁻¹ ^ n * ((γ * θ) ^ n * Real.exp (-γ * θ)) := by
    rw [mul_pow, ← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hγ.ne', one_pow, one_mul]
  calc θ ^ r * Real.exp (-γ * θ)
      ≤ θ ^ n * Real.exp (-γ * θ) := mul_le_mul_of_nonneg_right hpow1 (Real.exp_pos _).le
    _ = γ⁻¹ ^ n * ((γ * θ) ^ n * Real.exp (-γ * θ)) := hθn_eq
    _ ≤ γ⁻¹ ^ n * (Nat.factorial n : ℝ) :=
        mul_le_mul_of_nonneg_left hmul_exp (pow_nonneg (inv_nonneg.2 hγ.le) n)

/-- On `s ≥ 2 / ν` with `clockTheta ν s ≥ 1`, the clock gain factor from `2 / ν` to `s`
satisfies
`exp (γ (θ₀ - θ)) (θ₀ / θ)^{κre} ≤ C(γ, κre) ν^9 s^4 a(s) (exp (γ θ₀) θ₀^{κre})`. -/
private theorem clock_decay_le_nu9_s4 {γ κre ν s : ℝ} (hγ : 0 < γ) (hν : 0 < ν)
    (hs : 2 / ν ≤ s) (hθ1 : 1 ≤ IIIa.clockTheta ν s) :
    Real.exp (γ * (IIIa.clockTheta ν (2 / ν) - IIIa.clockTheta ν s)) *
        (IIIa.clockTheta ν (2 / ν) / IIIa.clockTheta ν s) ^ κre ≤
      (16 * γ⁻¹ ^ ⌈max (5 - κre) 0⌉₊ * (Nat.factorial ⌈max (5 - κre) 0⌉₊ : ℝ)) *
        ν ^ 9 * s ^ 4 * IIIa.clockA ν s *
        (Real.exp (γ * IIIa.clockTheta ν (2 / ν)) * IIIa.clockTheta ν (2 / ν) ^ κre) := by
  set θ₀ : ℝ := IIIa.clockTheta ν (2 / ν)
  set θ : ℝ := IIIa.clockTheta ν s
  have hs0 : 0 ≤ s := (div_pos zero_lt_two hν).le.trans hs
  have hθ0_pos : 0 < θ₀ := IIIa.theta_pos hν (div_nonneg zero_le_two hν.le)
  have hθ_pos : 0 < θ := one_pos.trans_le hθ1
  have hexp_split : Real.exp (γ * (θ₀ - θ)) = Real.exp (γ * θ₀) * Real.exp (-γ * θ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrpow_split : (θ₀ / θ) ^ κre = θ₀ ^ κre * θ ^ (-κre) := by
    rw [div_eq_mul_inv, Real.mul_rpow hθ0_pos.le (inv_nonneg.2 hθ_pos.le),
      Real.inv_rpow hθ_pos.le, Real.rpow_neg hθ_pos.le]
  have hθ_split : θ ^ (-κre) = (θ⁻¹) ^ (5 : ℕ) * θ ^ (5 - κre) := by
    have h1 : θ ^ (-5 : ℝ) * θ ^ (5 - κre) = θ ^ (-κre) := by
      rw [← Real.rpow_add hθ_pos]
      congr 1
      ring
    have h2 : θ ^ (-5 : ℝ) = (θ⁻¹) ^ (5 : ℕ) := by
      rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hθ_pos.le,
        Real.rpow_natCast, inv_pow]
    rw [← h1, h2]
  have hθ_inv : θ⁻¹ = ν * IIIa.clockA ν s := by
    unfold θ IIIa.clockTheta
    exact inv_inv _
  have hνs : 2 ≤ ν * s := (div_le_iff₀' hν).1 hs
  have ha_le : IIIa.clockA ν s ≤ 2 * (ν * s) := by
    unfold IIIa.clockA
    linarith
  have ha_nonneg : 0 ≤ IIIa.clockA ν s := zero_le_one.trans (IIIa.one_le_clockA hν.le hs0)
  have hpow5 : (θ⁻¹) ^ (5 : ℕ) ≤ 16 * ν ^ 9 * s ^ 4 * IIIa.clockA ν s := by
    rw [hθ_inv]
    calc (ν * IIIa.clockA ν s) ^ (5 : ℕ)
        = ν ^ 5 * (IIIa.clockA ν s) ^ 4 * IIIa.clockA ν s := by ring
      _ ≤ ν ^ 5 * (2 * (ν * s)) ^ 4 * IIIa.clockA ν s := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ ha_nonneg ha_le 4) (pow_nonneg hν.le 5)) ha_nonneg
      _ = 16 * ν ^ 9 * s ^ 4 * IIIa.clockA ν s := by ring
  have hrem := rpow_mul_exp_neg_le (r := 5 - κre) hγ hθ1
  set K5 : ℝ := γ⁻¹ ^ ⌈max (5 - κre) 0⌉₊ * (Nat.factorial ⌈max (5 - κre) 0⌉₊ : ℝ)
  have hK5_nonneg : 0 ≤ K5 :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 hγ.le) _) (Nat.cast_nonneg _)
  have hprod : θ ^ (-κre) * Real.exp (-γ * θ) ≤
      (16 * K5) * ν ^ 9 * s ^ 4 * IIIa.clockA ν s := by
    rw [hθ_split, mul_assoc]
    calc (θ⁻¹) ^ (5 : ℕ) * (θ ^ (5 - κre) * Real.exp (-γ * θ))
        ≤ (16 * ν ^ 9 * s ^ 4 * IIIa.clockA ν s) * K5 :=
          mul_le_mul hpow5 hrem
            (mul_nonneg (Real.rpow_nonneg hθ_pos.le _) (Real.exp_pos _).le)
            (by positivity)
      _ = (16 * K5) * ν ^ 9 * s ^ 4 * IIIa.clockA ν s := by ring
  calc Real.exp (γ * (θ₀ - θ)) * (θ₀ / θ) ^ κre
      = (θ ^ (-κre) * Real.exp (-γ * θ)) * (Real.exp (γ * θ₀) * θ₀ ^ κre) := by
          rw [hexp_split, hrpow_split]; ring
    _ ≤ ((16 * K5) * ν ^ 9 * s ^ 4 * IIIa.clockA ν s) *
          (Real.exp (γ * θ₀) * θ₀ ^ κre) :=
        mul_le_mul_of_nonneg_right hprod
          (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hθ0_pos.le _))
    _ = (16 * γ⁻¹ ^ ⌈max (5 - κre) 0⌉₊ * (Nat.factorial ⌈max (5 - κre) 0⌉₊ : ℝ)) *
          ν ^ 9 * s ^ 4 * IIIa.clockA ν s *
          (Real.exp (γ * θ₀) * θ₀ ^ κre) := by
        unfold K5
        ring

/-- **Proof of Leaf 2 (`G1.LaterOutput.UnforcedFlowKcCoreBound D`) from
`IIIa.FullClockLongForward`** (source lines 2836-2860, 3020-3022, 3228-3240, 4440-4455). -/
theorem unforcedFlowKcCoreBound_of_longForward (D : SeqData)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward) :
    G1.LaterOutput.UnforcedFlowKcCoreBound D := by
  intro dm dp hst κ _hκ m _ hm8
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨b₀, hb₀⟩ := hLF D.Pl hst.planar m hm8
  refine ⟨max b₀ 1, le_max_right b₀ 1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_right b₀ 1).trans hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  obtain ⟨C, ν₁, hν₁, hC⟩ := hb₀ b ((le_max_left b₀ 1).trans hb)
  obtain ⟨K₀, hK₀, hK_emb⟩ := kcLp_mul_clockA_le_xNorm (m := m) hm8
  set γ : ℝ := D.Pl.eigenvalue.re
  set κre : ℝ := D.Pl.kappa.re
  have hγ : 0 < γ := hst.gamma_pos
  set K5 : ℝ := 16 * γ⁻¹ ^ ⌈max (5 - κre) 0⌉₊ * (Nat.factorial ⌈max (5 - κre) 0⌉₊ : ℝ)
  have hK5_nonneg : 0 ≤ K5 := by positivity
  set D₀ : ℝ := (3 : ℝ) ^ ((3 : ℝ) / 2)
  have hD₀_nonneg : 0 ≤ D₀ := by positivity
  set Cu : ℝ := K₀ * max C 0 * K5 * D₀
  have hCu_nonneg : 0 ≤ Cu := by positivity
  have hν_small : ∀ᶠ n : ℕ in atTop, nu D n < min ν₁ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (lt_min hν₁ one_pos))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hν_small
  refine ⟨Cu, N, hCu_nonneg, fun n hn FI => ?_⟩
  let ν : ℝ := nu D n
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hν_lt : ν < min ν₁ 1 := hN n hn
  have hνa : ν ≤ ν₁ := hν_lt.le.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν_lt.le.trans (min_le_right _ _)
  have hcOf : cOf ν = ν ^ (-2 : ℝ) := by
    rw [cOf, Real.rpow_neg hν.le, Real.rpow_two]
  intro w s hs_lo hs_hi
  have key : ∀ (c : ℝ) (hc : c = ν ^ (-2 : ℝ)) [Fact (0 < c)]
      (tr : UnforcedLeray.B0140.TrainSol ν c) (_ : UnforcedLeray.Short.PartI.IsBUCTrain tr)
      (FI' : FlatInstData κ ν c m tr) (w' : Xmc c m),
      ‖kcLp (FI'.ev.U s (2 / ν) w')‖ ≤
        Cu * ν ^ 9 * s ^ 4 *
          (‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ *
            (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ * ‖w'‖)) := by
    intro c hc hfact tr hbuc FI' w'
    subst hc
    obtain ⟨-, hLong⟩ := hC ν ⟨hν, hνa⟩ tr hbuc
    set s₀ : ℝ := 2 / ν
    have hs₀_nonneg : 0 ≤ s₀ := div_nonneg zero_le_two hν.le
    have hs_nonneg : 0 ≤ s := hs₀_nonneg.trans hs_lo
    have h1 : ν * s ≤ (ν * b)⁻¹ - 1 := by
      have := mul_le_mul_of_nonneg_left hs_hi hν.le
      rwa [IIIa.coreEnd, mul_inv_cancel_left₀ hν.ne'] at this
    have ha1 : 1 ≤ IIIa.clockA ν s := IIIa.one_le_clockA hν.le hs_nonneg
    have hapos : 0 < IIIa.clockA ν s := one_pos.trans_le ha1
    have hνb : ν ≤ ν * b := by nlinarith
    have hale : IIIa.clockA ν s ≤ ν⁻¹ := by
      have : 1 + ν * s ≤ (ν * b)⁻¹ := by linarith
      exact this.trans (inv_anti₀ hν hνb)
    have hθb : b ≤ IIIa.clockTheta ν s := by
      unfold IIIa.clockTheta
      rw [le_inv_comm₀ hbpos (mul_pos hν hapos)]
      have h4 : 1 + ν * s ≤ (ν * b)⁻¹ := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hν.le
      have h6 : ν * (ν * b)⁻¹ = b⁻¹ := by field_simp
      exact h5.trans_eq h6
    have hθ1 : 1 ≤ IIIa.clockTheta ν s := hb1.trans hθb
    obtain ⟨u', hu'⟩ := FI'.ev.flow s₀ hs₀_nonneg w'
    have hLF1 := hLong s₀ s hs₀_nonneg hs_lo hθb (xFn w') (xFn_memLp w') (xFn_zeroCirc w') _ _ hu'
    have has₀_eq : IIIa.clockA ν s₀ = 3 := by
      unfold IIIa.clockA s₀
      rw [mul_div_cancel₀ _ hν.ne']
      norm_num
    have has₀1 : 1 ≤ IIIa.clockA ν s₀ := by rw [has₀_eq]; norm_num
    have hs2_scale : IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s₀)) m
        (IIIa.JscaleInv (IIIa.clockA ν s₀) (xFn w')) ≤
        ENNReal.ofReal D₀ * ENNReal.ofReal ‖w'‖ := by
      have h := IIIa.xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m (IIIa.clockA ν s₀) hm0 has₀1
        (xFn w') (xFn_memLp w')
      rw [xNorm_xFn_eq] at h
      exact h.trans_eq (by rw [has₀_eq])
    have hstep1 := hK_emb ν hν hν1 _ rfl (IIIa.clockA ν s) ha1 hale (FI'.ev.U s s₀ w')
    set G_gain : ℝ := Real.exp (γ * (IIIa.clockTheta ν s₀ - IIIa.clockTheta ν s)) *
      (IIIa.clockTheta ν s₀ / IIIa.clockTheta ν s) ^ κre
    have hG_nonneg : 0 ≤ G_gain :=
      mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg (div_nonneg (IIIa.theta_pos hν hs₀_nonneg).le (one_pos.trans_le hθ1).le) _)
    have hCG_le : C * G_gain ≤ max C 0 * G_gain :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hG_nonneg
    have hcalc : ENNReal.ofReal (‖kcLp (FI'.ev.U s s₀ w')‖ * IIIa.clockA ν s) ≤
        ENNReal.ofReal (K₀ * (max C 0 * G_gain) * (D₀ * ‖w'‖)) := by
      rw [ENNReal.ofReal_mul (norm_nonneg _), mul_comm (ENNReal.ofReal ‖kcLp (FI'.ev.U s s₀ w')‖)]
      calc ENNReal.ofReal (IIIa.clockA ν s) * ENNReal.ofReal ‖kcLp (FI'.ev.U s s₀ w')‖
          ≤ ENNReal.ofReal K₀ * IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)) m
              (IIIa.JscaleInv (IIIa.clockA ν s) (xFn (FI'.ev.U s s₀ w'))) := hstep1
        _ ≤ ENNReal.ofReal K₀ * (ENNReal.ofReal (max C 0 * G_gain) *
              (ENNReal.ofReal D₀ * ENNReal.ofReal ‖w'‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ bot_le
            refine (hLF1.trans (mul_le_mul_of_nonneg_right
              (ENNReal.ofReal_le_ofReal (by simpa [G_gain, mul_assoc] using hCG_le)) bot_le)).trans ?_
            exact mul_le_mul_of_nonneg_left hs2_scale bot_le
        _ = ENNReal.ofReal (K₀ * (max C 0 * G_gain) * (D₀ * ‖w'‖)) := by
            rw [← ENNReal.ofReal_mul hD₀_nonneg,
              ← ENNReal.ofReal_mul (mul_nonneg (le_max_right C 0) hG_nonneg),
              ← ENNReal.ofReal_mul hK₀]
            congr 1
            ring
    have hreal : ‖kcLp (FI'.ev.U s s₀ w')‖ * IIIa.clockA ν s ≤
        K₀ * (max C 0 * G_gain) * (D₀ * ‖w'‖) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcalc
    have hG_bd := clock_decay_le_nu9_s4 (κre := κre) hγ hν hs_lo hθ1
    rw [exp_theta0_mul_rpow_eq_nnu_div_fpm D.Pl.eigenvalue D.Pl.kappa hν] at hG_bd
    set NF : ℝ := ‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ *
      ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν s₀ 0‖⁻¹
    have hprod_le : ‖kcLp (FI'.ev.U s s₀ w')‖ * IIIa.clockA ν s ≤
        (Cu * ν ^ 9 * s ^ 4 * (NF * ‖w'‖)) * IIIa.clockA ν s := by
      calc ‖kcLp (FI'.ev.U s s₀ w')‖ * IIIa.clockA ν s
          ≤ K₀ * (max C 0 * G_gain) * (D₀ * ‖w'‖) := hreal
        _ = (K₀ * max C 0 * D₀ * ‖w'‖) * G_gain := by ring
        _ ≤ (K₀ * max C 0 * D₀ * ‖w'‖) * (K5 * ν ^ 9 * s ^ 4 * IIIa.clockA ν s * NF) :=
            mul_le_mul_of_nonneg_left hG_bd (by positivity)
        _ = (Cu * ν ^ 9 * s ^ 4 * (NF * ‖w'‖)) * IIIa.clockA ν s := by
            unfold Cu K5
            ring
    have hfinal := le_of_mul_le_mul_right hprod_le hapos
    simpa [NF, s₀, mul_assoc] using hfinal
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  exact key (cOf ν) hcOf (D.train n) (D.train_buc n) FI w

/-! ## 5. Leaf 3 (`UnforcedFlowKcImpulseBound D`) from `FullClockLongForward` and `CTKineticImpulse` -/

/-- Real-part projection `x ↦ (x + conjX x) / 2` on `Xmc c m`. -/
private def reProj {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) : Xmc c m :=
  ((2 : ℂ)⁻¹) • (x + conjX x)

private theorem conjX_reProj {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) :
    conjX (reProj x) = reProj x := by
  unfold reProj
  rw [conjX_smul, conjX_add, conjX_conjX, add_comm]
  have h2 : (starRingEnd ℂ) (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, map_ofNat]
  rw [h2]

private theorem norm_reProj_le {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) :
    ‖reProj x‖ ≤ ‖x‖ := by
  unfold reProj
  rw [norm_smul, norm_inv, Complex.norm_ofNat]
  have h1 := norm_add_le x (conjX x)
  rw [norm_conjX] at h1
  linarith

private theorem reProj_comm_U {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (ev : TrainEvolution m tr)
    (s t : ℝ) (x : Xmc c m) :
    ev.U s t (reProj x) = reProj (ev.U s t x) := by
  unfold reProj
  rw [map_smul, map_add, ev.real]

private theorem reX_reProj {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) :
    reX (reProj x).1 = reX x.1 := by
  refine Lp.ext ?_
  have hsmul : ((reProj x).1 : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m]
      fun p => (2 : ℂ)⁻¹ * ((x.1 : ℝ × ℝ → ℂ) p + (conjAmb x.1 : ℝ × ℝ → ℂ) p) := by
    change (((2 : ℂ)⁻¹ • (x.1 + conjAmb x.1) : XAmb c m) : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m] _
    filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (x.1 + conjAmb x.1),
      Lp.coeFn_add x.1 (conjAmb x.1)] with p hp1 hp2
    rw [hp1, Pi.smul_apply, hp2, Pi.add_apply, smul_eq_mul]
  filter_upwards [coeFn_reX (reProj x).1, coeFn_reX x.1, hsmul, coeFn_conjAmb x.1] with
    p hp1 hp2 hp3 hp4
  rw [hp1, hp2, hp3, hp4]
  simp [Complex.mul_re]
  ring

private theorem kcLp_reProj {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (x : Xmc c m) :
    kcLp (reProj x) = kcLp x := by
  unfold kcLp
  congr 1
  exact reX_reProj x

private theorem jscale_jscaleInv_eq {a : ℝ} (ha : 0 < a) (g : ℝ × ℝ → ℂ) :
    IIIa.Jscale a (IIIa.JscaleInv a g) = g := by
  ext ⟨x1, x2⟩
  unfold IIIa.Jscale IIIa.JscaleInv
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have ha_pow : a ^ (-2 : ℝ) * a ^ 2 = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')]
  rw [← mul_assoc, ← Complex.ofReal_mul, ha_pow, Complex.ofReal_one, one_mul]
  congr 1
  ext <;> simp [mul_div_cancel₀ _ hsq]

private theorem isLinearisedFlow_congr_initial {ν c m t : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f f' : ℝ × ℝ → ℂ}
    {ω : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (h : IIIa.IsLinearisedFlow ν c m tr t f ω u)
    (hf : f =ᵐ[volume.restrict (B0579.cell c)] f') :
    IIIa.IsLinearisedFlow ν c m tr t f' ω u where
  initial := h.initial.trans hf
  memX := h.memX
  strongCont := h.strongCont
  biotSavart := h.biotSavart
  integrable := h.integrable
  timeIntegrable := h.timeIntegrable
  weak φ hφ s hs := by
    rw [h.weak φ hφ s hs]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]

private theorem clockAge_eq_coreEnd {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    IIIa.clockAge ν r = IIIa.coreEnd ν r := by
  have hνne : ν ≠ 0 := hν.ne'
  have hrne : r ≠ 0 := hr.ne'
  unfold IIIa.clockAge IIIa.coreEnd
  field_simp

private theorem clockAge_clockTheta {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    IIIa.clockAge ν (IIIa.clockTheta ν s) = s := by
  have hνne : ν ≠ 0 := hν.ne'
  have ha : 0 < 1 + ν * s := by nlinarith
  have hane : 1 + ν * s ≠ 0 := ha.ne'
  unfold IIIa.clockAge IIIa.clockTheta IIIa.clockA
  field_simp
  ring

private theorem inv_nu_mul_clockTheta {ν s : ℝ} (hν : 0 < ν) :
    (ν * IIIa.clockTheta ν s)⁻¹ = IIIa.clockA ν s := by
  have hνne : ν ≠ 0 := hν.ne'
  unfold IIIa.clockTheta
  field_simp

private theorem clockA_coreEnd {ν r : ℝ} (hν : 0 < ν) :
    IIIa.clockA ν (IIIa.coreEnd ν r) = (ν * r)⁻¹ := by
  have hνne : ν ≠ 0 := hν.ne'
  unfold IIIa.clockA IIIa.coreEnd
  field_simp
  ring

private theorem clockTheta_coreEnd {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    IIIa.clockTheta ν (IIIa.coreEnd ν r) = r := by
  have hνne : ν ≠ 0 := hν.ne'
  have hrne : r ≠ 0 := hr.ne'
  unfold IIIa.clockTheta
  rw [clockA_coreEnd hν]
  field_simp

private theorem dOfTheta_eq_cellLen {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    IIIa.dOfTheta ν θ = IIIa.cellLen (ν ^ (-2 : ℝ)) (ν * θ)⁻¹ := by
  unfold IIIa.dOfTheta IIIa.cellLen
  have hνne : ν ≠ 0 := hν.ne'
  have hθne : θ ≠ 0 := hθ.ne'
  have h1 : ν ^ (-2 : ℝ) = Real.sqrt ((ν ^ 4)⁻¹) := by
    have hsq : ((ν ^ 2)⁻¹) ^ 2 = (ν ^ 4)⁻¹ := by ring
    rw [Real.rpow_neg hν.le, Real.rpow_two, ← hsq, Real.sqrt_sq (by positivity)]
  rw [h1, ← Real.sqrt_div (by positivity)]
  congr 1
  field_simp

private theorem kcLp_mul_clockA_le_kinNorm {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {a : ℝ} (ha : 0 < a) {ξ : Xmc c m} (hreal : conjX ξ = ξ) :
    ENNReal.ofReal a * ENNReal.ofReal ‖kcLp ξ‖ ≤
      IIIa.kinNorm (IIIa.cellLen c a) (IIIa.JscaleInv a (xFn ξ)) := by
  have hc : 0 < c := Fact.out
  have hd : 0 < IIIa.cellLen c a := div_pos hc (Real.sqrt_pos.2 ha)
  have hbs0 : IIIa.IsBiotSavart c (xFn ξ) (kcC ξ) := isBiotSavart_kc hreal
  have hx_re : xFn ξ =ᵐ[volume.restrict (B0579.cell c)]
      fun x => (((xFn ξ x).re : ℝ) : ℂ) := by
    filter_upwards [xFn_of_real hreal, ae_cell_of_ae_cellMeasure (coeFn_reX ξ.1)] with x h1 h2
    have h2' : reX ξ.1 x = (xFn ξ x).re := h2
    exact h1.trans (by rw [h2'])
  have hbs_re : IIIa.IsBiotSavart c (fun x => (((xFn ξ x).re : ℝ) : ℂ)) (kcC ξ) :=
    isBiotSavart_congr_ae hbs0 hx_re
  have hkc_le : ENNReal.ofReal ‖kcLp ξ‖ ≤ IIIa.velNorm c (kcC ξ) :=
    kcLp_norm_le_velNorm ξ (kcC ξ) hbs_re
  have hbs_a := isBiotSavart_jscaleInv c a hc ha (xFn ξ) (kcC ξ) hbs0
  have hvel_a := IIIa.velNorm_scale c a hc ha (kcC ξ)
  refine (mul_le_mul_of_nonneg_left hkc_le bot_le).trans (hvel_a.symm.le.trans ?_)
  refine le_iInf₂ fun v hv => ?_
  have hae := IIIa.CTE.isBiotSavart_unique (IIIa.cellLen c a) hd
    (IIIa.JscaleInv a (xFn ξ)) _ v hbs_a hv
  unfold IIIa.velNorm
  refine le_of_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact eLpNorm_congr_ae (hae.mono fun x hx => congr_fun hx j)

private theorem exists_kinNorm_reSym_le (m : ℝ) [Fact (1 < m)] (hm8 : 8 < m) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ {ν c a : ℝ} [Fact (0 < c)],
      0 < ν → ν ≤ 1 → c = ν ^ (-2 : ℝ) → 1 ≤ a → a ≤ ν⁻¹ →
      ∀ ξ : Xmc c m,
        MemLp (IIIa.JscaleInv a (reSym ξ)) 2 (B0579.cellMeasure (IIIa.cellLen c a) m) ∧
        IIIa.HasZeroCirculation (IIIa.cellLen c a) (IIIa.JscaleInv a (reSym ξ)) ∧
        IIIa.IsCentrallyEven (IIIa.JscaleInv a (reSym ξ)) ∧
        IIIa.kinNorm (IIIa.cellLen c a) (IIIa.JscaleInv a (reSym ξ)) ≤
          ENNReal.ofReal K₁ * IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ)) := by
  obtain ⟨C2, hC2⟩ := IIIa.CTE.biotSavart_exists_uniform m hm8
  refine ⟨max C2 0, le_max_right C2 0, fun {ν c a} _ hν hν1 hc ha1 haν ξ => ?_⟩
  have hc0 : 0 < c := Fact.out
  have ha0 : 0 < a := one_pos.trans_le ha1
  have hd1 : 1 ≤ IIIa.cellLen c a := one_le_cellLen_short hν hν1 hc ha1 haν
  have h1 := reSym_ae ξ
  have h2 := rePart_zeroCirc_aux ξ
  have hgz : IIIa.HasZeroCirculation c (reSym ξ) :=
    ⟨h2.1.congr h1.symm, by rw [integral_congr_ae h1]; exact h2.2⟩
  have hge : IIIa.IsCentrallyEven (reSym ξ) := reSym_even ξ
  obtain ⟨hGe, hGz⟩ := jscaleInv_even_zeroCirc c a hc0 ha0 (reSym ξ) hge hgz
  obtain ⟨hMr, hNr⟩ := jscaleInv_rePart_memLp_le a ha1 ξ
  have hGr := jscaleInv_ae_cellMeasure c a m ha0 h1
  have hGM : MemLp (IIIa.JscaleInv a (reSym ξ)) 2 (B0579.cellMeasure (IIIa.cellLen c a) m) :=
    hMr.ae_eq hGr.symm
  obtain ⟨u_b, hu_b, hv_b⟩ :=
    hC2 (IIIa.cellLen c a) hd1 (IIIa.JscaleInv a (reSym ξ)) hGM hGz hGe
  have hxn : IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (reSym ξ)) =
      IIIa.xNorm (IIIa.cellLen c a) m
        (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) :=
    eLpNorm_congr_ae hGr
  refine ⟨hGM, hGz, hGe, ?_⟩
  calc IIIa.kinNorm (IIIa.cellLen c a) (IIIa.JscaleInv a (reSym ξ))
      ≤ IIIa.velNorm (IIIa.cellLen c a) u_b := iInf₂_le u_b hu_b
    _ ≤ ENNReal.ofReal C2 *
          IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (reSym ξ)) := hv_b
    _ ≤ ENNReal.ofReal (max C2 0) *
          IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ)) := by
        rw [hxn]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hNr

/-- **Proof of Leaf 3 (`G1.LaterOutput.UnforcedFlowKcImpulseBound D`) from
`IIIa.FullClockLongForward` and `IIIa.CTKineticImpulse`** (source lines 3228-3251, 4440-4455). -/
theorem unforcedFlowKcImpulseBound_of_longForward (D : SeqData)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    G1.LaterOutput.UnforcedFlowKcImpulseBound D := by
  intro dm dp hst κ _hκ m _ hm8
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨b₁, hb₁⟩ := hLF D.Pl hst.planar m hm8
  obtain ⟨b₂, hb₂⟩ := hKI D.Pl hst.planar m hm8
  refine ⟨max (max b₁ b₂) 1, le_max_right _ 1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_right _ 1).trans hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  have hb_le1 : b₁ ≤ b := ((le_max_left b₁ b₂).trans (le_max_left _ 1)).trans hb
  have hb_le2 : b₂ ≤ b := ((le_max_right b₁ b₂).trans (le_max_left _ 1)).trans hb
  obtain ⟨C_LF, ν₁, hν₁, hC_LF⟩ := hb₁ b hb_le1
  obtain ⟨C_KI, ν₂, hν₂, hC_KI⟩ := hb₂ b hb_le2
  obtain ⟨K₁, hK₁, hK_kin⟩ := exists_kinNorm_reSym_le m hm8
  set γ : ℝ := D.Pl.eigenvalue.re
  set κre : ℝ := D.Pl.kappa.re
  set E_b : ℝ := Real.exp (-γ * b) * b ^ (-κre)
  have hEb_nonneg : 0 ≤ E_b :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hbpos.le _)
  set D₀ : ℝ := (3 : ℝ) ^ ((3 : ℝ) / 2)
  have hD₀_nonneg : 0 ≤ D₀ := by positivity
  set Cu : ℝ := max C_KI 0 * b * K₁ * max C_LF 0 * E_b * D₀
  have hCu_nonneg : 0 ≤ Cu := by positivity
  set ν_cap : ℝ := min (min ν₁ ν₂) ((3 * b)⁻¹)
  have hν_cap_pos : 0 < ν_cap :=
    lt_min (lt_min hν₁ hν₂) (inv_pos.2 (by positivity))
  have hν_small : ∀ᶠ n : ℕ in atTop, nu D n < ν_cap :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν_cap_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hν_small
  refine ⟨Cu, N, hCu_nonneg, fun n hn FI => ?_⟩
  let ν : ℝ := nu D n
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hν_lt : ν < ν_cap := hN n hn
  have hνa1 : ν ≤ ν₁ := hν_lt.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνa2 : ν ≤ ν₂ := hν_lt.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3b : ν ≤ (3 * b)⁻¹ := hν_lt.le.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hν3b.trans ((inv_le_one₀ (by positivity)).2 (by linarith))
  have hcOf : cOf ν = ν ^ (-2 : ℝ) := by
    rw [cOf, Real.rpow_neg hν.le, Real.rpow_two]
  intro w s hs_hi
  have key : ∀ (c : ℝ) (hc : c = ν ^ (-2 : ℝ)) [Fact (0 < c)]
      (tr : UnforcedLeray.B0140.TrainSol ν c) (_ : UnforcedLeray.Short.PartI.IsBUCTrain tr)
      (FI' : FlatInstData κ ν c m tr) (w' : Xmc c m),
      ‖kcLp (FI'.ev.U s (2 / ν) w')‖ ≤
        Cu * ν *
          (‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ *
            (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ * ‖w'‖)) := by
    intro c hc hfact tr hbuc FI' w'
    subst hc
    obtain ⟨-, hLong⟩ := hC_LF ν ⟨hν, hνa1⟩ tr hbuc
    have hKI_inst := hC_KI ν ⟨hν, hνa2⟩ tr hbuc
    set s₀ : ℝ := 2 / ν
    set s_b : ℝ := IIIa.coreEnd ν b
    have hs₀_nonneg : 0 ≤ s₀ := div_nonneg zero_le_two hν.le
    have h3_le : 3 ≤ (ν * b)⁻¹ := by
      have h1 := mul_le_mul_of_nonneg_right hν3b (by positivity : (0 : ℝ) ≤ 3 * b)
      rw [inv_mul_cancel₀ (by positivity)] at h1
      rw [le_inv_comm₀ (by positivity : (0 : ℝ) < 3) (mul_pos hν hbpos)]
      linarith
    have hs_b_lo : s₀ ≤ s_b := by
      unfold s₀ s_b IIIa.coreEnd
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hν.le)
    have hs_b_nonneg : 0 ≤ s_b := hs₀_nonneg.trans hs_b_lo
    have hs_nonneg : 0 ≤ s := hs_b_nonneg.trans hs_hi
    set w_re : Xmc (ν ^ (-2 : ℝ)) m := reProj w'
    set x_b : Xmc (ν ^ (-2 : ℝ)) m := FI'.ev.U s_b s₀ w_re
    set x_s : Xmc (ν ^ (-2 : ℝ)) m := FI'.ev.U s s₀ w_re
    have hkc_eq : kcLp (FI'.ev.U s s₀ w') = kcLp x_s := by
      change kcLp (FI'.ev.U s s₀ w') = kcLp (FI'.ev.U s s₀ (reProj w'))
      rw [reProj_comm_U, kcLp_reProj]
    have hreal_b : conjX x_b = x_b := by
      change conjX (FI'.ev.U s_b s₀ (reProj w')) = FI'.ev.U s_b s₀ (reProj w')
      rw [reProj_comm_U, conjX_reProj]
    have hreal_s : conjX x_s = x_s := by
      change conjX (FI'.ev.U s s₀ (reProj w')) = FI'.ev.U s s₀ (reProj w')
      rw [reProj_comm_U, conjX_reProj]
    have hcocycle : x_s = FI'.ev.U s s_b x_b := by
      have hc := FI'.ev.cocycle s s_b s₀ hs₀_nonneg hs_b_lo hs_hi
      exact (congr_arg (fun L => L w_re) hc).symm
    set a_b : ℝ := (ν * b)⁻¹
    have ha_b_eq : IIIa.clockA ν s_b = a_b := clockA_coreEnd hν
    have ha_b1 : 1 ≤ a_b := by linarith
    have ha_b0 : 0 < a_b := one_pos.trans_le ha_b1
    have ha_b_le : a_b ≤ ν⁻¹ := inv_anti₀ hν (by nlinarith)
    have hθ_b_eq : IIIa.clockTheta ν s_b = b := clockTheta_coreEnd hν hbpos
    obtain ⟨u_lf, hu_lf⟩ := FI'.ev.flow s₀ hs₀_nonneg w_re
    have hLF1 := hLong s₀ s_b hs₀_nonneg hs_b_lo (le_of_eq hθ_b_eq.symm)
      (xFn w_re) (xFn_memLp w_re) (xFn_zeroCirc w_re) _ _ hu_lf
    rw [ha_b_eq, hθ_b_eq] at hLF1
    have has₀_eq : IIIa.clockA ν s₀ = 3 := by
      unfold IIIa.clockA s₀
      rw [mul_div_cancel₀ _ hν.ne']
      norm_num
    have has₀1 : 1 ≤ IIIa.clockA ν s₀ := by rw [has₀_eq]; norm_num
    have hs2_scale : IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s₀)) m
        (IIIa.JscaleInv (IIIa.clockA ν s₀) (xFn w_re)) ≤
        ENNReal.ofReal D₀ * ENNReal.ofReal ‖w_re‖ := by
      have h := IIIa.xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m (IIIa.clockA ν s₀) hm0 has₀1
        (xFn w_re) (xFn_memLp w_re)
      rw [xNorm_xFn_eq] at h
      exact h.trans_eq (by rw [has₀_eq])
    obtain ⟨hGM, hGz, hGe, hkin_b⟩ := hK_kin hν hν1 rfl ha_b1 ha_b_le x_b
    set h_b : ℝ × ℝ → ℂ := IIIa.JscaleInv a_b (reSym x_b)
    have hd_b_eq : IIIa.dOfTheta ν b = IIIa.cellLen (ν ^ (-2 : ℝ)) a_b :=
      dOfTheta_eq_cellLen hν hbpos
    set θ : ℝ := IIIa.clockTheta ν s
    have hθ_pos : 0 < θ := IIIa.theta_pos hν hs_nonneg
    have hθ_le_b : θ ≤ b := by
      rw [← hθ_b_eq]
      unfold θ IIIa.clockTheta
      refine inv_anti₀ (mul_pos hν (IIIa.one_le_clockA hν.le hs_b_nonneg |>.trans_lt' one_pos)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hν.le
      unfold IIIa.clockA
      linarith [mul_le_mul_of_nonneg_left hs_hi hν.le]
    set a_s : ℝ := IIIa.clockA ν s
    have ha_s_pos : 0 < a_s := one_pos.trans_le (IIIa.one_le_clockA hν.le hs_nonneg)
    have ha_s_eq : (ν * θ)⁻¹ = a_s := inv_nu_mul_clockTheta hν
    have hd_s_eq : IIIa.dOfTheta ν θ = IIIa.cellLen (ν ^ (-2 : ℝ)) a_s := by
      rw [dOfTheta_eq_cellLen hν hθ_pos, ha_s_eq]
    set Zh : ℝ × ℝ → ℂ := IIIa.JscaleInv (ν * θ)⁻¹ (xFn x_s)
    have hHeat : IIIa.HeatEvolvesTo ν m tr b θ h_b Zh := by
      obtain ⟨u_b, hu_b⟩ := FI'.ev.flow s_b hs_b_nonneg x_b
      have hx_b_re : xFn x_b =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] reSym x_b := by
        have h1 : xFn x_b =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
            fun x => (((xFn x_b x).re : ℝ) : ℂ) := by
          filter_upwards [xFn_of_real hreal_b, ae_cell_of_ae_cellMeasure (coeFn_reX x_b.1)] with
            x hx1 hx2
          have hx2' : reX x_b.1 x = (xFn x_b x).re := hx2
          exact hx1.trans (by rw [hx2'])
        exact h1.trans (reSym_ae x_b).symm
      have hj_eq : IIIa.Jscale (ν * b)⁻¹ h_b = reSym x_b :=
        jscale_jscaleInv_eq ha_b0 (reSym x_b)
      have hu_b' : IIIa.IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr (IIIa.clockAge ν b)
          (IIIa.Jscale (ν * b)⁻¹ h_b) (fun t => xFn (FI'.ev.U t s_b x_b)) u_b := by
        rw [clockAge_eq_coreEnd hν hbpos, hj_eq]
        exact isLinearisedFlow_congr_initial hu_b hx_b_re
      refine ⟨fun t => xFn (FI'.ev.U t s_b x_b), u_b, hu_b', ?_⟩
      dsimp only
      rw [clockAge_clockTheta hν hs_nonneg, ← hcocycle]
    have hGM' : MemLp h_b 2 (B0579.cellMeasure (IIIa.dOfTheta ν b) m) := by
      rwa [hd_b_eq]
    have hGz' : IIIa.HasZeroCirculation (IIIa.dOfTheta ν b) h_b := by
      rwa [hd_b_eq]
    have hKI1 := hKI_inst b θ hθ_pos hθ_le_b le_rfl h_b Zh hGM' hGz' hGe hHeat
    have hkin_s : ENNReal.ofReal a_s * ENNReal.ofReal ‖kcLp x_s‖ ≤
        IIIa.kinNorm (IIIa.dOfTheta ν θ) Zh := by
      rw [hd_s_eq]
      change ENNReal.ofReal a_s * ENNReal.ofReal ‖kcLp x_s‖ ≤
        IIIa.kinNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) a_s)
          (IIIa.JscaleInv (ν * θ)⁻¹ (xFn x_s))
      rw [ha_s_eq]
      exact kcLp_mul_clockA_le_kinNorm ha_s_pos hreal_s
    set G_b : ℝ := Real.exp (γ * (IIIa.clockTheta ν s₀ - b)) *
      (IIIa.clockTheta ν s₀ / b) ^ κre
    have hGb_nonneg : 0 ≤ G_b :=
      mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg (div_nonneg (IIIa.theta_pos hν hs₀_nonneg).le hbpos.le) _)
    have hCLF_le : C_LF * G_b ≤ max C_LF 0 * G_b :=
      mul_le_mul_of_nonneg_right (le_max_left C_LF 0) hGb_nonneg
    have hCKI_le : C_KI * (b / θ) ≤ max C_KI 0 * (b / θ) :=
      mul_le_mul_of_nonneg_right (le_max_left C_KI 0) (div_nonneg hbpos.le hθ_pos.le)
    have hcalc : ENNReal.ofReal (a_s * ‖kcLp x_s‖) ≤
        ENNReal.ofReal ((max C_KI 0 * (b / θ)) * (K₁ * ((max C_LF 0 * G_b) * (D₀ * ‖w_re‖)))) := by
      rw [ENNReal.ofReal_mul ha_s_pos.le]
      calc ENNReal.ofReal a_s * ENNReal.ofReal ‖kcLp x_s‖
          ≤ IIIa.kinNorm (IIIa.dOfTheta ν θ) Zh := hkin_s
        _ ≤ ENNReal.ofReal (C_KI * (b / θ)) * IIIa.kinNorm (IIIa.dOfTheta ν b) h_b := hKI1
        _ ≤ ENNReal.ofReal (max C_KI 0 * (b / θ)) *
              (ENNReal.ofReal K₁ *
                IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) a_b) m (IIIa.JscaleInv a_b (xFn x_b))) := by
            rw [hd_b_eq]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hCKI_le) hkin_b
        _ ≤ ENNReal.ofReal (max C_KI 0 * (b / θ)) *
              (ENNReal.ofReal K₁ *
                (ENNReal.ofReal (max C_LF 0 * G_b) *
                  (ENNReal.ofReal D₀ * ENNReal.ofReal ‖w_re‖))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ bot_le) bot_le
            refine (hLF1.trans (mul_le_mul_of_nonneg_right
              (ENNReal.ofReal_le_ofReal (by simpa [G_b, mul_assoc] using hCLF_le)) bot_le)).trans ?_
            exact mul_le_mul_of_nonneg_left hs2_scale bot_le
        _ = ENNReal.ofReal
              ((max C_KI 0 * (b / θ)) * (K₁ * ((max C_LF 0 * G_b) * (D₀ * ‖w_re‖)))) := by
            rw [← ENNReal.ofReal_mul hD₀_nonneg,
              ← ENNReal.ofReal_mul (mul_nonneg (le_max_right C_LF 0) hGb_nonneg),
              ← ENNReal.ofReal_mul hK₁,
              ← ENNReal.ofReal_mul (mul_nonneg (le_max_right C_KI 0) (div_nonneg hbpos.le hθ_pos.le))]
    have hreal : a_s * ‖kcLp x_s‖ ≤
        (max C_KI 0 * (b / θ)) * (K₁ * ((max C_LF 0 * G_b) * (D₀ * ‖w_re‖))) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcalc
    have hGb_eq : G_b = E_b *
        (‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ *
          ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν s₀ 0‖⁻¹) := by
      have hexp_split : Real.exp (γ * (IIIa.clockTheta ν s₀ - b)) =
          Real.exp (-γ * b) * Real.exp (γ * IIIa.clockTheta ν s₀) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hrpow_split : (IIIa.clockTheta ν s₀ / b) ^ κre =
          b ^ (-κre) * (IIIa.clockTheta ν s₀) ^ κre := by
        have hθ0_pos : 0 < IIIa.clockTheta ν s₀ := IIIa.theta_pos hν hs₀_nonneg
        rw [div_eq_mul_inv, Real.mul_rpow hθ0_pos.le (inv_nonneg.2 hbpos.le),
          Real.inv_rpow hbpos.le, Real.rpow_neg hbpos.le, mul_comm]
      unfold G_b E_b
      rw [hexp_split, hrpow_split,
        ← exp_theta0_mul_rpow_eq_nnu_div_fpm D.Pl.eigenvalue D.Pl.kappa hν]
      ring
    have hb_div_θ : b / θ = b * ν * a_s := by
      rw [← ha_s_eq]
      have hνne : ν ≠ 0 := hν.ne'
      have hθne : θ ≠ 0 := hθ_pos.ne'
      field_simp
    set NF : ℝ := ‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ *
      ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν s₀ 0‖⁻¹
    have hNF_nonneg : 0 ≤ NF := by positivity
    have hprod_le : ‖kcLp x_s‖ * a_s ≤ (Cu * ν * (NF * ‖w'‖)) * a_s := by
      calc ‖kcLp x_s‖ * a_s
          = a_s * ‖kcLp x_s‖ := mul_comm _ _
        _ ≤ (max C_KI 0 * (b / θ)) * (K₁ * ((max C_LF 0 * G_b) * (D₀ * ‖w_re‖))) := hreal
        _ = (Cu * ν * NF * ‖w_re‖) * a_s := by
            rw [hb_div_θ, hGb_eq]
            unfold Cu
            ring
        _ ≤ (Cu * ν * NF * ‖w'‖) * a_s := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (norm_reProj_le w') (by positivity)) ha_s_pos.le
        _ = (Cu * ν * (NF * ‖w'‖)) * a_s := by ring
    have hfinal := le_of_mul_le_mul_right hprod_le ha_s_pos
    rw [hkc_eq]
    simpa [NF, s₀, mul_assoc] using hfinal
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  exact key (cOf ν) hcOf (D.train n) (D.train_buc n) FI w

/-- **Direct assembly of `G3.LaterOutputAbsOp D`** from `PartI.TrainL2Decay`,
`IIIa.FullClockLongForward`, and `IIIa.CTKineticImpulse`. -/
theorem laterOutputAbsOp_of_longForward (D : SeqData)
    (hL2 : UnforcedLeray.Short.PartI.TrainL2Decay)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    G3.LaterOutputAbsOp D :=
  laterOutputAbsOp_of_parts D
    (trainVelTailBound_of_l2Decay D hL2)
    (unforcedFlowKcCoreBound_of_longForward D hLF)
    (unforcedFlowKcImpulseBound_of_longForward D hLF hKI)

/-- **Direct assembly of `G3.LaterOutputRem D`** from `PartI.TrainL2Decay`,
`IIIa.FullClockLongForward`, and `IIIa.CTKineticImpulse`. -/
theorem laterOutputRem_of_longForward (D : SeqData)
    (hL2 : UnforcedLeray.Short.PartI.TrainL2Decay)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    G3.LaterOutputRem D :=
  laterOutputRem_of_laterOutputAbsOp D (laterOutputAbsOp_of_longForward D hL2 hLF hKI)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

end
