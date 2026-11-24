import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntLeaf1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_3

/-!
# `PartIII-b:IIIb-D3/2/G1/5/2`: the tail (`s > H = 2/ν`) of the later output

Source of record: `the November 2 reference manuscript` (73 pages):
* lines 4432-4460 (`eq:young-later-output` 4454, propagation of a state at `H` to the long-clock
  age `b` by `eq:short-causal-long-forward` 4440-4448, Biot-Savart and moment embedding at `b`
  since `d(b) ≥ 1`, and the impulse estimates at `r = b` 4449-4455);
* lines 3272-3289 (`eq:ct-tested-impulse` and `eq:ct-absolute-impulse`).

What is proved here:
1. `duhIntegrand_integrableOn_of_bclass`: integrability of the Duhamel integrand on `(0, T]` for any
   `T > 0` and any matrix family `B` in `IsBclass a ν B`.
2. `xiD_tail_eq_of_bclass`: for `s ≥ H = 2/ν`, by the cocycle law (`YoungLaws.trans`) and the
   support `B(t) = 0` for `t ≥ 1.1/ν`, `ξ_B(s) = s^{-μ} 𝒰(s, 2/ν) D_H` where
   `D_H = duhamel pk μ (g_B B) (2/ν)`.
3. `measurable_integrand_levelFlat`: measurability in `s` of the `momentC` integrand for an actual
   flat setting `levelFlat`.
4. `integrand_tail_eq_unforcedTailDens`: for `s ≥ 2/ν`, using `χ_o(s) = 1` (`s ≥ 2/ν ≥ 1.5/ν`) and
   a.e. real homogeneity of `K_c` on the cell (`kcMerLinear`), the `momentC` integrand reduces to
   the unforced tail stress density `unforcedTailDens FI k μ D_H s` from the state `D_H` at `H = 2/ν`.
5. `tailBound_of`: derives `G1.LaterOutput.TailBound D` from `UnforcedTailImpulseBound D` (the
   missing Part III-a / Part III-b unforced propagation and impulse bound for `unforcedTailDens`
   from an arbitrary datum `w ∈ X_{m,c}` at `H = 2/ν`, source 4440-4458 and 3272-3289).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

open ConcreteYF FlatSettingInst

/-- Integrability of the Duhamel integrand on `(0, T]` for `B ∈ 𝓑_a` and `0 ≤ μ`. -/
theorem duhIntegrand_integrableOn_of_bclass {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {μ a T : ℝ} (hμ : 0 ≤ μ) (hT : 0 < T)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) :
    IntegrableOn (DuhIntegrand FI μ B T) (Ioc 0 T) := by
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    FI.src.H_cont.continuousOn
  obtain ⟨Cr, hCr⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    FI.src.R_cont.continuousOn
  set Csrc : ℝ := |Ch| + |Cr| with hCsrc_def
  obtain ⟨Cs, hCs⟩ := FI.ev.locBdd T
  have hCs0 : 0 ≤ Cs := (norm_nonneg (FI.ev.U 0 0)).trans (hCs 0 0 le_rfl le_rfl hT.le)
  have haeB : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)),
      matNorm (B t) ≤ bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (bclassAeBound a ν B hB)
  set K : ℝ := T ^ μ *
      (Cs * (3 * Csrc * (bNorm a B * (Real.exp (|a| * T) * T ^ (3 / 2 : ℝ))))) with hK_def
  have hbN0 : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hd : AEStronglyMeasurable (fun t : ℝ => Bd (B t)) (volume.restrict (Ioc 0 T)) :=
    (((hB.1 0 0).sub (hB.1 2 2)).div_const 2).aestronglyMeasurable
  have he : AEStronglyMeasurable (fun t : ℝ => Be (B t)) (volume.restrict (Ioc 0 T)) :=
    (((hB.1 0 2).add (hB.1 2 0)).div_const 2).aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun t : ℝ => Bbeta (B t)) (volume.restrict (Ioc 0 T)) :=
    (((hB.1 0 0).add (hB.1 2 2)).div_const 2).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (DuhIntegrand FI μ B T) (volume.restrict (Ioc 0 T)) :=
    duhIntegrand_aesm FI μ B T hd he hb
  have hintK : Integrable (fun _ : ℝ => K) (volume.restrict (Ioc (0 : ℝ) T)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  refine hintK.mono' hmeas ?_
  filter_upwards [haeB, ae_restrict_mem measurableSet_Ioc] with t htB ht
  unfold DuhIntegrand
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hg1 : ‖gBD FI B t‖ ≤ 3 * Csrc * matNorm (B t) := by
    refine G4.gBPointwise (actualFlatSetting FI (fun _ => 0) 0) T Csrc (fun r hr => ?_) B t htIcc
    have hHr : ‖FI.src.H r‖ ≤ Csrc :=
      (hCh r hr).trans ((le_abs_self _).trans (by linarith [abs_nonneg Cr]))
    have hRr : ‖FI.src.R r‖ ≤ Csrc :=
      (hCr r hr).trans ((le_abs_self _).trans (by linarith [abs_nonneg Ch]))
    change ‖FI.src.H r‖ ≤ Csrc ∧ ‖conjX (FI.src.H r)‖ ≤ Csrc ∧ ‖FI.src.R r‖ ≤ Csrc
    rw [norm_conjX]
    exact ⟨hHr, hHr, hRr⟩
  have hexp : Real.exp (a * t) ≤ Real.exp (|a| * T) := by
    apply Real.exp_le_exp.2
    calc a * t ≤ |a| * t := mul_le_mul_of_nonneg_right (le_abs_self a) ht.1.le
      _ ≤ |a| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg a)
  have ht32 : t ^ (3 / 2 : ℝ) ≤ T ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow ht.1.le ht.2 (by norm_num)
  have htμ : t ^ μ ≤ T ^ μ :=
    Real.rpow_le_rpow ht.1.le ht.2 hμ
  have hB_le : matNorm (B t) ≤ bNorm a B * (Real.exp (|a| * T) * T ^ (3 / 2 : ℝ)) :=
    htB.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hexp ht32 (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le) hbN0)
  have hg2 : ‖gBD FI B t‖ ≤ 3 * Csrc * (bNorm a B * (Real.exp (|a| * T) * T ^ (3 / 2 : ℝ))) :=
    hg1.trans (mul_le_mul_of_nonneg_left hB_le (by positivity))
  have hU : ‖FI.ev.U T t (gBD FI B t)‖ ≤
      Cs * (3 * Csrc * (bNorm a B * (Real.exp (|a| * T) * T ^ (3 / 2 : ℝ)))) :=
    ((FI.ev.U T t).le_opNorm _).trans
      (mul_le_mul (hCs T t ht.1.le ht.2 le_rfl) hg2 (norm_nonneg _) hCs0)
  exact mul_le_mul htμ hU (norm_nonneg _) (by positivity)

/-- **Tail cocycle formula for `ξ_B` (source 4440-4445, 4610)**: for `s ≥ H = 2/ν`,
`ξ_B(s) = s^{-μ} 𝒰(s, 2/ν) (duhamel pk μ (g_B B) (2/ν))`. -/
theorem xiD_tail_eq_of_bclass {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {μ a s : ℝ} (hμ : 0 ≤ μ)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) (hs : 2 / ν ≤ s) :
    haveI : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
    xiD FI (μ : ℂ) B s =
      ((s ^ (-μ) : ℝ) : ℂ) •
        FI.ev.U s (2 / ν) (duhamel (actualPk FI) (μ : ℂ) (gBD FI B) (2 / ν)) := by
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  set H : ℝ := 2 / ν with hH_def
  have hHpos : 0 < H := div_pos two_pos hν
  have hspos : 0 < s := hHpos.trans_le hs
  have hBz : ∀ t, H < t → B t = 0 := by
    intro t ht
    apply hB.2.2.2.1 t
    intro htIoo
    have h11 : 1.1 / ν ≤ 2 / ν := div_le_div_of_nonneg_right (by norm_num) hν.le
    linarith [htIoo.2, ht]
  have hInt : IntegrableOn (DuhIntegrand FI μ B H) (Ioc 0 H) :=
    duhIntegrand_integrableOn_of_bclass FI hμ hHpos hB
  have hlate := xiDLate m κ ν μ hν tr FI B H s hHpos hs hBz hInt
  have hpowH : (H : ℂ) ^ (μ : ℂ) * (H : ℂ) ^ (-(μ : ℂ)) = 1 := by
    have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hHpos.ne'
    rw [Complex.cpow_neg, mul_inv_cancel₀ (Complex.cpow_ne_zero_iff.2 (Or.inl hH0))]
  have hduhH : ((H : ℂ) ^ (μ : ℂ)) • xiD FI (μ : ℂ) B H =
      duhamel (actualPk FI) (μ : ℂ) (gBD FI B) H := by
    rw [xiD_apply, smul_smul, hpowH, one_smul]
    rfl
  have hs_cpow : (s : ℂ) ^ (-(μ : ℂ)) = ((s ^ (-μ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, Complex.ofReal_cpow hspos.le]
  rw [hlate, mul_smul, ← map_smul, hduhH, hs_cpow]

/-- Measurability of `matNorm` on `Mat3`. -/
private theorem measurable_matNorm : Measurable (matNorm : Mat3 → ℝ) := by
  unfold matNorm
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact continuous_abs.measurable.comp (( measurable_pi_apply j).comp (measurable_pi_apply i))

/-- Measurability in `s` of the `momentC` integrand for an actual flat setting `levelFlat`. -/
theorem measurable_integrand_levelFlat {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (hν : 0 < ν)
    (FI : FlatInstData κ ν (cOf ν) m tr) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ)
    (k : ℕ) {μ a : ℝ} (hμ : 0 ≤ μ) {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) :
    Measurable fun s : ℝ =>
      (levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
        cellInt (levelFlat hν FI χo ε).c (fun p =>
          matNorm ((levelFlat hν FI χo ε).Mcell s ((levelFlat hν FI χo ε).xi (μ : ℂ) B s) p)) := by
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  have hξc : ContinuousOn (xiD FI (μ : ℂ) B) (Ioi 0) := G4.xiD_contOn_of_bclass FI hμ hB
  have hξ0 : ∀ s : ℝ, s ≤ 0 → xiD FI (μ : ℂ) B s = 0 := fun s hs => xiD_nonpos FI (μ : ℂ) B hs
  have hK := kcJointMeasurable (cOf ν) m (xiD FI (μ : ℂ) B) hξc hξ0
  have hKi : ∀ i : Fin 2, Measurable fun p : Chart => kcMer (xiD FI (μ : ℂ) B p.1) p.2 i :=
    fun i => Complex.measurable_re.comp (hK i)
  have hT : Measurable (NearInst.trainMer tr) := NearInst.trainMerMeasurable ν (cOf ν) tr
  have hP : ∀ i : Fin 2, Measurable fun v : Merid => v i := fun i =>
    (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).continuous.measurable
  have hemb : ∀ j : Fin 3, Measurable fun v : Merid => IIIa.embedMerid v j := by
    intro j; fin_cases j
    · exact hP 0
    · exact measurable_const
    · exact hP 1
  have hTe : ∀ j : Fin 3, Measurable fun p : Chart => IIIa.embedMerid (NearInst.trainMer tr p) j :=
    fun j => (hemb j).comp hT
  have hKe : ∀ j : Fin 3, Measurable fun p : Chart =>
      IIIa.embedMerid (kcMer (xiD FI (μ : ℂ) B p.1) p.2) j := by
    intro j; fin_cases j
    · exact hKi 0
    · exact measurable_const
    · exact hKi 1
  have hSym : ∀ i j : Fin 3, Measurable fun p : Chart =>
      IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiD FI (μ : ℂ) B p.1) p.2) i j :=
    fun i j => ((hTe i).mul (hKe j)).add ((hKe i).mul (hTe j))
  have hF : Measurable fun p : Chart =>
      matNorm (IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiD FI (μ : ℂ) B p.1) p.2)) := by
    unfold matNorm
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp (hSym i j)
  have hInt : Measurable fun s : ℝ =>
      ∫ x in (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ),
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiD FI (μ : ℂ) B s) x)) :=
    (hF.stronglyMeasurable.integral_prod_right').measurable
  have hCell : Measurable fun s : ℝ =>
      cellInt (cOf ν) (fun x =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiD FI (μ : ℂ) B s) x))) :=
    measurable_const.mul hInt
  have hChi : Measurable fun s : ℝ => χo (ν * s) :=
    (hχo.smooth.continuous.comp (continuous_const.mul continuous_id)).measurable
  have hPow : Measurable fun s : ℝ => s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) :=
    measurable_id.pow_const _
  exact (hChi.mul hPow).mul hCell

/-- Unforced tail stress density at age `s` from a datum `w ∈ X_{m,c}` at `H = 2/ν`:
`s^{-3/2 - k/2} · s^{-μ} · (1/c) ∫_cell |v(s) ⊗ K_c(𝒰(s, 2/ν)w) + K_c(𝒰(s, 2/ν)w) ⊗ v(s)|`. -/
def unforcedTailDens {κ : IIIa.PlanarFrameKernels} {ν m : ℝ} [Fact (1 < m)] [Fact (0 < cOf ν)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (FI : FlatInstData κ ν (cOf ν) m tr)
    (k : ℕ) (μ : ℝ) (w : Xmc (cOf ν) m) (s : ℝ) : ℝ :=
  s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
    (s ^ (-μ) * cellInt (cOf ν) (fun p =>
      matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer (FI.ev.U s (2 / ν) w) p))))

private theorem matNorm_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    matNorm (r • M) = r * matNorm M := by
  unfold matNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change |r * M i j| = r * |M i j|
  rw [abs_mul, abs_of_nonneg hr]

/-- On the tail `s ≥ 2/ν`, the `momentC` integrand of `levelFlat` equals `unforcedTailDens` from
`D_H = duhamel (actualPk FI) μ (gBD FI B) (2/ν)`. -/
theorem integrand_tail_eq_unforcedTailDens {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ)
    (k : ℕ) {μ a s : ℝ} (hμ : 0 ≤ μ) {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B)
    (hs : 2 / ν ≤ s) :
    haveI : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
    (levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
        cellInt (levelFlat hν FI χo ε).c (fun p =>
          matNorm ((levelFlat hν FI χo ε).Mcell s ((levelFlat hν FI χo ε).xi (μ : ℂ) B s) p)) =
      unforcedTailDens FI k μ (duhamel (actualPk FI) (μ : ℂ) (gBD FI B) (2 / ν)) s := by
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  have hχ1 : (levelFlat hν FI χo ε).chiO s = 1 := by
    change χo (ν * s) = 1
    apply hχo.one
    have h2 : (2 : ℝ) ≤ ν * s := by
      calc (2 : ℝ) = ν * (2 / ν) := (mul_div_cancel₀ 2 hν.ne').symm
        _ ≤ ν * s := mul_le_mul_of_nonneg_left hs hν.le
    linarith
  have hxi := xiD_tail_eq_of_bclass hν FI hμ hB hs
  set w := FI.ev.U s (2 / ν) (duhamel (actualPk FI) (μ : ℂ) (gBD FI B) (2 / ν)) with hw_def
  set r : ℝ := s ^ (-μ) with hr_def
  have hspos : 0 < s := (div_pos two_pos hν).trans_le hs
  have hr0 : 0 ≤ r := Real.rpow_nonneg hspos.le _
  have hK_avg : kcMer ((r : ℂ) • w) =ᵐ[Cyl.avgμ (cOf ν)] r • kcMer w :=
    (kcMerLinear m ν hν w w r).2
  have hcpos : 0 < cOf ν := cOf_pos hν
  have hne : ENNReal.ofReal (cOf ν)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hcpos)).ne'
  have hcell_eq : Cyl.cell (cOf ν) = B0579.cell (cOf ν) := by
    simp only [Cyl.cell, B0579.cell, neg_div]
  have hK_cell : kcMer ((r : ℂ) • w) =ᵐ[volume.restrict (B0579.cell (cOf ν))] r • kcMer w := by
    unfold Cyl.avgμ Cyl.cellμ Filter.EventuallyEq at hK_avg
    rw [hcell_eq, Measure.ae_ennreal_smul_measure_eq hne] at hK_avg
    exact hK_avg
  have hsub : (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ) ⊆ B0579.cell (cOf ν) := by
    rintro ⟨q, η⟩ ⟨hq, _⟩
    exact ⟨⟨by linarith [hq.1], hq.2⟩, trivial⟩
  have hK_open : kcMer ((r : ℂ) • w) =ᵐ[volume.restrict ((Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ))]
      r • kcMer w :=
    ae_restrict_of_ae_restrict_of_subset hsub hK_cell
  have hCell_eq : cellInt (cOf ν) (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer (xiD FI (μ : ℂ) B s) p))) =
      r * cellInt (cOf ν) (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer w p))) := by
    unfold cellInt
    rw [hxi]
    have hint_eq : (∫ p in (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ),
          matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ((r : ℂ) • w) p))) =
        ∫ p in (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ),
          r * matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer w p)) := by
      refine integral_congr_ae ?_
      filter_upwards [hK_open] with p hp
      have hp' : kcMer ((r : ℂ) • w) p = r • kcMer w p := hp
      rw [hp', symOuter_smul_right', matNorm_smul_nonneg hr0]
    rw [hint_eq, integral_const_mul]
    ring
  change (levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
      cellInt (cOf ν) (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer (xiD FI (μ : ℂ) B s) p))) =
    unforcedTailDens FI k μ (duhamel (actualPk FI) (μ : ℂ) (gBD FI B) (2 / ν)) s
  rw [hχ1, one_mul, hCell_eq]
  rfl

private theorem unforcedTailDens_nonneg {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (k : ℕ) (μ : ℝ) (w : Xmc (cOf ν) m)
    {s : ℝ} (hs : 0 < s) :
    0 ≤ unforcedTailDens FI k μ w s := by
  have hc : 0 < cOf ν := Fact.out
  unfold unforcedTailDens cellInt
  refine mul_nonneg (Real.rpow_nonneg hs.le _) (mul_nonneg (Real.rpow_nonneg hs.le _) ?_)
  refine mul_nonneg (inv_nonneg.2 hc.le) (setIntegral_nonneg
    (measurableSet_Ioo.prod MeasurableSet.univ) fun p _ => ?_)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **Unforced tail propagation and absolute-stress impulse bound** (source 4440-4458 and 3272-3289:
propagate a state `w ∈ X_{m,c}` at `H = 2/ν` to the long-clock age `b` via `FullClockLongForward`
with exponential decay above `b`, then apply the uniform Biot-Savart embedding at `b` since
`d(b) ≥ 1` and `eq:ct-absolute-impulse` at `r = b` on `0 < θ ≤ b`): for every datum `w ∈ X_{m,c}`
at `H = 2/ν`, the tail Lebesgue integral of `unforcedTailDens FI k μ w` on `s > 2/ν` is bounded
by `C (|N_ν| ν^{3+2μ} / c) ν^k |F_+(2/ν, 0)|⁻¹ ‖w‖`. -/
def UnforcedTailImpulseBound (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ κ : IIIa.PlanarFrameKernels, SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n ≥ N,
      ∀ (FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n)),
      haveI : Fact (0 < cOf (nu D n)) := ⟨cOf_pos (retNu_pos D.Pl D.σ₀ n)⟩
      ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1, ∀ w : Xmc (cOf (nu D n)) m,
        ∫⁻ s in Ioi (2 / nu D n), ENNReal.ofReal (unforcedTailDens FI k (D.mu n z) w s) ≤
          ENNReal.ofReal (C * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
            nu D n ^ (3 + 2 * D.mu n z) / cOf (nu D n)) * nu D n ^ k *
              (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖)))

/-- **Reduction of `TailBound` to `UnforcedTailImpulseBound`** (source 4440-4458): uses
`measurable_integrand_levelFlat`, the cocycle identity `xiD_tail_eq_of_bclass`, the cutoff identity
`χ_o(s) = 1` on `s ≥ 2/ν`, and the cell homogeneity `integrand_tail_eq_unforcedTailDens`. -/
theorem tailBound_of (D : SeqData) (hImp : UnforcedTailImpulseBound D) :
    G1.LaterOutput.TailBound D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨C, N1, hC0, hC⟩ := hImp dm dp hst κ hκ m hm
  have hmu_ev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hS.and hmu_ev)
  refine ⟨C, max N1 N2, fun n hn k hk z hz B hB => ?_⟩
  obtain ⟨⟨FI, hSn⟩, hmu_z⟩ := hN2 n (le_trans (le_max_right _ _) hn)
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have : Fact (0 < cOf (nu D n)) := ⟨cOf_pos hν⟩
  have hμ0 : 0 ≤ D.mu n z := by
    have := (hmu_z z hz).1
    linarith [hst.sigma_pos]
  set w : Xmc (cOf (nu D n)) m :=
    duhamel (actualPk FI) (D.mu n z : ℂ) (gBD FI B) (2 / nu D n) with hw_def
  have hbd_u := hC n (le_trans (le_max_left _ _) hn) FI k hk z hz w
  have heq_on : EqOn (integrand D S n k z B) (unforcedTailDens FI k (D.mu n z) w)
      (Ioi (2 / nu D n)) := by
    intro s hs
    have hs_le : 2 / nu D n ≤ s := (mem_Ioi.1 hs).le
    unfold integrand
    rw [hSn]
    exact integrand_tail_eq_unforcedTailDens hν FI D.K.hχo (retEps D.Pl D.σ₀ n) k hμ0 hB hs_le
  have hnn_on : ∀ s ∈ Ioi (2 / nu D n), 0 ≤ integrand D S n k z B s := by
    intro s hs
    rw [heq_on hs]
    exact unforcedTailDens_nonneg FI k (D.mu n z) w ((div_pos two_pos hν).trans hs)
  have hmeas : Measurable (integrand D S n k z B) := by
    unfold integrand
    rw [hSn]
    exact measurable_integrand_levelFlat hν FI D.K.hχo (retEps D.Pl D.σ₀ n) k hμ0 hB
  have hlint_eq : (∫⁻ s in Ioi (2 / nu D n), ‖integrand D S n k z B s‖ₑ) =
      ∫⁻ s in Ioi (2 / nu D n), ENNReal.ofReal (unforcedTailDens FI k (D.mu n z) w s) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [Real.enorm_eq_ofReal (hnn_on s hs), heq_on hs]
  have hint : IntegrableOn (integrand D S n k z B) (Ioi (2 / nu D n)) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    show (∫⁻ s in Ioi (2 / nu D n), ‖integrand D S n k z B s‖ₑ) < ⊤
    rw [hlint_eq]
    exact lt_of_le_of_lt hbd_u ENNReal.ofReal_lt_top
  have hrhs0 : 0 ≤ rhs D S n k z B := by
    unfold rhs
    rw [hSn]
    have hc : 0 < (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).c := cOf_pos hν
    positivity
  have hrhs_eq : C * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
        cOf (nu D n)) * nu D n ^ k *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖)) =
      C * rhs D S n k z B := by
    unfold rhs
    rw [hSn]
    rfl
  refine ⟨hint, ?_⟩
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Ioi (2 / nu D n))] integrand D S n k z B :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn_on)
  rw [integral_eq_lintegral_of_nonneg_ae hnn_ae hmeas.aestronglyMeasurable]
  have hlint_eq' : (∫⁻ s in Ioi (2 / nu D n), ENNReal.ofReal (integrand D S n k z B s)) =
      ∫⁻ s in Ioi (2 / nu D n), ENNReal.ofReal (unforcedTailDens FI k (D.mu n z) w s) :=
    setLIntegral_congr_fun measurableSet_Ioi fun s hs => by rw [heq_on hs]
  rw [hlint_eq']
  rw [hrhs_eq] at hbd_u
  exact (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0 hrhs0) hbd_u)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput
