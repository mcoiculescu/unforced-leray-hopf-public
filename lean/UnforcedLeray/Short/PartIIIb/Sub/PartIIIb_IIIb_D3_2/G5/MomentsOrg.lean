import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6Org
import UnforcedLeray.Short.PartIIIb.Concrete.FlatMoments
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Kflat

/-!
# `PartIII-b:IIIb-D3/2/G5/3/org`: old moments of `𝔗A` at the levels (`FrakTMoments`)

Source of record: `the November 2 reference manuscript` (73 pages):
* lines 4848-4854 (uniform source theorem gives `N_j^χ(𝔗A) ≤ C_j 𝒜_ν ν^j ‖A‖_𝒜`, `j = 0, 1`),
* lines 4637-4640 (`flat-return:all-moments`, proof 4686-4693),
* lines 4757-4760 (`B_{μ,ν}[A] ∈ 𝓑_{a_s}`, `‖B_{μ,ν}[A]‖_{a_s} ≤ C_K ‖A‖_𝒜`),
* lines 4917-4927 (`OldThinFinite`).

`frakTMoments_of` proves `FlatUnif.G5.FrakTMoments D` from:
* `GroupYoung D` (task `PartIII-b:IIIb-D3/2/G1`, `flatGroupYoung D`),
* `GroupTested D` (task `PartIII-b:IIIb-D3/2/G4`, `flatGroupTested D`),
* `FlatNearUnit D` (task `PartIII-b:IIIb-D3/2/G5/1`, `flatNearUnit D`),
* `G6.BmatBclass` (task `PartIII-b:IIIb-D3/2/G6/3`, `G6.bmatBclass`),
* `G6.ActualSeqPinned D` (task `PartIII-b:IIIb-D3/2/G6/5`, `G6.actualSeqPinned D`),
* `FrakTOldFinite` (task `PartIII-b:C/asrc/kflat/1`, `frakTOldFinite`).

Composed in task `PartIII-b:IIIb-D3/2/G5/3` (`Sub/PartIII-b_IIIb-D3_2/G5/Moments.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

open ConcreteYF

private instance sfinite_avgμ (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ Cyl.cellμ
  infer_instance

/-! ## 1. Transfer along a.e. equality on `oldMeasure` -/

private lemma oldThinFinite_congr {c ν : ℝ} {M M' : Chart → Mat3}
    (h : M =ᵐ[oldMeasure c ν] M') (hM : OldThinFinite c ν M) :
    OldThinFinite c ν M' := by
  refine ⟨hM.1.congr h, hM.2.congr ?_⟩
  filter_upwards [h] with p hp
  rw [hp]

private lemma oldN0w_congr {c ν : ℝ} (χo : ℝ → ℝ) {M M' : Chart → Mat3}
    (h : M =ᵐ[oldMeasure c ν] M') :
    oldN0w c ν χo M = oldN0w c ν χo M' := by
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (6 / 5 / ν))),
      ∀ᵐ x ∂(Cyl.avgμ c), M (u, x) = M' (u, x) := by
    unfold oldMeasure at h
    exact Measure.ae_ae_of_ae_prod h
  unfold oldN0w
  refine integral_congr_ae (hae.mono fun u hu => ?_)
  dsimp only
  congr 2
  exact integral_congr_ae (hu.mono fun x hx => by dsimp only; rw [hx])

private lemma oldN1w_congr {c ν : ℝ} (χo : ℝ → ℝ) {M M' : Chart → Mat3}
    (h : M =ᵐ[oldMeasure c ν] M') :
    oldN1w c ν χo M = oldN1w c ν χo M' := by
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (6 / 5 / ν))),
      ∀ᵐ x ∂(Cyl.avgμ c), M (u, x) = M' (u, x) := by
    unfold oldMeasure at h
    exact Measure.ae_ae_of_ae_prod h
  unfold oldN1w
  refine integral_congr_ae (hae.mono fun u hu => ?_)
  dsimp only
  congr 2
  exact integral_congr_ae (hu.mono fun x hx => by dsimp only; rw [hx])

/-! ## 2. Matrix norms and cell integrals -/

private lemma frob_nonneg_local (A : Mat3) : 0 ≤ frob A := by
  unfold frob
  exact Real.sqrt_nonneg _

private lemma matNorm_nonneg_local (A : Mat3) : 0 ≤ matNorm A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma abs_entry_le_matNorm (A : Mat3) (i j : Fin 3) :
    |A i j| ≤ matNorm A := by
  unfold matNorm
  calc |A i j| ≤ ∑ j', |A i j'| :=
        Finset.single_le_sum (f := fun j' => |A i j'|) (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |A i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |A i' j'|)
          (fun i' _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)

private lemma frob_le_matNorm (A : Mat3) : frob A ≤ matNorm A := by
  unfold frob
  rw [← Real.sqrt_sq (matNorm_nonneg_local A)]
  apply Real.sqrt_le_sqrt
  have h1 : ∀ i j : Fin 3, A i j ^ 2 ≤ |A i j| * matNorm A := fun i j => by
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_left (abs_entry_le_matNorm A i j) (abs_nonneg _)
  calc ∑ i, ∑ j, A i j ^ 2
      ≤ ∑ i, ∑ j, (|A i j| * matNorm A) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = matNorm A ^ 2 := by
        simp only [← Finset.sum_mul, sq]
        rfl

private lemma abs_entry_le_frob_local (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
          (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)

private lemma matNorm_le_nine_frob (A : Mat3) : matNorm A ≤ 9 * frob A := by
  unfold matNorm
  calc ∑ i : Fin 3, ∑ j : Fin 3, |A i j|
      ≤ ∑ _ : Fin 3, ∑ _ : Fin 3, frob A :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => abs_entry_le_frob_local A i j
    _ = 9 * frob A := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring

private lemma integral_avgμ_eq_cellInt {c : ℝ} (hc : 0 ≤ c) (F : ℝ × ℝ → ℝ) :
    ∫ p, F p ∂(Cyl.avgμ c) = cellInt c F := by
  rw [Cyl.integral_avgμ hc F, cellInt, smul_eq_mul]
  congr 1
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Ioo (-c / 2) (c / 2) ×ˢ univ) =
      (volume : Measure (ℝ × ℝ)).restrict (Cyl.cell c) := by
    rw [Cyl.cell, Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
      Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ico]
  rw [hmeas]

private lemma integral_le_of_ae_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hg : Integrable g μ) (h0 : ∀ᵐ u ∂μ, 0 ≤ g u) (hle : ∀ᵐ u ∂μ, f u ≤ g u) :
    ∫ u, f u ∂μ ≤ ∫ u, g u ∂μ := by
  by_cases hf : Integrable f μ
  · exact integral_mono_ae hf hg hle
  · rw [integral_undef hf]
    exact integral_nonneg_of_ae h0

/-! ## 3. Bounding `oldN0w` and `oldN1w` by `momentC` at `levelFlat` -/

private lemma momentC_levelFlat_eq {ν m : ℝ} [Fact (1 < m)]
    {κk : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (hν : 0 < ν) (FI : FlatSettingInst.FlatInstData κk ν (cOf ν) m tr)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ) (lam κ : ℂ) (μ : ℝ) (k : ℕ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    (levelFlat hν FI χo ε).momentC lam κ μ k (Bmat ν μ χf A) =
      ∫ u in Ioi (6 / 5 / ν), χo (ν * u) * u ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
        ∫ x, matNorm (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x)) ∂(Cyl.avgμ (cOf ν)) := by
  set S := levelFlat hν FI χo ε
  set M := frakT S ν μ χf A
  have hc : S.c = cOf ν := rfl
  have hchi : ∀ u, S.chiO u = χo (ν * u) := fun _ => rfl
  have hM : ∀ u x, S.Mcell u (S.xi (μ : ℂ) (Bmat ν μ χf A) u) x = M (u, x) := fun _ _ => rfl
  unfold FlatSetting.momentC
  set g : ℝ → ℝ := fun u => χo (ν * u) * u ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
    ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ (cOf ν))
  have hrew : ∀ u : ℝ, S.chiO u * u ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
      cellInt S.c (fun p => matNorm (S.Mcell u (S.xi (μ : ℂ) (Bmat ν μ χf A) u) p)) =
      (Ioi (6 / 5 / ν)).indicator g u := by
    intro u
    rw [hchi u, hc, ← integral_avgμ_eq_cellInt (cOf_pos hν).le]
    by_cases hu : u ∈ Ioi (6 / 5 / ν)
    · rw [indicator_of_mem hu]
      rfl
    · rw [indicator_of_notMem hu]
      have hu' : u ≤ 6 / 5 / ν := not_lt.1 hu
      have hνu : ν * u ≤ 6 / 5 := by
        have := (le_div_iff₀ hν).1 hu'
        linarith
      simp [hχo.zero (ν * u) hνu]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hrew u),
    setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
    sup_eq_right.2 (div_pos (by norm_num) hν).le]

private lemma integrable_matNorm_oldMeasure {c ν : ℝ} {M : Chart → Mat3}
    (hM : OldThinFinite c ν M) :
    Integrable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * matNorm (M p)) (oldMeasure c ν) := by
  have hcont : Continuous matNorm := by unfold matNorm; fun_prop
  have haesm : AEStronglyMeasurable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * matNorm (M p))
      (oldMeasure c ν) :=
    (measurable_fst.aemeasurable.pow_const _).aestronglyMeasurable.mul
      (hcont.comp_aestronglyMeasurable hM.1)
  refine (hM.2.norm.const_mul 9).mono' haesm (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (matNorm_nonneg_local _), abs_of_nonneg (frob_nonneg_local _)]
  nlinarith [matNorm_le_nine_frob (M p), abs_nonneg (p.1 ^ (-(3 / 2 : ℝ)))]

private lemma slice_frob_le_matNorm_ae {c ν : ℝ} (hν : 0 < ν) {M : Chart → Mat3}
    (hM : OldThinFinite c ν M) :
    ∀ᵐ u ∂(volume.restrict (Ioi (6 / 5 / ν))),
      ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) ≤ ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c) := by
  have h1 := (integrable_matNorm_oldMeasure hM).prod_right_ae
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioi] with u hu1 hu
  have hpos : 0 < u := lt_trans (div_pos (by norm_num) hν) hu
  have hInt : Integrable (fun x => matNorm (M (u, x))) (Cyl.avgμ c) := by
    refine (hu1.const_mul (u ^ (3 / 2 : ℝ))).congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← mul_assoc, ← Real.rpow_add hpos]
    norm_num
  exact integral_le_of_ae_le_of_nonneg hInt
    (Eventually.of_forall fun x => matNorm_nonneg_local _)
    (Eventually.of_forall fun x => frob_le_matNorm _)

private lemma integrable_moment_rhs {c ν : ℝ} (hν : 0 < ν) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) {M : Chart → Mat3} (hM : OldThinFinite c ν M) (k : ℕ) :
    Integrable (fun u => χo (ν * u) * u ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
      ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c)) (volume.restrict (Ioi (6 / 5 / ν))) := by
  have hMat := integrable_matNorm_oldMeasure hM
  have hG0 : Integrable (fun u => u ^ (-(3 / 2 : ℝ)) * ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c))
      (volume.restrict (Ioi (6 / 5 / ν))) := by
    refine hMat.integral_prod_left.congr (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [integral_const_mul]
  have hcont : Continuous matNorm := by unfold matNorm; fun_prop
  have hIm : AEStronglyMeasurable (fun u => ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c))
      (volume.restrict (Ioi (6 / 5 / ν))) :=
    (hcont.comp_aestronglyMeasurable hM.1).integral_prod_right'
  have hχm : Continuous (fun u => χo (ν * u)) :=
    hχo.smooth.continuous.comp (continuous_const.mul continuous_id)
  have haesm : AEStronglyMeasurable
      (fun u => χo (ν * u) * u ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
        ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c))
      (volume.restrict (Ioi (6 / 5 / ν))) :=
    (hχm.aestronglyMeasurable.mul
      (measurable_id.aemeasurable.pow_const _).aestronglyMeasurable).mul hIm
  set a : ℝ := 6 / 5 / ν
  have ha : 0 < a := div_pos (by norm_num) hν
  refine (hG0.norm.const_mul (a ^ (-(k : ℝ) / 2))).mono' haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := ha.trans hu
  have hχ0 : 0 ≤ χo (ν * u) := (hχo.range (ν * u)).1
  have hχ1 : χo (ν * u) ≤ 1 := (hχo.range (ν * u)).2
  have hI0 : 0 ≤ ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c) :=
    integral_nonneg fun x => matNorm_nonneg_local _
  have hr0 : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
  have hrk0 : 0 ≤ u ^ (-(k : ℝ) / 2) := Real.rpow_nonneg hu0.le _
  have hr_eq : u ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) = u ^ (-(k : ℝ) / 2) * u ^ (-(3 / 2 : ℝ)) := by
    have : -(3 / 2 : ℝ) - (k : ℝ) / 2 = -(k : ℝ) / 2 + -(3 / 2 : ℝ) := by ring
    rw [this, Real.rpow_add hu0]
  have hrk_le : u ^ (-(k : ℝ) / 2) ≤ a ^ (-(k : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos ha hu.le
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (Nat.cast_nonneg k)) (by norm_num))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hr_eq,
    abs_of_nonneg (mul_nonneg (mul_nonneg hχ0 (mul_nonneg hrk0 hr0)) hI0),
    abs_of_nonneg (mul_nonneg hr0 hI0)]
  calc χo (ν * u) * (u ^ (-(k : ℝ) / 2) * u ^ (-(3 / 2 : ℝ))) *
        ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c)
      ≤ 1 * (a ^ (-(k : ℝ) / 2) * u ^ (-(3 / 2 : ℝ))) *
          ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c) := by
        apply mul_le_mul_of_nonneg_right _ hI0
        exact mul_le_mul hχ1 (mul_le_mul_of_nonneg_right hrk_le hr0) (mul_nonneg hrk0 hr0) zero_le_one
    _ = a ^ (-(k : ℝ) / 2) * (u ^ (-(3 / 2 : ℝ)) * ∫ x, matNorm (M (u, x)) ∂(Cyl.avgμ c)) := by
        ring

private lemma oldN0w_le_momentC {ν m : ℝ} [Fact (1 < m)]
    {κk : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (hν : 0 < ν) (FI : FlatSettingInst.FlatInstData κk ν (cOf ν) m tr)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ) (lam κ : ℂ) (μ : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hM : OldThinFinite (cOf ν) ν (frakT (levelFlat hν FI χo ε) ν μ χf A)) :
    oldN0w (cOf ν) ν χo (frakT (levelFlat hν FI χo ε) ν μ χf A) ≤
      (levelFlat hν FI χo ε).momentC lam κ μ 0 (Bmat ν μ χf A) := by
  rw [momentC_levelFlat_eq hν FI hχo ε lam κ μ 0 χf A]
  unfold oldN0w
  refine integral_le_of_ae_le_of_nonneg (integrable_moment_rhs hν hχo hM 0) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans (div_pos (by norm_num) hν) hu
    exact mul_nonneg (mul_nonneg (hχo.range (ν * u)).1 (Real.rpow_nonneg hu0.le _))
      (integral_nonneg fun x => matNorm_nonneg_local _)
  · filter_upwards [slice_frob_le_matNorm_ae hν hM, ae_restrict_mem measurableSet_Ioi] with u hsl hu
    have hu0 : 0 < u := lt_trans (div_pos (by norm_num) hν) hu
    have hχ0 : 0 ≤ χo (ν * u) := (hχo.range (ν * u)).1
    have hr0 : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
    have hexp : -(3 / 2 : ℝ) - ((0 : ℕ) : ℝ) / 2 = -(3 / 2 : ℝ) := by norm_num
    rw [hexp]
    calc u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) *
          ∫ x, frob (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x)) ∂(Cyl.avgμ (cOf ν)))
        ≤ u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) *
            ∫ x, matNorm (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x)) ∂(Cyl.avgμ (cOf ν))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsl hχ0) hr0
      _ = χo (ν * u) * u ^ (-(3 / 2 : ℝ)) *
            ∫ x, matNorm (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x)) ∂(Cyl.avgμ (cOf ν)) := by
          ring

private lemma oldN1w_le_momentC {ν m : ℝ} [Fact (1 < m)]
    {κk : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (hν : 0 < ν) (FI : FlatSettingInst.FlatInstData κk ν (cOf ν) m tr)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ) (lam κ : ℂ) (μ : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hM : OldThinFinite (cOf ν) ν (frakT (levelFlat hν FI χo ε) ν μ χf A)) :
    oldN1w (cOf ν) ν χo (frakT (levelFlat hν FI χo ε) ν μ χf A) ≤
      (levelFlat hν FI χo ε).momentC lam κ μ 1 (Bmat ν μ χf A) := by
  rw [momentC_levelFlat_eq hν FI hχo ε lam κ μ 1 χf A]
  unfold oldN1w
  refine integral_le_of_ae_le_of_nonneg (integrable_moment_rhs hν hχo hM 1) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans (div_pos (by norm_num) hν) hu
    exact mul_nonneg (mul_nonneg (hχo.range (ν * u)).1 (Real.rpow_nonneg hu0.le _))
      (integral_nonneg fun x => matNorm_nonneg_local _)
  · filter_upwards [slice_frob_le_matNorm_ae hν hM, ae_restrict_mem measurableSet_Ioi] with u hsl hu
    have hu0 : 0 < u := lt_trans (div_pos (by norm_num) hν) hu
    have hχ0 : 0 ≤ χo (ν * u) := (hχo.range (ν * u)).1
    have hr0 : 0 ≤ u ^ (-(2 : ℝ)) := Real.rpow_nonneg hu0.le _
    have hexp : -(3 / 2 : ℝ) - ((1 : ℕ) : ℝ) / 2 = -(2 : ℝ) := by norm_num
    rw [hexp]
    calc u ^ (-(2 : ℝ)) * (χo (ν * u) *
          ∫ x, frob (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x)) ∂(Cyl.avgμ (cOf ν)))
        ≤ u ^ (-(2 : ℝ)) * (χo (ν * u) *
            ∫ x, matNorm (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x)) ∂(Cyl.avgμ (cOf ν))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsl hχ0) hr0
      _ = χo (ν * u) * u ^ (-(2 : ℝ)) *
            ∫ x, matNorm (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x)) ∂(Cyl.avgμ (cOf ν)) := by
          ring

/-! ## 4. Window-uniform `momentC` bound and assembly of `FrakTMoments` -/

private lemma momentC_bound_step {S : FlatSetting} {lam κ : ℂ} {ν μ as CS CT CL : ℝ} {k : ℕ}
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hν : 0 < ν) (hc : S.c = ν⁻¹ ^ 2)
    (hT : testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) ≤ CT * bNorm as B)
    (hS : ‖duhamel S.pk (μ : ℂ) (S.gB B) (2 / ν)‖ ≤
      CS * ‖Fpm true lam κ ν (2 / ν) 0‖ * testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B))
    (hL : S.momentC lam κ μ k B ≤
      CL * (‖Nnu lam κ ν‖ * ν ^ (3 + 2 * μ) / S.c) * ν ^ k *
        (‖Fpm true lam κ ν (2 / ν) 0‖⁻¹ * ‖duhamel S.pk (μ : ℂ) (S.gB B) (2 / ν)‖ +
          testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B))) :
    S.momentC lam κ μ k B ≤
      (|CL| * (|CS| + 1) * |CT|) * (‖Nnu lam κ ν‖ * ν ^ (5 + 2 * μ)) * ν ^ k * bNorm as B := by
  have hcpow : ‖Nnu lam κ ν‖ * ν ^ (3 + 2 * μ) / S.c = ‖Nnu lam κ ν‖ * ν ^ (5 + 2 * μ) := by
    rw [hc, mul_div_assoc, rpow_div_c_flat ν μ hν]
  rw [hcpow] at hL
  have hbN0 : 0 ≤ bNorm as B := ENNReal.toReal_nonneg
  have hF : ‖Fpm true lam κ ν (2 / ν) 0‖ ≠ 0 := Fpm_true_two_ne_zero lam κ ν hν
  have hTN0 : 0 ≤ testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) :=
    testedNorm_nonneg_flat _ _ _ _ _ _ _
  have hDle : ‖duhamel S.pk (μ : ℂ) (S.gB B) (2 / ν)‖ ≤
      |CS| * ‖Fpm true lam κ ν (2 / ν) 0‖ * (|CT| * bNorm as B) := by
    have h1 : CS * ‖Fpm true lam κ ν (2 / ν) 0‖ *
        testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) ≤
        |CS| * ‖Fpm true lam κ ν (2 / ν) 0‖ *
        testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)) hTN0
    have h2 : testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) ≤ |CT| * bNorm as B :=
      hT.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hbN0)
    have h3 : |CS| * ‖Fpm true lam κ ν (2 / ν) 0‖ *
        testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) ≤
        |CS| * ‖Fpm true lam κ ν (2 / ν) 0‖ * (|CT| * bNorm as B) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    exact hS.trans (h1.trans h3)
  have h2 : testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) ≤ |CT| * bNorm as B :=
    hT.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hbN0)
  have hY : ‖Fpm true lam κ ν (2 / ν) 0‖⁻¹ * ‖duhamel S.pk (μ : ℂ) (S.gB B) (2 / ν)‖ ≤
      |CS| * |CT| * bNorm as B := by
    have h4 := mul_le_mul_of_nonneg_left hDle
      (inv_nonneg.mpr (norm_nonneg (Fpm true lam κ ν (2 / ν) 0)))
    calc _ ≤ _ := h4
      _ = |CS| * |CT| * bNorm as B := by field_simp
  have hY' : ‖Fpm true lam κ ν (2 / ν) 0‖⁻¹ * ‖duhamel S.pk (μ : ℂ) (S.gB B) (2 / ν)‖ +
      testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) ≤
      (|CS| + 1) * |CT| * bNorm as B := by
    linarith [hY, h2]
  have hX : 0 ≤ ‖Nnu lam κ ν‖ * ν ^ (5 + 2 * μ) :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)
  have hk0 : 0 ≤ ν ^ k := pow_nonneg hν.le k
  have hY0 : 0 ≤ ‖Fpm true lam κ ν (2 / ν) 0‖⁻¹ * ‖duhamel S.pk (μ : ℂ) (S.gB B) (2 / ν)‖ +
      testedNorm S.pk lam κ ν (μ : ℂ) (1.1 / ν) (S.gB B) :=
    add_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hTN0
  have hA : CL * (‖Nnu lam κ ν‖ * ν ^ (5 + 2 * μ)) * ν ^ k ≤
      |CL| * (‖Nnu lam κ ν‖ * ν ^ (5 + 2 * μ)) * ν ^ k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hX) hk0
  calc S.momentC lam κ μ k B
      ≤ |CL| * (‖Nnu lam κ ν‖ * ν ^ (5 + 2 * μ)) * ν ^ k * ((|CS| + 1) * |CT| * bNorm as B) := by
        refine hL.trans ((mul_le_mul_of_nonneg_right hA hY0).trans ?_)
        exact mul_le_mul_of_nonneg_left hY' (mul_nonneg (mul_nonneg (abs_nonneg _) hX) hk0)
    _ = (|CL| * (|CS| + 1) * |CT|) * (‖Nnu lam κ ν‖ * ν ^ (5 + 2 * μ)) * ν ^ k * bNorm as B := by
        ring

/-- **`FrakTMoments` from the uniform young/tested inputs, `FlatNearUnit`, `BmatBclass`,
`ActualSeqPinned` and `FrakTOldFinite`** (source 4848-4854, 4637-4640, 4757-4760).
Composed in task `PartIII-b:IIIb-D3/2/G5/3` (`Sub/PartIII-b_IIIb-D3_2/G5/Moments.lean`). -/
theorem frakTMoments_of (D : SeqData) (hY : GroupYoung D) (hT : GroupTested D)
    (hU : FlatNearUnit D) (hB : G6.BmatBclass) (hSeq : G6.ActualSeqPinned D)
    (hFin : ∀ (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)], FrakTOldFinite as χf m) :
    FrakTMoments D := by
  intro dm dp hst hcol
  obtain ⟨κk, m, hm1, S, hκ, hm8, hSact, hSpin⟩ := hSeq dm dp hst
  obtain ⟨⟨CS, NS, hSt⟩, ⟨CL, NL, hLo⟩⟩ := hY dm dp hst κk hκ m hm8 S hSact
  obtain ⟨⟨CT, NT, hTe⟩, -⟩ := hT dm dp hst κk hκ m hm8 S hSact
  obtain ⟨Cb, hCb0, hBcl⟩ := hB D.K.χf hst.chiF D.K.as
  obtain ⟨ν₀, hν₀, hFin'⟩ := hFin D.K.as D.K.χf m hst.chiF hm8
  have hcol' : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearInst.Kflat.IsFlatDuhamelColumn
      (D.flat n) (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf := hcol
  have hsmall : ∀ᶠ n : ℕ in atTop, nu D n ≤ ν₀ :=
    ((retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)).mono fun _ hn => hn.le
  have hLH := D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt hst.chiY
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    (hSact.and (hSpin.and (hcol'.and
      ((G6.flatRealization_of D hU dm dp hst).and (hsmall.and hLH)))))
  refine ⟨(|CL| * (|CS| + 1) * |CT|) * Cb, max N0 (max NT (max NS NL)), by positivity,
    fun n hn z hz A => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : max NT (max NS NL) ≤ n := le_trans (le_max_right _ _) hn
  have hnT : NT ≤ n := le_trans (le_max_left _ _) hn1
  have hnS : NS ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn1)
  have hnL : NL ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn1)
  obtain ⟨⟨FI, hFI⟩, hSp, hDp, hRe, hνn, hLHn⟩ := hN0 n hn0
  have hl := hLHn z hz
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hμ0 : 0 ≤ D.mu n z := hl.mu_pos.le
  have hμlt : D.mu n z < 1 / 4 := hl.mu_lt
  have hμ1 : D.mu n z ≤ 1 := by linarith
  obtain ⟨mZ, ρb, o, R0, hM0, hS0, hR0, hD0, hh⟩ := hRe z hz
  obtain ⟨h, hh'⟩ := hh A
  have hid := G6.oldIdent hst.chiF (hSp z hz) (hDp z hz) o R0 hM0 hS0 hR0 hD0
    (affIota_mem _ A) h hh'
  have hFinS : OldThinFinite (cOf (nu D n)) (nu D n)
      (frakT (S n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) := by
    rw [hFI]
    exact hFin' κk (nu D n) (D.mu n z) (retEps D.Pl D.σ₀ n) D.K.χo hν hνn hμ0 hμlt
      (D.train n) (D.train_buc n) FI (affIota D.K.as A) (affIota_mem D.K.as A)
  have hFinD : OldThinFinite (cOf (nu D n)) (nu D n)
      (frakT (D.flat n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) :=
    oldThinFinite_congr hid hFinS
  obtain ⟨hBc, hBn⟩ := hBcl (nu D n) (D.mu n z) hν hμ0 hμ1 A
  have hc : (S n).c = (nu D n)⁻¹ ^ 2 :=
    (G6.level_facts hν FI D.K.χo (retEps_pos D.coeff_ne n) (S n) hFI).1.1
  set B := Bmat (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)
  have hmom0 : (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) 0 B ≤
      (|CL| * (|CS| + 1) * |CT|) * Anu D n z * (nu D n) ^ 0 * bNorm D.K.as B :=
    momentC_bound_step hν hc (hTe n hnT z hz B hBc) (hSt n hnS z hz B hBc)
      (hLo n hnL 0 (by norm_num) z hz B hBc)
  have hmom1 : (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) 1 B ≤
      (|CL| * (|CS| + 1) * |CT|) * Anu D n z * (nu D n) ^ 1 * bNorm D.K.as B :=
    momentC_bound_step hν hc (hTe n hnT z hz B hBc) (hSt n hnS z hz B hBc)
      (hLo n hnL 1 (by norm_num) z hz B hBc)
  have hFinL : OldThinFinite (cOf (nu D n)) (nu D n)
      (frakT (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)) (nu D n) (D.mu n z) D.K.χf
        (affIota D.K.as A)) := by
    rwa [← hFI]
  have hAnu0 : 0 ≤ Anu D n z :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)
  have hC0 : 0 ≤ |CL| * (|CS| + 1) * |CT| := by positivity
  refine ⟨hFinD, ?_, ?_⟩
  · rw [← oldN1w_congr D.K.χo hid, hFI]
    calc oldN1w (cOf (nu D n)) (nu D n) D.K.χo
          (frakT (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)) (nu D n) (D.mu n z) D.K.χf
            (affIota D.K.as A))
        ≤ (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).momentC D.Pl.eigenvalue D.Pl.kappa
            (D.mu n z) 1 B :=
          oldN1w_le_momentC hν FI hl.chiO (retEps D.Pl D.σ₀ n) D.Pl.eigenvalue D.Pl.kappa
            (D.mu n z) D.K.χf (affIota D.K.as A) hFinL
      _ = (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) 1 B := by rw [← hFI]
      _ ≤ (|CL| * (|CS| + 1) * |CT|) * Anu D n z * (nu D n) ^ 1 * bNorm D.K.as B := hmom1
      _ ≤ (|CL| * (|CS| + 1) * |CT|) * Anu D n z * (nu D n) ^ 1 * (Cb * ‖A‖) :=
          mul_le_mul_of_nonneg_left hBn (mul_nonneg (mul_nonneg hC0 hAnu0) (pow_nonneg hν.le 1))
      _ = (|CL| * (|CS| + 1) * |CT|) * Cb * Anu D n z * nu D n * ‖A‖ := by ring
  · rw [← oldN0w_congr D.K.χo hid, hFI]
    calc oldN0w (cOf (nu D n)) (nu D n) D.K.χo
          (frakT (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)) (nu D n) (D.mu n z) D.K.χf
            (affIota D.K.as A))
        ≤ (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).momentC D.Pl.eigenvalue D.Pl.kappa
            (D.mu n z) 0 B :=
          oldN0w_le_momentC hν FI hl.chiO (retEps D.Pl D.σ₀ n) D.Pl.eigenvalue D.Pl.kappa
            (D.mu n z) D.K.χf (affIota D.K.as A) hFinL
      _ = (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) 0 B := by rw [← hFI]
      _ ≤ (|CL| * (|CS| + 1) * |CT|) * Anu D n z * (nu D n) ^ 0 * bNorm D.K.as B := hmom0
      _ ≤ (|CL| * (|CS| + 1) * |CT|) * Anu D n z * (nu D n) ^ 0 * (Cb * ‖A‖) :=
          mul_le_mul_of_nonneg_left hBn (mul_nonneg (mul_nonneg hC0 hAnu0) (pow_nonneg hν.le 0))
      _ = (|CL| * (|CS| + 1) * |CT|) * Cb * Anu D n z * ‖A‖ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
