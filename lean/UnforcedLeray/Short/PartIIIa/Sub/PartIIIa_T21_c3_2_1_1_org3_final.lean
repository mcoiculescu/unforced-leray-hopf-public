import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a.Assembly_T21_c3_2_1_1_org_3_a
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelBlockDiagonal.Pins
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2
import UnforcedLeray.Short.PartIIb.Org.RealCompactDuhamel

/-!
# Part III-a, task `PartIII-a:T21/c3/2/1/1/org/3`: corrected cell-block bound (`relCellBlockBoundF`)

Source of record: `the November 2 reference manuscript` (SP), lines 2943-2944 and
2962-2982 (`lem:short-compact-duhamel` applied on blocks of length `B` to the cell-projected free
evolution `F_n = (clampF B F_rel) ∘ cellProjW_{d(t₁)}` and damped interaction `A_n = clampA B A_rel`).

Since `d(ageAt ν t₁ r) ≤ d(t₁)` for all `r ∈ [0, B]` and `A_rel r` lands in `B0579.cell (d(ageAt ν t₁ r))`
(`RelBlockDiagonalSub.dampedInt_cellSupported`, SP 2943-2944), `cellProjW_{d(t₁)} (clampA B A_rel r V) =
clampA B A_rel r V` identically; hence `U_n(t, s) := U_rel(t, s) ∘ cellProjW_{d(t₁)}` is the Duhamel
evolution of `(F_n, A_n)` on all blocks `s ≤ t ≤ s + B`, and agrees with `U_rel(B, 0)` on entrance
cell-supported data `W`. Applying `RCDuhamel.compact_duhamel` along the successive-limit filter of
hypothetically violating configurations yields operator-norm convergence of `(U_n - F_n)(B, 0)` to
`(U_0 - F_0)(B, 0)` (SP 2978-2980), contradicting the violation.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3

namespace RelCellFinalAux

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

private lemma clampB_eq_of_mem {B r : ℝ} (hr0 : 0 ≤ r) (hrB : r ≤ B) : clampB B r = r := by
  unfold clampB
  rw [min_eq_left hrB, max_eq_right hr0]

private lemma clampB_mem_Icc {B : ℝ} (hB : 0 ≤ B) (r : ℝ) : clampB B r ∈ Icc (0 : ℝ) B :=
  ⟨clampB_nonneg B r, clampB_le B r hB⟩

private lemma isCellSupportedW_mono {m d₁ d₂ : ℝ} (hd : d₁ ≤ d₂) {V : Planar.L2w m}
    (hV : IsCellSupportedW d₁ V) : IsCellSupportedW d₂ V := by
  filter_upwards [hV] with z hz hnot
  apply hz
  intro hmem
  apply hnot
  simp only [B0579.cell, mem_prod, mem_univ, and_true, mem_Ico] at hmem ⊢
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

private lemma cellProjW_eq_self_of_isCellSupportedW {m d : ℝ} {W : Planar.L2w m}
    (hW : IsCellSupportedW d W) : cellProjW m d W = W := by
  have hW' : ∀ᵐ z ∂(Planar.wMeasure m), cToPlane z ∉ B0579.cell d → (W : ℂ → ℂ) z = 0 :=
    (Planar.wMeasure_ac m).ae_le hW
  have happ : cellProjW m d W = ((Lp.memLp W).indicator (measurableSet_cellC d)).toLp _ := rfl
  rw [happ]
  refine Lp.ext ?_
  filter_upwards [((Lp.memLp W).indicator (measurableSet_cellC d)).coeFn_toLp, hW'] with z h1 h2
  rw [h1]
  by_cases hz : z ∈ {z : ℂ | cToPlane z ∈ B0579.cell d}
  · exact Set.indicator_of_mem hz _
  · rw [Set.indicator_of_notMem hz, h2 hz]

private lemma cellLen_ageAt_le_entrance {ν t₁ t₂ B τ : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hBeq : movingZ ν t₂ - movingZ ν t₁ = B) (hτ : τ ∈ Icc (0 : ℝ) B) :
    cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) ≤
      cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁) := by
  have hage : t₁ ≤ ageAt ν t₁ τ :=
    (VariationOfConstantsSub.ageAt_mem_Icc hν ht₁ h12 hBeq hτ).1
  have ha₁ : 0 < clockA ν t₁ := by unfold clockA; positivity
  have ha_le : clockA ν t₁ ≤ clockA ν (ageAt ν t₁ τ) := by
    unfold clockA
    nlinarith [mul_le_mul_of_nonneg_left hage hν.le]
  unfold cellLen
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hν.le _)
    (Real.sqrt_pos.2 ha₁) (Real.sqrt_le_sqrt ha_le)

private lemma cellProjW_clampA_eq {κ : PlanarFrameKernels} {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ t₂ B : ℝ}
    {A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hB : 0 ≤ B)
    (hBeq : movingZ ν t₂ - movingZ ν t₁ = B)
    (hA : IsDampedComplBlockInt κ P ν m tr t₁ B A_rel)
    (r : ℝ) (V : Planar.L2w m) :
    cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) (clampA B A_rel r V) =
      clampA B A_rel r V := by
  have hτ : clampB B r ∈ Icc (0 : ℝ) B := clampB_mem_Icc hB r
  have hsupp_τ : IsCellSupportedW
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ (clampB B r)))) (A_rel (clampB B r) V) :=
    RelBlockDiagonalSub.dampedInt_cellSupported hA hτ V
  have hd_le := cellLen_ageAt_le_entrance hν ht₁ h12 hBeq hτ
  exact cellProjW_eq_self_of_isCellSupportedW (isCellSupportedW_mono hd_le hsupp_τ)

private lemma isDuhamelEvolution_proj {κ : PlanarFrameKernels} {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ t₂ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    {A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    {U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hB : 0 ≤ B)
    (hBeq : movingZ ν t₂ - movingZ ν t₁ = B)
    (hA : IsDampedComplBlockInt κ P ν m tr t₁ B A_rel)
    (hU : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
      (fun _ => clampF B F_rel) (fun _ => clampA B A_rel) (fun _ => U_rel)) :
    UnforcedLeray.Short.IIb.RCDuhamel.IsDuhamelEvolution (ι := Unit) B
      (fun _ t s =>
        (clampF B F_rel t s) ∘L cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)))
      (fun _ => clampA B A_rel)
      (fun _ t s =>
        (U_rel t s) ∘L cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))) := by
  set proj := cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
  have hPA : ∀ r V, proj (clampA B A_rel r V) = clampA B A_rel r V :=
    cellProjW_clampA_eq hν ht₁ h12 hB hBeq hA
  refine
    { integrable := fun p s t hst hts x => ?_
      duhamel := fun p s t hst hts x => ?_
      bounded := fun p s => ?_ }
  · have heq :
        (fun r => ((clampF B F_rel t r) ∘L proj) (clampA B A_rel r (((U_rel r s) ∘L proj) x))) =
          fun r => clampF B F_rel t r (clampA B A_rel r (U_rel r s (proj x))) := by
      funext r
      simp only [ContinuousLinearMap.comp_apply, hPA]
    rw [heq]
    exact hU.integrable () s t hst hts (proj x)
  · simp only [ContinuousLinearMap.comp_apply, hPA]
    exact hU.duhamel () s t hst hts (proj x)
  · obtain ⟨C, hC⟩ := hU.bounded () s
    refine ⟨max C 0, fun t hst hts => ?_⟩
    have hCt : ‖U_rel t s‖ ≤ max C 0 := (hC t hst hts).trans (le_max_left _ _)
    calc ‖(U_rel t s) ∘L proj‖
        ≤ ‖U_rel t s‖ * ‖proj‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ max C 0 * 1 :=
          mul_le_mul hCt (StrongA.norm_cellProjW_le _ _) (norm_nonneg _) (le_max_right _ _)
      _ = max C 0 := mul_one _

private lemma norm_planarRelTransportRe_le (P : PlanarData) (m t s : ℝ) :
    ‖planarRelTransportRe P m t s‖ ≤ Real.exp (-P.eigenvalue.re * (t - s)) := by
  unfold planarRelTransportRe
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-P.eigenvalue.re * (t - s)) * ‖Planar.transportGroupW m (t - s)‖
      ≤ Real.exp (-P.eigenvalue.re * (t - s)) * 1 :=
        mul_le_mul_of_nonneg_left (Planar.norm_transportGroupW_le m (t - s)) (Real.exp_pos _).le
    _ = Real.exp (-P.eigenvalue.re * (t - s)) := mul_one _

private lemma norm_planarRelTransportRe_clampB_le_one {P : PlanarData}
    (hre : 0 ≤ P.eigenvalue.re) (m B : ℝ) {t s : ℝ} (hst : s ≤ t) :
    ‖planarRelTransportRe P m (clampB B t) (clampB B s)‖ ≤ 1 := by
  have hcl : 0 ≤ clampB B t - clampB B s := sub_nonneg.2 (clampB_mono B hst)
  refine (norm_planarRelTransportRe_le P m (clampB B t) (clampB B s)).trans ?_
  rw [Real.exp_le_one_iff]
  nlinarith

private structure ViolCfg (κ : PlanarFrameKernels) (P : PlanarData)
    (m K C₀ h Cproj B M_free K_A δ_gap : ℝ) where
  b : ℝ
  hb1 : 1 ≤ b
  ν : ℝ
  hν0 : 0 < ν
  hF : PerFrameFacts κ ν m b K
  tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))
  htr : UnforcedLeray.Short.PartI.IsBUCTrain tr
  t₁ : ℝ
  t₂ : ℝ
  ht₁ : 0 ≤ t₁
  h12 : t₁ ≤ t₂
  hbt : b ≤ clockTheta ν t₂
  hBeq : movingZ ν t₂ - movingZ ν t₁ = B
  α' : ℝ
  hα' : 0 ≤ α'
  F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m
  A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m
  U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m
  htriple : BlockTriple κ P ν m tr t₁ B M_free K_A α' F_rel A_rel U_rel
  W : Planar.L2w m
  hW : IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W
  hviol : (C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) + α' +
      Real.exp (-P.eigenvalue.re * B) + δ_gap) * ‖W‖ < ‖U_rel B 0 W‖

private structure SuccIdx where
  b₀ : ℝ
  hb₀ : 1 ≤ b₀
  ν₀ : ℝ → ℝ
  hν₀ : ∀ b, b₀ ≤ b → 0 < ν₀ b

private def tailSet {κ : PlanarFrameKernels} {P : PlanarData}
    {m K C₀ h Cproj B M_free K_A δ_gap : ℝ} (i : SuccIdx) :
    Set (ViolCfg κ P m K C₀ h Cproj B M_free K_A δ_gap) :=
  {c | i.b₀ ≤ c.b ∧ c.ν ≤ i.ν₀ c.b}

private def succFilterBasis (κ : PlanarFrameKernels) (P : PlanarData)
    (m K C₀ h Cproj B M_free K_A δ_gap : ℝ) :
    FilterBasis (ViolCfg κ P m K C₀ h Cproj B M_free K_A δ_gap) where
  sets := range (tailSet (κ := κ) (P := P) (m := m) (K := K) (C₀ := C₀) (h := h)
    (Cproj := Cproj) (B := B) (M_free := M_free) (K_A := K_A) (δ_gap := δ_gap))
  nonempty := ⟨tailSet ⟨1, le_rfl, fun _ => 1, fun _ _ => one_pos⟩,
    ⟨⟨1, le_rfl, fun _ => 1, fun _ _ => one_pos⟩, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i₁, rfl⟩ ⟨i₂, rfl⟩
    let i₃ : SuccIdx :=
      { b₀ := max i₁.b₀ i₂.b₀
        hb₀ := i₁.hb₀.trans (le_max_left _ _)
        ν₀ := fun b => min (i₁.ν₀ b) (i₂.ν₀ b)
        hν₀ := fun b hb => lt_min
          (i₁.hν₀ b ((le_max_left _ _).trans hb))
          (i₂.hν₀ b ((le_max_right _ _).trans hb)) }
    refine ⟨tailSet i₃, ⟨i₃, rfl⟩, fun c hc => ?_⟩
    exact ⟨⟨(le_max_left _ _).trans hc.1, hc.2.trans (min_le_left _ _)⟩,
      ⟨(le_max_right _ _).trans hc.1, hc.2.trans (min_le_right _ _)⟩⟩

private lemma eventually_of_succBlock {κ : PlanarFrameKernels} {P : PlanarData}
    {m K C₀ h Cproj B M_free K_A δ_gap : ℝ}
    {Q : ∀ ν : ℝ, UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)) → ℝ → ℝ → Prop}
    (hQ : SuccBlock κ m K B Q) :
    ∀ᶠ c in (succFilterBasis κ P m K C₀ h Cproj B M_free K_A δ_gap).filter,
      Q c.ν c.tr c.t₁ c.t₂ := by
  obtain ⟨b₀, hb₀, hstep⟩ := hQ
  classical
  let ν_fn : ℝ → ℝ := fun b =>
    if hb : b₀ ≤ b then Classical.choose (hstep b hb) else 1
  have hν_pos : ∀ b, b₀ ≤ b → 0 < ν_fn b := by
    intro b hb
    dsimp only [ν_fn]
    split_ifs
    exact (Classical.choose_spec (hstep b hb)).1
  let idx : SuccIdx := ⟨b₀, hb₀, ν_fn, hν_pos⟩
  rw [Filter.Eventually, FilterBasis.mem_filter_iff]
  refine ⟨tailSet idx, ⟨idx, rfl⟩, fun c hc => ?_⟩
  have hb : b₀ ≤ c.b := hc.1
  have hν_le : c.ν ≤ Classical.choose (hstep c.b hb) := by
    have h := hc.2
    dsimp only [idx, ν_fn] at h
    split_ifs at h
    exact h
  exact (Classical.choose_spec (hstep c.b hb)).2 c.ν ⟨c.hν0, hν_le⟩ c.hF c.tr c.htr
    c.t₁ c.t₂ c.ht₁ c.h12 c.hbt c.hBeq

private theorem relCellBlockBoundF_proof (κ : PlanarFrameKernels)
    (hS : RelStrongLimit κ) (hA : RelPlanarInteraction κ) :
    RelCellBlockBoundF κ := by
  intro hκ P hP m hm K C₀ h Cproj B M_free K_A δ_gap
    hC₀ hh hh_le hCp hB hM hKA hδ hSeed hProj
  by_contra hnot
  let FB := succFilterBasis κ P m K C₀ h Cproj B M_free K_A δ_gap
  let l := FB.filter
  have hl_neBot : l.NeBot := by
    rw [Filter.neBot_iff]
    intro hempty
    have he : (∅ : Set (ViolCfg κ P m K C₀ h Cproj B M_free K_A δ_gap)) ∈ l :=
      Filter.empty_mem_iff_bot.2 hempty
    rw [FilterBasis.mem_filter_iff] at he
    obtain ⟨_, ⟨idx, rfl⟩, hsub⟩ := he
    apply hnot
    refine ⟨idx.b₀, idx.hb₀, fun b hb => ⟨idx.ν₀ b, idx.hν₀ b hb, ?_⟩⟩
    intro ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBeq α' hα' F_rel A_rel U_rel htriple W hW
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    let cfg : ViolCfg κ P m K C₀ h Cproj B M_free K_A δ_gap :=
      { b := b
        hb1 := idx.hb₀.trans hb
        ν := ν
        hν0 := hν.1
        hF := hF
        tr := tr
        htr := htr
        t₁ := t₁
        t₂ := t₂
        ht₁ := ht₁
        h12 := h12
        hbt := hbt
        hBeq := hBeq
        α' := α'
        hα' := hα'
        F_rel := F_rel
        A_rel := A_rel
        U_rel := U_rel
        htriple := htriple
        W := W
        hW := hW
        hviol := hlt }
    exact hsub (a := cfg) ⟨hb, hν.2⟩
  obtain ⟨A0, hA0c, hA0tb, hD0, hU0_bd, hA_lim⟩ :=
    hA hκ P hP m hm K C₀ h Cproj B hC₀ hh hh_le hCp hB hSeed hProj
  let F₀ : Unit → ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
    fun _ t s => planarRelTransportRe P m (clampB B t) (clampB B s)
  let A₀' : Unit → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
    fun _ r => A0 (clampB B r)
  have hre0 : 0 ≤ P.eigenvalue.re := hh.le.trans hh_le
  have hF0_one : ∀ (p : Unit) (t s : ℝ), s ≤ t → t ≤ s + B → ‖F₀ p t s‖ ≤ 1 :=
    fun _ _ _ hst _ => norm_planarRelTransportRe_clampB_le_one hre0 m B hst
  -- Norm bound on `A₀'` from one configuration meeting `hA_lim 1`
  have hA1_ev := eventually_of_succBlock (P := P)
    (C₀ := C₀) (h := h) (Cproj := Cproj) (M_free := M_free) (K_A := K_A) (δ_gap := δ_gap)
    (hA_lim 1 one_pos)
  obtain ⟨c₁, hc₁⟩ := hA1_ev.exists
  have hA0_bd : ∀ (p : Unit) (r : ℝ), ‖A₀' p r‖ ≤ K_A + 1 := by
    intro _ r
    have hr : clampB B r ∈ Icc (0 : ℝ) B := clampB_mem_Icc hB.le r
    have hdiff : ‖c₁.A_rel (clampB B r) - A0 (clampB B r)‖ < 1 :=
      hc₁ c₁.A_rel c₁.htriple.2.2.1 _ hr
    have hAr : ‖c₁.A_rel (clampB B r)‖ ≤ K_A := c₁.htriple.2.2.2.1 _
    calc ‖A0 (clampB B r)‖
        = ‖c₁.A_rel (clampB B r) - (c₁.A_rel (clampB B r) - A0 (clampB B r))‖ := by
          rw [sub_sub_cancel]
      _ ≤ ‖c₁.A_rel (clampB B r)‖ + ‖c₁.A_rel (clampB B r) - A0 (clampB B r)‖ := norm_sub_le _ _
      _ ≤ K_A + 1 := add_le_add hAr hdiff.le
  obtain ⟨U₀, hU₀_sum⟩ := UnforcedLeray.B0104.exists_isDysonSum hF0_one hA0_bd hD0
  have hU₀_b0104 : UnforcedLeray.B0104.IsDuhamelEvolution B F₀ A₀' U₀ :=
    hU₀_sum.isDuhamelEvolution hF0_one hA0_bd hD0
  have hU₀ : UnforcedLeray.Short.IIb.RCDuhamel.IsDuhamelEvolution B F₀ A₀' U₀ :=
    ⟨hU₀_b0104.integrable, hU₀_b0104.duhamel, hU₀_b0104.bounded⟩
  have hU₀_B0 : ‖U₀ () B 0‖ ≤ C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) :=
    hU0_bd U₀ hU₀_sum
  let F_proj : ViolCfg κ P m K C₀ h Cproj B M_free K_A δ_gap →
      Unit → ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
    fun c _ t s =>
      (clampF B c.F_rel t s) ∘L cellProjW m (cellLen (c.ν ^ (-2 : ℝ)) (clockA c.ν c.t₁))
  let A_proj : ViolCfg κ P m K C₀ h Cproj B M_free K_A δ_gap →
      Unit → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
    fun c _ => clampA B c.A_rel
  let U_proj : ViolCfg κ P m K C₀ h Cproj B M_free K_A δ_gap →
      Unit → ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
    fun c _ t s =>
      (c.U_rel t s) ∘L cellProjW m (cellLen (c.ν ^ (-2 : ℝ)) (clockA c.ν c.t₁))
  have hFb : ∃ M, ∀ c p t s, s ≤ t → t ≤ s + B →
      ‖F_proj c p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M := by
    refine ⟨max M_free 1, fun c p t s hst hts => ⟨?_, ?_⟩⟩
    · have hcl1 : clampB B s ≤ clampB B t := clampB_mono B hst
      have hcl2 : clampB B t ≤ clampB B s + B := by
        have := clampB_le B t hB.le
        have := clampB_nonneg B s
        linarith
      have hFc : ‖clampF B c.F_rel t s‖ ≤ M_free :=
        c.htriple.2.1 _ _ hcl1 hcl2
      calc ‖F_proj c p t s‖
          ≤ ‖clampF B c.F_rel t s‖ *
              ‖cellProjW m (cellLen (c.ν ^ (-2 : ℝ)) (clockA c.ν c.t₁))‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M_free * 1 :=
            mul_le_mul hFc (StrongA.norm_cellProjW_le _ _) (norm_nonneg _) hM
        _ = M_free := mul_one _
        _ ≤ max M_free 1 := le_max_left _ _
    · exact (hF0_one p t s hst hts).trans (le_max_right _ _)
  have hF_str : UnforcedLeray.Short.IIb.RCDuhamel.StrongTendstoOnBlocks l B F_proj F₀ := by
    intro x ε hε
    refine (eventually_of_succBlock (P := P)
      (C₀ := C₀) (h := h) (Cproj := Cproj) (M_free := M_free) (K_A := K_A) (δ_gap := δ_gap)
      (hS hκ P hP m hm K B hB ε hε x)).mono fun c hc p t s hst _ => ?_
    exact (hc c.F_rel c.htriple.1 (clampB B s) (clampB B t)
      (clampB_nonneg B s) (clampB_mono B hst) (clampB_le B t hB.le)).1
  have hF_adj : UnforcedLeray.Short.IIb.RCDuhamel.StrongTendstoOnBlocks l B
      (fun c p t s => ContinuousLinearMap.adjoint (F_proj c p t s))
      (fun p t s => ContinuousLinearMap.adjoint (F₀ p t s)) := by
    intro x ε hε
    refine (eventually_of_succBlock (P := P)
      (C₀ := C₀) (h := h) (Cproj := Cproj) (M_free := M_free) (K_A := K_A) (δ_gap := δ_gap)
      (hS hκ P hP m hm K B hB ε hε x)).mono fun c hc p t s hst _ => ?_
    exact (hc c.F_rel c.htriple.1 (clampB B s) (clampB B t)
      (clampB_nonneg B s) (clampB_mono B hst) (clampB_le B t hB.le)).2
  have hAb : ∃ K', ∀ c p r, ‖A_proj c p r‖ ≤ K' :=
    ⟨K_A, fun c _ r => c.htriple.2.2.2.1 (clampB B r)⟩
  have hA_str : ∀ ε > 0, ∀ᶠ c in l, ∀ p r, ‖A_proj c p r - A₀' p r‖ < ε := by
    intro ε hε
    refine (eventually_of_succBlock (P := P)
      (C₀ := C₀) (h := h) (Cproj := Cproj) (M_free := M_free) (K_A := K_A) (δ_gap := δ_gap)
      (hA_lim ε hε)).mono fun c hc _ r =>
      hc c.A_rel c.htriple.2.2.1 (clampB B r) (clampB_mem_Icc hB.le r)
  have hA₀c' : ∀ p r, IsCompactOperator (A₀' p r) := fun _ r => hA0c (clampB B r)
  have hA₀p' : TotallyBounded (range fun q : Unit × ℝ => A₀' q.1 q.2) := by
    refine hA0tb.subset ?_
    rintro _ ⟨⟨_, r⟩, rfl⟩
    exact ⟨clampB B r, rfl⟩
  have hU_all : ∀ c, UnforcedLeray.Short.IIb.RCDuhamel.IsDuhamelEvolution B
      (F_proj c) (A_proj c) (U_proj c) :=
    fun c => isDuhamelEvolution_proj c.hν0 c.ht₁ c.h12 hB.le c.hBeq
      c.htriple.2.2.1 c.htriple.2.2.2.2.1
  have hCD := UnforcedLeray.Short.IIb.RCDuhamel.compact_duhamel (l := l) (B := B)
    hFb hF_str hF_adj hAb hA_str hA₀c' hA₀p' hU_all hU₀
  obtain ⟨c, hc_rem⟩ := (hCD.2.2 δ_gap hδ).exists
  have hrem : ‖(U_proj c () B 0 - F_proj c () B 0) - (U₀ () B 0 - F₀ () B 0)‖ < δ_gap :=
    hc_rem () B 0 hB.le (by linarith)
  have hprojW : cellProjW m (cellLen (c.ν ^ (-2 : ℝ)) (clockA c.ν c.t₁)) c.W = c.W :=
    cellProjW_eq_self_of_isCellSupportedW c.hW
  have hclB : clampB B B = B := clampB_eq_of_mem hB.le le_rfl
  have hcl0 : clampB B 0 = 0 := clampB_eq_of_mem le_rfl hB.le
  have hUW : U_proj c () B 0 c.W = c.U_rel B 0 c.W := by
    show c.U_rel B 0 (cellProjW m (cellLen (c.ν ^ (-2 : ℝ)) (clockA c.ν c.t₁)) c.W) = _
    rw [hprojW]
  have hFW : F_proj c () B 0 c.W = c.F_rel B 0 c.W := by
    show clampF B c.F_rel B 0
      (cellProjW m (cellLen (c.ν ^ (-2 : ℝ)) (clockA c.ν c.t₁)) c.W) = _
    rw [hprojW]
    simp only [clampF, hclB, hcl0]
  have hsplit : c.U_rel B 0 c.W =
      ((c.F_rel B 0 c.W + U₀ () B 0 c.W) + (-F₀ () B 0 c.W)) +
        ((U_proj c () B 0 - F_proj c () B 0) - (U₀ () B 0 - F₀ () B 0)) c.W := by
    simp only [sub_apply, hUW, hFW]
    abel
  have hF_bdW : ‖c.F_rel B 0 c.W‖ ≤ c.α' * ‖c.W‖ :=
    c.htriple.2.2.2.2.2 c.W c.hW
  have hU0_bdW : ‖U₀ () B 0 c.W‖ ≤
      (C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B)) * ‖c.W‖ :=
    ((U₀ () B 0).le_opNorm c.W).trans (mul_le_mul_of_nonneg_right hU₀_B0 (norm_nonneg _))
  have hF0_B0 : ‖F₀ () B 0‖ ≤ Real.exp (-P.eigenvalue.re * B) := by
    show ‖planarRelTransportRe P m (clampB B B) (clampB B 0)‖ ≤ _
    rw [hclB, hcl0]
    simpa [sub_zero] using norm_planarRelTransportRe_le P m B 0
  have hF0_bdW : ‖-F₀ () B 0 c.W‖ ≤ Real.exp (-P.eigenvalue.re * B) * ‖c.W‖ := by
    rw [norm_neg]
    exact ((F₀ () B 0).le_opNorm c.W).trans (mul_le_mul_of_nonneg_right hF0_B0 (norm_nonneg _))
  have hrem_bdW :
      ‖((U_proj c () B 0 - F_proj c () B 0) - (U₀ () B 0 - F₀ () B 0)) c.W‖ ≤ δ_gap * ‖c.W‖ :=
    (((U_proj c () B 0 - F_proj c () B 0) - (U₀ () B 0 - F₀ () B 0)).le_opNorm c.W).trans
      (mul_le_mul_of_nonneg_right hrem.le (norm_nonneg _))
  have htot : ‖c.U_rel B 0 c.W‖ ≤
      (C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) + c.α' +
        Real.exp (-P.eigenvalue.re * B) + δ_gap) * ‖c.W‖ := by
    rw [hsplit]
    calc ‖((c.F_rel B 0 c.W + U₀ () B 0 c.W) + (-F₀ () B 0 c.W)) +
            ((U_proj c () B 0 - F_proj c () B 0) - (U₀ () B 0 - F₀ () B 0)) c.W‖
        ≤ ‖(c.F_rel B 0 c.W + U₀ () B 0 c.W) + (-F₀ () B 0 c.W)‖ +
            ‖((U_proj c () B 0 - F_proj c () B 0) - (U₀ () B 0 - F₀ () B 0)) c.W‖ :=
          norm_add_le _ _
      _ ≤ (‖c.F_rel B 0 c.W‖ + ‖U₀ () B 0 c.W‖ + ‖-F₀ () B 0 c.W‖) +
            ‖((U_proj c () B 0 - F_proj c () B 0) - (U₀ () B 0 - F₀ () B 0)) c.W‖ := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (c.α' * ‖c.W‖ + (C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B)) * ‖c.W‖ +
            Real.exp (-P.eigenvalue.re * B) * ‖c.W‖) + δ_gap * ‖c.W‖ :=
          add_le_add (add_le_add (add_le_add hF_bdW hU0_bdW) hF0_bdW) hrem_bdW
      _ = (C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) + c.α' +
            Real.exp (-P.eigenvalue.re * B) + δ_gap) * ‖c.W‖ := by ring
  exact not_lt_of_ge htot c.hviol

end RelCellFinalAux

/-- Conditional assembly of `RelCellBlockBoundF` from `RelStrongLimit` and `RelPlanarInteraction`
(SP 2943-2944, 2962-2980). -/
theorem relCellBlockBoundF_of (κ : PlanarFrameKernels)
    (hS : RelStrongLimit κ) (hA : RelPlanarInteraction κ) :
    RelCellBlockBoundF κ :=
  RelCellFinalAux.relCellBlockBoundF_proof κ hS hA

theorem relCellBlockBoundF (κ : PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.RelCellBlockBoundF κ :=
  relCellBlockBoundF_of κ (UnforcedLeray.Short.IIIa.relStrongLimit κ) (relPlanarInteraction κ)

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3
