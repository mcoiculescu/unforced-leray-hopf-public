import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22_2_1

/-!
# Part III-a, task `PartIII-a:T22/2/1/1`: compact-interval `X_G`-norm boundedness (`CanonicalCompactXGBound`)

Source of record: `the November 2 reference manuscript`, lines 1076–1093 and
3121–3128 (`CanonicalCompactXGBound` in `Sub/PartIII-a_T22_2_1.lean:1071`).

## Proved results (`0 sorry`, `0 axiom`)

1. **`CompactXGBoundAux.planarReference_seed_and_kappa`** (Step 1 of task specification):
   Every planar reference `(P : PlanarData, hP : IsPlanarReference P)` induces a Part I seed triple
   `PartI.IsSeedXG P.eigenvalue q_P (innerSL ℂ qdag_P)` with `hq_P : q_P ∈ B0094.D.domain` and
   `PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P = P.kappa`.

2. **`CompactXGBoundAux.exists_canonical_rep_of_planarReference`** (Step 2 of task specification):
   From `T22Sub.canonicalBranch_unconditional`, `Spine.strongCanonicalIsMild`, and
   `Spine.classicalRegularityHyp`, there exist the unique `X_G`-valued canonical solution
   `V : ℝ → B0010.XG` (`PartI.IsCanonicalSolution V`, `PartI.HasCanonicalAsymptotic P.eigenvalue P.kappa q_P V`)
   and its smooth profile representative `W : ℝ → Profile` (`W θ =ᵐ[B0010.xGMeasure] V θ` for `θ > 0`)
   satisfying `IsCanonicalBranch P.eigenvalue P.kappa P.mode W`, `Cons.C01.IsXGContinuous W`, and
   the compact-interval `X_G` bound `∀ B ≥ 1, ∃ C₂ ≥ 0, ∀ θ ∈ Icc 1 B, gaussianNorm (W θ) ≤ C₂`.

3. **`CompactXGBoundAux.canonical_unique_of_rep`** (Step 3 uniqueness under `PartI.IsCanonicalSolution`):
   Whenever `P.canonical` represents any `X_G`-valued strong canonical solution `V'`
   (`PartI.IsCanonicalSolution V'`), `PartI.CanonicalBranch` uniqueness forces `V' θ = V θ` for all
   `θ > 0` and `Spine.aeEqOfContinuousOn_proof` forces `P.canonical θ r = W θ r` for all `θ, r > 0`.

4. **Conditional compact-interval bridges & concrete Part I realization**:
   * `canonicalCompactXGBound_at_of_xgContinuous`: proves the compact `[1, B]` `gaussianNorm` bound
     at any `(P, hP)` with `Cons.C01.IsXGContinuous P.canonical`.
   * `canonicalCompactXGBound_at_of_rep`: proves the compact `[1, B]` `gaussianNorm` bound at any
     `(P, hP)` whose `P.canonical` represents a `PartI.IsCanonicalSolution`.
   * `canonicalCompactXGBound_of`: reduces `CanonicalCompactXGBound` to the standing `X_G`-continuity
     field `∀ P, IsPlanarReference P → Cons.C01.IsXGContinuous P.canonical`.
   * `exists_c01_planarReference_compactXGBound`: proves unconditionally that the Part I whole-line
     Rayleigh reference datum `P₀ = Cons.C01.modeData c F W` satisfies `IsPlanarReference P₀`,
     `Cons.C01.IsXGContinuous P₀.canonical`, and compact-interval `gaussianNorm` boundedness on
     `[1, B]` for every `B ≥ 1` (hence all four clauses of `CTCanonicalBranchProps` via
     `ctCanonicalBranchProps_at`).
   * `canonicalCompactXGBound_proof`: unconditionally closes `CanonicalCompactXGBound` via
     `IsCanonicalBranch.xg_continuous`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.IIIa.T22Sub

open UnforcedLeray.Short.IIIa

namespace CompactXGBoundAux

private theorem abs_gaussianNorm_sub_le {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    |gaussianNorm f - gaussianNorm g| ≤ gaussianNorm (fun r => f r - g r) := by
  let hLf := UnforcedLeray.Cons.G3b.memLp_of_memXG hf
  let hLg := UnforcedLeray.Cons.G3b.memLp_of_memXG hg
  change |gaussianNorm f - gaussianNorm g| ≤ gaussianNorm (f - g)
  rw [UnforcedLeray.Cons.G3b.gaussianNorm_eq_norm_toLp hLf,
    UnforcedLeray.Cons.G3b.gaussianNorm_eq_norm_toLp hLg,
    UnforcedLeray.Cons.G3b.gaussianNorm_eq_norm_toLp (hLf.sub hLg),
    MemLp.toLp_sub hLf hLg]
  exact abs_norm_sub_norm_le _ _

private theorem oscillatorD_const_mul_on_pos {f g : Profile} {μ : ℂ}
    (heq : EqOn f (fun r => μ * g r) (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    oscillatorD f r = μ * oscillatorD g r := by
  have hd1 : EqOn (deriv f) (deriv (fun x => μ * g x)) (Ioi 0) := heq.deriv isOpen_Ioi
  have hd2 : EqOn (deriv (deriv f)) (deriv (deriv (fun x => μ * g x))) (Ioi 0) :=
    hd1.deriv isOpen_Ioi
  have hd1_r : deriv f r = μ * deriv g r := by
    rw [hd1 hr, deriv_const_mul_field]
  have hd2_r : deriv (deriv f) r = μ * deriv (deriv g) r := by
    rw [hd2 hr, deriv_const_mul_field', deriv_const_mul_field]
  unfold oscillatorD
  rw [hd1_r, hd2_r, heq hr]
  ring

private theorem continuousOn_canonical_slice {P : PlanarData} (hP : IsPlanarReference P)
    {θ : ℝ} (hθ : 0 < θ) : ContinuousOn (P.canonical θ) (Ioi 0) := by
  have hsm := hP.canonical.smooth.continuousOn
  have hmap : ContinuousOn (fun r : ℝ => (θ, r)) (Ioi 0) :=
    continuousOn_const.prodMk continuousOn_id
  exact hsm.comp hmap fun r hr => ⟨hθ, hr⟩

/-- Compact-interval `[1, B]` boundedness of `gaussianNorm (W θ)` for any profile curve `W`
satisfying pointwise `MemXG` and `Cons.C01.IsXGContinuous`. -/
theorem compactXGBound_of_memXG_and_xgContinuous {W : ℝ → Profile}
    (hMem : ∀ θ : ℝ, 0 < θ → MemXG (W θ))
    (hCont : UnforcedLeray.Cons.C01.IsXGContinuous W)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ θ ∈ Icc (1 : ℝ) B, gaussianNorm (W θ) ≤ C₂ := by
  have hgn_cont : ContinuousOn (fun θ : ℝ => gaussianNorm (W θ)) (Ioi 0) := by
    intro θ₀ hθ₀
    have hθ₀' : 0 < θ₀ := hθ₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have htend := (Metric.tendsto_nhds.1 (hCont θ₀ hθ₀')) ε hε
    filter_upwards [htend, isOpen_Ioi.mem_nhds hθ₀'] with θ hdist hθ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold gaussianNorm; exact Real.sqrt_nonneg _)]
      at hdist
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (abs_gaussianNorm_sub_le (hMem θ hθ) (hMem θ₀ hθ₀')) hdist
  have hK : IsCompact (Icc (1 : ℝ) B) := isCompact_Icc
  have hne : (Icc (1 : ℝ) B).Nonempty := ⟨1, le_rfl, hB⟩
  have hsub : Icc (1 : ℝ) B ⊆ Ioi 0 := fun θ hθ => lt_of_lt_of_le one_pos hθ.1
  obtain ⟨θ_max, _, hmax⟩ := hK.exists_isMaxOn hne (hgn_cont.mono hsub)
  refine ⟨max (gaussianNorm (W θ_max)) 0, le_max_right _ _, fun θ hθ => ?_⟩
  exact (hmax hθ).trans (le_max_left _ _)

/-- **Step 1**: Every `IsPlanarReference P` induces a Part I seed triple
`(P.eigenvalue, q_P, innerSL ℂ qdag_P)` with `q_P ∈ B0094.D.domain` and
`PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P = P.kappa`. -/
theorem planarReference_seed_and_kappa (P : PlanarData) (hP : IsPlanarReference P) :
    let q_P : UnforcedLeray.B0010.XG :=
      (UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG).toLp P.mode
    let qdag_P : UnforcedLeray.B0010.XG :=
      (UnforcedLeray.Cons.G3b.memLp_of_memXG hP.adjoint.memXG).toLp P.adjointMode
    ∃ hq_P : q_P ∈ UnforcedLeray.B0094.D.domain,
      UnforcedLeray.Short.PartI.IsSeedXG P.eigenvalue q_P (innerSL ℂ qdag_P) ∧
        UnforcedLeray.Short.PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P = P.kappa := by
  intro q_P qdag_P
  let hm_q := UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG
  let hm_qd := UnforcedLeray.Cons.G3b.memLp_of_memXG hP.adjoint.memXG
  obtain ⟨c, -, -, -, F, hF⟩ := UnforcedLeray.Cons.C01.exists_wholeLineData
  have hSeed0 : UnforcedLeray.Short.PartI.IsSeedXG (UnforcedLeray.Cons.G3b.lamMode c)
      (UnforcedLeray.Cons.G3b.qMode hF) (innerSL ℂ (UnforcedLeray.Cons.G3b.qdagMode hF)) :=
    UnforcedLeray.Short.Spine.wholeLineModeIsSeed c F hF
  have hq_P_eigen : UnforcedLeray.B0012.L0 q_P = P.eigenvalue • q_P := by
    change UnforcedLeray.B0012.L0 (hm_q.toLp P.mode) = P.eigenvalue • q_P
    rw [UnforcedLeray.B0012.L0_toLp hm_q]
    apply Lp.ext
    filter_upwards [UnforcedLeray.B0012.ae_xG_pos,
      (UnforcedLeray.B0012.memLp_L0Fun hm_q).coeFn_toLp,
      hm_q.coeFn_toLp, Lp.coeFn_smul P.eigenvalue q_P] with r hr hL hq hsmul
    have hq' : ((q_P : UnforcedLeray.B0010.XG) : ℝ → ℂ) r = P.mode r := hq
    rw [hL]
    change UnforcedLeray.B0012.L0Fun P.mode r =
      ((P.eigenvalue • q_P : UnforcedLeray.B0010.XG) : ℝ → ℂ) r
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hq', ← UnforcedLeray.Cons.G3b.generatorL0_eq_L0Fun,
      hP.eigenpair.eigen r hr]
  have hq_P_ne : q_P ≠ 0 := by
    intro h0
    apply hP.eigenpair.nonzero
    have hzeroX : P.mode =ᵐ[UnforcedLeray.B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [hm_q.coeFn_toLp,
        (show (⇑q_P : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure] 0 from by
          rw [h0]; exact Lp.coeFn_zero ℂ 2 UnforcedLeray.B0010.xGMeasure)] with r h1 h2
      rw [← h1, h2]
    exact UnforcedLeray.B0012.restrict_ac.ae_le hzeroX
  obtain ⟨hlam, μ, hμ⟩ := UnforcedLeray.Planar.L0_eigen_unique hSeed0.re_pos hP.eigenpair.re_pos
    hSeed0.eigen hq_P_eigen hSeed0.ne_zero hq_P_ne
  have hL_adj : ∀ v : UnforcedLeray.B0010.XG,
      inner ℂ qdag_P (UnforcedLeray.Planar.L0 v) = P.eigenvalue * inner ℂ qdag_P v := by
    intro v
    let p : Profile := (v : ℝ → ℂ)
    have hpMeas : AEStronglyMeasurable p (volume.restrict (Ioi (0 : ℝ))) :=
      (Lp.aestronglyMeasurable v).mono_ac UnforcedLeray.B0012.restrict_ac
    have hp : MemXG p := UnforcedLeray.Cons.G3b.memXG_of_memLp hpMeas (Lp.memLp v)
    have hgenAe : generatorL0 p =ᵐ[UnforcedLeray.B0010.xGMeasure]
        (UnforcedLeray.B0012.L0 v : ℝ → ℂ) := by
      filter_upwards [UnforcedLeray.B0012.coeFn_L0 v] with r hr
      rw [UnforcedLeray.Cons.G3b.generatorL0_eq_L0Fun]
      exact hr.symm
    have hgenLp : MemLp (generatorL0 p) 2 UnforcedLeray.B0010.xGMeasure :=
      (Lp.memLp (UnforcedLeray.B0012.L0 v)).ae_eq hgenAe.symm
    have hgenMeas : AEStronglyMeasurable (generatorL0 p) (volume.restrict (Ioi (0 : ℝ))) :=
      (UnforcedLeray.B0012.memXG_coe (UnforcedLeray.B0012.L0 v)).1.congr
        (UnforcedLeray.B0012.restrict_ac.ae_le hgenAe.symm)
    have hgen : MemXG (generatorL0 p) := UnforcedLeray.Cons.G3b.memXG_of_memLp hgenMeas hgenLp
    have hpRep : (UnforcedLeray.Cons.G3b.memLp_of_memXG hp).toLp p = v := by
      apply Lp.ext
      filter_upwards [(UnforcedLeray.Cons.G3b.memLp_of_memXG hp).coeFn_toLp] with r hr
      exact hr
    have hgenRep : (UnforcedLeray.Cons.G3b.memLp_of_memXG hgen).toLp (generatorL0 p) =
        UnforcedLeray.Planar.L0 v := by
      apply Lp.ext
      filter_upwards [(UnforcedLeray.Cons.G3b.memLp_of_memXG hgen).coeFn_toLp,
        UnforcedLeray.B0012.coeFn_L0 v] with r hr₁ hr₂
      rw [hr₁, UnforcedLeray.Cons.G3b.generatorL0_eq_L0Fun]
      exact hr₂.symm
    have hleft := hP.adjoint.left_eigen p hp
    rw [UnforcedLeray.Cons.G3b.gaussianPairing_eq_inner hp hP.adjoint.memXG,
      UnforcedLeray.Cons.G3b.gaussianPairing_eq_inner hgen hP.adjoint.memXG,
      hgenRep, hpRep] at hleft
    exact hleft
  have hadj_P : ContinuousLinearMap.adjoint UnforcedLeray.Planar.L0 qdag_P =
      (starRingEnd ℂ) (UnforcedLeray.Cons.G3b.lamMode c) • qdag_P := by
    apply ext_inner_right ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, inner_smul_left, starRingEnd_self_apply,
      hL_adj v, hlam]
  obtain ⟨ν_c, hν_c⟩ := UnforcedLeray.Short.PartI.adjoint_eigenvector_unique hSeed0
    (fun f => rfl) hadj_P
  have hnorm_P : inner ℂ qdag_P q_P = 1 := by
    rw [← UnforcedLeray.Cons.G3b.gaussianPairing_eq_inner hP.eigenpair.memXG hP.adjoint.memXG]
    exact hP.adjoint.normalized
  have hνμ : (starRingEnd ℂ) ν_c * μ = 1 := by
    have h1 := hnorm_P
    rw [hν_c, hμ, inner_smul_left, inner_smul_right,
      UnforcedLeray.Cons.G3b.inner_qdagMode_qMode hF, mul_one] at h1
    exact h1
  have hP_proj : UnforcedLeray.Infra.Dunford.rankOneProj (innerSL ℂ qdag_P) q_P =
      UnforcedLeray.Infra.Dunford.rankOneProj (innerSL ℂ (UnforcedLeray.Cons.G3b.qdagMode hF))
        (UnforcedLeray.Cons.G3b.qMode hF) := by
    ext x
    rw [UnforcedLeray.Infra.Dunford.rankOneProj_apply,
      UnforcedLeray.Infra.Dunford.rankOneProj_apply,
      innerSL_apply_apply, innerSL_apply_apply, hν_c, inner_smul_left, hμ, smul_smul]
    have hc : (starRingEnd ℂ) ν_c * inner ℂ (UnforcedLeray.Cons.G3b.qdagMode hF) x * μ =
        inner ℂ (UnforcedLeray.Cons.G3b.qdagMode hF) x := by
      linear_combination inner ℂ (UnforcedLeray.Cons.G3b.qdagMode hF) x * hνμ
    rw [hc]
  have hSeedP : UnforcedLeray.Short.PartI.IsSeedXG P.eigenvalue q_P (innerSL ℂ qdag_P) := by
    refine ⟨hP.eigenpair.re_pos, hq_P_ne, hq_P_eigen, ?_, ?_⟩
    · rw [innerSL_apply_apply]; exact hnorm_P
    · rw [hP_proj, hlam]; exact hSeed0.proj
  have hq0_dom := UnforcedLeray.Cons.G3b.qMode_mem_Ddomain hF
  have hq_P_dom : q_P ∈ UnforcedLeray.B0094.D.domain := by
    rw [hμ]
    exact Submodule.smul_mem _ μ hq0_dom
  refine ⟨hq_P_dom, hSeedP, ?_⟩
  have hsub_eq : (⟨q_P, hq_P_dom⟩ : UnforcedLeray.B0094.D.domain) =
      μ • ⟨UnforcedLeray.Cons.G3b.qMode hF, hq0_dom⟩ := Subtype.ext hμ
  have hsk_eq : UnforcedLeray.Short.PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P_dom =
      UnforcedLeray.Cons.G3b.kapMode c F := by
    unfold UnforcedLeray.Short.PartI.seedKappa
    rw [hsub_eq, LinearPMap.map_smul, innerSL_apply_apply, hν_c, inner_smul_left, inner_smul_right]
    have hkap0 := UnforcedLeray.Short.Spine.wholeLineModeKappa c F hF
    unfold UnforcedLeray.Short.PartI.seedKappa at hkap0
    rw [innerSL_apply_apply] at hkap0
    rw [hkap0]
    linear_combination UnforcedLeray.Cons.G3b.kapMode c F * hνμ
  have hmode_ae : P.mode =ᵐ[UnforcedLeray.B0010.xGMeasure]
      fun r => μ * UnforcedLeray.ComplexODEC.modeVort c F r := by
    have hcoe : (q_P : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure]
        ((μ • UnforcedLeray.Cons.G3b.qMode hF : UnforcedLeray.B0010.XG) : ℝ → ℂ) := by
      rw [hμ]
    filter_upwards [hm_q.coeFn_toLp, hcoe,
      Lp.coeFn_smul μ (UnforcedLeray.Cons.G3b.qMode hF),
      UnforcedLeray.Cons.G3b.coeFn_qMode hF] with r h1 h2 h3 h4
    rw [← h1, h2, h3, Pi.smul_apply, smul_eq_mul, h4]
  have hmode_eqOn : EqOn P.mode (fun r => μ * UnforcedLeray.ComplexODEC.modeVort c F r) (Ioi 0) :=
    UnforcedLeray.Short.Spine.aeEqOfContinuousOn_proof P.mode _
      hP.eigenpair.smooth.continuousOn
      (continuousOn_const.mul (UnforcedLeray.ComplexODEC.continuousOn_modeVort hF)) hmode_ae
  have hadj_ae_xG : P.adjointMode =ᵐ[UnforcedLeray.B0010.xGMeasure]
      fun r => ν_c * UnforcedLeray.Cons.C01.adjointMode c F r := by
    have hcoe : (qdag_P : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure]
        ((ν_c • UnforcedLeray.Cons.G3b.qdagMode hF : UnforcedLeray.B0010.XG) : ℝ → ℂ) := by
      rw [hν_c]
    filter_upwards [hm_qd.coeFn_toLp, hcoe,
      Lp.coeFn_smul ν_c (UnforcedLeray.Cons.G3b.qdagMode hF),
      (UnforcedLeray.Cons.G3b.memLp_of_memXG
        (UnforcedLeray.Cons.C01.memXG_adjointMode hF)).coeFn_toLp] with r h1 h2 h3 h4
    rw [← h1, h2, h3, Pi.smul_apply, smul_eq_mul]
    exact congrArg (ν_c * ·) h4
  have hadj_ae : P.adjointMode =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => ν_c * UnforcedLeray.Cons.C01.adjointMode c F r :=
    UnforcedLeray.B0012.restrict_ac.ae_le hadj_ae_xG
  have hPkap_eq : P.kappa = UnforcedLeray.Cons.G3b.kapMode c F := by
    unfold PlanarData.kappa UnforcedLeray.Cons.G3b.kapMode gaussianPairing
    have hae_int : (fun r : ℝ => oscillatorD P.mode r * conj (P.adjointMode r) *
          ((gaussianWeightInv r * r : ℝ) : ℂ)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun r : ℝ => ((starRingEnd ℂ) ν_c * μ) *
          (oscillatorD (UnforcedLeray.ComplexODEC.modeVort c F) r *
            conj (UnforcedLeray.Cons.C01.adjointMode c F r) *
            ((gaussianWeightInv r * r : ℝ) : ℂ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hadj_ae] with r hr hadj_r
      rw [oscillatorD_const_mul_on_pos hmode_eqOn hr, hadj_r, map_mul]
      ring
    rw [integral_congr_ae hae_int, hνμ]
    simp only [one_mul]
  rw [hsk_eq, hPkap_eq]

/-- **Step 2**: For every `IsPlanarReference P`, `PartI.CanonicalBranch`
(`T22Sub.canonicalBranch_unconditional`), `Spine.strongCanonicalIsMild`, and
`Spine.classicalRegularityHyp` construct the unique `X_G`-valued canonical solution `V` and a
smooth profile representative `W` satisfying `IsCanonicalBranch P.eigenvalue P.kappa P.mode W`,
`Cons.C01.IsXGContinuous W`, and compact-interval `X_G`-norm boundedness on `[1, B]`. -/
theorem exists_canonical_rep_of_planarReference (P : PlanarData) (hP : IsPlanarReference P) :
    let q_P : UnforcedLeray.B0010.XG :=
      (UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG).toLp P.mode
    ∃ (V : ℝ → UnforcedLeray.B0010.XG) (W : ℝ → Profile),
      UnforcedLeray.Short.PartI.IsCanonicalSolution V ∧
      UnforcedLeray.Short.PartI.HasCanonicalAsymptotic P.eigenvalue P.kappa q_P V ∧
      (∀ V' : ℝ → UnforcedLeray.B0010.XG,
        UnforcedLeray.Short.PartI.IsCanonicalSolution V' →
        UnforcedLeray.Short.PartI.HasCanonicalAsymptotic P.eigenvalue P.kappa q_P V' →
        ∀ θ : ℝ, 0 < θ → V' θ = V θ) ∧
      UnforcedLeray.Cons.G3b.IsXGCanonicalBranch P.eigenvalue P.kappa q_P V ∧
      (∀ θ : ℝ, 0 < θ → W θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ)) ∧
      IsCanonicalBranch P.eigenvalue P.kappa P.mode W ∧
      UnforcedLeray.Cons.C01.IsXGContinuous W ∧
      (∀ B : ℝ, 1 ≤ B → ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ θ ∈ Icc (1 : ℝ) B, gaussianNorm (W θ) ≤ C₂) := by
  intro q_P
  obtain ⟨hq_P, hSeed, hKap⟩ := planarReference_seed_and_kappa P hP
  obtain ⟨V, hVsol, hVasy, ⟨Cb, hCb⟩, hUniq, -⟩ :=
    canonicalBranch_unconditional P.eigenvalue q_P
      (innerSL ℂ ((UnforcedLeray.Cons.G3b.memLp_of_memXG hP.adjoint.memXG).toLp P.adjointMode))
      hSeed hq_P
  rw [hKap] at hVasy hUniq
  have hMild := UnforcedLeray.Short.Spine.strongCanonicalIsMild V hVsol
  have hXG : UnforcedLeray.Cons.G3b.IsXGCanonicalBranch P.eigenvalue P.kappa q_P V := by
    refine ⟨hMild, hVsol.smooth.continuousOn, ⟨Cb, hCb⟩, ?_⟩
    obtain ⟨C, b, hb, hA⟩ := hVasy
    refine ⟨C, b, hb, fun θ hθ => ?_⟩
    have h := hA θ hθ
    have e : UnforcedLeray.Cons.G3b.gauge P.eigenvalue P.kappa θ • V θ =
        Complex.exp (P.eigenvalue * θ) • (θ : ℂ) ^ P.kappa • V θ := by
      unfold UnforcedLeray.Cons.G3b.gauge
      rw [mul_smul]
    rw [e]
    exact h
  obtain ⟨W, hWV, hWs, hWe⟩ := UnforcedLeray.Short.Spine.classicalRegularityHyp V hMild
  have hq_ae : (q_P : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure] P.mode :=
    (UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG).coeFn_toLp
  obtain ⟨hWB, hWX⟩ := UnforcedLeray.Cons.G3b.isCanonicalBranch_of_rep hq_ae hXG hWV hWs hWe
  exact ⟨V, W, hVsol, hVasy, hUniq, hXG, hWV, hWB, hWX,
    compactXGBound_of_memXG_and_xgContinuous hWB.memXG hWX⟩

/-- **Step 3 uniqueness under `PartI.IsCanonicalSolution`**: if `P.canonical` represents any
`X_G`-valued strong canonical solution `V'`, then `V'` coincides on `(0, ∞)` with the canonical
solution `V` from `exists_canonical_rep_of_planarReference`, and `P.canonical θ r = W θ r` holds
pointwise on `(0, ∞) × (0, ∞)`. -/
theorem canonical_unique_of_rep (P : PlanarData) (hP : IsPlanarReference P)
    {V W : ℝ → _}
    (hUniq : ∀ V' : ℝ → UnforcedLeray.B0010.XG,
      UnforcedLeray.Short.PartI.IsCanonicalSolution V' →
      UnforcedLeray.Short.PartI.HasCanonicalAsymptotic P.eigenvalue P.kappa
        ((UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG).toLp P.mode) V' →
      ∀ θ : ℝ, 0 < θ → V' θ = V θ)
    (hWV : ∀ θ : ℝ, 0 < θ → W θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    (hWB : IsCanonicalBranch P.eigenvalue P.kappa P.mode W)
    {V' : ℝ → UnforcedLeray.B0010.XG}
    (hV'sol : UnforcedLeray.Short.PartI.IsCanonicalSolution V')
    (hPV' : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V' θ : ℝ → ℂ)) :
    (∀ θ : ℝ, 0 < θ → V' θ = V θ) ∧
      (∀ θ : ℝ, 0 < θ → ∀ r : ℝ, 0 < r → P.canonical θ r = W θ r) := by
  let q_P : UnforcedLeray.B0010.XG :=
    (UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG).toLp P.mode
  have hq_ae : (q_P : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure] P.mode :=
    (UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG).coeFn_toLp
  have hV'asy : UnforcedLeray.Short.PartI.HasCanonicalAsymptotic P.eigenvalue P.kappa q_P V' := by
    obtain ⟨C, θ₁, hθ₁, hA⟩ := hP.canonical.asymptotic
    refine ⟨C, θ₁, hθ₁, fun θ hθ => ?_⟩
    have hθ0 : 0 < θ := lt_of_lt_of_le hθ₁ hθ
    have hae : (fun r => Complex.exp (P.eigenvalue * θ) * (θ : ℂ) ^ P.kappa * P.canonical θ r -
        P.mode r) =ᵐ[UnforcedLeray.B0010.xGMeasure]
        ((Complex.exp (P.eigenvalue * θ) • (θ : ℂ) ^ P.kappa • V' θ - q_P :
          UnforcedLeray.B0010.XG) : ℝ → ℂ) := by
      filter_upwards [hPV' θ hθ0,
        Lp.coeFn_sub (Complex.exp (P.eigenvalue * θ) • (θ : ℂ) ^ P.kappa • V' θ) q_P,
        Lp.coeFn_smul (Complex.exp (P.eigenvalue * θ)) ((θ : ℂ) ^ P.kappa • V' θ),
        Lp.coeFn_smul ((θ : ℂ) ^ P.kappa) (V' θ), hq_ae] with r h1 h2 h3 h4 h5
      rw [h2, Pi.sub_apply, h3, Pi.smul_apply, smul_eq_mul, h4, Pi.smul_apply, smul_eq_mul,
        ← h1, ← h5, mul_assoc]
    rw [← UnforcedLeray.Cons.G3b.gaussianNorm_eq_norm hae]
    exact hA θ hθ
  have hEqV : ∀ θ : ℝ, 0 < θ → V' θ = V θ := hUniq V' hV'sol hV'asy
  refine ⟨hEqV, fun θ hθ r hr => ?_⟩
  have hae_PW : P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] W θ := by
    have hVV' : (V' θ : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ) := by
      rw [hEqV θ hθ]
    exact (hPV' θ hθ).trans (hVV'.trans (hWV θ hθ).symm)
  have hW_cont : ContinuousOn (W θ) (Ioi 0) :=
    UnforcedLeray.Cons.G3b.continuousOn_slice hWB.smooth hθ
  have hEqOn : EqOn (P.canonical θ) (W θ) (Ioi 0) :=
    UnforcedLeray.Short.Spine.aeEqOfContinuousOn_proof (P.canonical θ) (W θ)
      (continuousOn_canonical_slice hP hθ) hW_cont hae_PW
  exact hEqOn hr

/-- Compact-interval `X_G`-norm boundedness of `P.canonical` on `[1, B]` (`1 ≤ B`) at any planar
reference `P` whose canonical branch satisfies `Cons.C01.IsXGContinuous P.canonical`. -/
theorem canonicalCompactXGBound_at_of_xgContinuous (P : PlanarData) (hP : IsPlanarReference P)
    (hCont : UnforcedLeray.Cons.C01.IsXGContinuous P.canonical)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ θ ∈ Icc (1 : ℝ) B, gaussianNorm (P.canonical θ) ≤ C₂ :=
  compactXGBound_of_memXG_and_xgContinuous hP.canonical.memXG hCont B hB

/-- Compact-interval `X_G`-norm boundedness of `P.canonical` on `[1, B]` (`1 ≤ B`) at any planar
reference `P` whose canonical branch represents an `X_G`-valued canonical solution
`PartI.IsCanonicalSolution V`. -/
theorem canonicalCompactXGBound_at_of_rep (P : PlanarData) (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hV : UnforcedLeray.Short.PartI.IsCanonicalSolution V)
    (hPV : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ θ ∈ Icc (1 : ℝ) B, gaussianNorm (P.canonical θ) ≤ C₂ :=
  canonicalCompactXGBound_at_of_xgContinuous P hP
    (PreparedDatumAux.isXGContinuous_of_canonicalSolution hP.canonical.memXG hV hPV) B hB

/-- Conditional assembly of `CanonicalCompactXGBound` from the `X_G`-continuity bridge on
`IsPlanarReference`. -/
theorem canonicalCompactXGBound_of
    (hXG : ∀ P : PlanarData, IsPlanarReference P →
      UnforcedLeray.Cons.C01.IsXGContinuous P.canonical) :
    CanonicalCompactXGBound :=
  fun P hP B hB => canonicalCompactXGBound_at_of_xgContinuous P hP (hXG P hP) B hB

/-- Unconditional verification (`0 sorry`) on Part I's concrete whole-line Rayleigh reference datum:
there exists `P₀ : PlanarData` satisfying `IsPlanarReference P₀`,
`Cons.C01.IsXGContinuous P₀.canonical`, and compact-interval `X_G`-norm boundedness on `[1, B]`
for every `1 ≤ B`. -/
theorem exists_c01_planarReference_compactXGBound :
    ∃ P₀ : PlanarData, IsPlanarReference P₀ ∧
      UnforcedLeray.Cons.C01.IsXGContinuous P₀.canonical ∧
      (∀ B : ℝ, 1 ≤ B → ∃ C₂ : ℝ, 0 ≤ C₂ ∧
        ∀ θ ∈ Icc (1 : ℝ) B, gaussianNorm (P₀.canonical θ) ≤ C₂) := by
  obtain ⟨c, -, hre0, hre1, F, hF⟩ := UnforcedLeray.Cons.C01.exists_wholeLineData
  have hSeed := UnforcedLeray.Short.Spine.wholeLineModeIsSeed c F hF
  have hq := UnforcedLeray.Cons.G3b.qMode_mem_Ddomain hF
  obtain ⟨V, hVsol, hVasy, ⟨Cb, hCb⟩, -, -⟩ :=
    canonicalBranch_unconditional (UnforcedLeray.Cons.G3b.lamMode c)
      (UnforcedLeray.Cons.G3b.qMode hF)
      (innerSL ℂ (UnforcedLeray.Cons.G3b.qdagMode hF)) hSeed hq
  rw [UnforcedLeray.Short.Spine.wholeLineModeKappa c F hF] at hVasy
  have hMild := UnforcedLeray.Short.Spine.strongCanonicalIsMild V hVsol
  have hXG : UnforcedLeray.Cons.G3b.IsXGCanonicalBranch
      (UnforcedLeray.Cons.G3b.lamMode c) (UnforcedLeray.Cons.G3b.kapMode c F)
      (UnforcedLeray.Cons.G3b.qMode hF) V := by
    refine ⟨hMild, hVsol.smooth.continuousOn, ⟨Cb, hCb⟩, ?_⟩
    obtain ⟨C, b, hb, hA⟩ := hVasy
    refine ⟨C, b, hb, fun θ hθ => ?_⟩
    have h := hA θ hθ
    have e : UnforcedLeray.Cons.G3b.gauge (UnforcedLeray.Cons.G3b.lamMode c)
          (UnforcedLeray.Cons.G3b.kapMode c F) θ • V θ =
        Complex.exp (UnforcedLeray.Cons.G3b.lamMode c * θ) •
          (θ : ℂ) ^ (UnforcedLeray.Cons.G3b.kapMode c F) • V θ := by
      unfold UnforcedLeray.Cons.G3b.gauge
      rw [mul_smul]
    rw [e]
    exact h
  obtain ⟨W, hWV, hWs, hWe⟩ := UnforcedLeray.Short.Spine.classicalRegularityHyp V hMild
  obtain ⟨hWB, hWX⟩ := UnforcedLeray.Cons.G3b.isCanonicalBranch_of_rep
    (UnforcedLeray.Cons.G3b.coeFn_qMode hF) hXG hWV hWs hWe
  obtain ⟨σ₀, hRef⟩ := UnforcedLeray.Cons.C01.exists_referenceChoice_of_mode hF hre0 hre1 hWB
    (UnforcedLeray.Cons.C01.continuousOn_quadCurve hWB.memXG hWX)
  exact ⟨UnforcedLeray.Cons.C01.modeData c F W, hRef.1, hWX,
    canonicalCompactXGBound_at_of_xgContinuous _ hRef.1 hWX⟩

end CompactXGBoundAux

/-- Compact-interval `X_G`-norm boundedness of `P.canonical` on `[1, B]` (`1 ≤ B`) for every
planar reference `P` (`PartIII-a:T22/2/1/1`, SP 1076–1093, 3121–3128). -/
theorem canonicalCompactXGBound_proof : UnforcedLeray.Short.IIIa.T22Sub.CanonicalCompactXGBound :=
  CompactXGBoundAux.canonicalCompactXGBound_of (fun _ hP => hP.canonical.xg_continuous)

end UnforcedLeray.Short.IIIa.T22Sub
