import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.Continuity
import UnforcedLeray.Lib.LerayLp.Duality
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Joint continuity of the jets of the Leray term (`PartII-b:S3/1/1/2/1/2/2`)

Source of record: `the November 2 reference manuscript`,
lines 2552-2562 ("the bounded Cartesian Leray map preserves them in $W^{k,p}$ ... the resulting
$C_\tau W^{k,4}$ regularity").

`lerayJetContinuous_proof : CorrComovingSub.LerayJetContinuous`.

Proof. The jets of `𝔓(U·∇U)` are the smooth Leray representatives of the jets
`G τ = ∂^{ws}(U τ·∇U τ)` (`CoordDerivSub.dirSpatialJet_smoothConvectiveLeray`), and `G` is a
uniformly smooth `L⁴` slice family which is jointly continuous (product rule along the jets; the
jets of `U = U_raw + E_εα + w` are jointly continuous). For such `G` the smooth Leray slice
`H = smoothLeraySlice G` is jointly continuous:
* `H τ` is Lipschitz in space uniformly in `τ` (bounded first derivative);
* for fixed `y₀`, `⟪v, H τ y₀⟫` is the uniform limit (as `r → 0`) of the mollified values
  `∫ ρ_r ⟪v, H τ⟫ = ∫ ⟪𝔓(ρ_r v), G τ⟫` (symmetry of `𝔓` under the `L^{4/3}`–`L⁴` pairing);
* `τ ↦ ∫ ⟪f, G τ⟫` is continuous for every `f ∈ L^{4/3}`: approximate `f` in `L^{4/3}` by
  continuous compactly supported `g` (uniform `L⁴` bound of `G τ`), and `τ ↦ ∫ ⟪g, G τ⟫` is
  continuous by joint continuity of `G`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Blueprint UnforcedLeray.RieszLp

namespace LerayContSub

local instance fact_one_le_four_lc : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

local instance fact_q0_ge_one_lc : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  inferInstanceAs (Fact (1 ≤ q0E))

/-! ## 1. Uniform approximation -/

/-- A real function uniformly approximable by continuous functions is continuous. -/
theorem continuous_of_forall_approx {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ F : α → ℝ, Continuous F ∧ ∀ y, dist (f y) (F y) ≤ ε) :
    Continuous f := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨F, hF, hFf⟩ := h (ε / 2) (half_pos hε)
  exact ⟨F, hF, fun y => hεu (lt_of_le_of_lt (hFf y) (half_lt_self hε))⟩

/-! ## 2. Slice facts -/

theorem memLp_slice {G : ℝ → SpatialField} (hG : IsUniformSmoothL4SliceFamily G) (τ : ℝ) :
    MemLp (G τ) 4 volume := by
  have h0 := SmoothLeraySliceSub.memLp_iteratedFDeriv_of_sliceFamily hG 0 τ
  refine h0.congr_norm
    (HigherPhaseSub.sliceFamily_contDiff_infty hG τ).continuous.aestronglyMeasurable ?_
  exact Eventually.of_forall fun y => norm_iteratedFDeriv_zero

theorem exists_norm_toLp_le {G : ℝ → SpatialField} (hG : IsUniformSmoothL4SliceFamily G) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, ‖(memLp_slice hG τ).toLp (G τ)‖ ≤ M := by
  obtain ⟨M, hM⟩ := hG.l4_bounded 0
  refine ⟨max M 0, le_max_right _ _, fun τ => ?_⟩
  rw [Lp.norm_toLp]
  have heq : eLpNorm (G τ) 4 volume =
      eLpNorm (fun y => iteratedFDeriv ℝ 0 (G τ) y) 4 volume :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_iteratedFDeriv_zero.symm)
  rw [heq]
  exact (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
    ((hM τ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))

/-! ## 3. Weak continuity: `τ ↦ ∫ ⟪f, G τ⟫` for `f ∈ L^{4/3}` -/

/-- `τ ↦ ∫ ⟪g, G τ⟫` is continuous for continuous compactly supported `g`. -/
theorem continuous_integral_inner_of_compact {g : Space → Space} (hg : Continuous g)
    (hgc : HasCompactSupport g) {G : ℝ → SpatialField}
    (hGc : Continuous (fun x : ℝ × Space => G x.1 x.2)) :
    Continuous fun τ => ∫ y, inner ℝ (g y) (G τ y) := by
  have heq : (fun τ => ∫ y, inner ℝ (g y) (G τ y)) =
      fun τ => ∫ y in tsupport g, inner ℝ (g y) (G τ y) := by
    funext τ
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, inner_zero_left]
  rw [heq]
  have hc : Continuous (Function.uncurry fun (τ : ℝ) (y : Space) => inner ℝ (g y) (G τ y)) :=
    (hg.comp continuous_snd).inner hGc
  exact continuous_parametric_integral_of_continuous hc hgc

/-- **Weak continuity.** For a jointly continuous uniformly smooth `L⁴` slice family `G` and
`f ∈ L^{4/3}`, `τ ↦ ∫ ⟪f, G τ⟫` is continuous. -/
theorem continuous_integral_inner_Lp {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) (hGc : Continuous (fun x : ℝ × Space => G x.1 x.2))
    (f : Lp Space (conjExp 4) (volume : Measure Space)) :
    Continuous fun τ => ∫ y, inner ℝ (f y) (G τ y) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_toLp_le hG
  obtain ⟨C, hC0, hCb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Lp Space (conjExp 4) (volume : Measure Space))
      (w : Lp Space 4 (volume : Measure Space)),
      ‖innerPairing (conjExp 4) 4 u w‖ ≤ C * ‖u‖ * ‖w‖ :=
    ⟨‖innerPairing (conjExp 4) 4‖, ContinuousLinearMap.opNorm_nonneg _, fun u w => ContinuousLinearMap.le_opNorm₂ _ _ _⟩
  have hpair : ∀ (u : Lp Space (conjExp 4) (volume : Measure Space)) (τ : ℝ),
      ∫ y, inner ℝ (u y) (G τ y) = innerPairing (conjExp 4) 4 u ((memLp_slice hG τ).toLp (G τ)) := by
    intro u τ
    rw [innerPairing_apply]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_slice hG τ).coeFn_toLp] with y hy
    rw [hy]
  refine continuous_of_forall_approx fun ε hε => ?_
  set δ : ℝ := ε / (C * M + 1) with hδ
  have hden : 0 < C * M + 1 := by positivity
  have hδ0 : 0 < δ := div_pos hε hden
  have hp : conjExp 4 ≠ ⊤ := conjExp_ne_top (by norm_num)
  obtain ⟨g, hgc, hfg, hgcont, hgm⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal δ) (by simpa using hδ0)
  refine ⟨fun τ => ∫ y, inner ℝ (g y) (G τ y),
    continuous_integral_inner_of_compact hgcont hgc hGc, fun τ => ?_⟩
  have hg' : (fun τ => ∫ y, inner ℝ (g y) (G τ y)) τ =
      innerPairing (conjExp 4) 4 (hgm.toLp g) ((memLp_slice hG τ).toLp (G τ)) := by
    rw [← hpair]
    refine integral_congr_ae ?_
    filter_upwards [hgm.coeFn_toLp] with y hy
    rw [hy]
  rw [hg', hpair, dist_eq_norm, ← ContinuousLinearMap.sub_apply, ← map_sub]
  have hnorm : ‖f - hgm.toLp g‖ ≤ δ := by
    rw [Lp.norm_def]
    have heq : eLpNorm (⇑(f - hgm.toLp g)) (conjExp 4) volume =
        eLpNorm (⇑f - g) (conjExp 4) volume := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub f (hgm.toLp g), hgm.coeFn_toLp] with y h1 h2
      rw [h1, Pi.sub_apply, h2, Pi.sub_apply]
    rw [heq]
    exact ENNReal.toReal_le_of_le_ofReal hδ0.le hfg
  calc ‖innerPairing (conjExp 4) 4 (f - hgm.toLp g) ((memLp_slice hG τ).toLp (G τ))‖
      ≤ C * ‖f - hgm.toLp g‖ * ‖(memLp_slice hG τ).toLp (G τ)‖ := hCb _ _
    _ ≤ C * δ * M := by
        gcongr
        · exact hM τ
    _ = ε * (C * M / (C * M + 1)) := by
        rw [hδ]
        field_simp
    _ ≤ ε * 1 := by
        gcongr
        rw [div_le_one hden]
        linarith
    _ = ε := mul_one ε

/-! ## 4. Joint continuity of the smooth Leray slice -/

/-- The smooth Leray slice of a uniformly smooth `L⁴` family is Lipschitz in space, uniformly in
the phase. -/
theorem exists_lipschitz_smoothLeraySlice {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) :
    ∃ K : ℝ≥0, ∀ τ, LipschitzWith K (smoothLeraySlice G τ) := by
  have hH : IsUniformSmoothL4SliceFamily (smoothLeraySlice G) :=
    (SmoothLeraySliceSub.sliceFamily_smoothLeraySlice_of_repExists smoothLerayRepExists_proof
      G hG).2
  obtain ⟨M, hM⟩ := hH.iteratedFDeriv_bounded 1
  refine ⟨M.toNNReal, fun τ => ?_⟩
  have hd : Differentiable ℝ (smoothLeraySlice G τ) :=
    (HigherPhaseSub.sliceFamily_contDiff_infty hH τ).differentiable (by simp)
  refine lipschitzWith_of_nnnorm_fderiv_le hd fun y => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal', ← norm_iteratedFDeriv_one]
  exact (hM τ y).trans (le_max_left _ _)

/-- The mollified value `∫ ρ ⟪v, H τ⟫` is continuous in the phase. -/
theorem continuous_integral_bump_inner {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) (hGc : Continuous (fun x : ℝ × Space => G x.1 x.2))
    {ρ : Space → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (v : Space) :
    Continuous fun τ => ∫ y, inner ℝ (ρ y • v) (smoothLeraySlice G τ y) := by
  have h1 : (1 : ℝ≥0∞) < 4 := by norm_num
  have h4 : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hp1 : 1 < conjExp 4 := one_lt_of_holderConjugate (p := (4 : ℝ≥0∞)) (q := conjExp 4) h4
  have hp : conjExp 4 ≠ ⊤ := conjExp_ne_top h1
  have hφc : Continuous fun y => ρ y • v := hρ.smul continuous_const
  have hφcs : HasCompactSupport fun y => ρ y • v := hρc.smul_right
  have hφ : MemLp (fun y => ρ y • v) (conjExp 4) volume := hφc.memLp_of_hasCompactSupport hφcs
  set f : Lp Space (conjExp 4) (volume : Measure Space) := lerayLp (conjExp 4) hp1 hp (hφ.toLp _)
    with hf
  have heq : (fun τ => ∫ y, inner ℝ (ρ y • v) (smoothLeraySlice G τ y)) =
      fun τ => ∫ y, inner ℝ (f y) (G τ y) := by
    funext τ
    obtain ⟨hMemG, -, hae⟩ :=
      (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp smoothLerayRepExists_proof hG τ).1
    have hsym := integral_inner_lerayLp_symm hp1 hp h1 h4 (hφ.toLp _) (hMemG.toLp (G τ))
    calc ∫ y, inner ℝ (ρ y • v) (smoothLeraySlice G τ y)
        = ∫ y, inner ℝ ((hφ.toLp (fun y => ρ y • v) : Space → Space) y)
            (lerayLp 4 h1 h4 (hMemG.toLp (G τ)) y) := by
          refine integral_congr_ae ?_
          filter_upwards [hae, hφ.coeFn_toLp] with y hy hy'
          rw [hy, hy']
      _ = ∫ y, inner ℝ (f y) ((hMemG.toLp (G τ) : Space → Space) y) := hsym.symm
      _ = ∫ y, inner ℝ (f y) (G τ y) := by
          refine integral_congr_ae ?_
          filter_upwards [hMemG.coeFn_toLp] with y hy
          rw [hy]
  rw [heq]
  exact continuous_integral_inner_Lp hG hGc f

/-- For fixed `y₀`, `τ ↦ ⟪v, H τ y₀⟫` is continuous. -/
theorem continuous_inner_smoothLeraySlice_apply {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) (hGc : Continuous (fun x : ℝ × Space => G x.1 x.2))
    (v y₀ : Space) :
    Continuous fun τ => inner ℝ v (smoothLeraySlice G τ y₀) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_smoothLeraySlice hG
  refine continuous_of_forall_approx fun ε hε => ?_
  set r : ℝ := ε / ((‖v‖ + 1) * ((K : ℝ) + 1)) with hr
  have hden : 0 < (‖v‖ + 1) * ((K : ℝ) + 1) := by positivity
  have hr0 : 0 < r := div_pos hε hden
  let b : ContDiffBump y₀ := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩
  set ρ : Space → ℝ := b.normed volume with hρ
  refine ⟨fun τ => ∫ y, inner ℝ (ρ y • v) (smoothLeraySlice G τ y),
    continuous_integral_bump_inner hG hGc b.continuous_normed b.hasCompactSupport_normed v,
    fun τ => ?_⟩
  have hint1 : Integrable fun y => ρ y * inner ℝ v (smoothLeraySlice G τ y₀) :=
    b.integrable_normed.mul_const _
  have hcontH : Continuous (smoothLeraySlice G τ) := (hK τ).continuous
  have hint2 : Integrable fun y => inner ℝ (ρ y • v) (smoothLeraySlice G τ y) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((b.continuous_normed.smul continuous_const).inner hcontH) ?_
    refine (b.hasCompactSupport_normed (μ := volume)).mono' ?_
    intro y hy
    apply subset_tsupport
    intro hρy
    apply hy
    change inner ℝ (b.normed volume y • v) (smoothLeraySlice G τ y) = 0
    rw [hρy, zero_smul, inner_zero_left]
  have hval : inner ℝ v (smoothLeraySlice G τ y₀) =
      ∫ y, ρ y * inner ℝ v (smoothLeraySlice G τ y₀) := by
    rw [integral_mul_const, b.integral_normed, one_mul]
  rw [hval, dist_eq_norm, ← integral_sub hint1 hint2]
  have hbound : ∀ y, ‖ρ y * inner ℝ v (smoothLeraySlice G τ y₀) -
      inner ℝ (ρ y • v) (smoothLeraySlice G τ y)‖ ≤ ρ y * (‖v‖ * ((K : ℝ) * r)) := by
    intro y
    have hρ0 : 0 ≤ ρ y := b.nonneg_normed y
    rw [real_inner_smul_left, ← mul_sub, ← inner_sub_right, norm_mul, Real.norm_of_nonneg hρ0]
    by_cases hy : y ∈ Metric.ball y₀ r
    · refine mul_le_mul_of_nonneg_left ?_ hρ0
      refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      have hlip := (hK τ).dist_le_mul y₀ y
      have hy' : dist y₀ y < r := by rw [dist_comm]; exact Metric.mem_ball.1 hy
      calc ‖smoothLeraySlice G τ y₀ - smoothLeraySlice G τ y‖
          = dist (smoothLeraySlice G τ y₀) (smoothLeraySlice G τ y) := (dist_eq_norm _ _).symm
        _ ≤ (K : ℝ) * dist y₀ y := hlip
        _ ≤ (K : ℝ) * r := mul_le_mul_of_nonneg_left hy'.le K.2
    · have hρy : ρ y = 0 := by
        rw [← Function.notMem_support, hρ, b.support_normed_eq]
        exact hy
      simp [hρy]
  calc ‖∫ y, (ρ y * inner ℝ v (smoothLeraySlice G τ y₀) -
        inner ℝ (ρ y • v) (smoothLeraySlice G τ y))‖
      ≤ ∫ y, ρ y * (‖v‖ * ((K : ℝ) * r)) :=
        norm_integral_le_of_norm_le (b.integrable_normed.mul_const _)
          (Eventually.of_forall hbound)
    _ = ‖v‖ * ((K : ℝ) * r) := by rw [integral_mul_const, b.integral_normed, one_mul]
    _ ≤ ε := by
        have : ‖v‖ * ((K : ℝ) * r) = ε * (‖v‖ * (K : ℝ) / ((‖v‖ + 1) * ((K : ℝ) + 1))) := by
          rw [hr]; field_simp
        rw [this]
        have hle : ‖v‖ * (K : ℝ) / ((‖v‖ + 1) * ((K : ℝ) + 1)) ≤ 1 := by
          rw [div_le_one hden]
          have h1 : ‖v‖ ≤ ‖v‖ + 1 := by linarith
          have h2 : (K : ℝ) ≤ (K : ℝ) + 1 := by linarith
          exact mul_le_mul h1 h2 K.2 (by positivity)
        calc ε * (‖v‖ * (K : ℝ) / ((‖v‖ + 1) * ((K : ℝ) + 1))) ≤ ε * 1 :=
              mul_le_mul_of_nonneg_left hle hε.le
          _ = ε := mul_one ε

/-- For fixed `y₀`, `τ ↦ H τ y₀` is continuous. -/
theorem continuous_smoothLeraySlice_apply {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) (hGc : Continuous (fun x : ℝ × Space => G x.1 x.2))
    (y₀ : Space) :
    Continuous fun τ => smoothLeraySlice G τ y₀ := by
  have hfun : (fun τ => smoothLeraySlice G τ y₀) = fun τ =>
      ∑ i : Fin 3, inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i) (smoothLeraySlice G τ y₀) •
        EuclideanSpace.basisFun (Fin 3) ℝ i := by
    funext τ
    rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (smoothLeraySlice G τ y₀)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OrthonormalBasis.repr_apply_apply]
    rw [(EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (smoothLeraySlice G τ y₀)]
  rw [hfun]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_inner_smoothLeraySlice_apply hG hGc _ y₀).smul continuous_const

/-- **Joint continuity of the smooth Leray slice.** -/
theorem continuous_smoothLeraySlice {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) (hGc : Continuous (fun x : ℝ × Space => G x.1 x.2)) :
    Continuous fun x : ℝ × Space => smoothLeraySlice G x.1 x.2 := by
  obtain ⟨K, hK⟩ := exists_lipschitz_smoothLeraySlice hG
  exact continuous_prod_of_continuous_lipschitzWith' (fun x : ℝ × Space => smoothLeraySlice G x.1 x.2)
    K (fun τ => hK τ) (fun y => continuous_smoothLeraySlice_apply hG hGc y)

/-! ## 5. Joint continuity of jets: products -/

/-- All spatial jets of `V` are jointly continuous. -/
def JetCont (V : ℝ → SpatialField) : Prop :=
  ∀ ws : List Space, Continuous fun x : ℝ × Space => dirSpatialJet (V x.1) ws x.2

theorem jetCont_dirSpatialJet {V : ℝ → SpatialField} (hV : JetCont V) (vs : List Space) :
    JetCont fun τ => dirSpatialJet (V τ) vs := by
  intro ws
  have hfun : (fun x : ℝ × Space => dirSpatialJet (dirSpatialJet (V x.1) vs) ws x.2) =
      fun x => dirSpatialJet (V x.1) (ws ++ vs) x.2 := by
    funext x
    rw [HigherPhaseSub.dirSpatialJet_append]
  rw [hfun]
  exact hV _

theorem dirSpatialJet_coord_smul_singleton' (j : Fin 3) {F H : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (w : Space) :
    dirSpatialJet (fun y => (F y j) • H y) [w] =
      (fun y => (dirSpatialJet F [w] y j) • H y) +
        (fun y => (F y j) • dirSpatialJet H [w] y) := by
  funext y
  change fderiv ℝ (fun y' : Space => ((EuclideanSpace.proj j : Space →L[ℝ] ℝ) (F y')) • H y') y w =
    (fderiv ℝ F y w j) • H y + (F y j) • fderiv ℝ H y w
  have hdF : HasFDerivAt F (fderiv ℝ F y) y :=
    (hF.differentiable (by simp) y).hasFDerivAt
  have hdFj : HasFDerivAt (fun y' : Space => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (F y'))
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ F y)) y :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y hdF
  have hdH : HasFDerivAt H (fderiv ℝ H y) y :=
    (hH.differentiable (by simp) y).hasFDerivAt
  have hdf := (hdFj.smul hdH).fderiv
  change fderiv ℝ ((fun y' : Space => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (F y')) • H) y w = _
  rw [hdf]
  simp [add_comm]

theorem contDiff_infty_coord_smul' (j : Fin 3) {F H : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun y : Space => (F y j) • H y) :=
  ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hF).smul hH

theorem jetCont_coord_smul (j : Fin 3) {V H : ℝ → SpatialField}
    (hV : ∀ τ, ContDiff ℝ ∞ (V τ)) (hH : ∀ τ, ContDiff ℝ ∞ (H τ))
    (cV : JetCont V) (cH : JetCont H) :
    JetCont fun τ y => (V τ y j) • H τ y := by
  intro ws
  induction ws using List.reverseRecOn generalizing V H with
  | nil =>
      simp only [dirSpatialJet_nil]
      have h1 : Continuous fun x : ℝ × Space => V x.1 x.2 := cV []
      have h2 : Continuous fun x : ℝ × Space => H x.1 x.2 := cH []
      exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp h1).smul h2
  | append_singleton ws w ih =>
      have hfun : (fun x : ℝ × Space =>
          dirSpatialJet (fun y => (V x.1 y j) • H x.1 y) (ws ++ [w]) x.2) =
          fun x => dirSpatialJet (fun y => (dirSpatialJet (V x.1) [w] y j) • H x.1 y) ws x.2 +
            dirSpatialJet (fun y => (V x.1 y j) • dirSpatialJet (H x.1) [w] y) ws x.2 := by
        funext x
        rw [← HigherPhaseSub.dirSpatialJet_append,
          dirSpatialJet_coord_smul_singleton' j (hV x.1) (hH x.1) w,
          HigherPhaseSub.dirSpatialJet_add
            (contDiff_infty_coord_smul' j
              (JointSmoothSub.contDiff_infty_dirSpatialJet (hV x.1) [w]) (hH x.1))
            (contDiff_infty_coord_smul' j
              (hV x.1) (JointSmoothSub.contDiff_infty_dirSpatialJet (hH x.1) [w])) ws]
        rfl
      rw [hfun]
      exact (ih (fun τ => JointSmoothSub.contDiff_infty_dirSpatialJet (hV τ) [w]) hH
        (jetCont_dirSpatialJet cV [w]) cH).add
        (ih hV (fun τ => JointSmoothSub.contDiff_infty_dirSpatialJet (hH τ) [w]) cV
          (jetCont_dirSpatialJet cH [w]))

theorem jetCont_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → SpatialField}
    (hF : ∀ i ∈ s, ∀ τ, ContDiff ℝ ∞ (F i τ)) (cF : ∀ i ∈ s, JetCont (F i)) :
    JetCont fun τ y => ∑ i ∈ s, F i τ y := by
  intro ws
  have hfun : (fun x : ℝ × Space => dirSpatialJet (fun y => ∑ i ∈ s, F i x.1 y) ws x.2) =
      fun x => ∑ i ∈ s, dirSpatialJet (F i x.1) ws x.2 := by
    funext x
    rw [HigherPhaseSub.dirSpatialJet_sum s (F := fun i => F i x.1) (fun i hi => hF i hi x.1) ws]
  rw [hfun]
  exact continuous_finsetSum _ fun i hi => cF i hi ws

theorem jetCont_spatialConvect {V W : ℝ → SpatialField}
    (hV : ∀ τ, ContDiff ℝ ∞ (V τ)) (hW : ∀ τ, ContDiff ℝ ∞ (W τ))
    (cV : JetCont V) (cW : JetCont W) :
    JetCont fun τ => spatialConvect (V τ) (W τ) := by
  have hfun : (fun τ => spatialConvect (V τ) (W τ)) =
      fun τ y => ∑ j : Fin 3, (V τ y j) • spatialPartial j (W τ) y := by
    funext τ y
    exact HigherPhaseSub.spatialConvect_eq_sum (V τ) (W τ) y
  rw [hfun]
  refine jetCont_sum Finset.univ
    (F := fun j τ y => (V τ y j) • spatialPartial j (W τ) y)
    (fun j _ τ => contDiff_infty_coord_smul' j (hV τ)
      (JointSmoothSub.contDiff_infty_dirSpatialJet (hW τ) [EuclideanSpace.single j 1]))
    (fun j _ => ?_)
  exact jetCont_coord_smul j hV
    (fun τ => JointSmoothSub.contDiff_infty_dirSpatialJet (hW τ) [EuclideanSpace.single j 1])
    cV (jetCont_dirSpatialJet cW [EuclideanSpace.single j 1])

/-! ## 6. Joint continuity of the jets of `U = bgField p z` -/

local instance fact_q0_ge_one_lc' : Fact (1 ≤ q0E) := inferInstance

theorem jetCont_bgField (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (hRawCD : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    (hInCD : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2))
    (hGraph : ∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
      IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) :
    JetCont (bgField p z) := by
  have hcorrS : ∀ τ, ContDiff ℝ ∞ (p.corr z τ) :=
    CoordDerivSub.corr_slice_contDiff_infty_of_period_le_one p hP1 z hGraph
  have hrawS : ∀ τ, ContDiff ℝ ∞ (p.raw τ) := PhaseDerivStepSub.contDiff_slice_of_joint hRawCD
  have hinS : ∀ (i : Fin 2) τ, ContDiff ℝ ∞ (p.inlet i τ) := fun i =>
    PhaseDerivStepSub.contDiff_slice_of_joint (hInCD i)
  have hES : ∀ τ, ContDiff ℝ ∞ (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y) :=
    fun τ => ContDiff.sum fun i _ => (hinS i τ).const_smul (p.coord z i)
  have hcorrC : ∀ vs : List Space,
      Continuous (fun x : ℝ × Space => dirSpatialJet (p.corr z x.1) vs x.2) := by
    refine CorrComovingSub.continuous_dirSpatialJet_of_coordWord hcorrS fun k α => ?_
    obtain ⟨g, hg⟩ := hGraph k
    have hfun : (fun x : ℝ × Space =>
        dirSpatialJet (p.corr z x.1) (PhaseDerivStepSub.coordWord α) x.2) =
        fun x => contRep (g α : Yq p.period q0E) x.1 x.2 := by
      funext x
      exact CoordDerivSub.dirSpatialJet_contRep_coordWord_eq hP1 p.ν_pos hGraph k g hg x.1 α x.2
    rw [hfun]
    exact (CorrComovingSub.isContRep_contRep_D hP1 p.ν_pos (g α)).1
  have hEC : ∀ vs : List Space, Continuous (fun x : ℝ × Space =>
      dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) vs x.2) := by
    intro vs
    have hfun : (fun x : ℝ × Space =>
        dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) vs x.2) =
        fun x => ∑ i : Fin 2, p.coord z i • dirSpatialJet (p.inlet i x.1) vs x.2 := by
      funext x
      rw [congrFun (HigherPhaseSub.dirSpatialJet_sum Finset.univ
        (F := fun i y => p.coord z i • p.inlet i x.1 y)
        (fun i _ => (hinS i x.1).const_smul (p.coord z i)) vs) x.2]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact congrFun (HigherPhaseSub.dirSpatialJet_smul (p.coord z i) (hinS i x.1) vs) x.2
    rw [hfun]
    exact continuous_finsetSum _ fun i _ =>
      (CorrComovingSub.continuous_dirSpatialJet_of_joint (hInCD i) vs).const_smul (p.coord z i)
  intro vs
  have hfun : (fun x : ℝ × Space => dirSpatialJet (bgField p z x.1) vs x.2) =
      fun x => dirSpatialJet (p.raw x.1) vs x.2 +
        dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) vs x.2 +
        dirSpatialJet (p.corr z x.1) vs x.2 := by
    funext x
    have e : bgField p z x.1 =
        (p.raw x.1 + fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) + p.corr z x.1 := rfl
    have hA : ContDiff ℝ ∞ (p.raw x.1 + fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) :=
      (hrawS x.1).add (hES x.1)
    rw [e, HigherPhaseSub.dirSpatialJet_add hA (hcorrS x.1) vs,
      HigherPhaseSub.dirSpatialJet_add (hrawS x.1) (hES x.1) vs]
    rfl
  rw [hfun]
  exact ((CorrComovingSub.continuous_dirSpatialJet_of_joint hRawCD vs).add (hEC vs)).add (hcorrC vs)

end LerayContSub

open LerayContSub in
/-- **`PartII-b:S3/1/1/2/1/2/2` (`LerayJetContinuous`)** (SP 2552-2562): every spatial jet of
`𝔓(U·∇U) = smoothConvectiveLeray U U`, `U = bgField p z`, is jointly continuous on `ℝ × ℝ³`. -/
theorem lerayJetContinuous_proof : UnforcedLeray.Short.IIb.CorrComovingSub.LerayJetContinuous := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, hPer⟩ := exists_period_le_one_of_bgRegime (dp := dp) hdm
  refine ⟨ν₂, hν₂, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet ws
  have hP1 : p.period ≤ 1 := hPer p d hReg hν
  have hUS : ∀ τ, ContDiff ℝ ∞ (bgField p z τ) := HigherPhaseSub.sliceFamily_contDiff_infty hBg
  have hJ : JetCont (bgField p z) := jetCont_bgField p hP1 z hRawCD hInCD hGraph
  set G : ℝ → SpatialField := fun τ => dirSpatialJet (spatialConvect (bgField p z τ)
    (bgField p z τ)) ws with hGdef
  have hG : IsUniformSmoothL4SliceFamily G :=
    HigherPhaseSub.sliceFamily_dirSpatialJet (HigherPhaseSub.sliceFamily_spatialConvect hBg hBg) ws
  have hGc : Continuous fun x : ℝ × Space => G x.1 x.2 :=
    jetCont_spatialConvect hUS hUS hJ hJ ws
  have hfun : (fun x : ℝ × Space =>
      dirSpatialJet (smoothConvectiveLeray (bgField p z) (bgField p z) x.1) ws x.2) =
      fun x => smoothLeraySlice G x.1 x.2 := by
    funext x
    rw [CoordDerivSub.dirSpatialJet_smoothConvectiveLeray hBg hBg ws x.1]
    rfl
  rw [hfun]
  exact continuous_smoothLeraySlice hG hGc

end UnforcedLeray.Short.IIb

end
