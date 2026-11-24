import UnforcedLeray.Lib.CZL2.TestOffSupport

/-!
# The kernel formula for `R_iR_k` on L² off a compact support (INF01 level L0, target T4)

Blueprint: INF01 target T4 (scoping note `INF01-CZ.md` §4.2, §5, `rieszPairL2_offSupport`);
this is the `offSupport` field that the Calderón–Zygmund theorem T10/T13 asks of
`rieszPairL2`. Manuscript: `R_iR_k = ∂_i∂_k(-Δ)^{-1}` with kernel `K_ik = ∂_i∂_k N`
(`paper/main.tex` lines 107–111).

If `f ∈ L²` vanishes a.e. outside a compact set `S`, then for a.e. `x ∉ S`,
`(R_iR_k f)(x) = ∫ K_ik(x - y) f(y) dy`.

Proof (duality, no mollification): `rieszPairL2 k i` is the L² adjoint of
`rieszPairL2 i k` (`inner_rieszPairL2`, from the self-adjointness of `I - 𝔓`). For a
test `g` supported in `Sᶜ`, `R_ki g = ∂ₖ∂ᵢ(N ∗ g)`, which on `S` equals
`∫ K_ki(y - x) g(x) dx` (`rieszPairTest_offSupport`). Fubini, with the kernel bounded by
`π⁻¹δ⁻³` at distance `δ = dist(tsupport g, S) > 0`, gives
`∫ g · R_ik f = ∫ g(x) ∫ K_ik(x - y) f(y) dy dx`. Both sides are locally integrable on
the open set `Sᶜ`, so they agree a.e. there
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

/-- Disjoint compact sets are at positive distance. -/
theorem exists_pos_le_norm_sub_of_disjoint {A B : Set Space} (hA : IsCompact A)
    (hB : IsCompact B) (h : Disjoint A B) : ∃ δ > 0, ∀ x ∈ A, ∀ y ∈ B, δ ≤ ‖x - y‖ := by
  obtain ⟨δ, hδ, hsub⟩ := hB.exists_cthickening_subset_open hA.isClosed.isOpen_compl
    (fun y hyB hyA => Set.disjoint_left.mp h hyA hyB)
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have hxB : x ∈ cthickening δ B :=
    Metric.mem_cthickening_of_dist_le x y δ B hy (by rw [dist_eq_norm]; exact hlt.le)
  exact hsub hxB hx

/-- `eᵢ`-coordinate and `eᵢ`-embedding are adjoint. -/
theorem inner_coordL2 (G : ScalarL2) (F : L2Space) (i : Fin 3) :
    inner ℝ G (coordL2 i F) = inner ℝ (embedL2 i G) F := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_coordL2 i F, coeFn_embedL2 i G] with x h1 h2
  rw [h1, h2, Real.inner_apply, real_inner_smul_left, coordinateVector,
    EuclideanSpace.inner_single_left]
  simp

/-- `I - 𝔓` is self-adjoint. -/
theorem inner_complementL2 (F F' : L2Space) :
    inner ℝ (complementL2 F) F' = inner ℝ F (complementL2 F') := by
  rw [complementL2_apply, complementL2_apply, inner_sub_left, inner_sub_right,
    Leray.projection_selfadjoint]

/-- The adjoint of `R_iR_k` on L² is `R_kR_i`. -/
theorem inner_rieszPairL2 (i k : Fin 3) (G f : ScalarL2) :
    inner ℝ G (rieszPairL2 i k f) = inner ℝ (rieszPairL2 k i G) f := by
  have h1 : inner ℝ G (coordL2 i (complementL2 (embedL2 k f))) =
      inner ℝ (complementL2 (embedL2 i G)) (embedL2 k f) := by
    rw [inner_coordL2]
    exact (inner_complementL2 _ _).symm
  have h2 : inner ℝ (coordL2 k (complementL2 (embedL2 i G))) f =
      inner ℝ (complementL2 (embedL2 i G)) (embedL2 k f) := by
    rw [real_inner_comm, inner_coordL2, real_inner_comm]
  simp only [rieszPairL2, neg_apply, ContinuousLinearMap.comp_apply, inner_neg_left,
    inner_neg_right]
  rw [h1, h2]

/-- The kernel integral `x ↦ ∫ K_ik(x - y) φ(y) dy` is strongly measurable. -/
theorem stronglyMeasurable_kernelIntegral (i k : Fin 3) {φ : Space → ℝ}
    (hφ : StronglyMeasurable φ) :
    StronglyMeasurable (fun x => ∫ y, newtonHessianKernel i k (x - y) * φ y) := by
  have h : StronglyMeasurable
      (fun p : Space × Space => newtonHessianKernel i k (p.1 - p.2) * φ p.2) :=
    ((newtonHessianKernel_measurable i k).comp
      (measurable_fst.sub measurable_snd)).stronglyMeasurable.mul
      (hφ.comp_measurable measurable_snd)
  exact h.integral_prod_right'

/-- Pointwise bound of the kernel integral at distance `δ` from the support. -/
theorem abs_kernelIntegral_le (i k : Fin 3) {φ : Space → ℝ} (hφ : Integrable φ volume)
    {δ : ℝ} (hδ : 0 < δ) {x : Space} (hx : ∀ y, φ y ≠ 0 → δ ≤ ‖x - y‖) :
    ‖∫ y, newtonHessianKernel i k (x - y) * φ y‖ ≤
      Real.pi⁻¹ * (δ ^ 3)⁻¹ * ∫ y, |φ y| := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hφ.abs.const_mul _) (Eventually.of_forall fun y => ?_)
  by_cases hy : φ y = 0
  · simp [hy]
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_newtonHessianKernel_le_of_le i k hδ (hx y hy))
      (abs_nonneg _)

/-- **INF01 T4 (off-support kernel formula).** If `f ∈ L²` vanishes a.e. outside a compact
set `S`, then for a.e. `x ∉ S`, `(R_iR_k f)(x) = ∫ K_ik(x - y) f(y) dy`. -/
theorem rieszPairL2_offSupport (i k : Fin 3) (f : ScalarL2) {S : Set Space}
    (hS : IsCompact S) (hf : ∀ᵐ y ∂volume, y ∉ S → f y = 0) :
    ∀ᵐ x ∂volume, x ∉ S →
      rieszPairL2 i k f x = ∫ y, newtonHessianKernel i k (x - y) * f y := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  set f' : Space → ℝ := S.indicator (fun y => f y) with hf'def
  have hff' : (fun y => f y) =ᵐ[volume] f' := by
    filter_upwards [hf] with y hy
    by_cases hyS : y ∈ S
    · rw [hf'def, indicator_of_mem hyS]
    · rw [hf'def, indicator_of_notMem hyS, hy hyS]
  have hf'S : ∀ y, f' y ≠ 0 → y ∈ S := fun y hy => Set.mem_of_indicator_ne_zero hy
  have hf'i : Integrable f' volume := by
    rw [hf'def, integrable_indicator_iff hSm]
    exact ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hS
  have hf'm : StronglyMeasurable f' := (Lp.stronglyMeasurable f).indicator hSm
  set Kf : Space → ℝ := fun x => ∫ y, newtonHessianKernel i k (x - y) * f' y with hKf
  have hKfeq : ∀ x, (∫ y, newtonHessianKernel i k (x - y) * f y) = Kf x := fun x =>
    integral_congr_ae (by filter_upwards [hff'] with y hy; beta_reduce at hy ⊢; rw [hy])
  have hKfm : StronglyMeasurable Kf := stronglyMeasurable_kernelIntegral i k hf'm
  -- local integrability of `Kf` on `Sᶜ`
  have hKfloc : LocallyIntegrableOn Kf Sᶜ volume := by
    rw [locallyIntegrableOn_iff hS.isClosed.isOpen_compl.isLocallyClosed]
    intro C hCU hC
    obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_of_disjoint hC hS
      (Set.subset_compl_iff_disjoint_right.mp hCU)
    refine Measure.integrableOn_of_bounded hC.measure_lt_top.ne hKfm.aestronglyMeasurable
      (M := Real.pi⁻¹ * (δ ^ 3)⁻¹ * ∫ y, |f' y|) ?_
    rw [ae_restrict_iff' hC.measurableSet]
    exact Eventually.of_forall fun x hx =>
      abs_kernelIntegral_le i k hf'i hδ fun y hy => hsep x hx y (hf'S y hy)
  -- the duality identity against tests supported in `Sᶜ`
  have key : ∀ g : Space → ℝ, IsSpatialTest g → tsupport g ⊆ Sᶜ →
      Integrable (fun x => g x * Kf x) volume ∧
        ∫ x, g x * rieszPairL2 i k f x = ∫ x, g x * Kf x := by
    intro g hg hgS
    obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_of_disjoint hg.compact hS
      (Set.subset_compl_iff_disjoint_right.mp hgS)
    have hgi : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hg.compact
    -- Fubini integrand
    have hFm : StronglyMeasurable
        (fun p : Space × Space => newtonHessianKernel i k (p.1 - p.2) * g p.1 * f' p.2) :=
      (((newtonHessianKernel_measurable i k).comp
        (measurable_fst.sub measurable_snd)).stronglyMeasurable.mul
        (hg.continuous.comp continuous_fst).stronglyMeasurable).mul
        (hf'm.comp_measurable measurable_snd)
    have hint : Integrable (Function.uncurry fun x y =>
        newtonHessianKernel i k (x - y) * g x * f' y) (volume.prod volume) := by
      refine (((hgi.mul_prod hf'i).norm).const_mul (Real.pi⁻¹ * (δ ^ 3)⁻¹)).mono'
        hFm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      change ‖newtonHessianKernel i k (p.1 - p.2) * g p.1 * f' p.2‖ ≤
        Real.pi⁻¹ * (δ ^ 3)⁻¹ * ‖g p.1 * f' p.2‖
      by_cases h0 : g p.1 * f' p.2 = 0
      · rw [mul_assoc, h0, mul_zero, norm_zero, mul_zero]
      · have hg0 : g p.1 ≠ 0 := left_ne_zero_of_mul h0
        have hf0 : f' p.2 ≠ 0 := right_ne_zero_of_mul h0
        rw [mul_assoc, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (abs_newtonHessianKernel_le_of_le i k hδ
            (hsep p.1 (subset_tsupport g hg0) p.2 (hf'S p.2 hf0))) (norm_nonneg _)
    have hrow : ∀ x, ∫ y, newtonHessianKernel i k (x - y) * g x * f' y = g x * Kf x := by
      intro x
      rw [hKf, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      beta_reduce
      ring
    have hgK : Integrable (fun x => g x * Kf x) volume := by
      have := hint.integral_prod_left
      refine this.congr (Eventually.of_forall fun x => ?_)
      exact hrow x
    refine ⟨hgK, ?_⟩
    set G : ScalarL2 := (hg.memLp 2).toLp g with hGdef
    have hL : ∫ x, g x * rieszPairL2 i k f x = inner ℝ G (rieszPairL2 i k f) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(hg.memLp 2).coeFn_toLp] with x hx
      rw [hx, Real.inner_apply]
    have hB : inner ℝ (rieszPairL2 k i G) f = ∫ y, rieszPairTest k i g y * f' y := by
      rw [hGdef, rieszPairL2_toLp hg k i, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_rieszPairTest hg k i).coeFn_toLp, hff'] with y h1 h2
      beta_reduce at h2
      rw [h1, Real.inner_apply, h2]
    have hC : ∀ y, rieszPairTest k i g y * f' y =
        (∫ x, newtonHessianKernel i k (x - y) * g x) * f' y := by
      intro y
      by_cases hy : f' y = 0
      · simp [hy]
      · have hyg : y ∉ tsupport g := fun h => hgS h (hf'S y hy)
        rw [rieszPairTest_offSupport hg k i hyg]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        beta_reduce
        rw [newtonHessianKernel_symm k i, show y - x = -(x - y) by abel,
          newtonHessianKernel_neg]
    calc ∫ x, g x * rieszPairL2 i k f x
        = inner ℝ (rieszPairL2 k i G) f := by rw [hL, inner_rieszPairL2]
      _ = ∫ y, (∫ x, newtonHessianKernel i k (x - y) * g x) * f' y := by
          rw [hB]
          exact integral_congr_ae (Eventually.of_forall hC)
      _ = ∫ y, ∫ x, newtonHessianKernel i k (x - y) * g x * f' y := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [integral_mul_const]
      _ = ∫ x, ∫ y, newtonHessianKernel i k (x - y) * g x * f' y :=
          (integral_integral_swap hint).symm
      _ = ∫ x, g x * Kf x := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          exact hrow x
  -- conclude on the open set `Sᶜ`
  have hRloc : LocallyIntegrable (rieszPairL2 i k f) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hloc : LocallyIntegrableOn (fun x => rieszPairL2 i k f x - Kf x) Sᶜ volume :=
    (hRloc.locallyIntegrableOn _).sub hKfloc
  have hzero := hS.isClosed.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hgd hgc hgS => by
      obtain ⟨hgK, hid⟩ := key g ⟨hgd, hgc⟩ hgS
      have hgR : Integrable (fun x => g x * rieszPairL2 i k f x) volume :=
        memLp_one_iff_integrable.mp ((Lp.memLp (rieszPairL2 i k f)).mul' ((⟨hgd, hgc⟩ : IsSpatialTest g).memLp 2))
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub hgR hgK, hid, sub_self])
  filter_upwards [hzero] with x hx hxS
  rw [hKfeq]
  exact sub_eq_zero.mp (hx hxS)

end UnforcedLeray.RieszLp
