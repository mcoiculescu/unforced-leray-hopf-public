import UnforcedLeray.Lib.Parabolic.Adjoint
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Order.CompletePartialOrder

/-!
# The kernel representation of `∂_i∂_j (∂_t - νΔ)^{-1}` off the support (INF02 T6)


step 3 ("prove the kernel representation `T f(X) = ∫K(X−Y)f(Y)dY` for `X` off `supp f`, where
`K = 1_{t>0}∂_{ij}G_t`"), §5 target T6. Manuscript: eq:free-stress-11
(`paper/main.tex` lines 7447–7477, blueprint unit B0423), kernel at line 7466.

* `causalKernelNu ν i j (t, x) = 1_{t>0} ∂_i∂_j G_{νt}(x)` (`causalKernel` at time `νt`).
* `abs_causalKernelNu_le_of_le`: the kernel is bounded on `{‖Z‖ ≥ δ}`.
* `backTest_offSupport`: for a test `g` and `Y ∉ tsupport g`,
  `backTest ν i j g (Y) = ∫ K_ν(X - Y) g(X) dX` (two spatial integrations by parts on each
  time slice).
* `secondDerivOp_offSupport` (**INF02 T6, off-support representation**): if `F ∈ L²`
  vanishes a.e. outside a compact `S`, then for a.e. `X ∉ S`,
  `(secondDerivOp ν i j F)(X) = ∫ K_ν(X - Y) F(Y) dY`. Proof by duality with `backOp`, as in
  `Lib/CZL2/L2OffSupport.lean` (INF01 T4).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter Metric
open scoped ENNReal NNReal ContDiff Topology RealInnerProductSpace

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

/-- The causal kernel at viscosity `ν`: `K_ν(t, x) = 1_{t>0} ∂_i∂_j G_{νt}(x)`. -/
def causalKernelNu (ν : ℝ) (i j : Fin d) (X : PS d) : ℝ := causalKernel i j (ν * X.1, X.2)

theorem causalKernelNu_one (i j : Fin d) : causalKernelNu 1 i j = causalKernel i j := by
  funext X; simp [causalKernelNu]

theorem measurable_causalKernelNu (ν : ℝ) (i j : Fin d) : Measurable (causalKernelNu ν i j) :=
  (measurable_causalKernel i j).comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)

theorem causalKernelNu_of_pos {ν : ℝ} (hν : 0 < ν) (i j : Fin d) {X : PS d} (h : 0 < X.1) :
    causalKernelNu ν i j X = hessG i j (ν * X.1) X.2 :=
  causalKernel_of_pos i j (X := (ν * X.1, X.2)) (mul_pos hν h)

theorem causalKernelNu_of_nonpos {ν : ℝ} (hν : 0 < ν) (i j : Fin d) {X : PS d} (h : X.1 ≤ 0) :
    causalKernelNu ν i j X = 0 :=
  causalKernel_of_nonpos i j (X := (ν * X.1, X.2)) (mul_nonpos_of_nonneg_of_nonpos hν.le h)

/-- The kernel is bounded away from the origin. -/
theorem abs_causalKernelNu_le_of_le {ν : ℝ} (hν : 0 < ν) (i j : Fin d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z : PS d, δ ≤ ‖Z‖ → |causalKernelNu ν i j Z| ≤ C := by
  obtain ⟨C, hC, h⟩ := abs_hessG_le (d := d) i j
  set m := min (ν * δ) (δ ^ 2) with hm
  have hm0 : 0 < m := lt_min (mul_pos hν hδ) (by positivity)
  refine ⟨C * m ^ (-(((d : ℝ) + 2) / 2)), by positivity, fun Z hZ => ?_⟩
  rcases le_or_gt Z.1 0 with ht | ht
  · rw [causalKernelNu_of_nonpos hν i j ht, abs_zero]; positivity
  rw [causalKernelNu_of_pos hν i j ht]
  refine (h (mul_pos hν ht) Z.2).trans ?_
  have hle : m ≤ ν * Z.1 + ‖Z.2‖ ^ 2 := by
    rw [Prod.norm_def] at hZ
    rcases le_max_iff.1 hZ with h1 | h1
    · rw [Real.norm_eq_abs, abs_of_pos ht] at h1
      have : ν * δ ≤ ν * Z.1 := mul_le_mul_of_nonneg_left h1 hν.le
      linarith [min_le_left (ν * δ) (δ ^ 2), sq_nonneg ‖Z.2‖]
    · have : δ ^ 2 ≤ ‖Z.2‖ ^ 2 := pow_le_pow_left₀ hδ.le h1 2
      linarith [min_le_right (ν * δ) (δ ^ 2), mul_pos hν ht]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm0 hle (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)) hC.le

/-- Disjoint compact sets are at positive distance. -/
theorem exists_pos_le_norm_sub_of_disjoint' {A B : Set (PS d)} (hA : IsCompact A)
    (hB : IsCompact B) (h : Disjoint A B) : ∃ δ > 0, ∀ x ∈ A, ∀ y ∈ B, δ ≤ ‖x - y‖ := by
  obtain ⟨δ, hδ, hsub⟩ := hB.exists_cthickening_subset_open hA.isClosed.isOpen_compl
    (fun y hyB hyA => Set.disjoint_left.mp h hyA hyB)
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have hxB : x ∈ cthickening δ B :=
    Metric.mem_cthickening_of_dist_le x y δ B hy (by rw [dist_eq_norm]; exact hlt.le)
  exact hsub hxB hx

section SliceIBP

/-- Integration by parts on `ℝ^d` with one compactly supported factor. -/
theorem integral_mul_fderiv_euc {f g : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : Euc d) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have hfd : Continuous fun x => fderiv ℝ f x v :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgd : Continuous fun x => fderiv ℝ g x v :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)
  · exact (hfd.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  · exact (hf.continuous.mul hgd).integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ v).mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left

theorem fderiv_fderiv_apply_eq {G : Euc d → ℝ} (hG : ContDiff ℝ 2 G) (x u v : Euc d) :
    fderiv ℝ (fun y => fderiv ℝ G y u) x v = fderiv ℝ (fderiv ℝ G) x v u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- `∂_i∂_j G_τ = ∂_j (∂_i G_τ)` in `fderiv` form. -/
theorem hessG_eq_fderiv (τ : ℝ) (i j : Fin d) (w : Euc d) :
    hessG i j τ w = fderiv ℝ (fun y => fderiv ℝ (gaussKernel d τ) y (ev i)) w (ev j) := by
  have hG : ContDiff ℝ ∞ (gaussKernel d τ) := Gaussian.contDiff_gaussKernel τ
  rw [fderiv_fderiv_apply_eq (hG.of_le (by simp)), hessG, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact (hG.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- **Two integrations by parts on a time slice.** For a `C_c^∞` `φ`,
`∫ G_τ(w) ∂_i∂_j φ(y + w) dw = ∫ ∂_i∂_j G_τ(w) φ(y + w) dw`. -/
theorem integral_gauss_mul_second {τ : ℝ} {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (i j : Fin d) (y : Euc d) :
    ∫ w, gaussKernel d τ w *
        fderiv ℝ (fun y' => fderiv ℝ φ y' (ev j)) (y + w) (ev i) =
      ∫ w, hessG i j τ w * φ (y + w) := by
  set ψ : Euc d → ℝ := fun w => φ (y + w) with hψdef
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_const.add contDiff_id)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.addLeft y)
  set ψj : Euc d → ℝ := fun w => fderiv ℝ ψ w (ev j) with hψjdef
  have hψj : ContDiff ℝ ∞ ψj := (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hψjc : HasCompactSupport ψj := hψc.fderiv_apply ℝ (ev j)
  have hψj' : ψj = fun w => fderiv ℝ φ (y + w) (ev j) := by
    funext w'; simp only [ψj, ψ]; rw [fderiv_comp_add_left]
  have e1 : ∀ w, fderiv ℝ (fun y' => fderiv ℝ φ y' (ev j)) (y + w) (ev i) =
      fderiv ℝ ψj w (ev i) := by
    intro w
    rw [hψj', fderiv_comp_add_left (f := fun y' => fderiv ℝ φ y' (ev j))]
  simp_rw [e1]
  have hG : ContDiff ℝ ∞ (gaussKernel d τ) := Gaussian.contDiff_gaussKernel τ
  have hGi : ContDiff ℝ ∞ (fun w => fderiv ℝ (gaussKernel d τ) w (ev i)) :=
    (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [integral_mul_fderiv_euc (hG.of_le (by simp)) (hψj.of_le (by simp)) hψjc (ev i)]
  have h2 := integral_mul_fderiv_euc (f := fun w => fderiv ℝ (gaussKernel d τ) w (ev i))
    (g := ψ) (hGi.of_le (by simp)) (hψ.of_le (by simp)) hψc (ev j)
  change -∫ w, fderiv ℝ (gaussKernel d τ) w (ev i) * fderiv ℝ ψ w (ev j) = _
  rw [h2, neg_neg]
  congr 1; funext w
  rw [hessG_eq_fderiv]

end SliceIBP

section BackOffSupport

variable {ν : ℝ}

/-- **Off-support formula for the backward operator on tests.** For `Y ∉ tsupport g`,
`backTest ν i j g (Y) = ∫ K_ν(X - Y) g(X) dX`. -/
theorem backTest_offSupport (hν : 0 < ν) {g : PS d → ℝ} (hg : IsSTTest g) (i j : Fin d)
    {Y : PS d} (hY : Y ∉ tsupport g) :
    backTest ν i j g Y = ∫ X, causalKernelNu ν i j (X - Y) * g X := by
  have hB := hg.sD2 i j
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_of_disjoint' hg.2.isCompact
    (isCompact_singleton (x := Y)) (Set.disjoint_singleton_right.2 hY)
  obtain ⟨C, hC0, hC⟩ := abs_causalKernelNu_le_of_le hν i j hδ
  -- the two sides as integrals in `W = X - Y`
  rw [backTest_eq hν hg i j Y,
    ← integral_add_right_eq_self (fun X => causalKernelNu ν i j (X - Y) * g X) Y]
  simp only [add_sub_cancel_right]
  have hint1 : Integrable (fun W : PS d => causalHeat ν W * sD2 i j g (Y + W)) volume := by
    have := (locallyIntegrable_causalHeat (d := d) hν).integrable_smul_right_of_hasCompactSupport
      (g := fun W => sD2 i j g (Y + W)) (hB.continuous.comp (continuous_const.add continuous_id))
      (hB.2.comp_homeomorph (Homeomorph.addLeft Y))
    simpa [smul_eq_mul] using this
  have hint2 : Integrable (fun W : PS d => causalKernelNu ν i j W * g (W + Y)) volume := by
    have hgY : Integrable (fun W : PS d => g (W + Y)) volume := hg.integrable.comp_add_right Y
    refine (hgY.norm.const_mul C).mono' ?_ (Eventually.of_forall fun W => ?_)
    · exact ((measurable_causalKernelNu ν i j).mul (hg.continuous.measurable.comp
        (measurable_id.add measurable_const))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      by_cases h0 : g (W + Y) = 0
      · simp [h0]
      · have hW := hsep (W + Y) (subset_tsupport g h0) Y rfl
        rw [add_sub_cancel_right] at hW
        exact mul_le_mul_of_nonneg_right (hC W hW) (norm_nonneg _)
  refine (integral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Euc d))) _
    hint1).trans (Eq.trans ?_ (integral_prod (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Euc d))) _ hint2).symm)
  congr 1; funext r
  rcases le_or_gt r 0 with hr | hr
  · simp [causalHeat_of_nonpos ν (Y := (r, _)) hr, causalKernelNu_of_nonpos hν i j
      (X := (r, _)) hr]
  · simp only [causalHeat_of_pos ν (Y := (r, _)) hr, causalKernelNu_of_pos hν i j
      (X := (r, _)) hr]
    have hslice : ∀ w : Euc d, sD2 i j g (Y + (r, w)) =
        fderiv ℝ (fun y' => fderiv ℝ (fun x => g (Y.1 + r, x)) y' (ev j)) (Y.2 + w) (ev i) := by
      intro w
      exact sD2_slice hg i j (Y.1 + r) (Y.2 + w)
    simp_rw [hslice]
    rw [integral_gauss_mul_second (hg.slice_contDiff (Y.1 + r))
      (hg.slice_hasCompactSupport (Y.1 + r)) i j Y.2]
    congr 1; funext w
    congr 1
    congr 1
    ext <;> simp [add_comm]

end BackOffSupport

section L2OffSupport

variable {ν : ℝ}

theorem stronglyMeasurable_kernelIntegral (i j : Fin d) {φ : PS d → ℝ}
    (hφ : StronglyMeasurable φ) :
    StronglyMeasurable (fun X => ∫ Y, causalKernelNu ν i j (X - Y) * φ Y) := by
  have h : StronglyMeasurable
      (fun p : PS d × PS d => causalKernelNu ν i j (p.1 - p.2) * φ p.2) :=
    ((measurable_causalKernelNu ν i j).comp
      (measurable_fst.sub measurable_snd)).stronglyMeasurable.mul
      (hφ.comp_measurable measurable_snd)
  exact h.integral_prod_right'

/-- **INF02 T6: off-support kernel representation.** If `F ∈ L²` vanishes a.e. outside a
compact set `S`, then for a.e. `X ∉ S`, `(secondDerivOp ν i j F)(X) = ∫ K_ν(X - Y) F(Y) dY`
with `K_ν(t, x) = 1_{t>0} ∂_i∂_j G_{νt}(x)`. -/
theorem secondDerivOp_offSupport (hν : 0 < ν) (i j : Fin d)
    (F : Lp ℝ 2 (volume : Measure (PS d))) {S : Set (PS d)} (hS : IsCompact S)
    (hF : ∀ᵐ Y ∂volume, Y ∉ S → F Y = 0) :
    ∀ᵐ X ∂volume, X ∉ S →
      secondDerivOp hν i j F X = ∫ Y, causalKernelNu ν i j (X - Y) * F Y := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  set F' : PS d → ℝ := S.indicator (fun Y => F Y) with hF'def
  have hFF' : (fun Y => F Y) =ᵐ[volume] F' := by
    filter_upwards [hF] with Y hY
    by_cases hYS : Y ∈ S
    · rw [hF'def, indicator_of_mem hYS]
    · rw [hF'def, indicator_of_notMem hYS, hY hYS]
  have hF'S : ∀ Y, F' Y ≠ 0 → Y ∈ S := fun Y hY => Set.mem_of_indicator_ne_zero hY
  have hF'i : Integrable F' volume := by
    rw [hF'def, integrable_indicator_iff hSm]
    exact ((Lp.memLp F).locallyIntegrable (by norm_num)).integrableOn_isCompact hS
  have hF'm : StronglyMeasurable F' := (Lp.stronglyMeasurable F).indicator hSm
  set Kf : PS d → ℝ := fun X => ∫ Y, causalKernelNu ν i j (X - Y) * F' Y with hKf
  have hKfeq : ∀ X, (∫ Y, causalKernelNu ν i j (X - Y) * F Y) = Kf X := fun X =>
    integral_congr_ae (by filter_upwards [hFF'] with Y hY; beta_reduce at hY ⊢; rw [hY])
  have hKfm : StronglyMeasurable Kf := stronglyMeasurable_kernelIntegral i j hF'm
  -- local integrability of `Kf` on `Sᶜ`
  have hKfloc : LocallyIntegrableOn Kf Sᶜ volume := by
    rw [locallyIntegrableOn_iff hS.isClosed.isOpen_compl.isLocallyClosed]
    intro K hKU hK
    obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_of_disjoint' hK hS
      (Set.subset_compl_iff_disjoint_right.mp hKU)
    obtain ⟨C, hC0, hC⟩ := abs_causalKernelNu_le_of_le hν i j hδ
    refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne hKfm.aestronglyMeasurable
      (M := C * ∫ Y, |F' Y|) ?_
    rw [ae_restrict_iff' hK.measurableSet]
    refine Eventually.of_forall fun X hX => ?_
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hF'i.abs.const_mul _) (Eventually.of_forall fun Y => ?_)
    by_cases hY : F' Y = 0
    · simp [hY]
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC _ (hsep X hX Y (hF'S Y hY))) (abs_nonneg _)
  -- the duality identity against tests supported in `Sᶜ`
  have key : ∀ φ : PS d → ℝ, IsSTTest φ → tsupport φ ⊆ Sᶜ →
      Integrable (fun X => φ X * Kf X) volume ∧
        ∫ X, φ X * secondDerivOp hν i j F X = ∫ X, φ X * Kf X := by
    intro φ hφ hφS
    obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_of_disjoint' hφ.2.isCompact hS
      (Set.subset_compl_iff_disjoint_right.mp hφS)
    obtain ⟨C, hC0, hC⟩ := abs_causalKernelNu_le_of_le hν i j hδ
    have hFm : StronglyMeasurable
        (fun p : PS d × PS d => causalKernelNu ν i j (p.1 - p.2) * φ p.1 * F' p.2) :=
      (((measurable_causalKernelNu ν i j).comp
        (measurable_fst.sub measurable_snd)).stronglyMeasurable.mul
        (hφ.continuous.comp continuous_fst).stronglyMeasurable).mul
        (hF'm.comp_measurable measurable_snd)
    have hint : Integrable (Function.uncurry fun X Y =>
        causalKernelNu ν i j (X - Y) * φ X * F' Y) (volume.prod volume) := by
      refine (((hφ.integrable.mul_prod hF'i).norm).const_mul C).mono'
        hFm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      change ‖causalKernelNu ν i j (p.1 - p.2) * φ p.1 * F' p.2‖ ≤ C * ‖φ p.1 * F' p.2‖
      by_cases h0 : φ p.1 * F' p.2 = 0
      · simp [mul_assoc, h0]
      · have hg0 : φ p.1 ≠ 0 := left_ne_zero_of_mul h0
        have hf0 : F' p.2 ≠ 0 := right_ne_zero_of_mul h0
        rw [mul_assoc, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (hC _ (hsep p.1 (subset_tsupport φ hg0) p.2 (hF'S p.2 hf0))) (norm_nonneg _)
    have hrow : ∀ X, ∫ Y, causalKernelNu ν i j (X - Y) * φ X * F' Y = φ X * Kf X := by
      intro X
      rw [hKf, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
      beta_reduce
      ring
    have hgK : Integrable (fun X => φ X * Kf X) volume :=
      hint.integral_prod_left.congr (Eventually.of_forall fun X => hrow X)
    refine ⟨hgK, ?_⟩
    set G : Lp ℝ 2 (volume : Measure (PS d)) := (hφ.memLp 2).toLp φ with hGdef
    have hL : ∫ X, φ X * secondDerivOp hν i j F X =
        ∫ X, secondDerivOp hν i j F X * G X := by
      refine integral_congr_ae ?_
      filter_upwards [(hφ.memLp 2).coeFn_toLp] with X hX
      rw [hX, mul_comm]
    have hB : ∫ Y, F Y * backOp hν i j G Y = ∫ Y, F' Y * backTest ν i j φ Y := by
      rw [hGdef, backOp_toLp hν hφ i j]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_backTest hν hφ i j).coeFn_toLp, hFF'] with Y h1 h2
      beta_reduce at h2
      rw [h1, h2]
    have hCe : ∀ Y, F' Y * backTest ν i j φ Y =
        (∫ X, causalKernelNu ν i j (X - Y) * φ X) * F' Y := by
      intro Y
      by_cases hY : F' Y = 0
      · simp [hY]
      · have hYφ : Y ∉ tsupport φ := fun h => hφS h (hF'S Y hY)
        rw [backTest_offSupport hν hφ i j hYφ, mul_comm]
    calc ∫ X, φ X * secondDerivOp hν i j F X
        = ∫ Y, F Y * backOp hν i j G Y := by rw [hL, integral_secondDerivOp_mul]
      _ = ∫ Y, (∫ X, causalKernelNu ν i j (X - Y) * φ X) * F' Y := by
          rw [hB]; exact integral_congr_ae (Eventually.of_forall hCe)
      _ = ∫ Y, ∫ X, causalKernelNu ν i j (X - Y) * φ X * F' Y := by
          refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
          beta_reduce
          rw [integral_mul_const]
      _ = ∫ X, ∫ Y, causalKernelNu ν i j (X - Y) * φ X * F' Y :=
          (integral_integral_swap hint).symm
      _ = ∫ X, φ X * Kf X := by
          refine integral_congr_ae (Eventually.of_forall fun X => ?_)
          exact hrow X
  -- conclude on the open set `Sᶜ`
  have hRloc : LocallyIntegrable (secondDerivOp hν i j F) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hloc : LocallyIntegrableOn (fun X => secondDerivOp hν i j F X - Kf X) Sᶜ volume :=
    (hRloc.locallyIntegrableOn _).sub hKfloc
  have hzero := hS.isClosed.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun φ hφd hφc hφS => by
      obtain ⟨hgK, hid⟩ := key φ ⟨hφd, hφc⟩ hφS
      have hgR : Integrable (fun X => φ X * secondDerivOp hν i j F X) volume :=
        memLp_one_iff_integrable.mp
          ((Lp.memLp (secondDerivOp hν i j F)).mul' (IsSTTest.memLp (f := φ) ⟨hφd, hφc⟩ 2))
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub hgR hgK, hid, sub_self])
  filter_upwards [hzero] with X hX hXS
  rw [hKfeq]
  exact sub_eq_zero.mp (hX hXS)

end L2OffSupport

end UnforcedLeray.Parabolic
