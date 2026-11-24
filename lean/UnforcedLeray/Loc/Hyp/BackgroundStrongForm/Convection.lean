import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.Hypotheses

/-!
# H-BgStrong, helpers: `-𝔓 div(U ⊗ U)` in `L²` for a bounded field with `L²` gradient

Support for `Loc/Hyp/BackgroundStrongForm.lean` (target `BackgroundStrongForm`,
`paper/main.tex` lines 159–168; blueprint units B0707, B0708, B0711).

Let `U` be a field with `U ∈ L^∞`, weak derivatives `∂ₖU ∈ L²` and `U ⊗ U` with `L²`
columns. (For the background, `U = U_*(τ) = H_h[u_dss](τ) + r_heat(τ)` is bounded by
`HeatProfileRegularity` and `H2EmbedsC0`, and `∇U_* ∈ L²` by `HeatProfileGradientL2` and
`r_heat ∈ H²`; `U` itself is not in `L²`.) Then every column `U_j U` of `U ⊗ U` is in `H¹`
with `∂ₖ(U_j U) = (∂ₖU)_j U + U_j ∂ₖU` (`hasWeak_bilin_self`, a localized weak product rule:
on the support of a test `U_j U = U_j (χ_R U)` with `χ_R U ∈ H¹`, and the compiled product
rule `L01.leibniz` applies). Hence `N = -𝔓 ∑_j ∂_j(U_j U)` is an `L²` field with
`⟨N, φ⟩ = -⟨𝔓 div(U ⊗ U), φ⟩` for every vector test (`isMinusLerayDiv_convection`), the
literal characterization `IsMinusLerayDiv` of `Blueprint/Localization/Spaces.lean`. The
formula `convection_eq` writes `N` through the Hölder products `L^∞ × L² → L²`, which gives
continuity in the data (`continuous_convSum`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.HypBg

open SobolevGraph

/-! ## Products of scalar tests -/

theorem isSpatialTest_mul {φ χ : Space → ℝ} (hφ : IsSpatialTest φ) (hχ : IsSpatialTest χ) :
    IsSpatialTest (fun y => φ y * χ y) :=
  ⟨hφ.smooth.mul hχ.smooth, hφ.compact.mul_right⟩

theorem spatialTestDerivative_mul {φ χ : Space → ℝ} (hφ : IsSpatialTest φ)
    (hχ : IsSpatialTest χ) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (fun y => φ y * χ y) x =
      spatialTestDerivative i φ x * χ x + φ x * spatialTestDerivative i χ x := by
  have hφd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.smooth.differentiable (by simp) x).hasFDerivAt
  have hχd : HasFDerivAt χ (fderiv ℝ χ x) x :=
    (hχ.smooth.differentiable (by simp) x).hasFDerivAt
  have hd : HasFDerivAt (fun y => φ y * χ y) (φ x • fderiv ℝ χ x + χ x • fderiv ℝ φ x) x :=
    hφd.mul hχd
  unfold spatialTestDerivative
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem integrable_test_smul_top {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) {a : SpatialField}
    (ha : MemLp a ∞ volume) : Integrable (fun x => ψ x • a x) :=
  memLp_one_iff_integrable.mp (ha.smul (hψ.memLp 1))

theorem integrable_test_smul_two {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) {a : SpatialField}
    (ha : MemLp a 2 volume) : Integrable (fun x => ψ x • a x) :=
  memLp_one_iff_integrable.mp (ha.smul (hψ.memLp 2))

theorem locL2_of_top {a : SpatialField} (ha : MemLp a ∞ volume) : L01.LocL2 a :=
  fun _ hφ => L01.test_smul_memLp (s := 2) hφ ha

/-- The weak product rule for a scalar test times a bounded field with `L²` derivative. -/
theorem hasWeak_test_smul {χ : Space → ℝ} (hχ : IsSpatialTest χ) {a a' : SpatialField}
    {i : Fin 3} (ha : HasWeakSpatialDerivative i a a') (ha8 : MemLp a ∞ volume)
    (ha' : MemLp a' 2 volume) :
    HasWeakSpatialDerivative i (fun x => χ x • a x)
      (fun x => spatialTestDerivative i χ x • a x + χ x • a' x) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · refine (integrable_test_smul_top (isSpatialTest_mul (hφ.derivative i) hχ) ha8).congr
      (Eventually.of_forall fun x => ?_)
    simp only [smul_smul]
  · have h1 := integrable_test_smul_top (isSpatialTest_mul hφ (hχ.derivative i)) ha8
    have h2 := integrable_test_smul_two (isSpatialTest_mul hφ hχ) ha'
    refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, smul_add, smul_smul]
  · have hid := ha.identity _ (isSpatialTest_mul hφ hχ)
    have hA := integrable_test_smul_top (isSpatialTest_mul (hφ.derivative i) hχ) ha8
    have hB := integrable_test_smul_top (isSpatialTest_mul hφ (hχ.derivative i)) ha8
    have hC := integrable_test_smul_two (isSpatialTest_mul hφ hχ) ha'
    have e1 : (fun x => spatialTestDerivative i (fun y => φ y * χ y) x • a x) =
        fun x => (spatialTestDerivative i φ x * χ x) • a x +
          (φ x * spatialTestDerivative i χ x) • a x := by
      funext x
      rw [spatialTestDerivative_mul hφ hχ, add_smul]
    rw [e1, integral_add hA hB] at hid
    have lhs : (fun x => spatialTestDerivative i φ x • (χ x • a x)) =
        fun x => (spatialTestDerivative i φ x * χ x) • a x := by
      funext x
      rw [smul_smul]
    have rhs : (fun x => φ x • (spatialTestDerivative i χ x • a x + χ x • a' x)) =
        fun x => (φ x * spatialTestDerivative i χ x) • a x + (φ x * χ x) • a' x := by
      funext x
      rw [smul_add, smul_smul, smul_smul]
    rw [lhs, rhs, integral_add hB hC]
    rw [eq_neg_iff_add_eq_zero] at hid ⊢
    rw [← add_assoc]
    exact hid

/-! ## The cutoff `χ_R U ∈ H¹` -/

theorem spatialTestDerivative_cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ < R)
    (i : Fin 3) : spatialTestDerivative i (L14.cutoff R) x = 0 := by
  have hev : L14.cutoff R =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)] with y hy
    exact L14.cutoff_eq_one hR (mem_ball_zero_iff.mp hy).le
  unfold spatialTestDerivative
  rw [hev.fderiv_eq]
  simp

section Product

variable {U : SpatialField} {dU : Fin 3 → L2Space}

/-- `χ_R U ∈ H¹` for a bounded `U` with `L²` derivatives. -/
def cutoffH1 (hU : MemLp U ∞ volume)
    (hdU : ∀ i, HasWeakSpatialDerivative i U (dU i : SpatialField)) {R : ℝ} (hR : 0 < R) : H1 :=
  H1.ofFields (fun x => L14.cutoff R x • U x)
    (fun i x => spatialTestDerivative i (L14.cutoff R) x • U x +
      L14.cutoff R x • (dU i : SpatialField) x)
    (L01.test_smul_memLp (s := 2) (L14.cutoff_isSpatialTest hR) hU)
    (fun i => (L01.test_smul_memLp (s := 2) ((L14.cutoff_isSpatialTest hR).derivative i)
      hU).add (L01.test_smul_memLp (s := ∞) (L14.cutoff_isSpatialTest hR) (Lp.memLp (dU i))))
    (fun i => hasWeak_test_smul (L14.cutoff_isSpatialTest hR) (hdU i) hU (Lp.memLp (dU i)))

/-- **Localized weak product rule.** For a bilinear `B`, a bounded field `U` with weak
derivatives `∂ₖU ∈ L²`: `∂ₖ B(U, U) = B(∂ₖU, U) + B(U, ∂ₖU)` weakly. -/
theorem hasWeak_bilin_self (B : Space →L[ℝ] Space →L[ℝ] Space) (k : Fin 3)
    (hU : MemLp U ∞ volume) (hdU : ∀ i, HasWeakSpatialDerivative i U (dU i : SpatialField)) :
    HasWeakSpatialDerivative k (fun x => B (U x) (U x))
      (fun x => B ((dU k : SpatialField) x) (U x) + B (U x) ((dU k : SpatialField) x)) := by
  have hd2 : MemLp (dU k : SpatialField) 2 volume := Lp.memLp _
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have h := B.memLp_of_bilin 1
      (memLp_one_iff_integrable.mpr (integrable_test_smul_top (hφ.derivative k) hU)) hU
    refine (memLp_one_iff_integrable.mp h).congr (Eventually.of_forall fun x => ?_)
    exact L01.bilin_smul_left B _ _ _
  · have h1 := B.memLp_of_bilin 1
      (memLp_one_iff_integrable.mpr (integrable_test_smul_two hφ hd2)) hU
    have h2 := B.memLp_of_bilin 1 (L01.test_smul_memLp (s := 2) hφ hU) hd2
    refine ((memLp_one_iff_integrable.mp h1).add (memLp_one_iff_integrable.mp h2)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, L01.bilin_smul_left, smul_add]
  · obtain ⟨R, hRpos, hsub⟩ : ∃ R, 0 < R ∧ tsupport φ ⊆ Metric.ball (0 : Space) R :=
      (IsCompact.isBounded hφ.compact).subset_ball_lt 0 0
    set F := cutoffH1 hU hdU hRpos with hF
    have hL := L01.leibniz B k (hdU k) (locL2_of_top hU) (L01.locL2_L2 (dU k)) F
    have hv : (F.value : SpatialField) =ᵐ[volume] fun x => L14.cutoff R x • U x :=
      coeFn_toL2 (L01.test_smul_memLp (s := 2) (L14.cutoff_isSpatialTest hRpos) hU)
    have hdv : (F.derivative k : SpatialField) =ᵐ[volume] fun x =>
        spatialTestDerivative k (L14.cutoff R) x • U x +
          L14.cutoff R x • (dU k : SpatialField) x :=
      coeFn_toL2 ((L01.test_smul_memLp (s := 2)
        ((L14.cutoff_isSpatialTest hRpos).derivative k) hU).add
        (L01.test_smul_memLp (s := ∞) (L14.cutoff_isSpatialTest hRpos) (Lp.memLp (dU k))))
    have hin : ∀ x ∈ tsupport φ,
        L14.cutoff R x = 1 ∧ spatialTestDerivative k (L14.cutoff R) x = 0 := by
      intro x hx
      have hxR : ‖x‖ < R := mem_ball_zero_iff.mp (hsub hx)
      exact ⟨L14.cutoff_eq_one hRpos hxR.le, spatialTestDerivative_cutoff_eq_zero hRpos hxR k⟩
    have e1 : (fun x => spatialTestDerivative k φ x • B (U x) (F.value x)) =ᵐ[volume]
        fun x => spatialTestDerivative k φ x • B (U x) (U x) := by
      filter_upwards [hv] with x hx
      by_cases hxs : x ∈ tsupport φ
      · rw [hx, (hin x hxs).1, one_smul]
      · have h0 : spatialTestDerivative k φ x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hxs (hφ.derivative_support_subset k h))
        rw [h0, zero_smul, zero_smul]
    have e2 : (fun x => φ x • (B ((dU k : SpatialField) x) (F.value x) +
        B (U x) (F.derivative k x))) =ᵐ[volume]
        fun x => φ x • (B ((dU k : SpatialField) x) (U x) + B (U x) ((dU k : SpatialField) x)) := by
      filter_upwards [hv, hdv] with x hx hdx
      by_cases hxs : x ∈ tsupport φ
      · rw [hx, hdx, (hin x hxs).1, (hin x hxs).2, one_smul, zero_smul, zero_add, one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hxs, zero_smul, zero_smul]
    rw [← integral_congr_ae e1, ← integral_congr_ae e2]
    exact hL.identity φ hφ

/-- The derivative `∂ₖ(U_j U) = (∂ₖU)_j U + U_j ∂ₖU` of column `j` of `U ⊗ U`. -/
def colDeriv (U : SpatialField) (dU : Fin 3 → L2Space) (j k : Fin 3) : SpatialField :=
  fun x => L01.prodJ j ((dU k : SpatialField) x) (U x) + L01.prodJ j (U x) ((dU k : SpatialField) x)

theorem memLp_colDeriv (hU : MemLp U ∞ volume) (j k : Fin 3) :
    MemLp (colDeriv U dU j k) 2 volume :=
  ((L01.prodJ j).memLp_of_bilin 2 (Lp.memLp (dU k)) hU).add
    ((L01.prodJ j).memLp_of_bilin 2 hU (Lp.memLp (dU k)))

theorem hasWeak_column (hU : MemLp U ∞ volume)
    (hdU : ∀ i, HasWeakSpatialDerivative i U (dU i : SpatialField)) (j k : Fin 3) :
    HasWeakSpatialDerivative k (tensorColumns U U j) (colDeriv U dU j k) :=
  hasWeak_bilin_self (L01.prodJ j) k hU hdU

/-- Column `j` of `U ⊗ U` as an element of `H¹`. -/
def colH1 (hU : MemLp U ∞ volume)
    (hdU : ∀ i, HasWeakSpatialDerivative i U (dU i : SpatialField))
    (hcol : ColumnsL2 (tensorColumns U U)) (j : Fin 3) : H1 :=
  H1.ofFields (tensorColumns U U j) (colDeriv U dU j) (hcol j) (memLp_colDeriv hU j)
    (hasWeak_column hU hdU j)

/-- `N = -𝔓 ∑_j ∂_j(U_j U) = -𝔓 div(U ⊗ U)`. -/
def convection (hU : MemLp U ∞ volume)
    (hdU : ∀ i, HasWeakSpatialDerivative i U (dU i : SpatialField))
    (hcol : ColumnsL2 (tensorColumns U U)) : L2Space :=
  -Leray.projection (∑ j : Fin 3, (colH1 hU hdU hcol j).derivative j)

/-- **The literal weak characterization**: `N = -𝔓 div(U ⊗ U)` against every vector test. -/
theorem isMinusLerayDiv_convection (hU : MemLp U ∞ volume)
    (hdU : ∀ i, HasWeakSpatialDerivative i U (dU i : SpatialField))
    (hcol : ColumnsL2 (tensorColumns U U)) :
    IsMinusLerayDiv (tensorColumns U U) (convection hU hdU hcol) := by
  refine ⟨hcol, fun φ hφ => ?_⟩
  have hterm : ∀ j : Fin 3,
      inner ℝ (Leray.projection ((colH1 hU hdU hcol j).derivative j)) (toL2 φ) =
        -inner ℝ (toL2 (tensorColumns U U j)) (Leray.projection (toL2 (testPartial φ j))) := by
    intro j
    have h := L01.H1_inner_testPartial (Leray.h1Projection (colH1 hU hdU hcol j)) hφ j
    have hv : (colH1 hU hdU hcol j).value = toL2 (tensorColumns U U j) := rfl
    rw [Leray.value_h1Projection, Leray.derivative_h1Projection, hv] at h
    rw [eq_neg_iff_add_eq_zero, ← Leray.projection_selfadjoint, h]
    exact add_neg_cancel _
  rw [convection, inner_neg_left, map_sum, sum_inner, lerayDivPairing, neg_neg]
  simp only [hterm, Finset.sum_neg_distrib, neg_neg]

/-- The Hölder form of `∑_j ∂_j(U_j U)`: `∑_j P_j(∂_jU, U) + P_j(U, ∂_jU)`. -/
def convSum (v : L01.LinfSpace) (d : Fin 3 → L2Space) : L2Space :=
  ∑ j : Fin 3, (L01.hol j 2 ∞ (d j) v + L01.hol j ∞ 2 v (d j))

theorem convection_eq (hU : MemLp U ∞ volume)
    (hdU : ∀ i, HasWeakSpatialDerivative i U (dU i : SpatialField))
    (hcol : ColumnsL2 (tensorColumns U U)) {V : ZeroAtInftyContinuousMap Space Space}
    (hV : (V : SpatialField) =ᵐ[volume] U) :
    convection hU hdU hcol = -Leray.projection (convSum (L01.toLinf V) dU) := by
  rw [convection, convSum]
  refine congrArg (fun F => -Leray.projection F) (Finset.sum_congr rfl fun j _ => ?_)
  change toL2 (colDeriv U dU j j) = _
  rw [L10.toL2_congr (memLp_colDeriv hU j j) (g := ((L01.hol j 2 ∞ (dU j) (L01.toLinf V) +
    L01.hol j ∞ 2 (L01.toLinf V) (dU j) : L2Space) : SpatialField)), L10.toL2_coeFn]
  filter_upwards [Lp.coeFn_add (L01.hol j 2 ∞ (dU j) (L01.toLinf V))
      (L01.hol j ∞ 2 (L01.toLinf V) (dU j)), L01.coeFn_hol j (dU j) (L01.toLinf V),
    L01.coeFn_hol j (L01.toLinf V) (dU j), L01.coeFn_toLinf V, hV] with x h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, h4, h5]
  rfl

theorem continuous_convSum {α : Type*} [TopologicalSpace α] {v : α → L01.LinfSpace}
    {d : α → Fin 3 → L2Space} (hv : Continuous v) (hd : Continuous d) :
    Continuous fun a => convSum (v a) (d a) := by
  unfold convSum
  refine continuous_finsetSum _ fun j _ => ?_
  exact (((L01.hol j 2 ∞).continuous.comp ((continuous_apply j).comp hd)).clm_apply hv).add
    (((L01.hol j ∞ 2).continuous.comp hv).clm_apply ((continuous_apply j).comp hd))

end Product

end UnforcedLeray.Blueprint.HypBg
