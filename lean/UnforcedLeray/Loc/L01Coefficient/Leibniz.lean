import UnforcedLeray.Loc.L01Coefficient.Basic

/-!
# Step L1, helpers: the weak product rule

Support for `Loc/L01Coefficient.lean` (step L1, `paper/main.tex` lines 279–290,
`loc:eq:coefficient-maps`, blueprint unit B0711, infrastructure "weak product rule").

For a bilinear `B : ℝ³ × ℝ³ → ℝ³`, a coefficient `a ∈ L²_loc` with weak derivative
`∂ₖa ∈ L²_loc`, and `F ∈ H¹`, the product `B(a, F)` has weak derivative
`B(∂ₖa, F) + B(a, ∂ₖF)` (`leibniz`). The proof tests the weak derivative of `a` against
`φ · (ρₙ * F)ₘ`, which is smooth with compact support, and passes to the limit with the
compiled `H¹` convergence of mollifications (`Leray.h1MollifierAverage_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L01

open SobolevGraph

/-- `a ∈ L²_loc` in the form used here: every scalar test times `a` lies in `L²`. -/
def LocL2 (a : SpatialField) : Prop :=
  ∀ φ : Space → ℝ, IsSpatialTest φ → MemLp (fun x => φ x • a x) 2 volume

theorem integrable_smul_of_L2 {s : Space → ℝ} {w : SpatialField} (hs : MemLp s 2 volume)
    (hw : MemLp w 2 volume) : Integrable (fun x => s x • w x) volume :=
  memLp_one_iff_integrable.mp (hw.smul hs)

theorem integrable_bilin_of_L2 (B : Space →L[ℝ] Space →L[ℝ] Space) {f g : SpatialField}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => B (f x) (g x)) volume :=
  memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hf hg)

theorem bilin_expand (B : Space →L[ℝ] Space →L[ℝ] Space) (u v : Space) :
    B u v = ∑ m : Fin 3, v m • B.flip (EuclideanSpace.single m 1) u := by
  conv_lhs => rw [← space_sum_single v]
  simp [map_sum, map_smul]

theorem component_memLp {b : SpatialField} (hb : MemLp b 2 volume) (m : Fin 3) :
    MemLp (fun x => b x m) 2 volume :=
  (EuclideanSpace.proj m : Space →L[ℝ] ℝ).comp_memLp' hb

theorem spatialTestDerivative_mul_component {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    {b : SpatialField} (hb : ContDiff ℝ ∞ b) (k m : Fin 3) (x : Space) :
    spatialTestDerivative k (fun y => φ y * b y m) x =
      spatialTestDerivative k φ x * b x m + φ x * (fderiv ℝ b x (coordinateVector k)) m := by
  have hφd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.smooth.differentiable (by simp) x).hasFDerivAt
  have hbd : HasFDerivAt b (fderiv ℝ b x) x := (hb.differentiable (by simp) x).hasFDerivAt
  have hbm : HasFDerivAt (fun y => b y m)
      ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).comp (fderiv ℝ b x)) x :=
    (EuclideanSpace.proj m : Space →L[ℝ] ℝ).hasFDerivAt.comp x hbd
  have h : HasFDerivAt (fun y => φ y * b y m) _ x := hφd.mul hbm
  unfold spatialTestDerivative
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  change φ x * (fderiv ℝ b x (coordinateVector k)) m + b x m * _ = _
  ring

theorem isSpatialTest_mul_component {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    {b : SpatialField} (hb : ContDiff ℝ ∞ b) (m : Fin 3) :
    IsSpatialTest (fun y => φ y * b y m) :=
  ⟨hφ.smooth.mul ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).contDiff.comp hb),
    hφ.compact.mul_right⟩

/-- The product rule against a smooth `L²` factor with `L²` derivative. -/
theorem leibniz_smooth (B : Space →L[ℝ] Space →L[ℝ] Space) (k : Fin 3) {a a' : SpatialField}
    (ha : HasWeakSpatialDerivative k a a') (hla : LocL2 a) (hla' : LocL2 a')
    {b : SpatialField} (hb : ContDiff ℝ ∞ b) (hb2 : MemLp b 2 volume)
    (hdb2 : MemLp (fun x => fderiv ℝ b x (coordinateVector k)) 2 volume)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    ∫ x, B (spatialTestDerivative k φ x • a x) (b x) =
      -(∫ x, B (φ x • a' x) (b x)) -
        ∫ x, B (φ x • a x) (fderiv ℝ b x (coordinateVector k)) := by
  set e : Fin 3 → Space := fun m => EuclideanSpace.single m (1 : ℝ) with he
  have hA1 : MemLp (fun x => spatialTestDerivative k φ x • a x) 2 volume :=
    hla _ (hφ.derivative k)
  have hA2 : MemLp (fun x => φ x • a' x) 2 volume := hla' φ hφ
  have hA3 : MemLp (fun x => φ x • a x) 2 volume := hla φ hφ
  have i1 : ∀ m, Integrable (fun x => b x m •
      (B.flip (e m)) (spatialTestDerivative k φ x • a x)) volume := fun m =>
    integrable_smul_of_L2 (component_memLp hb2 m) ((B.flip (e m)).comp_memLp' hA1)
  have i2 : ∀ m, Integrable (fun x => (fderiv ℝ b x (coordinateVector k)) m •
      (B.flip (e m)) (φ x • a x)) volume := fun m =>
    integrable_smul_of_L2 (component_memLp hdb2 m) ((B.flip (e m)).comp_memLp' hA3)
  have i3 : ∀ m, Integrable (fun x => b x m • (B.flip (e m)) (φ x • a' x)) volume := fun m =>
    integrable_smul_of_L2 (component_memLp hb2 m) ((B.flip (e m)).comp_memLp' hA2)
  have key : ∀ m, (∫ x, b x m • (B.flip (e m)) (spatialTestDerivative k φ x • a x)) +
      (∫ x, (fderiv ℝ b x (coordinateVector k)) m • (B.flip (e m)) (φ x • a x)) =
        -∫ x, b x m • (B.flip (e m)) (φ x • a' x) := by
    intro m
    have hψ := isSpatialTest_mul_component hφ hb m
    have hid := ha.identity _ hψ
    have hL := congrArg (B.flip (e m)) hid
    rw [← (B.flip (e m)).integral_comp_comm (ha.left_integrable _ hψ), map_neg,
      ← (B.flip (e m)).integral_comp_comm (ha.right_integrable _ hψ)] at hL
    have h1 : ∀ x, (B.flip (e m)) (spatialTestDerivative k (fun y => φ y * b y m) x • a x) =
        b x m • (B.flip (e m)) (spatialTestDerivative k φ x • a x) +
          (fderiv ℝ b x (coordinateVector k)) m • (B.flip (e m)) (φ x • a x) := by
      intro x
      rw [spatialTestDerivative_mul_component hφ hb k m x]
      simp only [add_smul, map_add, map_smul, smul_smul]
      rw [mul_comm (b x m), mul_comm ((fderiv ℝ b x (coordinateVector k)) m)]
    have h2 : ∀ x, (B.flip (e m)) ((φ x * b x m) • a' x) =
        b x m • (B.flip (e m)) (φ x • a' x) := by
      intro x
      simp only [map_smul, smul_smul]
      rw [mul_comm (b x m)]
    simp_rw [h1, h2] at hL
    rw [integral_add (i1 m) (i2 m)] at hL
    exact hL
  have e1 : ∫ x, B (spatialTestDerivative k φ x • a x) (b x) =
      ∑ m, ∫ x, b x m • (B.flip (e m)) (spatialTestDerivative k φ x • a x) := by
    rw [← integral_finsetSum _ (fun m _ => i1 m)]
    exact integral_congr_ae (Eventually.of_forall fun x => bilin_expand B _ _)
  have e2 : ∫ x, B (φ x • a' x) (b x) = ∑ m, ∫ x, b x m • (B.flip (e m)) (φ x • a' x) := by
    rw [← integral_finsetSum _ (fun m _ => i3 m)]
    exact integral_congr_ae (Eventually.of_forall fun x => bilin_expand B _ _)
  have e3 : ∫ x, B (φ x • a x) (fderiv ℝ b x (coordinateVector k)) =
      ∑ m, ∫ x, (fderiv ℝ b x (coordinateVector k)) m • (B.flip (e m)) (φ x • a x) := by
    rw [← integral_finsetSum _ (fun m _ => i2 m)]
    exact integral_congr_ae (Eventually.of_forall fun x => bilin_expand B _ _)
  rw [e1, e2, e3, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun m _ => eq_sub_of_add_eq (key m))

/-- `⟨B(f, G)⟩` as the `L²` pairing. -/
theorem lpPairing_toL2 (B : Space →L[ℝ] Space →L[ℝ] Space) {f : SpatialField}
    (hf : MemLp f 2 volume) (G : L2Space) :
    B.lpPairing (volume : Measure Space) 2 2 (toL2 f) G = ∫ x, B (f x) (G x) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [coeFn_toL2 hf] with x hx
  rw [hx]

theorem bilin_smul_left (B : Space →L[ℝ] Space →L[ℝ] Space) (c : ℝ) (u v : Space) :
    B (c • u) v = c • B u v := by
  rw [map_smul, ContinuousLinearMap.smul_apply]

/-- **Weak product rule.** For a bilinear `B`, a coefficient `a` with weak derivative `a'`,
both in `L²_loc`, and `F ∈ H¹`: `∂ₖ B(a, F) = B(∂ₖa, F) + B(a, ∂ₖF)` weakly. -/
theorem leibniz (B : Space →L[ℝ] Space →L[ℝ] Space) (k : Fin 3) {a a' : SpatialField}
    (ha : HasWeakSpatialDerivative k a a') (hla : LocL2 a) (hla' : LocL2 a') (F : H1) :
    HasWeakSpatialDerivative k (fun x => B (a x) (F.value x))
      (fun x => B (a' x) (F.value x) + B (a x) (F.derivative k x)) := by
  have hFv := Lp.memLp F.value
  have hFd := Lp.memLp (F.derivative k)
  have hleft : ∀ φ, IsSpatialTest φ → (fun x => spatialTestDerivative k φ x • B (a x) (F.value x))
      = fun x => B (spatialTestDerivative k φ x • a x) (F.value x) := fun φ _ => by
    funext x
    rw [bilin_smul_left]
  have hright : ∀ φ, IsSpatialTest φ →
      (fun x => φ x • (B (a' x) (F.value x) + B (a x) (F.derivative k x))) =
        fun x => B (φ x • a' x) (F.value x) + B (φ x • a x) (F.derivative k x) := fun φ _ => by
    funext x
    rw [smul_add, bilin_smul_left, bilin_smul_left]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [hleft φ hφ]
    exact integrable_bilin_of_L2 B (hla _ (hφ.derivative k)) hFv
  · rw [hright φ hφ]
    exact (integrable_bilin_of_L2 B (hla' φ hφ) hFv).add (integrable_bilin_of_L2 B (hla φ hφ) hFd)
  · rw [hleft φ hφ, hright φ hφ,
      integral_add (integrable_bilin_of_L2 B (hla' φ hφ) hFv)
        (integrable_bilin_of_L2 B (hla φ hφ) hFd)]
    have hA1 := hla _ (hφ.derivative k)
    have hA2 := hla' φ hφ
    have hA3 := hla φ hφ
    -- the mollified sequence
    set ρ := SobolevEmbedding.shrinkingMollifier with hρ
    set M := fun n => Leray.h1MollifierAverage (ρ n) F with hM
    have hMt : Tendsto M atTop (𝓝 F) := Leray.h1MollifierAverage_tendsto F
    have hv : Tendsto (fun n => (M n).value) atTop (𝓝 F.value) :=
      (H1.valueCLM.continuous.tendsto F).comp hMt
    have hd : Tendsto (fun n => (M n).derivative k) atTop (𝓝 (F.derivative k)) :=
      ((H1.derivativeCLM k).continuous.tendsto F).comp hMt
    have hn : ∀ n, B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => spatialTestDerivative k φ x • a x) (M n).value =
        -(B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => φ x • a' x) (M n).value) -
          B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => φ x • a x) ((M n).derivative k) := by
      intro n
      set b := SobolevEmbedding.mollification (ρ n) (F.value : SpatialField) with hbdef
      have hb : ContDiff ℝ ∞ b := SobolevEmbedding.mollification_smooth _ _ hFv
      have hb2 : MemLp b 2 volume := SobolevEmbedding.mollification_memLp _ _ hFv
      have hdb : (fun x => fderiv ℝ b x (coordinateVector k)) =
          SobolevEmbedding.mollification (ρ n) (F.derivative k : SpatialField) := by
        funext x
        exact SobolevEmbedding.mollification_derivative (F.hasWeakDerivative k) hFv (ρ n) x
      have hdb2 : MemLp (fun x => fderiv ℝ b x (coordinateVector k)) 2 volume := by
        rw [hdb]
        exact SobolevEmbedding.mollification_memLp _ _ hFd
      have hs := leibniz_smooth B k ha hla hla' hb hb2 hdb2 hφ
      have cv : (M n).value =ᵐ[volume] b := Leray.coeFn_value_h1MollifierAverage (ρ n) F
      have cd : (M n).derivative k =ᵐ[volume] fun x => fderiv ℝ b x (coordinateVector k) := by
        rw [hdb]
        exact Leray.coeFn_derivative_h1MollifierAverage (ρ n) F k
      have q1 : B.lpPairing (volume : Measure Space) 2 2
          (toL2 fun x => spatialTestDerivative k φ x • a x) (M n).value =
            ∫ x, B (spatialTestDerivative k φ x • a x) (b x) := by
        rw [lpPairing_toL2 B hA1]
        exact integral_congr_ae (cv.mono fun x hx => by simp only [hx])
      have q2 : B.lpPairing (volume : Measure Space) 2 2
          (toL2 fun x => φ x • a' x) (M n).value = ∫ x, B (φ x • a' x) (b x) := by
        rw [lpPairing_toL2 B hA2]
        exact integral_congr_ae (cv.mono fun x hx => by simp only [hx])
      have q3 : B.lpPairing (volume : Measure Space) 2 2
          (toL2 fun x => φ x • a x) ((M n).derivative k) =
            ∫ x, B (φ x • a x) (fderiv ℝ b x (coordinateVector k)) := by
        rw [lpPairing_toL2 B hA3]
        exact integral_congr_ae (cd.mono fun x hx => by simp only [hx])
      rw [q1, q2, q3]
      exact hs
    have hl1 : Tendsto (fun n => B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => spatialTestDerivative k φ x • a x)
        (M n).value) atTop (𝓝 (B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => spatialTestDerivative k φ x • a x) F.value)) :=
      (((B.lpPairing (volume : Measure Space) 2 2) _).continuous.tendsto _).comp hv
    have hl2 : Tendsto (fun n => -(B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => φ x • a' x) (M n).value) -
        B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => φ x • a x) ((M n).derivative k)) atTop
        (𝓝 (-(B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => φ x • a' x) F.value) -
          B.lpPairing (volume : Measure Space) 2 2 (toL2 fun x => φ x • a x) (F.derivative k))) :=
      ((((B.lpPairing (volume : Measure Space) 2 2) _).continuous.tendsto _).comp hv).neg.sub ((((B.lpPairing (volume : Measure Space) 2 2) _).continuous.tendsto _).comp hd)
    have final := tendsto_nhds_unique (hl1.congr hn) hl2
    rw [lpPairing_toL2 B hA1, lpPairing_toL2 B hA2, lpPairing_toL2 B hA3] at final
    rw [final]
    abel

end UnforcedLeray.Blueprint.L01
