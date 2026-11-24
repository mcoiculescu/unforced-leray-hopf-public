import UnforcedLeray.Short.PartIIb.Sub.T12_1_1_3

/-!
# Leaf `PartII-b:T12/1/1/3/3`: `G` is weakly divergence free

Source: `the November 2 reference manuscript` lines 1670, 1923-1926. With
`f_k = planeComp F k` and `g_i = f_i - Σ_k S_{ik} f_k`, the pairing `∫ G·∇φ` is transported to
`Fin 2 → ℝ` by `finTwoArrow`, where `∂_i(φ ∘ L) = (∂_iφ) ∘ L`. Then `∫ Σ_i g_i ∂_iψ = 0` follows
from the transposition clause `∫ S_{ik}f · g = ∫ f · S_{ki}g` and the first test identity
`Σ_i S_{ki} ∂_iψ = ∂_kψ` of `IsPlaneRieszFamily`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `k`-th component of `F` transported, as an element of `L²(Fin 2 → ℝ)`. -/
def rieszOrth_f {F : ℝ × ℝ → RMerid} (hF : MemLp F 2 volume) : Fin 2 → PlaneL2 :=
  fun k => (planeComp_memLp hF k).toLp _

theorem rieszOrth_f_ae {F : ℝ × ℝ → RMerid} (hF : MemLp F 2 volume) (k : Fin 2) :
    (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) =ᵐ[volume] planeComp F k :=
  (planeComp_memLp hF k).coeFn_toLp

/-- The `i`-th component of a planar test field, transported to `Fin 2 → ℝ`. -/
def rieszOrth_test (Ψ : ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2) : (Fin 2 → ℝ) → ℝ :=
  fun x => Ψ (MeasurableEquiv.finTwoArrow x) i

/-- The linear change of variables `Fin 2 → ℝ ≃ ℝ × ℝ`. -/
def rieszOrth_L : (Fin 2 → ℝ) ≃L[ℝ] ℝ × ℝ := ContinuousLinearEquiv.finTwoArrow ℝ ℝ

theorem rieszOrth_L_apply (x : Fin 2 → ℝ) : rieszOrth_L x = MeasurableEquiv.finTwoArrow x := rfl

theorem rieszOrth_test_smooth {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (i : Fin 2) :
    ContDiff ℝ ∞ (rieszOrth_test Ψ i) :=
  (hΨ.comp i).smooth.comp rieszOrth_L.contDiff

theorem rieszOrth_test_compact {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (i : Fin 2) :
    HasCompactSupport (rieszOrth_test Ψ i) :=
  (hΨ.comp i).compact.comp_homeomorph rieszOrth_L.toHomeomorph

theorem rieszOrth_test_memLp {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (i : Fin 2) :
    MemLp (rieszOrth_test Ψ i) 2 volume :=
  (rieszOrth_test_smooth hΨ i).continuous.memLp_of_hasCompactSupport (rieszOrth_test_compact hΨ i)

/-- Chain rule for the linear change of variables. -/
theorem rieszOrth_fderiv (g : ℝ × ℝ → ℝ) (hg : Differentiable ℝ g) (x v : Fin 2 → ℝ) :
    fderiv ℝ (fun y => g (rieszOrth_L y)) x v = fderiv ℝ g (rieszOrth_L x) (rieszOrth_L v) := by
  have h1 : HasFDerivAt (fun y => g (rieszOrth_L y))
      ((fderiv ℝ g (rieszOrth_L x)).comp rieszOrth_L.toContinuousLinearMap) x :=
    (hg (rieszOrth_L x)).hasFDerivAt.comp x rieszOrth_L.toContinuousLinearMap.hasFDerivAt
  rw [h1.fderiv]
  rfl

theorem rieszOrth_L_single0 : rieszOrth_L (Pi.single 0 1) = (1, 0) := by
  ext <;> simp [rieszOrth_L, Pi.single_apply]

theorem rieszOrth_L_single1 : rieszOrth_L (Pi.single 1 1) = (0, 1) := by
  ext <;> simp [rieszOrth_L, Pi.single_apply]

/-- A planar solenoidal test has transported divergence zero. -/
theorem rieszOrth_div {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (x : Fin 2 → ℝ) :
    ∑ i : Fin 2, fderiv ℝ (rieszOrth_test Ψ i) x (Pi.single i 1) = 0 := by
  have hdiff : ∀ j : Fin 2, Differentiable ℝ (fun z => Ψ z j) := fun j =>
    (hΨ.comp j).smooth.differentiable (by simp)
  have hd := hΨ.div_free (rieszOrth_L x)
  rw [Fin.sum_univ_two]
  have e0 : rieszOrth_test Ψ 0 = fun y => (fun z => Ψ z 0) (rieszOrth_L y) := rfl
  have e1 : rieszOrth_test Ψ 1 = fun y => (fun z => Ψ z 1) (rieszOrth_L y) := rfl
  rw [e0, e1, rieszOrth_fderiv _ (hdiff 0) x (Pi.single 0 1),
    rieszOrth_fderiv _ (hdiff 1) x (Pi.single 1 1), rieszOrth_L_single0, rieszOrth_L_single1]
  exact hd

theorem rieszOrth_G_eq (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) {F : ℝ × ℝ → RMerid}
    (hF : MemLp F 2 volume) :
    planeRieszG S F = fun z => WithLp.toLp 2 (fun i =>
      ((rieszOrth_f hF i - ∑ k, S i k (rieszOrth_f hF k) : PlaneL2) :
        (Fin 2 → ℝ) → ℝ) (MeasurableEquiv.finTwoArrow.symm z)) := by
  rw [planeRieszG, dif_pos hF]
  rfl

theorem rieszDiv_smooth {φ : ℝ × ℝ → ℝ} (hφ : PlaneTest φ) :
    ContDiff ℝ ∞ (fun y => φ (rieszOrth_L y)) :=
  hφ.smooth.comp rieszOrth_L.contDiff

theorem rieszDiv_compact {φ : ℝ × ℝ → ℝ} (hφ : PlaneTest φ) :
    HasCompactSupport (fun y => φ (rieszOrth_L y)) :=
  hφ.compact.comp_homeomorph rieszOrth_L.toHomeomorph

/-- The `i`-th partial derivative of the transported test function. -/
def rieszDiv_D (φ : ℝ × ℝ → ℝ) (i : Fin 2) : (Fin 2 → ℝ) → ℝ :=
  fun x => fderiv ℝ (fun y => φ (rieszOrth_L y)) x (Pi.single i 1)

theorem rieszDiv_D_memLp {φ : ℝ × ℝ → ℝ} (hφ : PlaneTest φ) (i : Fin 2) :
    MemLp (rieszDiv_D φ i) 2 volume := by
  have hc : Continuous (rieszDiv_D φ i) := by
    have h1 : Continuous (fderiv ℝ (fun y => φ (rieszOrth_L y))) :=
      (rieszDiv_smooth hφ).continuous_fderiv (by simp)
    exact h1.clm_apply continuous_const
  have hs : HasCompactSupport (rieszDiv_D φ i) :=
    (rieszDiv_compact hφ).fderiv_apply ℝ (Pi.single i 1)
  exact hc.memLp_of_hasCompactSupport hs

theorem rieszDiv_D_eq {φ : ℝ × ℝ → ℝ} (hφ : PlaneTest φ) (x : Fin 2 → ℝ) :
    rieszDiv_D φ 0 x = fderiv ℝ φ (MeasurableEquiv.finTwoArrow x) (1, 0) ∧
      rieszDiv_D φ 1 x = fderiv ℝ φ (MeasurableEquiv.finTwoArrow x) (0, 1) := by
  have hdiff : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  constructor
  · unfold rieszDiv_D
    rw [rieszOrth_fderiv φ hdiff x (Pi.single 0 1), rieszOrth_L_single0]
    rfl
  · unfold rieszDiv_D
    rw [rieszOrth_fderiv φ hdiff x (Pi.single 1 1), rieszOrth_L_single1]
    rfl

theorem rieszDiv_G_apply (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) {F : ℝ × ℝ → RMerid}
    (hF : MemLp F 2 volume) (x : Fin 2 → ℝ) (i : Fin 2) :
    planeRieszG S F (MeasurableEquiv.finTwoArrow x) i =
      ((rieszOrth_f hF i - ∑ k, S i k (rieszOrth_f hF k) : PlaneL2) : (Fin 2 → ℝ) → ℝ) x := by
  rw [rieszOrth_G_eq S hF]
  simp only [MeasurableEquiv.symm_apply_apply, PiLp.toLp_apply]

theorem rieszDiv_ae (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) {F : ℝ × ℝ → RMerid}
    (hF : MemLp F 2 volume) (i : Fin 2) : ∀ᵐ x ∂volume,
    ((rieszOrth_f hF i - ∑ k, S i k (rieszOrth_f hF k) : PlaneL2) : (Fin 2 → ℝ) → ℝ) x =
      (rieszOrth_f hF i : (Fin 2 → ℝ) → ℝ) x - ∑ k, (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x := by
  filter_upwards [Lp.coeFn_sub (rieszOrth_f hF i) (∑ k, S i k (rieszOrth_f hF k)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun k => S i k (rieszOrth_f hF k))] with x h1 h2
  rw [h1, Pi.sub_apply, h2]

/-- **Leaf `PartII-b:T12/1/1/3/3`**: `G` is weakly divergence free. -/
theorem planeRieszGDiv : PlaneRieszGDiv := by
  intro S B hS F hF φ hφ
  have hD : ∀ i : Fin 2, MemLp (rieszDiv_D φ i) 2 volume := fun i => rieszDiv_D_memLp hφ i
  -- first test identity: Σ_i S_{ki} ∂_iψ = ∂_kψ
  have hc4 : ∀ k : Fin 2, ∑ i, S k i ((hD i).toLp _) = (hD k).toLp _ := fun k =>
    hS.2.2.2.1 (fun y => φ (rieszOrth_L y)) (rieszDiv_smooth hφ) (rieszDiv_compact hφ) hD k
  -- pointwise form of the integrand on the transported plane
  have hint_eq : ∀ x : Fin 2 → ℝ,
      planeRieszG S F (MeasurableEquiv.finTwoArrow x) 0 * fderiv ℝ φ (MeasurableEquiv.finTwoArrow x) (1, 0) +
        planeRieszG S F (MeasurableEquiv.finTwoArrow x) 1 * fderiv ℝ φ (MeasurableEquiv.finTwoArrow x) (0, 1) =
      ∑ i : Fin 2, ((rieszOrth_f hF i - ∑ k, S i k (rieszOrth_f hF k) : PlaneL2) : (Fin 2 → ℝ) → ℝ) x *
        rieszDiv_D φ i x := by
    intro x
    rw [Fin.sum_univ_two, ← (rieszDiv_D_eq hφ x).1, ← (rieszDiv_D_eq hφ x).2,
      rieszDiv_G_apply S hF, rieszDiv_G_apply S hF]
  have hA_ae : ∀ᵐ x ∂volume, ∑ i : Fin 2, ((rieszOrth_f hF i - ∑ k, S i k (rieszOrth_f hF k) : PlaneL2) :
        (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x =
      ∑ i : Fin 2, (rieszOrth_f hF i : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x -
        ∑ i : Fin 2, ∑ k : Fin 2, (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x := by
    filter_upwards [ae_all_iff.2 (fun i => rieszDiv_ae S hF i)] with x hx
    simp only [hx, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  have hfD : ∀ i : Fin 2, Integrable (fun x => (rieszOrth_f hF i : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x)
      volume :=
    fun i => (Lp.memLp (rieszOrth_f hF i)).integrable_mul (hD i)
  have hTD : ∀ i k : Fin 2, Integrable (fun x => (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x *
      rieszDiv_D φ i x) volume :=
    fun i k => (Lp.memLp (S i k (rieszOrth_f hF k))).integrable_mul (hD i)
  have hA : ∀ i k : Fin 2, ∫ x, (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x =
      ∫ x, (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x * (S k i ((hD i).toLp _) : (Fin 2 → ℝ) → ℝ) x := by
    intro i k
    have h1 : (fun x => (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x) =ᵐ[volume]
        (fun x => (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x * ((hD i).toLp _ : (Fin 2 → ℝ) → ℝ) x) := by
      filter_upwards [(hD i).coeFn_toLp] with x hx
      rw [hx]
    rw [integral_congr_ae h1]
    exact hS.2.1 i k _ _
  have hsum_ae : ∀ k : Fin 2, ∀ᵐ x ∂volume,
      ∑ i, (S k i ((hD i).toLp _) : (Fin 2 → ℝ) → ℝ) x = rieszDiv_D φ k x := by
    intro k
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i => S k i ((hD i).toLp _))
    rw [hc4 k] at hs
    filter_upwards [hs, (hD k).coeFn_toLp] with x h1 h2
    rw [← h2]
    exact h1.symm
  have hk : ∀ k : Fin 2, ∑ i : Fin 2, ∫ x, (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x *
      (S k i ((hD i).toLp _) : (Fin 2 → ℝ) → ℝ) x =
      ∫ x, (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ k x := by
    intro k
    have hint_k : ∀ i : Fin 2, Integrable (fun x => (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x *
        (S k i ((hD i).toLp _) : (Fin 2 → ℝ) → ℝ) x) volume :=
      fun i => (Lp.memLp (rieszOrth_f hF k)).integrable_mul (Lp.memLp (S k i ((hD i).toLp _)))
    rw [← integral_finset_sum Finset.univ (fun i _ => hint_k i)]
    refine integral_congr_ae ?_
    filter_upwards [hsum_ae k] with x hx
    rw [← Finset.mul_sum, hx]
  have hB : ∫ x, ∑ i : Fin 2, ∑ k : Fin 2, (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x *
      rieszDiv_D φ i x = ∑ k : Fin 2, ∫ x, (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ k x := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ => hTD i k)]
    calc ∑ i : Fin 2, ∫ x, ∑ k : Fin 2, (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x *
          rieszDiv_D φ i x
        = ∑ i : Fin 2, ∑ k : Fin 2, ∫ x, (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x *
          rieszDiv_D φ i x := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finset_sum _ fun k _ => hTD i k]
      _ = ∑ i : Fin 2, ∑ k : Fin 2, ∫ x, (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x *
          (S k i ((hD i).toLp _) : (Fin 2 → ℝ) → ℝ) x :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hA i k
      _ = ∑ k : Fin 2, ∑ i : Fin 2, ∫ x, (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x *
          (S k i ((hD i).toLp _) : (Fin 2 → ℝ) → ℝ) x := Finset.sum_comm
      _ = ∑ k : Fin 2, ∫ x, (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ k x :=
          Finset.sum_congr rfl fun k _ => hk k
  have hAint : ∫ x, ∑ i : Fin 2, (rieszOrth_f hF i : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x =
      ∑ k : Fin 2, ∫ x, (rieszOrth_f hF k : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ k x :=
    integral_finset_sum _ fun i _ => hfD i
  have hBint : Integrable (fun x => ∑ i : Fin 2, ∑ k : Fin 2, (S i k (rieszOrth_f hF k) : (Fin 2 → ℝ) → ℝ) x *
      rieszDiv_D φ i x) volume :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ => hTD i k
  have hAint_int : Integrable (fun x => ∑ i : Fin 2, (rieszOrth_f hF i : (Fin 2 → ℝ) → ℝ) x *
      rieszDiv_D φ i x) volume :=
    integrable_finset_sum _ fun i _ => hfD i
  have hQint : Integrable (fun x => ∑ i : Fin 2, ((rieszOrth_f hF i - ∑ k, S i k (rieszOrth_f hF k) :
      PlaneL2) : (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x) volume :=
    (hAint_int.sub hBint).congr (hA_ae.mono fun x hx => hx.symm)
  have hQ0 : ∫ x, ∑ i : Fin 2, ((rieszOrth_f hF i - ∑ k, S i k (rieszOrth_f hF k) : PlaneL2) :
      (Fin 2 → ℝ) → ℝ) x * rieszDiv_D φ i x = 0 := by
    rw [integral_congr_ae hA_ae, integral_sub hAint_int hBint, hAint, hB, sub_self]
  -- transport back to `ℝ²`
  have hmp := volume_preserving_finTwoArrow ℝ
  refine ⟨?_, ?_⟩
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (g := fun z : ℝ × ℝ => planeRieszG S F z 0 * fderiv ℝ φ z (1, 0) +
        planeRieszG S F z 1 * fderiv ℝ φ z (0, 1))).1
      (hQint.congr (Filter.Eventually.of_forall fun x => (hint_eq x).symm))
  · have key := hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun z : ℝ × ℝ => planeRieszG S F z 0 * fderiv ℝ φ z (1, 0) + planeRieszG S F z 1 * fderiv ℝ φ z (0, 1))
    simp only at key
    rw [← key, integral_congr_ae (Filter.Eventually.of_forall fun x => hint_eq x), hQ0]

end UnforcedLeray.Short.IIb
