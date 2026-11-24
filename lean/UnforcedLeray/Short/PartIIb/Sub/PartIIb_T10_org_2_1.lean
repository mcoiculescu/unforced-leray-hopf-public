import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_2
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# `PartII-b:T10/org/2/1`: slices of a phase-solenoidal field are solenoidal (a.e. phase)

Target `solSepSliceSol : SolSepSliceSol` (`Sub/PartII-b_T10_org_2.lean`).

Proof outline (same architecture as `PartII-b_T10_org_2_2.lean`).
1. For a spatial test `φ` and `n : ℤ`, the scalar phase test `e_n(τ) φ(y)` has
   `gradT = e_n(τ) V_φ(y)` with `V_φ(y) = ∑ᵢ ∂ᵢφ(y) eᵢ`; so the Fourier coefficients of
   `τ ↦ ⟪V_φ, s(τ)⟫` vanish and `⟪V_φ, s(τ)⟫ = 0` for a.e. `τ`.
2. A countable family `D` of spatial tests, dense in the derivative sup norm on balls, makes
   this hold simultaneously for all `φ ∈ D` at a.e. `τ`.
3. Lipschitz estimate on balls in the derivative norm gives the identity for all `φ`, and the
   integrability clause of `IsSolenoidalC` comes from `s(τ) ∈ L^q`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0414

/-! ### Generic support and smoothness -/

theorem o2OutG {F : Type*} [Zero F] [TopologicalSpace F] {Ψ : Space → F}
    (hΨs : HasCompactSupport Ψ) : ∃ n : ℕ, ∀ y : Space, (n : ℝ) < ‖y‖ → Ψ y = 0 := by
  obtain ⟨r, hr⟩ := hΨs.isCompact.isBounded.subset_closedBall (0 : Space)
  obtain ⟨n, hrn⟩ := exists_nat_ge r
  refine ⟨n, fun y hy => ?_⟩
  by_contra hne
  have hyt : y ∈ tsupport Ψ := subset_tsupport _ (Function.mem_support.2 hne)
  have h1 := hr hyt
  rw [mem_closedBall_zero_iff] at h1
  linarith

theorem o2IsPhaseTestG {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (P : ℝ) [Fact (0 < P)]
    (n : ℤ) {Ψ : Space → F} (hΨd : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ) :
    IsPhaseTest P (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) := by
  obtain ⟨n0, hn0⟩ := o2OutG hΨs
  refine ⟨?_, ?_, ⟨(n0 : ℝ), fun τ y hy => by simp [hn0 y hy]⟩⟩
  · exact ContDiff.smul ((o2FourierCD P n).comp contDiff_fst) (hΨd.comp contDiff_snd)
  · intro τ y
    simp

/-! ### Derivative of the product test, general codomain -/

theorem o2DyG {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (P : ℝ) [Fact (0 < P)]
    (n : ℤ) {Ψ : Space → F} (hΨd : Differentiable ℝ Ψ) (x : ℝ × Space) (j : Fin 3) :
    dy j (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) x =
      fourier n (x.1 : AddCircle P) • fderiv ℝ Ψ x.2 (EuclideanSpace.single j (1 : ℝ)) := by
  have hc : Differentiable ℝ (fun t : ℝ => fourier n (t : AddCircle P)) :=
    (o2FourierCD P n).differentiable (by simp)
  have hcf := ((hc x.1).hasFDerivAt).comp x hasFDerivAt_fst
  have hΨs := ((hΨd x.2).hasFDerivAt).comp x hasFDerivAt_snd
  have hD : HasFDerivAt (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) _ x :=
    hcf.smul hΨs
  unfold dy
  rw [hD.fderiv]
  simp [coordinateVector]

/-! ### Pairing with the product test, general spatial profile -/

theorem o2MemLpC {Ψ : Space → CVec3} (hc : Continuous Ψ) (hs : HasCompactSupport Ψ) (r : ℝ≥0∞) :
    MemLp Ψ r volume :=
  hc.memLp_of_hasCompactSupport hs

theorem o2PhasePairG (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (n : ℤ)
    {Ψ : Space → CVec3} (hΨd : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ) (s : Yq P q) :
    phasePair P q (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) s =
      ∫ τ : AddCircle P, fourier n τ * innerPair q
        ((o2MemLpC hΨd.continuous hΨs (conjExp q)).toLp _) (s τ) ∂AddCircle.haarAddCircle := by
  have hΦ : IsPhaseTest P (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) :=
    o2IsPhaseTestG P n hΨd hΨs
  have hs' := hΦ.isSliceTest (conjExp q)
  have hslice : ∀ τ : AddCircle P,
      circleSlice hs' τ = fourier n τ • (o2MemLpC hΨd.continuous hΨs (conjExp q)).toLp _ := by
    intro τ
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      rw [circleSlice_coe, sliceMap, ← MemLp.toLp_const_smul]
      apply MemLp.toLp_congr
      exact Eventually.of_forall fun y => rfl
  rw [phasePair, phasePairing_apply, testElem_of hs']
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp q) (volume : Measure Space))
    (p := conjExp q) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs')] with τ hτ
  rw [hτ, hslice τ, map_smul, smul_apply, smul_eq_mul]

theorem o2AeG (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (s : Yq P q)
    {Ψ : Space → CVec3} (hΨd : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ)
    (h : ∀ n : ℤ, phasePair P q (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) s = 0) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∫ y, dotL (Ψ y) ((s τ : Space → CVec3) y) = 0 := by
  have hint : Integrable
      (fun τ : AddCircle P => innerPair q ((o2MemLpC hΨd.continuous hΨs (conjExp q)).toLp _) (s τ))
      AddCircle.haarAddCircle :=
    (innerPair q ((o2MemLpC hΨd.continuous hΨs (conjExp q)).toLp _)).integrable_comp
      (integrable_Yq s)
  have hz := ae_eq_zero_of_fourier hint (fun n => by
    rw [← o2PhasePairG P q n hΨd hΨs]
    exact h n)
  filter_upwards [hz] with τ hτ
  have e : innerPair q ((o2MemLpC hΨd.continuous hΨs (conjExp q)).toLp _) (s τ) =
      ∫ y, dotL (Ψ y) ((s τ : Space → CVec3) y) := by
    rw [innerPair_apply]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (o2MemLpC hΨd.continuous hΨs (conjExp q))] with y hy
    rw [hy]
  rw [← e]
  exact hτ

/-! ### The vector field `V_φ = ∑ᵢ ∂ᵢφ eᵢ` of a spatial test -/

/-- The gradient `V_φ(y) = ∑ᵢ ∂ᵢφ(y) eᵢ ∈ ℂ³` of a real spatial test. -/
def o2V (φ : Space → ℝ) (y : Space) : CVec3 :=
  ∑ i : Fin 3, ((spatialTestDerivative i φ y : ℝ) : ℂ) • EuclideanSpace.single i (1 : ℂ)

theorem o2V_apply (φ : Space → ℝ) (y : Space) (k : Fin 3) :
    o2V φ y k = ((spatialTestDerivative k φ y : ℝ) : ℂ) := by
  simp [o2V, Finset.sum_apply, Pi.single_apply]

theorem o2V_contDiff (φ : Space → ℝ) (hφ : IsSpatialTest φ) : ContDiff ℝ ∞ (o2V φ) := by
  unfold o2V
  refine ContDiff.sum fun i _ => ?_
  have h1 : ContDiff ℝ ∞ (fun y : Space => ((spatialTestDerivative i φ y : ℝ) : ℂ)) := by
    refine Complex.ofRealCLM.contDiff.comp ?_
    exact (hφ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact h1.smul contDiff_const

theorem o2V_compact (φ : Space → ℝ) (hφ : IsSpatialTest φ) : HasCompactSupport (o2V φ) := by
  have hc := hφ.compact.fderiv (𝕜 := ℝ)
  refine HasCompactSupport.intro hc.isCompact (fun y hy => ?_)
  have h0 : fderiv ℝ φ y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [o2V, spatialTestDerivative, h0]

theorem o2V_zero_of {φ : Space → ℝ} {y : Space} (h0 : fderiv ℝ φ y = 0) : o2V φ y = 0 := by
  simp [o2V, spatialTestDerivative, h0]

theorem o2Vdist (φ φ' : Space → ℝ) (y : Space) :
    dist (o2V φ y) (o2V φ' y) ≤ 3 * ‖fderiv ℝ φ y - fderiv ℝ φ' y‖ := by
  rw [dist_eq_norm]
  unfold o2V
  rw [← Finset.sum_sub_distrib]
  set D := fderiv ℝ φ y - fderiv ℝ φ' y with hD
  have hterm : ∀ i : Fin 3,
      ‖((spatialTestDerivative i φ y : ℝ) : ℂ) • EuclideanSpace.single i (1 : ℂ) -
        ((spatialTestDerivative i φ' y : ℝ) : ℂ) • EuclideanSpace.single i (1 : ℂ)‖ ≤ ‖D‖ := by
    intro i
    rw [← sub_smul, ← Complex.ofReal_sub, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Complex.norm_real]
    have e : spatialTestDerivative i φ y - spatialTestDerivative i φ' y =
        D (EuclideanSpace.single i (1 : ℝ)) := by
      simp [hD, spatialTestDerivative, coordinateVector]
    rw [e, Real.norm_eq_abs]
    have := ContinuousLinearMap.le_opNorm D (EuclideanSpace.single i (1 : ℝ))
    rw [EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs] at this
    exact this
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _i : Fin 3, ‖D‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = 3 * ‖D‖ := by simp

/-- `dotL` is symmetric. -/
theorem o2dotL_comm (a b : CVec3) : dotL a b = dotL b a := by
  rw [dotL_apply, dotL_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ### Gradient of the scalar product test -/

theorem o2FDerivOfReal (φ : Space → ℝ) (y : Space) (hφ : DifferentiableAt ℝ φ y) (v : Space) :
    fderiv ℝ (fun z => ((φ z : ℝ) : ℂ)) y v = ((fderiv ℝ φ y v : ℝ) : ℂ) := by
  have h : fderiv ℝ (fun z => ((φ z : ℝ) : ℂ)) y =
      Complex.ofRealCLM.comp (fderiv ℝ φ y) :=
    (Complex.ofRealCLM.hasFDerivAt.comp y hφ.hasFDerivAt).fderiv
  rw [h]
  simp

theorem o2Grad (P : ℝ) [Fact (0 < P)] (n : ℤ) {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    gradT (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • ((φ p.2 : ℝ) : ℂ)) =
      fun p => fourier n (p.1 : AddCircle P) • o2V φ p.2 := by
  have hdφ : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hd : Differentiable ℝ (fun z : Space => ((φ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp hdφ
  funext p
  unfold gradT
  simp only [o2DyG P n hd]
  simp only [o2FDerivOfReal φ _ (hdφ _), o2V, Finset.smul_sum, smul_smul]
  rfl

/-! ### Countable dense family in the derivative norm -/

def o2OutR (n : ℕ) (φ : Space → ℝ) : Prop := ∀ y : Space, (n : ℝ) < ‖y‖ → φ y = 0

def o2SnR (n : ℕ) : Set (Space → ℝ) := {φ | IsSpatialTest φ ∧ o2OutR n φ}

theorem o2SnR_mem {n : ℕ} {φ : Space → ℝ} (h : φ ∈ o2SnR n) : IsSpatialTest φ ∧ o2OutR n φ := h

theorem o2fderivVanish {φ : Space → ℝ} {n : ℕ} (h : o2OutR n φ) {y : Space}
    (hy : (n : ℝ) < ‖y‖) : fderiv ℝ φ y = 0 := by
  have hev : φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact h z hz
  rw [hev.fderiv_eq]
  simp

theorem o2ZeroR : IsSpatialTest (0 : Space → ℝ) := ⟨contDiff_const, HasCompactSupport.zero⟩

instance o2NonemptySnR (n : ℕ) : Nonempty (o2SnR n) :=
  ⟨⟨0, show IsSpatialTest (0 : Space → ℝ) ∧ o2OutR n 0 from ⟨o2ZeroR, fun _ _ => rfl⟩⟩⟩

abbrev o2EbR (n : ℕ) : Type := C(Metric.closedBall (0 : Space) (n : ℝ), Space →L[ℝ] ℝ)

def o2FbR (n : ℕ) (φ : o2SnR n) : o2EbR n :=
  ⟨fun y => fderiv ℝ φ.1 y.1,
    ((o2SnR_mem φ.2).1.smooth.continuous_fderiv (by simp)).comp continuous_subtype_val⟩

theorem o2DenseR (n : ℕ) :
    ∃ T : Set (o2EbR n), T ⊆ Set.range (o2FbR n) ∧ T.Countable ∧
      Set.range (o2FbR n) ⊆ closure T := by
  have hsep : TopologicalSpace.IsSeparable (Set.range (o2FbR n)) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  exact hsep.exists_countable_dense_subset

theorem o2ApproxR (n : ℕ) :
    ∃ Dn : Set (Space → ℝ), Dn.Countable ∧ (∀ φ ∈ Dn, φ ∈ o2SnR n) ∧
      ∀ φ ∈ o2SnR n, ∀ ε : ℝ, 0 < ε → ∃ φ' ∈ Dn, ∀ y ∈ Metric.closedBall (0 : Space) (n : ℝ),
        dist (fderiv ℝ φ y) (fderiv ℝ φ' y) < ε := by
  obtain ⟨T, hTs, hTc, hTd⟩ := o2DenseR n
  refine ⟨(fun g => (Function.invFun (o2FbR n) g).1) '' T, hTc.image _, ?_, ?_⟩
  · rintro φ ⟨g, _, rfl⟩
    exact (Function.invFun (o2FbR n) g).2
  · intro φ hφ ε hε
    have hcl : o2FbR n ⟨φ, hφ⟩ ∈ closure T := hTd ⟨⟨φ, hφ⟩, rfl⟩
    obtain ⟨g, hgT, hdist⟩ := (Metric.mem_closure_iff (α := o2EbR n)).1 hcl ε hε
    obtain ⟨a, ha⟩ := hTs hgT
    have hinv : o2FbR n (Function.invFun (o2FbR n) g) = g := Function.invFun_eq ⟨a, ha⟩
    refine ⟨(Function.invFun (o2FbR n) g).1, ⟨g, hgT, rfl⟩, fun y hy => ?_⟩
    have h4 : dist (o2FbR n ⟨φ, hφ⟩) (o2FbR n (Function.invFun (o2FbR n) g)) < ε := by
      rw [hinv]
      exact hdist
    exact lt_of_le_of_lt
      (ContinuousMap.dist_apply_le_dist (f := o2FbR n ⟨φ, hφ⟩)
        (g := o2FbR n (Function.invFun (o2FbR n) g)) ⟨y, hy⟩) h4

theorem o2ExistsDR : ∃ D : Set (Space → ℝ), D.Countable ∧ (∀ φ ∈ D, IsSpatialTest φ) ∧
    ∀ n : ℕ, ∀ φ : Space → ℝ, φ ∈ o2SnR n → ∀ ε : ℝ, 0 < ε → ∃ φ' ∈ D, o2OutR n φ' ∧
      ∀ y ∈ Metric.closedBall (0 : Space) (n : ℝ), dist (fderiv ℝ φ y) (fderiv ℝ φ' y) < ε := by
  choose Dn hDc hDsub hDapp using o2ApproxR
  refine ⟨⋃ n, Dn n, Set.countable_iUnion hDc, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hφ
    exact (o2SnR_mem (hDsub n φ hn)).1
  · intro n φ hφ ε hε
    obtain ⟨φ', hφ'D, hφ'close⟩ := hDapp n φ hφ ε hε
    exact ⟨φ', Set.mem_iUnion.2 ⟨n, hφ'D⟩, (o2SnR_mem (hDsub n φ' hφ'D)).2, hφ'close⟩

/-! ### The Lipschitz limit argument -/

theorem o2VOut {φ : Space → ℝ} {n : ℕ} (h : o2OutR n φ) : o2Outside n (o2V φ) :=
  fun _ hy => o2V_zero_of (o2fderivVanish h hy)

theorem o2Eps (C K ε : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hε : 0 < ε) :
    C * (3 * (ε / (3 * (C * K + 1)))) * K ≤ ε := by
  have hpos : 0 < C * K + 1 := by nlinarith [mul_nonneg hC hK]
  have h1 : C * (3 * (ε / (3 * (C * K + 1)))) * K = ε * ((C * K) / (C * K + 1)) := by
    field_simp
  rw [h1]
  have h2 : (C * K) / (C * K + 1) ≤ 1 := (div_le_one hpos).2 (by linarith)
  nlinarith

theorem o2Limit (D : Set (Space → ℝ)) (hDS : ∀ φ ∈ D, IsSpatialTest φ)
    (hDapp : ∀ n : ℕ, ∀ φ : Space → ℝ, φ ∈ o2SnR n → ∀ ε : ℝ, 0 < ε → ∃ φ' ∈ D, o2OutR n φ' ∧
      ∀ y ∈ Metric.closedBall (0 : Space) (n : ℝ), dist (fderiv ℝ φ y) (fderiv ℝ φ' y) < ε)
    (g : Space → CVec3) (hg : ∀ n : ℕ, IntegrableOn g (Metric.closedBall (0 : Space) (n : ℝ)))
    (hz : ∀ φ' ∈ D, ∫ y, dotL (o2V φ' y) (g y) = 0)
    (φ : Space → ℝ) (hφ : IsSpatialTest φ) : ∫ y, dotL (o2V φ y) (g y) = 0 := by
  obtain ⟨n, hn⟩ := o2OutG hφ.compact
  rw [← o2BallEq (o2VOut hn)]
  have hC0 : 0 ≤ ‖dotL‖ := by positivity
  have hK0 : 0 ≤ ∫ y in Metric.closedBall (0 : Space) (n : ℝ), ‖g y‖ :=
    setIntegral_nonneg measurableSet_closedBall (fun y _ => norm_nonneg _)
  have key : ∀ ε : ℝ, 0 < ε →
      ‖∫ y in Metric.closedBall (0 : Space) (n : ℝ), dotL (o2V φ y) (g y)‖ ≤ ε := by
    intro ε hε
    have hpos : 0 < ε / (3 * (‖dotL‖ * (∫ y in Metric.closedBall (0 : Space) (n : ℝ),
        ‖g y‖) + 1)) := div_pos hε (by nlinarith [mul_nonneg hC0 hK0])
    obtain ⟨φ', hφ'D, hφ'o, hφ'close⟩ := hDapp n φ ⟨hφ, hn⟩ _ hpos
    have hest := o2Estimate (hg n) (o2V_contDiff φ hφ).continuous
      (o2V_contDiff φ' (hDS φ' hφ'D)).continuous (δ := 3 * (ε / (3 * (‖dotL‖ * (∫ y in
        Metric.closedBall (0 : Space) (n : ℝ), ‖g y‖) + 1)))) (by positivity)
      (fun y hy => by
        refine (o2Vdist φ φ' y).trans ?_
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left (hφ'close y hy).le (by norm_num))
    rw [o2BallEq (o2VOut hφ'o), hz φ' hφ'D, sub_zero] at hest
    have := o2Eps ‖dotL‖ _ ε hC0 hK0 hε
    linarith
  have h0 : ‖∫ y in Metric.closedBall (0 : Space) (n : ℝ), dotL (o2V φ y) (g y)‖ ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by linarith [key ε hε]
  exact norm_le_zero_iff.1 h0

theorem solSepSliceSol : SolSepSliceSol := by
  intro q _ P _ s hs
  obtain ⟨D, hDc, hDS, hDapp⟩ := o2ExistsDR
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hfour : ∀ φ : Space → ℝ, IsSpatialTest φ → ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      ∫ y, dotL (o2V φ y) ((s τ : Space → CVec3) y) = 0 := by
    intro φ hφ
    refine o2AeG P q s (o2V_contDiff φ hφ) (o2V_compact φ hφ) (fun n => ?_)
    have hΦ : IsPhaseTest P
        (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • ((φ p.2 : ℝ) : ℂ)) :=
      o2IsPhaseTestG P n (Ψ := fun y => ((φ y : ℝ) : ℂ))
        (Complex.ofRealCLM.contDiff.comp hφ.smooth)
        (hφ.compact.comp_left Complex.ofReal_zero)
    have h1 := hs _ hΦ
    rw [o2Grad P n hφ] at h1
    exact h1
  have hB : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ φ ∈ D,
      ∫ y, dotL (o2V φ y) ((s τ : Space → CVec3) y) = 0 := by
    rw [ae_ball_iff hDc]
    intro φ hφ
    exact hfour φ (hDS φ hφ)
  filter_upwards [hB] with τ hτ
  have hgAll : ∀ n : ℕ, IntegrableOn (fun y => (s τ : Space → CVec3) y)
      (Metric.closedBall (0 : Space) (n : ℝ)) := fun n => by
    haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) (n : ℝ))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
    exact MemLp.integrable hq1 ((Lp.memLp (s τ)).restrict _)
  have hfun : ∀ φ : Space → ℝ,
      (fun x => ∑ i : Fin 3, (s τ : Space → CVec3) x i *
        ((spatialTestDerivative i φ x : ℝ) : ℂ)) =
      fun x => dotL (o2V φ x) ((s τ : Space → CVec3) x) := by
    intro φ
    funext x
    rw [dotL_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [o2V_apply, mul_comm]
  refine ⟨?_, ?_⟩
  · intro φ hφ
    rw [hfun φ]
    obtain ⟨n, hn⟩ := o2OutG hφ.compact
    have hI := o2IntegrableBall (hgAll n) (o2V_contDiff φ hφ).continuous
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 hI
    intro x hx
    by_contra h
    apply hx
    have hxn : (n : ℝ) < ‖x‖ := not_le.1 fun h' => h (mem_closedBall_zero_iff.2 h')
    show dotL (o2V φ x) ((s τ : Space → CVec3) x) = 0
    rw [o2V_zero_of (o2fderivVanish hn hxn), map_zero, ContinuousLinearMap.zero_apply]
  · intro φ hφ
    rw [hfun φ]
    exact o2Limit D hDS hDapp (fun y => (s τ : Space → CVec3) y) hgAll hτ φ hφ

end UnforcedLeray.Short.IIb
