import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2
import UnforcedLeray.Units.B0411.Separation
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# `PartII-b:T10/org/2/2`: spatial slices are orthogonal to spatial tests (a.e. phase)

Target `solSepSliceOrth : SolSepSliceOrth` (`Sub/PartII-b_T10_org_2.lean`).
Source `the November 2 reference manuscript` 1409-1412, 1498-1500.

Proof outline.
1. For `Ψ` a spatial solenoidal test and `n : ℤ`, `Φ(τ,y) = e_n(τ) Ψ(y)` is a solenoidal phase test.
   Its pairing with `s` is the Fourier coefficient of `h_Ψ(τ) := ⟪Ψ, s(τ)⟫`, so `h_Ψ = 0` a.e.
   (`ae_eq_zero_of_fourier`).
2. A countable family `D` of spatial tests, dense in the sup norm on balls with the supports
   in the balls, gives `h_Ψ(τ) = 0` for all `Ψ ∈ D` at a.e. `τ`.
3. For a fixed good `τ`, `Ψ ↦ h_Ψ(τ)` is Lipschitz in the sup norm on balls (with constant the
   `L¹`-norm of `s(τ)` on the ball), so it vanishes on all spatial tests.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Vanishing outside the closed ball of radius `n`. -/
def o2Outside (n : ℕ) (Ψ : Space → CVec3) : Prop :=
  ∀ y : Space, (n : ℝ) < ‖y‖ → Ψ y = 0

theorem o2Cont {Ψ : Space → CVec3} (h : SpatialSolTest Ψ) : Continuous Ψ := by
  obtain ⟨h1, -, -⟩ := h
  exact h1.continuous

theorem o2MemLp {Ψ : Space → CVec3} (h : SpatialSolTest Ψ) (r : ℝ≥0∞) : MemLp Ψ r volume := by
  obtain ⟨h1, hc, -⟩ := h
  exact h1.continuous.memLp_of_hasCompactSupport hc

theorem o2CD {Ψ : Space → CVec3} (h : SpatialSolTest Ψ) : ContDiff ℝ ∞ Ψ := by
  obtain ⟨h1, -, -⟩ := h
  exact h1

theorem o2Outside_exists {Ψ : Space → CVec3} (h : SpatialSolTest Ψ) : ∃ n : ℕ, o2Outside n Ψ := by
  obtain ⟨-, hc, -⟩ := h
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Space)
  obtain ⟨n, hrn⟩ := exists_nat_ge r
  refine ⟨n, fun y hy => ?_⟩
  by_contra hne
  have hyt : y ∈ tsupport Ψ := subset_tsupport _ (Function.mem_support.2 hne)
  have h1 := hr hyt
  rw [mem_closedBall_zero_iff] at h1
  linarith

/-! ### The countable family -/

/-- Spatial solenoidal tests vanishing outside the ball of radius `n`. -/
def o2Sn (n : ℕ) : Set (Space → CVec3) := {Ψ | SpatialSolTest Ψ ∧ o2Outside n Ψ}

theorem o2Sn_mem {n : ℕ} {Ψ : Space → CVec3} (h : Ψ ∈ o2Sn n) :
    SpatialSolTest Ψ ∧ o2Outside n Ψ := h

theorem o2Zero : SpatialSolTest (0 : Space → CVec3) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, fun y => ?_⟩
  show ∑ j : Fin 3, fderiv ℝ (fun _ : Space => (0 : CVec3)) y (EuclideanSpace.single j (1 : ℝ)) j = 0
  simp

instance o2Nonempty (n : ℕ) : Nonempty (o2Sn n) :=
  ⟨⟨0, show SpatialSolTest (0 : Space → CVec3) ∧ o2Outside n 0 from ⟨o2Zero, fun _ _ => rfl⟩⟩⟩

abbrev o2Eb (n : ℕ) : Type := C(Metric.closedBall (0 : Space) (n : ℝ), CVec3)

instance o2CompactBall (n : ℕ) : CompactSpace (Metric.closedBall (0 : Space) (n : ℝ)) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

def o2Fb (n : ℕ) (Ψ : o2Sn n) : o2Eb n :=
  ⟨fun y => Ψ.1 y.1, (o2Cont (o2Sn_mem Ψ.2).1).comp continuous_subtype_val⟩

theorem o2Dense (n : ℕ) :
    ∃ T : Set (o2Eb n), T ⊆ Set.range (o2Fb n) ∧ T.Countable ∧ Set.range (o2Fb n) ⊆ closure T := by
  have hsep : TopologicalSpace.IsSeparable (Set.range (o2Fb n)) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  exact hsep.exists_countable_dense_subset

theorem o2Approx (n : ℕ) :
    ∃ Dn : Set (Space → CVec3), Dn.Countable ∧ (∀ Ψ ∈ Dn, Ψ ∈ o2Sn n) ∧
      ∀ Ψ ∈ o2Sn n, ∀ ε : ℝ, 0 < ε → ∃ Ψ' ∈ Dn, ∀ y ∈ Metric.closedBall (0 : Space) (n : ℝ),
        dist (Ψ y) (Ψ' y) < ε := by
  obtain ⟨T, hTs, hTc, hTd⟩ := o2Dense n
  refine ⟨(fun g => (Function.invFun (o2Fb n) g).1) '' T, hTc.image _, ?_, ?_⟩
  · rintro Ψ ⟨g, _, rfl⟩
    exact (Function.invFun (o2Fb n) g).2
  · intro Ψ hΨ ε hε
    have hcl : o2Fb n ⟨Ψ, hΨ⟩ ∈ closure T := hTd ⟨⟨Ψ, hΨ⟩, rfl⟩
    obtain ⟨g, hgT, hdist⟩ := Metric.mem_closure_iff.1 hcl ε hε
    obtain ⟨a, ha⟩ := hTs hgT
    have hinv : o2Fb n (Function.invFun (o2Fb n) g) = g := Function.invFun_eq ⟨a, ha⟩
    refine ⟨(Function.invFun (o2Fb n) g).1, ⟨g, hgT, rfl⟩, fun y hy => ?_⟩
    have h4 : dist (o2Fb n ⟨Ψ, hΨ⟩) (o2Fb n (Function.invFun (o2Fb n) g)) < ε := by
      rw [hinv]
      exact hdist
    exact lt_of_le_of_lt
      (ContinuousMap.dist_apply_le_dist (f := o2Fb n ⟨Ψ, hΨ⟩)
        (g := o2Fb n (Function.invFun (o2Fb n) g)) ⟨y, hy⟩) h4

theorem o2ExistsD : ∃ D : Set (Space → CVec3), D.Countable ∧ (∀ Ψ ∈ D, SpatialSolTest Ψ) ∧
    ∀ n : ℕ, ∀ Ψ : Space → CVec3, Ψ ∈ o2Sn n → ∀ ε : ℝ, 0 < ε → ∃ Ψ' ∈ D, o2Outside n Ψ' ∧
      ∀ y ∈ Metric.closedBall (0 : Space) (n : ℝ), dist (Ψ y) (Ψ' y) < ε := by
  choose Dn hDc hDsub hDapp using o2Approx
  refine ⟨⋃ n, Dn n, Set.countable_iUnion hDc, ?_, ?_⟩
  · intro Ψ hΨ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hΨ
    exact (o2Sn_mem (hDsub n Ψ hn)).1
  · intro n Ψ hΨ ε hε
    obtain ⟨Ψ', hΨ'D, hΨ'close⟩ := hDapp n Ψ hΨ ε hε
    exact ⟨Ψ', Set.mem_iUnion.2 ⟨n, hΨ'D⟩, (o2Sn_mem (hDsub n Ψ' hΨ'D)).2, hΨ'close⟩

/-! ### Solenoidal product phase tests -/

theorem o2FourierCD (P : ℝ) [Fact (0 < P)] (n : ℤ) :
    ContDiff ℝ ∞ (fun t : ℝ => fourier n (t : AddCircle P)) := by
  have h1 : (fun t : ℝ => fourier n (t : AddCircle P)) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * (t : ℂ) / P) := by
    funext t
    exact fourier_coe_apply
  rw [h1]
  exact Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _)

theorem o2DyFourier (P : ℝ) [Fact (0 < P)] (n : ℤ) {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ)
    (x : ℝ × Space) (j : Fin 3) :
    dy j (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) x =
      fourier n (x.1 : AddCircle P) • fderiv ℝ Ψ x.2 (EuclideanSpace.single j (1 : ℝ)) := by
  have hc : Differentiable ℝ (fun t : ℝ => fourier n (t : AddCircle P)) :=
    (o2FourierCD P n).differentiable (by simp)
  have hΨd : Differentiable ℝ Ψ := (o2CD hΨ).differentiable (by simp)
  have hcf := ((hc x.1).hasFDerivAt).comp x hasFDerivAt_fst
  have hΨs := ((hΨd x.2).hasFDerivAt).comp x hasFDerivAt_snd
  have hD : HasFDerivAt (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) _ x :=
    hcf.smul hΨs
  unfold dy
  rw [hD.fderiv]
  simp [coordinateVector]


theorem o2IsSolTest (P : ℝ) [Fact (0 < P)] (n : ℤ) {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ) :
    Cons.C03.Concrete.IsSolTest P (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) := by
  obtain ⟨n0, hn0⟩ := o2Outside_exists hΨ
  have hd : ∀ x : Space, ∑ j : Fin 3, fderiv ℝ Ψ x (EuclideanSpace.single j (1 : ℝ)) j = 0 := by
    obtain ⟨-, -, h3⟩ := hΨ
    exact h3
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact ContDiff.smul ((o2FourierCD P n).comp contDiff_fst) ((o2CD hΨ).comp contDiff_snd)
  · intro τ y
    simp
  · exact ⟨(n0 : ℝ), fun τ y hy => by simp [o2Outside, hn0 y hy]⟩
  · intro x
    simp only [o2DyFourier P n hΨ]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hd x.2, mul_zero]

theorem o2PhasePair (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (n : ℤ) {Ψ : Space → CVec3}
    (hΨ : SpatialSolTest Ψ) (s : Yq P q) :
    phasePair P q (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) s =
      ∫ τ : AddCircle P, fourier n τ * innerPair q ((o2MemLp hΨ (conjExp q)).toLp _) (s τ)
        ∂AddCircle.haarAddCircle := by
  have hΦ : IsPhaseTest P (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2) :=
    (o2IsSolTest P n hΨ).1
  have hs' := hΦ.isSliceTest (conjExp q)
  have hslice : ∀ τ : AddCircle P,
      circleSlice hs' τ = fourier n τ • (o2MemLp hΨ (conjExp q)).toLp _ := by
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
  rw [hτ, hslice τ, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem o2Fourier (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (s : Yq P q)
    (hs : ∀ Φ : ℝ × Space → CVec3, Cons.C03.Concrete.IsSolTest P Φ → phasePair P q Φ s = 0)
    (n : ℤ) {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ) :
    ∫ τ : AddCircle P, fourier n τ * innerPair q ((o2MemLp hΨ (conjExp q)).toLp _) (s τ)
      ∂AddCircle.haarAddCircle = 0 := by
  rw [← o2PhasePair P q n hΨ s]
  exact hs _ (o2IsSolTest P n hΨ)

theorem o2SliceAe (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (s : Yq P q)
    (hs : ∀ Φ : ℝ × Space → CVec3, Cons.C03.Concrete.IsSolTest P Φ → phasePair P q Φ s = 0)
    {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∫ y, dotL (Ψ y) ((s τ : Space → CVec3) y) = 0 := by
  have hint : Integrable
      (fun τ : AddCircle P => innerPair q ((o2MemLp hΨ (conjExp q)).toLp _) (s τ))
      AddCircle.haarAddCircle :=
    (innerPair q ((o2MemLp hΨ (conjExp q)).toLp _)).integrable_comp (integrable_Yq s)
  have hz := ae_eq_zero_of_fourier hint (fun n => o2Fourier P q s hs n hΨ)
  filter_upwards [hz] with τ hτ
  have e : innerPair q ((o2MemLp hΨ (conjExp q)).toLp _) (s τ) =
      ∫ y, dotL (Ψ y) ((s τ : Space → CVec3) y) := by
    rw [innerPair_apply]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (o2MemLp hΨ (conjExp q))] with y hy
    rw [hy]
  rw [← e]
  exact hτ

theorem o2BallEq {Ψ g : Space → CVec3} {n : ℕ} (hΨ : o2Outside n Ψ) :
    ∫ y in Metric.closedBall (0 : Space) (n : ℝ), dotL (Ψ y) (g y) =
      ∫ y, dotL (Ψ y) (g y) := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have hy' : (n : ℝ) < ‖y‖ := not_le.1 fun h => hy (mem_closedBall_zero_iff.2 h)
  simp [hΨ y hy']

theorem o2IntegrableBall {g : Space → CVec3} {n : ℕ}
    (hg : IntegrableOn g (Metric.closedBall (0 : Space) (n : ℝ)))
    {Ψ : Space → CVec3} (hΨc : Continuous Ψ) :
    IntegrableOn (fun y => dotL (Ψ y) (g y)) (Metric.closedBall (0 : Space) (n : ℝ)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space) (n : ℝ)).exists_bound_of_continuousOn
    hΨc.continuousOn
  refine Integrable.mono' (hg.norm.const_mul (‖dotL‖ * M)) ?_ ?_
  · exact ContinuousLinearMap.aestronglyMeasurable_comp₂ dotL hΨc.aestronglyMeasurable
      hg.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_closedBall).2 (ae_of_all _ fun y hy => ?_)
    calc ‖dotL (Ψ y) (g y)‖ ≤ ‖dotL‖ * ‖Ψ y‖ * ‖g y‖ := ContinuousLinearMap.le_opNorm₂ dotL _ _
      _ ≤ ‖dotL‖ * M * ‖g y‖ := by
        gcongr
        exact hM y hy

theorem o2Estimate {g : Space → CVec3} {n : ℕ}
    (hg : IntegrableOn g (Metric.closedBall (0 : Space) (n : ℝ)))
    {Ψ Ψ' : Space → CVec3} (hΨc : Continuous Ψ) (hΨ'c : Continuous Ψ') {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ y ∈ Metric.closedBall (0 : Space) (n : ℝ), dist (Ψ y) (Ψ' y) ≤ δ) :
    ‖(∫ y in Metric.closedBall (0 : Space) (n : ℝ), dotL (Ψ y) (g y)) -
        ∫ y in Metric.closedBall (0 : Space) (n : ℝ), dotL (Ψ' y) (g y)‖ ≤
      ‖dotL‖ * δ * ∫ y in Metric.closedBall (0 : Space) (n : ℝ), ‖g y‖ := by
  have hI := o2IntegrableBall hg hΨc
  have hI' := o2IntegrableBall hg hΨ'c
  rw [← integral_sub hI hI']
  have hbd : ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) (n : ℝ))),
      ‖dotL (Ψ y) (g y) - dotL (Ψ' y) (g y)‖ ≤ ‖dotL‖ * δ * ‖g y‖ := by
    refine (ae_restrict_iff' measurableSet_closedBall).2 (ae_of_all _ fun y hy => ?_)
    have e : dotL (Ψ y) (g y) - dotL (Ψ' y) (g y) = dotL (Ψ y - Ψ' y) (g y) := by
      rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [e]
    calc ‖dotL (Ψ y - Ψ' y) (g y)‖ ≤ ‖dotL‖ * ‖Ψ y - Ψ' y‖ * ‖g y‖ :=
          ContinuousLinearMap.le_opNorm₂ dotL _ _
      _ ≤ ‖dotL‖ * δ * ‖g y‖ := by
        rw [← dist_eq_norm]
        gcongr
        exact hδ y hy
  calc _ ≤ ∫ y, ‖dotL‖ * δ * ‖g y‖ ∂(volume.restrict (Metric.closedBall (0 : Space) (n : ℝ))) :=
        norm_integral_le_of_norm_le (hg.norm.const_mul (‖dotL‖ * δ)) hbd
    _ = ‖dotL‖ * δ * ∫ y in Metric.closedBall (0 : Space) (n : ℝ), ‖g y‖ :=
        integral_const_mul _ _

theorem solSepSliceOrth : SolSepSliceOrth := by
  intro q _ P _ s hs
  obtain ⟨D, hDc, hDS, hDapp⟩ := o2ExistsD
  have hB : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ Ψ ∈ D,
      ∫ y, dotL (Ψ y) ((s τ : Space → CVec3) y) = 0 := by
    rw [ae_ball_iff hDc]
    intro Ψ hΨ
    exact o2SliceAe P q s hs (hDS Ψ hΨ)
  filter_upwards [hB] with τ hτ
  intro Ψ hΨ
  obtain ⟨n, hn⟩ := o2Outside_exists hΨ
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) (n : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have hg : IntegrableOn (fun y => (s τ : Space → CVec3) y)
      (Metric.closedBall (0 : Space) (n : ℝ)) :=
    MemLp.integrable hq1 ((Lp.memLp (s τ)).restrict _)
  have hK0 : 0 ≤ ∫ y in Metric.closedBall (0 : Space) (n : ℝ), ‖(s τ : Space → CVec3) y‖ :=
    setIntegral_nonneg measurableSet_closedBall (fun y _ => norm_nonneg _)
  have hC0 : 0 ≤ ‖dotL‖ := by positivity
  have key : ∀ ε : ℝ, 0 < ε →
      ‖∫ y in Metric.closedBall (0 : Space) (n : ℝ), dotL (Ψ y) ((s τ : Space → CVec3) y)‖ ≤ ε := by
    intro ε hε
    have hCK := mul_nonneg hC0 hK0
    have hpos : 0 < ε / (‖dotL‖ * (∫ y in Metric.closedBall (0 : Space) (n : ℝ),
        ‖(s τ : Space → CVec3) y‖) + 1) := div_pos hε (by linarith)
    obtain ⟨Ψ', hΨ'D, hΨ'o, hΨ'close⟩ := hDapp n Ψ (show Ψ ∈ o2Sn n from ⟨hΨ, hn⟩) _ hpos
    have hest := o2Estimate hg (o2Cont hΨ) (o2Cont (hDS Ψ' hΨ'D)) hpos.le
      (fun y hy => (hΨ'close y hy).le)
    rw [o2BallEq hΨ'o, hτ Ψ' hΨ'D, sub_zero] at hest
    have hfin : ‖dotL‖ * (ε / (‖dotL‖ * (∫ y in Metric.closedBall (0 : Space) (n : ℝ),
        ‖(s τ : Space → CVec3) y‖) + 1)) * (∫ y in Metric.closedBall (0 : Space) (n : ℝ),
        ‖(s τ : Space → CVec3) y‖) ≤ ε := by
      set K := ∫ y in Metric.closedBall (0 : Space) (n : ℝ), ‖(s τ : Space → CVec3) y‖
      have h1 : ‖dotL‖ * (ε / (‖dotL‖ * K + 1)) * K = ε * ((‖dotL‖ * K) / (‖dotL‖ * K + 1)) := by
        field_simp
      have h2 : (‖dotL‖ * K) / (‖dotL‖ * K + 1) ≤ 1 :=
        (div_le_one (by linarith)).2 (by linarith)
      rw [h1]
      nlinarith
    linarith
  have h0 : ‖∫ y in Metric.closedBall (0 : Space) (n : ℝ), dotL (Ψ y) ((s τ : Space → CVec3) y)‖
      ≤ 0 := le_of_forall_pos_le_add fun ε hε => by linarith [key ε hε]
  rw [← o2BallEq hn]
  exact norm_le_zero_iff.1 h0

end UnforcedLeray.Short.IIb
