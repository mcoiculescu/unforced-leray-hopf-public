import UnforcedLeray.Units.B0428.Slice
import UnforcedLeray.Units.B0005.Bridge.Realize

/-!
# Slicing a distributional spatial derivative of `Y_q` into the phases

Helper for `Proofs/Wiring/Mode/StressInvH1Grad.lean` (source 1556-1572 `free:weak-stress`:
`∇ S_μ T ∈ Y_2`; 5975-5978: `b, ∇b ∈ Y_2`).  The phase-space identity
`HasPhaseOp (fun Φ => -dy j Φ) w g` (`∂_j w = g` in distributions on `(ℝ/Pℤ) × ℝ³`) holds in
almost every phase, against every spatial test at once (the argument of `B0428.ae_forall_pair`
with the first-order product tests `dy_prodTest`), and the pairing form gives the compiled
`HasWeakSpatialDerivative` for the real parts.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.GradSlice

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0428
open UnforcedLeray.B0411 (prodTest isPhaseTest_prodTest phasePair_prodTest innerPair_spatialTest
  ae_eq_zero_of_fourier integrable_Yq integrable_fourier_smul)
open UnforcedLeray.B0005 (cplxL reL reL_apply cplxL_apply)

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- **One test, almost every phase.** If `∂_j w = g` in distributions on `(ℝ/Pℤ) × ℝ³`, then for
each spatial test `ψ` and component `i`: `⟪∂_jψ eᵢ, w(τ)⟫ = -⟪ψ eᵢ, g(τ)⟫` for a.e. `τ`. -/
theorem ae_slice_grad {j : Fin 3} {w g : Yq P q} (h : HasPhaseOp (fun Φ => -dy j Φ) w g)
    {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) (i : Fin 3) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      innerPair q (sT q (isSpatialTest_sd hψ j) i) (w τ) = -innerPair q (sT q hψ i) (g τ) := by
  set a := sT q (isSpatialTest_sd hψ j) i with ha
  set b := sT q hψ i with hb
  have hint : Integrable (fun τ => innerPair q a (w τ) + innerPair q b (g τ))
      (AddCircle.haarAddCircle (T := P)) :=
    ((innerPair q a).integrable_comp (integrable_Yq w)).add
      ((innerPair q b).integrable_comp (integrable_Yq g))
  have hF : ∀ n : ℤ, ∫ τ, fourier n τ * (innerPair q a (w τ) + innerPair q b (g τ))
      ∂AddCircle.haarAddCircle = 0 := by
    intro n
    have i1 := (innerPair q a).integrable_comp (integrable_fourier_smul w n)
    have i2 := (innerPair q b).integrable_comp (integrable_fourier_smul g n)
    simp only [map_smul, smul_eq_mul] at i1 i2
    have e1 : ∫ τ, fourier n τ * innerPair q a (w τ) ∂AddCircle.haarAddCircle =
        innerPair q a (∫ τ, fourier n τ • w τ ∂AddCircle.haarAddCircle) := by
      rw [← (innerPair q a).integral_comp_comm (integrable_fourier_smul w n)]
      simp only [map_smul, smul_eq_mul]
    have e2 : ∫ τ, fourier n τ * innerPair q b (g τ) ∂AddCircle.haarAddCircle =
        innerPair q b (∫ τ, fourier n τ • g τ ∂AddCircle.haarAddCircle) := by
      rw [← (innerPair q b).integral_comp_comm (integrable_fourier_smul g n)]
      simp only [map_smul, smul_eq_mul]
    have hsd := isSpatialTest_sd hψ j
    have hp : phasePair P q (-dy j (prodTest P n ψ i)) w = phasePair P q (prodTest P n ψ i) g :=
      h _ (isPhaseTest_prodTest n hψ.smooth hψ.compact i)
    rw [dy_prodTest n hψ i j, phasePair_neg (isPhaseTest_prodTest n hsd.smooth hsd.compact i),
      phasePair_prodTest w n hsd.smooth hsd.compact i,
      phasePair_prodTest g n hψ.smooth hψ.compact i] at hp
    have hp' : innerPair q a (∫ τ, fourier n τ • w τ ∂AddCircle.haarAddCircle) =
        -innerPair q b (∫ τ, fourier n τ • g τ ∂AddCircle.haarAddCircle) :=
      neg_eq_iff_eq_neg.mp hp
    simp only [mul_add]
    rw [integral_add i1 i2, e1, e2, hp', neg_add_cancel]
  filter_upwards [ae_eq_zero_of_fourier hint hF] with τ hτ
  exact eq_neg_of_add_eq_zero_left hτ

/-- The embedding of a spatial test `ψ ↦ (ψeᵢ, ∂_jψeᵢ)ᵢ`. -/
def testEmbG (q : ℝ≥0∞) (j : Fin 3) (ψ : {ψ : Space → ℝ // IsSpatialTest ψ}) :
    Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space) :=
  fun i => (sT q ψ.2 i, sT q (isSpatialTest_sd ψ.2 j) i)

/-- **The distributional derivative holds in almost every phase** (`1 < q < ∞`): if `∂_j w = g` in
distributions on `(ℝ/Pℤ) × ℝ³`, then for a.e. `τ`, `⟪∂_jψeᵢ, w(τ)⟫ = ⟪ψeᵢ, -g(τ)⟫` for every spatial
test `ψ` and every component `i`. -/
theorem ae_forall_grad (hq1 : 1 < q) {j : Fin 3} {w g : Yq P q}
    (h : HasPhaseOp (fun Φ => -dy j Φ) w g) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ ψ : Space → ℝ, ∀ hψ : IsSpatialTest ψ,
      ∀ i, innerPair q (sT q (isSpatialTest_sd hψ j) i) (w τ) =
        innerPair q (sT q hψ i) (-(g τ)) := by
  have : Fact (conjExp q ≠ ⊤) := ⟨B0428.conjExp_ne_top hq1⟩
  have h1 : SecondCountableTopology (Lp CVec3 (conjExp q) (volume : Measure Space)) :=
    inferInstance
  have h2 : SecondCountableTopology (Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) := inferInstance
  have h3 : SecondCountableTopology (Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) := inferInstance
  set s := range (testEmbG q j) with hs
  have hsep : TopologicalSpace.IsSeparable s := TopologicalSpace.IsSeparable.of_separableSpace s
  have := hsep.separableSpace
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense s
  have hsub : s ⊆ closure (Subtype.val '' D) := Subtype.dense_iff.1 hDd
  have : Countable D := hDc.to_subtype
  have hgood : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ d : D,
      PairCond q (w τ) (-(g τ)) (d : s) := by
    rw [ae_all_iff]
    intro d
    obtain ⟨ψ, hψ⟩ := (d : s).2
    rw [← hψ]
    have hi : ∀ i : Fin 3, ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        innerPair q (sT q (isSpatialTest_sd ψ.2 j) i) (w τ) =
          -innerPair q (sT q ψ.2 i) (g τ) := fun i => ae_slice_grad h ψ.2 i
    filter_upwards [ae_all_iff.2 hi] with τ hτ
    intro i
    simp only [testEmbG, map_neg]
    exact hτ i
  filter_upwards [hgood] with τ hτ
  intro ψ hψ i
  have hcl : closure (Subtype.val '' D) ⊆ {x | PairCond q (w τ) (-(g τ)) x} := by
    refine closure_minimal ?_ (isClosed_pairCond _ _)
    rintro _ ⟨d, hd, rfl⟩
    exact hτ ⟨d, hd⟩
  exact hcl (hsub ⟨⟨ψ, hψ⟩, rfl⟩) i

omit hP in
/-- **The pairing form gives the compiled weak derivative of the real parts**: if
`⟪∂_jψeᵢ, u⟫ = ⟪ψeᵢ, -Λ⟫` for all spatial tests, `u` is the complexification of a real field `f`
and `G` is the real part of `Λ`, then `∂_j f = G` (`HasWeakSpatialDerivative`). -/
theorem hasWeak_of_pair {j : Fin 3} {u Λ : Lp CVec3 2 (volume : Measure Space)}
    {f G : SpatialField}
    (hpair : ∀ ψ : Space → ℝ, ∀ hψ : IsSpatialTest ψ, ∀ i,
      innerPair 2 (sT 2 (isSpatialTest_sd hψ j) i) u = innerPair 2 (sT 2 hψ i) (-Λ))
    (hu : (u : Space → CVec3) =ᵐ[volume] fun y => cplxL (f y))
    (hG : ∀ᵐ y, reL ((Λ : Space → CVec3) y) = G y) :
    HasWeakSpatialDerivative j f G := by
  have hmf : MemLp f 2 (volume : Measure Space) := by
    refine (reL.comp_memLp' (Lp.memLp u)).ae_eq ?_
    filter_upwards [hu] with y hy
    simp only [Function.comp_apply, hy]
    ext k
    simp
  have hmG : MemLp G 2 (volume : Measure Space) := (reL.comp_memLp' (Lp.memLp Λ)).ae_eq hG
  have hlf : LocallyIntegrable f (volume : Measure Space) := hmf.locallyIntegrable (by norm_num)
  have hlG : LocallyIntegrable G (volume : Measure Space) := hmG.locallyIntegrable (by norm_num)
  have hL : ∀ φ, IsSpatialTest φ → Integrable (fun x => spatialTestDerivative j φ x • f x) :=
    fun φ hφ => hlf.integrable_smul_left_of_hasCompactSupport (hφ.derivative j).smooth.continuous
      (hφ.derivative j).compact
  have hR : ∀ φ, IsSpatialTest φ → Integrable (fun x => φ x • G x) := fun φ hφ =>
    hlG.integrable_smul_left_of_hasCompactSupport hφ.smooth.continuous hφ.compact
  refine ⟨hL, hR, fun φ hφ => ?_⟩
  have hφd := hφ.derivative j
  ext k
  have c1 : (∫ x, spatialTestDerivative j φ x • f x) k =
      ∫ x, spatialTestDerivative j φ x * f x k := by
    have := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm (hL φ hφ)
    change EuclideanSpace.proj k (∫ x, spatialTestDerivative j φ x • f x) = _
    rw [← this]
    simp
  have c2 : (∫ x, φ x • G x) k = ∫ x, φ x * G x k := by
    have := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm (hR φ hφ)
    change EuclideanSpace.proj k (∫ x, φ x • G x) = _
    rw [← this]
    simp
  rw [PiLp.neg_apply, c1, c2]
  have h1 := hpair φ hφ k
  have hsd := isSpatialTest_sd hφ j
  rw [sT, sT, innerPair_spatialTest hsd.smooth hsd.compact k,
    innerPair_spatialTest hφ.smooth hφ.compact k] at h1
  have hl : ∫ y, ((sd j φ y : ℝ) : ℂ) * ((u : Space → CVec3) y) k =
      ((∫ y, spatialTestDerivative j φ y * f y k : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hu] with y hy
    rw [hy, cplxL_apply]
    push_cast
    rfl
  have hmΛ : MemLp (fun y => ((-Λ : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3) y k) 2
      (volume : Measure Space) :=
    (EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).comp_memLp' (Lp.memLp (-Λ))
  have hintΛ : Integrable (fun y => ((φ y : ℝ) : ℂ) *
      ((-Λ : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3) y k) := by
    have := (hmΛ.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.smooth.continuous hφ.compact
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [Complex.real_smul]
  have hr : (∫ y, ((φ y : ℝ) : ℂ) *
      ((-Λ : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3) y k).re =
      -∫ y, φ y * G y k := by
    rw [← integral_neg, ← RCLike.re_to_complex, ← integral_re hintΛ]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg Λ, hG] with y hy hy'
    rw [hy, ← hy']
    simp [reL_apply]
  have h2 := congrArg Complex.re h1
  rw [hl, Complex.ofReal_re, hr] at h2
  exact h2

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.GradSlice
