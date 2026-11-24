import UnforcedLeray.Units.B0428.Spatial
import UnforcedLeray.Units.B0411.Separation
import UnforcedLeray.TestFunctions
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Slicing a distributional Laplacian in `Y_q` into the phases (helper for B0428)

Blueprint unit **B0428** (`eq:free-stress-19`, `paper/main.tex` lines 7541–7548): the hypothesis
"`w, Δw ∈ Y_q` in distributions" is the space-time identity `HasPhaseOp lapT w L` of

pairings against smooth `P`-periodic phase tests with bounded spatial support). The proof of the
unit is spatial, at each phase (blueprint proof outline: "At each phase, the `ℝ³` inequality
[...] Then apply Cauchy–Schwarz in `τ`"). This file proves that the space-time identity holds in
every phase:

* `lapT_prodTest`: `Δ_y(e_n(τ)ψ(y)eᵢ) = e_n(τ)(Δψ)(y)eᵢ` for the product tests of
  `B0411.Separation`;
* `ae_slice_pair`: for each spatial test `ψ` and component `i`,
  `∫ Δψ (w(τ))ᵢ = ∫ ψ (L(τ))ᵢ` for a.e. phase `τ` (Fourier uniqueness on the phase circle,
  `B0411.ae_eq_zero_of_fourier`);
* `ae_isWeakLaplacian`: for `1 < q < ∞`, **`L(τ) = Δ(w(τ))` in `𝒟'(ℝ³)` for a.e. `τ`**
  (`Heat.IsWeakLaplacian`). The exceptional null set is made independent of the test through a
  countable family of tests that is dense for the pairings: the tests embed into the
  second-countable space `(L^{q'} × L^{q'})³`, `q' < ∞`, by `ψ ↦ (ψeᵢ, Δψeᵢ)ᵢ`.

Status: helper for B0428; Theorem A is not proved in Lean.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0428

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.Heat UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411 (prodTest spatialTest memLp_spatialTest isPhaseTest_prodTest
  phasePair_prodTest innerPair_spatialTest ae_eq_zero_of_fourier integrable_Yq
  integrable_fourier_smul)

/-! ### Spatial tests -/

theorem isSpatialTest_sd {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) (j : Fin 3) :
    IsSpatialTest (sd j ψ) :=
  hψ.derivative j

theorem isSpatialTest_laplacian {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) :
    IsSpatialTest (laplacian ψ) := by
  have h : ∀ j : Fin 3, IsSpatialTest (sd j (sd j ψ)) := fun j =>
    isSpatialTest_sd (isSpatialTest_sd hψ j) j
  have he : laplacian ψ = fun y => sd 0 (sd 0 ψ) y + sd 1 (sd 1 ψ) y + sd 2 (sd 2 ψ) y := by
    funext y
    rw [laplacian_eq_sum_sd, Fin.sum_univ_three]
  rw [he]
  exact ⟨((h 0).smooth.add (h 1).smooth).add (h 2).smooth,
    (((h 0).compact.add (h 1).compact).add (h 2).compact)⟩

/-! ### The slice derivative and the Laplacian of product tests -/

theorem dy_apply_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × Space → F} (hΦ : Differentiable ℝ Φ) (j : Fin 3) (t : ℝ) (y : Space) :
    dy j Φ (t, y) = fderiv ℝ (fun z => Φ (t, z)) y (coordinateVector j) := by
  have hi : HasFDerivAt (fun z : Space => ((t, z) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have h2 : HasFDerivAt (fun z => Φ (t, z))
      ((fderiv ℝ Φ (t, y)).comp ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) y :=
    (hΦ (t, y)).hasFDerivAt.comp y hi
  rw [h2.fderiv]
  simp [dy]

variable {P : ℝ}

theorem prodTest_apply_eq (n : ℤ) (φ : Space → ℝ) (i : Fin 3) (t : ℝ) (z : Space) :
    prodTest P n φ i (t, z) =
      φ z • (fourier n (t : AddCircle P) • EuclideanSpace.single i (1 : ℂ)) := by
  ext k
  simp only [prodTest, PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem dy_prodTest (n : ℤ) {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) (i j : Fin 3) :
    dy j (prodTest P n ψ i) = prodTest P n (sd j ψ) i := by
  funext p
  obtain ⟨t, y⟩ := p
  rw [dy_apply_slice ((isPhaseTest_prodTest (P := P) n hψ.smooth hψ.compact i).smooth.differentiable
    (by simp)) j t y]
  simp_rw [prodTest_apply_eq]
  rw [fderiv_smul_const (hψ.smooth.differentiable (by simp) y),
    ContinuousLinearMap.smulRight_apply]
  rfl

/-- `Δ_y(e_n(τ)ψ(y)eᵢ) = e_n(τ)(Δψ)(y)eᵢ`. -/
theorem lapT_prodTest (n : ℤ) {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) (i : Fin 3) :
    lapT (prodTest P n ψ i) = prodTest P n (laplacian ψ) i := by
  have h1 : ∀ j : Fin 3, dy j (dy j (prodTest P n ψ i)) = prodTest P n (sd j (sd j ψ)) i :=
    fun j => by rw [dy_prodTest n hψ i j, dy_prodTest n (isSpatialTest_sd hψ j) i j]
  funext p
  simp only [lapT, h1]
  simp only [prodTest, laplacian_eq_sum_sd]
  push_cast
  rw [Finset.mul_sum, Finset.sum_smul]

/-! ### Each test pairing holds in almost every phase -/

variable [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- The spatial test `ψeᵢ` as an element of `L^{q'}(ℝ³; ℂ³)`. -/
def sT (q : ℝ≥0∞) {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) (i : Fin 3) :
    Lp CVec3 (conjExp q) (volume : Measure Space) :=
  (memLp_spatialTest hψ.smooth hψ.compact i (conjExp q)).toLp _

/-- **One test, almost every phase.** If `L = Δw` in distributions on `(ℝ/Pℤ) × ℝ³`, then for
each spatial test `ψ` and component `i`: `⟪Δψeᵢ, w(τ)⟫ = ⟪ψeᵢ, L(τ)⟫` for a.e. `τ`. -/
theorem ae_slice_pair {w L : Yq P q} (h : HasPhaseOp lapT w L) {ψ : Space → ℝ}
    (hψ : IsSpatialTest ψ) (i : Fin 3) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      innerPair q (sT q (isSpatialTest_laplacian hψ) i) (w τ) = innerPair q (sT q hψ i) (L τ) := by
  set a := sT q (isSpatialTest_laplacian hψ) i with ha
  set b := sT q hψ i with hb
  have hint : Integrable (fun τ => innerPair q a (w τ) - innerPair q b (L τ))
      (AddCircle.haarAddCircle (T := P)) :=
    ((innerPair q a).integrable_comp (integrable_Yq w)).sub
      ((innerPair q b).integrable_comp (integrable_Yq L))
  have hF : ∀ n : ℤ, ∫ τ, fourier n τ * (innerPair q a (w τ) - innerPair q b (L τ))
      ∂AddCircle.haarAddCircle = 0 := by
    intro n
    have i1 := (innerPair q a).integrable_comp (integrable_fourier_smul w n)
    have i2 := (innerPair q b).integrable_comp (integrable_fourier_smul L n)
    simp only [map_smul, smul_eq_mul] at i1 i2
    have e1 : ∫ τ, fourier n τ * innerPair q a (w τ) ∂AddCircle.haarAddCircle =
        innerPair q a (∫ τ, fourier n τ • w τ ∂AddCircle.haarAddCircle) := by
      rw [← (innerPair q a).integral_comp_comm (integrable_fourier_smul w n)]
      simp only [map_smul, smul_eq_mul]
    have e2 : ∫ τ, fourier n τ * innerPair q b (L τ) ∂AddCircle.haarAddCircle =
        innerPair q b (∫ τ, fourier n τ • L τ ∂AddCircle.haarAddCircle) := by
      rw [← (innerPair q b).integral_comp_comm (integrable_fourier_smul L n)]
      simp only [map_smul, smul_eq_mul]
    have hp := h _ (isPhaseTest_prodTest n hψ.smooth hψ.compact i)
    rw [lapT_prodTest n hψ i,
      phasePair_prodTest w n (isSpatialTest_laplacian hψ).smooth
        (isSpatialTest_laplacian hψ).compact i,
      phasePair_prodTest L n hψ.smooth hψ.compact i] at hp
    simp only [mul_sub]
    rw [integral_sub i1 i2, e1, e2]
    exact sub_eq_zero.2 hp
  filter_upwards [ae_eq_zero_of_fourier hint hF] with τ hτ
  exact sub_eq_zero.1 hτ

/-! ### A common null set for all tests -/

omit hP hq in
theorem conjExp_ne_top (hq1 : 1 < q) : conjExp q ≠ ⊤ := by
  unfold conjExp
  exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ENNReal.inv_lt_one.2 hq1)).ne'

/-- The pairings `⟪x.2, w⟫ = ⟪x.1, L⟫` for all components: a closed condition. -/
def PairCond (q : ℝ≥0∞) [Fact (1 ≤ q)] (u Λ : Lp CVec3 q (volume : Measure Space))
    (x : Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) : Prop :=
  ∀ i, innerPair q (x i).2 u = innerPair q (x i).1 Λ

theorem isClosed_pairCond (u Λ : Lp CVec3 q (volume : Measure Space)) :
    IsClosed {x | PairCond q u Λ x} := by
  have h : {x | PairCond q u Λ x} = ⋂ i : Fin 3,
      {x : Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
        Lp CVec3 (conjExp q) (volume : Measure Space) |
          innerPair q (x i).2 u = innerPair q (x i).1 Λ} := by
    ext x; simp [PairCond]
  rw [h]
  refine isClosed_iInter fun i => isClosed_eq ?_ ?_
  · exact ((innerPair q).continuous.comp (continuous_snd.comp (continuous_apply i))).clm_apply
      continuous_const
  · exact ((innerPair q).continuous.comp (continuous_fst.comp (continuous_apply i))).clm_apply
      continuous_const

/-- The embedding of a spatial test `ψ ↦ (ψeᵢ, Δψeᵢ)ᵢ`. -/
def testEmb (q : ℝ≥0∞) (ψ : {ψ : Space → ℝ // IsSpatialTest ψ}) :
    Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space) :=
  fun i => (sT q ψ.2 i, sT q (isSpatialTest_laplacian ψ.2) i)

/-- **The distributional Laplacian holds in almost every phase** (`1 < q < ∞`): if `L = Δw` in
distributions on `(ℝ/Pℤ) × ℝ³`, then for a.e. `τ`, `L(τ) = Δ(w(τ))` against every spatial test,
in the pairing form `⟪Δψeᵢ, w(τ)⟫ = ⟪ψeᵢ, L(τ)⟫`. -/
theorem ae_forall_pair (hq1 : 1 < q) {w L : Yq P q} (h : HasPhaseOp lapT w L) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ ψ : Space → ℝ, ∀ hψ : IsSpatialTest ψ,
      ∀ i, innerPair q (sT q (isSpatialTest_laplacian hψ) i) (w τ) =
        innerPair q (sT q hψ i) (L τ) := by
  have : Fact (conjExp q ≠ ⊤) := ⟨conjExp_ne_top hq1⟩
  have h1 : SecondCountableTopology (Lp CVec3 (conjExp q) (volume : Measure Space)) :=
    inferInstance
  have h2 : SecondCountableTopology (Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) := inferInstance
  have h3 : SecondCountableTopology (Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) := inferInstance
  set s := range (testEmb q) with hs
  have hsep : TopologicalSpace.IsSeparable s := TopologicalSpace.IsSeparable.of_separableSpace s
  have := hsep.separableSpace
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense s
  have hsub : s ⊆ closure (Subtype.val '' D) := Subtype.dense_iff.1 hDd
  have : Countable D := hDc.to_subtype
  have hgood : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ d : D,
      PairCond q (w τ) (L τ) (d : s) := by
    rw [ae_all_iff]
    intro d
    obtain ⟨ψ, hψ⟩ := (d : s).2
    rw [← hψ]
    have hi : ∀ i : Fin 3, ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        innerPair q (sT q (isSpatialTest_laplacian ψ.2) i) (w τ) =
          innerPair q (sT q ψ.2 i) (L τ) := fun i => ae_slice_pair h ψ.2 i
    filter_upwards [ae_all_iff.2 hi] with τ hτ
    exact hτ
  filter_upwards [hgood] with τ hτ
  intro ψ hψ i
  have hcl : closure (Subtype.val '' D) ⊆ {x | PairCond q (w τ) (L τ) x} := by
    refine closure_minimal ?_ (isClosed_pairCond _ _)
    rintro _ ⟨d, hd, rfl⟩
    exact hτ ⟨d, hd⟩
  exact hcl (hsub ⟨⟨ψ, hψ⟩, rfl⟩) i

/-- The pairing form of the spatial weak Laplacian implies `Heat.IsWeakLaplacian`. -/
theorem isWeakLaplacian_of_pair {u Λ : Lp CVec3 q (volume : Measure Space)}
    (h : ∀ ψ : Space → ℝ, ∀ hψ : IsSpatialTest ψ, ∀ i,
      innerPair q (sT q (isSpatialTest_laplacian hψ) i) u = innerPair q (sT q hψ i) Λ) :
    IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3) := by
  refine ⟨fun φ hφ => ?_⟩
  have hφL := isSpatialTest_laplacian hφ
  have hiu : Integrable (fun x => laplacian φ x • (u : Space → CVec3) x) :=
    ((Lp.memLp u).locallyIntegrable hq.out).integrable_smul_left_of_hasCompactSupport
      hφL.smooth.continuous hφL.compact
  have hiΛ : Integrable (fun x => φ x • (Λ : Space → CVec3) x) :=
    ((Lp.memLp Λ).locallyIntegrable hq.out).integrable_smul_left_of_hasCompactSupport
      hφ.smooth.continuous hφ.compact
  ext i
  have h1 := h φ hφ i
  rw [sT, sT, innerPair_spatialTest hφL.smooth hφL.compact i,
    innerPair_spatialTest hφ.smooth hφ.compact i] at h1
  have c1 : (∫ x, laplacian φ x • (u : Space → CVec3) x) i =
      ∫ x, (laplacian φ x : ℂ) * ((u : Space → CVec3) x) i := by
    have := (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integral_comp_comm hiu
    change EuclideanSpace.proj i (∫ x, laplacian φ x • (u : Space → CVec3) x) = _
    rw [← this]
    simp [Complex.real_smul]
  have c2 : (∫ x, φ x • (Λ : Space → CVec3) x) i =
      ∫ x, (φ x : ℂ) * ((Λ : Space → CVec3) x) i := by
    have := (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integral_comp_comm hiΛ
    change EuclideanSpace.proj i (∫ x, φ x • (Λ : Space → CVec3) x) = _
    rw [← this]
    simp [Complex.real_smul]
  rw [c1, c2, h1]

/-- **Slicing** (`1 < q < ∞`): `HasPhaseOp lapT w L` implies `IsWeakLaplacian (w τ) (L τ)` for
a.e. phase `τ`. -/
theorem ae_isWeakLaplacian (hq1 : 1 < q) {w L : Yq P q} (h : HasPhaseOp lapT w L) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      IsWeakLaplacian ((w τ : Lp CVec3 q (volume : Measure Space)) : Space → CVec3)
        ((L τ : Lp CVec3 q (volume : Measure Space)) : Space → CVec3) := by
  filter_upwards [ae_forall_pair hq1 h] with τ hτ
  exact isWeakLaplacian_of_pair hτ

end UnforcedLeray.B0428
