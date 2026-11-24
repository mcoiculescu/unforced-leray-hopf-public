import UnforcedLeray.Blueprint.Localization.Realization
import UnforcedLeray.Loc.L02FreeEvolution.Operators
import UnforcedLeray.Analysis.SobolevGraph.Pairing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Step L13, helpers: similarity dilations, the Leray projection and the literal `𝔓 div`

Support for `Loc/L13PhysicalRemainder.lean` (step L13 `PhysicalRemainderStep`,
`paper/main.tex` lines 525–547, blueprint units B1026, B1028, B1029). The physical remainder
is `ρ(t) = t^{-1/2} R(·/√t, log t)` (line 536), i.e. `ρ(e^τ) = D(-τ) R(τ)` with the compiled
similarity dilation `D(s) F = e^{s/2} F(e^{s/2}·)` (`Loc.L02.dil`). This file proves:

* the pairing identity `⟨D(s)A, G⟩ = e^{-s} ⟨A, G(e^{-s/2}·)⟩` (change of variables) and the
  adjoint identity `⟨D(s)A, B⟩ = e^{-s/2} ⟨A, D(-s)B⟩`;
* `𝔓 D(s) = D(s) 𝔓` for the compiled orthogonal Leray projection (`D(±s)` preserve `L²_div`);
* the scaling of the literal pairing `⟨𝔓 div 𝕋, φ⟩` and hence of `IsMinusLerayDiv`:
  if `F = -𝔓div(V⊗V)` and `u = e^{-τ/2} V(e^{-τ/2}·)`, then `-𝔓div(u⊗u) = e^{-τ} D(-τ) F`
  (lines 527–531: `N(t) = t^{-3/2} 𝒩(·/√t, log t)`);
* strong continuity of `(s, F) ↦ D(s)F` along continuous paths for `s ≥ 0`, and
  `𝒪`-invariance of `D(s)F`.

The `toL2` algebra and the density of vector tests in `L²` are copied from

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L13

open SobolevGraph
open UnforcedLeray.Loc.L02 (dil dilH2 coeFn_dil norm_dil_apply_le dil_mem_solenoidal)

/-! ## `toL2` algebra (copied from `Loc/L10Nonlinear/Pairing.lean`) -/

theorem toL2_add' {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    toL2 (f + g) = toL2 f + toL2 g := by
  rw [toL2_of_memLp (hf.add hg), toL2_of_memLp hf, toL2_of_memLp hg]
  exact hf.toLp_add hg

theorem toL2_smul' (a : ℝ) {f : SpatialField} (hf : MemLp f 2 volume) :
    toL2 (a • f) = a • toL2 f := by
  rw [toL2_of_memLp (hf.const_smul a), toL2_of_memLp hf]
  exact hf.toLp_const_smul a

theorem toL2_congr {f g : SpatialField} (hf : MemLp f 2 volume) (h : f =ᵐ[volume] g) :
    toL2 f = toL2 g := by
  have hg : MemLp g 2 volume := (memLp_congr_ae h).mp hf
  rw [toL2_of_memLp hf, toL2_of_memLp hg]
  exact (hf.toLp_eq_toLp_iff hg).mpr h

theorem toL2_coeFn (F : L2Space) : toL2 (F : SpatialField) = F := by
  rw [toL2_of_memLp (Lp.memLp F)]
  exact Lp.toLp_coeFn F (Lp.memLp F)

theorem toL2_of_ae_eq_coeFn {f : SpatialField} {F : L2Space}
    (h : (F : SpatialField) =ᵐ[volume] f) : toL2 f = F := by
  rw [← toL2_congr (Lp.memLp F) h, toL2_coeFn]

theorem isVectorTest_memLp {φ : Space → Space} (hφ : IsVectorTest φ) : MemLp φ 2 volume :=
  hφ.smooth.continuous.memLp_of_hasCompactSupport hφ.compact

/-- Smooth compactly supported vector fields separate `L²(ℝ³;ℝ³)` (copied from
`Loc/L10Nonlinear/Pairing.lean`, `eq_zero_of_forall_vectorTest`). -/
theorem eq_zero_of_forall_vectorTest {F : L2Space}
    (h : ∀ φ, IsVectorTest φ → inner ℝ F (toL2 φ) = 0) : F = 0 := by
  have hint : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (F : SpatialField) x = 0 := by
    intro ψ hs hc
    have hψ : IsSpatialTest ψ := ⟨hs, hc⟩
    apply ext_inner_left ℝ
    intro v
    rw [inner_zero_right, ← pairing_apply ψ hψ v F]
    change inner ℝ (testVector ψ hψ v) F = 0
    have hφ : IsVectorTest (fun x => ψ x • v) :=
      ⟨hs.smul contDiff_const, hc.smul_right⟩
    have hm : MemLp (fun x => ψ x • v) 2 volume :=
      hφ.smooth.continuous.memLp_of_hasCompactSupport hφ.compact
    have heq : toL2 (fun x => ψ x • v) = testVector ψ hψ v := by
      rw [toL2_of_memLp hm]
      rfl
    rw [real_inner_comm, ← heq]
    exact h _ hφ
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp F).locallyIntegrable (by norm_num)) hint
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr hae

/-- Equality of `L²` classes tested against vector tests. -/
theorem eq_of_forall_vectorTest {F G : L2Space}
    (h : ∀ φ, IsVectorTest φ → inner ℝ F (toL2 φ) = inner ℝ G (toL2 φ)) : F = G := by
  have : F - G = 0 := eq_zero_of_forall_vectorTest (fun φ hφ => by
    rw [inner_sub_left, h φ hφ, sub_self])
  exact sub_eq_zero.mp this

/-! ## The pairing and adjoint identities of the dilation -/

/-- Change of variables: `⟨D(s)A, G⟩ = e^{-s} ⟨A, G(e^{-s/2}·)⟩` for `G ∈ L²`. -/
theorem dil_inner_toL2 (s : ℝ) (A : L2Space) {G : SpatialField} (hG : MemLp G 2 volume) :
    inner ℝ (dil s A) (toL2 G) =
      Real.exp (-s) * inner ℝ A (toL2 (fun y => G (Real.exp (-s / 2) • y))) := by
  have hc0 : 0 < Real.exp (s / 2) := Real.exp_pos _
  set c := Real.exp (s / 2) with hc
  have hci : Real.exp (-s / 2) = c⁻¹ := by
    rw [hc, ← Real.exp_neg]
    ring_nf
  rw [hci]
  have hGc : MemLp (fun y => G (c⁻¹ • y)) 2 volume :=
    SpatialScaling.memLp_comp_dilation hG (inv_ne_zero hc0.ne')
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 : (∫ x, inner ℝ ((dil s A : SpatialField) x) ((toL2 G : SpatialField) x)) =
      ∫ x, c * inner ℝ ((A : SpatialField) (c • x)) (G x) := by
    apply integral_congr_ae
    filter_upwards [coeFn_dil s A, coeFn_toL2 hG] with x h1 h2
    rw [h1, h2]
    simp only [SpatialScaling.spatialScale, real_inner_smul_left]
    rfl
  have h2 : (∫ y, inner ℝ ((A : SpatialField) y)
      ((toL2 (fun y => G (c⁻¹ • y)) : SpatialField) y)) =
      ∫ y, inner ℝ ((A : SpatialField) y) (G (c⁻¹ • y)) := by
    apply integral_congr_ae
    filter_upwards [coeFn_toL2 hGc] with y hy
    rw [hy]
  have h3 : (∫ x, inner ℝ ((A : SpatialField) (c • x)) (G x)) =
      (c ^ 3)⁻¹ * ∫ y, inner ℝ ((A : SpatialField) y) (G (c⁻¹ • y)) := by
    have := MeasureTheory.Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
      (fun y => inner ℝ ((A : SpatialField) y) (G (c⁻¹ • y))) c (hR := hc0.le)
    simp only [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul, finrank_euclideanSpace,
      Fintype.card_fin, smul_eq_mul] at this
    exact this
  rw [h1, h2, integral_const_mul, h3]
  have hcs : c ^ 2 = Real.exp s := by
    rw [hc, sq, ← Real.exp_add]
    ring_nf
  have he : Real.exp (-s) = (c ^ 2)⁻¹ := by rw [hcs, Real.exp_neg]
  rw [he]
  field_simp

/-- The case `s = -τ`: `⟨D(-τ)A, G⟩ = e^{τ} ⟨A, G(e^{τ/2}·)⟩`. -/
theorem dil_neg_inner_toL2 (τ : ℝ) (A : L2Space) {G : SpatialField} (hG : MemLp G 2 volume) :
    inner ℝ (dil (-τ) A) (toL2 G) =
      Real.exp τ * inner ℝ A (toL2 (fun y => G (Real.exp (τ / 2) • y))) := by
  rw [dil_inner_toL2 (-τ) A hG, neg_neg]

/-- `D(s)` has the coefficient form `e^{s/2} F(e^{s/2}·)` as an `L²` class. -/
theorem dil_eq_toL2 (s : ℝ) (F : L2Space) :
    dil s F = toL2 (SpatialScaling.spatialScale (Real.exp (s / 2)) (Real.exp (s / 2))
      (F : SpatialField)) :=
  (toL2_of_ae_eq_coeFn (coeFn_dil s F)).symm

/-- `⟨D(s)A, B⟩ = e^{-s/2} ⟨A, D(-s)B⟩`. -/
theorem dil_adjoint (s : ℝ) (A B : L2Space) :
    inner ℝ (dil s A) B = Real.exp (-s / 2) * inner ℝ A (dil (-s) B) := by
  have h := dil_inner_toL2 s A (Lp.memLp B)
  rw [toL2_coeFn] at h
  rw [h]
  have hB : toL2 (fun y => (B : SpatialField) (Real.exp (-s / 2) • y)) =
      Real.exp (s / 2) • dil (-s) B := by
    apply toL2_of_ae_eq_coeFn
    filter_upwards [Lp.coeFn_smul (Real.exp (s / 2)) (dil (-s) B), coeFn_dil (-s) B]
      with y h1 h2
    rw [h1, Pi.smul_apply, h2]
    simp only [SpatialScaling.spatialScale, smul_smul]
    rw [← Real.exp_add]
    ring_nf
    rw [Real.exp_zero, one_smul]
  rw [hB, real_inner_smul_right, ← mul_assoc, ← Real.exp_add]
  ring_nf

/-- The Leray projection commutes with the similarity dilations. -/
theorem projection_dil (s : ℝ) (A : L2Space) :
    Leray.projection (dil s A) = dil s (Leray.projection A) := by
  apply Leray.projection_eq_of_orthogonal
  · exact (Leray.mem_solenoidalSubspace_iff _).mp (dil_mem_solenoidal s (Leray.projection_mem A))
  · rw [← map_sub]
    rw [Submodule.mem_orthogonal]
    intro G hG
    rw [real_inner_comm, dil_adjoint]
    have hres := Leray.residual_mem_orthogonal A
    rw [Submodule.mem_orthogonal] at hres
    have h0 := hres _ (dil_mem_solenoidal (-s) hG)
    rw [real_inner_comm] at h0
    rw [h0, mul_zero]

/-! ## Dilated tests -/

theorem isVectorTest_comp_smul {φ : Space → Space} (hφ : IsVectorTest φ) {c : ℝ}
    (hc : c ≠ 0) : IsVectorTest (fun y => φ (c • y)) :=
  ⟨hφ.smooth.comp (contDiff_const_smul c), hφ.compact.comp_smul hc⟩

theorem fderiv_comp_smul {φ : Space → Space} (hφ : Differentiable ℝ φ) (c : ℝ) (y v : Space) :
    fderiv ℝ (fun y' => φ (c • y')) y v = c • fderiv ℝ φ (c • y) v := by
  have hd : HasFDerivAt (fun y' : Space => φ (c • y'))
      ((fderiv ℝ φ (c • y)).comp (c • ContinuousLinearMap.id ℝ Space)) y :=
    (hφ (c • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul c)
  rw [hd.fderiv]
  simp

theorem testPartial_comp_smul {φ : Space → Space} (hφ : Differentiable ℝ φ) (c : ℝ)
    (j : Fin 3) :
    testPartial (fun y => φ (c • y)) j = fun y => c • testPartial φ j (c • y) := by
  funext y
  exact fderiv_comp_smul hφ c y _

theorem testPartial_memLp {φ : Space → Space} (hφ : IsVectorTest φ) (j : Fin 3) :
    MemLp (testPartial φ j) 2 volume := by
  have hc : Continuous (fun y => fderiv ℝ φ y (coordinateVector j)) :=
    ((hφ.smooth.continuous_fderiv (by simp))).clm_apply continuous_const
  exact hc.memLp_of_hasCompactSupport (hφ.compact.fderiv_apply (𝕜 := ℝ) _)

/-! ## Scaling of the literal pairing and of `IsMinusLerayDiv` -/

/-- `⟨𝔓 div 𝕋_τ, φ⟩ = ⟨𝔓 div 𝕋, φ(e^{τ/2}·)⟩` for the scaled tensor
`𝕋_τ = e^{-τ} 𝕋(e^{-τ/2}·)` (the tensor of `u = e^{-τ/2}V(e^{-τ/2}·)` from that of `V`). -/
theorem lerayDivPairing_scale (τ : ℝ) {col : Fin 3 → SpatialField} (hcol : ColumnsL2 col)
    {φ : Space → Space} (hφ : IsVectorTest φ) :
    lerayDivPairing
        (fun j => SpatialScaling.spatialScale (Real.exp (-τ)) (Real.exp (-τ / 2)) (col j)) φ =
      lerayDivPairing col (fun y => φ (Real.exp (τ / 2) • y)) := by
  unfold lerayDivPairing
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have h1 : toL2 (SpatialScaling.spatialScale (Real.exp (-τ)) (Real.exp (-τ / 2)) (col j)) =
      Real.exp (-τ / 2) • dil (-τ) (toL2 (col j)) := by
    have hs : SpatialScaling.spatialScale (Real.exp (-τ)) (Real.exp (-τ / 2)) (col j) =
        Real.exp (-τ / 2) • SpatialScaling.spatialScale (Real.exp (-τ / 2)) (Real.exp (-τ / 2))
          (col j) := by
      funext y
      simp only [SpatialScaling.spatialScale, Pi.smul_apply, smul_smul, ← Real.exp_add]
      ring_nf
    rw [hs, toL2_smul' _ (SpatialScaling.memLp_spatialScale (hcol j) _ (Real.exp_pos _).ne')]
    congr 1
    rw [dil_eq_toL2]
    apply toL2_congr (SpatialScaling.memLp_spatialScale (hcol j) _ (Real.exp_pos _).ne')
    exact SpatialScaling.ae_eq_spatialScale (coeFn_toL2 (hcol j)).symm _
      (Real.exp_pos _).ne'
  have hm : MemLp (fun y => testPartial φ j (Real.exp (τ / 2) • y)) 2 volume :=
    SpatialScaling.memLp_comp_dilation (testPartial_memLp hφ j) (Real.exp_pos _).ne'
  have h2 : toL2 (testPartial (fun y => φ (Real.exp (τ / 2) • y)) j) =
      Real.exp (τ / 2) • toL2 (fun y => testPartial φ j (Real.exp (τ / 2) • y)) := by
    rw [testPartial_comp_smul hd]
    exact toL2_smul' _ hm
  rw [h1, h2, real_inner_smul_left, map_smul, real_inner_smul_right,
    ← Leray.projection_selfadjoint (dil (-τ) (toL2 (col j))),
    projection_dil, dil_neg_inner_toL2 τ _ (testPartial_memLp hφ j),
    ← Leray.projection_selfadjoint (toL2 (col j))]
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- If `F = -𝔓div(V⊗V)` and `u = e^{-τ/2} V(e^{-τ/2}·)` a.e., then
`e^{-τ} D(-τ) F = -𝔓div(u⊗u)`. -/
theorem isMinusLerayDiv_scale (τ : ℝ) {V u : SpatialField} {F : L2Space}
    (hF : IsMinusLerayDiv (tensorColumns V V) F)
    (hu : u =ᵐ[volume]
      SpatialScaling.spatialScale (Real.exp (-τ / 2)) (Real.exp (-τ / 2)) V) :
    IsMinusLerayDiv (tensorColumns u u) (Real.exp (-τ) • dil (-τ) F) := by
  have hcols : ∀ j, tensorColumns u u j =ᵐ[volume]
      SpatialScaling.spatialScale (Real.exp (-τ)) (Real.exp (-τ / 2)) (tensorColumns V V j) := by
    intro j
    have he : Real.exp (-τ) = Real.exp (-τ / 2) * Real.exp (-τ / 2) := by
      rw [← Real.exp_add]
      ring_nf
    filter_upwards [hu] with x hx
    simp only [tensorColumns, hx, SpatialScaling.spatialScale, PiLp.smul_apply, smul_eq_mul,
      smul_smul, he]
    congr 1
    ring
  have hL2 : ∀ j, MemLp (SpatialScaling.spatialScale (Real.exp (-τ)) (Real.exp (-τ / 2))
      (tensorColumns V V j)) 2 volume :=
    fun j => SpatialScaling.memLp_spatialScale (hF.1 j) _ (Real.exp_pos _).ne'
  refine ⟨fun j => (memLp_congr_ae (hcols j)).mpr (hL2 j), fun φ hφ => ?_⟩
  have hcongr : lerayDivPairing (tensorColumns u u) φ = lerayDivPairing
      (fun j => SpatialScaling.spatialScale (Real.exp (-τ)) (Real.exp (-τ / 2))
        (tensorColumns V V j)) φ := by
    unfold lerayDivPairing
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [toL2_congr ((memLp_congr_ae (hcols j)).mpr (hL2 j)) (hcols j)]
  rw [hcongr, lerayDivPairing_scale τ hF.1 hφ, real_inner_smul_left,
    dil_neg_inner_toL2 τ F (isVectorTest_memLp hφ)]
  have hφτ := isVectorTest_comp_smul hφ (Real.exp_pos (τ / 2)).ne'
  rw [← hF.2 _ hφτ, ← mul_assoc, ← Real.exp_add]
  simp

/-! ## Continuity and symmetry of the dilation -/

/-- `s ↦ D(s) g(s)` is continuous on a set of nonnegative `s` along a continuous path `g`
(`D` is strongly continuous on `[0,∞)` with `‖D(s)‖ ≤ 1` there). -/
theorem continuousOn_dil_apply {S : Set ℝ} (hS : S ⊆ Ici 0) {g : ℝ → L2Space}
    (hg : ContinuousOn g S) : ContinuousOn (fun s => dil s (g s)) S := by
  intro s₀ hs₀
  have hstrong : Tendsto (fun s => dil s (g s₀)) (𝓝[S] s₀) (𝓝 (dil s₀ (g s₀))) :=
    ((Loc.L02.continuousOn_freeL2 le_rfl (g s₀)).mono hS) s₀ hs₀
  have hg0 : Tendsto (fun s => ‖g s - g s₀‖) (𝓝[S] s₀) (𝓝 0) := by
    have := ((hg s₀ hs₀).tendsto.sub_const (g s₀)).norm
    simpa using this
  have hsmall : Tendsto (fun s => dil s (g s) - dil s (g s₀)) (𝓝[S] s₀) (𝓝 0) := by
    apply squeeze_zero_norm' _ hg0
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← map_sub]
    have hs0 : 0 ≤ s := hS hs
    calc ‖dil s (g s - g s₀)‖ ≤ Real.exp (-(s / 4)) * ‖g s - g s₀‖ := norm_dil_apply_le s _
      _ ≤ 1 * ‖g s - g s₀‖ := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = ‖g s - g s₀‖ := one_mul _
  have := hsmall.add hstrong
  simp only [sub_add_cancel, zero_add] at this
  exact this

/-- `𝒪`-invariance is preserved by the similarity dilations. -/
theorem isAxisymmetricNoSwirl_dil (s : ℝ) {F : L2Space}
    (hF : IsAxisymmetricNoSwirl (F : SpatialField)) :
    IsAxisymmetricNoSwirl (dil s F : SpatialField) := by
  intro g hg
  set c := Real.exp (s / 2)
  have hc : c ≠ 0 := (Real.exp_pos _).ne'
  have h1 := coeFn_dil s F
  have h2 : (fun x => g ((dil s F : SpatialField) (g.symm x))) =ᵐ[volume]
      (fun x => g (SpatialScaling.spatialScale c c (F : SpatialField) (g.symm x))) := by
    have := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp h1
    filter_upwards [this] with x hx
    simp only [Function.comp_apply] at hx
    rw [hx]
  have h3 : (fun x => g (SpatialScaling.spatialScale c c (F : SpatialField) (g.symm x))) =
      SpatialScaling.spatialScale c c (fun x => g ((F : SpatialField) (g.symm x))) := by
    funext x
    simp only [SpatialScaling.spatialScale, map_smul]
  have h4 := SpatialScaling.ae_eq_spatialScale (hF g hg) c hc
  rw [h3] at h2
  exact h2.trans (h4.trans h1.symm)

/-! ## The dilation on `H²` -/

theorem dilH2_value (s : ℝ) (G : H2) : (dilH2 s G).value = dil s G.value := rfl

theorem dilH2_first (s : ℝ) (G : H2) (i : Fin 3) :
    (dilH2 s G).first i = Real.exp (s / 2) • dil s (G.first i) := rfl

theorem dilH2_second (s : ℝ) (G : H2) (i j : Fin 3) :
    (dilH2 s G).second i j = Real.exp s • dil s (G.second i j) := rfl

theorem laplace_dilH2 (s : ℝ) (G : H2) :
    H2.laplace (dilH2 s G) = Real.exp s • dil s (H2.laplace G) := by
  rw [H2.laplace_eq, H2.laplace_eq, map_sum, Finset.smul_sum]
  rfl

end UnforcedLeray.Blueprint.L13
