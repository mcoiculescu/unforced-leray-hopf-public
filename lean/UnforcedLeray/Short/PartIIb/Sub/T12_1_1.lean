import UnforcedLeray.Short.PartIIb.Sub.T12_1
import UnforcedLeray.Lib.CZCore

/-!
# Part II-b, task `PartII-b:T12/1/1` (`PlaneHelmholtzLr`): the planar Leray projection in
`L² ∩ L^r` (conditional assembly and sub-leaves)

Source of record: `the November 2 reference manuscript`: line 1670 ("`P_0` the
ordinary planar cylinder projection") and lines 1923-1926 (`P_0` inside the causal formula);
classical Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8; repository
INF01). The target is `PlaneHelmholtzLr` of `Sub/T12_1.lean`.

## Why the target splits this way

`PlaneHelmholtzLr` is the `ℂ²`-valued planar Leray projection `P_0 = I - ∇Δ⁻¹ div` on
`L² ∩ L^r(ℝ²)`: contraction on `L²`, bounded on `L^r`, and the two Helmholtz identities
(`G` weakly divergence free, `F - G` orthogonal to compactly supported smooth solenoidal fields).

1. **Complexification** (proved here: `planeHelmholtzLr_of`). The projection is real, so the
   `ℂ²` statement follows from the statement for real `ℝ²`-valued fields (`PlaneLerayReal`) applied
   to `Re F` and `Im F`: `|G|² = |Re G|² + |Im G|²` gives the `L²` constant `1`, and
   `|G| ≤ |Re G| + |Im G|` gives the `L^r` constant `2 C_real`; the two Helmholtz identities are
   `ℝ`-linear.
2. **Real Leray from Riesz operators** (`PlaneLerayOfRiesz`, leaf `T12/1/1/3`). If there is a
   family `S_{ik}` (`i, k ∈ {0, 1}`) of real operators on `L²(ℝ²)` which are Calderón-Zygmund
   convolution operators (`UnforcedLeray.CZ.IsCZConvolution`, the kernels `∂_i∂_k (2π)⁻¹ log |x|`),
   mutually transposed (`S_{ik}ᵀ = S_{ki}`), with `I - S` an `L²` contraction and the two test-level
   identities `Σ_i S_{ki} ∂_iφ = ∂_kφ`, `Σ_i S_{ki} Ψ_i = 0` for solenoidal `Ψ`
   (`IsPlaneRieszFamily`), then `G = F - S F` solves `PlaneLerayReal`: the `L^r` bound is
   `CZ.lp_bound` for each `S_{ik}`, and the Helmholtz identities follow from the transposition and
   the test identities.
3. **The Riesz family exists** (`PlaneRieszFamilyExists`, leaf `T12/1/1/2`, uses the kernel
   estimates `PlaneRieszKernelCZ`, leaf `T12/1/1/1`): the `N = 2` copy of `Lib/CZL2` and
   `Lib/LerayLp` (Newton potential `(2π)⁻¹ log |x|` of a test, pressure identity for the `L²`
   contraction, off-support kernel representation).

Proved here: `planeHelmholtzLr_of : PlaneLerayReal → PlaneHelmholtzLr` and
`planeHelmholtzLr_of_riesz : PlaneRieszFamilyExists → PlaneLerayOfRiesz → PlaneHelmholtzLr`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Real planar vectors and the real Helmholtz pair -/

/-- Real planar vectors `(F_0, F_1)` with the Euclidean norm. -/
abbrev RMerid : Type := EuclideanSpace ℝ (Fin 2)

/-- Real version of `IsPlaneHelmholtz`. -/
def IsPlaneHelmholtzReal (F G : ℝ × ℝ → RMerid) : Prop :=
  (∀ φ : ℝ × ℝ → ℝ, PlaneTest φ →
      Integrable (fun z => G z 0 * fderiv ℝ φ z (1, 0) + G z 1 * fderiv ℝ φ z (0, 1)) ∧
        ∫ z, (G z 0 * fderiv ℝ φ z (1, 0) + G z 1 * fderiv ℝ φ z (0, 1)) = 0) ∧
    (∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, PlaneSolTest Ψ →
      Integrable (fun z => ∑ i : Fin 2, (F z i - G z i) * Ψ z i) ∧
        ∫ z, ∑ i : Fin 2, (F z i - G z i) * Ψ z i = 0)

/-- **The real planar Leray projection in `L² ∩ L^r`** (the real form of `PlaneHelmholtzLr`). -/
def PlaneLerayReal : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ F : ℝ × ℝ → RMerid,
    MemLp F 2 volume → MemLp F (ENNReal.ofReal r) volume →
      ∃ G : ℝ × ℝ → RMerid, MemLp G 2 volume ∧ MemLp G (ENNReal.ofReal r) volume ∧
        eLpNorm G 2 volume ≤ eLpNorm F 2 volume ∧
        eLpNorm G (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume ∧
        IsPlaneHelmholtzReal F G

/-! ## Complexification -/

/-- Componentwise real part `ℂ² → ℝ²`. -/
def cmRe : CMerid →L[ℝ] RMerid :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => (v i).re)
      map_add' := by intro v w; ext i; simp
      map_smul' := by intro a v; ext i; simp }

/-- Componentwise imaginary part `ℂ² → ℝ²`. -/
def cmIm : CMerid →L[ℝ] RMerid :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => (v i).im)
      map_add' := by intro v w; ext i; simp
      map_smul' := by intro a v; ext i; simp }

/-- Componentwise inclusion `ℝ² → ℂ²`. -/
def cmEmb : RMerid →L[ℝ] CMerid :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => WithLp.toLp 2 (fun i => ((e i : ℝ) : ℂ))
      map_add' := by intro v w; ext i; simp
      map_smul' := by intro a v; ext i; simp }

theorem cmRe_apply (v : CMerid) (i : Fin 2) : cmRe v i = (v i).re := by
  simp [cmRe]

theorem cmIm_apply (v : CMerid) (i : Fin 2) : cmIm v i = (v i).im := by
  simp [cmIm]

theorem cmEmb_apply (e : RMerid) (i : Fin 2) : cmEmb e i = ((e i : ℝ) : ℂ) := by
  simp [cmEmb]

/-- Recombination `e + i e'` of two real planar vectors. -/
def cmComb (e e' : RMerid) : CMerid := cmEmb e + Complex.I • cmEmb e'

theorem cmComb_apply (e e' : RMerid) (i : Fin 2) :
    cmComb e e' i = ((e i : ℝ) : ℂ) + Complex.I * ((e' i : ℝ) : ℂ) := by
  simp [cmComb, cmEmb_apply]

theorem cmRe_cmComb (e e' : RMerid) : cmRe (cmComb e e') = e := by
  ext i
  rw [cmRe_apply, cmComb_apply]
  simp

theorem cmIm_cmComb (e e' : RMerid) : cmIm (cmComb e e') = e' := by
  ext i
  rw [cmIm_apply, cmComb_apply]
  simp

theorem cm_decomp (v : CMerid) : v = cmComb (cmRe v) (cmIm v) := by
  ext i
  rw [cmComb_apply, cmRe_apply, cmIm_apply]
  apply Complex.ext <;> simp

theorem cm_apply_decomp (v : CMerid) (i : Fin 2) :
    v i = ((cmRe v i : ℝ) : ℂ) + Complex.I * ((cmIm v i : ℝ) : ℂ) := by
  rw [← cmComb_apply, ← cm_decomp]

theorem cm_norm_sq (v : CMerid) : ‖v‖ ^ 2 = ‖cmRe v‖ ^ 2 + ‖cmIm v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cmRe_apply, cmIm_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, Complex.sq_norm,
    Complex.normSq_apply]
  ring

theorem cmRe_norm_le (v : CMerid) : ‖cmRe v‖ ≤ ‖v‖ := by
  have h := cm_norm_sq v
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖cmIm v‖])

theorem cmIm_norm_le (v : CMerid) : ‖cmIm v‖ ≤ ‖v‖ := by
  have h := cm_norm_sq v
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖cmRe v‖])

theorem cm_norm_le (v : CMerid) : ‖v‖ ≤ ‖cmRe v‖ + ‖cmIm v‖ := by
  have h := cm_norm_sq v
  refine (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).1 ?_
  nlinarith [mul_nonneg (norm_nonneg (cmRe v)) (norm_nonneg (cmIm v))]

theorem cm_enorm_sq (v : CMerid) : ‖v‖ₑ ^ 2 = ‖cmRe v‖ₑ ^ 2 + ‖cmIm v‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    cm_norm_sq]

/-- Pythagoras for the `L²` norm of a `ℂ²`-valued function. -/
theorem cm_eLpNorm_two_sq {h : ℝ × ℝ → CMerid} (hh : AEStronglyMeasurable h volume) :
    eLpNorm h 2 volume ^ 2 =
      eLpNorm (fun z => cmRe (h z)) 2 volume ^ 2 + eLpNorm (fun z => cmIm (h z)) 2 volume ^ 2 := by
  have key : ∀ {E : Type} [NormedAddCommGroup E] (f : ℝ × ℝ → E),
      eLpNorm f 2 volume ^ 2 = ∫⁻ z, ‖f z‖ₑ ^ 2 := by
    intro E _ f
    have h1 := eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure (ℝ × ℝ))) (f := f)
      (p := 2) two_ne_zero
    have e2 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by simp
    have e3 : ((2 : ℝ≥0) : ℝ) = 2 := by simp
    rw [e2, e3] at h1
    simp only [ENNReal.rpow_two] at h1
    exact h1
  rw [key, key, key]
  simp_rw [cm_enorm_sq]
  refine lintegral_add_left' ?_ _
  exact ((cmRe.continuous.comp_aestronglyMeasurable hh).enorm.pow_const 2)

/-- The recombination of two `L^p` real vector fields is an `L^p` complex vector field. -/
theorem cm_memLp_comb {p : ℝ≥0∞} {A B : ℝ × ℝ → RMerid} (hA : MemLp A p volume)
    (hB : MemLp B p volume) : MemLp (fun z => cmComb (A z) (B z)) p volume := by
  have hmeas : AEStronglyMeasurable (fun z => cmComb (A z) (B z)) volume := by
    unfold cmComb
    exact (cmEmb.continuous.comp_aestronglyMeasurable hA.1).add
      ((cmEmb.continuous.comp_aestronglyMeasurable hB.1).const_smul Complex.I)
  refine (hA.norm.add hB.norm).of_le hmeas (Eventually.of_forall fun z => ?_)
  have h := cm_norm_le (cmComb (A z) (B z))
  rw [cmRe_cmComb, cmIm_cmComb] at h
  have h0 : 0 ≤ ‖A z‖ + ‖B z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  simpa [Real.norm_of_nonneg h0] using h

/-- Minkowski for the recombination. -/
theorem cm_eLpNorm_comb_le {p : ℝ≥0∞} (hp : 1 ≤ p) {A B : ℝ × ℝ → RMerid}
    (hA : MemLp A p volume) (hB : MemLp B p volume) :
    eLpNorm (fun z => cmComb (A z) (B z)) p volume ≤ eLpNorm A p volume + eLpNorm B p volume := by
  have h1 : eLpNorm (fun z => cmComb (A z) (B z)) p volume ≤
      eLpNorm ((fun z => ‖A z‖) + (fun z => ‖B z‖)) p volume := by
    refine eLpNorm_mono fun z => ?_
    have h := cm_norm_le (cmComb (A z) (B z))
    rw [cmRe_cmComb, cmIm_cmComb] at h
    have h0 : 0 ≤ ‖A z‖ + ‖B z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa [Real.norm_of_nonneg h0] using h
  refine h1.trans ?_
  have h2 := eLpNorm_add_le hA.1.norm hB.1.norm hp
  rw [eLpNorm_norm, eLpNorm_norm] at h2
  exact h2

/-- Integral of a recombined integrable real pair. -/
theorem cm_integral_comb {A B : ℝ × ℝ → ℝ} (hA : Integrable A volume) (hB : Integrable B volume) :
    Integrable (fun z => ((A z : ℝ) : ℂ) + Complex.I * ((B z : ℝ) : ℂ)) volume ∧
      ∫ z, (((A z : ℝ) : ℂ) + Complex.I * ((B z : ℝ) : ℂ)) =
        ((∫ z, A z : ℝ) : ℂ) + Complex.I * ((∫ z, B z : ℝ) : ℂ) := by
  have h1 : Integrable (fun z => ((A z : ℝ) : ℂ)) volume := hA.ofReal
  have h2 : Integrable (fun z => Complex.I * ((B z : ℝ) : ℂ)) volume :=
    hB.ofReal.const_mul Complex.I
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, integral_complex_ofReal, integral_const_mul, integral_complex_ofReal]

/-- The two real Helmholtz pairs give the complex Helmholtz pair of the recombinations. -/
theorem cm_isPlaneHelmholtz {F G : ℝ × ℝ → CMerid} {Fre Fim Gre Gim : ℝ × ℝ → RMerid}
    (hF : ∀ z, F z = cmComb (Fre z) (Fim z)) (hG : ∀ z, G z = cmComb (Gre z) (Gim z))
    (hre : IsPlaneHelmholtzReal Fre Gre) (him : IsPlaneHelmholtzReal Fim Gim) :
    IsPlaneHelmholtz F G := by
  have hFi : ∀ z i, F z i = ((Fre z i : ℝ) : ℂ) + Complex.I * ((Fim z i : ℝ) : ℂ) :=
    fun z i => by rw [hF z, cmComb_apply]
  have hGi : ∀ z i, G z i = ((Gre z i : ℝ) : ℂ) + Complex.I * ((Gim z i : ℝ) : ℂ) :=
    fun z i => by rw [hG z, cmComb_apply]
  constructor
  · intro φ hφ
    obtain ⟨hI1, hE1⟩ := hre.1 φ hφ
    obtain ⟨hI2, hE2⟩ := him.1 φ hφ
    have hrw : (fun z => G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) =
        fun z => ((Gre z 0 * fderiv ℝ φ z (1, 0) + Gre z 1 * fderiv ℝ φ z (0, 1) : ℝ) : ℂ) +
          Complex.I * ((Gim z 0 * fderiv ℝ φ z (1, 0) + Gim z 1 * fderiv ℝ φ z (0, 1) : ℝ) : ℂ) := by
      funext z
      rw [hGi z 0, hGi z 1]
      push_cast
      ring
    rw [hrw]
    obtain ⟨hi, he⟩ := cm_integral_comb hI1 hI2
    exact ⟨hi, by rw [he, hE1, hE2]; simp⟩
  · intro Ψ hΨ
    obtain ⟨hI1, hE1⟩ := hre.2 Ψ hΨ
    obtain ⟨hI2, hE2⟩ := him.2 Ψ hΨ
    have hrw : (fun z => ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ)) =
        fun z => ((∑ i : Fin 2, (Fre z i - Gre z i) * Ψ z i : ℝ) : ℂ) +
          Complex.I * ((∑ i : Fin 2, (Fim z i - Gim z i) * Ψ z i : ℝ) : ℂ) := by
      funext z
      simp only [Fin.sum_univ_two]
      rw [hFi z 0, hFi z 1, hGi z 0, hGi z 1]
      push_cast
      ring
    rw [hrw]
    obtain ⟨hi, he⟩ := cm_integral_comb hI1 hI2
    exact ⟨hi, by rw [he, hE1, hE2]; simp⟩

/-- Complexification: the `ℂ²` planar Helmholtz projection from the real one. -/
theorem planeHelmholtzLr_of (hReal : PlaneLerayReal) : PlaneHelmholtzLr := by
  intro r hr
  obtain ⟨C, hC, hCF⟩ := hReal r hr
  refine ⟨2 * C, by positivity, fun F hF2 hFr => ?_⟩
  have hFre2 : MemLp (fun z => cmRe (F z)) 2 volume := cmRe.comp_memLp' hF2
  have hFim2 : MemLp (fun z => cmIm (F z)) 2 volume := cmIm.comp_memLp' hF2
  have hFrer : MemLp (fun z => cmRe (F z)) (ENNReal.ofReal r) volume := cmRe.comp_memLp' hFr
  have hFimr : MemLp (fun z => cmIm (F z)) (ENNReal.ofReal r) volume := cmIm.comp_memLp' hFr
  obtain ⟨Gre, hGre2, hGrer, hGre2n, hGrern, hHre⟩ := hCF _ hFre2 hFrer
  obtain ⟨Gim, hGim2, hGimr, hGim2n, hGimrn, hHim⟩ := hCF _ hFim2 hFimr
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr.le
  refine ⟨fun z => cmComb (Gre z) (Gim z), cm_memLp_comb hGre2 hGim2,
    cm_memLp_comb hGrer hGimr, ?_, ?_,
    cm_isPlaneHelmholtz (fun z => cm_decomp (F z)) (fun z => rfl) hHre hHim⟩
  · -- the `L²` contraction
    have hmeas : AEStronglyMeasurable (fun z => cmComb (Gre z) (Gim z)) volume :=
      (cm_memLp_comb hGre2 hGim2).1
    have h1 := cm_eLpNorm_two_sq hmeas
    have h2 := cm_eLpNorm_two_sq hF2.1
    simp only [cmRe_cmComb, cmIm_cmComb] at h1
    have h3 : eLpNorm (fun z => cmComb (Gre z) (Gim z)) 2 volume ^ 2 ≤ eLpNorm F 2 volume ^ 2 := by
      rw [h1, h2]
      exact add_le_add (pow_le_pow_left' hGre2n 2) (pow_le_pow_left' hGim2n 2)
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h3
  · -- the `L^r` bound
    have hre_le : eLpNorm (fun z => cmRe (F z)) (ENNReal.ofReal r) volume ≤
        eLpNorm F (ENNReal.ofReal r) volume := eLpNorm_mono fun z => cmRe_norm_le (F z)
    have him_le : eLpNorm (fun z => cmIm (F z)) (ENNReal.ofReal r) volume ≤
        eLpNorm F (ENNReal.ofReal r) volume := eLpNorm_mono fun z => cmIm_norm_le (F z)
    calc eLpNorm (fun z => cmComb (Gre z) (Gim z)) (ENNReal.ofReal r) volume
        ≤ eLpNorm Gre (ENNReal.ofReal r) volume + eLpNorm Gim (ENNReal.ofReal r) volume :=
          cm_eLpNorm_comb_le hp1 hGrer hGimr
      _ ≤ ENNReal.ofReal C * eLpNorm (fun z => cmRe (F z)) (ENNReal.ofReal r) volume +
          ENNReal.ofReal C * eLpNorm (fun z => cmIm (F z)) (ENNReal.ofReal r) volume :=
          add_le_add hGrern hGimrn
      _ ≤ ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume +
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume := by gcongr
      _ = ENNReal.ofReal (2 * C) * eLpNorm F (ENNReal.ofReal r) volume := by
          rw [← two_mul, ← mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_ofNat]

/-! ## The Riesz-operator leaves -/

/-- The isotropic weight `(1, 1)` of the Calderón-Zygmund core on the plane `Fin 2 → ℝ`
(its gauge `anisoNorm` is the sup norm and its homogeneous dimension is `2`). -/
def planeWeight : Fin 2 → ℕ+ := fun _ => 1

/-- The real `L²` space of the plane `Fin 2 → ℝ`. -/
abbrev PlaneL2 : Type := Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))

/-- The Calderón-Zygmund kernel of `R_iR_k = ∂_i∂_k(-Δ)⁻¹`-type operators on the plane:
`K_{ik}(x) = ∂_i∂_k (2π)⁻¹ log |x| = (2π)⁻¹ (δ_{ik}|x|² - 2 x_i x_k) / |x|⁴` for `x ≠ 0`
(Euclidean norm; the value at `0` is irrelevant). -/
def planeRieszKernel (i k : Fin 2) (x : Fin 2 → ℝ) : ℝ :=
  if x = 0 then 0 else
    (2 * Real.pi)⁻¹ * ((if i = k then (1 : ℝ) else 0) * (x 0 ^ 2 + x 1 ^ 2) - 2 * x i * x k) /
      (x 0 ^ 2 + x 1 ^ 2) ^ 2

/-- **Leaf `PartII-b:T12/1/1/1`** (kernel estimates; the `N = 2` analogue of `newtonHessianKernel`
in `Lib/CZL2/HessianKernel.lean` and `hormander_newtonHessianKernel` in `Lib/CZL2/Hormander.lean`):
the kernels `K_{ik}` are measurable, satisfy the size bound `|K_{ik}(x)| ≤ B |x|_∞^{-2}` and the
Hörmander condition over sup-norm balls `∫_{|x|_∞ > 2|y|_∞} |K_{ik}(x - y) - K_{ik}(x)| dx ≤ B`
(the fields `measurable`, `size`, `hormander` of `UnforcedLeray.CZ.IsCZConvolution`, with the
anisotropic gauge `anisoNorm planeWeight` = sup norm, `homDim planeWeight = 2`). Proof: the kernel is
homogeneous of degree `-2` and smooth off `0`; `|K_{ik}(x)| ≤ 3 (2π)⁻¹ |x|⁻²`, the mean value theorem
on the segment from `x` to `x - y` (which stays at Euclidean distance `≥ |x|/8` from `0` when
`2|y|_∞ < |x|_∞`) bounds `|K(x - y) - K(x)| ≤ C |y| |x|⁻³`, and `∫_{|x|_∞ > 2|y|_∞} |y| |x|⁻³ dx`
is a constant (polar coordinates / `lintegral_anisoNorm_rpow_neg_le` of `Lib/CZCore/Dyadic.lean`). -/
def PlaneRieszKernelCZ : Prop :=
  ∃ B : ℝ≥0, ∀ i k : Fin 2,
    Measurable (planeRieszKernel i k) ∧
    (∀ x : Fin 2 → ℝ, x ≠ 0 →
      |planeRieszKernel i k x| ≤
        B * UnforcedLeray.CZ.anisoNorm planeWeight x ^ (-(UnforcedLeray.CZ.homDim planeWeight : ℝ))) ∧
    (∀ y : Fin 2 → ℝ,
      ∫⁻ x in {x | 2 * UnforcedLeray.CZ.anisoNorm planeWeight y <
          UnforcedLeray.CZ.anisoNorm planeWeight x},
        ‖planeRieszKernel i k (x - y) - planeRieszKernel i k x‖ₑ ≤ B)

/-- A family of **planar Riesz-pair operators** `S_{ik} = ∂_i∂_k Δ⁻¹` (symbol `ξ_iξ_k/|ξ|²`) on the
real `L²(ℝ²)`, `i, k ∈ {0, 1}`:

* each `S_{ik}` is a Calderón-Zygmund convolution operator with kernel `planeRieszKernel i k`
  and constant `B` (`UnforcedLeray.CZ.IsCZConvolution`, which includes the off-support kernel
  representation);
* `S_{ik}ᵀ = S_{ki}` (`∫ S_{ik}f · g = ∫ f · S_{ki}g`);
* `I - S` is an `L²` contraction on pairs: `Σ_i ‖f_i - Σ_k S_{ik}f_k‖² ≤ Σ_i ‖f_i‖²`;
* test identities: `Σ_i S_{ki}(∂_iφ) = ∂_kφ` for `φ ∈ C_c^∞(ℝ²)`, and `Σ_i S_{ki}Ψ_i = 0` for
  `C_c^∞` fields `Ψ` with `div Ψ = 0`. -/
def IsPlaneRieszFamily (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) (B : ℝ≥0) : Prop :=
  (∀ i k : Fin 2,
    UnforcedLeray.CZ.IsCZConvolution planeWeight (S i k) (planeRieszKernel i k) B) ∧
  (∀ (i k : Fin 2) (f g : PlaneL2), ∫ x, S i k f x * g x = ∫ x, f x * S k i g x) ∧
  (∀ f : Fin 2 → PlaneL2, ∑ i, ‖f i - ∑ k, S i k (f k)‖ ^ 2 ≤ ∑ i, ‖f i‖ ^ 2) ∧
  (∀ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ (h : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ φ x (Pi.single i 1)) 2 volume) (k : Fin 2),
      ∑ i, S k i ((h i).toLp _) = (h k).toLp _) ∧
  (∀ Ψ : Fin 2 → (Fin 2 → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (Ψ i) ∧ HasCompactSupport (Ψ i)) →
    (∀ x, ∑ i, fderiv ℝ (Ψ i) x (Pi.single i 1) = 0) →
    ∀ (h : ∀ i : Fin 2, MemLp (Ψ i) 2 volume) (k : Fin 2),
      ∑ i, S k i ((h i).toLp _) = 0)

/-- **Leaf `PartII-b:T12/1/1/2`** (the `L²` theory of the planar Riesz pairs; the `N = 2` copy of
`Lib/CZL2` and the Riesz part of `Lib/LerayLp`; uses `PlaneRieszKernelCZ` for the size and
Hörmander fields): there is a family `S_{ik}` of planar Riesz-pair operators. Proof sketch (SIZE XL,
expect it to be split again): for a test `f ∈ C_c^∞(ℝ²)` put `S_{ik}f = ∂_i∂_k (N * f)`,
`N = (2π)⁻¹ log |x|`; show `S_{ik}f ∈ L²` with the pressure identity
`Σ_{i,k} ‖S_{ik}f‖₂² = ‖f‖₂²` and `Σ_k S_{kk}f = f` (integration by parts; the boundary terms
vanish since `∇N * f = O(|x|⁻¹)`, `∇²N * f = O(|x|⁻²)`), extend to `L²` by density, the off-support
kernel representation by differentiating under the integral for `x` away from the support, the
transposition by symmetry of the kernel. The test identities hold at test level
(`Σ_i ∂_i∂_k N * ∂_iφ = ∂_k (ΔN * φ) = ∂_kφ`; and `Σ_i ∂_i∂_k N * Ψ_i = ∂_k N * div Ψ = 0`), and
the contraction follows from `Σ_i ‖f_i - Σ_k S_{ik}f_k‖² = Σ‖f_i‖² - Σ_i ⟨f_i, Σ_k S_{ik} f_k⟩`
(since `S` is an orthogonal projection: symmetric and idempotent, from the pressure identity). -/
def PlaneRieszFamilyExists : Prop :=
  ∃ (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) (B : ℝ≥0), IsPlaneRieszFamily S B

/-- **Leaf `PartII-b:T12/1/1/3`** (real planar Leray projection from the Riesz family; the `N = 2`
version of `Lib/LerayLp/Leray.lean`, `Helmholtz.lean`, `Duality.lean`). Given the family `S_{ik}`,
put `G = F - S F` componentwise, transporting `ℝ × ℝ` to `Fin 2 → ℝ` by the measure preserving
`MeasurableEquiv.finTwoArrow`/`volume_preserving_finTwoArrow`. Then: `G ∈ L²` with
`‖G‖₂ ≤ ‖F‖₂` is the contraction hypothesis (the pointwise norm of `ℝ²` is Euclidean, so
`‖G(z)‖² = Σ_i G_i(z)²` and `‖G‖₂² = Σ_i ‖G_i‖₂²`); `G ∈ L^r` with
`‖G‖_r ≤ (1 + 4 C) ‖F‖_r` from `UnforcedLeray.CZ.lp_bound` applied to each `S_{ik}` (hypotheses: the
`IsCZConvolution` of `S_{ik}` and of `S_{ki}` and the transposition `hadj`), using `‖F_k‖_r ≤ ‖F‖_r`
and `‖G‖ ≤ ‖F‖ + Σ_{i,k} |S_{ik}F_k|`; the weak divergence identity
`∫ G·∇φ = Σ_k ∫ F_k(∂_kφ - Σ_i S_{ki} ∂_iφ) = 0` by transposition and the first test identity, and
the orthogonality `∫ (F - G)·Ψ = Σ_k ∫ F_k Σ_i S_{ki}Ψ_i = 0` by transposition and the second test
identity. Integrability of the pairings: Hölder against the compactly supported smooth tests
(`F, G ∈ L² ⊂ L²_loc`). -/
def PlaneLerayOfRiesz : Prop := PlaneRieszFamilyExists → PlaneLerayReal

/-- **Conditional `PlaneHelmholtzLr`** from the Riesz family and the two assembly steps. -/
theorem planeHelmholtzLr_of_riesz (h1 : PlaneRieszFamilyExists) (h2 : PlaneLerayOfRiesz) :
    PlaneHelmholtzLr :=
  planeHelmholtzLr_of (h2 h1)

end UnforcedLeray.Short.IIb
