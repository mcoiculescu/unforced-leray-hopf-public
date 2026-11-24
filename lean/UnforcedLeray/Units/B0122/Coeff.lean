import UnforcedLeray.Units.B0122.Leibniz
import UnforcedLeray.Units.B0012

/-!
# B0122 helper: the coefficients `Ω`, `k` and the planar functions

Blueprint unit **B0122** (`paper/main.tex` lines 1867--1871). This file provides

* `isLFam_of_family`: a family of weak derivatives `∂^α F ∈ L²(ℝ²)`, `|α| ≤ n` (the form of
  B0121's `exists_weakDerivs`), gives the one-letter-at-a-time family `IsLFam` used by the
  Leibniz rule of `Units/B0122/Leibniz.lean`;
* `angularTwoField_ae_eq_of_xG`: profiles equal a.e. on `(0, ∞)` (or in `X_G`) have planar
  functions `f₂(r) e^{2iϑ}` equal a.e. on `ℝ²` (polar coordinates);
* the coefficients `Ω(|y|) = e^{-|y|²/4}` and `k(|y|) = (|y|²/4 - 2) e^{-|y|²/4}`
  (tex line 639, `eq:st18-t00001`; `GaussianVortex.radialOmega`, `GaussianVortex.radialK`) as
  `√G ψ` with `ψ` Schwartz: `gS_psiOmega`, `gS_psiK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap ENNReal ContDiff Real

namespace UnforcedLeray.B0122

open UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob UnforcedLeray.B0010

/-! ## From multi-index families to word families -/

/-- Weak derivatives `G α = ∂^α F ∈ L²(ℝ²)` for all `|α| ≤ n` give the word family
`u ↦ G (cnt u)`, with `∂_v (G (cnt u)) = G (cnt (v :: u))` weakly for `|u| < n`. -/
theorem isLFam_of_family {n : ℕ} {F : ℝ × ℝ → ℂ} {G : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : ∀ α ∈ multiIdx n, MemLp (G α) 2 volume ∧ HasWeakDerivOn univ (pdListR α) F (G α)) :
    IsLFam n (fun u => G (cnt u)) := by
  have hmem : ∀ u : List (Fin 2), u.length ≤ n → cnt u ∈ multiIdx n := fun u hu => by
    rw [mem_multiIdx, cnt_le]
    exact hu
  refine ⟨fun u hu => (h _ (hmem u hu)).1, fun u v hu => ?_⟩
  have hu' : HasWeakDerivOn univ (dl u) F (G (cnt u)) :=
    hasWeakDerivOn_perm (dl_perm u).symm (h _ (hmem u hu.le)).2
  have hvu : HasWeakDerivOn univ (dl (v :: u)) F (G (cnt (v :: u))) :=
    hasWeakDerivOn_perm (dl_perm (v :: u)).symm (h _ (hmem (v :: u) (by simp; omega))).2
  intro φ hφ
  have e1 := hu' _ (hφ.dirDeriv (ev v))
  have e2 := hvu φ hφ
  have e : iterDirDeriv (dl u) (dirDeriv (ev v) φ) = iterDirDeriv (dl (v :: u)) φ := by
    have hp : (dl u ++ [ev v]).Perm (dl (v :: u)) := by
      simp [dl, List.perm_append_singleton]
    rw [← iterDirDeriv_perm hp hφ.smooth, iterDirDeriv_append]
    rfl
  rw [e, e2] at e1
  have hl : (dl (v :: u)).length = (dl u).length + 1 := by simp [dl]
  rw [hl, pow_succ] at e1
  have hne : ((-1 : ℂ) ^ (dl u).length) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (-1 : ℂ) ^ (dl u).length * ∫ z, G (cnt u) z * dirDeriv (ev v) φ z =
      (-1 : ℂ) ^ (dl u).length * ((-1 : ℂ) ^ [ev v].length * ∫ z, G (cnt (v :: u)) z * φ z) := by
    rw [← e1, List.length_singleton, pow_one]
    ring
  exact mul_left_cancel₀ hne h3

/-! ## Planar functions of a.e. equal profiles -/

theorem volume_polarRadius_preimage_null {N : Set ℝ} (hNm : MeasurableSet N)
    (hN : volume.restrict (Ioi (0 : ℝ)) N = 0) :
    volume {z : ℝ × ℝ | (polarCoord z).1 ∈ N} = 0 := by
  have hEm : MeasurableSet {z : ℝ × ℝ | (polarCoord z).1 ∈ N} :=
    measurable_polarCoord_fun.fst hNm
  rw [← lintegral_indicator_one hEm, ← lintegral_comp_polarCoord_symm]
  have hT : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := polarCoord_target
  have h1 : ∀ᵐ p ∂(volume.restrict polarCoord.target), p ∈ polarCoord.target :=
    ae_restrict_mem polarCoord.open_target.measurableSet
  have h2 : ∀ᵐ p ∂(volume.restrict polarCoord.target), p.1 ∉ N := by
    rw [hT, Measure.volume_eq_prod, ← Measure.prod_restrict, ae_iff]
    have e : {a : ℝ × ℝ | ¬a.1 ∉ N} = N ×ˢ univ := by
      ext a
      simp
    rw [e, Measure.prod_prod, hN, zero_mul]
  have hae : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
      ({z : ℝ × ℝ | (polarCoord z).1 ∈ N}.indicator 1 (polarCoord.symm p) : ℝ≥0∞))
      =ᵐ[volume.restrict polarCoord.target] 0 := by
    filter_upwards [h1, h2] with p hp1 hp2
    have e : (polarCoord (polarCoord.symm p)).1 = p.1 := by rw [polarCoord.right_inv hp1]
    have hnot : polarCoord.symm p ∉ {z : ℝ × ℝ | (polarCoord z).1 ∈ N} := by
      intro hm
      exact hp2 (e ▸ hm)
    show ENNReal.ofReal p.1 • ({z : ℝ × ℝ | (polarCoord z).1 ∈ N}.indicator 1
      (polarCoord.symm p) : ℝ≥0∞) = 0
    rw [Set.indicator_of_notMem hnot, smul_zero]
  rw [lintegral_congr_ae hae]
  simp

/-- Profiles equal a.e. on `(0, ∞)` have planar functions `f₂(r) e^{2iϑ}` equal a.e. on `ℝ²`. -/
theorem angularTwoField_ae_eq {h₁ h₂ : ℝ → ℂ} (h : h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h₂) :
    angularTwoField h₁ =ᵐ[volume] angularTwoField h₂ := by
  set N := toMeasurable (volume.restrict (Ioi (0 : ℝ))) {r : ℝ | ¬h₁ r = h₂ r} with hNdef
  have hN : volume.restrict (Ioi (0 : ℝ)) N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 h
  rw [EventuallyEq, ae_iff]
  refine measure_mono_null (fun z hz => ?_)
    (volume_polarRadius_preimage_null (measurableSet_toMeasurable _ _) hN)
  apply subset_toMeasurable
  intro he
  apply hz
  simp only [angularTwoField, he]

theorem angularTwoField_ae_eq_of_xG {h₁ h₂ : ℝ → ℂ} (h : h₁ =ᵐ[xGMeasure] h₂) :
    angularTwoField h₁ =ᵐ[volume] angularTwoField h₂ :=
  angularTwoField_ae_eq (B0012.restrict_ac.ae_le h)

theorem angularTwoField_mul (a : ℝ → ℝ) (h : ℝ → ℂ) (z : ℝ × ℝ) :
    angularTwoField (fun r => (a r : ℂ) * h r) z = (a (polarCoord z).1 : ℂ) * angularTwoField h z := by
  simp only [angularTwoField]
  ring

/-! ## The coefficients as `√G ψ` -/

theorem polarRadius_sq (z : ℝ × ℝ) : (polarCoord z).1 ^ 2 = z.1 ^ 2 + z.2 ^ 2 := by
  show Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 = _
  exact Real.sq_sqrt (by positivity)

theorem sqGc_mul_sqGc (z : ℝ × ℝ) :
    sqGc z * sqGc z = (((4 * π)⁻¹ * Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 4)) : ℝ) : ℂ) := by
  rw [sqGc, ← Complex.ofReal_mul, ← sq, sqG_sq]
  rfl

/-- `Ω/√G = 4π √G`, a Schwartz function. -/
def psiOmega : S2 := wS (fun _ => ((4 * π : ℝ) : ℂ)) (Function.HasTemperateGrowth.const _)

/-- `Ω(|y|) = e^{-|y|²/4} = √G · psiOmega`. -/
theorem gS_psiOmega (z : ℝ × ℝ) :
    gS psiOmega z = (GaussianVortex.radialOmega (polarCoord z).1 : ℂ) := by
  rw [gS_apply, psiOmega, wS_apply, ← mul_assoc, sqGc_mul_sqGc, GaussianVortex.radialOmega,
    polarRadius_sq, ← Complex.ofReal_mul]
  congr 1
  field_simp

/-- The polynomial `4π (|y|²/4 - 2)`. -/
def polyK (z : ℝ × ℝ) : ℂ := (π : ℂ) * (crdC 0 z ^ 2 + crdC 1 z ^ 2) + (-(8 * π : ℝ) : ℂ)

theorem hasTemperateGrowth_polyK : polyK.HasTemperateGrowth := by
  have h : polyK = fun z => (π : ℂ) * (crdC 0 z ^ 2 + crdC 1 z ^ 2) + (-(8 * π : ℝ) : ℂ) := rfl
  rw [h]
  exact ((Function.HasTemperateGrowth.const _).mul
    (((hasTemperateGrowth_crdC 0).pow 2).add ((hasTemperateGrowth_crdC 1).pow 2))).add
    (Function.HasTemperateGrowth.const _)

/-- `k/√G = 4π (|y|²/4 - 2) √G`, a Schwartz function. -/
def psiK : S2 := wS polyK hasTemperateGrowth_polyK

/-- `k(|y|) = (|y|²/4 - 2) e^{-|y|²/4} = √G · psiK`. -/
theorem gS_psiK (z : ℝ × ℝ) :
    gS psiK z = (GaussianVortex.radialK (polarCoord z).1 : ℂ) := by
  rw [gS_apply, psiK, wS_apply, ← mul_assoc, sqGc_mul_sqGc, GaussianVortex.radialK,
    GaussianVortex.radialOmega, polarRadius_sq]
  simp only [polyK, crdC, crdL_zero_apply, crdL_one_apply]
  push_cast
  field_simp
  ring

end UnforcedLeray.B0122
