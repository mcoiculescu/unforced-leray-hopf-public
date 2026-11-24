import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_3_of
import UnforcedLeray.Short.PartI.Tasks.SeedModeRegularityProof
import UnforcedLeray.Short.PartI.Tasks.SeedFunctionalProof
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Part III-a, task `PartIII-a:T21/c5/1/1/1` decomposition (`Sub/PartIII-a_T21_c5_1_1_1.lean`)

Source of record: `the November 2 reference manuscript` (SP), lines 593-610,
890-912, 2504-2523, and 2891-2905 (`eq:short-seed-functional`, `eq:short-causal-moving-eq`).

## Proved infrastructure in this file

1. **Continuity, `O((1 + |z₁| + |z₂|)⁻²)` decay of `pdCx k L`, and termwise differentiation of
   `perSum d L` (`norm_dir_eq_one`, `continuous_pdCx_of_contDiff`, `norm_pdCx_le_norm_fderiv`,
   `norm_pdCx_le_inv_sq_of_fderiv`, `translate_bound_of_inv_sq`, `hasFDerivAt_perSum_of_inv_sq_decay`,
   `differentiableAt_perSum_of_inv_sq_decay`, `pdCx_perSum_eq_perSum_pdCx`,
   `seedLamGradPerSum_of`)**:

   `SeedLamPJet1Decay κ`.
2. **Smoothness of the seed profile `h` and exact pointwise identification of `κ.lamP`
   (`seed_h_smooth_of_isSeedKernels`, `seedDualExplicit`, `seedDualExplicit_cont_and_pairing`,
   `eq_of_integral_planeToC_eq`, `lamP_eq_seedDualExplicit`)**:
   Combines `PartI.seedModeRegularity_proof`, `PartI.seedFunctional_proof`,
   `PartI.greenTwoSmooth_proof`, `seedProfileOrderTwo_proof`, `seedPolarPlane_proof`, and
   `ae_eq_of_integral_contDiff_smul_eq` to prove that for any `κ : PlanarFrameKernels` satisfying
   `IsSeedKernels κ`, the witness `(lam, h, hh, ℓ)` has `ContDiff ℝ ∞ (PartI.seedPlanar h)` and
   `ContDiffOn ℝ ∞ h (Ioi 0)`, and `κ.lamP j = seedDualExplicit lam h j` everywhere on `ℝ × ℝ`.
3. **Analytical leaves for `SeedLamPJet1Decay κ` and conditional assembly
   (`seedLamGradPerSum_of_leaves`)**:
   * `SeedDualRadialGDerivBounds` (`PartIII-a:T21/c5/1/1/1/1`, SP 601-610, 890-912): 1D radial
     derivative bounds `‖deriv (seedDualRadialG lam h) r‖ ≤ C₀ * r` on `(0, 1]` and
     `‖deriv (seedDualRadialG lam h) r‖ ≤ C₁ / r ^ 2` on `[1, ∞)` for the quotient
     `seedDualRadialG lam h r = Planar.greenN 2 h r / (radialOmega r - I * lam / 2)`.
   * `PolarKernelJet1Decay` (`PartIII-a:T21/c5/1/1/1/2`, SP 601-610, 2891-2905): 2D polar-to-Cartesian
     `C¹` regularity and `O((1 + |z₁| + |z₂|)⁻²)` `fderiv` bound for any planar kernel of the form
     `y ↦ c * G ‖planeToC y‖ * angPhase n (planeToC y)` whose radial profile `G` satisfies the
     `0`- and `1`-jet bounds at `0` and `∞`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace CutFTCGradPerSum

open ComplCouplingHeat

/-! ## 1. Continuity and `O((1 + |z₁| + |z₂|)⁻²)` bounds for `pdCx k L` -/

/-- Each coordinate unit vector `B0579.dir k` (`k : Fin 2`) has norm `1`. -/
theorem norm_dir_eq_one (k : Fin 2) : ‖B0579.dir k‖ = 1 := by
  fin_cases k <;> simp [B0579.dir]

/-- For any `C¹` planar field `L : ℝ × ℝ → ℂ`, `pdCx k L` is continuous on `ℝ × ℝ`. -/
theorem continuous_pdCx_of_contDiff {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 1 L) (k : Fin 2) :
    Continuous (pdCx k L) := by
  unfold pdCx
  exact (hL.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Pointwise bound `‖pdCx k L z‖ ≤ ‖fderiv ℝ L z‖` for `k : Fin 2`. -/
theorem norm_pdCx_le_norm_fderiv (L : ℝ × ℝ → ℂ) (k : Fin 2) (z : ℝ × ℝ) :
    ‖pdCx k L z‖ ≤ ‖fderiv ℝ L z‖ := by
  unfold pdCx
  calc ‖fderiv ℝ L z (B0579.dir k)‖
      ≤ ‖fderiv ℝ L z‖ * ‖B0579.dir k‖ := (fderiv ℝ L z).le_opNorm (B0579.dir k)
    _ = ‖fderiv ℝ L z‖ := by rw [norm_dir_eq_one k, mul_one]

/-- Pointwise `O((1 + |z₁| + |z₂|)⁻²)` bound for `pdCx k L` from an `fderiv` bound. -/
theorem norm_pdCx_le_inv_sq_of_fderiv {L : ℝ × ℝ → ℂ} {C : ℝ}
    (h1 : ∀ z : ℝ × ℝ, ‖fderiv ℝ L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (k : Fin 2) (z : ℝ × ℝ) :
    ‖pdCx k L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 :=
  (norm_pdCx_le_norm_fderiv L k z).trans (h1 z)

/-! ## 2. Termwise differentiability and `pdCx` of `perSum d L` -/

/-- Converts an `O((1 + |z₁| + |z₂|)⁻²)` bound into the `O((1 + |z₁|)⁻²)` translate bound used by
`UnforcedLeray.Gaussian`. -/
theorem translate_bound_of_inv_sq {f : ℝ × ℝ → ℝ} {C : ℝ}
    (hf : ∀ z : ℝ × ℝ, f z ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) (z : ℝ × ℝ) :
    f z ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  refine (hf z).trans ?_
  rw [Lam0B.rpow_neg_two_eq _ (by positivity)]
  have h1 : (1 + |z.1| + |z.2|)⁻¹ ≤ (1 + |z.1|)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith [abs_nonneg z.2])
  have h2 : ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ ((1 + |z.1|)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  calc C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ |C| * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((1 + |z.1|)⁻¹) ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)

/-- Helper connecting `y - Gaussian.shiftVec (-d) n` with `(y.1 + n * d, y.2)`. -/
theorem sub_shiftVec_neg (d : ℝ) (n : ℤ) (y : ℝ × ℝ) :
    y - Gaussian.shiftVec (-d) n = (y.1 + (n : ℝ) * d, y.2) := by
  rw [Gaussian.sub_shiftVec (-d) n y]
  ext <;> simp

/-- Termwise Fréchet derivative of `perSum d L` for any differentiable `L : ℝ × ℝ → ℂ` with
`O((1 + |z₁| + |z₂|)⁻²)` decay of `L` and `fderiv ℝ L`. -/
theorem hasFDerivAt_perSum_of_inv_sq_decay {L : ℝ × ℝ → ℂ} (hL : Differentiable ℝ L)
    {C₀ C₁ d : ℝ} (hd : d ≠ 0)
    (h0 : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C₀ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (h1 : ∀ z : ℝ × ℝ, ‖fderiv ℝ L z‖ ≤ C₁ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (y : ℝ × ℝ) :
    HasFDerivAt (perSum d L)
      (∑' n : ℤ, fderiv ℝ L (y - Gaussian.shiftVec (-d) n)) y := by
  have heq : perSum d L = fun z => ∑' n : ℤ, L (z - Gaussian.shiftVec (-d) n) :=
    perSum_eq_tsum_shiftVec d L
  rw [heq]
  have hF := Gaussian.hasFDerivAt_tsum_translates hL (s := 2) (c := -d)
    (by norm_num) (neg_ne_zero.2 hd)
    (translate_bound_of_inv_sq h0) (translate_bound_of_inv_sq h1) y
  simp_rw [fderiv_comp_sub] at hF
  exact hF

/-- Differentiability of `perSum d L` at `y` under `O((1 + |z₁| + |z₂|)⁻²)` bounds on `L` and
`fderiv ℝ L`. -/
theorem differentiableAt_perSum_of_inv_sq_decay {L : ℝ × ℝ → ℂ} (hL : Differentiable ℝ L)
    {C₀ C₁ d : ℝ} (hd : d ≠ 0)
    (h0 : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C₀ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (h1 : ∀ z : ℝ × ℝ, ‖fderiv ℝ L z‖ ≤ C₁ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (y : ℝ × ℝ) :
    DifferentiableAt ℝ (perSum d L) y :=
  (hasFDerivAt_perSum_of_inv_sq_decay hL hd h0 h1 y).differentiableAt

/-- Termwise coordinate partial derivative `pdCx k (perSum d L) y = perSum d (pdCx k L) y`. -/
theorem pdCx_perSum_eq_perSum_pdCx {L : ℝ × ℝ → ℂ} (hL : Differentiable ℝ L)
    {C₀ C₁ d : ℝ} (hd : d ≠ 0)
    (h0 : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C₀ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (h1 : ∀ z : ℝ × ℝ, ‖fderiv ℝ L z‖ ≤ C₁ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (perSum d L) y = perSum d (pdCx k L) y := by
  have hF := hasFDerivAt_perSum_of_inv_sq_decay hL hd h0 h1 y
  have ht1 := translate_bound_of_inv_sq h1
  have hsumD : Summable (fun n : ℤ => fderiv ℝ L (y - Gaussian.shiftVec (-d) n)) :=
    Summable.of_norm_bounded
      ((Gaussian.summable_translate (s := 2) (c := -d) (by norm_num) (neg_ne_zero.2 hd) y.1).mul_left |C₁|)
      (fun n => by rw [Gaussian.sub_shiftVec]; exact ht1 _)
  unfold pdCx
  rw [hF.fderiv]
  have hev : (∑' n : ℤ, fderiv ℝ L (y - Gaussian.shiftVec (-d) n)) (B0579.dir k) =
      ∑' n : ℤ, fderiv ℝ L (y - Gaussian.shiftVec (-d) n) (B0579.dir k) :=
    (hsumD.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ (B0579.dir k))).tsum_eq.symm
  rw [hev]
  unfold perSum
  refine tsum_congr fun n => ?_
  rw [sub_shiftVec_neg]

/-! ## 3. `SeedLamPJet1Decay` and reduction of `SeedLamGradPerSum` -/

/-- **`C¹` regularity and first-derivative decay hypothesis for `κ.lamP` (`SeedLamPJet1Decay`)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), the planar dual profiles `κ.lamP j` are `C¹` on
`ℝ × ℝ` and satisfy `‖fderiv ℝ (κ.lamP j) z‖ ≤ C_g * ((1 + |z.1| + |z.2|)⁻¹) ^ 2` matching
`κ.lamP_decay` (SP 593-610, 2891-2905). -/
def SeedLamPJet1Decay (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  (∀ j : Fin 2, ContDiff ℝ 1 (κ.lamP j)) ∧
  ∃ C_g : ℝ, 0 ≤ C_g ∧
    ∀ (j : Fin 2) (z : ℝ × ℝ),
      ‖fderiv ℝ (κ.lamP j) z‖ ≤ C_g * ((1 + |z.1| + |z.2|)⁻¹) ^ 2

/-- Conditional proof of `SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`) from
`SeedLamPJet1Decay κ`. -/
theorem seedLamGradPerSum_of (κ : PlanarFrameKernels) (hJet : SeedLamPJet1Decay κ) :
    SeedLamGradPerSum κ := by
  intro hκ
  obtain ⟨hCD, C_g, hC_g0, hD1⟩ := hJet hκ
  obtain ⟨C₀, hD0⟩ := κ.lamP_decay
  refine ⟨C_g, hC_g0,
    fun j k => continuous_pdCx_of_contDiff (hCD j) k,
    fun j k z => norm_pdCx_le_inv_sq_of_fderiv (hD1 j) k z,
    fun {d} hd j k y => ?_⟩
  have hd_ne : d ≠ 0 := by linarith
  have hDiff : Differentiable ℝ (κ.lamP j) := (hCD j).differentiable one_ne_zero
  exact ⟨differentiableAt_perSum_of_inv_sq_decay hDiff hd_ne (hD0 j) (hD1 j) y,
    pdCx_perSum_eq_perSum_pdCx hDiff hd_ne (hD0 j) (hD1 j) k y⟩

/-! ## 4. Explicit formula for `κ.lamP` and uniqueness on `ℝ × ℝ` -/

/-- Explicit radial quotient `G(r) = greenN 2 h(r) / (Ω(r) - iλ/2)` for `r > 0` (`0` for `r ≤ 0`)
from `PartI_S09_2` and `T21_c1_a_3_of` (SP 601-610, 890-912). -/
def seedDualRadialG (lam : ℂ) (h : ℝ → ℂ) (r : ℝ) : ℂ :=
  if 0 < r then
    Planar.greenN 2 h r / ((GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2)
  else 0

/-- Explicit planar dual kernel pair `λ₀(y), λ₁(y)` representing `PartI.seedEll h` on sectors
`±2` (SP 601-610, 2891-2897). -/
def seedDualExplicit (lam : ℂ) (h : ℝ → ℂ) (j : Fin 2) (y : ℝ × ℝ) : ℂ :=
  let c : ℂ := (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ)
  if j = 0 then
    c * seedDualRadialG lam h ‖planeToC y‖ * Planar.NUE.Ang.angPhase (-2) (planeToC y)
  else
    conj c * conj (seedDualRadialG lam h ‖planeToC y‖) * Planar.NUE.Ang.angPhase 2 (planeToC y)

private lemma seedPlanar_eq_of_eqOn_Ioi {f g : ℝ → ℂ} (hfg : EqOn f g (Ioi 0)) :
    PartI.seedPlanar f = PartI.seedPlanar g := by
  funext z
  unfold PartI.seedPlanar Planar.NUE.Ang.ofProfile Planar.NUE.Ang.angPhase
  by_cases hz : z = 0
  · subst hz; simp
  · rw [hfg (norm_pos_iff.mpr hz)]

/-- Under `IsSeedKernels κ`, the witness profile `h` itself agrees with its smooth representative on
`Ioi 0`, so `PartI.seedPlanar h` is `C^∞` on `ℂ` and `h` is `C^∞` on `Ioi 0`. -/
theorem seed_h_smooth_of_isSeedKernels {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      PartI.IsSeedXG lam (hh.toLp h) ℓ ∧
      ContDiff ℝ ∞ (PartI.seedPlanar h) ∧
      ContDiffOn ℝ ∞ h (Ioi 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
        ‖iteratedFDeriv ℝ k (PartI.seedPlanar h) y‖ ≤
          C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) ∧
      (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ y, κ.lamP 0 y * f (planeToC y) = PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
        ∫ y, κ.lamP 1 y * f (planeToC y) =
          conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))) := by
  obtain ⟨lam, h, hh, ℓ, hIS, he0, _he1, hcl⟩ := hκ
  obtain ⟨_, _, h', hae', hsm', hder', _, _, _, _, _, _⟩ :=
    PartI.seedModeRegularity_proof lam h hh ℓ hIS
  have hcont_h' : ContinuousOn h' (Ioi 0) := by
    have hcd : ContinuousOn (fun r : ℝ => PartI.seedPlanar h' (r : ℂ)) (Ioi 0) :=
      (hsm'.continuous.comp Complex.continuous_ofReal).continuousOn
    exact hcd.congr (fun r hr => (seedPlanar_ofReal_eq h' r hr).symm)
  have hcont_h : ContinuousOn h (Ioi 0) := by
    have hce : ContinuousOn (fun r : ℝ => κ.e 0 (r, 0)) (Ioi 0) :=
      ((κ.e_cont 0).comp (continuous_id.prodMk continuous_const)).continuousOn
    refine hce.congr (fun r hr => ?_)
    have hpl : planeToC (r, 0) = (r : ℂ) := by
      apply Complex.ext <;> simp [planeToC]
    dsimp only
    rw [he0 (r, 0), hpl, seedPlanar_ofReal_eq h r hr]
  have heq_h'h : EqOn h' h (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hcont_h' hcont_h
  have hsp_eq : PartI.seedPlanar h = PartI.seedPlanar h' :=
    (seedPlanar_eq_of_eqOn_Ioi heq_h'h).symm
  have hsm : ContDiff ℝ ∞ (PartI.seedPlanar h) := hsp_eq ▸ hsm'
  have hcd_h : ContDiffOn ℝ ∞ h (Ioi 0) := by
    have hcd : ContDiffOn ℝ ∞ (fun r : ℝ => PartI.seedPlanar h (r : ℂ)) (Ioi 0) :=
      (hsm.comp Complex.ofRealCLM.contDiff).contDiffOn.mono (subset_univ _)
    exact hcd.congr (fun r hr => (seedPlanar_ofReal_eq h r hr).symm)
  refine ⟨lam, h, hh, ℓ, hIS, hsm, hcd_h, fun k => ?_, hcl⟩
  rw [hsp_eq]
  exact hder' k

/-- Continuity, `O((1 + |y₁| + |y₂|)⁻²)` decay, and sector test-function pairing of
`seedDualExplicit lam h`. -/
theorem seedDualExplicit_cont_and_pairing (lam : ℂ) (h : ℝ → ℂ)
    (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ)
    (hS : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (hsm : ContDiff ℝ ∞ (PartI.seedPlanar h))
    (hon : ContDiffOn ℝ ∞ h (Ioi 0)) :
    (∀ j : Fin 2, Continuous (seedDualExplicit lam h j)) ∧
    (∃ C : ℝ, ∀ (j : Fin 2) (y : ℝ × ℝ),
      ‖seedDualExplicit lam h j y‖ ≤ C * (1 + |y.1| + |y.2|)⁻¹ ^ 2) ∧
    (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ y, seedDualExplicit lam h 0 y * f (planeToC y) =
        PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
      ∫ y, seedDualExplicit lam h 1 y * f (planeToC y) =
        conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))) := by
  have hg_props := PartI.seedQuotientSmooth_proof lam h hh ℓ hS hon
  -- Note: `seedQuotientSmooth_of greenTwoSmooth_proof` constructs literally
  -- `g r = Planar.greenN 2 h r / ((radialOmega r : ℂ) - Complex.I * lam / 2)`
  let g : ℝ → ℂ := fun r =>
    Planar.greenN 2 h r / ((GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2)
  have hre := hS.re_pos
  set q : B0010.XG := hh.toLp h
  have hGs : ContDiffOn ℝ ∞ (fun r : ℝ => Planar.greenN 2 h r) (Ioi 0) :=
    PartI.greenTwoSmooth_proof h hh hon
  have hΩ : ContDiff ℝ ∞ (fun r : ℝ => (GaussianVortex.radialOmega r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp GaussianVortex.radialOmega_smooth
  have hK : ContDiff ℝ ∞ (fun r : ℝ => (GaussianVortex.radialK r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp GaussianVortex.radialK_smooth
  have hqh : (⇑q) =ᵐ[volume.restrict (Ioi (0 : ℝ))] h :=
    B0012.restrict_ac.ae_le hh.coeFn_toLp
  have hgreen : ∀ r, Planar.greenN 2 (⇑q) r = Planar.greenN 2 h r :=
    PartI.adjEig_greenN_congr hqh
  have hgd : ContDiffOn ℝ ∞ g (Ioi 0) := by
    have hD' : ContDiffOn ℝ ∞
        (fun r : ℝ => ((GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2)⁻¹) (Ioi 0) := by
      intro r _
      have hat : ContDiffAt ℝ ∞ (fun z : ℂ => z⁻¹)
          ((GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2) :=
        (contDiffAt_inv ℂ (PartI.adjEig_den_ne hre _)).restrict_scalars ℝ
      exact hat.comp_contDiffWithinAt r ((hΩ.sub contDiff_const).contDiffWithinAt)
    simpa only [g, div_eq_mul_inv] using hGs.mul hD'
  have hgk : ∀ r : ℝ, 0 < r → Blueprint.Planar.strainK r ≠ 0 →
      g r = h r / (Blueprint.Planar.strainK r : ℂ) := by
    intro r hr hk
    have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        ((GaussianVortex.radialOmega x : ℂ) - Complex.I * lam / 2) * h x =
          (GaussianVortex.radialK x : ℂ) * Planar.greenN 2 h x := by
      have h0 := B0012.restrict_ac.ae_le (PartI.adjEig_pointwise hS.eigen)
      filter_upwards [h0, hqh] with x hx hx'
      rw [← hx', ← hgreen x]
      exact hx
    have hcont : ContinuousOn
        (fun x : ℝ => ((GaussianVortex.radialOmega x : ℂ) - Complex.I * lam / 2) * h x) (Ioi 0) :=
      ((hΩ.continuous.sub continuous_const).continuousOn).mul hon.continuousOn
    have hcont2 : ContinuousOn
        (fun x : ℝ => (GaussianVortex.radialK x : ℂ) * Planar.greenN 2 h x) (Ioi 0) :=
      hK.continuous.continuousOn.mul hGs.continuousOn
    have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcont hcont2 hr
    simp only at heq
    have hk' : (Blueprint.Planar.strainK r : ℂ) ≠ 0 := by exact_mod_cast hk
    rw [Cons.C01.strainK_eq] at hk' ⊢
    have hD := PartI.adjEig_den_ne hre (GaussianVortex.radialOmega r)
    dsimp [g]
    rw [div_eq_div_iff hD hk']
    linear_combination -heq
  obtain ⟨C_G, hC_G0, hC_G⟩ := Planar.norm_greenN_two_le_XG
  have hC1 : ∀ r : ℝ, 1 ≤ r → ‖g r‖ ≤ (2 * (C_G * ‖q‖) / lam.re) / r ^ 2 := by
    intro r hr1
    have hr0 : 0 < r := by linarith
    have hb := hC_G q r hr0
    have hmin : min r ((r ^ 2)⁻¹) ≤ (r ^ 2)⁻¹ := min_le_right _ _
    have hG_le : ‖Planar.greenN 2 h r‖ ≤ C_G * ‖q‖ * (r ^ 2)⁻¹ := by
      rw [← hgreen r]
      exact hb.trans (by gcongr)
    have hD : lam.re / 2 ≤ ‖(GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2‖ := by
      have h1 := Complex.abs_im_le_norm ((GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2)
      rw [PartI.adjEig_im_den, abs_neg, abs_of_pos (by linarith)] at h1
      exact h1
    have hDpos : 0 < lam.re / 2 := by linarith
    dsimp [g]
    rw [norm_div]
    calc ‖Planar.greenN 2 h r‖ / ‖(GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2‖
        ≤ (C_G * ‖q‖ * (r ^ 2)⁻¹) / (lam.re / 2) :=
          div_le_div₀ (by positivity) hG_le hDpos hD
      _ = 2 * (C_G * ‖q‖) / lam.re / r ^ 2 := by field_simp
  obtain ⟨C0, hC0⟩ := seedProfileOrderTwo_proof h hsm
  set G : ℝ → ℂ := seedDualRadialG lam h
  have hGc : ContinuousOn G (Ioi 0) :=
    hgd.continuousOn.congr (fun r hr => by simp [G, seedDualRadialG, g, mem_Ioi.mp hr])
  have hG0 : G 0 = 0 := by simp [G, seedDualRadialG]
  have hGr : ∀ r : ℝ, 0 < r → G r = g r := fun r hr => by simp [G, seedDualRadialG, g, hr]
  have hGn : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C * r ^ 2 := by
    refine ⟨C0, fun r hr hr1 => ?_⟩
    have hk := strainK_abs_ge_one hr1 hr
    have hk0 : Blueprint.Planar.strainK r ≠ 0 := by
      intro h0; rw [h0] at hk; norm_num at hk
    rw [hGr r hr, hgk r hr hk0, norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc ‖h r‖ / |Blueprint.Planar.strainK r| ≤ ‖h r‖ :=
          div_le_self (norm_nonneg _) hk
      _ ≤ _ := hC0 r hr hr1
  have hGinf : ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖G r‖ ≤ C / r ^ 2 :=
    ⟨2 * (C_G * ‖q‖) / lam.re, fun r hr => by rw [hGr r (by linarith)]; exact hC1 r hr⟩
  have hGnb : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C := by
    obtain ⟨C, hC⟩ := hGn
    refine ⟨|C|, fun r hr hr1 => (hC r hr hr1).trans ?_⟩
    have : r ^ 2 ≤ 1 := by nlinarith
    calc C * r ^ 2 ≤ |C| * r ^ 2 := by gcongr; exact le_abs_self C
      _ ≤ |C| * 1 := by gcongr
      _ = |C| := mul_one _
  have hGc' : ContinuousOn (fun r => conj (G r)) (Ioi 0) :=
    Complex.continuous_conj.comp_continuousOn hGc
  have hG0' : conj (G 0) = 0 := by rw [hG0]; simp
  have hGn' : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖conj (G r)‖ ≤ C * r ^ 2 := by
    obtain ⟨C, hC⟩ := hGn
    exact ⟨C, fun r hr hr1 => by rw [Complex.norm_conj]; exact hC r hr hr1⟩
  have hGinf' : ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖conj (G r)‖ ≤ C / r ^ 2 := by
    obtain ⟨C, hC⟩ := hGinf
    exact ⟨C, fun r hr => by rw [Complex.norm_conj]; exact hC r hr⟩
  have hGnb' : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖conj (G r)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hGnb
    exact ⟨C, fun r hr hr1 => by rw [Complex.norm_conj]; exact hC r hr hr1⟩
  set c : ℂ := (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ) with hc
  have hc2 : c * (2 * Real.pi : ℂ) = (PartI.seedJ h)⁻¹ := by
    have : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this]
    rw [hc]; field_simp
  have hcc : conj c * (2 * Real.pi : ℂ) = conj ((PartI.seedJ h)⁻¹) := by
    have := congrArg (fun z => conj z) hc2
    simpa [map_ofNat] using this
  obtain ⟨hc0, hb0⟩ := kernel_props G c (fun y => Planar.NUE.Ang.angPhase (-2) (planeToC y))
    hGc hG0 hGn hGinf (fun y hy => angPhase_planeToC_continuousAt _ hy)
    (fun y => norm_angPhase_le _ _)
  obtain ⟨hc1, hb1⟩ := kernel_props (fun r => conj (G r)) (conj c)
    (fun y => Planar.NUE.Ang.angPhase 2 (planeToC y)) hGc' hG0' hGn' hGinf'
    (fun y hy => angPhase_planeToC_continuousAt _ hy) (fun y => norm_angPhase_le _ _)
  have hae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      Blueprint.Planar.strainK r ≠ 0 ∧ 0 < r :=
    (ae_restrict_of_ae PartI.ae_strainK_ne_zero).and (ae_restrict_mem measurableSet_Ioi)
  refine ⟨?_, ?_, ?_⟩
  · intro j; fin_cases j
    · exact hc0
    · exact hc1
  · obtain ⟨Ca, hCa⟩ := hb0
    obtain ⟨Cb, hCb⟩ := hb1
    refine ⟨max Ca Cb, fun j y => ?_⟩
    have hp : 0 ≤ (1 + |y.1| + |y.2|)⁻¹ ^ 2 := by positivity
    fin_cases j
    · exact (hCa y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
    · exact (hCb y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)
  · intro f hf hfc
    constructor
    · have e1 := seedPolarPlane_proof 2 G hGc hGnb f hf hfc
      have hI : ∫ y : ℝ × ℝ, seedDualExplicit lam h 0 y * f (planeToC y) =
          c * ∫ y : ℝ × ℝ, G ‖planeToC y‖ * Planar.NUE.Ang.angPhase (-2) (planeToC y) * f (planeToC y) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [seedDualExplicit, ↓reduceIte]; ring
      rw [hI, e1, ← mul_assoc, hc2]
      unfold PartI.seedEll
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with r ⟨hk, hr⟩
      rw [hGr r hr, hgk r hr hk]; ring
    · have e2 := seedPolarPlane_proof (-2) (fun r => conj (G r)) hGc' hGnb' f hf hfc
      rw [neg_neg] at e2
      have hI : ∫ y : ℝ × ℝ, seedDualExplicit lam h 1 y * f (planeToC y) =
          conj c * ∫ y : ℝ × ℝ, conj (G ‖planeToC y‖) * Planar.NUE.Ang.angPhase 2 (planeToC y) * f (planeToC y) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [seedDualExplicit, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]; ring
      rw [hI, e2]
      unfold PartI.seedEll
      rw [map_mul, ← integral_conj, ← mul_assoc, ← hcc]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with r ⟨hk, hr⟩
      rw [hGr r hr, hgk r hr hk]
      simp [map_div₀, Complex.conj_ofReal]
      left; ring

/-- Two continuous functions on `ℝ × ℝ` having equal integrals against all smooth compactly
supported `f : ℂ → ℂ` composed with `planeToC` are equal everywhere on `ℝ × ℝ`. -/
theorem eq_of_integral_planeToC_eq {F₁ F₂ : ℝ × ℝ → ℂ}
    (hF₁ : Continuous F₁) (hF₂ : Continuous F₂)
    (hInt : ∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ y : ℝ × ℝ, F₁ y * f (planeToC y) = ∫ y : ℝ × ℝ, F₂ y * f (planeToC y)) :
    F₁ = F₂ := by
  have hae : F₁ =ᵐ[volume] F₂ := by
    refine ae_eq_of_integral_contDiff_smul_eq hF₁.locallyIntegrable hF₂.locallyIntegrable ?_
    intro g hg hgc
    let f : ℂ → ℂ := fun z => ((g (Complex.equivRealProdCLM z) : ℝ) : ℂ)
    have hf_diff : ContDiff ℝ ∞ f :=
      Complex.ofRealCLM.contDiff.comp (hg.comp Complex.equivRealProdCLM.contDiff)
    have hf_supp : HasCompactSupport f := by
      have h1 : HasCompactSupport (fun y : ℝ × ℝ => ((g y : ℝ) : ℂ)) :=
        hgc.comp_left Complex.ofReal_zero
      exact h1.comp_homeomorph Complex.equivRealProdCLM.toHomeomorph
    have hplane : ∀ y : ℝ × ℝ, f (planeToC y) = (g y : ℂ) := by
      intro y
      have hpy : Complex.equivRealProdCLM (planeToC y) = y := by
        ext <;> simp [planeToC]
      change ((g (Complex.equivRealProdCLM (planeToC y)) : ℝ) : ℂ) = (g y : ℂ)
      rw [hpy]
    have hsmul : ∀ (F : ℝ × ℝ → ℂ) (y : ℝ × ℝ), g y • F y = F y * f (planeToC y) := by
      intro F y
      rw [hplane y, Complex.real_smul, mul_comm]
    simp_rw [hsmul]
    exact hInt f hf_diff hf_supp
  exact Measure.eq_of_ae_eq hae hF₁ hF₂

/-- Under `IsSeedKernels κ`, `κ.lamP` equals `seedDualExplicit lam h` everywhere on `ℝ × ℝ`. -/
theorem lamP_eq_seedDualExplicit {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      PartI.IsSeedXG lam (hh.toLp h) ℓ ∧
      ContDiff ℝ ∞ (PartI.seedPlanar h) ∧
      ContDiffOn ℝ ∞ h (Ioi 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
        ‖iteratedFDeriv ℝ k (PartI.seedPlanar h) y‖ ≤
          C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) ∧
      (∀ j : Fin 2, κ.lamP j = seedDualExplicit lam h j) := by
  obtain ⟨lam, h, hh, ℓ, hIS, hsm, hon, hder, hcl⟩ := seed_h_smooth_of_isSeedKernels hκ
  obtain ⟨hcont_exp, _, hpair_exp⟩ := seedDualExplicit_cont_and_pairing lam h hh ℓ hIS hsm hon
  refine ⟨lam, h, hh, ℓ, hIS, hsm, hon, hder, fun j => ?_⟩
  fin_cases j
  · exact eq_of_integral_planeToC_eq (κ.lamP_cont 0) (hcont_exp 0)
      (fun f hf hfc => (hcl f hf hfc).1.trans (hpair_exp f hf hfc).1.symm)
  · exact eq_of_integral_planeToC_eq (κ.lamP_cont 1) (hcont_exp 1)
      (fun f hf hfc => (hcl f hf hfc).2.trans (hpair_exp f hf hfc).2.symm)

/-! ## 5. Analytical leaves for `SeedLamPJet1Decay` and conditional assembly -/

/-- **Leaf 1 (`PartIII-a:T21/c5/1/1/1/1`, `SeedDualRadialGDerivBounds`, SP 601-610, 890-912)**:
For any seed triple `(lam, h, hh, ℓ)` with smooth `PartI.seedPlanar h`, `h` smooth on `Ioi 0`, and
Gaussian decay of `PartI.seedPlanar h`, the radial quotient `G = seedDualRadialG lam h`
(`G r = Planar.greenN 2 h r / (radialOmega r - I * lam / 2)` for `r > 0`, `G 0 = 0`) satisfies:
* `ContDiffOn ℝ ∞ G (Ioi 0)` and `G 0 = 0`,
* near `0`: `∃ C₀ : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C₀ * r ^ 2 ∧ ‖deriv G r‖ ≤ C₀ * r`,
* far field: `∃ C₁ : ℝ, ∀ r : ℝ, 1 ≤ r → ‖G r‖ ≤ C₁ / r ^ 2 ∧ ‖deriv G r‖ ≤ C₁ / r ^ 2`.
Composed by task `PartIII-a:T21/c5/1/1/1` via `seedLamGradPerSum_of_leaves`. -/
def SeedDualRadialGDerivBounds : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ →
    ContDiff ℝ ∞ (PartI.seedPlanar h) →
    ContDiffOn ℝ ∞ h (Ioi 0) →
    (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
      ‖iteratedFDeriv ℝ k (PartI.seedPlanar h) y‖ ≤
        C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) →
    let G := seedDualRadialG lam h
    ContDiffOn ℝ ∞ G (Ioi 0) ∧
    G 0 = 0 ∧
    (∃ C₀ : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C₀ * r ^ 2 ∧ ‖deriv G r‖ ≤ C₀ * r) ∧
    (∃ C₁ : ℝ, ∀ r : ℝ, 1 ≤ r → ‖G r‖ ≤ C₁ / r ^ 2 ∧ ‖deriv G r‖ ≤ C₁ / r ^ 2)

/-- **Leaf 2 (`PartIII-a:T21/c5/1/1/1/2`, `PolarKernelJet1Decay`, SP 601-610, 2891-2905)**:
First-jet generalization of `kernel_props` (`Sub/T21_c1_a_3_of.lean`): for any radial profile
`G : ℝ → ℂ` smooth on `Ioi 0` with `G 0 = 0`, near-origin bounds `‖G r‖ ≤ C₀ * r ^ 2` and
`‖deriv G r‖ ≤ C₀ * r` on `(0, 1]`, and far-field bounds `‖G r‖ ≤ C₁ / r ^ 2` and
`‖deriv G r‖ ≤ C₁ / r ^ 2` on `[1, ∞)`, and any scalar `c : ℂ` and sector `n ∈ ({-2, 2} : Set ℤ)`,
the planar kernel `y ↦ c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase n (planeToC y)` is `C¹` on
`ℝ × ℝ` and its Fréchet derivative satisfies `O((1 + |z₁| + |z₂|)⁻²)` decay.
Composed by task `PartIII-a:T21/c5/1/1/1` via `seedLamGradPerSum_of_leaves`. -/
def PolarKernelJet1Decay : Prop :=
  ∀ (G : ℝ → ℂ) (c : ℂ) (n : ℤ), (n = -2 ∨ n = 2) →
    ContDiffOn ℝ ∞ G (Ioi 0) →
    G 0 = 0 →
    (∃ C₀ : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C₀ * r ^ 2 ∧ ‖deriv G r‖ ≤ C₀ * r) →
    (∃ C₁ : ℝ, ∀ r : ℝ, 1 ≤ r → ‖G r‖ ≤ C₁ / r ^ 2 ∧ ‖deriv G r‖ ≤ C₁ / r ^ 2) →
    let F : ℝ × ℝ → ℂ := fun y => c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase n (planeToC y)
    ContDiff ℝ 1 F ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × ℝ, ‖fderiv ℝ F z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2

/-- Deduces `SeedLamPJet1Decay κ` from `SeedDualRadialGDerivBounds` and `PolarKernelJet1Decay`. -/
theorem seedLamPJet1Decay_of_leaves (κ : PlanarFrameKernels)
    (hRad : SeedDualRadialGDerivBounds) (hPol : PolarKernelJet1Decay) :
    SeedLamPJet1Decay κ := by
  intro hκ
  obtain ⟨lam, h, hh, ℓ, hIS, hsm, hon, hder, hlamP⟩ := lamP_eq_seedDualExplicit hκ
  obtain ⟨hGd, hG0, ⟨C₀, hC₀⟩, ⟨C₁, hC₁⟩⟩ := hRad lam h hh ℓ hIS hsm hon hder
  set G := seedDualRadialG lam h
  set c : ℂ := (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ)
  obtain ⟨hCD0, C_0, hC_0, hB0⟩ :=
    hPol G c (-2) (Or.inl rfl) hGd hG0 ⟨C₀, hC₀⟩ ⟨C₁, hC₁⟩
  -- For `j = 1`, `seedDualExplicit lam h 1 y = conj (seedDualExplicit lam h 0 y)`
  have h1_eq_conj : seedDualExplicit lam h 1 = Complex.conjLIE ∘ (seedDualExplicit lam h 0) := by
    funext y
    simp only [Function.comp_apply, Complex.conjLIE_apply, seedDualExplicit,
      show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, map_mul]
    congr 1
    unfold Planar.NUE.Ang.angPhase
    by_cases hy : planeToC y = 0
    · simp [hy]
    · simp only [zpow_neg, zpow_two, map_inv₀, map_mul, map_div₀, Complex.conj_ofReal]
      have hsq : planeToC y * conj (planeToC y) = (‖planeToC y‖ : ℂ) ^ 2 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      have hn : (‖planeToC y‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hy).ne'
      have hcy : conj (planeToC y) ≠ 0 := star_ne_zero.mpr hy
      have hdiv : (‖planeToC y‖ : ℂ) / conj (planeToC y) = planeToC y / (‖planeToC y‖ : ℂ) := by
        rw [div_eq_div_iff hcy hn]
        linear_combination -hsq
      rw [mul_inv, inv_div, hdiv]
  have h0_eq : κ.lamP 0 = fun y => c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase (-2) (planeToC y) := by
    rw [hlamP 0]
    funext y
    simp [seedDualExplicit, c, G]
  have h1_eq : κ.lamP 1 = Complex.conjLIE ∘ (κ.lamP 0) := by
    rw [hlamP 1, hlamP 0, h1_eq_conj]
  have hCD_0 : ContDiff ℝ 1 (κ.lamP 0) := h0_eq ▸ hCD0
  have hCD_1 : ContDiff ℝ 1 (κ.lamP 1) := by
    rw [h1_eq]
    exact Complex.conjCLE.contDiff.comp hCD_0
  refine ⟨fun j => by fin_cases j; exacts [hCD_0, hCD_1], C_0, hC_0, fun j z => ?_⟩
  fin_cases j
  · change ‖fderiv ℝ (κ.lamP 0) z‖ ≤ C_0 * ((1 + |z.1| + |z.2|)⁻¹) ^ 2
    rw [h0_eq]
    exact hB0 z
  · change ‖fderiv ℝ (κ.lamP 1) z‖ ≤ C_0 * ((1 + |z.1| + |z.2|)⁻¹) ^ 2
    rw [h1_eq]
    have hdiff0 : DifferentiableAt ℝ (κ.lamP 0) z := (hCD_0.differentiable one_ne_zero) z
    have hf1 : fderiv ℝ (Complex.conjLIE ∘ κ.lamP 0) z =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (κ.lamP 0) z) :=
      ((Complex.conjCLE.hasFDerivAt).comp z hdiff0.hasFDerivAt).fderiv
    have hnorm_le : ‖fderiv ℝ (Complex.conjLIE ∘ κ.lamP 0) z‖ ≤ ‖fderiv ℝ (κ.lamP 0) z‖ := by
      rw [hf1]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
      change ‖conj ((fderiv ℝ (κ.lamP 0) z) v)‖ ≤ ‖fderiv ℝ (κ.lamP 0) z‖ * ‖v‖
      rw [Complex.norm_conj]
      exact (fderiv ℝ (κ.lamP 0) z).le_opNorm v
    exact hnorm_le.trans (by rw [h0_eq]; exact hB0 z)

/-- Conditional assembly of `SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`) from
`SeedDualRadialGDerivBounds` and `PolarKernelJet1Decay`. -/
theorem seedLamGradPerSum_of_leaves (κ : PlanarFrameKernels)
    (hRad : SeedDualRadialGDerivBounds) (hPol : PolarKernelJet1Decay) :
    SeedLamGradPerSum κ :=
  seedLamGradPerSum_of κ (seedLamPJet1Decay_of_leaves κ hRad hPol)

end CutFTCGradPerSum

/-- Top-level alias for `CutFTCGradPerSum.SeedLamPJet1Decay`. -/
abbrev SeedLamPJet1Decay (κ : PlanarFrameKernels) : Prop :=
  CutFTCGradPerSum.SeedLamPJet1Decay κ

/-- Top-level alias for `CutFTCGradPerSum.seedDualRadialG`. -/
abbrev seedDualRadialG (lam : ℂ) (h : ℝ → ℂ) (r : ℝ) : ℂ :=
  CutFTCGradPerSum.seedDualRadialG lam h r

/-- Top-level alias for `CutFTCGradPerSum.seedDualExplicit`. -/
abbrev seedDualExplicit (lam : ℂ) (h : ℝ → ℂ) (j : Fin 2) (y : ℝ × ℝ) : ℂ :=
  CutFTCGradPerSum.seedDualExplicit lam h j y

/-- Top-level alias for `CutFTCGradPerSum.SeedDualRadialGDerivBounds` (`PartIII-a:T21/c5/1/1/1/1`). -/
abbrev SeedDualRadialGDerivBounds : Prop :=
  CutFTCGradPerSum.SeedDualRadialGDerivBounds

/-- Top-level alias for `CutFTCGradPerSum.PolarKernelJet1Decay` (`PartIII-a:T21/c5/1/1/1/2`). -/
abbrev PolarKernelJet1Decay : Prop :=
  CutFTCGradPerSum.PolarKernelJet1Decay

/-- Top-level conditional proof of `SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`) from
`SeedLamPJet1Decay κ`. -/
theorem seedLamGradPerSum_of (κ : PlanarFrameKernels) (hJet : SeedLamPJet1Decay κ) :
    SeedLamGradPerSum κ :=
  CutFTCGradPerSum.seedLamGradPerSum_of κ hJet

/-- Top-level conditional proof of `SeedLamPJet1Decay κ` from `SeedDualRadialGDerivBounds` and
`PolarKernelJet1Decay`. -/
theorem seedLamPJet1Decay_of_leaves (κ : PlanarFrameKernels)
    (hRad : SeedDualRadialGDerivBounds) (hPol : PolarKernelJet1Decay) :
    SeedLamPJet1Decay κ :=
  CutFTCGradPerSum.seedLamPJet1Decay_of_leaves κ hRad hPol

/-- Top-level conditional assembly of `SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`) from
`SeedDualRadialGDerivBounds` and `PolarKernelJet1Decay`. -/
theorem seedLamGradPerSum_of_leaves (κ : PlanarFrameKernels)
    (hRad : SeedDualRadialGDerivBounds) (hPol : PolarKernelJet1Decay) :
    SeedLamGradPerSum κ :=
  CutFTCGradPerSum.seedLamGradPerSum_of_leaves κ hRad hPol

end UnforcedLeray.Short.IIIa
