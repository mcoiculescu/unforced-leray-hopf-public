import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartI.Sub.PartI_S05_1_1
import UnforcedLeray.Lib.PlanarSectorsB.StressMoments
import UnforcedLeray.Lib.PlanarSectors.NUE.Symmetry
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Sectors
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_1

/-!
# `PartIII-a:T21/c5/2/1/2`, helper: the oscillator `D` on the seed modes in polar form

Source: `the November 2 reference manuscript` (SP), lines 593-601
(`q = h(r) e^{2iϑ}`), 2863 (`D = Δ + ½ y·∇ + 2`) and 2991-2992 (angular orthogonality of the
planar `D` pairing).

* `movD_comp_planeToC`: in complex notation `D (F ∘ planeToC) = (ΔF + ½ DF(z)[z] + 2F) ∘ planeToC`;
* `seed_polar_D`: on `q = h(|z|) e^{2iϑ}`, `ΔF + ½ DF(z)[z] + 2F = (D_rad h)(|z|) e^{2iϑ}`
  for `z ≠ 0`, with `D_rad = oscillatorD` (polar Laplacian `PartI.polarLaplacianCore_proof`,
  radial derivative `Planar.fderiv_ofProfile_two_radial`);
* `movD_conj`: `D` has real coefficients, `D \bar W = \overline{D W}`;
* `sectors_movD_seed`: the `±2` angular sectors of `D e₀ = D q` and `D e₁ = D \bar q`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa.OscGramPolar

open OscillatorForceSub

theorem planeToC_dir0 : planeToC (B0579.dir 0) = 1 := by
  apply Complex.ext <;> simp [planeToC, B0579.dir]

theorem planeToC_dir1 : planeToC (B0579.dir 1) = Complex.I := by
  apply Complex.ext <;> simp [planeToC, B0579.dir]

theorem planeToC_re_im (z : ℂ) : planeToC (z.re, z.im) = z := by
  apply Complex.ext <;> simp [planeToC]

/-- First partials of `F ∘ planeToC`. -/
theorem pdCx_comp_planeToC {F : ℂ → ℂ} (hF : Differentiable ℝ F) (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (fun y => F (planeToC y)) y = fderiv ℝ F (planeToC y) (planeToC (B0579.dir k)) := by
  have hcomp : (fun y => F (planeToC y)) = F ∘ planeToCCLM := by
    funext y
    simp [planeToCCLM_apply]
  unfold pdCx
  rw [hcomp, fderiv_comp y (hF _) planeToCCLM.differentiableAt, ContinuousLinearMap.fderiv]
  simp [planeToCCLM_apply]

/-- `∂_w (z ↦ DF(z)[v]) = D²F(z)[w, v]` for `C²` `F`. -/
theorem fderiv_fderiv_apply_const {F : ℂ → ℂ} (hF : ContDiff ℝ 2 F) (x w v : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ F z v) x w = fderiv ℝ (fderiv ℝ F) x w v := by
  have hdF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h : HasFDerivAt (fun z => fderiv ℝ F z v) ((fderiv ℝ (fderiv ℝ F) x).flip v) x := by
    simpa using (hdF x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  rw [h.fderiv, ContinuousLinearMap.flip_apply]

/-- `ladLapCx (F ∘ planeToC) = (Δ F) ∘ planeToC` for `C²` `F`. -/
theorem ladLapCx_comp_planeToC {F : ℂ → ℂ} (hF : ContDiff ℝ 2 F) (y : ℝ × ℝ) :
    ladLapCx (fun y => F (planeToC y)) y = Laplacian.laplacian F (planeToC y) := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd1 : ∀ v : ℂ, Differentiable ℝ (fun z => fderiv ℝ F z v) := fun v =>
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).clm_apply
      (differentiable_const v)
  have h1 : ∀ k : Fin 2, pdCx k (fun y => F (planeToC y)) =
      fun y => (fun z => fderiv ℝ F z (planeToC (B0579.dir k))) (planeToC y) :=
    fun k => funext fun y => pdCx_comp_planeToC hd k y
  unfold ladLapCx
  rw [h1 0, h1 1, pdCx_comp_planeToC (hd1 _), pdCx_comp_planeToC (hd1 _),
    fderiv_fderiv_apply_const hF, fderiv_fderiv_apply_const hF,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, planeToC_dir0, planeToC_dir1]
  simp

/-- The Euler part `y₁ ∂₁ + y₂ ∂₂` of `F ∘ planeToC` is `DF(z)[z]`. -/
theorem euler_comp_planeToC {F : ℂ → ℂ} (hF : Differentiable ℝ F) (y : ℝ × ℝ) :
    ((y.1 : ℝ) : ℂ) * pdCx 0 (fun y => F (planeToC y)) y +
        ((y.2 : ℝ) : ℂ) * pdCx 1 (fun y => F (planeToC y)) y =
      fderiv ℝ F (planeToC y) (planeToC y) := by
  rw [pdCx_comp_planeToC hF, pdCx_comp_planeToC hF, planeToC_dir0, planeToC_dir1]
  have hz : planeToC y = (y.1 : ℝ) • (1 : ℂ) + (y.2 : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [planeToC]
  set L := fderiv ℝ F (planeToC y)
  rw [hz, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- `D (F ∘ planeToC) = (ΔF + ½ DF(z)[z] + 2F) ∘ planeToC` (SP 2863). -/
theorem movD_comp_planeToC {F : ℂ → ℂ} (hF : ContDiff ℝ 2 F) (y : ℝ × ℝ) :
    movD (fun y => F (planeToC y)) y =
      Laplacian.laplacian F (planeToC y) + (2 : ℂ)⁻¹ * fderiv ℝ F (planeToC y) (planeToC y) +
        2 * F (planeToC y) := by
  unfold movD
  rw [ladLapCx_comp_planeToC hF y, euler_comp_planeToC (hF.differentiable (by norm_num)) y]

/-- The polar form of `D` on `q = h(|z|) e^{2iϑ}`, `z ≠ 0` (SP 593-601, 2863). -/
theorem seed_polar_D {h : ℝ → ℂ} (hsm : ContDiffOn ℝ ∞ h (Ioi 0)) {z : ℂ} (hz : z ≠ 0) :
    Laplacian.laplacian (PartI.seedPlanar h) z +
        (2 : ℂ)⁻¹ * fderiv ℝ (PartI.seedPlanar h) z z + 2 * PartI.seedPlanar h z =
      PartI.seedPlanar (oscillatorD h) z := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hlap := PartI.polarLaplacianCore_proof h hsm z hz
  have hdiff : HasDerivAt h (deriv h ‖z‖) ‖z‖ :=
    ((hsm.contDiffAt (Ioi_mem_nhds hpos)).differentiableAt (by simp)).hasDerivAt
  have hrad := Planar.fderiv_ofProfile_two_radial hz hdiff
  rw [hlap, hrad]
  simp only [PartI.seedPlanar, Planar.NUE.Ang.ofProfile, B0034.radialDelta2, oscillatorD]
  ring

/-- First partials commute with conjugation. -/
theorem pdCx_conj {W : ℝ × ℝ → ℂ} (hW : Differentiable ℝ W) (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (fun y => conj (W y)) y = conj (pdCx k W y) := by
  have h1 := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x := W y)).comp y (hW y).hasFDerivAt
  have e : (fun y => conj (W y)) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ W := by
    funext y
    simp
  unfold pdCx
  rw [e, h1.fderiv]
  simp

/-- `D` has real coefficients: `D \bar W = \overline{D W}`. -/
theorem movD_conj {W : ℝ × ℝ → ℂ} (hW : ContDiff ℝ 2 W) (y : ℝ × ℝ) :
    movD (fun y => conj (W y)) y = conj (movD W y) := by
  have hd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hd1 : ∀ k : Fin 2, Differentiable ℝ (pdCx k W) := fun k => by
    unfold pdCx
    exact ((hW.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).clm_apply
      (differentiable_const _)
  have h1 : ∀ k : Fin 2, pdCx k (fun y => conj (W y)) = fun y => conj (pdCx k W y) :=
    fun k => funext (pdCx_conj hd k)
  unfold movD ladLapCx
  rw [h1 0, h1 1, pdCx_conj (hd1 0), pdCx_conj (hd1 1)]
  simp only [map_add, map_mul, Complex.conj_ofReal, map_inv₀, map_ofNat]

/-- The profile of a globally smooth `q = h e^{2iϑ}` is smooth on `(0, ∞)`. -/
theorem contDiffOn_profile_of_seedPlanar {h : ℝ → ℂ}
    (hsmF : ContDiff ℝ ∞ (PartI.seedPlanar h)) : ContDiffOn ℝ ∞ h (Ioi 0) := by
  have hc : ContDiff ℝ ∞ (fun r : ℝ => PartI.seedPlanar h (r : ℂ)) :=
    hsmF.comp Complex.ofRealCLM.contDiff
  exact hc.contDiffOn.congr (fun r hr => (seedPlanar_ofReal_eq h r hr).symm)

/-- `D e₀ = (D_rad h)(|z|) e^{2iϑ}` off the origin. -/
theorem movD_seed_e0 {κ : PlanarFrameKernels} {h : ℝ → ℂ}
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y))
    (hsmF : ContDiff ℝ ∞ (PartI.seedPlanar h)) {y : ℝ × ℝ} (hy : planeToC y ≠ 0) :
    movD (κ.e 0) y = PartI.seedPlanar (oscillatorD h) (planeToC y) := by
  have he : κ.e 0 = fun y => PartI.seedPlanar h (planeToC y) := funext he0
  rw [he, movD_comp_planeToC (hsmF.of_le (by simp)) y]
  exact seed_polar_D (contDiffOn_profile_of_seedPlanar hsmF) hy

/-- **The `±2` sectors of `D e₀`, `D e₁`** (SP 593-601, 2991-2992): for `r > 0`,
`(D q)₂ = D_rad h`, `(D q)₋₂ = 0`, `(D \bar q)₂ = 0`, `(D \bar q)₋₂ = \overline{D_rad h}`. -/
theorem sectors_movD_seed {κ : PlanarFrameKernels} {h : ℝ → ℂ}
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y))
    (he1 : ∀ y, κ.e 1 y = conj (PartI.seedPlanar h (planeToC y)))
    (hsmF : ContDiff ℝ ∞ (PartI.seedPlanar h)) {r : ℝ} (hr : 0 < r) :
    Planar.NUE.Polar.angularSector (fun z : ℂ => movD (κ.e 0) (z.re, z.im)) 2 r =
        oscillatorD h r ∧
      Planar.NUE.Polar.angularSector (fun z : ℂ => movD (κ.e 0) (z.re, z.im)) (-2) r = 0 ∧
      Planar.NUE.Polar.angularSector (fun z : ℂ => movD (κ.e 1) (z.re, z.im)) 2 r = 0 ∧
      Planar.NUE.Polar.angularSector (fun z : ℂ => movD (κ.e 1) (z.re, z.im)) (-2) r =
        conj (oscillatorD h r) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have key0 : ∀ n : ℤ,
      Planar.NUE.Polar.angularSector (fun z : ℂ => movD (κ.e 0) (z.re, z.im)) n r =
        Planar.NUE.Polar.angularSector (PartI.seedPlanar (oscillatorD h)) n r := by
    intro n
    unfold Planar.NUE.Polar.angularSector
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hne : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero hrC (Complex.exp_ne_zero _)
    have hy : planeToC (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re,
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im) ≠ 0 := by
      rw [planeToC_re_im]
      exact hne
    simp only
    rw [movD_seed_e0 he0 hsmF hy, planeToC_re_im]
  have hW : ContDiff ℝ 2 (κ.e 0) := by
    have he : κ.e 0 = PartI.seedPlanar h ∘ planeToCCLM := by
      funext y
      simp [he0, planeToCCLM_apply]
    rw [he]
    exact (hsmF.of_le (by simp)).comp planeToCCLM.contDiff
  have he1' : κ.e 1 = fun y => conj (κ.e 0 y) := funext fun y => by rw [he1, he0]
  have key1 : (fun z : ℂ => movD (κ.e 1) (z.re, z.im)) =
      fun z : ℂ => conj ((fun z : ℂ => movD (κ.e 0) (z.re, z.im)) z) := by
    funext z
    rw [he1']
    exact movD_conj hW _
  have s2 : Planar.NUE.Polar.angularSector (fun z : ℂ => movD (κ.e 0) (z.re, z.im)) 2 r =
      oscillatorD h r := by
    rw [key0 2, SeedSectorsAux.angularSector_seedPlanar _ 2 r hr]
    simp
  have sm2 : Planar.NUE.Polar.angularSector (fun z : ℂ => movD (κ.e 0) (z.re, z.im)) (-2) r =
      0 := by
    rw [key0 (-2), SeedSectorsAux.angularSector_seedPlanar _ (-2) r hr]
    simp
  refine ⟨s2, sm2, ?_, ?_⟩
  · have c := Planar.NUE.Ang.angularSector_conj (fun z : ℂ => movD (κ.e 0) (z.re, z.im)) (-2) r
    rw [neg_neg] at c
    rw [key1, c, sm2, map_zero]
  · have c := Planar.NUE.Ang.angularSector_conj (fun z : ℂ => movD (κ.e 0) (z.re, z.im)) 2 r
    rw [key1, c, s2]

end UnforcedLeray.Short.IIIa.OscGramPolar
