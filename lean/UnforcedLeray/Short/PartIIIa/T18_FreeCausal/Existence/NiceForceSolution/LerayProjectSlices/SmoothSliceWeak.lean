import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2

/-!
# Part III-a, task `PartIII-a:T18/2/4/2/8`: classical derivative of a slice is its weak derivative

Target (`Sub/T18_2_4_2.lean`): `SmoothSliceWeak`. For `c > 0`, a `NiceSlices c u` family, every
`s`, and `i j : Fin 2`, the slice `x ↦ u(s, x) i` has the classical derivative
`x ↦ pdC j (u(s, ·) i) x` as its weak `j`-derivative on the cylinder `C_c`.
Source of record: `the November 2 reference manuscript`, lines 3442-3465.

## Proof idea

Split the slice `a = u(s, ·) i` into the real and imaginary parts `F`, `G`, which are smooth and
`c`-periodic in `q`. For a real smooth periodic `f` and a cylinder test `ψ` with band `R`, multiply
`f` by a cut-off `b(η)` that equals `1` for `|η| < |R| + 1`. The product is a cylinder test, so
`B0579.integral_mul_pd` applies, and the cut-off changes neither integrand. The complex identity
follows from the real and imaginary parts via `integral_re` and `integral_im`. Integrability comes
from continuity and the compact `η`-support of `ψ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Integrability on the cell -/

/-- A continuous function vanishing for `R < |η|` is integrable on the cylinder cell. -/
theorem ssw_integrableOn_cell {E : Type*} [NormedAddCommGroup E] (c R : ℝ)
    {g : ℝ × ℝ → E} (hg : Continuous g) (hv : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) :
    IntegrableOn g (B0579.cell c) :=
  (hg.continuousOn.integrableOn_compact (B0579.isCompact_box c R)).of_forall_sdiff_eq_zero
    (B0579.measurableSet_cell c)
    (fun x hx => hv x (not_le.1 fun h => hx.2 (B0579.mem_box_of_mem_cell hx.1 h)))

/-- The classical derivative of a function vanishing on `R < |η|` vanishes there. -/
theorem ssw_pd_eq_zero {ψ : ℝ × ℝ → ℝ} {R : ℝ} (hψ : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0)
    (j : Fin 2) {x : ℝ × ℝ} (hx : R < |x.2|) : B0579.pd j ψ x = 0 := by
  have hU : IsOpen {y : ℝ × ℝ | R < |y.2|} := isOpen_lt continuous_const continuous_snd.abs
  have hev : ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hψ y hy
  simp only [B0579.pd]
  rw [hev.fderiv_eq]
  simp

/-! ## Real integration by parts with a band-limited cut-off -/

/-- Integration by parts on the cylinder for a real smooth `c`-periodic `f` and a test `ψ`. -/
theorem ssw_ibp {c : ℝ} {f ψ : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfp : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) (hψ : B0579.IsCylTest c ψ) (j : Fin 2) :
    ∫ x in B0579.cell c, f x * B0579.pd j ψ x = -∫ x in B0579.cell c, B0579.pd j f x * ψ x := by
  obtain ⟨R, hR⟩ := hψ.band
  let B : ContDiffBump (0 : ℝ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  have hB1 : ∀ y : ℝ, |y| < |R| + 1 → B y = 1 := fun y hy =>
    B.one_of_mem_closedBall (show dist y 0 ≤ |R| + 1 by rw [Real.dist_eq, sub_zero]; exact hy.le)
  have hB0 : ∀ y : ℝ, |R| + 2 ≤ |y| → B y = 0 := fun y hy =>
    B.zero_of_le_dist (show |R| + 2 ≤ dist y 0 by rw [Real.dist_eq, sub_zero]; exact hy)
  have hBs : ContDiff ℝ ∞ ⇑B := B.contDiff
  have hφ : B0579.IsCylTest c (fun x : ℝ × ℝ => f x * B x.2) :=
    { smooth := hf.mul (hBs.comp contDiff_snd)
      periodic := fun x => by
        show f (x.1 + c, x.2) * B x.2 = f x * B x.2
        rw [hfp x]
      band := ⟨|R| + 2, fun x hx => by
        show f x * B x.2 = 0
        rw [hB0 x.2 hx.le, mul_zero]⟩ }
  have key : ∫ x in B0579.cell c, f x * B x.2 * B0579.pd j ψ x =
      -∫ x in B0579.cell c, B0579.pd j (fun y => f y * B y.2) x * ψ x :=
    B0579.integral_mul_pd hφ hψ j
  have hA : ∀ x : ℝ × ℝ, f x * B x.2 * B0579.pd j ψ x = f x * B0579.pd j ψ x := by
    intro x
    by_cases hx : R < |x.2|
    · simp [ssw_pd_eq_zero hR j hx]
    · have hx' : |x.2| < |R| + 1 := lt_of_le_of_lt (not_lt.1 hx) (by linarith [le_abs_self R])
      rw [hB1 x.2 hx', mul_one]
  have hB' : ∀ x : ℝ × ℝ, B0579.pd j (fun y => f y * B y.2) x * ψ x = B0579.pd j f x * ψ x := by
    intro x
    by_cases hx : R < |x.2|
    · simp [hR x hx]
    · have hx' : |x.2| < |R| + 1 := lt_of_le_of_lt (not_lt.1 hx) (by linarith [le_abs_self R])
      have hU : IsOpen {y : ℝ × ℝ | |y.2| < |R| + 1} :=
        isOpen_lt continuous_snd.abs continuous_const
      have hev : (fun y : ℝ × ℝ => f y * B y.2) =ᶠ[𝓝 x] f :=
        Filter.eventually_of_mem (hU.mem_nhds hx') fun y hy => by
          show f y * B y.2 = f y
          rw [hB1 y.2 hy, mul_one]
      simp only [B0579.pd]
      rw [hev.fderiv_eq]
  have e1 : ∫ x in B0579.cell c, f x * B x.2 * B0579.pd j ψ x =
      ∫ x in B0579.cell c, f x * B0579.pd j ψ x := by
    simp only [hA]
  have e2 : ∫ x in B0579.cell c, B0579.pd j (fun y => f y * B y.2) x * ψ x =
      ∫ x in B0579.cell c, B0579.pd j f x * ψ x := by
    simp only [hB']
  rw [e1, e2] at key
  exact key

/-! ## The slice as real and imaginary parts -/

/-- The classical derivative of a complex function splits into the derivatives of its real and
imaginary parts. -/
theorem ssw_pdC_eq {a : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (j : Fin 2) (x : ℝ × ℝ) :
    pdC j a x = ((B0579.pd j (fun y => (a y).re) x : ℝ) : ℂ) +
      Complex.I * ((B0579.pd j (fun y => (a y).im) x : ℝ) : ℂ) := by
  have hd : HasFDerivAt a (fderiv ℝ a x) x := ((ha.differentiable (by simp)) x).hasFDerivAt
  have hre : HasFDerivAt (fun y => (a y).re) (Complex.reCLM.comp (fderiv ℝ a x)) x :=
    Complex.reCLM.hasFDerivAt.comp x hd
  have him : HasFDerivAt (fun y => (a y).im) (Complex.imCLM.comp (fderiv ℝ a x)) x :=
    Complex.imCLM.hasFDerivAt.comp x hd
  unfold pdC B0579.pd
  rw [hre.fderiv, him.fderiv]
  apply Complex.ext <;> simp

/-- The real part of a complex integral is the integral of the real parts. -/
theorem ssw_re_integral {c : ℝ} {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f (B0579.cell c))
    {g : ℝ × ℝ → ℝ} (hg : ∀ x, (f x).re = g x) :
    (∫ x in B0579.cell c, f x).re = ∫ x in B0579.cell c, g x := by
  have e : ∫ x in B0579.cell c, (f x).re = (∫ x in B0579.cell c, f x).re := integral_re hf
  rw [← e]
  simp only [hg]

/-- The imaginary part of a complex integral is the integral of the imaginary parts. -/
theorem ssw_im_integral {c : ℝ} {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f (B0579.cell c))
    {g : ℝ × ℝ → ℝ} (hg : ∀ x, (f x).im = g x) :
    (∫ x in B0579.cell c, f x).im = ∫ x in B0579.cell c, g x := by
  have e : ∫ x in B0579.cell c, (f x).im = (∫ x in B0579.cell c, f x).im := integral_im hf
  rw [← e]
  simp only [hg]

/-! ## Weak derivative of a smooth periodic slice -/

/-- The classical derivative of a smooth `c`-periodic complex function is its weak cylinder
derivative. -/
theorem ssw_weak_of_smooth {c : ℝ} {a : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    (hp : ∀ x : ℝ × ℝ, a (x.1 + c, x.2) = a x) (j : Fin 2) :
    HasWeakCellDerivC c j a (fun x => pdC j a x) := by
  have hF : ContDiff ℝ ∞ (fun y => (a y).re) := Complex.reCLM.contDiff.comp ha
  have hG : ContDiff ℝ ∞ (fun y => (a y).im) := Complex.imCLM.contDiff.comp ha
  have hFp : ∀ x : ℝ × ℝ, (a (x.1 + c, x.2)).re = (a x).re := fun x => by rw [hp x]
  have hGp : ∀ x : ℝ × ℝ, (a (x.1 + c, x.2)).im = (a x).im := fun x => by rw [hp x]
  have hcont_a : Continuous a := ha.continuous
  have hcont_pdC : Continuous (fun x => pdC j a x) := by
    have h1 : Continuous (fun x => fderiv ℝ a x) := ha.continuous_fderiv (by simp)
    exact h1.clm_apply continuous_const
  unfold HasWeakCellDerivC
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · obtain ⟨R, hR⟩ := hψ.band
    exact ssw_integrableOn_cell c R
      (hcont_a.mul (Complex.continuous_ofReal.comp (hψ.pd j).continuous))
      (fun x hx => by simp [ssw_pd_eq_zero hR j hx])
  · obtain ⟨R, hR⟩ := hψ.band
    exact ssw_integrableOn_cell c R
      (hcont_pdC.mul (Complex.continuous_ofReal.comp hψ.continuous))
      (fun x hx => by simp [hR x hx])
  · obtain ⟨R, hR⟩ := hψ.band
    have hI1 : IntegrableOn (fun x => a x * ((B0579.pd j ψ x : ℝ) : ℂ)) (B0579.cell c) :=
      ssw_integrableOn_cell c R
        (hcont_a.mul (Complex.continuous_ofReal.comp (hψ.pd j).continuous))
        (fun x hx => by simp [ssw_pd_eq_zero hR j hx])
    have hI2 : IntegrableOn (fun x => pdC j a x * ((ψ x : ℝ) : ℂ)) (B0579.cell c) :=
      ssw_integrableOn_cell c R
        (hcont_pdC.mul (Complex.continuous_ofReal.comp hψ.continuous))
        (fun x hx => by simp [hR x hx])
    have hF' := ssw_ibp hF hFp hψ j
    have hG' := ssw_ibp hG hGp hψ j
    have hre1 : (∫ x in B0579.cell c, a x * ((B0579.pd j ψ x : ℝ) : ℂ)).re =
        ∫ x in B0579.cell c, (a x).re * B0579.pd j ψ x :=
      ssw_re_integral hI1 (fun x => by simp)
    have him1 : (∫ x in B0579.cell c, a x * ((B0579.pd j ψ x : ℝ) : ℂ)).im =
        ∫ x in B0579.cell c, (a x).im * B0579.pd j ψ x :=
      ssw_im_integral hI1 (fun x => by simp)
    have hre2 : (∫ x in B0579.cell c, pdC j a x * ((ψ x : ℝ) : ℂ)).re =
        ∫ x in B0579.cell c, B0579.pd j (fun y => (a y).re) x * ψ x :=
      ssw_re_integral hI2 (fun x => by rw [ssw_pdC_eq ha j x]; simp)
    have him2 : (∫ x in B0579.cell c, pdC j a x * ((ψ x : ℝ) : ℂ)).im =
        ∫ x in B0579.cell c, B0579.pd j (fun y => (a y).im) x * ψ x :=
      ssw_im_integral hI2 (fun x => by rw [ssw_pdC_eq ha j x]; simp)
    show ∫ x in B0579.cell c, a x * ((B0579.pd j ψ x : ℝ) : ℂ) =
      -∫ x in B0579.cell c, pdC j a x * ((ψ x : ℝ) : ℂ)
    apply Complex.ext
    · rw [Complex.neg_re, hre1, hre2]
      exact hF'
    · rw [Complex.neg_im, him1, him2]
      exact hG'

end UnforcedLeray.Short.IIIa

/-! ## The target -/

namespace UnforcedLeray.Short.IIIa

/-- **Classical to weak** (`PartIII-a:T18/2/4/2/8`). The classical derivative of a slice of a nice
family is its weak derivative on the cylinder. -/
theorem smoothSliceWeak : UnforcedLeray.Short.IIIa.SmoothSliceWeak := by
  unfold SmoothSliceWeak
  intro c _hc u hu s i j
  have hs : ContDiff ℝ ∞ (fun y : ℝ × ℝ => (s, y)) := contDiff_const.prodMk contDiff_id
  have ha : ContDiff ℝ ∞ (fun y : ℝ × ℝ => u (s, y) i) := (hu.smooth i).comp hs
  exact ssw_weak_of_smooth (c := c) ha (fun x => hu.periodic s x i) j

end UnforcedLeray.Short.IIIa
