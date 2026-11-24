import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.LerayForceProj.Reduction

/-!
# Weak derivatives of complex fields: components, real parts, vector tests
(leaves of `PartII-b:G4/4/2/org`)

Source: `the November 2 reference manuscript` lines 1307-1308 and 2381 (`𝔓`
commutes with `∂_j`; the complex fields of `Y_p` are handled through their real and imaginary
parts, `𝔓F = 𝔓(Re F) + i 𝔓(Im F)`).

* `weakDyCOfComp : WeakDyCOfComp`: the componentwise identity `CompDyC` gives the real weak
  derivatives of `Re u` and `Im u` (`HasWeakSpatialDerivative`);
* `compOfWeakDyC : CompOfWeakDyC`: the converse;
* `testDyOfComp : TestDyOfComp`: the componentwise identity gives `∫ (∂ⱼψ)·u = -∫ ψ·g` for every
  smooth compactly supported `ψ : ℝ³ → ℂ³` (split `ψᵢ = Re ψᵢ + i Im ψᵢ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-! ## Integrability and components -/

theorem integrable_ofReal_mul_coord {q : ℝ≥0∞} [Fact (1 ≤ q)] {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) (u : Lp CVec3 q (volume : Measure Space)) (i : Fin 3) :
    Integrable (fun y => (φ y : ℂ) * (u y) i) volume := by
  have hloc : LocallyIntegrable (fun y => (u y) i) volume :=
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).comp_memLp u).locallyIntegrable Fact.out
  have hc : Continuous (fun y => (φ y : ℂ)) :=
    Complex.continuous_ofReal.comp hφ.smooth.continuous
  have hcs : HasCompactSupport (fun y => (φ y : ℂ)) := hφ.compact.comp_left Complex.ofReal_zero
  simpa [smul_eq_mul] using hloc.integrable_smul_left_of_hasCompactSupport hc hcs

theorem integrable_smul_part {q : ℝ≥0∞} [Fact (1 ≤ q)] {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    (L : CVec3 →L[ℝ] Space) (u : Lp CVec3 q (volume : Measure Space)) :
    Integrable (fun x => φ x • L (u x)) volume :=
  ((L.comp_memLp u).locallyIntegrable Fact.out).integrable_smul_left_of_hasCompactSupport
    hφ.smooth.continuous hφ.compact

/-- `(∫ φ • Re u)ᵢ = Re ∫ φ uᵢ`. -/
theorem integral_smul_reV_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) (u : Lp CVec3 q (volume : Measure Space)) (i : Fin 3) :
    (∫ x, φ x • reV (u x)) i = (∫ y, (φ y : ℂ) * (u y) i).re := by
  have h1 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm
    (integrable_smul_part hφ reV u)
  have h2 := integral_re (integrable_ofReal_mul_coord hφ u i)
  simp only [RCLike.re_to_complex] at h2
  change EuclideanSpace.proj i (∫ x, φ x • reV (u x)) = _
  rw [← h1, ← h2]
  congr 1
  funext x
  simp [Complex.mul_re]

/-- `(∫ φ • Im u)ᵢ = Im ∫ φ uᵢ`. -/
theorem integral_smul_imV_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) (u : Lp CVec3 q (volume : Measure Space)) (i : Fin 3) :
    (∫ x, φ x • imV (u x)) i = (∫ y, (φ y : ℂ) * (u y) i).im := by
  have h1 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm
    (integrable_smul_part hφ imV u)
  have h2 := integral_im (integrable_ofReal_mul_coord hφ u i)
  simp only [RCLike.im_to_complex] at h2
  change EuclideanSpace.proj i (∫ x, φ x • imV (u x)) = _
  rw [← h1, ← h2]
  congr 1
  funext x
  simp [Complex.mul_im]

/-! ## Components and real parts -/

theorem weakDyC_of_compDyC {q : ℝ≥0∞} [Fact (1 ≤ q)] {j : Fin 3}
    {u g : Lp CVec3 q (volume : Measure Space)} (h : CompDyC j u g) : WeakDyC j u g := by
  unfold WeakDyC
  refine ⟨HasWeakSpatialDerivative.congr ?_ (reV.coeFn_compLpL u).symm
      (reV.coeFn_compLpL g).symm,
    HasWeakSpatialDerivative.congr ?_ (imV.coeFn_compLpL u).symm (imV.coeFn_compLpL g).symm⟩
  · refine ⟨fun φ hφ => integrable_smul_part (hφ.derivative j) reV u,
      fun φ hφ => integrable_smul_part hφ reV g, fun φ hφ => ?_⟩
    ext i
    rw [PiLp.neg_apply, integral_smul_reV_apply (hφ.derivative j) u i,
      integral_smul_reV_apply hφ g i, h φ hφ i, Complex.neg_re]
  · refine ⟨fun φ hφ => integrable_smul_part (hφ.derivative j) imV u,
      fun φ hφ => integrable_smul_part hφ imV g, fun φ hφ => ?_⟩
    ext i
    rw [PiLp.neg_apply, integral_smul_imV_apply (hφ.derivative j) u i,
      integral_smul_imV_apply hφ g i, h φ hφ i, Complex.neg_im]

theorem compDyC_of_weakDyC {q : ℝ≥0∞} [Fact (1 ≤ q)] {j : Fin 3}
    {u g : Lp CVec3 q (volume : Measure Space)} (h : WeakDyC j u g) : CompDyC j u g := by
  unfold WeakDyC at h
  have hR := h.1.congr (reV.coeFn_compLpL u) (reV.coeFn_compLpL g)
  have hI := h.2.congr (imV.coeFn_compLpL u) (imV.coeFn_compLpL g)
  intro φ hφ i
  have eR := congrArg (fun v : Space => v i) (hR.identity φ hφ)
  have eI := congrArg (fun v : Space => v i) (hI.identity φ hφ)
  simp only [PiLp.neg_apply] at eR eI
  rw [integral_smul_reV_apply (hφ.derivative j) u i, integral_smul_reV_apply hφ g i] at eR
  rw [integral_smul_imV_apply (hφ.derivative j) u i, integral_smul_imV_apply hφ g i] at eI
  apply Complex.ext
  · rw [eR, Complex.neg_re]
  · rw [eI, Complex.neg_im]

/-! ## Vector tests -/

theorem testDy_of_compDyC {q : ℝ≥0∞} [Fact (1 ≤ q)] {j : Fin 3}
    {u g : Lp CVec3 q (volume : Measure Space)} (h : CompDyC j u g) {ψ : Space → CVec3}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ y, dotL (fderiv ℝ ψ y (coordinateVector j)) (u y) = -∫ y, dotL (ψ y) (g y) := by
  have hcomp : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y => ψ y i) := fun i =>
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hψ
  have ha : ∀ i : Fin 3, IsSpatialTest (fun y => (ψ y i).re) := fun i =>
    ⟨Complex.reCLM.contDiff.comp (hcomp i),
      hψc.comp_left (g := fun z : CVec3 => (z i).re) (by simp)⟩
  have hb : ∀ i : Fin 3, IsSpatialTest (fun y => (ψ y i).im) := fun i =>
    ⟨Complex.imCLM.contDiff.comp (hcomp i),
      hψc.comp_left (g := fun z : CVec3 => (z i).im) (by simp)⟩
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hd : ∀ (i : Fin 3) (y : Space), fderiv ℝ ψ y (coordinateVector j) i =
      (spatialTestDerivative j (fun y => (ψ y i).re) y : ℂ) +
        (spatialTestDerivative j (fun y => (ψ y i).im) y : ℂ) * Complex.I := by
    intro i y
    have h0 : HasFDerivAt ψ (fderiv ℝ ψ y) y := (hdiff y).hasFDerivAt
    have h1 : HasFDerivAt (fun y => ψ y i)
        (((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ ψ y)) y :=
      ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp y h0
    have hre : HasFDerivAt (fun y => (ψ y i).re) (Complex.reCLM.comp
        (((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ ψ y))) y :=
      Complex.reCLM.hasFDerivAt.comp y h1
    have him : HasFDerivAt (fun y => (ψ y i).im) (Complex.imCLM.comp
        (((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ ψ y))) y :=
      Complex.imCLM.hasFDerivAt.comp y h1
    simp only [spatialTestDerivative, hre.fderiv, him.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply, Complex.imCLM_apply]
    exact (Complex.re_add_im _).symm
  have e1 : ∀ i : Fin 3, (fun y => fderiv ℝ ψ y (coordinateVector j) i * (u y) i) =
      fun y => (spatialTestDerivative j (fun y => (ψ y i).re) y : ℂ) * (u y) i +
        Complex.I * ((spatialTestDerivative j (fun y => (ψ y i).im) y : ℂ) * (u y) i) := by
    intro i
    funext y
    rw [hd i y]
    ring
  have e2 : ∀ i : Fin 3, (fun y => ψ y i * (g y) i) =
      fun y => (((ψ y i).re : ℝ) : ℂ) * (g y) i +
        Complex.I * ((((ψ y i).im : ℝ) : ℂ) * (g y) i) := by
    intro i
    funext y
    conv_lhs => rw [← Complex.re_add_im (ψ y i)]
    ring
  have hiU : ∀ i : Fin 3, Integrable (fun y => fderiv ℝ ψ y (coordinateVector j) i * (u y) i) := by
    intro i
    rw [e1 i]
    exact (integrable_ofReal_mul_coord ((ha i).derivative j) u i).add
      ((integrable_ofReal_mul_coord ((hb i).derivative j) u i).const_mul _)
  have hiG : ∀ i : Fin 3, Integrable (fun y => ψ y i * (g y) i) := by
    intro i
    rw [e2 i]
    exact (integrable_ofReal_mul_coord (ha i) g i).add
      ((integrable_ofReal_mul_coord (hb i) g i).const_mul _)
  have hcompI : ∀ i : Fin 3, ∫ y, fderiv ℝ ψ y (coordinateVector j) i * (u y) i =
      -∫ y, ψ y i * (g y) i := by
    intro i
    have h1 := h (fun y => (ψ y i).re) (ha i) i
    have h2 := h (fun y => (ψ y i).im) (hb i) i
    rw [e1 i, e2 i,
      integral_add (integrable_ofReal_mul_coord ((ha i).derivative j) u i)
        ((integrable_ofReal_mul_coord ((hb i).derivative j) u i).const_mul _),
      integral_add (integrable_ofReal_mul_coord (ha i) g i)
        ((integrable_ofReal_mul_coord (hb i) g i).const_mul _),
      integral_const_mul, integral_const_mul, h1, h2]
    ring
  simp only [dotL_apply]
  rw [integral_finsetSum _ fun i _ => hiU i, integral_finsetSum _ fun i _ => hiG i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hcompI i

/-! ## The leaves -/

/-- **Leaf `WeakDyCOfComp`.** -/
theorem weakDyCOfComp : WeakDyCOfComp := fun _ _ _ _ _ h => weakDyC_of_compDyC h

/-- **Leaf `CompOfWeakDyC`.** -/
theorem compOfWeakDyC : CompOfWeakDyC := fun _ _ _ _ _ h => compDyC_of_weakDyC h

/-- **Leaf `TestDyOfComp`.** -/
theorem testDyOfComp : TestDyOfComp := fun _ _ _ _ _ h _ hψ hψc => testDy_of_compDyC h hψ hψc

#print axioms weakDyCOfComp
#print axioms compOfWeakDyC
#print axioms testDyOfComp

end UnforcedLeray.Short.IIb
