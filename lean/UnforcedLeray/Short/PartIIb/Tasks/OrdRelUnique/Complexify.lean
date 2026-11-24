import UnforcedLeray.Short.PartIIb.Sub.B1

/-!
# Part II-b, task `PartII-b:B1` (OrdRelUnique): the real case gives the complex case

Proves `UnforcedLeray.Short.IIb.solTestApprox_of_real : RealSolTestApprox → SolTestApprox`
(`Sub/B1.lean`, the statements of the conditional target). Source of record:
`the November 2 reference manuscript` (lines 119-120, 1364, 4147).

Proof. A complex phase test `Φ` splits as `Φ = realC (reV Φ) + I • realC (imV Φ)`, and the two
real parts are real phase tests (`IsPhaseTest.clm_comp`). The real case gives solenoidal
approximants `Ψ₁ n`, `Ψ₂ n`, and `Ψ n := Ψ₁ n + I • Ψ₂ n` approximates `𝔓Φ`:
solenoidal tests are closed under complex combinations (phase tests are, and the spatial
divergence is linear), and the slice-wise Leray projection is `ℂ`-linear (`lerayC` is a
`ℂ`-linear continuous map), so `projTest P (A + c • B) = projTest P A + c • projTest P B` slice by
slice, hence in `Y_{q₀'}` (`testElem_add`, `testElem_const_smul`), hence for the pairings
(`phasePair_add`, `phasePair_const_smul`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.RieszLp

/-! ### Splitting a complex vector into its real and imaginary parts -/

/-- A complex vector is `realC` of its real part plus `i` times `realC` of its imaginary part. -/
theorem realC_reV_add_I_smul_imV (x : CVec3) :
    x = realC (reV x) + Complex.I • realC (imV x) := by
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, realC_apply, reV_apply, imV_apply, smul_eq_mul]
  linear_combination -(Complex.re_add_im (x i))

/-! ### Solenoidal tests are closed under complex combinations -/

theorem isSolTest_add_smul {P : ℝ} {A B : ℝ × Space → CVec3} (c : ℂ) (hA : IsSolTest P A)
    (hB : IsSolTest P B) : IsSolTest P (A + c • B) := by
  have hdA : Differentiable ℝ A := hA.1.smooth.differentiable (by simp)
  have hdB : Differentiable ℝ B := hB.1.smooth.differentiable (by simp)
  have hdcB : Differentiable ℝ (c • B) := fun p => (hdB p).const_smul c
  have hdy : ∀ j : Fin 3, dy j (c • B) = c • dy j B := by
    intro j
    funext p
    simp only [dy, Pi.smul_apply]
    rw [fderiv_const_smul (hdB p) c, smul_apply]
  have hsum : ∀ j : Fin 3, dy j (A + c • B) = dy j A + c • dy j B := by
    intro j
    rw [dy_add hdA hdcB j, hdy j]
  refine ⟨hA.1.add (hB.1.const_smul c), fun x => ?_⟩
  have h1 := hA.2 x
  have h2 := hB.2 x
  simp only [hsum, Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, mul_zero, add_zero]

/-! ### Linearity of the slice-wise Leray projection of tests -/

/-- The slice `τ ↦ Φ(τ, ·)` is linear in `Φ` (as an element of `L^r`). -/
theorem sliceMap_add_smul {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)] {A B : ℝ × Space → CVec3} (c : ℂ)
    (hA : IsSliceTest P r A) (hB : IsSliceTest P r B) (hAB : IsSliceTest P r (A + c • B))
    (τ : ℝ) : sliceMap hAB.2 τ = sliceMap hA.2 τ + c • sliceMap hB.2 τ := by
  apply Lp.ext
  unfold sliceMap
  filter_upwards [MemLp.coeFn_toLp (hAB.2.memLp τ),
    Lp.coeFn_add (MemLp.toLp _ (hA.2.memLp τ)) (c • MemLp.toLp _ (hB.2.memLp τ)),
    Lp.coeFn_smul c (MemLp.toLp _ (hB.2.memLp τ)),
    MemLp.coeFn_toLp (hA.2.memLp τ), MemLp.coeFn_toLp (hB.2.memLp τ)]
    with y h1 h2 h3 h4 h5
  rw [h1]
  simp only [h2, h3, h4, h5, Pi.add_apply, Pi.smul_apply]

/-- The slice-wise Leray projection is `ℂ`-linear on slices, almost everywhere in the spatial
variable. -/
theorem lerayProjectedPhaseTest_add_smul_ae {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r)
    (hrtop : r ≠ ⊤) {A B : ℝ × Space → CVec3} (c : ℂ) (hA : IsSliceTest P r A)
    (hB : IsSliceTest P r B) (hAB : IsSliceTest P r (A + c • B)) (τ : ℝ) :
    (fun y => lerayProjectedPhaseTest hr1 hrtop hAB (τ, y)) =ᵐ[volume]
      fun y => lerayProjectedPhaseTest hr1 hrtop hA (τ, y) +
        c • lerayProjectedPhaseTest hr1 hrtop hB (τ, y) := by
  have hs := sliceMap_add_smul c hA hB hAB τ
  have hmain : lerayC r hr1 hrtop (sliceMap hAB.2 τ) =
      lerayC r hr1 hrtop (sliceMap hA.2 τ) + c • lerayC r hr1 hrtop (sliceMap hB.2 τ) := by
    rw [hs, map_add, map_smul]
  filter_upwards [Lp.coeFn_add (lerayC r hr1 hrtop (sliceMap hA.2 τ))
      (c • lerayC r hr1 hrtop (sliceMap hB.2 τ)),
    Lp.coeFn_smul c (lerayC r hr1 hrtop (sliceMap hB.2 τ))] with y h1 h2
  show (lerayC r hr1 hrtop (sliceMap hAB.2 τ)) y =
    (lerayC r hr1 hrtop (sliceMap hA.2 τ)) y + c • (lerayC r hr1 hrtop (sliceMap hB.2 τ)) y
  rw [hmain, h1, Pi.add_apply, h2, Pi.smul_apply]

section Projection

variable {P : ℝ} [Fact (0 < P)]

/-- The Leray projection of a linear combination of phase tests, slice by slice. -/
theorem projTest_add_smul_ae {A B : ℝ × Space → CVec3} (c : ℂ) (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) (τ : ℝ) :
    (fun y => projTest P (A + c • B) (τ, y)) =ᵐ[volume]
      fun y => projTest P A (τ, y) + c • projTest P B (τ, y) := by
  have hAB : IsPhaseTest P (A + c • B) := hA.add (hB.const_smul c)
  rw [projTest_of_isPhaseTest hAB, projTest_of_isPhaseTest hA, projTest_of_isPhaseTest hB]
  exact lerayProjectedPhaseTest_add_smul_ae _ _ c (hA.isSliceTest (conjExp q0E))
    (hB.isSliceTest (conjExp q0E)) (hAB.isSliceTest (conjExp q0E)) τ

theorem isSliceTest_projTest {A : ℝ × Space → CVec3} (hA : IsPhaseTest P A) :
    IsSliceTest P (conjExp q0E) (projTest P A) := by
  rw [projTest_of_isPhaseTest hA]
  exact isSliceTest_lerayProjectedPhaseTest _ _ _

/-- Two slice tests whose slices agree a.e. give the same element of `Y_r`. -/
theorem testElem_congr_ae {r : ℝ≥0∞} [Fact (1 ≤ r)] {Φ Ψ : ℝ × Space → CVec3}
    (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ)
    (h : ∀ τ : ℝ, (fun y => Φ (τ, y)) =ᵐ[volume] fun y => Ψ (τ, y)) :
    testElem P r Φ = testElem P r Ψ := by
  rw [testElem_of hΦ, testElem_of hΨ]
  refine congrArg (ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r
    AddCircle.haarAddCircle ℂ) (circleSlice_ext hΦ hΨ fun τ => ?_)
  unfold sliceMap
  exact MemLp.toLp_congr _ _ (h τ)

/-- The projected test of a linear combination is the linear combination in `Y_{q₀'}`. -/
theorem testElem_projTest_add_smul {A B : ℝ × Space → CVec3} (c : ℂ) (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) :
    testElem P (conjExp q0E) (projTest P (A + c • B)) =
      testElem P (conjExp q0E) (projTest P A) + c • testElem P (conjExp q0E) (projTest P B) := by
  have hAB : IsPhaseTest P (A + c • B) := hA.add (hB.const_smul c)
  have sA := isSliceTest_projTest hA
  have sB := isSliceTest_projTest hB
  have sAB := isSliceTest_projTest hAB
  have hsum := sA.add (sB.const_smul c)
  rw [testElem_congr_ae sAB hsum (projTest_add_smul_ae c hA hB), testElem_add sA (sB.const_smul c),
    testElem_const_smul sB c]

/-- The pairing with the projected test of a linear combination of phase tests. -/
theorem phasePair_projTest_add_smul {A B : ℝ × Space → CVec3} (c : ℂ) (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) (d : Yq P q0E) :
    phasePair P q0E (projTest P (A + c • B)) d =
      phasePair P q0E (projTest P A) d + c * phasePair P q0E (projTest P B) d := by
  simp only [phasePair]
  rw [testElem_projTest_add_smul c hA hB, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]

end Projection

/-! ### The complexification -/

/-- The real case applied to the real and imaginary parts gives the complex case. -/
theorem solTestApprox_of_decomp (h : RealSolTestApprox) {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} {φ₁ φ₂ : ℝ × Space → Space} (hφ₁ : IsPhaseTest P φ₁)
    (hφ₂ : IsPhaseTest P φ₂) (hΦ : ∀ z, Φ z = realC (φ₁ z) + Complex.I • realC (φ₂ z)) :
    ∃ Ψ : ℕ → ℝ × Space → CVec3, (∀ n, IsSolTest P (Ψ n)) ∧
      ∀ d : Yq P q0E, Tendsto (fun n => phasePair P q0E (Ψ n) d) atTop
        (𝓝 (phasePair P q0E (projTest P Φ) d)) := by
  obtain ⟨Ψ₁, hΨ₁, hl₁⟩ := h P φ₁ hφ₁
  obtain ⟨Ψ₂, hΨ₂, hl₂⟩ := h P φ₂ hφ₂
  have hΦfun : Φ = (fun z => realC (φ₁ z)) + Complex.I • (fun z => realC (φ₂ z)) := by
    funext z
    exact hΦ z
  have hc₁ : IsPhaseTest P (fun z => realC (φ₁ z)) := isPhaseTest_realC_comp hφ₁
  have hc₂ : IsPhaseTest P (fun z => realC (φ₂ z)) := isPhaseTest_realC_comp hφ₂
  refine ⟨fun n => Ψ₁ n + Complex.I • Ψ₂ n, fun n => isSolTest_add_smul Complex.I (hΨ₁ n) (hΨ₂ n),
    fun d => ?_⟩
  have hkey : phasePair P q0E (projTest P Φ) d =
      phasePair P q0E (projTest P (fun z => realC (φ₁ z))) d +
        Complex.I * phasePair P q0E (projTest P (fun z => realC (φ₂ z))) d := by
    rw [hΦfun]
    exact phasePair_projTest_add_smul Complex.I hc₁ hc₂ d
  have hfun : (fun n => phasePair P q0E (Ψ₁ n + Complex.I • Ψ₂ n) d) =
      fun n => phasePair P q0E (Ψ₁ n) d + Complex.I * phasePair P q0E (Ψ₂ n) d := by
    funext n
    rw [phasePair_add (hΨ₁ n).1 ((hΨ₂ n).1.const_smul Complex.I),
      phasePair_const_smul (hΨ₂ n).1]
  show Tendsto (fun n => phasePair P q0E (Ψ₁ n + Complex.I • Ψ₂ n) d) atTop
    (𝓝 (phasePair P q0E (projTest P Φ) d))
  rw [hfun, hkey]
  exact (hl₁ d).add ((hl₂ d).const_mul Complex.I)

/-- **The real case of `SolTestApprox` gives the complex case.** A complex phase test `Φ` splits
into the complexifications of its real and imaginary parts, both real phase tests. -/
theorem solTestApprox_of_real (h : RealSolTestApprox) : SolTestApprox := by
  intro P _ Φ hΦ
  exact solTestApprox_of_decomp h (hΦ.clm_comp reV) (hΦ.clm_comp imV)
    (fun z => realC_reV_add_I_smul_imV (Φ z))

end UnforcedLeray.Short.IIb
