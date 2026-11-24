import UnforcedLeray.Lib.PhaseSpace.Test

/-!
# The phase pairing `⟪Φ, f⟫` on `Y_q` (INF25 T25.1)

Blueprint units B0411 (tex 7304–7337), B0005 (tex 136–147), B0427 (tex 7540–7542).
Bypass B25-1 of the scoping note `INF15-INF17-INF25-Parabolic.md`: every distributional
identity on `Y_q` is a pairing against a smooth `P`-periodic test with bounded spatial
support,

  `⟪Φ, f⟫ = P⁻¹ ∫₀ᴾ ∫_{ℝ³} ∑ᵢ Φᵢ(τ, y) fᵢ(τ)(y) dy dτ`

(`phasePair_eq_periodIntegral`). The pairing is Mathlib's `lpPairing` applied twice to the
bilinear dot product, so it is a continuous linear functional of `f ∈ Y_q`
(`phasePair P q Φ : Yq P q →L[ℂ] ℂ`), and continuous in the test through `Y_{q'}`.

Status: infrastructure only; no manuscript unit is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseSpace

section Pairing

variable (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- The spatial pairing `L^{q'} × L^q → ℂ`, `(g, h) ↦ ∫ g · h dy`. -/
def innerPair : Lp CVec3 (conjExp q) (volume : Measure Space) →L[ℂ]
    Lp CVec3 q (volume : Measure Space) →L[ℂ] ℂ :=
  dotL.lpPairing volume (conjExp q) q

/-- The phase pairing `Y_{q'} × Y_q → ℂ`, `(ψ, f) ↦ ∫ ⟪ψ(τ), f(τ)⟫ dhaar(τ)`. -/
def phasePairing : Yq P (conjExp q) →L[ℂ] Yq P q →L[ℂ] ℂ :=
  (innerPair q).lpPairing AddCircle.haarAddCircle (conjExp q) q

/-- Pairing with a phase test: `f ↦ ⟪Φ, f⟫`, a continuous linear functional on `Y_q`. -/
def phasePair (Φ : ℝ × Space → CVec3) : Yq P q →L[ℂ] ℂ :=
  phasePairing P q (testElem P (conjExp q) Φ)

variable {P q}

theorem innerPair_apply (g : Lp CVec3 (conjExp q) (volume : Measure Space))
    (h : Lp CVec3 q (volume : Measure Space)) :
    innerPair q g h = ∫ y, dotL (g y) (h y) :=
  ContinuousLinearMap.lpPairing_eq_integral _ _ _

theorem phasePairing_apply (ψ : Yq P (conjExp q)) (f : Yq P q) :
    phasePairing P q ψ f = ∫ τ, innerPair q (ψ τ) (f τ) ∂AddCircle.haarAddCircle :=
  ContinuousLinearMap.lpPairing_eq_integral _ _ _

end Pairing

/-! ### Linearity in the test -/

section Linear

variable {r : ℝ≥0∞} [Fact (1 ≤ r)] {P : ℝ} {Φ Ψ : ℝ × Space → CVec3}

theorem SliceCont.add (hΦ : SliceCont r Φ) (hΨ : SliceCont r Ψ) : SliceCont r (Φ + Ψ) where
  memLp τ := (hΦ.memLp τ).add (hΨ.memLp τ)
  continuous := (hΦ.continuous.add hΨ.continuous).congr fun τ =>
    (MemLp.toLp_add (hΦ.memLp τ) (hΨ.memLp τ)).symm

theorem SliceCont.const_smul (hΦ : SliceCont r Φ) (c : ℂ) : SliceCont r (c • Φ) where
  memLp τ := (hΦ.memLp τ).const_smul c
  continuous := (hΦ.continuous.const_smul c).congr fun τ =>
    (MemLp.toLp_const_smul c (hΦ.memLp τ)).symm

theorem IsSliceTest.add (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) :
    IsSliceTest P r (Φ + Ψ) :=
  ⟨fun τ y => by simp [hΦ.1 τ y, hΨ.1 τ y], hΦ.2.add hΨ.2⟩

theorem IsSliceTest.const_smul (hΦ : IsSliceTest P r Φ) (c : ℂ) :
    IsSliceTest P r (c • Φ) :=
  ⟨fun τ y => by simp [hΦ.1 τ y], hΦ.2.const_smul c⟩

variable [Fact (0 < P)]

theorem testElem_add (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) :
    testElem P r (Φ + Ψ) = testElem P r Φ + testElem P r Ψ := by
  have hc : circleSlice (hΦ.add hΨ) = circleSlice hΦ + circleSlice hΨ := by
    ext1 τ
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      rw [ContinuousMap.add_apply, circleSlice_coe, circleSlice_coe, circleSlice_coe]
      exact MemLp.toLp_add (hΦ.2.memLp t) (hΨ.2.memLp t)
  exact (testElem_of (hΦ.add hΨ)).trans
    ((congrArg (ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r
      AddCircle.haarAddCircle ℂ) hc).trans
      ((map_add _ _ _).trans (congrArg₂ (· + ·) (testElem_of hΦ).symm (testElem_of hΨ).symm)))

theorem testElem_const_smul (hΦ : IsSliceTest P r Φ) (c : ℂ) :
    testElem P r (c • Φ) = c • testElem P r Φ := by
  have hc : circleSlice (hΦ.const_smul c) = c • circleSlice hΦ := by
    ext1 τ
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      rw [ContinuousMap.smul_apply, circleSlice_coe, circleSlice_coe]
      exact MemLp.toLp_const_smul c (hΦ.2.memLp t)
  exact (testElem_of (hΦ.const_smul c)).trans
    ((congrArg (ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r
      AddCircle.haarAddCircle ℂ) hc).trans
      ((map_smul _ _ _).trans (congrArg (c • ·) (testElem_of hΦ).symm)))

end Linear

section PairLinear

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {Φ Ψ : ℝ × Space → CVec3}

theorem phasePair_add (hΦ : IsPhaseTest P Φ) (hΨ : IsPhaseTest P Ψ) (f : Yq P q) :
    phasePair P q (Φ + Ψ) f = phasePair P q Φ f + phasePair P q Ψ f := by
  have h := testElem_add (hΦ.isSliceTest (conjExp q)) (hΨ.isSliceTest (conjExp q))
  simp only [phasePair]
  rw [h, map_add, ContinuousLinearMap.add_apply]

theorem phasePair_const_smul (hΦ : IsPhaseTest P Φ) (c : ℂ) (f : Yq P q) :
    phasePair P q (c • Φ) f = c * phasePair P q Φ f := by
  have h := testElem_const_smul (hΦ.isSliceTest (conjExp q)) c
  simp only [phasePair]
  rw [h, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem phasePair_real_smul (hΦ : IsPhaseTest P Φ) (c : ℝ) (f : Yq P q) :
    phasePair P q (c • Φ) f = (c : ℂ) * phasePair P q Φ f := by
  have h : c • Φ = (c : ℂ) • Φ := by
    funext p
    simp [Pi.smul_apply, Complex.coe_smul]
  rw [h, phasePair_const_smul hΦ]

theorem phasePair_neg (hΦ : IsPhaseTest P Φ) (f : Yq P q) :
    phasePair P q (-Φ) f = -phasePair P q Φ f := by
  have h : -Φ = (-1 : ℂ) • Φ := by
    funext p
    simp
  rw [h, phasePair_const_smul hΦ, neg_one_mul]

theorem phasePair_sub (hΦ : IsPhaseTest P Φ) (hΨ : IsPhaseTest P Ψ) (f : Yq P q) :
    phasePair P q (Φ - Ψ) f = phasePair P q Φ f - phasePair P q Ψ f := by
  rw [sub_eq_add_neg, phasePair_add hΦ hΨ.neg, phasePair_neg hΨ, ← sub_eq_add_neg]

theorem phasePair_zero (f : Yq P q) : phasePair P q 0 f = 0 := by
  have h0 : (0 : ℝ × Space → CVec3) = (0 : ℂ) • (0 : ℝ × Space → CVec3) := by simp
  rw [h0, phasePair_const_smul IsPhaseTest.zero, zero_mul]

theorem phasePair_sum {ι : Type*} (s : Finset ι) {Φ : ι → ℝ × Space → CVec3}
    (h : ∀ i ∈ s, IsPhaseTest P (Φ i)) (f : Yq P q) :
    phasePair P q (∑ i ∈ s, Φ i) f = ∑ i ∈ s, phasePair P q (Φ i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phasePair_zero f
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      phasePair_add (h a (Finset.mem_insert_self a s))
        (IsPhaseTest.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end PairLinear

/-! ### The pairing as an iterated period integral -/

section Formula

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {Φ : ℝ × Space → CVec3}

/-- For a phase test, the pairing is the period average of the spatial integral
`∫ Φ(τ, y) · f(τ)(y) dy`: the manuscript's normalised phase integral (tex 7315). -/
theorem phasePair_eq_periodIntegral (hΦ : IsPhaseTest P Φ) (f : Yq P q) :
    phasePair P q Φ f =
      P⁻¹ • ∫ t in Ioc (0 : ℝ) (0 + P),
        ∫ y, dotL (Φ (t, y)) ((f (t : AddCircle P) : Space → CVec3) y) := by
  have hs := hΦ.isSliceTest (conjExp q)
  rw [phasePair, phasePairing_apply, testElem_of hs]
  have h1 : (fun τ : AddCircle P => innerPair q
      ((ContinuousMap.toLp (E := Lp CVec3 (conjExp q) (volume : Measure Space)) (conjExp q)
        AddCircle.haarAddCircle ℂ (circleSlice hs)) τ) (f τ)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => innerPair q (circleSlice hs τ) (f τ) := by
    filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp q) (volume : Measure Space))
      (p := conjExp q) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)] with τ hτ
    rw [hτ]
  rw [integral_congr_ae h1, AddCircle.integral_haarAddCircle,
    ← AddCircle.integral_preimage (T := P) (0 : ℝ)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [circleSlice_coe, innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
  simp only [sliceMap]
  rw [hy]

end Formula

end UnforcedLeray.PhaseSpace
