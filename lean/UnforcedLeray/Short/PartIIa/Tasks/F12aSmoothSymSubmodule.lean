import UnforcedLeray.Short.PartIIa.Sub.F12
import UnforcedLeray.Lib.PhaseSpace.Pairing

/-!
# Part II-a, task `PartII-a:F12/1`: smooth symmetric phase tensors form a subspace

Source of record: `the November 2 reference manuscript`, lines 1546-1586 (the
completion from smooth tensors). Proves `SmoothSymSubmodule` (defined in `Sub/F12.lean`).

`SmoothSymSubmodule` asserts that there is a linear subspace `M ≤ symY2 P` whose members are
exactly the smooth symmetric phase tensors `smoothTensor P G` (rows `G i` phase tests,
`IsSymRows G`).

Proof.
* Carrier: `smoothSymSet P = {X | ∃ G, (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = X}`.
  Zero, sums and complex multiples act rowwise: `testElem_zero`, `testElem_add` and
  `testElem_const_smul` (`Lib/PhaseSpace/Pairing.lean`, `ExtendedTest.lean`) make `smoothTensor`
  linear, and `IsPhaseTest.add`, `IsPhaseTest.const_smul` keep the rows phase tests.
* Containment: `symY2 P` is the intersection of the kernels of `symFun P i j φ`. For a smooth
  symmetric tensor, `symFun P i j φ (smoothTensor P G)` is the difference of two phase pairings,
  `phasePair P 2 (φ • e_j) (testElem P 2 (G i))` and `phasePair P 2 (φ • e_i) (testElem P 2 (G j))`.
  Lemma `smoothSym_phasePair_testElem` turns each into the normalised period integral
  `P⁻¹ ∫_{(0,P]} ∫_y ⟨Φ, G⟩`, which uses `phasePair_eq_periodIntegral` and an a.e. identification
  of the `Y_2` representative with the slice `G(t, ·)`. The two integrands are equal pointwise by
  `IsSymRows`, so the difference is zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- The bilinear dot product with a scaled basis vector: `(c e_j) · b = c b_j`. -/
theorem smoothSym_dotL_basis (c : ℂ) (j : Fin 3) (b : CVec3) :
    dotL (c • (EuclideanSpace.single j (1 : ℂ) : CVec3)) b = c * b j := by
  rw [dotL_apply]
  simp

/-- The vector field `p ↦ φ(p) e_j` is a phase test when the scalar field `φ` is one. -/
theorem smoothSym_isPhaseTest_basis {P : ℝ} [Fact (0 < P)] {φ : ℝ × Space → ℂ}
    (hφ : IsPhaseTest P φ) (j : Fin 3) :
    IsPhaseTest P (fun p => φ p • (EuclideanSpace.single j (1 : ℂ) : CVec3)) where
  smooth := hφ.smooth.smul_const _
  periodic τ y := by simp [hφ.periodic τ y]
  bounded_support := by
    obtain ⟨R, hR⟩ := hφ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

/-- On the phase circle `volume = P • haarAddCircle` (`AddCircle.volume_eq_smul_haarAddCircle`), and
a positive scalar does not change null sets: an a.e. statement for `volume` is one for the Haar
measure. -/
theorem smoothSym_ae_volume_iff {P : ℝ} [Fact (0 < P)] {p : AddCircle P → Prop} :
    (∀ᵐ τ ∂(volume : Measure (AddCircle P)), p τ) ↔
      ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), p τ := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  exact MeasureTheory.Measure.ae_ennreal_smul_measure_iff
    (ENNReal.ofReal_pos.2 (Fact.out : (0 : ℝ) < P)).ne'

/-- The phase pairing of a phase test with the `Y_2` element of a smooth phase test `G` is the
normalised period integral of the pointwise bilinear pairing `⟨Φ(t,y), G(t,y)⟩`. -/
theorem smoothSym_phasePair_testElem {P : ℝ} [Fact (0 < P)] {Φ G : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (hG : IsPhaseTest P G) :
    phasePair P 2 Φ (testElem P 2 G) =
      P⁻¹ • ∫ t in Ioc (0 : ℝ) (0 + P), ∫ y, dotL (Φ (t, y)) (G (t, y)) := by
  have hs := hG.isSliceTest 2
  have hc : ∀ᵐ τ : AddCircle P ∂(volume : Measure (AddCircle P)),
      (ContinuousMap.toLp (E := Lp CVec3 2 (volume : Measure Space)) 2 AddCircle.haarAddCircle ℂ
        (circleSlice hs)) τ = circleSlice hs τ :=
    smoothSym_ae_volume_iff.2 <| by
      filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space))
        (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)] with τ hτ
      exact hτ
  have hae : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) (0 + P))),
      testElem P 2 G (t : AddCircle P) = sliceMap hs.2 t := by
    rw [testElem_of hs]
    filter_upwards [(AddCircle.measurePreserving_mk (T := P) 0).quasiMeasurePreserving.ae hc]
      with t ht
    simpa only [circleSlice_coe] using ht
  rw [phasePair_eq_periodIntegral hΦ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [ht]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
  simp only [sliceMap]
  rw [hy]

/-- The set of smooth symmetric phase tensors: `smoothTensor P G` with rows `G i` phase tests and
`IsSymRows G`. -/
def smoothSymSet (P : ℝ) [Fact (0 < P)] : Set (Y2Sym P) :=
  {X | ∃ G : Fin 3 → ℝ × Space → CVec3,
    (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = X}

theorem mem_smoothSymSet {P : ℝ} [Fact (0 < P)] {X : Y2Sym P} :
    X ∈ smoothSymSet P ↔ ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = X :=
  Iff.rfl

theorem smoothSymSet_zero (P : ℝ) [Fact (0 < P)] : (0 : Y2Sym P) ∈ smoothSymSet P := by
  refine mem_smoothSymSet.2 ⟨0, fun i => IsPhaseTest.zero, fun i j p => by simp, ?_⟩
  ext i
  simp [smoothTensor, testElem_zero]

theorem smoothSymSet_add {P : ℝ} [Fact (0 < P)] {X X' : Y2Sym P}
    (hX : X ∈ smoothSymSet P) (hX' : X' ∈ smoothSymSet P) : X + X' ∈ smoothSymSet P := by
  obtain ⟨G, hG, hsG, rfl⟩ := mem_smoothSymSet.1 hX
  obtain ⟨G', hG', hsG', rfl⟩ := mem_smoothSymSet.1 hX'
  refine mem_smoothSymSet.2 ⟨G + G', fun i => (hG i).add (hG' i), fun i j p => ?_, ?_⟩
  · simp only [Pi.add_apply, PiLp.add_apply]
    rw [hsG i j p, hsG' i j p]
  · unfold smoothTensor
    rw [← WithLp.toLp_add]
    congr 1
    funext i
    exact testElem_add ((hG i).isSliceTest 2) ((hG' i).isSliceTest 2)

theorem smoothSymSet_smul {P : ℝ} [Fact (0 < P)] (c : ℂ) {X : Y2Sym P}
    (hX : X ∈ smoothSymSet P) : c • X ∈ smoothSymSet P := by
  obtain ⟨G, hG, hsG, rfl⟩ := mem_smoothSymSet.1 hX
  refine mem_smoothSymSet.2 ⟨c • G, fun i => (hG i).const_smul c, fun i j p => ?_, ?_⟩
  · simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hsG i j p]
  · unfold smoothTensor
    rw [← WithLp.toLp_smul]
    congr 1
    funext i
    exact testElem_const_smul ((hG i).isSliceTest 2) c

theorem smoothSymSet_subset_symY2 (P : ℝ) [Fact (0 < P)] :
    ∀ X ∈ smoothSymSet P, X ∈ symY2 P := by
  intro X hX
  obtain ⟨G, hG, hsG, rfl⟩ := mem_smoothSymSet.1 hX
  simp only [symY2, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  intro i j φ
  have h1 : (PiLp.proj 2 (fun _ : Fin 3 => Yq P 2) i : Y2Sym P →L[ℂ] Yq P 2) (smoothTensor P G) =
      testElem P 2 (G i) := rfl
  have h2 : (PiLp.proj 2 (fun _ : Fin 3 => Yq P 2) j : Y2Sym P →L[ℂ] Yq P 2) (smoothTensor P G) =
      testElem P 2 (G j) := rfl
  unfold symFun
  simp only [sub_apply, ContinuousLinearMap.comp_apply, h1, h2]
  rw [smoothSym_phasePair_testElem (smoothSym_isPhaseTest_basis φ.2 j) (hG i),
    smoothSym_phasePair_testElem (smoothSym_isPhaseTest_basis φ.2 i) (hG j)]
  have hcomm : ∀ (t : ℝ) (y : Space), φ.1 (t, y) * G i (t, y) j = φ.1 (t, y) * G j (t, y) i :=
    fun t y => by rw [hsG i j (t, y)]
  simp only [smoothSym_dotL_basis, hcomm, sub_self]

/-- **`PartII-a:F12/1`**: the smooth symmetric phase tensors form a linear subspace of `symY2 P`
whose members are exactly the smooth symmetric phase tensors (source lines 1546-1586). -/
theorem smoothSymSubmodule : SmoothSymSubmodule := by
  intro P _
  let M : Submodule ℂ (Y2Sym P) :=
    { carrier := smoothSymSet P
      add_mem' := fun {X X'} hX hX' => smoothSymSet_add hX hX'
      zero_mem' := smoothSymSet_zero P
      smul_mem' := fun c X hX => smoothSymSet_smul c hX }
  exact ⟨M, fun X hX => smoothSymSet_subset_symY2 P X hX, fun X => Iff.rfl⟩

end UnforcedLeray.Short.PartIIa
