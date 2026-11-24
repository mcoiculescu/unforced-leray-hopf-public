import UnforcedLeray.Short.PartIIa.Tasks.F12bPhaseInnerEqPairing
import UnforcedLeray.Units.B0411.Separation
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest

/-!
# Part II-a, task `PartII-a:F12/3`: `smoothSymSeparation`

Proves `SmoothSymSeparation` (defined in `Sub/F12.lean`) from `phaseInnerEqPairing`
(task `PartII-a:F12/2`, `Tasks/F12bPhaseInnerEqPairing.lean`).

Source of record: `the November 2 reference manuscript`, lines 1546-1586.

Proof outline. Write `e_b` for `EuclideanSpace.single b 1` and `⟨Φ, g⟩` for `phasePair P 2 Φ g`.

1. By `phaseInnerEqPairing`, `inner (testElem Φ) g = ⟨conjF Φ, g⟩` for a phase test `Φ`.
2. Diagonal probe. For a scalar phase test `φ`, the rows `G a = conjF (φ e_a)` and `G i = 0`
   (`i ≠ a`) form a symmetric tensor. The hypothesis gives `⟨φ e_a, Z a⟩ = 0`.
3. Off-diagonal probe (`a ≠ b`). The rows `G a = conjF (φ e_b)`, `G b = conjF (φ e_a)` and
   zero otherwise form a symmetric tensor. The hypothesis gives `⟨φ e_b, Z a⟩ + ⟨φ e_a, Z b⟩ = 0`,
   and the symmetry of `Z` gives `⟨φ e_b, Z a⟩ = ⟨φ e_a, Z b⟩`. Hence `⟨φ e_b, Z a⟩ = 0`.
4. A vector phase test `Ψ` is `∑ b, (Ψ · b) e_b`, a sum of scalar phase tests times basis
   vectors, so `⟨Ψ, Z a⟩ = 0` for every `a`. Separation (`B0411.eq_zero_of_forall_phasePair`)
   gives `Z a = 0`, hence `Z = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Coordinatewise conjugation is an involution. -/
theorem conjF_conjF (Φ : ℝ × Space → CVec3) : conjF (conjF Φ) = Φ := by
  funext p
  ext k
  simp [conjF]

/-- A scalar phase test times a fixed vector is a vector phase test. -/
theorem smul_vec_isPhaseTest {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) (e : CVec3) :
    IsPhaseTest P (fun p => φ p • e) where
  smooth := ContDiff.smul hφ.smooth contDiff_const
  periodic τ y := by simp [hφ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hφ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

/-- A coordinate of a vector phase test is a scalar phase test. -/
theorem coord_isPhaseTest {P : ℝ} {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) (b : Fin 3) :
    IsPhaseTest P (fun p => Ψ p b) :=
  hΨ.clm_comp ((EuclideanSpace.proj b : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)

/-- A sum over the rows that has a single nonzero row `a`. -/
theorem sum_one_row {P : ℝ} [Fact (0 < P)] (Z : Y2Sym P) (a : Fin 3) (X : ℝ × Space → CVec3) :
    ∑ i, inner ℂ (testElem P 2 (if i = a then X else 0)) (Z i) =
      inner ℂ (testElem P 2 X) (Z a) := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb, testElem_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- A sum over the rows that has two nonzero rows `a ≠ b`. -/
theorem sum_two_rows {P : ℝ} [Fact (0 < P)] (Z : Y2Sym P) (a b : Fin 3) (hab : a ≠ b)
    (X Y : ℝ × Space → CVec3) :
    ∑ i, inner ℂ (testElem P 2 (if i = a then X else if i = b then Y else 0)) (Z i) =
      inner ℂ (testElem P 2 X) (Z a) + inner ℂ (testElem P 2 Y) (Z b) := by
  rw [Finset.sum_eq_add a b hab]
  · simp [hab.symm]
  · intro c _ hc
    simp [hc.1, hc.2, testElem_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- **Task `PartII-a:F12/3`**: a symmetric tensor orthogonal to all smooth symmetric phase tensors
vanishes. -/
theorem smoothSymSeparation : SmoothSymSeparation := by
  unfold SmoothSymSeparation
  intro P hP Z hZ horth
  -- (1) the Hilbert pairing against a phase test, as a phase pairing
  have hIP : ∀ (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ → ∀ g : Yq P 2,
      inner ℂ (testElem P 2 Φ) g = phasePair P 2 (conjF Φ) g :=
    fun Φ hΦ g => (phaseInnerEqPairing P Φ hΦ).2 g
  -- (2) the hypothesis, read as a sum over the rows
  have hsum : ∀ G : Fin 3 → ℝ × Space → CVec3, (∀ i, IsPhaseTest P (G i)) → IsSymRows G →
      ∑ i, inner ℂ (testElem P 2 (G i)) (Z i) = 0 := by
    intro G hG hS
    have h := horth G hG hS
    rw [PiLp.inner_apply] at h
    simpa [smoothTensor] using h
  -- (3) symmetry of `Z` against scalar phase tests
  have hsymZ : ∀ (i j : Fin 3) (φ : ℝ × Space → ℂ), IsPhaseTest P φ →
      phasePair P 2 (fun p => φ p • (EuclideanSpace.single j (1 : ℂ) : CVec3)) (Z i) =
        phasePair P 2 (fun p => φ p • (EuclideanSpace.single i (1 : ℂ) : CVec3)) (Z j) := by
    intro i j φ hφ
    have hsym : symFun P i j φ Z = 0 := by
      have h := hZ
      simp only [symY2, Submodule.mem_iInf, LinearMap.mem_ker] at h
      exact h i j ⟨φ, hφ⟩
    unfold symFun at hsym
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      PiLp.proj_apply] at hsym
    exact sub_eq_zero.1 hsym
  -- (4) diagonal probe
  have hdiag : ∀ (a : Fin 3) (φ : ℝ × Space → ℂ), IsPhaseTest P φ →
      phasePair P 2 (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3)) (Z a) = 0 := by
    intro a φ hφ
    have hΦ : IsPhaseTest P (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3)) :=
      smul_vec_isPhaseTest hφ _
    have hG : ∀ i, IsPhaseTest P
        (if i = a then conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3)) else 0) := by
      intro i
      split_ifs
      · exact conjF_isPhaseTest hΦ
      · exact IsPhaseTest.zero
    have hS : IsSymRows
        (fun i => if i = a then conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3))
          else 0) := by
      intro i j p
      by_cases hi : i = a <;> by_cases hj : j = a <;>
        simp [conjF, hi, hj]
    have h : ∑ i, inner ℂ (testElem P 2
        (if i = a then conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3)) else 0))
        (Z i) = 0 := hsum _ hG hS
    have hsingle := sum_one_row Z a (conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3)))
    have h2 := hsingle.symm.trans h
    have h3 := hIP _ (conjF_isPhaseTest hΦ) (Z a)
    rw [conjF_conjF] at h3
    rw [← h3]
    exact h2
  -- (5) off-diagonal probe
  have hoff : ∀ (a b : Fin 3) (φ : ℝ × Space → ℂ), a ≠ b → IsPhaseTest P φ →
      phasePair P 2 (fun p => φ p • (EuclideanSpace.single b (1 : ℂ) : CVec3)) (Z a) = 0 := by
    intro a b φ hab hφ
    have hΦa : IsPhaseTest P (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3)) :=
      smul_vec_isPhaseTest hφ _
    have hΦb : IsPhaseTest P (fun p => φ p • (EuclideanSpace.single b (1 : ℂ) : CVec3)) :=
      smul_vec_isPhaseTest hφ _
    have hG : ∀ i, IsPhaseTest P
        (if i = a then conjF (fun p => φ p • (EuclideanSpace.single b (1 : ℂ) : CVec3))
          else if i = b then conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3))
          else 0) := by
      intro i
      split_ifs
      · exact conjF_isPhaseTest hΦb
      · exact conjF_isPhaseTest hΦa
      · exact IsPhaseTest.zero
    have hS : IsSymRows
        (fun i => if i = a then conjF (fun p => φ p • (EuclideanSpace.single b (1 : ℂ) : CVec3))
          else if i = b then conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3))
          else 0) := by
      intro i j p
      by_cases hia : i = a <;> by_cases hib : i = b <;> by_cases hja : j = a <;>
        by_cases hjb : j = b <;>
        simp [conjF, hia, hib, hja, hjb, hab, hab.symm]
    have hsum2 : ∑ i, inner ℂ (testElem P 2
        (if i = a then conjF (fun p => φ p • (EuclideanSpace.single b (1 : ℂ) : CVec3))
          else if i = b then conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3))
          else 0)) (Z i) = 0 := hsum _ hG hS
    have hcol := sum_two_rows Z a b hab (conjF (fun p => φ p • (EuclideanSpace.single b (1 : ℂ) : CVec3)))
      (conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3)))
    have hXY := hcol.symm.trans hsum2
    have e1 := hIP (conjF (fun p => φ p • (EuclideanSpace.single b (1 : ℂ) : CVec3)))
      (conjF_isPhaseTest hΦb) (Z a)
    have e2 := hIP (conjF (fun p => φ p • (EuclideanSpace.single a (1 : ℂ) : CVec3)))
      (conjF_isPhaseTest hΦa) (Z b)
    rw [conjF_conjF] at e1 e2
    have hs := hsymZ a b φ hφ
    rw [e1, e2] at hXY
    linear_combination (1 / 2 : ℂ) * hXY + (1 / 2 : ℂ) * hs
  -- (6) scalar probes against every basis direction
  have hkey : ∀ (a b : Fin 3) (φ : ℝ × Space → ℂ), IsPhaseTest P φ →
      phasePair P 2 (fun p => φ p • (EuclideanSpace.single b (1 : ℂ) : CVec3)) (Z a) = 0 := by
    intro a b φ hφ
    by_cases hab : a = b
    · subst hab
      exact hdiag _ φ hφ
    · exact hoff a b φ hab hφ
  -- (7) vector phase tests
  have hvec : ∀ (a : Fin 3) (Ψ : ℝ × Space → CVec3), IsPhaseTest P Ψ →
      phasePair P 2 Ψ (Z a) = 0 := by
    intro a Ψ hΨ
    have hdec : Ψ = ∑ b : Fin 3, (fun p => Ψ p b • (EuclideanSpace.single b (1 : ℂ) : CVec3)) := by
      funext p
      rw [Finset.sum_apply]
      have h := (EuclideanSpace.basisFun (Fin 3) ℂ).sum_repr (Ψ p)
      simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
      exact h.symm
    calc phasePair P 2 Ψ (Z a)
        = phasePair P 2 (∑ b : Fin 3, (fun p => Ψ p b • (EuclideanSpace.single b (1 : ℂ) : CVec3)))
            (Z a) := by rw [← hdec]
      _ = ∑ b : Fin 3, phasePair P 2
            (fun p => Ψ p b • (EuclideanSpace.single b (1 : ℂ) : CVec3)) (Z a) :=
          phasePair_sum _ (fun b _ => smul_vec_isPhaseTest (coord_isPhaseTest hΨ b) _) _
      _ = 0 := Finset.sum_eq_zero fun b _ => hkey a b (fun p => Ψ p b) (coord_isPhaseTest hΨ b)
  -- (8) separation of phase tests
  refine PiLp.ext fun a => ?_
  rw [PiLp.zero_apply]
  exact eq_zero_of_forall_phasePair fun Ψ hΨ => hvec a Ψ hΨ

end UnforcedLeray.Short.PartIIa
