import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CutoffViscousL2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.WordSqSucc
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord

/-!
# Part I, `PartI:T04/10/1/2/1/9` (`CutoffViscousJet`)

Source of record: `the November 2 reference manuscript`, lines 285-287.
Route: `CutoffViscousL2` for each word `g = ∂_u h` with `|u| = j` (`2^j` words, constant
`C₁ · card`), the word-sum dissipation identity `WordSqSucc`, and the pointwise bounds
`(∂_u h)² ≤ ‖D^j h‖²`, `(∂_η ∂_u h)² ≤ ‖D^{j+1} h‖²` from `cylJetWord_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem cutoffViscousJet_proof : CutoffViscousJet := by
  intro j
  obtain ⟨C₁, hC₁, hL2⟩ := cutoffViscousL2_proof
  refine ⟨((wordsOfLength j).card : ℝ) * C₁, mul_nonneg (Nat.cast_nonneg _) hC₁, ?_⟩
  intro c R h hc hR hsm hper hI0 hI1
  have hR0 : (0 : ℝ) < R := by linarith
  have hK : 0 ≤ C₁ / R := div_nonneg hC₁ hR0.le
  have hCJ : CylJetWord := cylJetWord_proof
  have hS : WordSqSucc := wordSqSucc_proof
  -- pointwise word bounds
  have hbd1 : ∀ u ∈ wordsOfLength j, ∀ z : Plane,
      B0151.derivWord u h z ^ 2 ≤ ‖iteratedFDeriv ℝ j h z‖ ^ 2 := by
    intro u hu z
    have h1 : |B0151.derivWord u h z| ≤ ‖iteratedFDeriv ℝ j h z‖ :=
      (hCJ h hsm j z).1 u (vjl_mem_wordsOfLength.1 hu)
    calc B0151.derivWord u h z ^ 2 = |B0151.derivWord u h z| ^ 2 := (sq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ j h z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hbd2 : ∀ u ∈ wordsOfLength j, ∀ z : Plane,
      Cyl.partialEta (B0151.derivWord u h) z ^ 2 ≤ ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2 := by
    intro u hu z
    have hlen : (false :: u).length = j + 1 := by
      simp [vjl_mem_wordsOfLength.1 hu]
    have h1 : |B0151.derivWord (false :: u) h z| ≤ ‖iteratedFDeriv ℝ (j + 1) h z‖ :=
      (hCJ h hsm (j + 1) z).1 (false :: u) hlen
    rw [partialEta_derivWord]
    calc B0151.derivWord (false :: u) h z ^ 2
        = |B0151.derivWord (false :: u) h z| ^ 2 := (sq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- periodicity and integrability of the words
  have hper' : ∀ u : List Bool, Cyl.IsPeriodic c (B0151.derivWord u h) := fun u z =>
    B0151.periodic_derivWord (L := c) (h := h) (fun q e => hper (q, e)) u z.1 z.2
  have hint1 : ∀ u ∈ wordsOfLength j,
      IntegrableOn (fun z => B0151.derivWord u h z ^ 2) (Cyl.cell c) := by
    intro u hu
    refine Integrable.mono' hI0 ((B0151.contDiff_derivWord hsm u).continuous.pow 2).aestronglyMeasurable
      (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbd1 u hu z
  have hint2 : ∀ u ∈ wordsOfLength j,
      IntegrableOn (fun z => Cyl.partialEta (B0151.derivWord u h) z ^ 2) (Cyl.cell c) := by
    intro u hu
    have hm : Continuous (fun z => Cyl.partialEta (B0151.derivWord u h) z ^ 2) := by
      simp only [partialEta_derivWord]
      exact ((B0151.contDiff_derivWord hsm (false :: u)).continuous).pow 2
    refine Integrable.mono' hI1 hm.aestronglyMeasurable (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbd2 u hu z
  -- the cutoff times the viscous term is integrable, word by word
  have hLint : ∀ u ∈ wordsOfLength j,
      IntegrableOn (fun z => etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z)) (Cyl.cell c) := by
    intro u _
    have hcont : Continuous (fun z => 2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z) :=
      (continuous_const.mul (B0151.contDiff_derivWord hsm u).continuous).mul
        (vjl_lapS_contDiff (B0151.contDiff_derivWord hsm u)).continuous
    exact vjl_cutoff_integrable hR0 hcont
  -- the dissipation density is continuous, and its word sum is the `(j+1)`-jet
  have hcontD : ∀ u : List Bool,
      Continuous (fun z : Plane => Cyl.partialQ (B0151.derivWord u h) z ^ 2 +
        Cyl.partialEta (B0151.derivWord u h) z ^ 2) := by
    intro u
    simp only [partialQ_derivWord, partialEta_derivWord]
    exact ((B0151.contDiff_derivWord hsm (true :: u)).continuous.pow 2).add
      ((B0151.contDiff_derivWord hsm (false :: u)).continuous.pow 2)
  have hLintD : ∀ u ∈ wordsOfLength j,
      IntegrableOn (fun z => etaCutoff R z.2 *
        (Cyl.partialQ (B0151.derivWord u h) z ^ 2 + Cyl.partialEta (B0151.derivWord u h) z ^ 2))
        (Cyl.cell c) := fun u _ => vjl_cutoff_integrable hR0 (hcontD u)
  -- sum of the left-hand sides
  have hsumL : ∫ z in Cyl.cell c, etaCutoff R z.2 *
      ∑ u ∈ wordsOfLength j, 2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z =
      ∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z) := by
    simp_rw [Finset.mul_sum]
    exact integral_finset_sum _ (fun u hu => hLint u hu)
  -- the dissipation sum is the `(j+1)`-jet energy
  have hsumD : ∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, etaCutoff R z.2 *
      (Cyl.partialQ (B0151.derivWord u h) z ^ 2 + Cyl.partialEta (B0151.derivWord u h) z ^ 2) =
      ∫ z in Cyl.cell c, etaCutoff R z.2 * wordSq (j + 1) h z := by
    have hpt : ∀ z : Plane, etaCutoff R z.2 * wordSq (j + 1) h z =
        ∑ u ∈ wordsOfLength j, etaCutoff R z.2 *
          (Cyl.partialQ (B0151.derivWord u h) z ^ 2 + Cyl.partialEta (B0151.derivWord u h) z ^ 2) := by
      intro z
      rw [← hS h j z, Finset.mul_sum]
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun u hu => hLintD u hu)]
  -- the per-word bounds
  have hw : ∀ u ∈ wordsOfLength j,
      ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z) ≤
      -(2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
          (Cyl.partialQ (B0151.derivWord u h) z ^ 2 + Cyl.partialEta (B0151.derivWord u h) z ^ 2)) +
        C₁ / R * ((∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2) +
          ∫ z in Cyl.cell c, Cyl.partialEta (B0151.derivWord u h) z ^ 2) := by
    intro u hu
    exact hL2 c R (B0151.derivWord u h) hc hR (B0151.contDiff_derivWord hsm u) (hper' u)
      (hint1 u hu) (hint2 u hu)
  -- summing the word bounds
  have hmain := Finset.sum_le_sum hw
  have hexp : ∑ u ∈ wordsOfLength j,
      (-(2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
          (Cyl.partialQ (B0151.derivWord u h) z ^ 2 + Cyl.partialEta (B0151.derivWord u h) z ^ 2)) +
        C₁ / R * ((∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2) +
          ∫ z in Cyl.cell c, Cyl.partialEta (B0151.derivWord u h) z ^ 2)) =
      -(2 * ∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, etaCutoff R z.2 *
          (Cyl.partialQ (B0151.derivWord u h) z ^ 2 + Cyl.partialEta (B0151.derivWord u h) z ^ 2)) +
        C₁ / R * ((∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2) +
          ∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, Cyl.partialEta (B0151.derivWord u h) z ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  -- comparison of the word sums with the full jets
  have hA : ∀ u ∈ wordsOfLength j,
      (∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2) ≤ ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2 :=
    fun u hu => integral_mono (hint1 u hu) hI0 (fun z => hbd1 u hu z)
  have hB : ∀ u ∈ wordsOfLength j,
      (∫ z in Cyl.cell c, Cyl.partialEta (B0151.derivWord u h) z ^ 2) ≤
        ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2 :=
    fun u hu => integral_mono (hint2 u hu) hI1 (fun z => hbd2 u hu z)
  have hsumA : ∑ u ∈ wordsOfLength j, (∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2) ≤
      ((wordsOfLength j).card : ℝ) * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2 := by
    calc ∑ u ∈ wordsOfLength j, (∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2)
        ≤ ∑ _u ∈ wordsOfLength j, ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2 :=
          Finset.sum_le_sum hA
      _ = ((wordsOfLength j).card : ℝ) * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsumB : ∑ u ∈ wordsOfLength j, (∫ z in Cyl.cell c, Cyl.partialEta (B0151.derivWord u h) z ^ 2) ≤
      ((wordsOfLength j).card : ℝ) * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2 := by
    calc ∑ u ∈ wordsOfLength j, (∫ z in Cyl.cell c, Cyl.partialEta (B0151.derivWord u h) z ^ 2)
        ≤ ∑ _u ∈ wordsOfLength j, ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2 :=
          Finset.sum_le_sum hB
      _ = ((wordsOfLength j).card : ℝ) * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hfin : C₁ / R * ((∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2) +
      ∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, Cyl.partialEta (B0151.derivWord u h) z ^ 2) ≤
      ((wordsOfLength j).card : ℝ) * C₁ / R *
        ((∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2) +
          ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2) := by
    have e : ((wordsOfLength j).card : ℝ) * C₁ / R *
        ((∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2) +
          ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2) =
        C₁ / R * ((((wordsOfLength j).card : ℝ) * (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2)) +
          ((wordsOfLength j).card : ℝ) * (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2)) := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (add_le_add hsumA hsumB) hK
  -- the integral of the left-hand side is the sum of the word integrals
  rw [hsumL]
  linarith [hmain, hexp, hfin, hsumD]

end UnforcedLeray.Short.PartI
