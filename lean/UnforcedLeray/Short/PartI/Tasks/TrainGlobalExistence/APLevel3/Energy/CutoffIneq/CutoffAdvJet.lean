import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CutoffAdvTopL2
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord

/-!
# Part I, `PartI:T04/10/1/2/1/11` (`CutoffAdvJet`)

Source of record: `the November 2 reference manuscript`, lines 286-287.
Route: `CutoffAdvTopL2` for each coordinate word `g = ∂_u h`, the pointwise bound
`(∂_u h)² ≤ ‖D^j h‖²` (`cylJetWord_proof`), summation over the `2^j` words, and the constant
`C₂ = #wordsOfLength j · C₂(CutoffAdvTopL2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem cutoffAdvJet_proof : CutoffAdvJet := by
  obtain ⟨C, hC, hT⟩ := cutoffAdvTopL2_proof
  intro j
  refine ⟨((wordsOfLength j).card : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro c R M b h hc hR hb hh hbp hhp hdiv hbM hI
  have hR0 : 0 < R := by linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hbM 0)
  have hK : 0 ≤ C / R * M := mul_nonneg (div_nonneg hC hR0.le) hM0
  -- periodicity in the `q`-variable, in the `IsPeriodicQ` form used by `periodic_derivWord`
  have hhq : B0151.IsPeriodicQ c h := fun q η => hhp (q, η)
  -- the pointwise bound `(∂_u h)² ≤ ‖D^j h‖²` for words of length `j`
  have hpt : ∀ u ∈ wordsOfLength j, ∀ z : Plane,
      B0151.derivWord u h z ^ 2 ≤ ‖iteratedFDeriv ℝ j h z‖ ^ 2 := by
    intro u hu z
    have hlen : u.length = j := vjl_mem_wordsOfLength.1 hu
    have h1 : |B0151.derivWord u h z| ≤ ‖iteratedFDeriv ℝ j h z‖ :=
      (cylJetWord_proof h hh j z).1 u hlen
    calc B0151.derivWord u h z ^ 2 = |B0151.derivWord u h z| ^ 2 := (sq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ j h z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- each word derivative is smooth and periodic
  have hgC : ∀ u : List Bool, ContDiff ℝ ∞ (B0151.derivWord u h) :=
    fun u => B0151.contDiff_derivWord hh u
  have hgP : ∀ u : List Bool, Cyl.IsPeriodic c (B0151.derivWord u h) :=
    fun u z => B0151.periodic_derivWord hhq u z.1 z.2
  -- square integrability of each word derivative
  have hg2 : ∀ u ∈ wordsOfLength j,
      IntegrableOn (fun z => B0151.derivWord u h z ^ 2) (Cyl.cell c) := by
    intro u hu
    refine Integrable.mono' hI ?_ (ae_of_all _ (fun z => ?_))
    · exact ((hgC u).continuous.pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt u hu z
  -- the integrand of each word is continuous
  have hF : ∀ u : List Bool, Continuous
      (fun z : Plane => 2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z) :=
    fun u => (continuous_const.mul (hgC u).continuous).mul
      (vjl_scalarAdv_contDiff hb (hgC u)).continuous
  have hI1 : ∀ u : List Bool, IntegrableOn
      (fun z : Plane => etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z)) (Cyl.cell c) :=
    fun u => vjl_cutoff_integrable hR0 (hF u)
  -- splitting the integral of the word sum
  have hsplit : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        ∑ u ∈ wordsOfLength j, 2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z) =
      ∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z) := by
    calc (∫ z in Cyl.cell c, etaCutoff R z.2 *
          ∑ u ∈ wordsOfLength j, 2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z)
        = ∫ z in Cyl.cell c, ∑ u ∈ wordsOfLength j, etaCutoff R z.2 *
            (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z) := by
          congr 1
          funext z
          rw [Finset.mul_sum]
      _ = ∑ u ∈ wordsOfLength j, ∫ z in Cyl.cell c, etaCutoff R z.2 *
            (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z) :=
          integral_finsetSum _ (fun u _ => hI1 u)
  -- the one-word bound from `CutoffAdvTopL2`
  have hterm : ∀ u ∈ wordsOfLength j,
      -(∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z)) ≤
        C / R * M * ∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2 := by
    intro u hu
    exact hT c R M b (B0151.derivWord u h) hc hR hb (hgC u) hbp (hgP u) hdiv hbM (hg2 u hu)
  -- comparison of the word integrals with the full jet integral
  have hint : ∀ u ∈ wordsOfLength j,
      ∫ z in Cyl.cell c, B0151.derivWord u h z ^ 2 ≤
        ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2 :=
    fun u hu => integral_mono (hg2 u hu) hI (fun z => hpt u hu z)
  rw [hsplit, ← Finset.sum_neg_distrib]
  refine le_trans (Finset.sum_le_sum (fun u hu => hterm u hu)) ?_
  refine le_trans (Finset.sum_le_sum (fun u hu =>
    mul_le_mul_of_nonneg_left (hint u hu) hK)) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  apply le_of_eq
  ring

end UnforcedLeray.Short.PartI
