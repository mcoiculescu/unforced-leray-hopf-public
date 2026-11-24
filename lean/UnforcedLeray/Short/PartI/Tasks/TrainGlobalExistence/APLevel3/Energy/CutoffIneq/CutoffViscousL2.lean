import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, `PartI:T04/10/1/2/1/7` (`CutoffViscousL2`)

Source of record: `the November 2 reference manuscript`, lines 286-287.
Route: `vi_scalar` gives `∫χ g Δg = -∫χ(|∂_q g|²+|∂_η g|²) - ∫χ' g ∂_η g`; `|χ'| ≤ C₀/R`
(from `etaCutoffFacts`, with `χ ≤ 1`); and `-2 χ' g ∂_η g ≤ (C₀/R)(g² + (∂_η g)²)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem cutoffViscousL2_proof : CutoffViscousL2 := by
  obtain ⟨C₀, hC₀, hcut⟩ := etaCutoffFacts
  refine ⟨C₀, hC₀, ?_⟩
  intro c R g hc hR hg hper hg2 hpe2
  have hR0 : 0 < R := by linarith
  have hK : 0 ≤ C₀ / R := div_nonneg hC₀ (by linarith)
  obtain ⟨hsm, h01, -, hzero, hder⟩ := hcut R hR
  have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h0 := hder η
    rw [hzero η hη, Real.sqrt_zero, mul_zero] at h0
    exact abs_nonpos_iff.1 h0
  -- pointwise `|χ'| ≤ C₀/R`
  have hd : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C₀ / R := by
    intro η
    have hs1 : Real.sqrt (etaCutoff R η) ≤ 1 := by
      have := Real.sqrt_le_sqrt (h01 η).2
      rwa [Real.sqrt_one] at this
    calc |deriv (etaCutoff R) η| ≤ C₀ / R * Real.sqrt (etaCutoff R η) := hder η
      _ ≤ C₀ / R * 1 := mul_le_mul_of_nonneg_left hs1 hK
      _ = C₀ / R := mul_one _
  obtain ⟨-, -, hC, -⟩ := vi_scalar hc hR0 cellIntegrable_of_support cellDerivZero_of_periodic
    hsm hzero hdzero g hg hper
  obtain ⟨-, -, -, hD⟩ := vi_scalar hc hR0 cellIntegrable_of_support cellDerivZero_of_periodic
    hsm hzero hdzero g hg hper
  -- rewrite `2 g Δg` as `2 (g Δg)` and pull out the constant
  have e1 : ∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * Train.lapS g z) =
      2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (g z * (Cyl.partialQ (Cyl.partialQ g) z + Cyl.partialEta (Cyl.partialEta g) z)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    unfold Train.lapS
    ring
  -- the pointwise bound on the cutoff-derivative term
  have hpt : ∀ z : Plane,
      -2 * (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z)) ≤
        C₀ / R * (g z ^ 2 + Cyl.partialEta g z ^ 2) := by
    intro z
    have hbe : 2 * (|g z| * |Cyl.partialEta g z|) ≤ g z ^ 2 + Cyl.partialEta g z ^ 2 := by
      nlinarith [sq_abs (g z), sq_abs (Cyl.partialEta g z),
        sq_nonneg (|g z| - |Cyl.partialEta g z|)]
    have hab : |deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z)| ≤
        C₀ / R * (|g z| * |Cyl.partialEta g z|) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hd z.2) (by positivity)
    nlinarith [neg_le_abs (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z)), hab,
      mul_le_mul_of_nonneg_left hbe hK]
  have hineq : ∫ z in Cyl.cell c, -2 * (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z)) ≤
      ∫ z in Cyl.cell c, C₀ / R * (g z ^ 2 + Cyl.partialEta g z ^ 2) :=
    integral_mono (hC.const_mul (-2)) ((hg2.add hpe2).const_mul (C₀ / R)) hpt
  rw [integral_const_mul, integral_const_mul, integral_add hg2 hpe2] at hineq
  rw [e1, hD]
  linarith [hineq]

end UnforcedLeray.Short.PartI
