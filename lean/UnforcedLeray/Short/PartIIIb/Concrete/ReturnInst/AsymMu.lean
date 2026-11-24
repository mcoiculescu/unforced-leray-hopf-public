import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.NhdsWithin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# The Floquet window stays compact: `μ_n(z) ∈ K ⋐ (0, 1/4)` (source 5946-5950)

Source of record: `the November 2 reference manuscript` (73 pages), lines 5946-5950:
`μ_n(z) = σ₀ + z/(2|log ν_n|)` stays in a compact `K ⋐ (0,1/4)` for large `n`, uniformly in
`z ∈ [-1,1]`.  Here `K = [σ₀/2, (σ₀+1/4)/2]`.

Write `δ = min (σ₀/2) ((1/4 - σ₀)/2) > 0`.  Since `ν_n → 0⁺`, `log ν_n → -∞`, so eventually
`|log ν_n| ≥ 1/δ`, and then `|z/(2|log ν_n|)| ≤ δ` for `|z| ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem mu_eventually_mem (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4) : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (D.σ₀ / 2) ((1 / 4 - D.σ₀) / 2) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ D.σ₀ / 2 := by
    rw [hδ]
    exact min_le_left _ _
  have hδ2 : δ ≤ (1 / 4 - D.σ₀) / 2 := by
    rw [hδ]
    exact min_le_right _ _
  have hνT : Tendsto (retNu D.Pl D.σ₀) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨retNu_tendsto D.σ₀ hω, Eventually.of_forall (retNu_pos D.Pl D.σ₀)⟩
  have hLT : Tendsto (fun n : ℕ => Real.log (retNu D.Pl D.σ₀ n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hνT
  have hev : ∀ᶠ n : ℕ in atTop, Real.log (retNu D.Pl D.σ₀ n) ≤ -(1 / δ) :=
    Filter.tendsto_atBot.1 hLT (-(1 / δ))
  filter_upwards [hev] with n hn z hz
  have hLle : 1 / δ ≤ |Real.log (retNu D.Pl D.σ₀ n)| := by
    linarith [neg_le_abs (Real.log (retNu D.Pl D.σ₀ n))]
  have hLpos : 0 < |Real.log (retNu D.Pl D.σ₀ n)| := lt_of_lt_of_le (one_div_pos.2 hδpos) hLle
  have h2L : 0 < 2 * |Real.log (retNu D.Pl D.σ₀ n)| := by linarith
  have hδL : 1 ≤ |Real.log (retNu D.Pl D.σ₀ n)| * δ := (div_le_iff₀ hδpos).1 hLle
  have hz1 : |z| ≤ 1 := abs_le.2 ⟨hz.1, hz.2⟩
  have hzt : |z / (2 * |Real.log (retNu D.Pl D.σ₀ n)|)| ≤ δ := by
    rw [abs_div, abs_of_pos h2L, div_le_iff₀ h2L]
    have e : δ * (2 * |Real.log (retNu D.Pl D.σ₀ n)|) =
        2 * (|Real.log (retNu D.Pl D.σ₀ n)| * δ) := by ring
    rw [e]
    linarith [abs_nonneg z]
  obtain ⟨ht1, ht2⟩ := abs_le.1 hzt
  rw [Set.mem_Icc]
  show D.σ₀ / 2 ≤ D.σ₀ + z / (2 * |Real.log (retNu D.Pl D.σ₀ n)|) ∧
    D.σ₀ + z / (2 * |Real.log (retNu D.Pl D.σ₀ n)|) ≤ (D.σ₀ + 1 / 4) / 2
  constructor <;> linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
