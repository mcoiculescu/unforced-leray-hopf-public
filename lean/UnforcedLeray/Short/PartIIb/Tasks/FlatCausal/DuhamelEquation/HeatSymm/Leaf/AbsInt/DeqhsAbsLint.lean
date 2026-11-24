import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.AbsInt.DeqhsAbsMeas
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.AbsInt.DeqhsConvPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.AbsInt.DeqhsConvLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.AbsInt.DeqhsPeriodicBox

/-!
# Part II-b, leaf `DeqhsAbsLint` (SP 1923-1927): finiteness of the Fubini lintegral

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Route. Tonelli in the form `lintegral_prod` (the integrand is a.e. measurable by `DeqhsAbsMeas`)
gives `∫⁻ z, ofReal |ψ z| * convAbs θ g z`. The function `ψ` is bounded and vanishes outside a box
`B = [-R,R]²`, so this is at most `ofReal M * ∫⁻ z in B, convAbs θ g z`, which is finite by
`DeqhsPeriodicBox` applied to `h := convAbs θ g` (measurable and periodic by `DeqhsConvPeriodic`,
with finite cell `L^r` norm by `DeqhsConvLp`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T12/7/3/1/5`** (SP 1923-1927): finiteness of the lintegral of the Fubini integrand
(Tonelli, `DeqhsAbsMeas`, `DeqhsConvPeriodic`, `DeqhsConvLp`, `DeqhsPeriodicBox`). -/
theorem deqhsAbsLint : UnforcedLeray.Short.IIb.DeqhsAbsLint := by
  intro c r g hc hr hg θ hθ ψ hψ hψc
  have hK : ∀ w : ℝ × ℝ, 0 ≤ flatHeatKernel θ w := fun w => by
    unfold flatHeatKernel
    have := Real.pi_pos
    positivity
  -- (1) measurability of the integrand (a.e.), from `DeqhsAbsMeas`
  have hAE : AEMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (flatHeatKernel θ p.2 * ‖g (p.1 - p.2)‖ * |ψ p.1|))
      (volume.prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((deqhsAbsMeas c r g hc hr hg θ hθ ψ hψ).1.aemeasurable)
  -- (2) pointwise factorization of the integrand
  have key : ∀ z w : ℝ × ℝ, ENNReal.ofReal (flatHeatKernel θ w * ‖g (z - w)‖ * |ψ z|) =
      ENNReal.ofReal |ψ z| * (ENNReal.ofReal (flatHeatKernel θ w) * ‖g (z - w)‖ₑ) := by
    intro z w
    rw [ENNReal.ofReal_mul (mul_nonneg (hK w) (norm_nonneg _)),
      ENNReal.ofReal_mul (hK w), ofReal_norm]
    ring
  -- (3) Tonelli: the lintegral is `∫⁻ z, ofReal |ψ z| * convAbs θ g z`
  have hlint : ∫⁻ p : (ℝ × ℝ) × (ℝ × ℝ),
      ENNReal.ofReal (flatHeatKernel θ p.2 * ‖g (p.1 - p.2)‖ * |ψ p.1|)
        ∂(volume.prod volume) = ∫⁻ z : ℝ × ℝ, ENNReal.ofReal |ψ z| * convAbs θ g z := by
    rw [lintegral_prod _ hAE]
    refine lintegral_congr fun z => ?_
    rw [convAbs, ← lintegral_const_mul' (ENNReal.ofReal |ψ z|) _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun w => key z w
  -- (4) ingredients: periodicity, measurability, `L^r` bound of `convAbs`
  have hcp := deqhsConvPeriodic c r g hc hr hg θ hθ
  have hmeas : Measurable (convAbs θ g) := hcp.1
  have hper : ∀ z : ℝ × ℝ, convAbs θ g (z.1 + c, z.2) = convAbs θ g z := hcp.2
  have hLp := deqhsConvLp c r g hc hr hg θ hθ
  -- (5) bounds on `ψ` and its support box
  obtain ⟨M, hM⟩ := hψ.bounded_above_of_compact_support hψc
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hψc.isCompact.isBounded
  let B : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R
  have hBm : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hsupp : ∀ z : ℝ × ℝ, ψ z ≠ 0 → z ∈ B := by
    intro z hne
    have hn := hR z (subset_tsupport ψ (Function.mem_support.2 hne))
    have h1 := norm_fst_le z
    have h2 := norm_snd_le z
    rw [Real.norm_eq_abs] at h1 h2
    obtain ⟨a1, a2⟩ := abs_le.1 (h1.trans hn)
    obtain ⟨b1, b2⟩ := abs_le.1 (h2.trans hn)
    simp only [B, Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  have hpt : ∀ z : ℝ × ℝ, ENNReal.ofReal |ψ z| * convAbs θ g z ≤
      B.indicator (fun z => ENNReal.ofReal M * convAbs θ g z) z := by
    intro z
    by_cases hz : z ∈ B
    · rw [indicator_of_mem hz]
      have h1 : |ψ z| ≤ M := by
        have := hM z
        rwa [Real.norm_eq_abs] at this
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h1) _
    · have h0 : ψ z = 0 := by
        by_contra hne
        exact hz (hsupp z hne)
      rw [indicator_of_notMem hz, h0]
      simp
  -- (6) the box integral of `convAbs` is finite
  have hBfin : ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, convAbs θ g z < ⊤ :=
    deqhsPeriodicBox c r hc hr (convAbs θ g) hmeas hper hLp R
  rw [hlint]
  calc ∫⁻ z : ℝ × ℝ, ENNReal.ofReal |ψ z| * convAbs θ g z
      ≤ ∫⁻ z : ℝ × ℝ, B.indicator (fun z => ENNReal.ofReal M * convAbs θ g z) z :=
        lintegral_mono hpt
    _ = ∫⁻ z in B, ENNReal.ofReal M * convAbs θ g z := lintegral_indicator hBm _
    _ = ENNReal.ofReal M * ∫⁻ z in B, convAbs θ g z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBfin

end UnforcedLeray.Short.IIb
