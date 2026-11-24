import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages

/-!
# Part II-b, task `PartII-b:T22/1/11` (`ConvTimeDeriv`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2074-2093 and
2103-2105. For `G(t) = ∫_s^t H_{ν(t-r)} F(r) dr` and `f_t(r) = H_{ν(t-r)}F(r)(x)` (the identity
for `r ≥ t`),
`G(t) - G(τ) = ∫_s^τ (f_t - f_τ) dr + ∫_τ^t f_t dr`. The first piece, divided by `t - τ`, tends to
`ν Σ_i ∫_s^τ (∂_iK_{ν(τ-r)} * ∂_iF(r)) dr` (`ConvTD_Quot`, via `ConvTD_A`: `∂_a H_a g = Σ_i
(∂_iK_a) * ∂_i g` for `g ∈ C¹`); the second tends to `F(τ)(x)` (`ConvTD_Bdry`). Integrability of
`f_t` on `[s, T]` is `ConvTD_Int`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- (a) `∂_a H_a g = Σ_i (∂_iK_a) * ∂_i g` for `g ∈ C¹` with `g, ∇g` weight-bounded and `a > 0`
(from `∂_aK_a = ΔK_a` and one integration by parts; `HeatEqn` itself needs `C²`). -/
def ConvTD_A : Prop := ∀ (B : ℝ) (g : Pl → ℝ), ContDiff ℝ 1 g → WB B g →
  (∀ j : Fin 2, WB B (B0579.pd j g)) → ∀ a : ℝ, 0 < a → ∀ x : Pl,
    HasDerivAt (fun b : ℝ => heatSG b g x) (∑ i : Fin 2, heatSGd i a (B0579.pd i g) x) a

/-- Integrability of `r ↦ H_{ν(t-r)} F(r)(x)` on `[s, T]` for `t ∈ [s, T]` (bounded by `B`,
measurable by `HeatCont` and the continuity of `F`; the identity for `r ≥ t`). -/
def ConvTD_Int : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r)) → ∀ t ∈ Icc s T, ∀ x : Pl,
    IntervalIntegrable (fun r : ℝ => heatSG (ν * (t - r)) (F r) x) volume s T

/-- (c) The boundary term: `(t-τ)⁻¹ ∫_τ^t H_{ν(t-r)} F(r)(x) dr → F(τ)(x)`. -/
def ConvTD_Bdry : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r)) → ∀ τ ∈ Icc s T, ∀ x : Pl,
    Tendsto (fun t : ℝ => (t - τ)⁻¹ * ∫ r in τ..t, heatSG (ν * (t - r)) (F r) x)
      (𝓝[Icc s T \ {τ}] τ) (𝓝 (F τ x))

/-- (b) The difference quotient of the first piece:
`(t-τ)⁻¹ ∫_s^τ (H_{ν(t-r)} - H_{ν(τ-r)}) F(r)(x) dr → ν Σ_i ∫_s^τ (∂_iK_{ν(τ-r)} * ∂_iF(r))(x) dr`
(dominated convergence with the bound `C B (1 + a^(-1/2))`, and the window `|r-τ| ≤ 2|t-τ|/ν`
where the contribution is `O(√|t-τ|)`). -/
def ConvTD_Quot : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r) ∧ ∀ j : Fin 2, WB B (B0579.pd j (F r))) →
    ∀ τ ∈ Icc s T, ∀ x : Pl,
      Tendsto (fun t : ℝ => (t - τ)⁻¹ * ∫ r in s..τ,
          (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x))
        (𝓝[Icc s T \ {τ}] τ)
        (𝓝 (ν * ∑ i : Fin 2, ∫ r in s..τ, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x))

theorem convTimeDeriv_of (hI : ConvTD_Int) (hQ : ConvTD_Quot) (hC : ConvTD_Bdry) :
    ConvTimeDeriv := by
  intro ν s T hν hsT B F hF hB τ hτ x
  have hB0 : ∀ r ∈ Icc s T, WB B (F r) := fun r hr => (hB r hr).1
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hsum := (hQ ν s T hν hsT B F hF hB τ hτ x).add (hC ν s T hν hsT B F hF hB0 τ hτ x)
  rw [add_comm (ν * _) (F τ x)] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htI : t ∈ Icc s T := ht.1
  set f : ℝ → ℝ → ℝ := fun u r => heatSG (ν * (u - r)) (F r) x with hf
  have hit : ∀ u ∈ Icc s T, IntervalIntegrable (f u) volume s T :=
    fun u hu => hI ν s T hν hsT B F hF hB0 u hu x
  have hsub : ∀ a b : ℝ, a ∈ Icc s T → b ∈ Icc s T → ∀ u ∈ Icc s T,
      IntervalIntegrable (f u) volume a b := by
    intro a b ha hb u hu
    refine (hit u hu).mono_set ?_
    exact uIcc_subset_uIcc (mem_uIcc_of_le ha.1 ha.2) (mem_uIcc_of_le hb.1 hb.2)
  have hs0 : s ∈ Icc s T := ⟨le_rfl, hsT⟩
  have h1 : (∫ r in s..τ, f t r) + ∫ r in τ..t, f t r = ∫ r in s..t, f t r :=
    intervalIntegral.integral_add_adjacent_intervals (hsub s τ hs0 hτ t htI)
      (hsub τ t hτ htI t htI)
  have h2 : (∫ r in s..τ, (f t r - f τ r)) = (∫ r in s..τ, f t r) - ∫ r in s..τ, f τ r :=
    intervalIntegral.integral_sub (hsub s τ hs0 hτ t htI)
      (hsub s τ hs0 hτ τ hτ)
  simp only [slope_def_field, duhamelConv]
  show (t - τ)⁻¹ * (∫ r in s..τ, (f t r - f τ r)) + (t - τ)⁻¹ * (∫ r in τ..t, f t r) =
    ((∫ r in s..t, f t r) - ∫ r in s..τ, f τ r) / (t - τ)
  rw [h2, ← h1]
  field_simp
  ring

end CylPDE

end UnforcedLeray.Short.IIb
