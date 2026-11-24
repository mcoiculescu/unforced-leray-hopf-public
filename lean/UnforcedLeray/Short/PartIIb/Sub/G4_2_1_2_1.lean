import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2

/-!
# Part II-b, task `PartII-b:G4/2/1/2/1` (leaf `GreenSqContinuous`) and its sibling leaf 2

Source: `the November 2 reference manuscript`
lines 2347-2352.

With `G = greenInverse q`, `q = a G` (`a = sqCoeff`), `h(v) = a(v) G(√v)/v`, the substitution
`s² = v` in the formula for `G` gives, for `u = r² > 0`,
`G(√u)/u = -(1/8)[u⁻² ∫₀^u v² h(v) dv + ∫_u^∞ h(v) dv]` (`sqF h u`).  The remaining facts are
isolated as Props `GreenSqH`, `GreenSqFormula`, `SqFCalculus`, `SqFubini`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- `h(v) = a(v) · G(√v)/v`. -/
def sqH (lam : ℂ) (q : Planar.Profile) (v : ℝ) : ℂ :=
  sqCoeff lam v * (Planar.greenInverse q (Real.sqrt v) / (v : ℂ))

/-- The closed form `-(1/8)[u⁻²∫₀^u v²h + ∫_u^∞ h]` for `G(√u)/u`. -/
def sqF (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  -(1 / 8 : ℂ) * (((u : ℂ) ^ 2)⁻¹ * (∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * h v) +
    ∫ v in Ioi u, h v)

/-- **Sub 1** (SP 2347-2352): `h = sqH` is integrable on `(0,∞)` (bounded near 0 by the `O(r²)`
bound and `q = aG`; at infinity `|a(v)| ≲ (1+v)e^{-v/4}` and `G(√v)/v` is bounded by `MemXG`),
continuous on `(0,∞)` (smoothness of `q`), and bounded on `(0,1]`. -/
def GreenSqH : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    (∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖Planar.greenInverse q r‖ ≤ C * r ^ 2) →
    IntegrableOn (sqH lam q) (Ioi 0) ∧ ContinuousOn (sqH lam q) (Ioi 0) ∧
      ∃ C : ℝ, ∀ u : ℝ, 0 < u → u ≤ 1 → ‖sqH lam q u‖ ≤ C

/-- **Sub 2** (SP 2347-2352): the closed form.  From `q(s) = a(s²)G(s) = s² h(s²)`,
`∫₀^r s³ q = ½∫₀^{r²} v² h` and `∫_r^∞ s⁻¹ q = ½∫_{r²}^∞ h` (substitution `v = s²`). -/
def GreenSqFormula : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    (∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖Planar.greenInverse q r‖ ≤ C * r ^ 2) →
    ∀ u : ℝ, 0 < u → Planar.greenInverse q (Real.sqrt u) / (u : ℂ) = sqF (sqH lam q) u

/-- **Sub 3** (calculus): for `h` integrable on `(0,∞)`, continuous there and bounded on `(0,1]`,
`sqF h` is continuous on `(0,∞)` and tends to `-(1/8)∫₀^∞ h` at `0⁺`
(`|u⁻²∫₀^u v²h| ≤ Cu/3 → 0`; `u ↦ ∫_u^∞ h` is continuous and tends to `∫₀^∞ h`). -/
def SqFCalculus : Prop :=
  ∀ h : ℝ → ℂ, IntegrableOn h (Ioi 0) → ContinuousOn h (Ioi 0) →
    (∃ C : ℝ, ∀ u : ℝ, 0 < u → u ≤ 1 → ‖h u‖ ≤ C) →
    ContinuousOn (sqF h) (Ioi 0) ∧
      Tendsto (sqF h) (𝓝[>] 0) (𝓝 (-(1 / 8 : ℂ) * ∫ v in Ioi (0 : ℝ), h v))

/-- Leaf 1 from the three subs. -/
theorem greenSqContinuous_of (h1 : GreenSqH) (h2 : GreenSqFormula) (h3 : SqFCalculus) :
    GreenSqContinuous := by
  intro lam q h hO
  obtain ⟨hint, hcont, hb⟩ := h1 lam q h hO
  obtain ⟨hFc, hFt⟩ := h3 _ hint hcont hb
  refine ⟨fun u => if 0 < u then sqF (sqH lam q) u
    else -(1 / 8 : ℂ) * ∫ v in Ioi (0 : ℝ), sqH lam q v, ?_, ?_⟩
  · intro u hu
    rcases (show (0 : ℝ) ≤ u from hu).eq_or_lt with rfl | hpos
    · have h0 : ContinuousWithinAt (fun u : ℝ => if 0 < u then sqF (sqH lam q) u
          else -(1 / 8 : ℂ) * ∫ v in Ioi (0 : ℝ), sqH lam q v) (Ioi 0) 0 := by
        rw [ContinuousWithinAt]
        have : (if (0 : ℝ) < 0 then sqF (sqH lam q) 0
            else -(1 / 8 : ℂ) * ∫ v in Ioi (0 : ℝ), sqH lam q v)
            = -(1 / 8 : ℂ) * ∫ v in Ioi (0 : ℝ), sqH lam q v := by simp
        rw [this]
        refine hFt.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp [show (0 : ℝ) < x from hx]
      exact continuousWithinAt_Ioi_iff_Ici.mp h0
    · have hc : ContinuousAt (sqF (sqH lam q)) u :=
        hFc.continuousAt (Ioi_mem_nhds hpos)
      refine (hc.congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds hpos] with x hx
      simp [show (0 : ℝ) < x from hx]
  · intro u hu
    simp only [hu, ite_true]
    exact (h2 lam q h hO u hu).symm

end UnforcedLeray.Short.IIb
