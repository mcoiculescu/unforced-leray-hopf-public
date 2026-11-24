import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2_1

/-!
# Part II-b, task `PartII-b:G4/2/1/2/2` (leaf `GreenSqVolterra`)

Source: `the November 2 reference manuscript`
lines 2347-2352.  Route avoiding second derivatives: with `g(u) = sqF h u` and `c = g 0 =
-(1/8)∫₀^∞ h`, Fubini gives `∫₀^u ¼∫₀¹ t² h(vt) dt dv = (1/8)(∫₀^u h - u⁻²∫₀^u v²h)`, which is
`g u - c`.  Uses `GreenSqH`, `GreenSqFormula`, `SqFCalculus` of `Sub.G4_2_1_2_1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- **Sub 4** (Fubini): for `h` continuous on `[0,∞)` and `u > 0`,
`∫₀^u ¼∫₀¹ t² h(vt) dt dv = (1/8)(∫₀^u h - u⁻² ∫₀^u v² h)`.
(Substitute `w = vt`, swap: `∫₀^u w²h(w) ∫_w^u v⁻³ dv dw`, and `∫_w^u v⁻³ = (w⁻²-u⁻²)/2`.) -/
def SqFubini : Prop :=
  ∀ h : ℝ → ℂ, ContinuousOn h (Ici 0) → ∀ u : ℝ, 0 < u →
    (∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * h (v * t)) =
      (1 / 8 : ℂ) * ((∫ v in (0 : ℝ)..u, h v) -
        ((u : ℂ) ^ 2)⁻¹ * ∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * h v)

/-- `sqCoeff` is continuous when `Re λ > 0` (the denominator has real part `Re λ`). -/
theorem sqCoeff_continuous {lam : ℂ} (hl : 0 < lam.re) : Continuous (sqCoeff lam) := by
  unfold sqCoeff
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro u h0
  have := congrArg Complex.re h0
  simp [-Complex.ofReal_exp] at this
  linarith

/-- Leaf 2 from the subs. -/
theorem greenSqVolterra_of (h1 : GreenSqH) (h2 : GreenSqFormula) (h3 : SqFCalculus)
    (h4 : SqFubini) : GreenSqVolterra := by
  intro lam q h hO g hgc hg
  obtain ⟨hint, hcont, hb⟩ := h1 lam q h hO
  obtain ⟨hFc, hFt⟩ := h3 _ hint hcont hb
  have hpcont : ContinuousOn (fun w => sqCoeff lam w * g w) (Ici 0) :=
    (sqCoeff_continuous h.re_pos).continuousOn.mul hgc
  have hpeq : ∀ w : ℝ, 0 < w → sqCoeff lam w * g w = sqH lam q w := by
    intro w hw
    simp [sqH, hg w hw]
  have hgF : ∀ w : ℝ, 0 < w → g w = sqF (sqH lam q) w := fun w hw =>
    (hg w hw).trans (h2 lam q h hO w hw)
  have hg0 : g 0 = -(1 / 8 : ℂ) * ∫ v in Ioi (0 : ℝ), sqH lam q v := by
    have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
      (hgc 0 (Set.mem_Ici.mpr le_rfl)).mono_left
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have ht2 : Tendsto g (𝓝[>] 0) (𝓝 (-(1 / 8 : ℂ) * ∫ v in Ioi (0 : ℝ), sqH lam q v)) := by
      refine hFt.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hgF x hx).symm
    exact tendsto_nhds_unique ht ht2
  refine ⟨g 0, ?_⟩
  intro u hu
  rcases hu.eq_or_lt with rfl | hpos
  · simp [sqVolterra]
  · unfold sqVolterra
    rw [h4 _ hpcont u hpos]
    have e1 : ∫ v in (0 : ℝ)..u, sqCoeff lam v * g v = ∫ v in (0 : ℝ)..u, sqH lam q v := by
      rw [intervalIntegral.integral_of_le hpos.le, intervalIntegral.integral_of_le hpos.le]
      exact setIntegral_congr_fun measurableSet_Ioc (fun w hw => hpeq w hw.1)
    have e2 : ∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * (sqCoeff lam v * g v) =
        ∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * sqH lam q v := by
      rw [intervalIntegral.integral_of_le hpos.le, intervalIntegral.integral_of_le hpos.le]
      exact setIntegral_congr_fun measurableSet_Ioc (fun w hw => by rw [hpeq w hw.1])
    have hsplit : ∫ v in Ioi (0 : ℝ), sqH lam q v =
        (∫ v in (0 : ℝ)..u, sqH lam q v) + ∫ v in Ioi u, sqH lam q v := by
      rw [intervalIntegral.integral_of_le hpos.le, ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi (hint.mono_set (fun x hx => hx.1)) (hint.mono_set (fun x hx =>
          lt_trans hpos hx)), Set.Ioc_union_Ioi_eq_Ioi hpos.le]
    rw [e1, e2, hgF u hpos, hg0, hsplit]
    unfold sqF
    ring

end UnforcedLeray.Short.IIb
