import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/6/5`: linear combinations of `X_{-m,c}`-derivatives (`HasXDerivOnLinear`)

Source: `the November 2 reference manuscript` line 3060 (the age derivative of a
weak adjoint in `X_{-m,c}`).  The difference quotient of `α f + β g` is `α` times the difference
quotient of `f` plus `β` times that of `g`, pointwise by `ring`; the `X_{-m,c}`-norm is then bounded by
the triangle inequality and the scalar bound for `eLpNorm`, and the two pieces tend to zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The `L²` norm of a linear combination (triangle inequality and scalar multiplication). -/
theorem hx_eLp_lin_le {μ : Measure (ℝ × ℝ)} (α β : ℂ) (u v : ℝ × ℝ → ℂ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    eLpNorm (fun x => α * u x + β * v x) 2 μ ≤ ‖α‖ₑ * eLpNorm u 2 μ + ‖β‖ₑ * eLpNorm v 2 μ := by
  have e1 : eLpNorm (fun x => α * u x) 2 μ = ‖α‖ₑ * eLpNorm u 2 μ := by
    have := eLpNorm_const_smul α u 2 μ
    simpa [Pi.smul_def, smul_eq_mul] using this
  have e2 : eLpNorm (fun x => β * v x) 2 μ = ‖β‖ₑ * eLpNorm v 2 μ := by
    have := eLpNorm_const_smul β v 2 μ
    simpa [Pi.smul_def, smul_eq_mul] using this
  calc eLpNorm (fun x => α * u x + β * v x) 2 μ
      ≤ eLpNorm (fun x => α * u x) 2 μ + eLpNorm (fun x => β * v x) 2 μ :=
        eLpNorm_add_le (hu.const_mul α).1 (hv.const_mul β).1 one_le_two
    _ = ‖α‖ₑ * eLpNorm u 2 μ + ‖β‖ₑ * eLpNorm v 2 μ := by rw [e1, e2]

/-- **(5) Linear combinations of `X_{-m,c}`-derivatives** (all slices in `X_{-m,c}`), and the zero
family. -/
theorem hasXDerivOnLinear : HasXDerivOnLinear := by
  unfold HasXDerivOnLinear
  intro c m I
  refine ⟨?_, ?_⟩
  · unfold HasXDerivOn
    intro r _hr
    refine Tendsto.congr (fun r' => ?_) tendsto_const_nhds
    simp [xNorm]
  · intro f f' g g' α β hmem hf hg
    unfold HasXDerivOn at hf hg ⊢
    intro r hr
    have hbd : ∀ᶠ r' in 𝓝[I \ {r}] r,
        xNorm c (-m) (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) *
            ((α * f r' x + β * g r' x) - (α * f r x + β * g r x)) -
              (α * f' r x + β * g' r x)) ≤
          ‖α‖ₑ * xNorm c (-m) (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) +
            ‖β‖ₑ * xNorm c (-m) (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (g r' x - g r x) - g' r x) := by
      filter_upwards [eventually_mem_nhdsWithin] with r' hr'
      have hr'I : r' ∈ I := hr'.1
      have m1 : MemLp (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) 2
          (B0579.cellMeasure c (-m)) :=
        (((hmem r' hr'I).1.sub (hmem r hr).1).const_mul _).sub (hmem r hr).2.1
      have n1 : MemLp (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (g r' x - g r x) - g' r x) 2
          (B0579.cellMeasure c (-m)) :=
        (((hmem r' hr'I).2.2.1.sub (hmem r hr).2.2.1).const_mul _).sub (hmem r hr).2.2.2
      have e : (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) *
            ((α * f r' x + β * g r' x) - (α * f r x + β * g r x)) -
              (α * f' r x + β * g' r x)) =
          fun x => α * ((((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) +
            β * ((((r' - r)⁻¹ : ℝ) : ℂ) * (g r' x - g r x) - g' r x) := by
        funext x
        ring
      rw [e]
      exact hx_eLp_lin_le (μ := B0579.cellMeasure c (-m)) α β _ _ m1 n1
    have hT : Tendsto (fun r' => ‖α‖ₑ *
          xNorm c (-m) (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) +
        ‖β‖ₑ * xNorm c (-m) (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (g r' x - g r x) - g' r x))
        (𝓝[I \ {r}] r) (𝓝 0) := by
      have h1 := ENNReal.Tendsto.const_mul (hf r hr) (Or.inr (enorm_ne_top (x := α)))
      have h2 := ENNReal.Tendsto.const_mul (hg r hr) (Or.inr (enorm_ne_top (x := β)))
      have := h1.add h2
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
      (Eventually.of_forall fun _ => zero_le) hbd

end UnforcedLeray.Short.IIIa
