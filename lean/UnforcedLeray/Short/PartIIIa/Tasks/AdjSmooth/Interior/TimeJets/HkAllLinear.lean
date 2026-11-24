import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/6/4`: linear combinations of `C(I; H^∞_{-m,c})` families (`AdjHkAllLinear`)

Source: `the November 2 reference manuscript` lines 3060-3061 (the weighted energies
of every order are linear in the adjoint).  Zero family: every cell jet field is `0`.  Combination
`α f + β g` with fields `α D + β E`: the cell-jet fields are linear (`IsCellJet`, the weak derivative
`HasWeakCellDerivC` is linear by `integral_add`), and the `X_{-m,c}`-continuity follows from the
triangle inequality for `eLpNorm` and the scalar bound `eLpNorm (c • f) = ‖c‖ₑ eLpNorm f`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The `L²` norm of a linear combination (triangle inequality and scalar multiplication). -/
theorem hk_eLp_lin_le {μ : Measure (ℝ × ℝ)} (α β : ℂ) (u v : ℝ × ℝ → ℂ)
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

/-- The integral of a linear combination of integrands. -/
theorem hk_int_lin {μ : Measure (ℝ × ℝ)} (α β : ℂ) (φ φ' ψ : ℝ × ℝ → ℂ)
    (h1 : Integrable (fun x => φ x * ψ x) μ) (h2 : Integrable (fun x => φ' x * ψ x) μ) :
    ∫ x, (α * φ x + β * φ' x) * ψ x ∂μ = α * ∫ x, φ x * ψ x ∂μ + β * ∫ x, φ' x * ψ x ∂μ := by
  have e : (fun x => (α * φ x + β * φ' x) * ψ x) =
      fun x => α * (φ x * ψ x) + β * (φ' x * ψ x) := by
    funext x
    ring
  rw [e, integral_add (h1.const_mul α) (h2.const_mul β), integral_const_mul, integral_const_mul]

/-- `HasWeakCellDerivC` is linear in the pair (field, derivative). -/
theorem hk_hwcd_lin {c : ℝ} {j : Fin 2} {φ φ' g g' : ℝ × ℝ → ℂ} (α β : ℂ)
    (h1 : HasWeakCellDerivC c j φ g) (h2 : HasWeakCellDerivC c j φ' g') :
    HasWeakCellDerivC c j (fun x => α * φ x + β * φ' x) (fun x => α * g x + β * g' x) := by
  unfold HasWeakCellDerivC at h1 h2 ⊢
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · have e : (fun x => (α * φ x + β * φ' x) * (B0579.pd j ψ x : ℂ)) =
        fun x => α * (φ x * (B0579.pd j ψ x : ℂ)) + β * (φ' x * (B0579.pd j ψ x : ℂ)) := by
      funext x
      ring
    show IntegrableOn (fun x => (α * φ x + β * φ' x) * (B0579.pd j ψ x : ℂ)) (B0579.cell c)
    rw [e]
    exact (Integrable.const_mul (h1a ψ hψ).1 α).add (Integrable.const_mul (h2a ψ hψ).1 β)
  · have e : (fun x => (α * g x + β * g' x) * (ψ x : ℂ)) =
        fun x => α * (g x * (ψ x : ℂ)) + β * (g' x * (ψ x : ℂ)) := by
      funext x
      ring
    show IntegrableOn (fun x => (α * g x + β * g' x) * (ψ x : ℂ)) (B0579.cell c)
    rw [e]
    exact (Integrable.const_mul (h1a ψ hψ).2 α).add (Integrable.const_mul (h2a ψ hψ).2 β)
  · show ∫ x in B0579.cell c, (α * φ x + β * φ' x) * (B0579.pd j ψ x : ℂ) =
      -∫ x in B0579.cell c, (α * g x + β * g' x) * (ψ x : ℂ)
    rw [hk_int_lin α β φ φ' (fun x => (B0579.pd j ψ x : ℂ)) (h1a ψ hψ).1 (h2a ψ hψ).1,
      hk_int_lin α β g g' (fun x => (ψ x : ℂ)) (h1a ψ hψ).2 (h2a ψ hψ).2,
      h1b ψ hψ, h2b ψ hψ]
    ring

/-- Linear combinations of cell jets of a fixed order are cell jets (fields `α D + β E`). -/
theorem hk_isCellJet_lin {c m : ℝ} {k : ℕ} {f g : ℝ × ℝ → ℂ} {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (α β : ℂ) (h1 : IsCellJet c m k f D) (h2 : IsCellJet c m k g E) :
    IsCellJet c m k (fun x => α * f x + β * g x) (fun w x => α * D w x + β * E w x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x
    show α * D [] x + β * E [] x = α * f x + β * g x
    rw [h1.base, h2.base]
  · intro w hw x
    show α * D w (x.1 + c, x.2) + β * E w (x.1 + c, x.2) = α * D w x + β * E w x
    rw [h1.periodic w hw x, h2.periodic w hw x]
  · intro w hw
    exact ((h1.memX w hw).const_mul α).add ((h2.memX w hw).const_mul β)
  · intro j w hw
    exact hk_hwcd_lin α β (h1.deriv j w hw) (h2.deriv j w hw)

/-- The zero family is a cell jet of every order. -/
theorem hk_isCellJet_zero (c m : ℝ) (k : ℕ) :
    IsCellJet c m k (fun _ => (0 : ℂ)) (fun _ _ => (0 : ℂ)) := by
  refine ⟨rfl, fun _ _ _ => rfl, fun _ _ => MemLp.zero', fun j w _ => ?_⟩
  unfold HasWeakCellDerivC
  refine ⟨fun ψ _ => ⟨?_, ?_⟩, fun ψ _ => ?_⟩ <;> simp

/-- **(4) Linear combinations of `C(I; H^∞_{-m,c})` families, and the zero family.** -/
theorem adjHkAllLinear : AdjHkAllLinear := by
  unfold AdjHkAllLinear
  intro c m I
  refine ⟨?_, ?_⟩
  · unfold AdjHkAll
    refine ⟨fun r _ k => hk_isCellJet_zero c m k, fun w r _ => ?_⟩
    have h0 : xNorm c (-m) ((fun _ : ℝ × ℝ => (0 : ℂ)) - (fun _ : ℝ × ℝ => (0 : ℂ))) = 0 := by
      rw [sub_self]
      unfold xNorm
      exact eLpNorm_zero
    exact Tendsto.congr (fun _ => h0.symm) tendsto_const_nhds
  · intro f g D E α β hf hg
    unfold AdjHkAll at hf hg ⊢
    obtain ⟨hf1, hf2⟩ := hf
    obtain ⟨hg1, hg2⟩ := hg
    refine ⟨fun r hr k => hk_isCellJet_lin α β (hf1 r hr k) (hg1 r hr k), fun w r hr => ?_⟩
    have hbd : ∀ᶠ r' in 𝓝[I] r,
        xNorm c (-m) ((fun x => α * D r' w x + β * E r' w x) -
            (fun x => α * D r w x + β * E r w x)) ≤
          ‖α‖ₑ * xNorm c (-m) (D r' w - D r w) + ‖β‖ₑ * xNorm c (-m) (E r' w - E r w) := by
      filter_upwards [self_mem_nhdsWithin] with r' hr'
      have m1 : MemLp (D r' w) 2 (B0579.cellMeasure c (-m)) :=
        (hf1 r' hr' w.length).memX w le_rfl
      have m0 : MemLp (D r w) 2 (B0579.cellMeasure c (-m)) :=
        (hf1 r hr w.length).memX w le_rfl
      have n1 : MemLp (E r' w) 2 (B0579.cellMeasure c (-m)) :=
        (hg1 r' hr' w.length).memX w le_rfl
      have n0 : MemLp (E r w) 2 (B0579.cellMeasure c (-m)) :=
        (hg1 r hr w.length).memX w le_rfl
      have e : (fun x => α * D r' w x + β * E r' w x) -
          (fun x => α * D r w x + β * E r w x) =
          fun x => α * (D r' w - D r w) x + β * (E r' w - E r w) x := by
        funext x
        simp only [Pi.sub_apply]
        ring
      rw [e]
      exact hk_eLp_lin_le (μ := B0579.cellMeasure c (-m)) α β (D r' w - D r w)
        (E r' w - E r w) (m1.sub m0) (n1.sub n0)
    have hT : Tendsto (fun r' => ‖α‖ₑ * xNorm c (-m) (D r' w - D r w) +
        ‖β‖ₑ * xNorm c (-m) (E r' w - E r w)) (𝓝[I] r) (𝓝 0) := by
      have h1 := ENNReal.Tendsto.const_mul (hf2 w r hr) (Or.inr (enorm_ne_top (x := α)))
      have h2 := ENNReal.Tendsto.const_mul (hg2 w r hr) (Or.inr (enorm_ne_top (x := β)))
      have := h1.add h2
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
      (Eventually.of_forall fun _ => zero_le) hbd

end UnforcedLeray.Short.IIIa
