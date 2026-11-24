import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2

/-!
# Conjugation closure of the causal energy class (for `PartIII-b:C/near/2/Exists`)

For real `μ` and `v = 0`, the complex conjugate of a causal zero-entrance energy solution (with
conjugated force and gradient) is again one: every clause of `IsCausalEnergySolution` is stable
under `z ↦ conj z` because test fields and `ν`, `μ`, `s` are real.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.IIIa

theorem integrable_conj' {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : Integrable (fun p => conj (f p)) μ :=
  Integrable.mono' hf.norm (Complex.continuous_conj.comp_aestronglyMeasurable hf.1)
    (Eventually.of_forall fun p => by simp)

theorem conj_vnorm2 (a : Fin 2 → ℂ) : vnorm2 (fun i => conj (a i)) = vnorm2 a := by
  simp [vnorm2]

theorem conj_tnorm2 (T : Fin 2 → Fin 2 → ℂ) : tnorm2 (fun i j => conj (T i j)) = tnorm2 T := by
  simp [tnorm2]

theorem conj_flatIntegrand (ν r : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    flatIntegrand ν (r : ℂ) (fun _ _ _ => 0) (fun p i j => conj (F p i j))
        (fun p i => conj (b p i)) Φ p =
      conj (flatIntegrand ν (r : ℂ) (fun _ _ _ => 0) F b Φ p) := by
  simp [flatIntegrand, map_sum, map_mul, map_sub, map_add, map_neg, map_div₀,
    Complex.conj_ofReal]

theorem conj_causal_sol {c ν r : ℝ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (h : IsCausalEnergySolution c ν (r : ℂ) (fun _ _ _ => 0) F b G) :
    IsCausalEnergySolution c ν (r : ℂ) (fun _ _ _ => 0) (fun p i j => conj (F p i j))
      (fun p i => conj (b p i)) (fun p i j => conj (G p i j)) := by
  have hm : ∀ {f : ℝ × (ℝ × ℝ) → ℂ}, Measurable f → Measurable fun p => conj (f p) :=
    fun hf => Complex.continuous_conj.measurable.comp hf
  refine ⟨fun i => hm (h.measurable i), fun i j => hm (h.gradMeasurable i j), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s₁ s₂ h1 h2
    simpa only [conj_vnorm2, conj_tnorm2] using h.energyLoc s₁ s₂ h1 h2
  · simpa only [conj_vnorm2] using h.zeroEntrance
  · intro s hs ψ hψ
    have := h.divFree s hs ψ hψ
    have e : ∀ x, conj (b (s, x) 0) * (B0579.pd 0 ψ x : ℂ) + conj (b (s, x) 1) * (B0579.pd 1 ψ x : ℂ)
        = conj (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) := by
      intro x; simp [Complex.conj_ofReal]
    simp_rw [e]
    rw [integral_conj, this, map_zero]
  · intro s hs i j
    have hw := (h.weakGrad s hs i j).2
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨a1, a2⟩ := (h.weakGrad s hs i j).1 ψ hψ
      refine ⟨?_, ?_⟩
      · show Integrable _ _
        have := integrable_conj' a1
        simpa [Complex.conj_ofReal] using this
      · show Integrable _ _
        have := integrable_conj' a2
        simpa [Complex.conj_ofReal] using this
    · have e1 : ∀ x, conj (b (s, x) i) * (B0579.pd j ψ x : ℂ) =
          conj (b (s, x) i * (B0579.pd j ψ x : ℂ)) := by
        intro x; simp [Complex.conj_ofReal]
      have e2 : ∀ x, conj (G (s, x) i j) * (ψ x : ℂ) = conj (G (s, x) i j * (ψ x : ℂ)) := by
        intro x; simp [Complex.conj_ofReal]
      simp_rw [e1, e2]
      rw [integral_conj, integral_conj, hw ψ hψ, map_neg]
  · intro Φ hΦ
    have e : flatIntegrand ν (r : ℂ) (fun _ _ _ => 0) (fun p i j => conj (F p i j))
        (fun p i => conj (b p i)) Φ =
        fun p => conj (flatIntegrand ν (r : ℂ) (fun _ _ _ => 0) F b Φ p) :=
      funext fun p => conj_flatIntegrand ν r F b Φ p
    rw [e]
    have hi : IntegrableOn (flatIntegrand ν (r : ℂ) (fun _ _ _ => 0) F b Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := h.integrable Φ hΦ
    exact integrable_conj' hi
  · intro Φ hΦ
    have e : flatIntegrand ν (r : ℂ) (fun _ _ _ => 0) (fun p i j => conj (F p i j))
        (fun p i => conj (b p i)) Φ =
        fun p => conj (flatIntegrand ν (r : ℂ) (fun _ _ _ => 0) F b Φ p) :=
      funext fun p => conj_flatIntegrand ν r F b Φ p
    rw [e, integral_conj, h.weak Φ hΦ, map_zero]

end UnforcedLeray.Short.PartIIIb.NearInst
