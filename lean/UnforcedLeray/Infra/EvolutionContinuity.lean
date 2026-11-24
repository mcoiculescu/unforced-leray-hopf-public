import UnforcedLeray.Infra.EvolutionContinuity.Abstract
import UnforcedLeray.Infra.EvolutionContinuity.Volterra
import UnforcedLeray.Infra.EvolutionContinuity.Dichotomy

/-!
# Strong continuity of the Volterra evolution and of the dichotomy kernels

Abstract form of `paper/main.tex`, lines 292-296 ("Volterra iteration … constructs a jointly
strongly continuous evolution `E(τ,s)`, periodic in both time arguments") and of the continuity
of the kernels `E(τ,s) Π₋(s)`, `E₊(τ,s) Π₊(s)` and of the projections `Π_±(θ)`
(lines 371-428), in the form required by `UnforcedLeray.Infra.HalfLineGreen`.

Files:

* `EvolutionContinuity/Abstract.lean`: `ForwardEvolution E` (evolution law, strip bounds,
  continuity in `τ`, continuity at the diagonal uniformly in the base point) and its
  consequences: (a) `s ↦ E(τ,s) x` continuous on `(-∞, τ]` (`ForwardEvolution.continuousOn_snd`),
  (b) `(τ,s) ↦ E(τ,s) x` continuous on `{s ≤ τ}` (`ForwardEvolution.continuousOn`),
  (c) the same for `E(τ,s) Q(s) x` with `Q` strongly continuous or periodic
  (`continuousOn_comp`, `continuousOn_snd_comp`, `continuousOn_comp_periodic`), and
  `continuous_of_periodic` (continuity across the period seam);
* `EvolutionContinuity/Volterra.lean`: the Volterra evolution of compatible data with
  `S₀ 0 = 1` is a `ForwardEvolution` (`forwardEvolution_volterra`); the diagonal continuity
  comes from the short-time estimate `‖E(τ,s) - S₀(τ-s)‖ ≤ C (τ-s)^{1/2}`;
* `EvolutionContinuity/Dichotomy.lean`: for a `PeriodicSplitting` whose evolution is a
  `ForwardEvolution`, `t ↦ Π_±(t) x` is continuous on `ℝ`, `s ↦ E(τ,s) Π₋(s) x` on `(-∞, τ]`,
  `(τ,s) ↦ E₊(τ,s) Π₊(s) x` on `ℝ × ℝ`; the `X`-valued `GreenKernel` (`greenKernel`), its
  `TimeContinuous` property and the `Dichotomy` structure of `HalfLineGreen`;
* this file: the summaries `volterra_evolution_continuity` and `periodic_halfLineGreen`
  (the `X → X` half-line Green operator of a periodic splitting: formula, bound uniform in
  `τ₀`, mild equation, terminal condition), and the Volterra case `volterra_halfLineGreen`.

Not covered: the `X → Z` smoothing of the kernels (`loc:eq:past-bound`,
`loc:eq:future-bound`), hence continuity of the kernels in the `Z`-norm; the Green operator here
maps `𝒳_β` to `𝒳_β`, not to `𝒵_β`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory

namespace UnforcedLeray.Infra.EvolutionContinuity

open UnforcedLeray.Infra.PeriodicDichotomy UnforcedLeray.Infra.HalfLineGreen
open UnforcedLeray.Infra.VolterraEvolution (VolterraData)

section VolterraSummary

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X]
  [CompleteSpace X]

/-- **Strong continuity of the Volterra evolution in both arguments, summary**
(`paper/main.tex`, lines 292-296). For compatible data with `S₀ 0 = 1`:
`E(t,t) = 1`; (a) `s ↦ E(τ,s) x` is continuous on `(-∞, τ]`; (b) `(τ,s) ↦ E(τ,s) x` is
continuous on `{s ≤ τ}`; (c) `(τ,s) ↦ E(τ,s) Q(s) x` is continuous on `{s ≤ τ, s ∈ U}` for
`Q` strongly continuous on `U`, and on `{s ≤ τ}` for `Q` `P`-periodic and strongly continuous on
`[0, P]`. -/
theorem volterra_evolution_continuity {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) :
    (∀ t, D.evolution t t = 1) ∧
    (∀ τ x, ContinuousOn (fun s => D.evolution τ s x) (Iic τ)) ∧
    (∀ x, ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 x) {p : ℝ × ℝ | p.2 ≤ p.1}) ∧
    (∀ (Q : ℝ → X →L[𝕜] X) (U : Set ℝ), (∀ y, ContinuousOn (fun s => Q s y) U) → ∀ x,
      ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 (Q p.2 x))
        {p : ℝ × ℝ | p.2 ≤ p.1 ∧ p.2 ∈ U}) ∧
    (∀ (Q : ℝ → X →L[𝕜] X) (P : ℝ), 0 < P → (∀ t, Q (t + P) = Q t) →
      (∀ y, ContinuousOn (fun t => Q t y) (Icc 0 P)) → ∀ x,
      ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 (Q p.2 x)) {p : ℝ × ℝ | p.2 ≤ p.1}) :=
  ⟨evolution_self hD hS₀, continuousOn_evolution_snd hD hS₀, continuousOn_evolution_prod hD hS₀,
    fun _ _ hQ x => continuousOn_evolution_comp hD hS₀ hQ x,
    fun _ _ hP hper hc x => continuousOn_evolution_comp_periodic hD hS₀ hP hper hc x⟩

end VolterraSummary

section Green

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **The `X → X` half-line Green operator of a periodic splitting**
(`paper/main.tex`, lines 406-430, with `Z = X`). Let the evolution of `D` be a
`ForwardEvolution` and the splitting circle be `|z| = e^{βP}`. There are rates `βm < β < βp`
such that for every terminal time `τ₀` the operator `R_β : 𝒳_β → 𝒳_β` of `HalfLineGreen`
built from `K₋ = E Π₋`, `K₊ = E₊ Π₊` satisfies
`(R_β f)(τ) = ∫_{-∞}^τ E(τ,s) Π₋(s) f(s) ds - ∫_τ^{τ₀} E₊(τ,s) Π₊(s) f(s) ds`,
`‖R_β‖ ≤ C_β` (independent of `τ₀`), the mild equation
`(R_β f)(τ) = E(τ,σ) (R_β f)(σ) + ∫_σ^τ E(τ,s) f(s) ds` and `Π₊(τ₀) (R_β f)(τ₀) = 0`. -/
theorem periodic_halfLineGreen (D : PeriodicSplitting X) (hE : ForwardEvolution D.E) {β : ℝ}
    (hβ : D.r = Real.exp (β * D.P)) :
    ∃ (βm βp K : ℝ)
      (hm : ∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s)))
      (hp : ∀ s τ, τ ≤ s → ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s)))
      (hβm : βm < β) (hβp : β < βp), ∀ τ₀ : ℝ,
      (∀ (f : WeightedSpace X β τ₀) (τ : Iic τ₀),
        (greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp) hβm hβp τ₀ f τ =
          (∫ s in Iio (τ : ℝ), D.E τ s (D.piMinus s (f.extend s))) -
            ∫ s in (τ : ℝ)..τ₀, D.extEvol τ s (D.piPlus s (f.extend s))) ∧
      ‖(greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp) hβm hβp τ₀‖ ≤
        (greenKernel D hE hm hp).greenConst β ∧
      (∀ (f : WeightedSpace X β τ₀) (σ τ : Iic τ₀), (σ : ℝ) ≤ τ →
        (greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp) hβm hβp τ₀ f τ =
          D.E τ σ ((greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp)
            hβm hβp τ₀ f σ) + ∫ s in (σ : ℝ)..τ, D.E τ s (f.extend s)) ∧
      (∀ f : WeightedSpace X β τ₀,
        D.piPlus τ₀ ((greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp)
          hβm hβp τ₀ f ⟨τ₀, self_mem_Iic⟩) = 0) := by
  obtain ⟨βm, βp, K, hm, hp, hβm, hβp, -⟩ := exists_greenKernel D hE hβ
  refine ⟨βm, βp, K, hm, hp, hβm, hβp, fun τ₀ => ?_⟩
  have hK := greenKernel_timeContinuous D hE hm hp
  have h1 := (greenKernel D hE hm hp).halfLineGreen hK hβm hβp τ₀
  have h2 := fun f : WeightedSpace X β τ₀ =>
    (dichotomy D hE hm hp).halfLineGreen_mild hK hβm hβp f
  exact ⟨fun f τ => (h1.1 f τ).2.2, h1.2.1, fun f σ τ hστ => ((h2 f).1 σ τ hστ).2,
    fun f => (h2 f).2⟩

/-- **Volterra case of `periodic_halfLineGreen`**: the periodic Volterra evolution
(compatible data, `S₀ 0 = 1`, `P`-periodic coefficients) with a spectrum-free circle
`|z| = e^{βP}` for the monodromy `E(P,0)` has a time-continuous `X`-valued Green kernel
`K₋ = E Π₋`, `K₊ = E₊ Π₊` with rates `βm < β < βp`, and the corresponding `R_β` satisfies the
mild equation and the terminal condition. -/
theorem volterra_halfLineGreen {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (V : VolterraData ℂ X Y) (hV : V.Compatible) (hS₀ : V.S₀ 0 = 1) {P : ℝ} (hP : 0 < P)
    (hB : ∀ t, V.B (t + P) = V.B t) {β : ℝ}
    (hsph : sphere (0 : ℂ) (Real.exp (β * P)) ⊆ resolventSet ℂ (V.evolution P 0)) :
    let D := PeriodicSplitting.ofVolterra V hV hS₀ hP hB (Real.exp_pos (β * P)) hsph
    let hE : ForwardEvolution D.E := forwardEvolution_ofVolterra V hV hS₀ hP hB _ hsph
    ∃ (βm βp K : ℝ)
      (hm : ∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s)))
      (hp : ∀ s τ, τ ≤ s → ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s)))
      (hβm : βm < β) (hβp : β < βp), ∀ τ₀ : ℝ,
      ‖(greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp) hβm hβp τ₀‖ ≤
        (greenKernel D hE hm hp).greenConst β ∧
      (∀ (f : WeightedSpace X β τ₀) (σ τ : Iic τ₀), (σ : ℝ) ≤ τ →
        (greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp) hβm hβp τ₀ f τ =
          V.evolution τ σ ((greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp)
            hβm hβp τ₀ f σ) + ∫ s in (σ : ℝ)..τ, V.evolution τ s (f.extend s)) ∧
      (∀ f : WeightedSpace X β τ₀,
        D.piPlus τ₀ ((greenKernel D hE hm hp).greenOp (greenKernel_timeContinuous D hE hm hp)
          hβm hβp τ₀ f ⟨τ₀, self_mem_Iic⟩) = 0) := by
  intro D hE
  obtain ⟨βm, βp, K, hm, hp, hβm, hβp, h⟩ := periodic_halfLineGreen D hE (β := β) rfl
  exact ⟨βm, βp, K, hm, hp, hβm, hβp, fun τ₀ => ⟨(h τ₀).2.1, (h τ₀).2.2.1, (h τ₀).2.2.2⟩⟩

end Green

end UnforcedLeray.Infra.EvolutionContinuity
