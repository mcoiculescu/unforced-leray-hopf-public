import UnforcedLeray.Infra.EvolutionContinuity.Volterra
import UnforcedLeray.Infra.PeriodicDichotomy
import UnforcedLeray.Infra.HalfLineGreen

/-!
# Continuity of the dichotomy projections and of the Green kernels

`paper/main.tex`, lines 371-428. Let `D : PeriodicSplitting X` (`PeriodicDichotomy`) whose
evolution `E = D.E` is a `ForwardEvolution` (for the Volterra evolution:
`forwardEvolution_ofVolterra`). Recall `Π₊(θ) = F_θ G_θ = E(θ,0) S E(P,θ)` on `[0, P]`
(`S = ℳ₊⁻¹ P₊`, extended by `0`), extended `P`-periodically, `Π₋ = 1 - Π₊`, and the exterior
evolution `E₊(τ,s) = F_θ ℳ₊^{k-l} G_φ`.

Results:

* `continuousOn_piPlusPhase_apply`: `θ ↦ Π₊(θ) x` is continuous on `[0, P]`
  (`θ ↦ E(P,θ) y` by continuity in the initial time, then `θ ↦ E(θ,0)` applied to it);
* `continuous_piPlus_apply`, `continuous_piMinus_apply`: `t ↦ Π_±(t) x` is continuous on `ℝ`,
  across the period seam, by `Π₊(0) = Π₊(P) = P₊` and `continuous_of_periodic`;
* past kernel: `continuousOn_E_piMinus` (`(τ,s) ↦ E(τ,s) Π₋(s) x` on `{s ≤ τ}`) and
  `continuousOn_E_piMinus_snd` (`s ↦ E(τ,s) Π₋(s) x` on `(-∞, τ]`);
* future kernel: `extEvol_apply_eq` (`E₊(τ,s) = E(τ,σ) E₊(σ,σ') E(σ',s) Π₊(s)` for
  `σ ≤ τ`, `s ≤ σ'`), `continuous_extEvol_apply` (`(τ,s) ↦ E₊(τ,s) x` is continuous on
  `ℝ × ℝ`), `continuous_extEvol_piPlus_apply`, `continuousOn_extEvol_piPlus_snd`
  (`s ↦ E₊(τ,s) Π₊(s) x` on `[τ, ∞)`);
* the Green kernel of `HalfLineGreen` at the level of `X` (`Z = X`, `ι = id`):
  `greenKernel` (`K₋(τ,s) = E(τ,s) Π₋(s)`, `K₊(τ,s) = E₊(τ,s) Π₊(s)`, bounds from given
  dichotomy rates), `greenKernel_timeContinuous` (`GreenKernel.TimeContinuous`), `dichotomy`
  (`HalfLineGreen.Dichotomy`), `exists_greenKernel` (rates from
  `PeriodicSplitting.periodic_dichotomy_rates`), and the Volterra case
  `exists_greenKernel_volterra`.

The `X → Z` smoothing of the kernels (`loc:eq:past-bound`, `loc:eq:future-bound`) is not part of
this file: the kernels here are `X → X`, which is the case `Z = X` of `HalfLineGreen`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace UnforcedLeray.Infra.EvolutionContinuity

open UnforcedLeray.Infra.PeriodicDichotomy UnforcedLeray.Infra.HalfLineGreen
open UnforcedLeray.Infra.VolterraEvolution (continuousOn_clm_apply VolterraData)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (D : PeriodicSplitting X)

/-! ### The projections -/

omit [CompleteSpace X] in
/-- `θ ↦ F_θ v = E(θ,0) v` is continuous on `[0, ∞)`. -/
theorem continuousOn_F_apply (hE : ForwardEvolution D.E) (v : D.exterior) :
    ContinuousOn (fun θ => D.F θ v) (Ici 0) :=
  hE.continuousOn_fst 0 v

/-- `θ ↦ G_θ x = ℳ₊⁻¹ P₊ E(P,θ) x` is continuous on `(-∞, P]`. -/
theorem continuousOn_G_apply (hE : ForwardEvolution D.E) (x : X) :
    ContinuousOn (fun θ => D.G θ x) (Iic D.P) :=
  (D.monodromyPlusInv.comp D.toExterior).continuous.comp_continuousOn
    (hE.continuousOn_snd D.P x)

/-- `θ ↦ Π₊(θ) x = E(θ,0) S E(P,θ) x` is continuous on `[0, P]`. -/
theorem continuousOn_piPlusPhase_apply (hE : ForwardEvolution D.E) (x : X) :
    ContinuousOn (fun θ => D.piPlusPhase θ x) (Icc 0 D.P) := by
  have h1 : ContinuousOn (fun θ => D.outerInv (D.E D.P θ x)) (Icc 0 D.P) :=
    (D.outerInv.continuous.comp_continuousOn (hE.continuousOn_snd D.P x)).mono
      Icc_subset_Iic_self
  have h2 : ContinuousOn (fun θ => D.E θ 0 (D.outerInv (D.E D.P θ x))) (Icc 0 D.P) := by
    refine continuousOn_clm_apply (K := fun θ => D.E θ 0)
      (fun e => (hE.continuousOn_fst 0 e).mono Icc_subset_Ici_self) (fun θ₀ _ => ?_) h1
    obtain ⟨C, hC⟩ := hE.bounded D.P
    refine ⟨C, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact hC 0 θ hθ.1 (by linarith [hθ.2])
  refine h2.congr (fun θ _ => ?_)
  rw [D.piPlusPhase_eq]
  rfl

/-- `Π₊(θ)` agrees with the phase projection on the closed period `[0, P]` (at `θ = P` by
`Π₊(0) = Π₊(P) = P₊`). -/
theorem piPlus_eq_piPlusPhase_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Icc 0 D.P) :
    D.piPlus θ = D.piPlusPhase θ := by
  rcases hθ.2.lt_or_eq with h | h
  · exact D.piPlus_of_mem ⟨hθ.1, h⟩
  · rw [h, D.piPlus_period, D.piPlusPhase_period]

/-- **Strong continuity of `Π₊`** on `ℝ`, across the period seam. -/
theorem continuous_piPlus_apply (hE : ForwardEvolution D.E) (x : X) :
    Continuous (fun t => D.piPlus t x) :=
  continuous_of_periodic D.P_pos (fun t => by rw [D.piPlus_add_period])
    ((continuousOn_piPlusPhase_apply D hE x).congr
      (fun θ hθ => by rw [piPlus_eq_piPlusPhase_of_mem_Icc D hθ]))

/-- **Strong continuity of `Π₋ = 1 - Π₊`** on `ℝ`. -/
theorem continuous_piMinus_apply (hE : ForwardEvolution D.E) (x : X) :
    Continuous (fun t => D.piMinus t x) := by
  have h : (fun t => D.piMinus t x) = fun t => x - D.piPlus t x := by
    funext t
    rw [PeriodicSplitting.piMinus, sub_apply, one_apply_eq_self]
  rw [h]
  exact continuous_const.sub (continuous_piPlus_apply D hE x)

/-! ### The past kernel `E(τ,s) Π₋(s)` -/

/-- **Past kernel, joint form.** `(τ,s) ↦ E(τ,s) Π₋(s) x` is continuous on `{s ≤ τ}`. -/
theorem continuousOn_E_piMinus (hE : ForwardEvolution D.E) (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => D.E p.1 p.2 (D.piMinus p.2 x)) {p : ℝ × ℝ | p.2 ≤ p.1} :=
  hE.continuousOn_comp_univ (continuous_piMinus_apply D hE) x

/-- **Past kernel.** `s ↦ E(τ,s) Π₋(s) x` is continuous on `(-∞, τ]`. -/
theorem continuousOn_E_piMinus_snd (hE : ForwardEvolution D.E) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => D.E τ s (D.piMinus s x)) (Iic τ) :=
  (continuousOn_E_piMinus D hE x).comp (continuousOn_const.prodMk continuousOn_id)
    (fun _ hs => hs)

/-- `(τ,s) ↦ E(τ,s) Π₊(s) x` is continuous on `{s ≤ τ}`. -/
theorem continuousOn_E_piPlus (hE : ForwardEvolution D.E) (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => D.E p.1 p.2 (D.piPlus p.2 x)) {p : ℝ × ℝ | p.2 ≤ p.1} :=
  hE.continuousOn_comp_univ (continuous_piPlus_apply D hE) x

/-! ### The future kernel `E₊(τ,s) Π₊(s)` -/

/-- Factorization of the exterior evolution through two fixed times:
`E₊(τ,s) x = E(τ,σ) E₊(σ,σ') E(σ',s) Π₊(s) x` for `σ ≤ τ` and `s ≤ σ'`. -/
theorem extEvol_apply_eq {σ σ' τ s : ℝ} (hστ : σ ≤ τ) (hsσ' : s ≤ σ') (x : X) :
    D.extEvol τ s x = D.E τ σ (D.extEvol σ σ' (D.E σ' s (D.piPlus s x))) := by
  have h1 : D.extEvol τ s = D.E τ σ * (D.extEvol σ σ' * (D.E σ' s * D.piPlus s)) := by
    rw [D.E_mul_piPlus_eq_extEvol hsσ', D.extEvol_mul_extEvol, D.E_mul_extEvol hστ]
  rw [h1]
  rfl

/-- **Future kernel, joint form.** `(τ,s) ↦ E₊(τ,s) x` is continuous on `ℝ × ℝ`. -/
theorem continuous_extEvol_apply (hE : ForwardEvolution D.E) (x : X) :
    Continuous (fun p : ℝ × ℝ => D.extEvol p.1 p.2 x) := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨τ₀, s₀⟩ := p₀
  set σ := min τ₀ s₀ - 1 with hσdef
  set σ' := max τ₀ s₀ + 1 with hσ'def
  have hσ : σ < τ₀ := by have := min_le_left τ₀ s₀; linarith
  have hσ' : s₀ < σ' := by have := le_max_right τ₀ s₀; linarith
  have hWn : Ici σ ×ˢ Iic σ' ∈ 𝓝 (τ₀, s₀) := prod_mem_nhds (Ici_mem_nhds hσ) (Iic_mem_nhds hσ')
  -- the initial-time factor `s ↦ E₊(σ,σ') E(σ',s) Π₊(s) x`
  have hv : ContinuousOn (fun s => D.extEvol σ σ' (D.E σ' s (D.piPlus s x))) (Iic σ') := by
    have h := hE.continuousOn_snd_comp (U := univ)
      (fun y => (continuous_piPlus_apply D hE y).continuousOn) σ' x
    rw [inter_univ] at h
    exact (D.extEvol σ σ').continuous.comp_continuousOn h
  have hg : ContinuousWithinAt
      (fun p : ℝ × ℝ => D.E p.1 σ (D.extEvol σ σ' (D.E σ' p.2 (D.piPlus p.2 x))))
      (Ici σ ×ˢ Iic σ') (τ₀, s₀) := by
    refine continuousWithinAt_clm_apply (K := fun p : ℝ × ℝ => D.E p.1 σ) ?_ ?_ ?_
    · intro e
      have hfst : ContinuousWithinAt (Prod.fst : ℝ × ℝ → ℝ) (Ici σ ×ˢ Iic σ') (τ₀, s₀) :=
        continuous_fst.continuousWithinAt
      exact ((hE.continuousOn_fst σ e) τ₀ hσ.le).comp hfst
        (fun p (hp : p ∈ Ici σ ×ˢ Iic σ') => hp.1)
    · obtain ⟨C, hC⟩ := hE.eventually_norm_fst_le σ τ₀
      refine ⟨C, ?_⟩
      have h1 : ∀ᶠ p in 𝓝 (τ₀, s₀), σ ≤ (p : ℝ × ℝ).1 → ‖D.E p.1 σ‖ ≤ C :=
        (continuous_fst.tendsto (τ₀, s₀)).eventually hC
      filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with p hp hp'
      exact hp hp'.1
    · have hsnd : ContinuousWithinAt (Prod.snd : ℝ × ℝ → ℝ) (Ici σ ×ˢ Iic σ') (τ₀, s₀) :=
        continuous_snd.continuousWithinAt
      have h3 : ContinuousWithinAt
          ((fun s => D.extEvol σ σ' (D.E σ' s (D.piPlus s x))) ∘ Prod.snd)
          (Ici σ ×ˢ Iic σ') (τ₀, s₀) :=
        (hv s₀ hσ'.le).comp hsnd (fun p (hp : p ∈ Ici σ ×ˢ Iic σ') => hp.2)
      exact h3
  refine (hg.continuousAt hWn).congr ?_
  filter_upwards [hWn] with p hp
  exact (extEvol_apply_eq D hp.1 hp.2 x).symm

/-- `E₊(τ,s) Π₊(s) x = E₊(τ,s) x`. -/
theorem extEvol_piPlus_apply (τ s : ℝ) (x : X) :
    D.extEvol τ s (D.piPlus s x) = D.extEvol τ s x := by
  show (D.extEvol τ s * D.piPlus s) x = _
  rw [D.extEvol_mul_piPlus]

/-- **Future kernel, joint form.** `(τ,s) ↦ E₊(τ,s) Π₊(s) x` is continuous on `ℝ × ℝ`. -/
theorem continuous_extEvol_piPlus_apply (hE : ForwardEvolution D.E) (x : X) :
    Continuous (fun p : ℝ × ℝ => D.extEvol p.1 p.2 (D.piPlus p.2 x)) := by
  simp only [extEvol_piPlus_apply]
  exact continuous_extEvol_apply D hE x

/-- **Future kernel.** `s ↦ E₊(τ,s) Π₊(s) x` is continuous on `[τ, ∞)` (indeed on `ℝ`). -/
theorem continuousOn_extEvol_piPlus_snd (hE : ForwardEvolution D.E) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => D.extEvol τ s (D.piPlus s x)) (Ici τ) :=
  ((continuous_extEvol_piPlus_apply D hE x).comp
    (continuous_const.prodMk continuous_id)).continuousOn

/-! ### The Green kernel of `HalfLineGreen` (case `Z = X`) -/

/-- `K ≥ 0` from a dichotomy rate bound at `τ = s`. -/
theorem nonneg_of_rate {K βm : ℝ}
    (hm : ∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s))) : 0 ≤ K := by
  have h := hm 0 0 le_rfl
  rw [sub_self, mul_zero, Real.exp_zero, mul_one] at h
  exact (norm_nonneg _).trans h

/-- The `X`-valued Green kernel of a periodic splitting with dichotomy rates `βm`, `βp`:
`K₋(τ,s) = E(τ,s) Π₋(s)`, `K₊(τ,s) = E₊(τ,s) Π₊(s)`. -/
def greenKernel (hE : ForwardEvolution D.E) {βm βp K : ℝ}
    (hm : ∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s)))
    (hp : ∀ s τ, τ ≤ s → ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s))) :
    GreenKernel ℂ X X where
  Km τ s := D.E τ s * D.piMinus s
  Kp τ s := D.extEvol τ s * D.piPlus s
  C := K
  βm := βm
  βp := βp
  norm_Km_le τ s hs := by
    refine (hm s τ hs.le).trans ?_
    have hK : 0 ≤ K := nonneg_of_rate D hm
    have h1 : (1 : ℝ) ≤ 1 + (τ - s) ^ (-(1 / 2 : ℝ)) :=
      le_add_of_nonneg_right (Real.rpow_nonneg (sub_pos.2 hs).le _)
    have h2 : K ≤ K * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) := le_mul_of_one_le_right hK h1
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  norm_Kp_le τ s hs := hp s τ hs
  continuousOn_Km τ x :=
    (continuousOn_E_piMinus_snd D hE τ x).mono Iio_subset_Iic_self
  continuousOn_Kp τ x := continuousOn_extEvol_piPlus_snd D hE τ x

section GreenKernel

variable (hE : ForwardEvolution D.E) {βm βp K : ℝ}
  (hm : ∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s)))
  (hp : ∀ s τ, τ ≤ s → ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s)))

@[simp] theorem greenKernel_Km (τ s : ℝ) :
    (greenKernel D hE hm hp).Km τ s = D.E τ s * D.piMinus s := rfl

@[simp] theorem greenKernel_Kp (τ s : ℝ) :
    (greenKernel D hE hm hp).Kp τ s = D.extEvol τ s * D.piPlus s := rfl

@[simp] theorem greenKernel_βm : (greenKernel D hE hm hp).βm = βm := rfl

@[simp] theorem greenKernel_βp : (greenKernel D hE hm hp).βp = βp := rfl

/-- **Time continuity of the kernels** in the form required by `HalfLineGreen`
(`GreenKernel.TimeContinuous`, via `timeContinuous_of_jointly`). -/
theorem greenKernel_timeContinuous : (greenKernel D hE hm hp).TimeContinuous :=
  (greenKernel D hE hm hp).timeContinuous_of_jointly
    (fun x => (continuousOn_E_piMinus D hE x).mono
      (fun p (hp : p.2 < p.1) => show p.2 ≤ p.1 from hp.le))
    (fun x => (continuous_extEvol_piPlus_apply D hE x).continuousOn)

/-- The algebraic dichotomy hypotheses of `HalfLineGreen` (`ι = id`, `E`, `E₊`, `Π₊`, `Π₋`). -/
def dichotomy : Dichotomy (greenKernel D hE hm hp) where
  ι := ContinuousLinearMap.id ℂ X
  E := D.E
  Ep := D.extEvol
  Pp := D.piPlus
  Pm := D.piMinus
  Km_eq _ _ _ := rfl
  Kp_eq _ _ _ := rfl
  E_comp τ r s hsr hrτ := by
    rw [← ContinuousLinearMap.mul_def]
    exact D.E_comp s r τ hsr hrτ
  E_comp_Ep τ r s hrτ := by
    simp only [← ContinuousLinearMap.mul_def]
    exact D.E_mul_extEvol_mul_piPlus hrτ s
  Ep_eq τ s hs := by
    simp only [← ContinuousLinearMap.mul_def]
    exact (D.E_mul_piPlus_eq_extEvol_mul_piPlus hs).symm
  Pp_add_Pm s := by
    rw [D.piPlus_add_piMinus]
    rfl
  Pp_idem s := by
    rw [← ContinuousLinearMap.mul_def]
    exact (D.isIdempotentElem_piPlus s).eq
  Pp_comp_E τ s hs := by
    simp only [← ContinuousLinearMap.mul_def]
    exact (D.E_mul_piPlus hs).symm

end GreenKernel

/-- **Green kernel of the periodic dichotomy.** If the splitting circle is `|z| = e^{βP}`,
there are rates `βm < β < βp` and a constant `K` for which `K₋ = E Π₋`, `K₊ = E₊ Π₊` satisfy
the bounds of `GreenKernel` (`greenKernel`) and are time continuous. -/
theorem exists_greenKernel (hE : ForwardEvolution D.E) {β : ℝ}
    (hβ : D.r = Real.exp (β * D.P)) :
    ∃ (βm βp K : ℝ)
      (hm : ∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s)))
      (hp : ∀ s τ, τ ≤ s → ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s))),
      βm < β ∧ β < βp ∧ (greenKernel D hE hm hp).TimeContinuous := by
  obtain ⟨C, hC⟩ := hE.bounded D.P
  obtain ⟨βm, βp, K, h1, h2, -, -, -, hm, hp⟩ := D.periodic_dichotomy_rates hβ hC
  exact ⟨βm, βp, K, hm, hp, h1, h2, greenKernel_timeContinuous D hE hm hp⟩

/-! ### The Volterra evolution -/

section Volterra

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The evolution of `PeriodicSplitting.ofVolterra` is a `ForwardEvolution`. -/
theorem forwardEvolution_ofVolterra (V : VolterraData ℂ X Y) (hV : V.Compatible)
    (hS₀ : V.S₀ 0 = 1) {P : ℝ} (hP : 0 < P) (hB : ∀ t, V.B (t + P) = V.B t) {r : ℝ}
    (hr : 0 < r) (hsph : sphere (0 : ℂ) r ⊆ resolventSet ℂ (V.evolution P 0)) :
    ForwardEvolution (PeriodicSplitting.ofVolterra V hV hS₀ hP hB hr hsph).E :=
  forwardEvolution_volterra hV hS₀

/-- **Volterra case.** For the periodic Volterra evolution with a splitting circle
`|z| = e^{βP}` in the resolvent set of the monodromy `E(P,0)`: `Π_±` are strongly continuous on
`ℝ`, `s ↦ E(τ,s) Π₋(s) x` is continuous on `(-∞, τ]`, `s ↦ E₊(τ,s) Π₊(s) x` on `[τ, ∞)`, and
there are rates `βm < β < βp` for which `K₋ = E Π₋`, `K₊ = E₊ Π₊` form a time-continuous
`GreenKernel ℂ X X`. -/
theorem exists_greenKernel_volterra (V : VolterraData ℂ X Y) (hV : V.Compatible)
    (hS₀ : V.S₀ 0 = 1) {P : ℝ} (hP : 0 < P) (hB : ∀ t, V.B (t + P) = V.B t) {β : ℝ}
    (hsph : sphere (0 : ℂ) (Real.exp (β * P)) ⊆ resolventSet ℂ (V.evolution P 0)) :
    let D := PeriodicSplitting.ofVolterra V hV hS₀ hP hB (Real.exp_pos (β * P)) hsph
    (∀ x, Continuous fun t => D.piPlus t x) ∧ (∀ x, Continuous fun t => D.piMinus t x) ∧
    (∀ τ x, ContinuousOn (fun s => V.evolution τ s (D.piMinus s x)) (Iic τ)) ∧
    (∀ τ x, ContinuousOn (fun s => D.extEvol τ s (D.piPlus s x)) (Ici τ)) ∧
    ∃ (βm βp K : ℝ)
      (hm : ∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s)))
      (hp : ∀ s τ, τ ≤ s → ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s))),
      βm < β ∧ β < βp ∧
        (greenKernel D (forwardEvolution_ofVolterra V hV hS₀ hP hB _ hsph) hm hp).TimeContinuous := by
  intro D
  have hE : ForwardEvolution D.E := forwardEvolution_ofVolterra V hV hS₀ hP hB _ hsph
  exact ⟨continuous_piPlus_apply D hE, continuous_piMinus_apply D hE,
    continuousOn_E_piMinus_snd D hE, continuousOn_extEvol_piPlus_snd D hE,
    exists_greenKernel D hE rfl⟩

end Volterra

end UnforcedLeray.Infra.EvolutionContinuity
