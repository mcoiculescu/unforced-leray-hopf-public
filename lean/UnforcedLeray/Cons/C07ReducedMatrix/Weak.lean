import UnforcedLeray.Blueprint.Construction.Steps

/-!
# Step C7, helper: weak free problems, the periodic `H¹` class and the natural lift

Infrastructure for `Cons/C07ReducedMatrix.lean` (step C7 `StepReducedMatrix`, blueprint units
B1004, B0770–B0772; `paper/main.tex` lines 9738–9750, 9139–9232, 10872–10900).

* `IsWeakFreeSolution h σ v T`: the free problem `L_free v = 𝔓 div T`,
  `L_free = σ + 𝒯₀ - hΔ - ½` (`unlabeled:8850`, lines 8850–8869, B0551), in distributions on
  `ℝ × ℝ³` with every pairing convergent, in the encoding of `IsWeakModeSolution`
  (`Blueprint/Construction/Cylinder.lean`): the stress pairing is the Lebesgue form
  `lerayDivIntegral`. With `T = 0` it is the homogeneous free problem. Proved: linearity
  (`sub`), invariance under null modifications of the field (`congr_field`) and of the
  stress (`congr_source`), and the passage between the mode equation (`IsWeakModeSolution`) and
  the free problem with the coupling stress `-(U⊗w + w⊗U)` (`ofMode`, `toMode`).
* `IsH1Periodic` (the periodic `H¹` class of `Cylinder.lean`): closed under differences
  (`isH1Periodic_sub`) and under modification on the symmetry axis
  (`isH1Periodic_congr_offAxis`); the axis `{y₁² + y₂² = 0}` is a null set of `ℝ³`
  (`volume_axis`) and `ℝ × axis` a null set of `ℝ × ℝ³` (`volume_axis_spacetime`).
* The natural lift `cylinderLift R b = 𝒩_v b` (`eq:st18-t00770`) is pointwise linear in `b`
  (`cylinderLift_sub`, `cylinderLift_neg`, `cylinderLift_zero`) and vanishes on the axis
  (`cylinderLift_axis`), where the ring chart takes Lean's junk value `s = R²/0 = 0`.

Everything here is proved; nothing is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Blueprint.C07

/-! ## The weak free problem -/

/-- The free problem `L_free v = 𝔓 div T` with `L_free = σ + 𝒯₀ - hΔ - ½`
(`unlabeled:8850`, lines 8850–8858, B0551: `𝓡^phys_μ = (L^phys_free,μ)⁻¹𝔓`,
`𝒮_μ = 𝒩_v⁻¹𝓡^phys_μ div 𝒩_T`), in distributions on `ℝ × ℝ³`, every derivative on the test,
every pairing convergent. The physical stress `T(τ)` is given by its three columns; its pairing
is `lerayDivIntegral` (the Lebesgue form of `⟨𝔓 div T, ψ⟩`, `Cylinder.lean`). -/
structure IsWeakFreeSolution (h σ : ℝ) (v : ℝ → SpatialField)
    (T : ℝ → Fin 3 → SpatialField) : Prop where
  value_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm v ψ)
  temporal_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (temporalTerm v ψ)
  dilation_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (dilationTerm v ψ)
  diffusion_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (diffusionTerm v ψ)
  source_integrable : ∀ ψ, IsSimilarityTest ψ → ∀ᵐ τ, ∀ j : Fin 3,
    Integrable (lerayDivIntegrand (T τ) (slice ψ τ) j)
  source_time_integrable : ∀ ψ, IsSimilarityTest ψ →
    Integrable (fun τ => lerayDivIntegral (T τ) (slice ψ τ))
  identity : ∀ ψ, IsSimilarityTest ψ →
    ∫ z, weakModeIntegrand h σ v ψ z = ∫ τ, lerayDivIntegral (T τ) (slice ψ τ)

theorem weakModeIntegrand_integrable {h σ : ℝ} {v : ℝ → SpatialField}
    {ψ : SpaceTime → Space} (h1 : Integrable (pairTerm v ψ))
    (h2 : Integrable (temporalTerm v ψ)) (h3 : Integrable (dilationTerm v ψ))
    (h4 : Integrable (diffusionTerm v ψ)) : Integrable (weakModeIntegrand h σ v ψ) := by
  have e : weakModeIntegrand h σ v ψ = fun z => (σ - 1 / 2) * pairTerm v ψ z +
      (-temporalTerm v ψ z + (3 / 2 : ℝ) * pairTerm v ψ z + (1 / 2 : ℝ) * dilationTerm v ψ z) -
      h * diffusionTerm v ψ z := rfl
  rw [e]
  exact ((h1.const_mul _).add ((h2.neg.add (h1.const_mul _)).add (h3.const_mul _))).sub
    (h4.const_mul _)

theorem IsWeakFreeSolution.weak_integrable {h σ : ℝ} {v : ℝ → SpatialField}
    {T : ℝ → Fin 3 → SpatialField} (hv : IsWeakFreeSolution h σ v T) {ψ : SpaceTime → Space}
    (hψ : IsSimilarityTest ψ) : Integrable (weakModeIntegrand h σ v ψ) :=
  weakModeIntegrand_integrable (hv.value_integrable ψ hψ) (hv.temporal_integrable ψ hψ)
    (hv.dilation_integrable ψ hψ) (hv.diffusion_integrable ψ hψ)

/-! ### Pointwise linearity of the pairing integrands -/

section Linear

variable (f g : ℝ → SpatialField) (ψ : SpaceTime → Space) (z : SpaceTime)

theorem pairTerm_sub : pairTerm (fun τ y => f τ y - g τ y) ψ z = pairTerm f ψ z - pairTerm g ψ z :=
  inner_sub_left _ _ _

theorem temporalTerm_sub :
    temporalTerm (fun τ y => f τ y - g τ y) ψ z = temporalTerm f ψ z - temporalTerm g ψ z :=
  inner_sub_left _ _ _

theorem dilationTerm_sub :
    dilationTerm (fun τ y => f τ y - g τ y) ψ z = dilationTerm f ψ z - dilationTerm g ψ z :=
  inner_sub_left _ _ _

theorem diffusionTerm_sub :
    diffusionTerm (fun τ y => f τ y - g τ y) ψ z = diffusionTerm f ψ z - diffusionTerm g ψ z :=
  inner_sub_left _ _ _

theorem weakModeIntegrand_sub (h σ : ℝ) :
    weakModeIntegrand h σ (fun τ y => f τ y - g τ y) ψ z =
      weakModeIntegrand h σ f ψ z - weakModeIntegrand h σ g ψ z := by
  simp only [weakModeIntegrand, driftAdjointTerm, pairTerm_sub, temporalTerm_sub,
    dilationTerm_sub, diffusionTerm_sub]
  ring

end Linear

theorem lerayDivIntegrand_sub (c₁ c₂ : Fin 3 → SpatialField) (φ : Space → Space) (j : Fin 3) :
    lerayDivIntegrand (c₁ - c₂) φ j = fun y => lerayDivIntegrand c₁ φ j y -
      lerayDivIntegrand c₂ φ j y := by
  funext y
  simp only [lerayDivIntegrand, Pi.sub_apply, inner_sub_left]

theorem lerayDivIntegrand_neg (c : Fin 3 → SpatialField) (φ : Space → Space) (j : Fin 3) :
    lerayDivIntegrand (-c) φ j = fun y => -lerayDivIntegrand c φ j y := by
  funext y
  simp only [lerayDivIntegrand, Pi.neg_apply, inner_neg_left]

theorem lerayDivIntegral_zero (φ : Space → Space) : lerayDivIntegral 0 φ = 0 := by
  simp [lerayDivIntegral, lerayDivIntegrand]

theorem lerayDivIntegral_neg (c : Fin 3 → SpatialField) (φ : Space → Space) :
    lerayDivIntegral (-c) φ = -lerayDivIntegral c φ := by
  simp only [lerayDivIntegral, lerayDivIntegrand_neg, integral_neg, Finset.sum_neg_distrib]

theorem lerayDivIntegral_sub {c₁ c₂ : Fin 3 → SpatialField} {φ : Space → Space}
    (h₁ : ∀ j, Integrable (lerayDivIntegrand c₁ φ j))
    (h₂ : ∀ j, Integrable (lerayDivIntegrand c₂ φ j)) :
    lerayDivIntegral (c₁ - c₂) φ = lerayDivIntegral c₁ φ - lerayDivIntegral c₂ φ := by
  simp only [lerayDivIntegral, lerayDivIntegrand_sub, integral_sub (h₁ _) (h₂ _),
    Finset.sum_sub_distrib]
  ring

/-- Columns equal almost everywhere have the same pairing integrands, almost everywhere. -/
theorem lerayDivIntegrand_congr {c₁ c₂ : Fin 3 → SpatialField} (hc : ∀ j, c₁ j =ᵐ[volume] c₂ j)
    (φ : Space → Space) (j : Fin 3) :
    lerayDivIntegrand c₁ φ j =ᵐ[volume] lerayDivIntegrand c₂ φ j := by
  filter_upwards [hc j] with y hy
  simp only [lerayDivIntegrand, hy]

theorem lerayDivIntegral_congr {c₁ c₂ : Fin 3 → SpatialField} (hc : ∀ j, c₁ j =ᵐ[volume] c₂ j)
    (φ : Space → Space) : lerayDivIntegral c₁ φ = lerayDivIntegral c₂ φ := by
  simp only [lerayDivIntegral]
  congr 1
  exact Finset.sum_congr rfl fun j _ => integral_congr_ae (lerayDivIntegrand_congr hc φ j)

/-! ### Linearity and invariance of the weak free problem -/

/-- The weak free problem is linear: `L(v₁ - v₂) = 𝔓 div(T₁ - T₂)`. -/
theorem IsWeakFreeSolution.sub {h σ : ℝ} {v₁ v₂ : ℝ → SpatialField}
    {T₁ T₂ : ℝ → Fin 3 → SpatialField} (h₁ : IsWeakFreeSolution h σ v₁ T₁)
    (h₂ : IsWeakFreeSolution h σ v₂ T₂) :
    IsWeakFreeSolution h σ (fun τ y => v₁ τ y - v₂ τ y) (T₁ - T₂) where
  value_integrable ψ hψ := by
    exact ((h₁.value_integrable ψ hψ).sub (h₂.value_integrable ψ hψ)).congr
      (Eventually.of_forall fun z => (pairTerm_sub v₁ v₂ ψ z).symm)
  temporal_integrable ψ hψ := by
    exact ((h₁.temporal_integrable ψ hψ).sub (h₂.temporal_integrable ψ hψ)).congr
      (Eventually.of_forall fun z => (temporalTerm_sub v₁ v₂ ψ z).symm)
  dilation_integrable ψ hψ := by
    exact ((h₁.dilation_integrable ψ hψ).sub (h₂.dilation_integrable ψ hψ)).congr
      (Eventually.of_forall fun z => (dilationTerm_sub v₁ v₂ ψ z).symm)
  diffusion_integrable ψ hψ := by
    exact ((h₁.diffusion_integrable ψ hψ).sub (h₂.diffusion_integrable ψ hψ)).congr
      (Eventually.of_forall fun z => (diffusionTerm_sub v₁ v₂ ψ z).symm)
  source_integrable ψ hψ := by
    filter_upwards [h₁.source_integrable ψ hψ, h₂.source_integrable ψ hψ] with τ hτ₁ hτ₂ j
    rw [Pi.sub_apply, lerayDivIntegrand_sub]
    exact (hτ₁ j).sub (hτ₂ j)
  source_time_integrable ψ hψ := by
    refine ((h₁.source_time_integrable ψ hψ).sub (h₂.source_time_integrable ψ hψ)).congr ?_
    filter_upwards [h₁.source_integrable ψ hψ, h₂.source_integrable ψ hψ] with τ hτ₁ hτ₂
    exact (lerayDivIntegral_sub hτ₁ hτ₂).symm
  identity ψ hψ := by
    have e1 : ∫ z, weakModeIntegrand h σ (fun τ y => v₁ τ y - v₂ τ y) ψ z =
        (∫ z, weakModeIntegrand h σ v₁ ψ z) - ∫ z, weakModeIntegrand h σ v₂ ψ z := by
      rw [← integral_sub (h₁.weak_integrable hψ) (h₂.weak_integrable hψ)]
      exact integral_congr_ae (Eventually.of_forall fun z => weakModeIntegrand_sub v₁ v₂ ψ z h σ)
    have e2 : ∫ τ, lerayDivIntegral ((T₁ - T₂) τ) (slice ψ τ) =
        (∫ τ, lerayDivIntegral (T₁ τ) (slice ψ τ)) -
          ∫ τ, lerayDivIntegral (T₂ τ) (slice ψ τ) := by
      rw [← integral_sub (h₁.source_time_integrable ψ hψ) (h₂.source_time_integrable ψ hψ)]
      refine integral_congr_ae ?_
      filter_upwards [h₁.source_integrable ψ hψ, h₂.source_integrable ψ hψ] with τ hτ₁ hτ₂
      rw [Pi.sub_apply, lerayDivIntegral_sub hτ₁ hτ₂]
    rw [e1, e2, h₁.identity ψ hψ, h₂.identity ψ hψ]

/-- The weak free problem only sees the spacetime class of the field. -/
theorem IsWeakFreeSolution.congr_field {h σ : ℝ} {v w : ℝ → SpatialField}
    {T : ℝ → Fin 3 → SpatialField} (hv : IsWeakFreeSolution h σ v T)
    (hvw : (fun z : SpaceTime => v z.1 z.2) =ᵐ[volume] fun z => w z.1 z.2) :
    IsWeakFreeSolution h σ w T where
  value_integrable ψ hψ := (hv.value_integrable ψ hψ).congr (hvw.mono fun z hz => by
    simp only [pairTerm, hz])
  temporal_integrable ψ hψ := (hv.temporal_integrable ψ hψ).congr (hvw.mono fun z hz => by
    simp only [temporalTerm, hz])
  dilation_integrable ψ hψ := (hv.dilation_integrable ψ hψ).congr (hvw.mono fun z hz => by
    simp only [dilationTerm, hz])
  diffusion_integrable ψ hψ := (hv.diffusion_integrable ψ hψ).congr (hvw.mono fun z hz => by
    simp only [diffusionTerm, hz])
  source_integrable := hv.source_integrable
  source_time_integrable := hv.source_time_integrable
  identity ψ hψ := by
    rw [← hv.identity ψ hψ]
    refine integral_congr_ae (hvw.mono fun z hz => ?_)
    simp only [weakModeIntegrand, driftAdjointTerm, pairTerm, temporalTerm, dilationTerm,
      diffusionTerm, hz]

/-- The weak free problem only sees the class of the stress at almost every phase. -/
theorem IsWeakFreeSolution.congr_source {h σ : ℝ} {v : ℝ → SpatialField}
    {T T' : ℝ → Fin 3 → SpatialField} (hv : IsWeakFreeSolution h σ v T)
    (hT : ∀ᵐ τ, ∀ j, T τ j =ᵐ[volume] T' τ j) : IsWeakFreeSolution h σ v T' where
  value_integrable := hv.value_integrable
  temporal_integrable := hv.temporal_integrable
  dilation_integrable := hv.dilation_integrable
  diffusion_integrable := hv.diffusion_integrable
  source_integrable ψ hψ := by
    filter_upwards [hv.source_integrable ψ hψ, hT] with τ hτ hτT j
    exact (hτ j).congr (lerayDivIntegrand_congr hτT _ j)
  source_time_integrable ψ hψ := by
    refine (hv.source_time_integrable ψ hψ).congr ?_
    filter_upwards [hT] with τ hτT
    exact lerayDivIntegral_congr hτT _
  identity ψ hψ := by
    rw [hv.identity ψ hψ]
    refine integral_congr_ae ?_
    filter_upwards [hT] with τ hτT
    exact lerayDivIntegral_congr hτT _

/-- The coupling stress `-(U⊗w + w⊗U)` of the mode equation, column by column. -/
def couplingSource (U w : ℝ → SpatialField) : ℝ → Fin 3 → SpatialField :=
  fun τ j => -symTensorColumns (U τ) (w τ) j

/-- A weak mode solution solves the free problem with the stress `-(U⊗w + w⊗U)`:
`L_free w = -𝔓 div(U⊗w + w⊗U)` (`eq:st18-t00633`, `loc:eq:mode`). -/
theorem IsWeakFreeSolution.ofMode {h σ : ℝ} {U w : ℝ → SpatialField}
    (hw : IsWeakModeSolution h σ U w) : IsWeakFreeSolution h σ w (couplingSource U w) where
  value_integrable := hw.value_integrable
  temporal_integrable := hw.temporal_integrable
  dilation_integrable := hw.dilation_integrable
  diffusion_integrable := hw.diffusion_integrable
  source_integrable ψ hψ := by
    filter_upwards [hw.coupling_integrable ψ hψ] with τ hτ j
    have e : couplingSource U w τ = -symTensorColumns (U τ) (w τ) := rfl
    rw [e, lerayDivIntegrand_neg]
    exact (hτ j).neg
  source_time_integrable ψ hψ := by
    have e : (fun τ => lerayDivIntegral (couplingSource U w τ) (slice ψ τ)) =
        fun τ => -weakCoupling U w ψ τ := by
      funext τ
      exact lerayDivIntegral_neg _ _
    rw [e]
    exact (hw.coupling_time_integrable ψ hψ).neg
  identity ψ hψ := by
    have e : (fun τ => lerayDivIntegral (couplingSource U w τ) (slice ψ τ)) =
        fun τ => -weakCoupling U w ψ τ := by
      funext τ
      exact lerayDivIntegral_neg _ _
    rw [e, integral_neg]
    linarith [hw.identity ψ hψ]

/-- Conversely, a weak free solution whose stress is `-(U⊗w + w⊗U)` at almost every phase
solves the mode equation. -/
theorem IsWeakFreeSolution.toMode {h σ : ℝ} {U w : ℝ → SpatialField}
    {T : ℝ → Fin 3 → SpatialField} (hw : IsWeakFreeSolution h σ w T)
    (hT : ∀ᵐ τ, ∀ j, T τ j =ᵐ[volume] couplingSource U w τ j) :
    IsWeakModeSolution h σ U w := by
  have hw' := hw.congr_source hT
  have e : ∀ ψ τ, weakCoupling U w ψ τ =
      -lerayDivIntegral (couplingSource U w τ) (slice ψ τ) := fun ψ τ => by
    have e0 : couplingSource U w τ = -symTensorColumns (U τ) (w τ) := rfl
    rw [e0, lerayDivIntegral_neg, neg_neg]
    rfl
  exact
    { value_integrable := hw.value_integrable
      temporal_integrable := hw.temporal_integrable
      dilation_integrable := hw.dilation_integrable
      diffusion_integrable := hw.diffusion_integrable
      coupling_integrable := fun ψ hψ => by
        filter_upwards [hw'.source_integrable ψ hψ] with τ hτ j
        have e0 : couplingSource U w τ = -symTensorColumns (U τ) (w τ) := rfl
        have h0 := hτ j
        rw [e0, lerayDivIntegrand_neg] at h0
        have h1 : Integrable
            (-(lerayDivIntegrand (symTensorColumns (U τ) (w τ)) (slice ψ τ) j)) := h0
        exact integrable_neg_iff.1 h1
      coupling_time_integrable := fun ψ hψ => by
        rw [show weakCoupling U w ψ = fun τ => -lerayDivIntegral (couplingSource U w τ)
          (slice ψ τ) from funext (e ψ)]
        exact (hw'.source_time_integrable ψ hψ).neg
      identity := fun ψ hψ => by
        rw [show weakCoupling U w ψ = fun τ => -lerayDivIntegral (couplingSource U w τ)
          (slice ψ τ) from funext (e ψ), integral_neg, hw'.identity ψ hψ]
        ring }

/-! ## The symmetry axis is a null set -/

/-- The coordinate plane `{y₁ = 0}` as a submodule of `ℝ³`. -/
def firstCoordinatePlane : Submodule ℝ Space where
  carrier := {y | y 0 = 0}
  add_mem' := by
    intro a b ha hb
    change a 0 = 0 at ha
    change b 0 = 0 at hb
    change (a + b) 0 = 0
    rw [PiLp.add_apply, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c y hy
    change y 0 = 0 at hy
    change (c • y) 0 = 0
    rw [PiLp.smul_apply, hy, smul_zero]

/-- The symmetry axis `{y₁² + y₂² = 0}` of `ℝ³` is a null set. -/
theorem volume_axis : volume {y : Space | y 0 ^ 2 + y 1 ^ 2 = 0} = 0 := by
  refine measure_mono_null (t := (firstCoordinatePlane : Set Space)) ?_ ?_
  · intro y hy
    change y 0 ^ 2 + y 1 ^ 2 = 0 at hy
    show y 0 = 0
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  · refine Measure.addHaar_submodule _ _ fun htop => ?_
    have hmem : coordinateVector 0 ∈ firstCoordinatePlane := by
      rw [htop]
      exact Submodule.mem_top
    change (coordinateVector 0 : Space) 0 = 0 at hmem
    simp [coordinateVector] at hmem

/-- `ℝ × axis` is a null set of `ℝ × ℝ³`. -/
theorem volume_axis_spacetime :
    volume {z : SpaceTime | z.2 0 ^ 2 + z.2 1 ^ 2 = 0} = 0 := by
  have e : {z : SpaceTime | z.2 0 ^ 2 + z.2 1 ^ 2 = 0} =
      (univ : Set ℝ) ×ˢ {y : Space | y 0 ^ 2 + y 1 ^ 2 = 0} := by
    ext z
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, volume_axis, mul_zero]

/-- Two fields that agree off the axis agree almost everywhere on `ℝ³`. -/
theorem ae_eq_of_offAxis {f g : SpatialField} (hfg : ∀ y : Space, y 0 ^ 2 + y 1 ^ 2 ≠ 0 →
    f y = g y) : f =ᵐ[volume] g := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 volume_axis] with y hy
  exact hfg y hy

/-- Two profiles that agree off the axis agree almost everywhere on `ℝ × ℝ³`. -/
theorem ae_eq_spacetime_of_offAxis {f g : ℝ → SpatialField}
    (hfg : ∀ τ (y : Space), y 0 ^ 2 + y 1 ^ 2 ≠ 0 → f τ y = g τ y) :
    (fun z : SpaceTime => f z.1 z.2) =ᵐ[volume] fun z => g z.1 z.2 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 volume_axis_spacetime] with z hz
  exact hfg z.1 z.2 hz

/-! ## The periodic `H¹` class -/

theorem isSolenoidal_sub {f g : SpatialField} (hf : IsSolenoidal f) (hg : IsSolenoidal g) :
    IsSolenoidal (fun y => f y - g y) where
  integrable φ hφ := by
    refine ((hf.integrable φ hφ).sub (hg.integrable φ hφ)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  identity φ hφ := by
    have e : (fun x => ∑ i : Fin 3, ((fun y => f y - g y) x) i * spatialTestDerivative i φ x) =
        fun x => (∑ i : Fin 3, (f x) i * spatialTestDerivative i φ x) -
          ∑ i : Fin 3, (g x) i * spatialTestDerivative i φ x := by
      funext x
      simp only [PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [e, integral_sub (hf.integrable φ hφ) (hg.integrable φ hφ), hf.identity φ hφ,
      hg.identity φ hφ, sub_zero]

theorem isSolenoidal_congr_ae {f g : SpatialField} (hf : IsSolenoidal f)
    (hfg : f =ᵐ[volume] g) : IsSolenoidal g where
  integrable φ hφ := (hf.integrable φ hφ).congr (hfg.mono fun x hx => by simp only [hx])
  identity φ hφ := by
    rw [← hf.identity φ hφ]
    exact integral_congr_ae (hfg.mono fun x hx => by simp only [hx])

theorem hasWeak_sub {i : Fin 3} {f g F G : SpatialField}
    (hf : HasWeakSpatialDerivative i f F) (hg : HasWeakSpatialDerivative i g G) :
    HasWeakSpatialDerivative i (fun x => f x - g x) (fun x => F x - G x) where
  left_integrable φ hφ := ((hf.left_integrable φ hφ).sub (hg.left_integrable φ hφ)).congr
    (Eventually.of_forall fun x => by simp only [Pi.sub_apply, smul_sub])
  right_integrable φ hφ := ((hf.right_integrable φ hφ).sub (hg.right_integrable φ hφ)).congr
    (Eventually.of_forall fun x => by simp only [Pi.sub_apply, smul_sub])
  identity φ hφ := by
    simp only [smul_sub]
    rw [integral_sub (hf.left_integrable φ hφ) (hg.left_integrable φ hφ),
      integral_sub (hf.right_integrable φ hφ) (hg.right_integrable φ hφ), hf.identity φ hφ,
      hg.identity φ hφ]
    abel

theorem hasWeak_congr_left_ae {i : Fin 3} {f g F : SpatialField}
    (hf : HasWeakSpatialDerivative i f F) (hfg : f =ᵐ[volume] g) :
    HasWeakSpatialDerivative i g F where
  left_integrable φ hφ := (hf.left_integrable φ hφ).congr (hfg.mono fun x hx => by
    simp only [hx])
  right_integrable := hf.right_integrable
  identity φ hφ := by
    rw [← hf.identity φ hφ]
    exact integral_congr_ae (hfg.mono fun x hx => by simp only [hx])

theorem periodic_sub {P : ℝ} {f g : ℝ → SpatialField} (hf : Function.Periodic f P)
    (hg : Function.Periodic g P) : Function.Periodic (fun τ y => f τ y - g τ y) P := by
  intro τ
  simp only [hf τ, hg τ]

/-- The periodic `H¹` class is closed under differences. -/
theorem isH1Periodic_sub {P : ℝ} {f g : ℝ → SpatialField} (hf : IsH1Periodic P f)
    (hg : IsH1Periodic P g) : IsH1Periodic P (fun τ y => f τ y - g τ y) where
  value :=
    { periodic := periodic_sub hf.value.periodic hg.value.periodic
      measurable := hf.value.measurable.sub hg.value.measurable
      memL2 := hf.value.memL2.sub hg.value.memL2
      solenoidal := by
        filter_upwards [hf.value.solenoidal, hg.value.solenoidal] with τ h1 h2
        exact isSolenoidal_sub h1 h2 }
  gradient := by
    obtain ⟨G, hG⟩ := hf.gradient
    obtain ⟨G', hG'⟩ := hg.gradient
    refine ⟨fun i τ y => G i τ y - G' i τ y, fun i => ⟨(hG i).1.sub (hG' i).1,
      (hG i).2.1.sub (hG' i).2.1, ?_⟩⟩
    filter_upwards [(hG i).2.2, (hG' i).2.2] with τ h1 h2
    exact hasWeak_sub h1 h2

/-- The periodic `H¹` class only sees fields off the symmetry axis (a null set at every
phase), provided the modification keeps exact periodicity. -/
theorem isH1Periodic_congr_offAxis {P : ℝ} {f g : ℝ → SpatialField} (hf : IsH1Periodic P f)
    (hg : Function.Periodic g P)
    (hfg : ∀ τ (y : Space), y 0 ^ 2 + y 1 ^ 2 ≠ 0 → g τ y = f τ y) : IsH1Periodic P g := by
  have hST := ae_eq_spacetime_of_offAxis (fun τ y hy => (hfg τ y hy).symm)
  have hsl : ∀ τ, f τ =ᵐ[volume] g τ := fun τ => ae_eq_of_offAxis fun y hy => (hfg τ y hy).symm
  refine ⟨⟨hg, hf.value.measurable.congr hST, (MemLp.ae_eq (ae_restrict_of_ae hST)
    hf.value.memL2), ?_⟩, ?_⟩
  · filter_upwards [hf.value.solenoidal] with τ hτ
    exact isSolenoidal_congr_ae hτ (hsl τ)
  · obtain ⟨G, hG⟩ := hf.gradient
    refine ⟨G, fun i => ⟨(hG i).1, (hG i).2.1, ?_⟩⟩
    filter_upwards [(hG i).2.2] with τ hτ
    exact hasWeak_congr_left_ae hτ (hsl τ)

/-! ## The natural lift -/

theorem cylinderLift_sub (R : ℝ) (b b' : CylinderField) (τ : ℝ) (y : Space) :
    cylinderLift R (b - b') τ y = cylinderLift R b τ y - cylinderLift R b' τ y := by
  simp only [cylinderLift, Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]
  module

theorem cylinderLift_neg (R : ℝ) (b : CylinderField) (τ : ℝ) (y : Space) :
    cylinderLift R (-b) τ y = -cylinderLift R b τ y := by
  simp only [cylinderLift, Pi.neg_apply, Prod.fst_neg, Prod.snd_neg]
  module

theorem cylinderLift_zero (R : ℝ) : cylinderLift R 0 = fun _ _ => 0 := by
  funext τ y
  simp [cylinderLift]

/-- On the axis the ring chart takes the junk value `s = R²/0 = 0`, so the lift vanishes. -/
theorem cylinderLift_axis (R : ℝ) (b : CylinderField) (τ : ℝ) {y : Space}
    (hy : y 0 ^ 2 + y 1 ^ 2 = 0) : cylinderLift R b τ y = 0 := by
  simp [cylinderLift, ringChart, hy]

end UnforcedLeray.Blueprint.C07
