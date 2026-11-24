import UnforcedLeray.Short.PartI.Sub.S13a
import UnforcedLeray.Lib.PlanarSectorsB.TransportFormula
import UnforcedLeray.Units.B0062.Flow

/-!
# Part I, task `PartI:TransportGroupHjM`, target `freeFlowExists_zero : FreeFlowExists 0`

Source of record: `the November 2 reference manuscript`, lines 841-852
(`T(t)f(r,ϑ) = f(r,ϑ - Ω(r)t)`; for `j = 0` the free transport is an isometry of `L²_M`).

Route.
* `flowMap t y = e^{-itΩ(|y|)} y` satisfies `freeFlow t f = f ∘ flowMap t`. It preserves the
  weighted measure `⟨y⟩^{2M} dy` (`B0062.measurePreserving_flow_withDensity`), so
  `f ↦ f ∘ flowMap t` is a linear isometry `compFlow` of `L²_M`.
* On every sector function `compFlow` agrees with the sector group `Planar.transportGroupW M t`
  (`Planar.coeFn_transportGroupW_secEmb`). Both are bounded and the sector sums are dense
  (`Planar.hasSum_secEmb_secProf`), so they agree on all of `L²_M`.
* `H^0_M` is identified with `L²_M` by the value map `HjM.valueCLM 0 M` and its inverse `ofL2`.
  Put `T t := ofL2 ∘ transportGroupW M t ∘ valueCLM`; `‖T t‖ ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

open UnforcedLeray.Planar (ProfL2 L2w secEmb secProf transportGroupW hasSum_secEmb_secProf
  coeFn_secEmb coeFn_transportGroupW_secEmb norm_transportGroupW_le)

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

namespace TransportGroupHjMZero

/-- The flow map `Φ_t y = e^{-itΩ(|y|)} y`; `freeFlow t f = f ∘ flowMap t` (`S13a`). -/
def flowMap (t : ℝ) (y : ℂ) : ℂ :=
  Complex.exp (((-(t * B0009.Omega y) : ℝ) : ℂ) * Complex.I) * y

/-- The flow map is the B0062 flow (`B0062.Omega r = e^{-r²/4} = B0009.Omega`). -/
theorem flow_eq_flowMap (t : ℝ) : B0062.flow t = flowMap t := by
  funext y
  have hΩ : B0062.Omega ‖y‖ = B0009.Omega y := rfl
  have hr : -(B0062.Omega ‖y‖ * t) = -(t * B0009.Omega y) := by
    rw [hΩ]
    ring
  simp only [B0062.flow, B0062.phase, B0062.gexp, flowMap, hr]

/-- The flow preserves the weighted measure `⟨y⟩^{2M} dy`. -/
theorem measurePreserving_flowMap (M t : ℝ) :
    MeasurePreserving (flowMap t) (UnforcedLeray.Planar.wMeasure M)
      (UnforcedLeray.Planar.wMeasure M) := by
  have hpos : ∀ r : ℝ, 0 < 1 + r ^ 2 := fun r => by positivity
  have hcont : Continuous fun r : ℝ => (1 + r ^ 2) ^ M :=
    (by fun_prop : Continuous fun r : ℝ => 1 + r ^ 2).rpow_const fun r => Or.inl (hpos r).ne'
  have hρ : Measurable fun r : ℝ => ENNReal.ofReal ((1 + r ^ 2) ^ M) :=
    hcont.measurable.ennreal_ofReal
  have h := B0062.measurePreserving_flow_withDensity t hρ
  rw [flow_eq_flowMap] at h
  exact h

/-- Composition with the flow map, a linear isometry of `L²_M`. -/
def compFlow (M t : ℝ) : L2w M →L[ℂ] L2w M :=
  (Lp.compMeasurePreservingₗᵢ ℂ (flowMap t) (measurePreserving_flowMap M t)).toContinuousLinearMap

theorem coeFn_compFlow (M t : ℝ) (f : L2w M) :
    (compFlow M t f : ℂ → ℂ) =ᵐ[UnforcedLeray.Planar.wMeasure M] (f : ℂ → ℂ) ∘ flowMap t :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_flowMap M t)

/-- On a sector function the sector group is the composition with the flow. -/
theorem transportGroupW_secEmb_eq (M t : ℝ) (n : ℤ) (w : ProfL2 M) :
    transportGroupW M t (secEmb M n w) = compFlow M t (secEmb M n w) := by
  have hy : ∀ y : ℂ, UnforcedLeray.Planar.NUE.rot
      (-(UnforcedLeray.GaussianVortex.radialOmega ‖y‖ * t)) y = flowMap t y := by
    intro y
    simp only [UnforcedLeray.Planar.NUE.rot, flowMap, B0009.Omega,
      mul_comm (UnforcedLeray.GaussianVortex.radialOmega ‖y‖) t]
  apply Lp.ext
  filter_upwards [coeFn_transportGroupW_secEmb M t n w, coeFn_compFlow M t (secEmb M n w),
    (measurePreserving_flowMap M t).quasiMeasurePreserving.ae_eq_comp (coeFn_secEmb M n w)]
    with y h1 h2 h3
  rw [h1, h2, h3, Function.comp_apply, hy y]

/-- The sector group equals the composition with the flow on all of `L²_M`. -/
theorem transportGroupW_eq_compFlow (M t : ℝ) (f : L2w M) :
    transportGroupW M t f = compFlow M t f := by
  have hfun : (fun n : ℤ => compFlow M t (secEmb M n (secProf M n f))) =
      (fun n : ℤ => transportGroupW M t (secEmb M n (secProf M n f))) :=
    funext fun n => (transportGroupW_secEmb_eq M t n (secProf M n f)).symm
  have h1 : HasSum (fun n : ℤ => compFlow M t (secEmb M n (secProf M n f)))
      (transportGroupW M t f) := by
    rw [hfun]
    exact (hasSum_secEmb_secProf f).mapL (transportGroupW M t)
  exact h1.unique ((hasSum_secEmb_secProf f).mapL (compFlow M t))

/-- **The free transport on `L²_M` is composition with the flow**, almost everywhere. -/
theorem coeFn_transportGroupW_flow (M t : ℝ) (f : L2w M) :
    (transportGroupW M t f : ℂ → ℂ) =ᵐ[volume] fun y => (f : ℂ → ℂ) (flowMap t y) := by
  rw [transportGroupW_eq_compFlow]
  exact (UnforcedLeray.Planar.volume_ac M).ae_eq (coeFn_compFlow M t f)

/-! ### `H^0_M` is identified with `L²_M` -/

/-- `H^0_M` has the single multi-index `(0,0)`. -/
theorem idx_zero_eq (α : B0008.Idx 0) : α = B0008.idx0 0 := by
  obtain ⟨⟨a, b⟩, hα⟩ := α
  rw [NonUniqueEuler.Sob.mem_multiIdx] at hα
  dsimp only at hα
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha
  subst hb
  rfl

/-- For `j = 0` the norm of `H^0_M` is the norm of the value. -/
theorem norm_eq_value_zero {M : ℝ} (F : B0008.HjM 0 M) : ‖F‖ = ‖F.value‖ := by
  have hsum : ∑ α : B0008.Idx 0, ‖F.der α‖ ^ 2 = ‖F.value‖ ^ 2 := by
    rw [Finset.sum_eq_single (B0008.idx0 0) ?_ ?_, B0008.HjM.der_idx0]
    · intro b _ hb
      exact absurd (idx_zero_eq b) hb
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h : ‖F‖ ^ 2 = ‖F.value‖ ^ 2 := by
    rw [B0008.HjM.norm_sq]
    exact hsum
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem hasWeakDerivOn_zero_index (f : ℂ → ℂ) :
    NonUniqueEuler.Sob.HasWeakDerivOn univ (NonUniqueEuler.Sob.pdList (0, 0)) f f := by
  unfold NonUniqueEuler.Sob.HasWeakDerivOn
  intro φ _
  simp [NonUniqueEuler.Sob.pdList, NonUniqueEuler.Sob.iterDirDeriv_nil]

/-- The tuple with all components equal to `g` lies in `H^0_M`. -/
theorem ofL2_mem {M : ℝ} (g : L2w M) :
    (WithLp.toLp 2 (fun _ : B0008.Idx 0 => g) : B0008.Tuple 0 M) ∈ B0008.HSub 0 M := by
  rw [B0008.mem_HSub_iff]
  intro α
  rw [idx_zero_eq α]
  exact hasWeakDerivOn_zero_index _

/-- The inverse of the value map of `H^0_M`: the element of `H^0_M` with value `g`. -/
def ofL2 (M : ℝ) : L2w M →ₗᵢ[ℂ] B0008.HjM 0 M where
  toFun g := ⟨WithLp.toLp 2 (fun _ : B0008.Idx 0 => g), ofL2_mem g⟩
  map_add' g h := by
    apply B0008.HjM.ext
    rfl
  map_smul' c g := by
    apply B0008.HjM.ext
    rfl
  norm_map' g := by
    rw [norm_eq_value_zero]
    rfl

theorem value_ofL2 {M : ℝ} (g : L2w M) : (ofL2 M g).value = g := rfl

/-- The free transport on `H^0_M`: `T(t) = ofL2 ∘ transportGroupW M t ∘ valueCLM`. -/
def T0 (M t : ℝ) : B0008.HjM 0 M →L[ℂ] B0008.HjM 0 M :=
  (ofL2 M).toContinuousLinearMap.comp ((transportGroupW M t).comp (B0008.HjM.valueCLM 0 M))

theorem value_T0 {M : ℝ} (t : ℝ) (F : B0008.HjM 0 M) :
    (T0 M t F).value = transportGroupW M t F.value := rfl

/-- The free transport on `H^0_M` has norm at most `1`. -/
theorem norm_T0_le (M t : ℝ) : ‖T0 M t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun F => ?_
  rw [one_mul, norm_eq_value_zero (T0 M t F), value_T0, norm_eq_value_zero F]
  calc ‖transportGroupW M t F.value‖ ≤ ‖transportGroupW M t‖ * ‖F.value‖ :=
        (transportGroupW M t).le_opNorm _
    _ ≤ 1 * ‖F.value‖ :=
        mul_le_mul_of_nonneg_right (norm_transportGroupW_le M t) (norm_nonneg _)
    _ = ‖F.value‖ := one_mul _

/-- The value of the free transport is the free flow, almost everywhere. -/
theorem value_T0_ae (M t : ℝ) (F : B0008.HjM 0 M) :
    ((T0 M t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ) := by
  rw [value_T0]
  exact coeFn_transportGroupW_flow M t F.value

end TransportGroupHjMZero

/-- **The free flow exists on `H^0_M`** (source lines 841-852, `j = 0`): for `M > 1` the operators
`T(t) = ofL2 ∘ ⊕ₙ e^{-inΩt} ∘ valueCLM` represent `f ↦ f ∘ Φ_t` and have `‖T(t)‖ ≤ 1`. -/
theorem freeFlowExists_zero : FreeFlowExists 0 := by
  unfold FreeFlowExists
  intro M _hM
  refine ⟨fun t => TransportGroupHjMZero.T0 M t,
    fun t F => TransportGroupHjMZero.value_T0_ae M t F, 1, zero_le_one, fun t => ?_⟩
  simp only [pow_zero, mul_one]
  exact TransportGroupHjMZero.norm_T0_le M t

end UnforcedLeray.Short.PartI
