import UnforcedLeray.Units.B0005
import Mathlib.MeasureTheory.Function.Floor

/-!
# Step C8, part 2: phases of periodic `𝒴₂` fields, periodization, spatial derivatives

Measure-theoretic support for `Cons/C08PhysicalMode.lean` (step C8 `StepPhysicalMode`,
`paper/main.tex` lines 10900–10911, blueprint unit B0773). The space `𝒴₂` of lines 136–141
(unit B0005) is encoded by `Blueprint.IsY2Div` / `B0005.IsY2`: periodic, jointly measurable,
square integrable on the period slab.

* `ae_memLp_slice`: a periodic field square integrable on the period slab is in `L²(ℝ³)` at
  almost every phase of the whole line.
* `periodize`: the `𝒯`-periodic extension of the restriction to `(0, 𝒯]` (used for the weak
  gradient of `IsH1Periodic`, which is not required to be periodic); it keeps joint
  measurability (`aestronglyMeasurable_periodize`, through the quasi-measure-preserving map
  `(τ, y) ↦ (τ mod 𝒯, y)`), square integrability on the slab, and every periodic
  almost-everywhere property (`ae_periodize`).
* `aestronglyMeasurable_partial`: the spatial partial derivative `∂_jU(τ, y)` of a jointly
  measurable field differentiable in `y` is jointly measurable (limit of difference quotients).

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C08

open UnforcedLeray.Blueprint

/-! ## Phases of slab-square-integrable periodic fields -/

/-- A `𝒯`-periodic field, square integrable on the period slab, is in `L²(ℝ³)` at almost
every phase. -/
theorem ae_memLp_slice {P : ℝ} (hP : 0 < P) {f : ℝ → SpatialField}
    (hper : Function.Periodic f P)
    (hm : MemLp (fun z : SpaceTime => f z.1 z.2) 2 (volume.restrict (periodSlab P))) :
    ∀ᵐ t : ℝ, MemLp (f t) 2 volume := by
  refine B0005.ae_of_periodic hP (fun t => by rw [hper t]) ?_
  rw [B0005.IsY2.slab_eq] at hm
  have hint := (hm.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top).prod_right_ae
  filter_upwards [hint, hm.aestronglyMeasurable.prodMk_left] with t ht hmt
  have hmt' : AEStronglyMeasurable (f t) volume := hmt
  refine (memLp_two_iff_integrable_sq_norm hmt').mpr ?_
  simpa using ht

/-! ## Periodization -/

/-- Translations of `ℝ × ℝ³` preserve Lebesgue measure. -/
theorem measurePreserving_shift (c : ℝ) (d : Space) :
    MeasurePreserving (fun z : SpaceTime => z + (c, d)) volume volume := by
  have e : (fun z : SpaceTime => z + (c, d)) = Prod.map (fun t : ℝ => t + c) (fun y => y + d) :=
    rfl
  rw [e, Measure.volume_eq_prod]
  exact (measurePreserving_add_right volume c).prod (measurePreserving_add_right volume d)

section Periodize

variable {P : ℝ} (hP : 0 < P)

theorem measurable_toIocMod : Measurable (toIocMod hP 0) := by
  have h1 : Measurable (fun b : ℝ => ⌊(0 + P - b) / P⌋) :=
    Int.measurable_floor.comp ((measurable_const.sub measurable_id).div_const P)
  have e : toIocMod hP 0 = fun b => b - (fun n : ℤ => (-n) • P) ⌊(0 + P - b) / P⌋ := by
    funext b
    rw [toIocMod, toIocDiv_eq_neg_floor]
  rw [e]
  exact measurable_id.sub ((measurable_from_top (f := fun n : ℤ => (-n) • P)).comp h1)

/-- `(τ, y) ↦ (τ mod 𝒯, y)` (representative in `(0, 𝒯]`) is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_mod :
    Measure.QuasiMeasurePreserving (fun z : SpaceTime => (toIocMod hP 0 z.1, z.2))
      volume volume := by
  have hΦ : Measurable (fun z : SpaceTime => (toIocMod hP 0 z.1, z.2)) :=
    ((measurable_toIocMod hP).comp measurable_fst).prodMk measurable_snd
  refine ⟨hΦ, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply hΦ hs]
  refine measure_mono_null (t := ⋃ k : ℤ,
      (fun z : SpaceTime => z + ((-(k • P) : ℝ), (0 : Space))) ⁻¹' s) ?_
    (measure_iUnion_null fun k => by
      rw [(measurePreserving_shift _ _).measure_preimage hs.nullMeasurableSet]; exact hs0)
  intro z hz
  refine mem_iUnion.mpr ⟨toIocDiv hP 0 z.1, ?_⟩
  simp only [mem_preimage] at hz ⊢
  have e : z + ((-(toIocDiv hP 0 z.1 • P) : ℝ), (0 : Space)) = (toIocMod hP 0 z.1, z.2) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, toIocMod, sub_eq_add_neg]
    · simp
  rw [e]
  exact hz

/-- The `𝒯`-periodic extension of `f` restricted to `(0, 𝒯]`. -/
def periodize (f : ℝ → SpatialField) : ℝ → SpatialField := fun τ => f (toIocMod hP 0 τ)

variable {hP}

theorem periodize_periodic (f : ℝ → SpatialField) : Function.Periodic (periodize hP f) P :=
  fun τ => by simp only [periodize, toIocMod_add_right]

theorem periodize_eq_of_mem (f : ℝ → SpatialField) {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) P) :
    periodize hP f τ = f τ := by
  have hτ' : τ ∈ Ioc (0 : ℝ) (0 + P) := by rwa [zero_add]
  simp only [periodize, (toIocMod_eq_self hP).mpr hτ']

theorem aestronglyMeasurable_periodize {f : ℝ → SpatialField}
    (hf : AEStronglyMeasurable (fun z : SpaceTime => f z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : SpaceTime => periodize hP f z.1 z.2) volume :=
  hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_mod hP)

theorem measurableSet_periodSlab : MeasurableSet (periodSlab P) :=
  measurableSet_Ioc.prod MeasurableSet.univ

theorem memLp_periodize {f : ℝ → SpatialField}
    (hf : MemLp (fun z : SpaceTime => f z.1 z.2) 2 (volume.restrict (periodSlab P))) :
    MemLp (fun z : SpaceTime => periodize hP f z.1 z.2) 2 (volume.restrict (periodSlab P)) := by
  refine hf.ae_eq ?_
  refine (ae_restrict_iff' measurableSet_periodSlab).mpr (Eventually.of_forall fun z hz => ?_)
  exact (congrFun (periodize_eq_of_mem f hz.1) z.2).symm

/-- A property of the pair (phase, value), invariant under a period shift of the phase, that
holds for `f` at almost every phase holds for the periodization. -/
theorem ae_periodize {f : ℝ → SpatialField} {q : ℝ → SpatialField → Prop}
    (hq : ∀ τ v, q (τ + P) v ↔ q τ v) (h : ∀ᵐ τ, q τ (f τ)) :
    ∀ᵐ τ, q τ (periodize hP f τ) := by
  refine B0005.ae_of_periodic hP (fun t => by rw [periodize_periodic f t, hq]) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae h] with τ hτ hτ'
  rwa [periodize_eq_of_mem f hτ]

end Periodize

/-! ## Joint measurability of spatial partial derivatives -/

/-- `∂_jU(τ, y)` is jointly measurable when `U` is jointly measurable and differentiable in
`y` at every phase: it is the pointwise limit of the difference quotients
`n (U(τ, y + e_j/n) - U(τ, y))`. -/
theorem aestronglyMeasurable_partial {U : ℝ → SpatialField}
    (hU : AEStronglyMeasurable (fun z : SpaceTime => U z.1 z.2) volume)
    (hd : ∀ τ, Differentiable ℝ (U τ)) (j : Fin 3) :
    AEStronglyMeasurable (fun z : SpaceTime => fderiv ℝ (U z.1) z.2 (coordinateVector j))
      volume := by
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hshift : ∀ c : Space, AEStronglyMeasurable (fun z : SpaceTime => U z.1 (z.2 + c))
      volume := fun c =>
    (hU.comp_measurePreserving (measurePreserving_shift 0 c)).congr
      (Eventually.of_forall fun z => by simp)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n (z : SpaceTime) => (t n)⁻¹ • (U z.1 (z.2 + t n • coordinateVector j) - U z.1 z.2))
    (fun n => by
      have h := ((hshift (t n • coordinateVector j)).sub hU).const_smul (t n)⁻¹
      exact h) (Eventually.of_forall fun z => ?_)
  have hline : HasDerivAt (fun s : ℝ => U z.1 (z.2 + s • coordinateVector j))
      (fderiv ℝ (U z.1) z.2 (coordinateVector j)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => z.2 + s • coordinateVector j) (coordinateVector j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector j)).const_add z.2
    have hU' := (hd z.1 (z.2 + (0 : ℝ) • coordinateVector j)).hasFDerivAt
    rw [zero_smul, add_zero] at hU'
    rw [show z.2 = z.2 + (0 : ℝ) • coordinateVector j by simp] at hU'
    exact hU'.comp_hasDerivAt (0 : ℝ) hl |>.congr_deriv (by simp)
  have hslope := hline.tendsto_slope_zero
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => ?_⟩
    simp only [t, mem_compl_iff, mem_singleton_iff, one_div, inv_eq_zero]
    positivity
  have := hslope.comp ht
  simpa [Function.comp_def] using this

end UnforcedLeray.Cons.C08
