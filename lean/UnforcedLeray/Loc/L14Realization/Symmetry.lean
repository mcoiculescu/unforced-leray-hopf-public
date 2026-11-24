import UnforcedLeray.Blueprint.Localization.Spaces
import UnforcedLeray.Analysis.Heat.Flow

/-!
# Step L14, helpers: `𝒪`-invariance of the heat flow and of the total field

Support for `Loc/L14Realization.lean` (step L14 `RealizationStep`, `paper/main.tex`
lines 112–115 for the group `𝒪` and lines 532–537 for the total field
`u = e^{htΔ}u₀ + ρ`; blueprint unit B1025, infrastructure INF24 "𝒪-equivariance of the heat
flow").

* `average_rotateField`: the Gaussian average commutes with every linear isometry `g`,
  `e^{sΔ}(g·f) = g·e^{sΔ}f` pointwise, since the kernel is radial and `g` preserves Lebesgue
  measure.
* `rotateField_flow`: for an `𝒪`-invariant datum, `g·e^{sΔ}u₀ = e^{sΔ}u₀` everywhere.
* `isAxisymmetricNoSwirl_congr`, `isAxisymmetricNoSwirl_add`: invariance passes to a.e. equal

  lines 121–131) and to sums.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace UnforcedLeray.Blueprint.L14

/-- The Gaussian average commutes with linear isometries. -/
theorem average_rotateField (s : ℝ) (f : SpatialField) (g : Space ≃ₗᵢ[ℝ] Space) (x : Space) :
    Heat.average s (rotateField g f) x = g (Heat.average s f (g.symm x)) := by
  unfold Heat.average rotateField
  have h1 : (fun y => Heat.kernel s y • g (f (g.symm (x - y)))) =
      fun y => g (Heat.kernel s y • f (g.symm x - g.symm y)) := by
    funext y
    rw [map_smul, map_sub]
  rw [h1, show (∫ y, g (Heat.kernel s y • f (g.symm x - g.symm y))) =
      g (∫ y, Heat.kernel s y • f (g.symm x - g.symm y)) from
    g.toLinearIsometry.integral_comp_comm _]
  congr 1
  have hmp : MeasurePreserving (g : Space → Space) volume volume := g.measurePreserving
  rw [← hmp.integral_comp g.toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [LinearIsometryEquiv.symm_apply_apply]
  congr 1
  unfold Heat.kernel Heat.Gaussian.kernel
  rw [LinearIsometryEquiv.norm_map]

/-- The heat flow of an `𝒪`-invariant datum is invariant at every point. -/
theorem rotateField_flow {u₀ : SpatialField} (hsym : IsAxisymmetricNoSwirl u₀)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) {s : ℝ} (hs : 0 < s) :
    rotateField g (Heat.flow u₀ s) = Heat.flow u₀ s := by
  funext x
  rw [Heat.flow_pos u₀ hs]
  change g (Heat.average s u₀ (g.symm x)) = Heat.average s u₀ x
  rw [← average_rotateField]
  exact congrFun (Heat.average_congr_ae (hsym g hg) s) x

theorem isAxisymmetricNoSwirl_flow {u₀ : SpatialField} (hsym : IsAxisymmetricNoSwirl u₀)
    {s : ℝ} (hs : 0 < s) : IsAxisymmetricNoSwirl (Heat.flow u₀ s) := fun _ hg =>
  EventuallyEq.of_eq (rotateField_flow hsym hg hs)

/-- `𝒪`-invariance passes to a.e. equal fields. -/
theorem isAxisymmetricNoSwirl_congr {f f' : SpatialField} (h : f =ᵐ[volume] f')
    (hf : IsAxisymmetricNoSwirl f) : IsAxisymmetricNoSwirl f' := by
  intro g hg
  have h1 : rotateField g f' =ᵐ[volume] rotateField g f := by
    have h2 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp h.symm
    filter_upwards [h2] with x hx
    simp only [rotateField]
    simp only [Function.comp_apply] at hx
    rw [hx]
  exact h1.trans ((hf g hg).trans h)

theorem isAxisymmetricNoSwirl_add {f f' : SpatialField} (hf : IsAxisymmetricNoSwirl f)
    (hf' : IsAxisymmetricNoSwirl f') : IsAxisymmetricNoSwirl (f + f') := by
  intro g hg
  have he : (fun x => g ((f + f') (g.symm x))) =
      (fun x => g (f (g.symm x))) + fun x => g (f' (g.symm x)) := by
    funext x
    simp
  rw [he]
  exact (hf g hg).add (hf' g hg)

end UnforcedLeray.Blueprint.L14
