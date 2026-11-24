import UnforcedLeray.Lib.LerayC.Transfer
import UnforcedLeray.Loc.L12Equivariance.Rotation

/-!
# The `L^p` Leray projection commutes with the orthogonal group (INF01 T16, `𝒪`-equivariance)

Blueprint: INF01 target T16 (`lerayLp_fixesAxis`) of


Manuscript: the action `(g·f)(x) = g f(g⁻¹x)` of the group `𝒪` of linear isometries fixing `e₃`
(`paper/main.tex` lines 112–115; `Statement.lean`, `FixesAxis`, `IsAxisymmetricNoSwirl`);
unit B0440 (`eq:m3-free-graph`, lines 3247–3255: "`R_{ζ,ν}` … preserves `𝒪`-invariant fields
(`P` commutes with `𝒪`)").

* `rotLp p g`: `F ↦ g F(g⁻¹ ·)` on `L^p(R³;R³)` for a linear isometry `g` of `R³`;
* `lerayLp_isometry` (**T16**): `𝔓 (g·F) = g·(𝔓F)` for every linear isometry `g` (no axis
  condition is needed); `lerayLp_fixesAxis` is the case `g ∈ 𝒪`;
* `lerayLp_isAxisymmetricNoSwirl`: `𝔓` maps `𝒪`-invariant `L^p` fields to `𝒪`-invariant fields.

Proof: the `L²` statement is `Blueprint.L12.projection_rotL2`

the transfer principle `lerayLp_comm_of_projection_comm`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The action `F ↦ g F(g⁻¹ ·)` of a linear isometry `g` of `R³` on `L^p(R³;R³)`. -/
def rotLp (g : Space ≃ₗᵢ[ℝ] Space) :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space) :=
  (g.toLinearIsometry.toContinuousLinearMap.compLpL p volume).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (g.symm : Space → Space)
      g.symm.measurePreserving).toContinuousLinearMap

theorem coeFn_rotLp (g : Space ≃ₗᵢ[ℝ] Space) (F : Lp Space p (volume : Measure Space)) :
    (rotLp p g F : SpatialField) =ᵐ[volume] fun x => g (F (g.symm x)) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (μ := volume) (p := p)
    g.toLinearIsometry.toContinuousLinearMap
    (Lp.compMeasurePreserving (g.symm : Space → Space) g.symm.measurePreserving F)
  have h2 := Lp.coeFn_compMeasurePreserving F g.symm.measurePreserving
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  simp only [hx, Function.comp_apply]
  rfl

/-- **INF01 T16 (`𝒪`-equivariance).** For `1 < p < ∞` and every linear isometry `g` of `R³`,
`𝔓 (g·F) = g·(𝔓F)` on `L^p(R³;R³)` (B0440, `paper/main.tex` lines 3247–3255). -/
theorem lerayLp_isometry (hp1 : 1 < p) (hp : p ≠ ⊤) (g : Space ≃ₗᵢ[ℝ] Space) :
    (lerayLp p hp1 hp).comp (rotLp p g) = (rotLp p g).comp (lerayLp p hp1 hp) := by
  refine lerayLp_comp_eq_of_projection_comm hp1 hp _ (B := Blueprint.L12.rotL2 g)
    (fun u v huv => ?_) (fun v => Blueprint.L12.projection_rotL2 g v)
  refine (coeFn_rotLp g u).trans (EventuallyEq.trans ?_ (Blueprint.L12.rotL2_ae g v).symm)
  exact Blueprint.L12.rotateField_congr g huv

/-- Pointwise form of `lerayLp_isometry`. -/
theorem lerayLp_rotLp (hp1 : 1 < p) (hp : p ≠ ⊤) (g : Space ≃ₗᵢ[ℝ] Space)
    (F : Lp Space p (volume : Measure Space)) :
    lerayLp p hp1 hp (rotLp p g F) = rotLp p g (lerayLp p hp1 hp F) := by
  have h := congrArg (fun T : Lp Space p (volume : Measure Space) →L[ℝ]
    Lp Space p (volume : Measure Space) => T F) (lerayLp_isometry hp1 hp g)
  simpa using h

/-- **INF01 T16 (`lerayLp_fixesAxis`).** The case `g ∈ 𝒪` (a linear isometry fixing `e₃`) of
`lerayLp_isometry`; the axis condition is not used. -/
theorem lerayLp_fixesAxis (hp1 : 1 < p) (hp : p ≠ ⊤) (g : Space ≃ₗᵢ[ℝ] Space)
    (_hg : FixesAxis g) :
    (lerayLp p hp1 hp).comp (rotLp p g) = (rotLp p g).comp (lerayLp p hp1 hp) :=
  lerayLp_isometry hp1 hp g

/-- **`𝔓` preserves `𝒪`-invariant fields** (B0440, `paper/main.tex` lines 3247–3255): if
`F ∈ L^p(R³;R³)`, `1 < p < ∞`, is axisymmetric without swirl (`IsAxisymmetricNoSwirl` of
`Statement.lean`: `g F(g⁻¹·) = F` a.e. for every `g ∈ 𝒪`), so is `𝔓F`. -/
theorem lerayLp_isAxisymmetricNoSwirl (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : Lp Space p (volume : Measure Space)) (hF : IsAxisymmetricNoSwirl (F : SpatialField)) :
    IsAxisymmetricNoSwirl (lerayLp p hp1 hp F : SpatialField) := by
  intro g hg
  have hrot : rotLp p g F = F := Lp.ext ((coeFn_rotLp g F).trans (hF g hg))
  have h := lerayLp_rotLp hp1 hp g F
  rw [hrot] at h
  have h2 := coeFn_rotLp g (lerayLp p hp1 hp F)
  rw [← h] at h2
  exact h2.symm

end UnforcedLeray.RieszLp
