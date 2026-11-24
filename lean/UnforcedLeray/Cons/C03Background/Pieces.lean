import UnforcedLeray.Blueprint.Construction.Steps
import UnforcedLeray.Lib.AxisymmetricB

/-!
# Theorem B3: the three pieces of the background and their sum

`paper/main.tex`, Theorem B3 (lines 5093–5141, unit B0705): the background is
`U = U_raw + E_bg α_bg + w_bg` (`background:eq:2.4`), periodic, solenoidal (`background:eq:2.5`,
`div U = 0`), in the class `background:eq:2.2`, with bounded `U` and `∇U` (`background:eq:2.7`
and line 5122, "Every fixed spatial derivative of `U` is bounded at fixed parameters").

`IsBackgroundPiece P f` collects, for one summand `f`, exactly the clauses of
`Blueprint.IsB3Core` that concern the background field: `IsBoundedBackground f`
(jointly measurable, differentiable at every phase, `f` and `∇f` bounded), `P`-periodic,
solenoidal and axisymmetric without swirl at every phase. The class is closed under sums and
scalar multiples (`IsBackgroundPiece.add`, `.const_smul`, `.lin2`), so the three pieces of
(2.4) give the clauses for `U` (assembled in `Scheme.lean`).

**Ring lifts** (`eq:m3-ring-lift`, lines 2070–2098, unit B0186; `eq:m2-background-inlet`,
lines 5146–5160). `U_raw` and the inlet columns are, off the axis, ring lifts
`𝒩_v b = √s(b_r e_r + b_z e_z)` of profiles `b(s, ξ, η)` that are `c`-periodic in `ξ`
(the library's `Axi.Nv`, `Lib/AxisymmetricB/Lift.lean`). `isBackgroundPiece_of_lift` proves
their periodicity and symmetry from the lift, with the compiled
`Axi.chart_add_period` (`Lib/Axisymmetric/RingChart.lean`: the chart shifts `ξ` by `c` when
`τ` moves by `P = 2c/R`) and `Axi.isAxisymmetricNoSwirl_Nv` (`Lib/AxisymmetricB/Range.lean`).
The field itself is the smooth Cartesian extension through the axis (line 5200, "Its smooth
Cartesian extension"); it agrees with the lift only off the axis. This matters: on the axis
the library's lift has the junk value `0` (`age = R²/0 = 0`), while the extension of
`U_raw` does not vanish there in general (its axial component tends to
`2ε lim √s ψ̄`, with `ψ̄` the cell average of the decaying stream). Periodicity on the axis
follows by continuity from the dense complement of the axis (`dense_compl_axis`), symmetry
from the a.e. equality (the axis is null, `Axi.volume_axis`).

Junk values: `fderiv` appears only for fields assumed differentiable everywhere, so the
bounds on `∇f` are bounds on genuine derivatives.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Cons.C03

open UnforcedLeray.Blueprint UnforcedLeray.Axi

/-! ## Solenoidality and symmetry are linear -/

theorem isSolenoidal_add {f g : SpatialField} (hf : IsSolenoidal f) (hg : IsSolenoidal g) :
    IsSolenoidal (f + g) := by
  have e : ∀ φ : Space → ℝ,
      (fun x => ∑ i : Fin 3, ((f + g) x) i * spatialTestDerivative i φ x) =
        fun x => (∑ i : Fin 3, (f x) i * spatialTestDerivative i φ x) +
          ∑ i : Fin 3, (g x) i * spatialTestDerivative i φ x := by
    intro φ
    funext x
    simp only [Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [e]
    exact (hf.integrable φ hφ).add (hg.integrable φ hφ)
  · rw [e, integral_add (hf.integrable φ hφ) (hg.integrable φ hφ), hf.identity φ hφ,
      hg.identity φ hφ, add_zero]

theorem isSolenoidal_const_smul {f : SpatialField} (hf : IsSolenoidal f) (a : ℝ) :
    IsSolenoidal (a • f) := by
  have e : ∀ φ : Space → ℝ,
      (fun x => ∑ i : Fin 3, ((a • f) x) i * spatialTestDerivative i φ x) =
        fun x => a * ∑ i : Fin 3, (f x) i * spatialTestDerivative i φ x := by
    intro φ
    funext x
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [e]
    exact (hf.integrable φ hφ).const_mul a
  · rw [e, integral_const_mul, hf.identity φ hφ, mul_zero]

theorem isAxisymmetricNoSwirl_add' {f f' : SpatialField} (hf : IsAxisymmetricNoSwirl f)
    (hf' : IsAxisymmetricNoSwirl f') : IsAxisymmetricNoSwirl (f + f') := by
  intro g hg
  have he : (fun x => g ((f + f') (g.symm x))) =
      (fun x => g (f (g.symm x))) + fun x => g (f' (g.symm x)) := by
    funext x
    simp
  rw [he]
  exact (hf g hg).add (hf' g hg)

theorem isAxisymmetricNoSwirl_const_smul {f : SpatialField} (hf : IsAxisymmetricNoSwirl f)
    (a : ℝ) : IsAxisymmetricNoSwirl (a • f) := by
  intro g hg
  have he : (fun x => g ((a • f) (g.symm x))) = a • fun x => g (f (g.symm x)) := by
    funext x
    simp
  rw [he]
  exact (hf g hg).const_smul a

/-- `𝒪`-invariance passes to a.e.-equal fields (adapted from
`SkeletonDesignA/LocalizationComposition.lean`, `isAxisymmetricNoSwirl_congr_ae`). -/
theorem isAxisymmetricNoSwirl_congr_ae' {f f' : SpatialField} (hf : IsAxisymmetricNoSwirl f)
    (hff' : f =ᵐ[volume] f') : IsAxisymmetricNoSwirl f' := by
  intro g hg
  have hmp : MeasurePreserving (g.symm : Space → Space) volume volume :=
    g.symm.measurePreserving
  have h1 : (f' ∘ g.symm) =ᵐ[volume] (f ∘ g.symm) :=
    hmp.quasiMeasurePreserving.ae_eq_comp hff'.symm
  have h2 : (fun x => g (f' (g.symm x))) =ᵐ[volume] (fun x => g (f (g.symm x))) := by
    filter_upwards [h1] with x hx
    simp only [Function.comp] at hx
    rw [hx]
  exact h2.trans ((hf g hg).trans hff')

/-! ## Bounded backgrounds are a linear class -/

theorem isBoundedBackground_add {U V : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (hV : IsBoundedBackground V) : IsBoundedBackground (U + V) where
  measurable := hU.measurable.add hV.measurable
  differentiable := fun τ => (hU.differentiable τ).add (hV.differentiable τ)
  bounded := by
    obtain ⟨C₁, h₁⟩ := hU.bounded
    obtain ⟨C₂, h₂⟩ := hV.bounded
    refine ⟨C₁ + C₂, fun τ y => ⟨?_, ?_⟩⟩
    · exact (norm_add_le _ _).trans (add_le_add (h₁ τ y).1 (h₂ τ y).1)
    · show ‖fderiv ℝ (U τ + V τ) y‖ ≤ C₁ + C₂
      rw [fderiv_add ((hU.differentiable τ) y) ((hV.differentiable τ) y)]
      exact (norm_add_le _ _).trans (add_le_add (h₁ τ y).2 (h₂ τ y).2)

theorem isBoundedBackground_const_smul {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (a : ℝ) : IsBoundedBackground (a • U) where
  measurable := hU.measurable.const_smul a
  differentiable := fun τ => (hU.differentiable τ).const_smul a
  bounded := by
    obtain ⟨C, h⟩ := hU.bounded
    refine ⟨|a| * C, fun τ y => ⟨?_, ?_⟩⟩
    · show ‖a • U τ y‖ ≤ |a| * C
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (h τ y).1 (abs_nonneg a)
    · show ‖fderiv ℝ (a • U τ) y‖ ≤ |a| * C
      rw [fderiv_const_smul ((hU.differentiable τ) y), norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (h τ y).2 (abs_nonneg a)

/-! ## Background pieces -/

/-- The clauses of `IsB3Core` on the background field, for one summand of
`U = U_raw + E_bg α_bg + w_bg` (`background:eq:2.4`, lines 5096–5122). -/
structure IsBackgroundPiece (P : ℝ) (f : ℝ → SpatialField) : Prop where
  /-- Jointly measurable, differentiable at every phase, `f` and `∇f` bounded
  (`background:eq:2.7`, line 5122). -/
  bounded : IsBoundedBackground f
  /-- `P`-periodic in the phase. -/
  periodic : Function.Periodic f P
  /-- Solenoidal at every phase (`background:eq:2.5`, `div U = 0`). -/
  solenoidal : ∀ τ, IsSolenoidal (f τ)
  /-- Axisymmetric without swirl at every phase (`background:eq:2.2`). -/
  symmetric : ∀ τ, IsAxisymmetricNoSwirl (f τ)

namespace IsBackgroundPiece

variable {P : ℝ}

theorem add {f g : ℝ → SpatialField} (hf : IsBackgroundPiece P f)
    (hg : IsBackgroundPiece P g) : IsBackgroundPiece P (f + g) where
  bounded := isBoundedBackground_add hf.bounded hg.bounded
  periodic := hf.periodic.add hg.periodic
  solenoidal := fun τ => isSolenoidal_add (hf.solenoidal τ) (hg.solenoidal τ)
  symmetric := fun τ => isAxisymmetricNoSwirl_add' (hf.symmetric τ) (hg.symmetric τ)

theorem const_smul {f : ℝ → SpatialField} (hf : IsBackgroundPiece P f) (a : ℝ) :
    IsBackgroundPiece P (a • f) where
  bounded := isBoundedBackground_const_smul hf.bounded a
  periodic := fun τ => by
    show a • f (τ + P) = a • f τ
    rw [hf.periodic τ]
  solenoidal := fun τ => isSolenoidal_const_smul (hf.solenoidal τ) a
  symmetric := fun τ => isAxisymmetricNoSwirl_const_smul (hf.symmetric τ) a

/-- The inlet term `E α = α₀E₀ + α₁E₁` of (2.4). -/
theorem lin2 {E : Fin 2 → ℝ → SpatialField} (hE : ∀ i, IsBackgroundPiece P (E i))
    (α : Fin 2 → ℝ) : IsBackgroundPiece P (∑ i : Fin 2, α i • E i) := by
  rw [Fin.sum_univ_two]
  exact ((hE 0).const_smul (α 0)).add ((hE 1).const_smul (α 1))

end IsBackgroundPiece

/-! ## Ring lifts: periodicity and symmetry from the chart -/

/-- The complement of the axis is dense (the axis is Lebesgue null). -/
theorem dense_compl_axis : Dense {y : Space | y ∉ axis} :=
  Measure.dense_of_ae ae_not_mem_axis

theorem age_pos {R : ℝ} (hR : R ≠ 0) {y : Space} (hy : y ∉ axis) : 0 < age R y :=
  div_pos (pow_pos (abs_pos.mpr hR) 2 |>.trans_eq (sq_abs R)) (pow_pos (ϱ_pos hy) 2)

/-- Off the axis the ring lift of a profile that is `c`-periodic in `ξ` at positive ages is
`P`-periodic in `τ`, `P = 2c/R` (`eq:m3-ring-lift`: "the period is `P = 2εc`"). Only the
ages `s = R²/ϱ² > 0` enter, so the profile need not be defined at `s ≤ 0`. -/
theorem Nv_add_period_of_not_mem_axis {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R)
    {b : ℝ × (ℝ × ℝ) → Merid} (hper : ∀ s, 0 < s → ∀ ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η)))
    (τ : ℝ) {y : Space} (hy : y ∉ axis) : Nv R b (τ + P) y = Nv R b τ y := by
  rw [Nv, Nv, chart_add_period hR hP, hper _ (age_pos hR hy)]
  rfl

/-- A field that agrees off the axis with the ring lift of a profile `c`-periodic in `ξ`, and
is continuous in `y`, is `P`-periodic in `τ` (`P = 2c/R`). -/
theorem periodic_of_lift {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R)
    {b : ℝ × (ℝ × ℝ) → Merid} (hper : ∀ s, 0 < s → ∀ ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η)))
    {f : ℝ → SpatialField} (hlift : ∀ τ y, y ∉ axis → f τ y = Nv R b τ y)
    (hcont : ∀ τ, Continuous (f τ)) : Function.Periodic f P := by
  intro τ
  refine Continuous.ext_on dense_compl_axis (hcont (τ + P)) (hcont τ) ?_
  intro y hy
  rw [hlift _ _ hy, hlift _ _ hy, Nv_add_period_of_not_mem_axis hR hP hper τ hy]

/-- A field that agrees off the axis with a ring lift is axisymmetric without swirl at every
phase (`Axi.isAxisymmetricNoSwirl_Nv`; the axis is null). -/
theorem symmetric_of_lift {R : ℝ} {b : ℝ × (ℝ × ℝ) → Merid} {f : ℝ → SpatialField}
    (hlift : ∀ τ y, y ∉ axis → f τ y = Nv R b τ y) (τ : ℝ) :
    IsAxisymmetricNoSwirl (f τ) := by
  refine isAxisymmetricNoSwirl_congr_ae' (isAxisymmetricNoSwirl_Nv R b τ) ?_
  filter_upwards [ae_not_mem_axis] with y hy
  exact (hlift τ y hy).symm

/-- **A lifted piece** (`eq:m3-ring-lift`, `eq:m2-background-inlet`): a bounded solenoidal
field agreeing off the axis with the ring lift of a profile `c`-periodic in `ξ` is a
background piece of period `P = 2c/R`. -/
theorem isBackgroundPiece_of_lift {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R)
    {b : ℝ × (ℝ × ℝ) → Merid} (hper : ∀ s, 0 < s → ∀ ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η)))
    {f : ℝ → SpatialField} (hlift : ∀ τ y, y ∉ axis → f τ y = Nv R b τ y)
    (hb : IsBoundedBackground f) (hsol : ∀ τ, IsSolenoidal (f τ)) :
    IsBackgroundPiece P f where
  bounded := hb
  periodic := periodic_of_lift hR hP hper hlift fun τ => (hb.differentiable τ).continuous
  solenoidal := hsol
  symmetric := symmetric_of_lift hlift

end UnforcedLeray.Cons.C03
