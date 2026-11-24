import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Cylindrical reduction of `ℝ³` integrals for `FarMajorantL2` (source 2666-2668)

Axisymmetric integrals over `ℝ³` are reduced to the half plane: the coordinates
`y ↦ ((y₀,y₁),y₂)` are measure preserving, Tonelli separates the height `y₂`, and the planar
polar change of variables `(q₁,q₂) = (ρcos φ, ρ sin φ)` turns the axisymmetric integrand into
`ρ` times a function of `(ρ, y₂)`, with the azimuth integral giving `2π`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The point of `ℝ³` with coordinates `(q₁, q₂, t)` for `p = ((q₁,q₂),t)`. -/
def polarRedPt (p : (ℝ × ℝ) × ℝ) : UnforcedLeray.Space :=
  WithLp.toLp 2 ![p.1.1, p.1.2, p.2]

theorem polarRedPt_zero (a b c : ℝ) : polarRedPt ((a, b), c) 0 = a := rfl

theorem polarRedPt_one (a b c : ℝ) : polarRedPt ((a, b), c) 1 = b := rfl

theorem polarRedPt_two (a b c : ℝ) : polarRedPt ((a, b), c) 2 = c := rfl

theorem polarRed_comp (y : UnforcedLeray.Space) :
    polarRedPt ((y 0, y 1), y 2) = y := by
  ext i
  fin_cases i <;> rfl

theorem polarRed_measurable_pt : Measurable polarRedPt := by
  have hv : Measurable (fun p : (ℝ × ℝ) × ℝ => (![p.1.1, p.1.2, p.2] : Fin 3 → ℝ)) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp hv

/-- `y ↦ ((y₀,y₁),y₂)` is measure preserving from `ℝ³` to `(ℝ×ℝ)×ℝ`. -/
theorem polarRed_coords :
    MeasurePreserving (fun y : UnforcedLeray.Space => ((y 0, y 1), y 2)) volume volume := by
  have h0 : (fun y : UnforcedLeray.Space => (y 2, (y 0, y 1))) =
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2) ∘ WithLp.ofLp := by
    funext y
    rfl
  have hG0 : MeasurePreserving (fun y : UnforcedLeray.Space => (y 2, (y 0, y 1)))
      volume volume := by
    rw [h0]
    have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_finTwoArrow ℝ)
    have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
    have h3 := PiLp.volume_preserving_ofLp (Fin 3)
    exact (h1.comp h2).comp h3
  exact (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (ℝ × ℝ)))).comp hG0

/-- **Pointwise reduction of an axisymmetric integral over `ℝ³` to the half plane**
(source 2666-2668): `∫_{|y'|>lo} H = 2π ∫_{ρ>lo} ∫_t ρ H(ρ,0,t)`. -/
theorem polarReduction_holds : PolarReduction := by
  intro H hH hax lo hlo
  have hc0 : Continuous (fun z : UnforcedLeray.Space => z 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).continuous
  have hc1 : Continuous (fun z : UnforcedLeray.Space => z 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).continuous
  have hRadc : Continuous hRad := by
    unfold hRad
    exact Real.continuous_sqrt.comp ((hc0.pow 2).add (hc1.pow 2))
  set S : Set UnforcedLeray.Space := {y | lo < hRad y} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const hRadc.measurable
  have hmem : ∀ z : UnforcedLeray.Space, z ∈ S ↔ lo < hRad z := fun z => Iff.rfl
  have hpt : Measurable polarRedPt := polarRed_measurable_pt
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ => S.indicator H (polarRedPt p)) :=
    (hH.indicator hS).comp hpt
  -- Step 1: move to the coordinates `((y₀,y₁),y₂)`.
  have step1 : ∫⁻ y in S, H y = ∫⁻ p : (ℝ × ℝ) × ℝ, S.indicator H (polarRedPt p) := by
    have h := polarRed_coords.lintegral_comp hm
    rw [← lintegral_indicator hS H, ← h]
    refine lintegral_congr (fun y => ?_)
    simp only [polarRed_comp]
  -- Step 2: Tonelli, the planar factor is the outer variable.
  have step2 : ∫⁻ p : (ℝ × ℝ) × ℝ, S.indicator H (polarRedPt p) =
      ∫⁻ q : ℝ × ℝ, ∫⁻ t : ℝ, S.indicator H (polarRedPt (q, t)) := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  -- Step 3: planar polar coordinates.
  have step3 : ∫⁻ q : ℝ × ℝ, ∫⁻ t : ℝ, S.indicator H (polarRedPt (q, t)) =
      ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 *
        ∫⁻ t : ℝ, S.indicator H (polarRedPt (polarCoord.symm p, t)) := by
    have h := lintegral_comp_polarCoord_symm
      (fun q : ℝ × ℝ => ∫⁻ t : ℝ, S.indicator H (polarRedPt (q, t)))
    simp only [smul_eq_mul] at h
    exact h.symm
  -- The integrand at a polar point is axisymmetric.
  have key : ∀ ρ φ t : ℝ, 0 < ρ →
      S.indicator H (polarRedPt ((ρ * Real.cos φ, ρ * Real.sin φ), t)) =
        if lo < ρ then H (ptOf ρ t) else 0 := by
    intro ρ φ t hρ
    have hr : hRad (polarRedPt ((ρ * Real.cos φ, ρ * Real.sin φ), t)) = ρ := by
      unfold hRad
      rw [polarRedPt_zero, polarRedPt_one]
      have h2 : (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 = ρ ^ 2 := by
        linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq φ
      rw [h2, Real.sqrt_sq hρ.le]
    have hr' : hRad (ptOf ρ t) = ρ := by
      unfold hRad
      rw [show ptOf ρ t 0 = ρ from rfl, show ptOf ρ t 1 = (0 : ℝ) from rfl]
      rw [show ρ ^ 2 + (0 : ℝ) ^ 2 = ρ ^ 2 by ring, Real.sqrt_sq hρ.le]
    have hval : H (polarRedPt ((ρ * Real.cos φ, ρ * Real.sin φ), t)) = H (ptOf ρ t) :=
      hax _ _ (hr.trans hr'.symm) ((polarRedPt_two _ _ _).trans rfl)
    by_cases h : lo < ρ
    · simp [hmem, hr, h, hval]
    · simp [hmem, hr, h]
  -- Step 5: the integrand on the target.
  have step5 : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 *
        ∫⁻ t : ℝ, S.indicator H (polarRedPt (polarCoord.symm p, t)) =
      ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 *
        ∫⁻ t : ℝ, (if lo < p.1 then H (ptOf p.1 t) else 0) := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    have hp' : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := hp
    have hp0 : 0 < p.1 := hp'.1
    have hsym : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
    simp only [hsym]
    congr 1
    exact lintegral_congr (fun t => key p.1 p.2 t hp0)
  -- The radial profile `F`.
  set F : ℝ → ℝ≥0∞ := fun ρ =>
    ENNReal.ofReal ρ * ∫⁻ t : ℝ, (if lo < ρ then H (ptOf ρ t) else 0) with hF
  have hptm : Measurable (fun z : ℝ × ℝ => ptOf z.1 z.2) :=
    hpt.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hJ : Measurable (fun z : ℝ × ℝ => if lo < z.1 then H (ptOf z.1 z.2) else 0) := by
    refine Measurable.ite ?_ (hH.comp hptm) measurable_const
    exact measurableSet_lt measurable_const measurable_fst
  have hG : Measurable (fun ρ : ℝ => ∫⁻ t : ℝ, (if lo < ρ then H (ptOf ρ t) else 0)) :=
    hJ.lintegral_prod_right'
  have hFm : Measurable F := ENNReal.measurable_ofReal.mul hG
  -- Step 6: the azimuth integral gives `2π`.
  have step6 : ∫⁻ p in polarCoord.target, F p.1 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ ρ in Ioi (0 : ℝ), F ρ := by
    have hvol : volume (Ioo (-Real.pi) Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
      rw [Real.volume_Ioo]
      congr 1
      ring
    have htar : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
    rw [htar, Measure.volume_eq_prod,
      setLIntegral_prod (fun p : ℝ × ℝ => F p.1) (hFm.comp measurable_fst).aemeasurable]
    simp only [setLIntegral_const, hvol]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
  -- Step 7: the support of `F` lies in `(lo, ∞)`.
  have hsupp : Function.support F ⊆ Ioi lo := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    rw [mem_Ioi]
    by_contra hc
    apply hρ
    simp [hF, hc]
  have step7a : ∫⁻ ρ in Ioi (0 : ℝ), F ρ = ∫⁻ ρ in Ioi lo, F ρ := by
    rw [setLIntegral_eq_of_support_subset (hsupp.trans (Ioi_subset_Ioi hlo)),
      setLIntegral_eq_of_support_subset hsupp]
  have step7b : ∫⁻ ρ in Ioi lo, F ρ =
      ∫⁻ ρ in Ioi lo, ∫⁻ t : ℝ, ENNReal.ofReal ρ * H (ptOf ρ t) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
    have h : lo < ρ := hρ
    simp only [hF, if_pos h]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ y in S, H y = ∫⁻ p : (ℝ × ℝ) × ℝ, S.indicator H (polarRedPt p) := step1
    _ = ∫⁻ q : ℝ × ℝ, ∫⁻ t : ℝ, S.indicator H (polarRedPt (q, t)) := step2
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 *
          ∫⁻ t : ℝ, S.indicator H (polarRedPt (polarCoord.symm p, t)) := step3
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 *
          ∫⁻ t : ℝ, (if lo < p.1 then H (ptOf p.1 t) else 0) := step5
    _ = ∫⁻ p in polarCoord.target, F p.1 := rfl
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ ρ in Ioi (0 : ℝ), F ρ := step6
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ ρ in Ioi lo, F ρ := by rw [step7a]
    _ = ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ ρ in Ioi lo, ∫⁻ t : ℝ, ENNReal.ofReal ρ * H (ptOf ρ t) := by rw [step7b]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
