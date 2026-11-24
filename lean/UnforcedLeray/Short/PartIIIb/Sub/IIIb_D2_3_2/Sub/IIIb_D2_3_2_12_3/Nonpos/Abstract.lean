import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.Lin.Helpers

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/5`: abstract continuity of an iterated phase integral with a junk term

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

For `ρb ≤ 0` the second component of `StrG` is the zero space, and its coercion is a fixed
(measurable) junk function `J`.  The value `phaseInt P (a x + J)` is the iterated integral
`P⁻¹ ∫_t ∫_y (a x + J)`; it is continuous in `x` whenever `a x` are integrable on the phase cell
and `x ↦ a x` is Lipschitz for the `L¹(cell)` norm.  Fibrewise, the `y`-integral of the sum is the
sum of the `y`-integrals for `t` in the (measurable) set where `J(t, ·)` is integrable, and `0`
elsewhere; the outer integral is then either affine-Lipschitz in `a x` or identically `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (phaseInt phaseCell)

theorem phaseCell_measure_eq (P : ℝ) :
    (volume : Measure (ℝ × Space)).restrict (phaseCell P)
      = (volume.restrict (Ioc 0 P)).prod (volume : Measure Space) := by
  rw [show phaseCell P = Ioc 0 P ×ˢ univ from rfl, Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ]

theorem phaseInt_add_cont_of {X : Type*} [PseudoMetricSpace X] {P : ℝ}
    (a : X → ℝ × Space → ℂ) (J : ℝ × Space → ℂ) (hJ : Measurable J)
    (hint : ∀ x, Integrable (a x) (volume.restrict (phaseCell P))) (C : ℝ)
    (hL : ∀ x x', ∫ z, ‖a x z - a x' z‖ ∂(volume.restrict (phaseCell P)) ≤ C * dist x x') :
    Continuous fun x => phaseInt P (fun z => a x z + J z) := by
  set μt : Measure ℝ := volume.restrict (Ioc (0 : ℝ) P) with hμt
  have hm : (volume : Measure (ℝ × Space)).restrict (phaseCell P) = μt.prod volume :=
    phaseCell_measure_eq P
  have hint' : ∀ x, Integrable (a x) (μt.prod volume) := fun x => hm ▸ hint x
  set S : Set ℝ := {t | Integrable (fun y => J (t, y))} with hSdef
  have hS : MeasurableSet S := by
    have hmeas : Measurable fun t : ℝ => ∫⁻ y, ‖J (t, y)‖ₑ := by
      have : Measurable fun z : ℝ × Space => ‖J z‖ₑ := hJ.enorm
      exact this.lintegral_prod_right'
    have : S = {t | (∫⁻ y, ‖J (t, y)‖ₑ) < ⊤} := by
      ext t
      simp only [hSdef, mem_setOf_eq]
      constructor
      · intro h; exact h.2
      · intro h
        exact ⟨(hJ.comp measurable_prodMk_left).aestronglyMeasurable, h⟩
    rw [this]
    exact measurableSet_lt hmeas measurable_const
  -- fibrewise decomposition
  have hae : ∀ x, (fun t => ∫ y : Space, (a x (t, y) + J (t, y))) =ᵐ[μt]
      fun t => S.indicator (fun t => ∫ y : Space, a x (t, y)) t + ∫ y : Space, J (t, y) := by
    intro x
    filter_upwards [(hint' x).prod_right_ae] with t ht
    by_cases hts : t ∈ S
    · rw [Set.indicator_of_mem hts, integral_add ht hts]
    · rw [Set.indicator_of_notMem hts, zero_add]
      have hnj : ¬ Integrable (fun y => J (t, y)) := hts
      have hns : ¬ Integrable (fun y => a x (t, y) + J (t, y)) := by
        intro h
        apply hnj
        refine (h.sub ht).congr (Eventually.of_forall fun y => ?_)
        simp
      rw [integral_undef hns, integral_undef hnj]
  have hindint : ∀ x, Integrable (S.indicator (fun t => ∫ y : Space, a x (t, y))) μt := fun x =>
    ((hint' x).integral_prod_left).indicator hS
  by_cases hB : Integrable (fun t => ∫ y : Space, J (t, y)) μt
  · -- affine case
    have hval : ∀ x, phaseInt P (fun z => a x z + J z) =
        P⁻¹ • (∫ t, S.indicator (fun t => ∫ y : Space, a x (t, y)) t ∂μt + ∫ t, (∫ y : Space, J (t, y)) ∂μt) := by
      intro x
      unfold phaseInt
      congr 1
      rw [← integral_add (hindint x) hB]
      exact integral_congr_ae (hae x)
    have hLip : ∀ x x', ‖∫ t, S.indicator (fun t => ∫ y : Space, a x (t, y)) t ∂μt -
        ∫ t, S.indicator (fun t => ∫ y : Space, a x' (t, y)) t ∂μt‖ ≤ C * dist x x' := by
      intro x x'
      rw [← integral_sub (hindint x) (hindint x')]
      have hd : Integrable (fun z => a x z - a x' z) (μt.prod volume) := (hint' x).sub (hint' x')
      have h1 : ‖∫ t, (S.indicator (fun t => ∫ y : Space, a x (t, y)) t -
          S.indicator (fun t => ∫ y : Space, a x' (t, y)) t) ∂μt‖ ≤
          ∫ t, (∫ y : Space, ‖a x (t, y) - a x' (t, y)‖) ∂μt := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_ae ((hindint x).sub (hindint x')).norm
          hd.norm.integral_prod_left ?_
        filter_upwards [(hint' x).prod_right_ae, (hint' x').prod_right_ae] with t h1 h2
        by_cases hts : t ∈ S
        · simp only [Set.indicator_of_mem hts]
          rw [← integral_sub h1 h2]
          exact norm_integral_le_integral_norm _
        · simp only [Set.indicator_of_notMem hts, sub_zero, norm_zero]
          exact integral_nonneg fun y => norm_nonneg _
      refine h1.trans ?_
      have h2 : ∫ t, (∫ y : Space, ‖a x (t, y) - a x' (t, y)‖) ∂μt =
          ∫ z, ‖a x z - a x' z‖ ∂(μt.prod volume) :=
        (integral_prod (fun z => ‖a x z - a x' z‖) hd.norm).symm
      rw [h2, ← hm]
      exact hL x x'
    have hLc : Continuous fun x => ∫ t, S.indicator (fun t => ∫ y : Space, a x (t, y)) t ∂μt := by
      refine LipschitzWith.continuous (K := C.toNNReal) (LipschitzWith.of_dist_le_mul fun x x' => ?_)
      rw [dist_eq_norm]
      refine (hLip x x').trans ?_
      have : C ≤ ((C.toNNReal : NNReal) : ℝ) := by
        simp [Real.coe_toNNReal']
      exact mul_le_mul_of_nonneg_right this dist_nonneg
    have : (fun x => phaseInt P (fun z => a x z + J z)) =
        fun x => P⁻¹ • (∫ t, S.indicator (fun t => ∫ y : Space, a x (t, y)) t ∂μt +
          ∫ t, (∫ y : Space, J (t, y)) ∂μt) := funext hval
    rw [this]
    exact (hLc.add continuous_const).const_smul P⁻¹
  · -- constant case
    have hval : ∀ x, phaseInt P (fun z => a x z + J z) = 0 := by
      intro x
      unfold phaseInt
      have hn : ¬ Integrable (fun t => ∫ y : Space, (a x (t, y) + J (t, y))) μt := by
        intro h
        apply hB
        have h' : Integrable (fun t => S.indicator (fun t => ∫ y : Space, a x (t, y)) t +
            ∫ y : Space, J (t, y)) μt := h.congr (hae x)
        refine (h'.sub (hindint x)).congr (Eventually.of_forall fun t => ?_)
        simp
      rw [integral_undef hn, smul_zero]
    have : (fun x => phaseInt P (fun z => a x z + J z)) = fun _ => 0 := funext hval
    rw [this]
    exact continuous_const

end UnforcedLeray.Short.PartIIIb.Concrete
