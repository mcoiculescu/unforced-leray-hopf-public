import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_A2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd

/-!
# `PairBound` (task `PartIII-b:C/near/pins/3/3/1/2`)

Source `the November 2 reference manuscript` 2666-2668, 2683-2689, 1640-1641.
For a solenoidal phase test `Φ` with period `P = 2εc`, the pairing with the physical velocity of
an `L²` chart field `f` is integrable on the phase cell and bounded by `C ‖f‖_{L²(ageμ c (-3/2))}`.
The proof uses `‖dotL a b‖ ≤ 3‖a‖‖b‖`, a compact-indicator majorant `g` of `‖Φ‖` on the cell,
Hölder on the cell, the norm identity `fwuB_norm_velPhys`, and `eLpNorm_liftFun`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

def PairBoundPh : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
    ∃ C : ℝ, ∀ f : Chart → Merid, Measurable f → MemLp f 2 (ageμ c (-3 / 2)) →
      Integrable (fun x : ℝ × Space => dotL (Φ x) (velPhys ε⁻¹ c f x))
        (volume.restrict (Ioc (0 : ℝ) (2 * ε * c) ×ˢ (univ : Set Space))) ∧
      ‖pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f)‖ ≤ C * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal

/-- **Leaf C (linearity and well-definedness)**: the pairing is additive and real-homogeneous in
`L²` chart fields (`wda_velPhys_eq`, `liftFun` linearity, with `PairBoundPh` integrability), and
depends only on the `ageμ c (-3/2)`-class of `f`, even for a non-measurable representative `f`
(`wda_velPhys_congr` for measurable ones; a null set of chart points has null preimage in the
phase cell). -/
def PairLinearPh : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
    (∀ f f' : Chart → Merid, Measurable f → Measurable f' →
      MemLp f 2 (ageμ c (-3 / 2)) → MemLp f' 2 (ageμ c (-3 / 2)) →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (f + f')) =
        pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f) + pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f')) ∧
    (∀ (a : ℝ) (f : Chart → Merid), Measurable f → MemLp f 2 (ageμ c (-3 / 2)) →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (a • f)) =
        a • pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f)) ∧
    (∀ f f' : Chart → Merid, Measurable f' → f =ᵐ[ageμ c (-3 / 2)] f' →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f) = pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f'))

/-- **Leaf D (bounded real functional on `L²`)**: `PairBoundPh` and `PairLinearPh` give a bounded
real-linear functional `L` on `Lp Merid 2 (ageμ c (-3/2))` (take a strongly measurable
representative of each class, `LinearMap.mkContinuous`), computing the pairing of every
representative. -/
def RealPairFunctionalPh : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
    ∃ L : Lp Merid 2 (ageμ c (-3 / 2)) →L[ℝ] ℂ,
      ∀ (b : Lp Merid 2 (ageμ c (-3 / 2))) (f : Chart → Merid),
        f =ᵐ[ageμ c (-3 / 2)] (b : Chart → Merid) →
          L b = pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f)


theorem pbp_norm_dotL_le (a b : CVec3) : ‖dotL a b‖ ≤ 3 * ‖a‖ * ‖b‖ := by
  rw [dotL_apply]
  have hi : ∀ (v : CVec3) (i : Fin 3), ‖v i‖ ≤ ‖v‖ := fun v i => PiLp.norm_apply_le v i
  calc ‖∑ i : Fin 3, a i * b i‖ ≤ ∑ i : Fin 3, ‖a i * b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖a‖ * ‖b‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]; exact mul_le_mul (hi a i) (hi b i) (norm_nonneg _) (norm_nonneg _)
    _ = 3 * ‖a‖ * ‖b‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- The real square-root form of the `L²` norm. -/
theorem pbp_toReal_eLpNorm {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal = (∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun a =>
      Real.rpow_nonneg (norm_nonneg _) _) _)]
  simp only [ENNReal.toReal_ofNat]

theorem pairBoundPh : PairBoundPh := by
  intro c ε hc hε Φ hΦ
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP0 : 0 < 2 * ε * c := by positivity
  haveI : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hPR : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  set P : ℝ := 2 * ε * c with hPdef
  obtain ⟨R0, hR0⟩ := hΦ.bounded_support
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  set K : Set (ℝ × Space) := Icc (0 : ℝ) P ×ˢ closedBall (0 : Space) R0 with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hKc.measurableSet
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn hΦc.continuousOn
  set M : ℝ := max C0 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  set g : ℝ × Space → ℝ := K.indicator fun _ => M with hgdef
  have hgnn : ∀ x, 0 ≤ g x := fun x => Set.indicator_nonneg (fun _ _ => hM0) x
  have hcellm : MeasurableSet (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  set μ : Measure (ℝ × Space) := volume.restrict (phaseCell P) with hμdef
  have hKfin : μ K ≠ ∞ := by
    rw [hμdef, Measure.restrict_apply hKm]
    exact (lt_of_le_of_lt (measure_mono inter_subset_left) hKc.measure_lt_top).ne
  have hgL : MemLp g 2 μ := memLp_indicator_const 2 hKm M (Or.inr hKfin)
  -- pointwise domination of `Φ` on the cell
  have hgw : ∀ᵐ x ∂μ, ‖Φ x‖ ≤ g x := by
    rw [hμdef]
    refine ae_restrict_of_forall_mem hcellm ?_
    intro x hx
    obtain ⟨hx1, -⟩ := hx
    by_cases hxK : x ∈ K
    · show ‖Φ x‖ ≤ K.indicator (fun _ => M) x
      rw [indicator_of_mem hxK]
      exact le_trans (hC0 x hxK) (le_max_left _ _)
    · have hx2 : R0 < ‖x.2‖ := by
        by_contra h
        push_neg at h
        exact hxK ⟨Ioc_subset_Icc_self hx1, mem_closedBall_zero_iff.2 h⟩
      have h0 : Φ x = 0 := hR0 x.1 x.2 hx2
      rw [h0, norm_zero]
      exact hgnn x
  set A : ℝ := (eLpNorm g 2 μ).toReal with hAdef
  set κ : ℝ := Real.sqrt Real.pi * ε⁻¹ * P ^ ((2 : ℝ)⁻¹) with hκdef
  refine ⟨P⁻¹ * (3 * A * κ), fun f hf hfL => ?_⟩
  have hfL' : MemLp (liftFun ε⁻¹ c f) 2 (phaseμ P) := fwuB_memLp_liftFun hR hc hPR hf hfL
  have hvel : MemLp (velPhys ε⁻¹ c f) 2 (phaseμ P) := fwuB_memLp_velPhys hR hf hfL'
  have hμeq : μ = ENNReal.ofReal P • phaseμ P := by
    rw [wda_phaseμ_eq P, smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hP0).ne'
      ENNReal.ofReal_ne_top, one_smul]
  have hwμ : MemLp (velPhys ε⁻¹ c f) 2 μ := by
    rw [hμeq]
    exact hvel.smul_measure ENNReal.ofReal_ne_top
  have hwn : MemLp (fun x => ‖velPhys ε⁻¹ c f x‖) 2 μ := hwμ.norm
  have hint : Integrable (fun x : ℝ × Space => dotL (Φ x) (velPhys ε⁻¹ c f x)) μ :=
    fwuB_integrable_dotL hΦc ⟨R0, hR0⟩ hwμ
  have hI2 : Integrable (fun x => g x * ‖velPhys ε⁻¹ c f x‖) μ :=
    MemLp.integrable_mul hgL hwn
  refine ⟨hint, ?_⟩
  have hpair : pairF P Φ (velPhys ε⁻¹ c f) = P⁻¹ • ∫ x, dotL (Φ x) (velPhys ε⁻¹ c f x) ∂μ :=
    pairF_eq_restrictedProductIntegral hint
  have hdom : ∫ x, ‖dotL (Φ x) (velPhys ε⁻¹ c f x)‖ ∂μ ≤
      3 * ∫ x, g x * ‖velPhys ε⁻¹ c f x‖ ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hint.norm (hI2.const_mul 3)
    filter_upwards [hgw] with x hx
    calc ‖dotL (Φ x) (velPhys ε⁻¹ c f x)‖ ≤ 3 * ‖Φ x‖ * ‖velPhys ε⁻¹ c f x‖ :=
          pbp_norm_dotL_le _ _
      _ ≤ 3 * (g x * ‖velPhys ε⁻¹ c f x‖) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            (by norm_num)
  have hH : ∫ x, g x * ‖velPhys ε⁻¹ c f x‖ ∂μ ≤
      A * (eLpNorm (velPhys ε⁻¹ c f) 2 μ).toReal := by
    have h2 : MemLp g (ENNReal.ofReal 2) μ := by rw [ENNReal.ofReal_ofNat]; exact hgL
    have h3 : MemLp (fun x => ‖velPhys ε⁻¹ c f x‖) (ENNReal.ofReal 2) μ := by
      rw [ENNReal.ofReal_ofNat]; exact hwn
    have hC := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2)
      Real.HolderConjugate.two_two h2 h3
    have hgn : ∀ x, ‖g x‖ = g x := fun x => Real.norm_of_nonneg (hgnn x)
    have eA := pbp_toReal_eLpNorm hgL
    have eB := pbp_toReal_eLpNorm hwμ
    simp only [hgn, norm_norm, one_div] at hC eA
    rw [hAdef, eA, eB]
    exact hC
  have hn : eLpNorm (velPhys ε⁻¹ c f) 2 μ =
      ENNReal.ofReal (Real.sqrt Real.pi * ε⁻¹) * ((ENNReal.ofReal P) ^ ((1 : ℝ≥0∞) / 2).toReal *
        eLpNorm (liftFun ε⁻¹ c f) 2 (phaseμ P)) := by
    have e1 : eLpNorm (velPhys ε⁻¹ c f) 2 μ =
        eLpNorm (fun x => (Real.sqrt Real.pi * ε⁻¹) * ‖liftFun ε⁻¹ c f x‖) 2 μ := by
      apply eLpNorm_congr_norm_ae
      exact ae_of_all _ fun x => by
        rw [fwuB_norm_velPhys hR f x,
          Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR.le) (norm_nonneg _))]
    have e2 : eLpNorm (fun x => (Real.sqrt Real.pi * ε⁻¹) * ‖liftFun ε⁻¹ c f x‖) 2 μ =
        ‖Real.sqrt Real.pi * ε⁻¹‖ₑ * eLpNorm (fun x => ‖liftFun ε⁻¹ c f x‖) 2 μ :=
      eLpNorm_const_smul (Real.sqrt Real.pi * ε⁻¹) (fun x => ‖liftFun ε⁻¹ c f x‖) 2 μ
    rw [eLpNorm_norm] at e2
    rw [e1, e2, Real.enorm_eq_ofReal (mul_nonneg (Real.sqrt_nonneg _) hR.le), hμeq,
      eLpNorm_smul_measure_of_ne_zero (ENNReal.ofReal_pos.2 hP0).ne', smul_eq_mul]
  have hz : ((1 : ℝ≥0∞) / 2).toReal = 2⁻¹ := by
    norm_num [ENNReal.toReal_div]
  have hB : (eLpNorm (velPhys ε⁻¹ c f) 2 μ).toReal =
      κ * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal := by
    rw [hn, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg (Real.sqrt_nonneg _) hR.le), ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hP0.le,
      hz, eLpNorm_liftFun hR hc hPR hf, hκdef]
    ring
  have hpn : ‖pairF P Φ (velPhys ε⁻¹ c f)‖ =
      P⁻¹ * ‖∫ x, dotL (Φ x) (velPhys ε⁻¹ c f x) ∂μ‖ := by
    rw [hpair, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hP0.le)]
  rw [hpn]
  have hI : ‖∫ x, dotL (Φ x) (velPhys ε⁻¹ c f x) ∂μ‖ ≤
      3 * (A * (κ * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal)) := by
    rw [← hB]
    exact le_trans (norm_integral_le_integral_norm _)
      (hdom.trans (mul_le_mul_of_nonneg_left hH (by norm_num)))
  calc P⁻¹ * ‖∫ x, dotL (Φ x) (velPhys ε⁻¹ c f x) ∂μ‖
      ≤ P⁻¹ * (3 * (A * (κ * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal))) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hP0.le)
    _ = P⁻¹ * (3 * A * κ) * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal := by ring

end UnforcedLeray.Short.PartIIIb.NearInst
