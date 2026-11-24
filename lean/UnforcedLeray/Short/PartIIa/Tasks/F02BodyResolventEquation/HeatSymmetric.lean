import UnforcedLeray.Short.PartIIa.Sub.F02
import UnforcedLeray.Units.B0418.HeatLp
import UnforcedLeray.Analysis.Heat.ConvolutionL2
import UnforcedLeray.Analysis.Heat.SelfAdjoint

/-!
# Part II-a, task `PartII-a:F02/1`: heat flow is symmetric on `L^p × L^q`

Source of record: `the November 2 reference manuscript`, lines 1363-1370.
This file proves the Prop `HeatSymmetricLp` defined in `Sub/F02.lean`.

Proof sketch. For `t = 0` the flow is the identity. For `t > 0` both sides reduce, by
`flow_pos` and a Fubini swap (`heat_pairing_swap`, used once for each side), to
`∫ k(z) J(z) dz` and `∫ k(z) J(-z) dz`, where `J(z) = ∫ ⟪u x, h (x - z)⟫ dx`. Evenness of the
kernel identifies the two.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa

/-- The Hölder constant `‖u‖_p ‖h‖_q` bounding every translated pairing uniformly. -/
def pairingBound (p q : ℝ≥0∞) (u h : SpatialField) : ℝ :=
  (∫ x, ‖u x‖ ^ p.toReal) ^ (1 / p.toReal) * (∫ x, ‖h x‖ ^ q.toReal) ^ (1 / q.toReal)

/-- Hölder for the translated pairing: `x ↦ ‖u x‖ ‖h (x - z)‖` is integrable, and its integral is
bounded uniformly in `z`. -/
theorem fiber_integrable_and_bound {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (u h : SpatialField) (hu : MemLp u p volume)
    (hh : MemLp h q volume) (z : Space) :
    Integrable (fun x => ‖u x‖ * ‖h (x - z)‖) volume ∧
      ∫ x, ‖u x‖ * ‖h (x - z)‖ ≤ pairingBound p q u h := by
  have hpq : p.toReal.HolderConjugate q.toReal :=
    ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hs : MemLp (fun x => h (x - z)) q volume :=
    hh.comp_measurePreserving (measurePreserving_sub_right volume z)
  have hsp : MemLp u (ENNReal.ofReal p.toReal) volume := by
    rw [ENNReal.ofReal_toReal hp]; exact hu
  have hsq : MemLp (fun x => h (x - z)) (ENNReal.ofReal q.toReal) volume := by
    rw [ENNReal.ofReal_toReal hq]; exact hs
  refine ⟨?_, ?_⟩
  · exact hu.norm.integrable_mul hs.norm
  · have hH : ∫ x, ‖u x‖ * ‖h (x - z)‖ ≤
        (∫ x, ‖u x‖ ^ p.toReal) ^ (1 / p.toReal) *
          (∫ x, ‖h (x - z)‖ ^ q.toReal) ^ (1 / q.toReal) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hsp hsq
    have e : ∫ x, ‖h (x - z)‖ ^ q.toReal = ∫ x, ‖h x‖ ^ q.toReal :=
      integral_sub_right_eq_self (μ := volume) (fun x => ‖h x‖ ^ q.toReal) z
    rw [e] at hH
    exact hH

/-- Pointwise identity: the heat average paired with `u x` is the kernel-weighted integral of
the translates of `h`. -/
theorem inner_average_eq_integral {q : ℝ≥0∞} {t : ℝ} (ht : 0 < t) (hq1 : 1 ≤ q) (hq : q ≠ ⊤)
    (u h : SpatialField) (hh : MemLp h q volume) (x : Space) :
    inner ℝ (u x) (Heat.average t h x) =
      ∫ z, Heat.kernel t z * inner ℝ (u x) (h (x - z)) := by
  unfold Heat.average
  rw [← integral_inner (UnforcedLeray.B0418.heat_integrand_integrable ht hq1 hq hh x) (u x)]
  simp only [real_inner_smul_right]

/-- Joint integrability of `(x, z) ↦ k(z) ⟪u x, h (x - z)⟫` on `R³ × R³`. -/
theorem heat_pairing_integrable {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) {t : ℝ} (ht : 0 < t) (u h : SpatialField)
    (hu : MemLp u p volume) (hh : MemLp h q volume) :
    Integrable (fun z : Space × Space => Heat.kernel t z.2 * inner ℝ (u z.1) (h (z.1 - z.2)))
      ((volume : Measure Space).prod volume) := by
  have hk1 : Integrable (Heat.kernel t) volume := Heat.kernel_integrable ht
  have hjoint : AEStronglyMeasurable
      (fun z : Space × Space => Heat.kernel t z.2 * inner ℝ (u z.1) (h (z.1 - z.2)))
      ((volume : Measure Space).prod volume) := by
    have h1 : AEStronglyMeasurable
        (fun z : Space × Space => inner ℝ (u z.1) (Heat.kernel t z.2 • h (z.1 - z.2)))
        ((volume : Measure Space).prod volume) :=
      (hu.aestronglyMeasurable.comp_fst).inner
        (UnforcedLeray.Heat.convolution_joint_aestronglyMeasurable hk1.aestronglyMeasurable
          hh.aestronglyMeasurable)
    refine h1.congr (Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right]
  have hslice : ∀ z : Space,
      Integrable (fun x : Space => Heat.kernel t z * inner ℝ (u x) (h (x - z))) volume := by
    intro z
    have hs : AEStronglyMeasurable (fun x => h (x - z)) volume :=
      (hh.comp_measurePreserving (measurePreserving_sub_right volume z)).aestronglyMeasurable
    refine Integrable.mono'
      ((fiber_integrable_and_bound hp hq u h hu hh z).1.const_mul (Heat.kernel t z))
      ((hu.aestronglyMeasurable.inner hs).const_mul _) (Eventually.of_forall fun x => ?_)
    show ‖Heat.kernel t z * inner ℝ (u x) (h (x - z))‖ ≤
      Heat.kernel t z * (‖u x‖ * ‖h (x - z)‖)
    rw [norm_mul, Real.norm_of_nonneg (Heat.kernel_nonneg ht z)]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (Heat.kernel_nonneg ht z)
  have hint2 : Integrable
      (fun z : Space => ∫ x, ‖Heat.kernel t z * inner ℝ (u x) (h (x - z))‖ ∂volume) volume := by
    refine Integrable.mono' ((Heat.kernel_integrable ht).mul_const (pairingBound p q u h))
      (hjoint.norm.prod_swap.integral_prod_right') (Eventually.of_forall fun z => ?_)
    show ‖∫ x, ‖Heat.kernel t z * inner ℝ (u x) (h (x - z))‖ ∂volume‖ ≤
      Heat.kernel t z * pairingBound p q u h
    have hnn : 0 ≤ ∫ x, ‖Heat.kernel t z * inner ℝ (u x) (h (x - z))‖ ∂volume :=
      integral_nonneg fun x => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    calc ∫ x, ‖Heat.kernel t z * inner ℝ (u x) (h (x - z))‖ ∂volume
        ≤ ∫ x, Heat.kernel t z * (‖u x‖ * ‖h (x - z)‖) ∂volume := by
          refine integral_mono (hslice z).norm
            ((fiber_integrable_and_bound hp hq u h hu hh z).1.const_mul _) (fun x => ?_)
          show ‖Heat.kernel t z * inner ℝ (u x) (h (x - z))‖ ≤
            Heat.kernel t z * (‖u x‖ * ‖h (x - z)‖)
          rw [norm_mul, Real.norm_of_nonneg (Heat.kernel_nonneg ht z)]
          exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (Heat.kernel_nonneg ht z)
      _ = Heat.kernel t z * ∫ x, ‖u x‖ * ‖h (x - z)‖ ∂volume := integral_const_mul _ _
      _ ≤ Heat.kernel t z * pairingBound p q u h :=
          mul_le_mul_of_nonneg_left (fiber_integrable_and_bound hp hq u h hu hh z).2
            (Heat.kernel_nonneg ht z)
  exact (integrable_prod_iff' hjoint).2 ⟨Eventually.of_forall hslice, hint2⟩

/-- Fubini swap for the heat pairing: `∫ ⟪u, e^{tΔ}h⟫ = ∫ k(z) ∫ ⟪u x, h (x - z)⟫ dx dz`. -/
theorem heat_pairing_swap {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) {t : ℝ} (ht : 0 < t) (u h : SpatialField)
    (hu : MemLp u p volume) (hh : MemLp h q volume) :
    ∫ x, inner ℝ (u x) (Heat.average t h x) =
      ∫ z, Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - z)) := by
  have hq1 : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  calc ∫ x, inner ℝ (u x) (Heat.average t h x)
      = ∫ x, ∫ z, Heat.kernel t z * inner ℝ (u x) (h (x - z)) :=
        integral_congr_ae
          (Eventually.of_forall fun x => inner_average_eq_integral ht hq1 hq u h hh x)
    _ = ∫ z, ∫ x, Heat.kernel t z * inner ℝ (u x) (h (x - z)) :=
        integral_integral_swap (f := fun x z => Heat.kernel t z * inner ℝ (u x) (h (x - z)))
          (heat_pairing_integrable hp hq ht u h hu hh)
    _ = ∫ z, Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - z)) := by
        simp only [integral_const_mul]

/-- **Heat flow is symmetric on `L^p × L^{p'}`** (task `PartII-a:F02/1`). -/
theorem heatSymmetricLp : HeatSymmetricLp := by
  unfold HeatSymmetricLp
  intro p q _ hp hq t ht u h hu hh
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    simp only [Heat.flow_zero]
  · have hK : ∀ z : Space,
        ∫ x, inner ℝ (h x) (u (x - z)) = ∫ x, inner ℝ (u x) (h (x - -z)) := by
      intro z
      calc ∫ x, inner ℝ (h x) (u (x - z))
          = ∫ x, inner ℝ (h (x + z)) (u (x + z - z)) :=
            (integral_add_right_eq_self (μ := volume)
              (fun x => inner ℝ (h x) (u (x - z))) z).symm
        _ = ∫ x, inner ℝ (u x) (h (x - -z)) := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            simp only [add_sub_cancel_right, sub_neg_eq_add]
            exact (real_inner_comm _ _).symm
    have hneg : ∫ z, Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - -z)) =
        ∫ z, Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - z)) := by
      calc ∫ z, Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - -z))
          = ∫ z, Heat.kernel t (-z) * ∫ x, inner ℝ (u x) (h (x - -(-z))) :=
            (integral_neg_eq_self (μ := volume)
              (fun z => Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - -z)))).symm
        _ = ∫ z, Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - z)) := by
            simp only [UnforcedLeray.Heat.kernel_neg, neg_neg]
    rw [Heat.flow_pos h hpos, Heat.flow_pos u hpos]
    calc ∫ y, inner ℝ (u y) (Heat.average t h y)
        = ∫ z, Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - z)) :=
          heat_pairing_swap hp hq hpos u h hu hh
      _ = ∫ z, Heat.kernel t z * ∫ x, inner ℝ (u x) (h (x - -z)) := hneg.symm
      _ = ∫ z, Heat.kernel t z * ∫ x, inner ℝ (h x) (u (x - z)) := by
          simp only [hK]
      _ = ∫ y, inner ℝ (h y) (Heat.average t u y) :=
          (heat_pairing_swap hq hp hpos h u hh hu).symm
      _ = ∫ y, inner ℝ (Heat.average t u y) (h y) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          exact real_inner_comm _ _

end UnforcedLeray.Short.PartIIa
