import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.QDecomposition
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.ClassSub

/-!
# Weak `∂_q` derivative from `(Q_ε, S, ∂_η)` (`∂_q = Q_ε + ε(2S + η∂_η + 1)`)

Source of record: `the November 2 reference manuscript`, lines 1960-1996.
Constructs `HasWeakVec vQ0 dZero b (dqOf ε b Sb Qb Eb)` from the weak derivatives
`S b = Sb`, `Q_ε b = Qb`, `∂_η b = Eb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `∂_q b = Q_ε b + ε (2 S b + η ∂_η b + b)` componentwise. -/
def dqOf (ε : ℝ) (b Sb Qb Eb : CProf) : CProf :=
  fun x => WithLp.toLp 2 fun i =>
    Qb x i + (ε : ℂ) * (2 * Sb x i + (x.2.2 : ℂ) * Eb x i + b x i)

@[simp]
theorem dqOf_apply (ε : ℝ) (b Sb Qb Eb : CProf) (x : Coord) (i : Fin 2) :
    dqOf ε b Sb Qb Eb x i =
      Qb x i + (ε : ℂ) * (2 * Sb x i + (x.2.2 : ℂ) * Eb x i + b x i) := rfl

theorem coordTranspose_vEta_eq_zero_of_notMem_tsupport {φ : Coord → ℝ} {x : Coord}
    (hx : x ∉ tsupport φ) : coordTranspose vEta dZero φ x = 0 := by
  rw [qd_T_E]
  have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  unfold cpd
  rw [hev.fderiv_eq]
  simp

/-- Any scalar function `u` with weak `η`-derivative `HasWeakFO vEta dZero u Eu` is locally
integrable against every coordinate test `φ`. Proof: `-∂_η(η φ) + η ∂_η φ = -φ`. -/
theorem integrable_mul_coordTest {u Eu : Coord → ℂ} (hE : HasWeakFO vEta dZero u Eu)
    {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    Integrable (fun x => u x * (φ x : ℂ)) := by
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hη : IsCoordTest (fun y : Coord => y.2.2 * φ y) := qd_test_mul_snd hφ
  have h1 : Integrable (fun x => u x * (coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℂ)) :=
    (hE.1 _ hη).1
  have h2 : Integrable (fun x => u x * (coordTranspose vEta dZero φ x : ℂ)) :=
    (hE.1 φ hφ).1
  obtain ⟨R, hR⟩ := hφ.compact.isBounded.subset_closedBall (0 : Coord)
  let g : Coord → ℂ := (Metric.closedBall (0 : Coord) R).indicator (fun x => (x.2.2 : ℂ))
  have hg_meas : AEStronglyMeasurable g volume :=
    ((Complex.continuous_ofReal.comp (continuous_snd.comp continuous_snd)).measurable.indicator
      measurableSet_closedBall).aestronglyMeasurable
  have hg_bdd : ∀ x : Coord, ‖g x‖ ≤ max R 0 := by
    intro x
    dsimp [g]
    by_cases hx : x ∈ Metric.closedBall (0 : Coord) R
    · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
      have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have h22 : |x.2.2| ≤ ‖x‖ :=
        (Real.norm_eq_abs _).symm.le.trans ((norm_snd_le x.2).trans (norm_snd_le x))
      exact (h22.trans hxR).trans (le_max_left R 0)
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact le_max_right R 0
  have h2g : Integrable (fun x => g x * (u x * (coordTranspose vEta dZero φ x : ℂ))) :=
    h2.bdd_mul hg_meas (ae_of_all _ hg_bdd)
  have hpt : ∀ x : Coord,
      u x * (φ x : ℂ) =
        g x * (u x * (coordTranspose vEta dZero φ x : ℂ)) -
          u x * (coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℂ) := by
    intro x
    have hgx : g x * (coordTranspose vEta dZero φ x : ℂ) =
        (x.2.2 : ℂ) * (coordTranspose vEta dZero φ x : ℂ) := by
      dsimp [g]
      by_cases hx : x ∈ Metric.closedBall (0 : Coord) R
      · rw [Set.indicator_of_mem hx]
      · have hxt : x ∉ tsupport φ := fun h => hx (hR h)
        rw [coordTranspose_vEta_eq_zero_of_notMem_tsupport hxt, Complex.ofReal_zero,
          mul_zero, mul_zero]
    have hφx : (φ x : ℂ) =
        (x.2.2 : ℂ) * (coordTranspose vEta dZero φ x : ℂ) -
          (coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℂ) := by
      have hr : φ x = x.2.2 * coordTranspose vEta dZero φ x -
          coordTranspose vEta dZero (fun y => y.2.2 * φ y) x := by
        rw [qd_T_E, qd_T_E, qd_cpd_snd_mul φ hφd x]
        ring
      exact_mod_cast hr
    calc u x * (φ x : ℂ)
        = u x * ((x.2.2 : ℂ) * (coordTranspose vEta dZero φ x : ℂ)) -
            u x * (coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℂ) := by
          rw [hφx, mul_sub]
      _ = g x * (u x * (coordTranspose vEta dZero φ x : ℂ)) -
            u x * (coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℂ) := by
          rw [← mul_left_comm (u x), hgx]
  exact (h2g.sub h1).congr (ae_of_all _ fun x => (hpt x).symm)

/-- Scalar weak `∂_q` derivative from `(Q_ε, S, ∂_η)`. -/
theorem hasWeakFO_dqOf (ε : ℝ) {u Su Qu Eu : Coord → ℂ}
    (hS : HasWeakFO vS dZero u Su)
    (hQ : HasWeakFO (vQ ε) (dQ ε) u Qu)
    (hE : HasWeakFO vEta dZero u Eu) :
    HasWeakFO vQ0 dZero u
      (fun x => Qu x + (ε : ℂ) * (2 * Su x + (x.2.2 : ℂ) * Eu x + u x)) := by
  set Du : Coord → ℂ := fun x => Qu x + (ε : ℂ) * (2 * Su x + (x.2.2 : ℂ) * Eu x + u x)
  have h_int : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => u x * (coordTranspose vQ0 dZero φ x : ℂ)) ∧
        Integrable (fun x => Du x * (φ x : ℂ)) := by
    intro φ hφ
    have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hη := qd_test_mul_snd hφ
    have huφ := integrable_mul_coordTest hE hφ
    have hIQ := (hQ.1 φ hφ).1
    have hIS := (hS.1 φ hφ).1
    have hIE := (hE.1 _ hη).1
    have hFQ := (hQ.1 φ hφ).2
    have hFS := (hS.1 φ hφ).2
    have hFE := (hE.1 _ hη).2
    refine ⟨?_, ?_⟩
    · have hpt : ∀ x : Coord,
          u x * (coordTranspose vQ0 dZero φ x : ℂ) =
            u x * (coordTranspose (vQ ε) (dQ ε) φ x : ℂ) +
              (2 * (ε : ℂ)) * (u x * (coordTranspose vS dZero φ x : ℂ)) +
              (ε : ℂ) * (u x * (coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℂ)) +
              (ε : ℂ) * (u x * (φ x : ℂ)) := by
        intro x
        have hr := qd_real ε φ hφd x
        have hc : (ε : ℂ) * (φ x : ℂ) = -((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ) +
            ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ) -
            2 * (ε : ℂ) * ((coordTranspose vS dZero φ x : ℝ) : ℂ) -
            (ε : ℂ) * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ) := by
          exact_mod_cast hr
        linear_combination -(u x) * hc
      exact (((hIQ.add (hIS.const_mul (2 * (ε : ℂ)))).add
        (hIE.const_mul (ε : ℂ))).add (huφ.const_mul (ε : ℂ))).congr
          (ae_of_all _ fun x => (hpt x).symm)
    · have hpt : ∀ x : Coord,
          Du x * (φ x : ℂ) =
            Qu x * (φ x : ℂ) +
              (2 * (ε : ℂ)) * (Su x * (φ x : ℂ)) +
              (ε : ℂ) * (Eu x * ((x.2.2 * φ x : ℝ) : ℂ)) +
              (ε : ℂ) * (u x * (φ x : ℂ)) := by
        intro x
        dsimp [Du]
        push_cast
        ring
      exact (((hFQ.add (hFS.const_mul (2 * (ε : ℂ)))).add
        (hFE.const_mul (ε : ℂ))).add (huφ.const_mul (ε : ℂ))).congr
          (ae_of_all _ fun x => (hpt x).symm)
  refine ⟨h_int, fun φ hφ => ?_⟩
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hη := qd_test_mul_snd hφ
  obtain ⟨hI0, hF1⟩ := h_int φ hφ
  have hIQ := (hQ.1 φ hφ).1
  have hIS := (hS.1 φ hφ).1
  have hIE := (hE.1 _ hη).1
  have hF2 := (hQ.1 φ hφ).2
  have hF3 := (hS.1 φ hφ).2
  have hF4 := (hE.1 _ hη).2
  have i2 : Integrable (fun x => Qu x * (φ x : ℂ) -
      u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)) := hF2.sub hIQ
  have i3 : Integrable (fun x => Su x * (φ x : ℂ) -
      u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ)) := hF3.sub hIS
  have i4 : Integrable (fun x => Eu x * ((x.2.2 * φ x : ℝ) : ℂ) -
      u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) := hF4.sub hIE
  have z2 : ∫ x, (Qu x * (φ x : ℂ) -
      u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF2 hIQ, hQ.2 φ hφ, sub_self]
  have z3 : ∫ x, (Su x * (φ x : ℂ) -
      u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF3 hIS, hS.2 φ hφ, sub_self]
  have z4 : ∫ x, (Eu x * ((x.2.2 * φ x : ℝ) : ℂ) -
      u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF4 hIE, hE.2 _ hη, sub_self]
  have hpt : ∀ x : Coord,
      Du x * (φ x : ℂ) - u x * (coordTranspose vQ0 dZero φ x : ℂ) =
        (Qu x * (φ x : ℂ) - u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)) +
          2 * (ε : ℂ) * (Su x * (φ x : ℂ) - u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ)) +
          (ε : ℂ) * (Eu x * ((x.2.2 * φ x : ℝ) : ℂ) -
            u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) := by
    intro x
    have hc : (ε : ℂ) * (φ x : ℂ) = -((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ) +
        ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ) -
        2 * (ε : ℂ) * ((coordTranspose vS dZero φ x : ℝ) : ℂ) -
        (ε : ℂ) * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ) := by
      exact_mod_cast qd_real ε φ hφd x
    dsimp [Du]
    push_cast
    linear_combination (u x) * hc
  have i23 : Integrable (fun x => (Qu x * (φ x : ℂ) -
      u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)) +
      2 * (ε : ℂ) * (Su x * (φ x : ℂ) - u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ))) :=
    i2.add (i3.const_mul (2 * (ε : ℂ)))
  have hdiff : ∫ x, (Du x * (φ x : ℂ) - u x * (coordTranspose vQ0 dZero φ x : ℂ)) = 0 := by
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_add i23 (i4.const_mul (ε : ℂ)),
      integral_add i2 (i3.const_mul (2 * (ε : ℂ))),
      integral_const_mul, integral_const_mul, z2, z3, z4]
    ring
  rw [← sub_eq_zero, ← integral_sub hF1 hI0]
  exact hdiff

/-- Vector weak `∂_q` derivative from `(Q_ε, S, ∂_η)`. -/
theorem hasWeakVec_dqOf (ε : ℝ) {b Sb Qb Eb : CProf}
    (hS : HasWeakVec vS dZero b Sb)
    (hQ : HasWeakVec (vQ ε) (dQ ε) b Qb)
    (hE : HasWeakVec vEta dZero b Eb) :
    HasWeakVec vQ0 dZero b (dqOf ε b Sb Qb Eb) := by
  intro i
  exact hasWeakFO_dqOf ε (hS i) (hQ i) (hE i)

end UnforcedLeray.Short.IIb

end
