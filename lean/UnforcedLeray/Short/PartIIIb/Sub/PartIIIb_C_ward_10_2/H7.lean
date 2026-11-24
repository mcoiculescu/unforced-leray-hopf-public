import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H6
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_red

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (7): domination of `Ψ_{X₀}`

Source of record: `the November 2 reference manuscript` (73 pages), 3687-3697,
4178-4186.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w2_srcNorm_measurable {P rOut : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P rOut T) :
    Measurable (Function.uncurry (IIIa.srcNorm T)) := by
  unfold IIIa.srcNorm IIIa.tensorNorm Function.uncurry
  refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (hT.measurable i j).pow_const 2

theorem w2_srcNorm_zero {P rOut : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) {z : Space} (hz : rOut < ϱ z) :
    IIIa.srcNorm T τ z = 0 := by
  have := hT.support τ z hz
  simp [IIIa.srcNorm, IIIa.tensorNorm, this]

/-- **Domination of the outward primitive of `X₀`** (source 3687-3697, 4178-4186). -/
theorem w2_psi_dom {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (r2 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space),
      R * Real.sqrt ν ≤ ϱ y → ϱ y ≤ r2 →
        ENNReal.ofReal |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| ≤
          ENNReal.ofReal C * w2Dom (w2k (R * Real.sqrt (5 * ν / 6))
            (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (r2 + R * Real.sqrt (5 * ν / 6)))
            (2 * μ + 2) (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ y := by
  obtain ⟨C0, hC0, hdom⟩ := w2_wdom
  refine ⟨2 * ‖w10Re‖ * C0, by positivity, ?_⟩
  intro g hg τ y hy1 hy2
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  set T := oldCutSrc R c r0 g with hT
  have hr0nn : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0 with hD
  have hDpos : 0 < D := sub_pos.2 hrr
  have hX0 := w10_X0_eq (μ := μ) hν hR hc hg
  set a : ℝ := 2 * μ + 2 with ha
  set G := IIIa.srcNorm T with hG
  have hμ1 : -(1 / 4) < μ + 1 := by linarith
  -- pointwise domination of `X₀` along the ray
  have hpt : ∀ p : Space, R * Real.sqrt ν ≤ ϱ p →
      ENNReal.ofReal |wardX0 ν μ R c g τ p 2| ≤
        ENNReal.ofReal (2 * ‖w10Re‖ * C0) * w2Dom (IIIa.sepKd 0 D) a G τ p := by
    intro p hp
    have e1 : |wardX0 ν μ R c g τ p 2| ≤ ‖sepWre ν μ T τ p‖ + ‖sepWre ν (μ + 1) T τ p‖ := by
      rw [hX0, sepX0_eq_sub]
      calc |(sepWre ν μ T τ p - sepWre ν (μ + 1) T τ p) 2|
          ≤ ‖sepWre ν μ T τ p - sepWre ν (μ + 1) T τ p‖ := wyl_abs_apply_le _ 2
        _ ≤ _ := norm_sub_le _ _
    have d1 := hdom ν hν μ hμ r0 (R * Real.sqrt ν) (2 * c / R) hr0nn hrr hP T hS τ p hp
    have d2 := hdom ν hν (μ + 1) hμ1 r0 (R * Real.sqrt ν) (2 * c / R) hr0nn hrr hP T hS τ p hp
    have m1 := w2_enorm_sepWre (ν := ν) μ T τ p
    have m2 := w2_enorm_sepWre (ν := ν) (μ + 1) T τ p
    have hmono : w2Dom (IIIa.sepKd 0 D) (2 * (μ + 1) + 2) G τ p ≤
        w2Dom (IIIa.sepKd 0 D) a G τ p :=
      w2Dom_mono_a _ (by rw [ha]; linarith) _ _ _
    calc ENNReal.ofReal |wardX0 ν μ R c g τ p 2|
        ≤ ENNReal.ofReal (‖sepWre ν μ T τ p‖ + ‖sepWre ν (μ + 1) T τ p‖) :=
          ENNReal.ofReal_le_ofReal e1
      _ = ‖sepWre ν μ T τ p‖ₑ + ‖sepWre ν (μ + 1) T τ p‖ₑ := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]
      _ ≤ ENNReal.ofReal ‖w10Re‖ * (ENNReal.ofReal C0 * w2Dom (IIIa.sepKd 0 D) a G τ p) +
          ENNReal.ofReal ‖w10Re‖ * (ENNReal.ofReal C0 *
            w2Dom (IIIa.sepKd 0 D) (2 * (μ + 1) + 2) G τ p) := by
          gcongr
          · exact m1.trans (mul_le_mul' le_rfl d1)
          · exact m2.trans (mul_le_mul' le_rfl d2)
      _ ≤ ENNReal.ofReal ‖w10Re‖ * (ENNReal.ofReal C0 * w2Dom (IIIa.sepKd 0 D) a G τ p) +
          ENNReal.ofReal ‖w10Re‖ * (ENNReal.ofReal C0 * w2Dom (IIIa.sepKd 0 D) a G τ p) := by
          gcongr
      _ = ENNReal.ofReal (2 * ‖w10Re‖ * C0) * w2Dom (IIIa.sepKd 0 D) a G τ p := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_ofNat]
          ring
  -- integrate along the ray
  have hnorm : ENNReal.ofReal |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| ≤
      ∫⁻ ρ in Ioi (ϱ y), ‖ρ * wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) 2‖ₑ := by
    unfold outPrim
    rw [← Real.enorm_eq_ofReal_abs, enorm_neg]
    exact enorm_integral_le_lintegral_enorm _
  refine hnorm.trans ?_
  calc ∫⁻ ρ in Ioi (ϱ y), ‖ρ * wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) 2‖ₑ
      ≤ ∫⁻ ρ in Ioi (ϱ y), ENNReal.ofReal (2 * ‖w10Re‖ * C0) *
          (ENNReal.ofReal ρ * w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
        have hρ' : ϱ y < ρ := hρ
        have hρ0 : 0 ≤ ρ := (ϱ_nonneg y).trans hρ'.le
        have hϱ : ϱ (!₂[ρ, 0, y 2] : Space) = ρ := wardFar_varrho ρ (y 2) hρ0
        have := hpt (!₂[ρ, 0, y 2] : Space) (by rw [hϱ]; linarith)
        rw [enorm_mul, Real.enorm_of_nonneg hρ0, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        calc ENNReal.ofReal ρ * ENNReal.ofReal |wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) 2|
            ≤ ENNReal.ofReal ρ * (ENNReal.ofReal (2 * ‖w10Re‖ * C0) *
                w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space)) := by gcongr
          _ = _ := by ring
    _ = ENNReal.ofReal (2 * ‖w10Re‖ * C0) *
          ∫⁻ ρ in Ioi (ϱ y), ENNReal.ofReal ρ *
            w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        exact w2_tonelli hr0nn hDpos a (w2_srcNorm_measurable hS)
          (fun τ' z hz => w2_srcNorm_zero hS τ' hz) τ hy2 (by rw [hD]; linarith)

end UnforcedLeray.Short.PartIIIb.Concrete
end
