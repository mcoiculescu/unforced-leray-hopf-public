import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H7
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_2

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (8): the young `L²` bound of the primitive field

Source of record: `the November 2 reference manuscript` (73 pages), 3687-3713,
4180-4186, 2683-2689.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w2_X0_periodic {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) {g : Chart → Ten3}
    (hg : IsOldL2 c ν g) (τ : ℝ) (y : Space) :
    wardX0 ν μ R c g (τ + 2 * c / R) y = wardX0 ν μ R c g τ y := by
  obtain ⟨hS, -, -⟩ := w10_ctx hν hR hc hg
  rw [w10_X0_eq hν hR hc hg, sepX0_eq_sub, sepX0_eq_sub,
    sepWre_periodic ν μ _ _ hS.periodic, sepWre_periodic ν (μ + 1) _ _ hS.periodic]

/-- The truncated modulus of the primitive of `X₀`: `|Ψ_{X₀}(ϱ y, y₃)|` for `ϱ y ≤ r₂`, else `0`. -/
def w2N (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : ℝ :=
  if ϱ y ≤ r2 then |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| else 0

/-- The corresponding vertical field. -/
def w2Phi (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  w2N ν μ R c r2 g τ y • coordinateVector 2

theorem w2N_nonneg (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    0 ≤ w2N ν μ R c r2 g τ y := by
  unfold w2N; split_ifs <;> positivity

theorem w2N_meridPt (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    w2N ν μ R c r2 g τ (meridPt y) = w2N ν μ R c r2 g τ y := by
  unfold w2N
  rw [w10_varrho_meridPt, w10_mp2]

theorem w2N_measurable {ν μ R c : ℝ} (r2 : ℝ) {g : Chart → Ten3} (hg : Measurable g) :
    Measurable (fun x : ℝ × Space => w2N ν μ R c r2 g x.1 x.2) := by
  unfold w2N
  have hZ := wardX0_measurable_of_measurable ν μ R c g hg
  have hO := outPrim_measurable hZ
  have hq : Measurable (fun x : ℝ × Space => ((x.1, ϱ x.2, x.2 2) : ℝ × ℝ × ℝ)) :=
    measurable_fst.prodMk ((continuous_ϱ.measurable.comp measurable_snd).prodMk
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd))
  refine Measurable.ite ?_ (hO.comp hq).abs measurable_const
  exact measurableSet_le (continuous_ϱ.measurable.comp measurable_snd) measurable_const

theorem w2Phi_norm (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    ‖w2Phi ν μ R c r2 g τ y‖ = w2N ν μ R c r2 g τ y := by
  unfold w2Phi
  rw [norm_smul, wyl_norm_coordinateVector, mul_one, Real.norm_of_nonneg (w2N_nonneg _ _ _ _ _ _ _ _)]

/-- Young at the level of the phase norms, for the cylinder majorant. -/
theorem w2_ltau {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (r2 : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g →
      IIIa.ltauLq (2 * c / R) 2 (w2Dom (w2k (R * Real.sqrt (5 * ν / 6))
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (r2 + R * Real.sqrt (5 * ν / 6)))
          (2 * μ + 2) (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g))) ≤
        ENNReal.ofReal B * IIIa.ltauLq (2 * c / R) 2
          (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) := by
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0 with hD
  have hDpos : 0 < D := sub_pos.2 hrr
  set k := w2k r0 D (r2 + r0) with hk
  have hkm : Measurable k := w2k_measurable _ _ _
  have hfin : ∫⁻ x : Space, k x ≠ ⊤ := w2k_lintegral_ne_top hDpos _
  set δ : ℝ := 2 * μ + 3 / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  refine ⟨(∫⁻ x : Space, k x).toReal * (1 / δ), by positivity, ?_⟩
  intro g hg
  obtain ⟨hS, -, -⟩ := w10_ctx hν hR hc hg
  have hP : 0 < 2 * c / R := by positivity
  have hper : ∀ τ z, IIIa.srcNorm (oldCutSrc R c r0 g) (τ + 2 * c / R) z =
      IIIa.srcNorm (oldCutSrc R c r0 g) τ z := by
    intro τ z; unfold IIIa.srcNorm; rw [hS.periodic]
  have := w2_young hkm hδpos (a := 2 * μ + 2) (by rw [hδ]; linarith) hfin (2 * c / R) hP
    (w2_srcNorm_measurable hS) hper
  refine this.trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hfin]

end UnforcedLeray.Short.PartIIIb.Concrete
end
