import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H14

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (15): pointwise domination and measurability

Source of record: `the November 2 reference manuscript` (73 pages), 4180-4186.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

section Ctx

variable {ν μ R c : ℝ} {g : Chart → Ten3} {χy : ℝ → ℝ}

theorem w2a_measurable (ν R : ℝ) (χy : ℝ → ℝ) : Measurable (w2a ν R χy) := by
  unfold w2a
  have hd : Measurable (deriv χy) := measurable_deriv χy
  exact ((hd.comp (measurable_const.mul (measurable_const.div (measurable_id.pow_const 2)))).mul
    (measurable_const.div (measurable_id.pow_const 3))).div measurable_id

theorem w2_corr_measurable (hg : IsOldL2 c ν g) :
    Measurable (fun x : ℝ × Space => wardStreamCorr ν R χy (wardX0 ν μ R c g) x.1 x.2) := by
  have hZ := wardX0_measurable_of_measurable ν μ R c g hg.measurable
  have hO := outPrim_measurable hZ
  have hq : Measurable (fun x : ℝ × Space => ((x.1, ϱ x.2, x.2 2) : ℝ × ℝ × ℝ)) :=
    measurable_fst.prodMk ((continuous_ϱ.measurable.comp measurable_snd).prodMk
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd))
  have hw : Measurable (fun x : ℝ × Space => w2a ν R χy (ϱ x.2)) :=
    (w2a_measurable ν R χy).comp (continuous_ϱ.measurable.comp measurable_snd)
  exact (hw.mul (hO.comp hq)).smul measurable_const

theorem w2_corr_diff (hχ : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : y ∈ youngOpen ν R) :
    DifferentiableAt ℝ (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) y := by
  have hy' : y ∉ axis := t9_not_axis hν hR hy
  have hρ : 0 < ϱ y := ϱ_pos hy'
  have hΨ := w2_psi_hasFDeriv hν hR hc hμ hg τ hy
  have hwd : HasDerivAt (w2a ν R χy) (deriv (w2a ν R χy) (ϱ y)) (ϱ y) :=
    (((w2a_contDiffOn (ν := ν) (R := R) hχ).contDiffAt (Ioi_mem_nhds hρ)).differentiableAt
      one_ne_zero).hasDerivAt
  have hA := (hwd.comp_hasFDerivAt y (hasFDerivAt_ϱ hy')).mul hΨ
  have hC := hA.smul_const (coordinateVector 2)
  have hfun : wardStreamCorr ν R χy (wardX0 ν μ R c g) τ =
      fun x : Space => ((w2a ν R χy ∘ ϱ) x * outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)) •
        coordinateVector 2 := by
    funext x; rfl
  rw [hfun]
  exact hC.differentiableAt

theorem w2_young_mono {C C' : ℝ} {F : ℝ → Space → Space}
    (h : YoungL2Le c ν R C F g) (hC : C ≤ C') : YoungL2Le c ν R C' F g :=
  ⟨h.1, h.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)⟩

theorem w2_read_smul (ν R k : ℝ) (F : ℝ → Space → Space) :
    wardYoungRead ν R (fun τ y => k • F τ y) = fun q => |k| * wardYoungRead ν R F q := by
  funext q
  unfold wardYoungRead
  by_cases hq : q ∈ wardYoungSet ν
  · rw [indicator_of_mem hq, indicator_of_mem hq, norm_smul, Real.norm_eq_abs]
    ring
  · rw [indicator_of_notMem hq, indicator_of_notMem hq]; simp

/-- Young bound from a pointwise domination by the primitive modulus and `X₀`. -/
theorem w2_young_of_pt (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (r2 : ℝ) {CX : ℝ}
    (hX : ∀ g : Chart → Ten3, IsOldL2 c ν g → YoungL2Le c ν R CX (wardX0 ν μ R c g) g)
    (hg : IsOldL2 c ν g) {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (wardYoungRead ν R F) (ageμ c (-3 / 2)))
    {K : ℝ} (hK : 0 ≤ K)
    (hΦ : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (w2Phi ν μ R c r2 g)) K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpt : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ‖F τ y‖ ≤ a * w2N ν μ R c r2 g τ y + b * ‖wardX0 ν μ R c g τ y‖) :
    YoungL2Le c ν R (a * K + b * max CX 0) F g := by
  have hZ := wyl_bd_of_young (hX g hg)
  have hA : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => a • w2Phi ν μ R c r2 g τ y)) (a * K) := by
    rw [w2_read_smul]
    simpa [abs_of_nonneg ha] using hΦ.const_mul a
  have hB : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => b • wardX0 ν μ R c g τ y)) (b * max CX 0) := by
    rw [w2_read_smul]
    simpa [abs_of_nonneg hb] using hZ.const_mul b
  refine w10_young_of_sum hFm hA hB (mul_nonneg ha hK) (mul_nonneg hb (le_max_right _ _)) le_rfl
    fun q => w10_read_dom hν hR (fun τ y hy => ?_) q
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
    abs_of_nonneg hb, w2Phi_norm]
  exact hpt τ y hy

end Ctx

end UnforcedLeray.Short.PartIIIb.Concrete
end
