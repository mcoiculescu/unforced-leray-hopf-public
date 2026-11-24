import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardBin
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

/-!
# The thin mass bound for the gained norm (source 5571-5584, 5601)

From `ThinMassBound` for the ungained `Z₁` norm, the gained thin mass of `T₁` is bounded by
`C c^k (a^{-3/4}+a^{-1/2}) e^{γ/ν} ‖T‖`, since `g(t) = e^{γt/(1+νt)} ≤ e^{γ/ν}` for `t ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gainG_le_exp_div' {γ ν s : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 0 ≤ s) :
    UnforcedLeray.Short.IIIa.gainG γ ν s ≤ Real.exp (γ / ν) := by
  unfold UnforcedLeray.Short.IIIa.gainG
  apply Real.exp_le_exp.2
  have h1 : 0 < 1 + ν * s := by nlinarith
  rw [div_le_div_iff₀ h1 hν]
  nlinarith

theorem ginv_inv_eq' (γ ν : ℝ) (p : Chart) :
    (ginv γ ν p)⁻¹ = UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) := by
  unfold ginv
  exact inv_inv _

theorem ginv_ne_zero' (γ ν : ℝ) (p : Chart) : ginv γ ν p ≠ 0 := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  exact inv_ne_zero (Real.exp_pos _).ne'

theorem ginv_inv_nonneg' (γ ν : ℝ) (p : Chart) : 0 ≤ (ginv γ ν p)⁻¹ := by
  rw [ginv_inv_eq']
  unfold UnforcedLeray.Short.IIIa.gainG
  exact (Real.exp_pos _).le

theorem ginv_inv_le_exp' {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (p : Chart) :
    (ginv γ ν p)⁻¹ ≤ Real.exp (γ / ν) := by
  rw [ginv_inv_eq']
  exact gainG_le_exp_div' hγ hν (le_max_right _ _)

/-- Transfer of a `z₁`-a.e. property to the age weight `s^{-3/2}`. -/
theorem ae_ageThreeHalves_of_z1 {c mZ : ℝ} (P : Chart → Prop)
    (h : ∀ᵐ p ∂(z1Measure c mZ), P p) : ∀ᵐ p ∂(ageμ c (-3 / 2)), P p := by
  have h1 : ∀ᵐ p ∂(ageμ c (-1 / 2)), P p := by
    rw [← NearInst.ae_z1Measure c mZ]
    exact h
  exact (Measure.ae_le_iff_absolutelyContinuous.2 (NearInst.ageμ_absCont c (-3 / 2) (-1 / 2))) h1

theorem eLpNorm_two_eq_lint (f : Chart → Ten3) (μ : Measure Chart) :
    eLpNorm f 2 μ = (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num

/-- Comparison of the ungained and gained `L²` norms on `Z₁` (the weight `ginv²` is bounded
below by `e^{-2γ/ν}`). -/
theorem eLpNorm_z1_le_gain {c mZ γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) {u : Chart → Ten3}
    (hu : Measurable u) :
    eLpNorm u 2 (z1Measure c mZ) ≤
      ENNReal.ofReal (Real.exp (γ / ν)) * eLpNorm u 2 (gainZ1Measure c mZ γ ν) := by
  have hWm : Measurable fun p : Chart => ENNReal.ofReal ((ginv γ ν p)⁻¹ ^ 2) :=
    ENNReal.measurable_ofReal.comp (((NearInst.ginv_measurable' γ ν).inv).pow_const 2)
  have hdens : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((NearInst.ginv_measurable' γ ν).pow_const 2)
  have hprod : ∀ p : Chart,
      ENNReal.ofReal (ginv γ ν p ^ 2) * ENNReal.ofReal ((ginv γ ν p)⁻¹ ^ 2) = 1 := by
    intro p
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow, mul_inv_cancel₀ (ginv_ne_zero' γ ν p),
      one_pow, ENNReal.ofReal_one]
  have hE2 : ∀ p : Chart,
      ENNReal.ofReal ((ginv γ ν p)⁻¹ ^ 2) ≤ ENNReal.ofReal (Real.exp (γ / ν)) ^ (2 : ℝ) := by
    intro p
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), Real.rpow_two]
    apply ENNReal.ofReal_le_ofReal
    have h1 := ginv_inv_le_exp' hγ hν p
    have h2 := ginv_inv_nonneg' γ ν p
    nlinarith
  have hJ : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)
      = ∫⁻ p, ENNReal.ofReal ((ginv γ ν p)⁻¹ ^ 2) * ‖u p‖ₑ ^ (2 : ℝ)
          ∂(gainZ1Measure c mZ γ ν) := by
    unfold gainZ1Measure
    have key : ∫⁻ p, ENNReal.ofReal ((ginv γ ν p)⁻¹ ^ 2) * ‖u p‖ₑ ^ (2 : ℝ)
        ∂((z1Measure c mZ).withDensity fun p => ENNReal.ofReal (ginv γ ν p ^ 2))
        = ∫⁻ p, ENNReal.ofReal (ginv γ ν p ^ 2)
            * (ENNReal.ofReal ((ginv γ ν p)⁻¹ ^ 2) * ‖u p‖ₑ ^ (2 : ℝ)) ∂(z1Measure c mZ) :=
      lintegral_withDensity_eq_lintegral_mul _ hdens (Measurable.mul hWm (hu.enorm.pow_const _))
    rw [key]
    apply lintegral_congr
    intro p
    rw [← mul_assoc, hprod p, one_mul]
  have hbound : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)
      ≤ ENNReal.ofReal (Real.exp (γ / ν)) ^ (2 : ℝ)
          * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν) := by
    rw [hJ, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
    apply lintegral_mono
    intro p
    exact mul_le_mul_of_nonneg_right (hE2 p) (by positivity)
  rw [eLpNorm_two_eq_lint u (z1Measure c mZ), eLpNorm_two_eq_lint u (gainZ1Measure c mZ γ ν)]
  calc (∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (Real.exp (γ / ν)) ^ (2 : ℝ)
          * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = ENNReal.ofReal (Real.exp (γ / ν)) * (∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ)
          ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num

theorem massGained (mZ : ℝ) : MassGained mZ := by
  intro hTM
  obtain ⟨C, k, hCb⟩ := hTM
  refine ⟨|C|, k, ?_⟩
  intro c ρb γ ν hc hγ hν T a ha g hg
  classical
  obtain ⟨u, hum, hu⟩ : ∃ u : Chart → Ten3, Measurable u ∧
      ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) : Chart → Ten3)
        =ᵐ[gainZ1Measure c mZ γ ν] u :=
    ⟨_, (Lp.aestronglyMeasurable (T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))).stronglyMeasurable_mk.measurable,
      (Lp.aestronglyMeasurable (T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))).ae_eq_mk⟩
  have hgu : ∀ᵐ p ∂(ageμ c (-3 / 2)), ‖g p‖ₑ ≤ ‖u p‖ₑ := by
    apply ae_ageThreeHalves_of_z1 (c := c) (mZ := mZ) (fun p => ‖g p‖ₑ ≤ ‖u p‖ₑ)
    rw [← NearInst.ae_gainZ1Measure c mZ γ ν]
    filter_upwards [hg, hu] with p hp1 hp2
    rw [← hp2]
    exact hp1
  have hmemu : MemLp u 2 (z1Measure c mZ) := by
    refine ⟨hum.aestronglyMeasurable, ?_⟩
    have hK := eLpNorm_z1_le_gain (c := c) (mZ := mZ) hγ hν hum
    have hfin : eLpNorm u 2 (gainZ1Measure c mZ γ ν) < ⊤ := by
      rw [← eLpNorm_congr_ae hu]
      exact (Lp.memLp _).eLpNorm_lt_top
    exact lt_of_le_of_lt hK (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  set f : Z1sp c mZ := hmemu.toLp u with hf
  have hfu : (f : Chart → Ten3) =ᵐ[z1Measure c mZ] u := hmemu.coeFn_toLp
  have hfu' : ∀ᵐ p ∂(ageμ c (-3 / 2)), ‖(f : Chart → Ten3) p‖ₑ = ‖u p‖ₑ :=
    ae_ageThreeHalves_of_z1 (c := c) (mZ := mZ) (fun p => ‖(f : Chart → Ten3) p‖ₑ = ‖u p‖ₑ)
      (hfu.mono fun p hp => by rw [hp])
  have hTMf := hCb c hc a ha f
  have hE : ‖f‖ₑ = eLpNorm u 2 (z1Measure c mZ) := by
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae hfu
  have hTfst : ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))‖ₑ
      = eLpNorm u 2 (gainZ1Measure c mZ γ ν) := by
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae hu
  have hfin : ‖f‖ₑ ≤ ENNReal.ofReal (Real.exp (γ / ν))
      * ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))‖ₑ := by
    rw [hE, hTfst]
    exact eLpNorm_z1_le_gain hγ hν hum
  have hTn : ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))‖ₑ ≤ ‖T‖ₑ :=
    WithLp.enorm_fst_le (x := T)
  have hX : 0 ≤ a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ)) :=
    add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  have hcpos : 0 ≤ c ^ k := pow_nonneg (by linarith) _
  have hA : ENNReal.ofReal (C * c ^ k * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ))))
      ≤ ENNReal.ofReal (|C| * c ^ k * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ)))) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hcpos) hX
  unfold ageMass
  calc ∫⁻ p in {p : Chart | a < p.1}, ‖g p‖ₑ ∂(ageμ c (-3 / 2))
      ≤ ∫⁻ p in {p : Chart | a < p.1}, ‖u p‖ₑ ∂(ageμ c (-3 / 2)) :=
        lintegral_mono_ae (ae_restrict_of_ae hgu)
    _ = ∫⁻ p in {p : Chart | a < p.1}, ‖(f : Chart → Ten3) p‖ₑ ∂(ageμ c (-3 / 2)) :=
        lintegral_congr_ae (ae_restrict_of_ae (hfu'.mono fun p hp => hp.symm))
    _ ≤ ENNReal.ofReal (C * c ^ k * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ)))) * ‖f‖ₑ := hTMf
    _ ≤ ENNReal.ofReal (|C| * c ^ k * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ))))
          * (ENNReal.ofReal (Real.exp (γ / ν))
            * ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))‖ₑ) :=
        mul_le_mul' hA hfin
    _ ≤ ENNReal.ofReal (|C| * c ^ k * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ))))
          * (ENNReal.ofReal (Real.exp (γ / ν)) * ‖T‖ₑ) :=
        by gcongr
    _ = ENNReal.ofReal (|C| * c ^ k * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ)))
            * Real.exp (γ / ν)) * ‖T‖ₑ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (abs_nonneg C) hcpos) hX)]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
