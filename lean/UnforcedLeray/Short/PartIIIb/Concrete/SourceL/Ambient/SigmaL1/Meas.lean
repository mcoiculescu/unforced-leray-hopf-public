import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_4
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1.Polar

/-!
# `SigmaMeas` (source 4771-4775)

`Σ_M(x') = Q(φ)(ρ⁻¹ E(ρ⁻²)) Q(φ)ᵀ` is a.e. strongly measurable on the plane.  The phase mean
`E(u)` is a.e. measurable in `u` (Fubini on `oldMeasure`), and `x' ↦ u(x') = (x'₁²+x'₂²)⁻¹`
pulls back a.e. statements through the polar-coordinate null-set lemma `polar_null`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

instance sfinite_avgμ_meas (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ Cyl.cellμ
  infer_instance

/-- Pullback of an a.e. strongly measurable function on `(0,∞)` along `x' ↦ (x'₁²+x'₂²)⁻¹`. -/
theorem pullback_aesm {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (fun x' : ℝ × ℝ => g ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) volume := by
  have hGm : Measurable (hg.mk g) := hg.measurable_mk
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), g u = hg.mk g u := hg.ae_eq_mk
  have hae' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioi (0 : ℝ) → g u = hg.mk g u :=
    (ae_restrict_iff' measurableSet_Ioi).1 hae
  obtain ⟨t, hsubt, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae')
  have hnull := polar_null htm ht0
  have hz : ∀ᵐ x' : ℝ × ℝ, x' ≠ 0 := by
    rw [ae_iff]
    have h0 : (volume : Measure (ℝ × ℝ)) ({0} : Set (ℝ × ℝ)) = 0 := by
      have hs : ({0} : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ ({0} : Set ℝ) := by
        ext x
        simp [Prod.ext_iff]
      rw [hs, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    simp only [Set.setOf_eq_eq_singleton, Set.mem_singleton_iff, ne_eq, not_not]
    exact h0
  have hcongr : (fun x' : ℝ × ℝ => g ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) =ᵐ[volume]
      (fun x' : ℝ × ℝ => hg.mk g ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) := by
    filter_upwards [hnull, hz] with x' hx hx0
    have hs : 0 < x'.1 ^ 2 + x'.2 ^ 2 := by
      rcases (show (0 : ℝ) ≤ x'.1 ^ 2 + x'.2 ^ 2 by positivity).lt_or_eq with h | h
      · exact h
      · exfalso
        apply hx0
        have h1 : x'.1 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg x'.2]) (sq_nonneg _)
        have h2 : x'.2 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg x'.1]) (sq_nonneg _)
        exact Prod.ext (pow_eq_zero_iff two_ne_zero |>.1 h1) (pow_eq_zero_iff two_ne_zero |>.1 h2)
    have hnt : (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∉ t := fun h => hx ⟨hs, h⟩
    by_contra hc
    exact hnt (hsubt (fun h => hc (h (inv_pos.2 hs))))
  exact (hGm.comp (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).inv)
    |>.aestronglyMeasurable).congr hcongr.symm

/-- Multiplying the outward cutoff `χ_o(ν·)` into an a.e. measurable function on the old region. -/
theorem chi_mul_aesm {χo : ℝ → ℝ} {ν : ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo) (F : ℝ → ℝ)
    (hF : AEStronglyMeasurable F (volume.restrict (Ioi (6 / 5 / ν)))) :
    AEStronglyMeasurable (fun u => χo (ν * u) * F u) (volume.restrict (Ioi (0 : ℝ))) := by
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hind : (fun u => χo (ν * u) * F u) =
      (Ioi (6 / 5 / ν)).indicator (fun u => χo (ν * u) * F u) := by
    funext u
    by_cases hu : u ∈ Ioi (6 / 5 / ν)
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      have hu' : u ≤ 6 / 5 / ν := by
        simp only [Set.mem_Ioi, not_lt] at hu
        exact hu
      have h1 : ν * u ≤ 6 / 5 := by
        calc ν * u ≤ ν * (6 / 5 / ν) := mul_le_mul_of_nonneg_left hu' hν.le
          _ = 6 / 5 := by field_simp
      rw [hχ.zero _ h1, zero_mul]
  have hcont : Continuous (fun u : ℝ => χo (ν * u)) :=
    hχ.smooth.continuous.comp (continuous_const.mul continuous_id)
  rw [hind, aestronglyMeasurable_indicator_iff measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi, sup_eq_left.2 ha.le]
  exact hcont.aestronglyMeasurable.mul hF

/-- Each entry of the phase mean is a.e. strongly measurable in `u` on `(0,∞)`. -/
theorem phaseMean_entry_aesm {c ν : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) (i j : Fin 3) :
    AEStronglyMeasurable (fun u => phaseMean c ν χo M u i j) (volume.restrict (Ioi (0 : ℝ))) := by
  by_cases h : i = 1 ∨ j = 1
  · have hfun : (fun u => phaseMean c ν χo M u i j) = fun _ => (0 : ℝ) := by
      funext u
      simp [phaseMean, h]
    rw [hfun]
    exact aestronglyMeasurable_const
  · have hfun : (fun u => phaseMean c ν χo M u i j) =
        fun u => χo (ν * u) * ∫ x, M (u, x) i j ∂(Cyl.avgμ c) := by
      funext u
      simp [phaseMean, h]
    rw [hfun]
    have hMij0 := ((continuous_apply j).comp (continuous_apply i)).comp_aestronglyMeasurable hM.1
    have hMij : AEStronglyMeasurable (fun p : Chart => M p i j)
        ((volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c)) := hMij0
    have hF : AEStronglyMeasurable (fun u => ∫ x, M (u, x) i j ∂(Cyl.avgμ c))
        (volume.restrict (Ioi (6 / 5 / ν))) := hMij.integral_prod_right'
    exact chi_mul_aesm hν hχ (fun u => ∫ x, M (u, x) i j ∂(Cyl.avgμ c)) hF

/-- Each entry `(a, b)` of `Σ_M` is a.e. strongly measurable on the plane. -/
theorem sigmaM_entry_aesm {c ν : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) (a b : Fin 3) :
    AEStronglyMeasurable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' a b) volume := by
  have hE : ∀ i j : Fin 3, AEStronglyMeasurable
      (fun x' : ℝ × ℝ => phaseMean c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) i j) volume :=
    fun i j => pullback_aesm (phaseMean_entry_aesm hν hχ M hM i j)
  have hsqrt : Measurable (fun x' : ℝ × ℝ => Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) :=
    Real.continuous_sqrt.measurable.comp
      ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
  have hrot : ∀ i j : Fin 3, Measurable (fun x' : ℝ × ℝ => rotQ x' i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rotQ] <;>
      first
      | exact measurable_const
      | exact measurable_fst.div hsqrt
      | exact (measurable_snd.div hsqrt).neg
      | exact measurable_snd.div hsqrt
  show AEStronglyMeasurable (fun x' : ℝ × ℝ => ∑ i, ∑ j, rotQ x' a i *
    ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * phaseMean c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) i j) *
      rotQ x' b j) volume
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  exact ((hrot a i).aestronglyMeasurable.mul
    (hsqrt.inv.aestronglyMeasurable.mul (hE i j))).mul (hrot b j).aestronglyMeasurable

/-- `SigmaMeas`: `Σ_M` is a.e. strongly measurable on the plane. -/
theorem sigmaMeas : SigmaMeas := by
  intro c ν χo hc hν hχ M hM
  have hent : ∀ a b : Fin 3, AEStronglyMeasurable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' a b) volume :=
    fun a b => sigmaM_entry_aesm hν hχ M hM a b
  exact (aemeasurable_pi_iff.2 fun a => aemeasurable_pi_iff.2 fun b =>
    (hent a b).aemeasurable).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
