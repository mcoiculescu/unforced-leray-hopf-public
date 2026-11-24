import UnforcedLeray.Short.PartI.Sub.PartI_S15_2
import UnforcedLeray.Short.PartI.Tasks.SeedFunctionalProof
import UnforcedLeray.Short.PartI.Tasks.SeedModeRegularityProof

/-!
# Part I, task `PartI:S15/2/1`: `seedDualBounded`

Source: `the November 2 reference manuscript` lines 603-609 (eq. `short-seed-functional`)
and 841-889.  The functional `f ↦ seedEll h f` is represented by the weight
`W r = (2π (1+r²)^M)⁻¹ · h(r)/k(r)` against the profile measure `2π r (1+r²)^M dr`, and
`W ∈ L²(profileMeasure M)` because

* on `(0,1]`, `|k| ≥ 1`, so `|h/k|² r ≤ |h|² r`, integrable by `MemLp h 2 (profileMeasure 0)`;
* on `[1,∞)`, `|h/k| ≤ C/r²` (from `seedFunctional_proof` applied to the smooth representative
  of `h`, which exists by `seedModeRegularity_proof`), so `|h/k|² r ≤ C² r⁻³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartI

/-- `|k(s)| ≥ 1` on `(0,1]`, where `k(s) = (s²/4 - 2) e^{-s²/4}`. -/
theorem dualBounded_abs_ge_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    1 ≤ |Blueprint.Planar.strainK s| := by
  have ht0 : 0 ≤ s ^ 2 / 4 := by positivity
  have ht1 : s ^ 2 / 4 ≤ 1 / 4 := by nlinarith
  have hexp : 1 - s ^ 2 / 4 ≤ Real.exp (-(s ^ 2 / 4)) := by
    have := Real.add_one_le_exp (-(s ^ 2 / 4))
    linarith
  have habs : |Blueprint.Planar.strainK s| = (2 - s ^ 2 / 4) * Real.exp (-(s ^ 2 / 4)) := by
    unfold Blueprint.Planar.strainK
    have e : -(s ^ 2) / 4 = -(s ^ 2 / 4) := by ring
    rw [e, abs_mul, abs_of_neg (show s ^ 2 / 4 - 2 < 0 by linarith),
      abs_of_pos (Real.exp_pos _)]
    ring
  rw [habs]
  have h2 : (2 - s ^ 2 / 4) * (1 - s ^ 2 / 4) ≤ (2 - s ^ 2 / 4) * Real.exp (-(s ^ 2 / 4)) :=
    mul_le_mul_of_nonneg_left hexp (by linarith)
  nlinarith [sq_nonneg (s ^ 2 / 4)]

/-- The weight `W r = (2π (1+r²)^M)⁻¹ · h(r)/k(r)` of the dual functional. -/
def dualW (M : ℝ) (h : ℝ → ℂ) (s : ℝ) : ℂ :=
  (((2 * π * (1 + s ^ 2) ^ M)⁻¹ : ℝ) : ℂ) * (h s / (Blueprint.Planar.strainK s : ℂ))

/-- The weighted quantity `|h/k|² r` is integrable on `(0,∞)`, given the local `L²` bound at
weight `0` and the `O(r⁻²)` bound on `[1,∞)`. -/
theorem dualBounded_weight {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi 0)))
    (h0 : IntegrableOn (fun s => ‖h s‖ ^ 2 * s) (Ioi 0)) {C : ℝ}
    (hC : ∀ᵐ r ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖h r / (Blueprint.Planar.strainK r : ℂ)‖ ≤ C / r ^ 2) :
    IntegrableOn (fun s => ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s) (Ioi 0) := by
  have hkm : Measurable (fun s : ℝ => (Blueprint.Planar.strainK s : ℂ)) := by
    have hc : Continuous (fun s : ℝ => (Blueprint.Planar.strainK s : ℂ)) := by
      unfold Blueprint.Planar.strainK
      fun_prop
    exact hc.measurable
  have hdk : AEStronglyMeasurable (fun s => h s / (Blueprint.Planar.strainK s : ℂ))
      (volume.restrict (Ioi 0)) := by
    have e : (fun s => h s / (Blueprint.Planar.strainK s : ℂ)) =
        fun s => h s * ((Blueprint.Planar.strainK s : ℂ))⁻¹ := by
      funext s
      rw [div_eq_mul_inv]
    rw [e]
    exact hm.mul hkm.inv.aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun s => ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s)
      (volume.restrict (Ioi 0)) :=
    (hdk.norm.pow 2).mul aestronglyMeasurable_id
  have hI1 : IntegrableOn (fun s => ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s) (Ioc 0 1) := by
    refine Integrable.mono' (g := fun s => ‖h s‖ ^ 2 * s) (h0.mono_set Ioc_subset_Ioi_self)
      (hF.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 < s := hs.1
    have hk1 := dualBounded_abs_ge_one hs0 hs.2
    have hle : ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ≤ ‖h s‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (norm_nonneg _) hk1
    have hnn : 0 ≤ ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s :=
      mul_nonneg (sq_nonneg _) hs0.le
    show ‖‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s‖ ≤ ‖h s‖ ^ 2 * s
    rw [Real.norm_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hle 2) hs0.le
  have hI2 : IntegrableOn (fun s => ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s) (Ioi 1) := by
    have hb : IntegrableOn (fun s : ℝ => C ^ 2 * s ^ (-3 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul (C ^ 2)
    refine Integrable.mono' hb
      (hF.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl)) ?_
    filter_upwards [hC, ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
      with s hs hs1
    have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs1
    have hn : 0 ≤ ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ hn hs 2
    have hcalc : (C / s ^ 2) ^ 2 * s = C ^ 2 * s ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le, Real.rpow_natCast]
      field_simp
    have hnn : 0 ≤ ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s :=
      mul_nonneg (sq_nonneg _) hs0.le
    show ‖‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s‖ ≤ C ^ 2 * s ^ (-3 : ℝ)
    rw [Real.norm_of_nonneg hnn]
    calc ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s ≤ (C / s ^ 2) ^ 2 * s :=
          mul_le_mul_of_nonneg_right hsq hs0.le
      _ = C ^ 2 * s ^ (-3 : ℝ) := hcalc
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact integrableOn_union.2 ⟨hI1, hI2⟩

/-- The conjugated weight lies in `L²(profileMeasure M)` for `M ≥ 0`. -/
theorem dualBounded_memLp {M : ℝ} (hM : 0 ≤ M) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi 0)))
    (hI : IntegrableOn (fun s => ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s) (Ioi 0)) :
    MemLp (fun s => (starRingEnd ℂ) (dualW M h s)) 2 (Planar.profileMeasure M) := by
  have hkm : Measurable (fun s : ℝ => (Blueprint.Planar.strainK s : ℂ)) := by
    have hc : Continuous (fun s : ℝ => (Blueprint.Planar.strainK s : ℂ)) := by
      unfold Blueprint.Planar.strainK
      fun_prop
    exact hc.measurable
  have hdk : AEStronglyMeasurable (fun s => h s / (Blueprint.Planar.strainK s : ℂ))
      (volume.restrict (Ioi 0)) := by
    have e : (fun s => h s / (Blueprint.Planar.strainK s : ℂ)) =
        fun s => h s * ((Blueprint.Planar.strainK s : ℂ))⁻¹ := by
      funext s
      rw [div_eq_mul_inv]
    rw [e]
    exact hm.mul hkm.inv.aestronglyMeasurable
  have hmeasP : Measurable (fun s : ℝ => (1 + s ^ 2) ^ M) :=
    Measurable.pow_const (by fun_prop) M
  have hmeasW : Measurable (fun s : ℝ => (((2 * π * (1 + s ^ 2) ^ M)⁻¹ : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_const.mul hmeasP).inv)
  have hW : AEStronglyMeasurable (fun s => dualW M h s) (volume.restrict (Ioi 0)) :=
    hmeasW.aestronglyMeasurable.mul hdk
  have hWc : AEStronglyMeasurable (fun s => (starRingEnd ℂ) (dualW M h s))
      (volume.restrict (Ioi 0)) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hW
  refine (Planar.memLp_profile_iff hWc).2 ?_
  have hF : AEStronglyMeasurable
      (fun s => ‖(starRingEnd ℂ) (dualW M h s)‖ ^ 2 * (s * (1 + s ^ 2) ^ M))
      (volume.restrict (Ioi 0)) :=
    (hWc.norm.pow 2).mul (aestronglyMeasurable_id.mul hmeasP.aestronglyMeasurable)
  refine Integrable.mono' (hI.const_mul ((4 * π ^ 2)⁻¹)) hF ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with s hs
  have hs0 : (0 : ℝ) < s := hs
  have hP1 : (1 : ℝ) ≤ (1 + s ^ 2) ^ M :=
    Real.one_le_rpow (by nlinarith [sq_nonneg s]) hM
  have hnW : ‖(starRingEnd ℂ) (dualW M h s)‖ =
      (2 * π * (1 + s ^ 2) ^ M)⁻¹ * ‖h s / (Blueprint.Planar.strainK s : ℂ)‖ := by
    unfold dualW
    rw [RCLike.norm_conj, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hnn : 0 ≤ ‖(starRingEnd ℂ) (dualW M h s)‖ ^ 2 * (s * (1 + s ^ 2) ^ M) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  show ‖‖(starRingEnd ℂ) (dualW M h s)‖ ^ 2 * (s * (1 + s ^ 2) ^ M)‖ ≤
    (4 * π ^ 2)⁻¹ * (‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s)
  rw [Real.norm_of_nonneg hnn, hnW]
  have key : ((2 * π * (1 + s ^ 2) ^ M)⁻¹ * ‖h s / (Blueprint.Planar.strainK s : ℂ)‖) ^ 2 *
      (s * (1 + s ^ 2) ^ M) =
      (4 * π ^ 2)⁻¹ * (‖h s / (Blueprint.Planar.strainK s : ℂ)‖ ^ 2 * s) *
        ((1 + s ^ 2) ^ M)⁻¹ := by
    have hPne : (1 + s ^ 2) ^ M ≠ 0 := by positivity
    field_simp
    ring
  rw [key]
  exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ hP1)

/-- **Target.** The explicit functional `f ↦ seedEll h f` is bounded on the weighted profile
space `L²(2π r ⟨r⟩^{2M} dr)` for `M > 1`. -/
theorem seedDualBounded : SeedDualBounded := by
  intro lam h hh ℓ hIS M hM
  have hM0 : (0 : ℝ) ≤ M := by linarith
  -- (a) `h` is in `L²` of the weight-zero profile measure
  have hae0 : (⇑(hh.toLp h)) =ᵐ[Planar.profileMeasure 0] h :=
    (profileMeasure_ac_xGMeasure (le_refl (0 : ℝ))).ae_le (MemLp.coeFn_toLp hh)
  have hmemh0 : MemLp h 2 (Planar.profileMeasure 0) :=
    MemLp.ae_eq hae0 (memLp_xgEmbM (le_refl (0 : ℝ)) (hh.toLp h))
  have hm : AEStronglyMeasurable h (volume.restrict (Ioi 0)) :=
    hmemh0.aestronglyMeasurable.mono_ac (Planar.ac_profileMeasure 0)
  have h0 : IntegrableOn (fun s => ‖h s‖ ^ 2 * s) (Ioi 0) := by
    have := (Planar.memLp_profile_iff hm).1 hmemh0
    simpa [Real.rpow_zero] using this
  -- (b) the regular representative and the `O(r⁻²)` bound on `[1,∞)`
  obtain ⟨-, -, h', hae', hsm, -⟩ := seedModeRegularity_proof lam h hh ℓ hIS
  have hae'' : h' =ᵐ[B0010.xGMeasure] h := B0012.xG_ac.ae_le hae'
  have hh' : MemLp h' 2 B0010.xGMeasure := MemLp.ae_eq hae''.symm hh
  have heq : hh'.toLp h' = hh.toLp h := (MemLp.toLp_eq_toLp_iff hh' hh).2 hae''
  have hIS' : IsSeedXG lam (hh'.toLp h') ℓ := by
    rw [heq]
    exact hIS
  obtain ⟨-, -, -, -, hg⟩ := seedFunctional_proof lam h' hh' ℓ hIS'
  have hcd' : ContDiffOn ℝ ∞ h' (Ioi 0) := by
    refine (hsm.comp Complex.ofRealCLM.contDiff).contDiffOn.congr (fun r hr => ?_)
    have hr' : (0 : ℝ) < r := hr
    simp only [Function.comp, Complex.ofRealCLM_apply, seedPlanar, Planar.NUE.Ang.ofProfile,
      Planar.NUE.Ang.angPhase]
    rw [Complex.norm_real, Real.norm_of_nonneg hr'.le,
      div_self (Complex.ofReal_ne_zero.2 hr'.ne'), one_zpow, mul_one]
  obtain ⟨g, -, hgk, C, hC⟩ := hg hcd'
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    simp only [one_pow, div_one] at h1
    exact le_trans (norm_nonneg _) h1
  have hCae : ∀ᵐ r ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖h r / (Blueprint.Planar.strainK r : ℂ)‖ ≤ C / r ^ 2 := by
    have h1 : ∀ᵐ r ∂(volume.restrict (Ioi (1 : ℝ))), h' r = h r :=
      ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one) hae'
    filter_upwards [h1, ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
      with r hr hr1
    have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr1
    have hr1' : 1 ≤ r := le_of_lt hr1
    rw [← hr]
    by_cases hk : Blueprint.Planar.strainK r = 0
    · rw [hk, Complex.ofReal_zero, div_zero, norm_zero]
      exact div_nonneg hC0 (sq_nonneg r)
    · have hgr := hgk r hr0 hk
      calc ‖h' r / (Blueprint.Planar.strainK r : ℂ)‖ = ‖g r‖ := by rw [hgr]
        _ ≤ C / r ^ 2 := hC r hr1'
  -- (c) the dual weight is in `L²`, and the functional is its inner product
  have hI := dualBounded_weight hm h0 hCae
  have hmemC := dualBounded_memLp hM0 hm hI
  refine ⟨(seedJ h)⁻¹ • innerSL ℂ (hmemC.toLp _), fun f => ?_⟩
  rw [smul_apply, innerSL_apply_apply, smul_eq_mul]
  unfold seedEll
  congr 1
  have hstep1 : ∫ a, ⟪(hmemC.toLp _) a, f a⟫_ℂ ∂(Planar.profileMeasure M) =
      ∫ a, dualW M h a * f a ∂(Planar.profileMeasure M) := by
    refine integral_congr_ae ?_
    filter_upwards [hmemC.coeFn_toLp] with a ha
    simp only [ha, RCLike.inner_apply, Complex.conj_conj]
    ring
  rw [MeasureTheory.L2.inner_def, hstep1]
  rw [Planar.integral_profileMeasure M (fun a => dualW M h a * f a)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs0 : (0 : ℝ) < s := hs
  have hP : (0 : ℝ) < (1 + s ^ 2) ^ M := by positivity
  have hPc : ((1 + s ^ 2) ^ M : ℝ) ≠ 0 := hP.ne'
  have hPC : (((1 + s ^ 2) ^ M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hPc
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  have hpiC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  simp only [dualW]
  push_cast
  field_simp

end UnforcedLeray.Short.PartI
