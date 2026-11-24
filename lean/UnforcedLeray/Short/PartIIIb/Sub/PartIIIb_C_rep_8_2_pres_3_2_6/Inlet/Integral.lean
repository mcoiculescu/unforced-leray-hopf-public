import UnforcedLeray.Lib.Axisymmetric.RingMeasure
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.WeightNorm.EtaInt

/-!
# The `L^{11/4}(ℝ³)` norm of a ring envelope (helper of `PartIII-b:C/rep/8/2/pres/3/2/6/1`)

Source `the November 2 reference manuscript`
2385-2386 ("The integrability exponent is `-9/8 + p = 13/8 > -1`"), 2681-2688 (the physical space
Jacobian after azimuthal integration is `πR² s^{-5/2} ds dη`).

A field on `ℝ³` bounded off the axis by the ring envelope
`1_{0<s≤H/2} M s^{3/2} (1+|η|)^N e^{-κ|η|/c}` at `s = R²/ϱ²`, `η = Ry₃/ϱ` has
`‖f‖_{L^{11/4}} ≤ K M (1+H) c^{N+1} R^{8/11}`: by `Axi.lintegral_ringChart`, the `p`-th power of
the norm is `πR² ∫ s^{-5/2} W^p ds dη`, the age integral is `∫_0^{H/2} M^p s^{13/8} ds`, and the
transverse integral is `UnforcedLeray.Short.IIb.WeightNormAux.lintegral_eta_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet

open UnforcedLeray.Axi

/-- The ring envelope `1_{0<s≤H/2} M s^{3/2} (1+|η|)^N e^{-κ|η|/c}`. -/
def ringEnv (H M κ c : ℝ) (N : ℕ) (s η : ℝ) : ℝ :=
  (Ioc 0 (H / 2)).indicator (fun s => M * s ^ (3 / 2 : ℝ)) s *
    ((1 + |η|) ^ N * Real.exp (-(κ * |η| / c)))

theorem ringEnv_of_mem {H M κ c : ℝ} {N : ℕ} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ H / 2) (η : ℝ) :
    ringEnv H M κ c N s η = M * s ^ (3 / 2 : ℝ) * ((1 + |η|) ^ N * Real.exp (-(κ * |η| / c))) := by
  rw [ringEnv, indicator_of_mem (show s ∈ Ioc 0 (H / 2) from ⟨hs0, hs⟩)]

theorem ringEnv_nonneg {H M κ c : ℝ} {N : ℕ} (hM : 0 ≤ M) (s η : ℝ) :
    0 ≤ ringEnv H M κ c N s η := by
  unfold ringEnv
  apply mul_nonneg
  · by_cases hs : s ∈ Ioc 0 (H / 2)
    · rw [indicator_of_mem hs]
      exact mul_nonneg hM (Real.rpow_nonneg hs.1.le _)
    · rw [indicator_of_notMem hs]
  · positivity

theorem measurable_ringEnv (H M κ c : ℝ) (N : ℕ) :
    Measurable fun z : ℝ × ℝ => ringEnv H M κ c N z.1 z.2 := by
  unfold ringEnv
  refine Measurable.mul ?_ ?_
  · exact ((measurable_const.mul (measurable_id.pow_const _)).indicator measurableSet_Ioc).comp
      measurable_fst
  · fun_prop

theorem sqrt_mul_self_eq_rpow {s : ℝ} (hs : 0 ≤ s) : √s * s = s ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add' hs (by norm_num),
    Real.rpow_one]

theorem eleven_fourths : (11 / 4 : ℝ≥0∞) = ENNReal.ofReal (11 / 4) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- **The `L^{11/4}(ℝ³)` norm of a ring envelope** (source 2385-2386, 2681-2688). -/
theorem eLpNorm_le_of_ringEnv (N : ℕ) {κ : ℝ} (hκ : 0 < κ) : ∃ K : ℝ, 0 < K ∧
    ∀ (R c H M : ℝ) (f : Space → Space), 0 < R → 1 ≤ c → 0 < H → 0 ≤ M →
      (∀ y : Space, y ∉ axis → ‖f y‖ ≤ ringEnv H M κ c N (age R y) (trans R y)) →
      eLpNorm f (11 / 4) volume ≤
        ENNReal.ofReal (K * M * (1 + H) * c ^ (N + 1) * R ^ (8 / 11 : ℝ)) := by
  set q : ℝ := 11 / 4 with hq
  have hq0 : 0 < q := by rw [hq]; norm_num
  obtain ⟨K', hK', hE⟩ := UnforcedLeray.Short.IIb.WeightNormAux.lintegral_eta_le (m := (N : ℝ) * q) (b := q * κ)
    (by positivity) (by positivity)
  refine ⟨(Real.pi * K') ^ (1 / q), by positivity, ?_⟩
  intro R c H M f hR hc hH hM hbd
  have hc0 : 0 < c := by linarith
  set g : Space → ℝ := fun y => ringEnv H M κ c N (age R y) (trans R y) with hg
  have h1 : eLpNorm f (11 / 4) volume ≤ eLpNorm g (11 / 4) volume := by
    apply eLpNorm_mono_ae
    filter_upwards [ae_not_mem_axis] with y hy
    rw [hg, Real.norm_of_nonneg (ringEnv_nonneg hM _ _)]
    exact hbd y hy
  refine h1.trans ?_
  rw [eleven_fourths, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by norm_num)]
  rw [← hq]
  -- the integrand in chart variables
  set G : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (ringEnv H M κ c N z.1 z.2) ^ q with hG
  have hGm : Measurable G :=
    (ENNReal.measurable_ofReal.comp (measurable_ringEnv H M κ c N)).pow_const q
  have hin : ∫⁻ y, ‖g y‖ₑ ^ q = ∫⁻ y, G (age R y, trans R y) := by
    refine lintegral_congr fun y => ?_
    simp only [hg, hG]
    rw [Real.enorm_of_nonneg (ringEnv_nonneg hM _ _)]
  rw [hin, lintegral_ringChart hR G hGm]
  -- separate variables
  set φ : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal ((Ioc 0 (H / 2)).indicator (fun s => M * s ^ (3 / 2 : ℝ)) s) with hφ
  set ψ : ℝ → ℝ≥0∞ := fun η => ENNReal.ofReal ((1 + |η|) ^ N * Real.exp (-(κ * |η| / c)))
    with hψ
  have hφm : Measurable φ :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (measurable_id.pow_const _)).indicator measurableSet_Ioc)
  have hψm : Measurable ψ := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hsplit : ∀ z : ℝ × ℝ, ENNReal.ofReal (z.1 ^ (-(5 / 2 : ℝ))) * G z =
      (ENNReal.ofReal (z.1 ^ (-(5 / 2 : ℝ))) * φ z.1 ^ q) * ψ z.2 ^ q := by
    intro z
    have hind : 0 ≤ (Ioc 0 (H / 2)).indicator (fun s => M * s ^ (3 / 2 : ℝ)) z.1 := by
      by_cases hs : z.1 ∈ Ioc 0 (H / 2)
      · rw [indicator_of_mem hs]; exact mul_nonneg hM (Real.rpow_nonneg hs.1.le _)
      · rw [indicator_of_notMem hs]
    simp only [hG, hφ, hψ, ringEnv]
    rw [ENNReal.ofReal_mul hind, ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    ring
  have hA : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (hφm.pow_const q)
  have hB : Measurable fun η : ℝ => ψ η ^ q := hψm.pow_const q
  have hprod : ∫⁻ z in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal (z.1 ^ (-(5 / 2 : ℝ))) * G z =
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q) *
        ∫⁻ η : ℝ, ψ η ^ q := by
    have hv : (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) =
        (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [hv, lintegral_congr hsplit]
    exact lintegral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume)
      (f := fun s : ℝ => ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q)
      (g := fun η : ℝ => ψ η ^ q) hA.aemeasurable hB.aemeasurable
  rw [hprod]
  -- the age integral
  have hage : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q ≤
      ENNReal.ofReal (M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) := by
    have hpt : ∀ s : ℝ, ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q ≤
        (Ioc 0 (H / 2)).indicator
          (fun _ => ENNReal.ofReal (M ^ q * (H / 2) ^ ((13 : ℝ) / 8))) s := by
      intro s
      by_cases hs : s ∈ Ioc 0 (H / 2)
      · have hs0 : 0 < s := hs.1
        rw [indicator_of_mem hs, hφ]
        simp only
        rw [indicator_of_mem hs,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hM (Real.rpow_nonneg hs0.le _)) hq0.le,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]
        apply ENNReal.ofReal_le_ofReal
        have e1 : s ^ (-(5 / 2 : ℝ)) * (M * s ^ (3 / 2 : ℝ)) ^ q = M ^ q * s ^ ((13 : ℝ) / 8) := by
          rw [Real.mul_rpow hM (Real.rpow_nonneg hs0.le _), ← Real.rpow_mul hs0.le]
          have e2 : s ^ (-(5 / 2 : ℝ)) * s ^ ((3 / 2 : ℝ) * q) = s ^ ((13 : ℝ) / 8) := by
            rw [← Real.rpow_add hs0, hq]
            norm_num
          calc s ^ (-(5 / 2 : ℝ)) * (M ^ q * s ^ ((3 / 2 : ℝ) * q))
              = M ^ q * (s ^ (-(5 / 2 : ℝ)) * s ^ ((3 / 2 : ℝ) * q)) := by ring
            _ = M ^ q * s ^ ((13 : ℝ) / 8) := by rw [e2]
        rw [e1]
        have h2 : s ^ ((13 : ℝ) / 8) ≤ (H / 2) ^ ((13 : ℝ) / 8) :=
          Real.rpow_le_rpow hs0.le hs.2 (by norm_num)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      · rw [indicator_of_notMem hs, hφ]
        simp only
        rw [indicator_of_notMem hs, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq0, mul_zero]
    calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q
        ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioc 0 (H / 2)).indicator
            (fun _ => ENNReal.ofReal (M ^ q * (H / 2) ^ ((13 : ℝ) / 8))) s := lintegral_mono hpt
      _ = ENNReal.ofReal (M ^ q * (H / 2) ^ ((13 : ℝ) / 8)) *
            (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 (H / 2)) :=
          lintegral_indicator_const measurableSet_Ioc _
      _ = ENNReal.ofReal (M ^ q * (H / 2) ^ ((13 : ℝ) / 8)) * ENNReal.ofReal (H / 2) := by
          rw [Measure.restrict_apply measurableSet_Ioc,
            Set.inter_eq_left.2 Ioc_subset_Ioi_self, Real.volume_Ioc]
          simp
      _ = ENNReal.ofReal (M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : (H / 2) ^ ((21 : ℝ) / 8) = (H / 2) ^ ((13 : ℝ) / 8) * (H / 2) := by
            rw [show (21 : ℝ) / 8 = 13 / 8 + 1 by norm_num, Real.rpow_add (by positivity),
              Real.rpow_one]
          rw [this]; ring
  -- the transverse integral
  have heta : ∫⁻ η : ℝ, ψ η ^ q ≤ ENNReal.ofReal (K' * c ^ ((N : ℝ) * q + 1)) := by
    have hψq : ∀ η : ℝ, ψ η ^ q =
        ENNReal.ofReal ((1 + |η|) ^ ((N : ℝ) * q) * Real.exp (-(q * κ * |η| / c))) := by
      intro η
      rw [hψ]
      simp only
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
      congr 1
      rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity), ← Real.exp_mul]
      congr 2; ring
    simp_rw [hψq]
    exact hE c hc
  -- assemble
  have hint : ENNReal.ofReal (Real.pi * R ^ 2) *
      ((∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q) *
        ∫⁻ η : ℝ, ψ η ^ q) ≤
      ENNReal.ofReal (Real.pi * R ^ 2 * (M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) *
        (K' * c ^ ((N : ℝ) * q + 1))) := by
    have e : ENNReal.ofReal (Real.pi * R ^ 2 * (M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) *
        (K' * c ^ ((N : ℝ) * q + 1))) = ENNReal.ofReal (Real.pi * R ^ 2) *
        (ENNReal.ofReal (M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) *
          ENNReal.ofReal (K' * c ^ ((N : ℝ) * q + 1))) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_assoc]
    rw [e]
    gcongr
  have hbound : ENNReal.ofReal (Real.pi * R ^ 2 * (M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) *
        (K' * c ^ ((N : ℝ) * q + 1))) ≤
      ENNReal.ofReal ((Real.pi * K') ^ (1 / q) * M * (1 + H) * c ^ (N + 1) *
        R ^ (8 / 11 : ℝ)) ^ q := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
    apply ENNReal.ofReal_le_ofReal
    have e1 : ((Real.pi * K') ^ (1 / q) * M * (1 + H) * c ^ (N + 1) * R ^ (8 / 11 : ℝ)) ^ q =
        Real.pi * K' * M ^ q * (1 + H) ^ q * c ^ ((N : ℝ) * q + q) * R ^ 2 := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
        (by positivity), Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hq0.ne', Real.rpow_one,
        ← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_mul hR.le]
      have hR2 : R ^ ((8 / 11 : ℝ) * q) = R ^ 2 := by
        rw [hq, show (8 / 11 : ℝ) * (11 / 4) = (2 : ℕ) by norm_num, Real.rpow_natCast]
      rw [hR2]
      congr 2
      push_cast; ring
    rw [e1]
    have h1 : (H / 2) ^ ((21 : ℝ) / 8) ≤ (1 + H) ^ q := by
      calc (H / 2) ^ ((21 : ℝ) / 8) ≤ (1 + H) ^ ((21 : ℝ) / 8) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ ≤ (1 + H) ^ q :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hq]; norm_num)
    have h2 : c ^ ((N : ℝ) * q + 1) ≤ c ^ ((N : ℝ) * q + q) :=
      Real.rpow_le_rpow_of_exponent_le hc (by rw [hq]; linarith)
    have hMq : 0 ≤ M ^ q := by positivity
    calc Real.pi * R ^ 2 * (M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) * (K' * c ^ ((N : ℝ) * q + 1))
        = Real.pi * K' * M ^ q * R ^ 2 * ((H / 2) ^ ((21 : ℝ) / 8) * c ^ ((N : ℝ) * q + 1)) := by
          ring
      _ ≤ Real.pi * K' * M ^ q * R ^ 2 * ((1 + H) ^ q * c ^ ((N : ℝ) * q + q)) := by
          gcongr
      _ = _ := by ring
  calc (ENNReal.ofReal (Real.pi * R ^ 2) *
        ((∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q) *
          ∫⁻ η : ℝ, ψ η ^ q)) ^ (1 / q)
      ≤ (ENNReal.ofReal ((Real.pi * K') ^ (1 / q) * M * (1 + H) * c ^ (N + 1) *
          R ^ (8 / 11 : ℝ)) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (hint.trans hbound) (by positivity)
    _ = _ := by rw [one_div]; exact ENNReal.rpow_rpow_inv hq0.ne' _

end UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet
