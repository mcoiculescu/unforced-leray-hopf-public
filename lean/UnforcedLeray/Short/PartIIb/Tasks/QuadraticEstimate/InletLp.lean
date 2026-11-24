import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Inlet.Quad
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Main
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak.Calc
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Lib.AxisymmetricB.Jv

/-!
# Global `Y_{q₀}` bound on the spatial gradient of the affine inlet (`PartII-b:Q1` helper)

Proves `inlet_dy_phaseLpNorm_le`: for `z : p.Z` and `j : Fin 3`,
`phaseLpNorm p.period bgp (dy j (p.eFun (p.coord z))) ≤ ENNReal.ofReal (C_de * (p.ν ^ k_de)⁻¹ * ‖z‖)`.

In ring chart coordinates `s = R²/ϱ²`, `η = Ry₃/ϱ`, the spatial derivative `dy j (p.eFun α)` has a
linear factor `s` (not `√s`), and `s^{-5/2} · s^{11/4} = s^{1/4}` is bounded on `(0, H/2]`.
Furthermore, the ring volume factor `R^{8/11} = ε^{-8/11}` cancels the scaling `p.coord z = ε^{8/11} A`
in the ambient state norm.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.B0412 UnforcedLeray.Axi
open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet

/-- Linear-in-`s` ring envelope `1_{0<s≤H/2} (M s) (1+|η|)^N e^{-κ|η|/c}`. -/
def ringEnv1 (H M κ c : ℝ) (N : ℕ) (s η : ℝ) : ℝ :=
  (Ioc 0 (H / 2)).indicator (fun s => M * s) s *
    ((1 + |η|) ^ N * Real.exp (-(κ * |η| / c)))

theorem ringEnv1_of_mem {H M κ c : ℝ} {N : ℕ} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ H / 2) (η : ℝ) :
    ringEnv1 H M κ c N s η = M * s * ((1 + |η|) ^ N * Real.exp (-(κ * |η| / c))) := by
  rw [ringEnv1, indicator_of_mem (show s ∈ Ioc 0 (H / 2) from ⟨hs0, hs⟩)]

theorem ringEnv1_nonneg {H M κ c : ℝ} {N : ℕ} (hM : 0 ≤ M) (s η : ℝ) :
    0 ≤ ringEnv1 H M κ c N s η := by
  unfold ringEnv1
  apply mul_nonneg
  · by_cases hs : s ∈ Ioc 0 (H / 2)
    · rw [indicator_of_mem hs]
      exact mul_nonneg hM hs.1.le
    · rw [indicator_of_notMem hs]
  · positivity

theorem measurable_ringEnv1 (H M κ c : ℝ) (N : ℕ) :
    Measurable fun z : ℝ × ℝ => ringEnv1 H M κ c N z.1 z.2 := by
  unfold ringEnv1
  refine Measurable.mul ?_ ?_
  · exact ((measurable_const.mul measurable_id).indicator measurableSet_Ioc).comp measurable_fst
  · fun_prop

/-- The `L^{11/4}(ℝ³)` norm of a field bounded off the axis by `ringEnv1` (`s^{-5/2} s^{11/4} = s^{1/4}`). -/
theorem eLpNorm_le_of_ringEnv1 (N : ℕ) {κ : ℝ} (hκ : 0 < κ) : ∃ K : ℝ, 0 < K ∧
    ∀ (R c H M : ℝ) (f : Space → CVec3), 0 < R → 1 ≤ c → 0 < H → 0 ≤ M →
      (∀ y : Space, y ∉ axis → ‖f y‖ ≤ ringEnv1 H M κ c N (age R y) (trans R y)) →
      eLpNorm f (11 / 4) volume ≤
        ENNReal.ofReal (K * M * (1 + H) * c ^ (N + 1) * R ^ (8 / 11 : ℝ)) := by
  set q : ℝ := 11 / 4 with hq
  have hq0 : 0 < q := by rw [hq]; norm_num
  obtain ⟨K', hK', hE⟩ := WeightNormAux.lintegral_eta_le (m := (N : ℝ) * q) (b := q * κ)
    (by positivity) (by positivity)
  refine ⟨(Real.pi * K') ^ (1 / q), by positivity, ?_⟩
  intro R c H M f hR hc hH hM hbd
  have hc0 : 0 < c := by linarith
  set g : Space → ℝ := fun y => ringEnv1 H M κ c N (age R y) (trans R y) with hg
  have h1 : eLpNorm f (11 / 4) volume ≤ eLpNorm g (11 / 4) volume := by
    apply eLpNorm_mono_ae
    filter_upwards [ae_not_mem_axis] with y hy
    rw [hg, Real.norm_of_nonneg (ringEnv1_nonneg hM _ _)]
    exact hbd y hy
  refine h1.trans ?_
  rw [eleven_fourths, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by norm_num)]
  rw [← hq]
  set G : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (ringEnv1 H M κ c N z.1 z.2) ^ q with hG
  have hGm : Measurable G :=
    (ENNReal.measurable_ofReal.comp (measurable_ringEnv1 H M κ c N)).pow_const q
  have hin : ∫⁻ y, ‖g y‖ₑ ^ q = ∫⁻ y, G (age R y, trans R y) := by
    refine lintegral_congr fun y => ?_
    simp only [hg, hG]
    rw [Real.enorm_of_nonneg (ringEnv1_nonneg hM _ _)]
  rw [hin, lintegral_ringChart hR G hGm]
  set φ : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal ((Ioc 0 (H / 2)).indicator (fun s => M * s) s) with hφ
  set ψ : ℝ → ℝ≥0∞ := fun η => ENNReal.ofReal ((1 + |η|) ^ N * Real.exp (-(κ * |η| / c)))
    with hψ
  have hφm : Measurable φ :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul measurable_id).indicator measurableSet_Ioc)
  have hψm : Measurable ψ := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hsplit : ∀ z : ℝ × ℝ, ENNReal.ofReal (z.1 ^ (-(5 / 2 : ℝ))) * G z =
      (ENNReal.ofReal (z.1 ^ (-(5 / 2 : ℝ))) * φ z.1 ^ q) * ψ z.2 ^ q := by
    intro z
    have hind : 0 ≤ (Ioc 0 (H / 2)).indicator (fun s => M * s) z.1 := by
      by_cases hs : z.1 ∈ Ioc 0 (H / 2)
      · rw [indicator_of_mem hs]; exact mul_nonneg hM hs.1.le
      · rw [indicator_of_notMem hs]
    simp only [hG, hφ, hψ, ringEnv1]
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
  have hage : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q ≤
      ENNReal.ofReal (M ^ q * (H / 2) ^ ((5 : ℝ) / 4)) := by
    have hpt : ∀ s : ℝ, ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q ≤
        (Ioc 0 (H / 2)).indicator
          (fun _ => ENNReal.ofReal (M ^ q * (H / 2) ^ ((1 : ℝ) / 4))) s := by
      intro s
      by_cases hs : s ∈ Ioc 0 (H / 2)
      · have hs0 : 0 < s := hs.1
        rw [indicator_of_mem hs, hφ]
        simp only
        rw [indicator_of_mem hs,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hM hs0.le) hq0.le,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]
        apply ENNReal.ofReal_le_ofReal
        have e1 : s ^ (-(5 / 2 : ℝ)) * (M * s) ^ q = M ^ q * s ^ ((1 : ℝ) / 4) := by
          rw [Real.mul_rpow hM hs0.le]
          have e2 : s ^ (-(5 / 2 : ℝ)) * s ^ q = s ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_add hs0, hq]
            norm_num
          calc s ^ (-(5 / 2 : ℝ)) * (M ^ q * s ^ q)
              = M ^ q * (s ^ (-(5 / 2 : ℝ)) * s ^ q) := by ring
            _ = M ^ q * s ^ ((1 : ℝ) / 4) := by rw [e2]
        rw [e1]
        have h2 : s ^ ((1 : ℝ) / 4) ≤ (H / 2) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hs0.le hs.2 (by norm_num)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      · rw [indicator_of_notMem hs, hφ]
        simp only
        rw [indicator_of_notMem hs, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq0, mul_zero]
    calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q
        ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioc 0 (H / 2)).indicator
            (fun _ => ENNReal.ofReal (M ^ q * (H / 2) ^ ((1 : ℝ) / 4))) s := lintegral_mono hpt
      _ = ENNReal.ofReal (M ^ q * (H / 2) ^ ((1 : ℝ) / 4)) *
            (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 (H / 2)) :=
          lintegral_indicator_const measurableSet_Ioc _
      _ = ENNReal.ofReal (M ^ q * (H / 2) ^ ((1 : ℝ) / 4)) * ENNReal.ofReal (H / 2) := by
          rw [Measure.restrict_apply measurableSet_Ioc,
            Set.inter_eq_left.2 Ioc_subset_Ioi_self, Real.volume_Ioc]
          simp
      _ = ENNReal.ofReal (M ^ q * (H / 2) ^ ((5 : ℝ) / 4)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : (H / 2) ^ ((5 : ℝ) / 4) = (H / 2) ^ ((1 : ℝ) / 4) * (H / 2) := by
            rw [show (5 : ℝ) / 4 = 1 / 4 + 1 by norm_num, Real.rpow_add (by positivity),
              Real.rpow_one]
          rw [this]; ring
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
  have hint : ENNReal.ofReal (Real.pi * R ^ 2) *
      ((∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * φ s ^ q) *
        ∫⁻ η : ℝ, ψ η ^ q) ≤
      ENNReal.ofReal (Real.pi * R ^ 2 * (M ^ q * (H / 2) ^ ((5 : ℝ) / 4)) *
        (K' * c ^ ((N : ℝ) * q + 1))) := by
    have e : ENNReal.ofReal (Real.pi * R ^ 2 * (M ^ q * (H / 2) ^ ((5 : ℝ) / 4)) *
        (K' * c ^ ((N : ℝ) * q + 1))) = ENNReal.ofReal (Real.pi * R ^ 2) *
        (ENNReal.ofReal (M ^ q * (H / 2) ^ ((5 : ℝ) / 4)) *
          ENNReal.ofReal (K' * c ^ ((N : ℝ) * q + 1))) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_assoc]
    rw [e]
    gcongr
  have hbound : ENNReal.ofReal (Real.pi * R ^ 2 * (M ^ q * (H / 2) ^ ((5 : ℝ) / 4)) *
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
    have h1 : (H / 2) ^ ((5 : ℝ) / 4) ≤ (1 + H) ^ q := by
      calc (H / 2) ^ ((5 : ℝ) / 4) ≤ (1 + H) ^ ((5 : ℝ) / 4) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ ≤ (1 + H) ^ q :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hq]; norm_num)
    have h2 : c ^ ((N : ℝ) * q + 1) ≤ c ^ ((N : ℝ) * q + q) :=
      Real.rpow_le_rpow_of_exponent_le hc (by rw [hq]; linarith)
    have hMq : 0 ≤ M ^ q := by positivity
    calc Real.pi * R ^ 2 * (M ^ q * (H / 2) ^ ((5 : ℝ) / 4)) * (K' * c ^ ((N : ℝ) * q + 1))
        = Real.pi * K' * M ^ q * R ^ 2 * ((H / 2) ^ ((5 : ℝ) / 4) * c ^ ((N : ℝ) * q + 1)) := by
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

/-- Pointwise ring envelope bound on `dy j (p.eFun α)` off the axis. -/
theorem inlet_dy_ptw
    (Sig : ℝ) (lam : ℂ) (q : Planar.Profile) (hSig : 0 < Sig)
    (hq : Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (B κ : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < B ∧ 0 < κ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ (α : Fin 2 → ℝ) (j : Fin 3) (τ : ℝ) (y : Space), y ∉ axis →
          ‖dy j (p.eFun α) (τ, y)‖ ≤
            ringEnv1 p.H (B * (1 + p.H) * (p.ν ^ k)⁻¹ * ‖α‖) κ p.c 1
              (age p.R y) (trans p.R y) := by
  obtain ⟨CJ, κ, kJ, νJ, hCJ, hκ, hνJ, hνJ1, HJ⟩ :=
    inletJetDecay Sig lam q hSig hq dm dp hdm
  obtain ⟨νV, hνV, HV⟩ :=
    inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  obtain ⟨KL, hKL, HL⟩ := jetLe
  refine ⟨8 * KL * CJ, κ, kJ, min νJ νV, by positivity, hκ, lt_min hνJ hνV,
    (min_le_left _ _).trans hνJ1, ?_⟩
  intro p d hreg hν hS hm α j τ y hy
  have h0 : p.ν ≤ νJ := hν.trans (min_le_left _ _)
  have h1 : p.ν ≤ νV := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := h0.trans hνJ1
  have hνpos : 0 < p.ν := p.ν_pos
  have hHpos : 0 < p.H := p.H_pos
  have HJ' := HJ p d ⟨hreg, h0, hS, hm⟩
  have HV' := HV p d hreg h1 hS hm
  set e : ℝ × (ℝ × ℝ) → Merid := α 0 • p.inletProfile 0 + α 1 • p.inletProfile 1 with he
  have hcd0 : ContDiff ℝ ∞ (p.inletProfile 0) := (HV' 0).1
  have hcd1 : ContDiff ℝ ∞ (p.inletProfile 1) := (HV' 1).1
  have hecd : ContDiff ℝ ∞ e := (hcd0.const_smul (α 0)).add (hcd1.const_smul (α 1))
  have hvan : ∀ m : ℝ × (ℝ × ℝ), p.H / 2 < m.1 → e m = 0 := by
    intro m hm'
    have hz0 := (HV' 0).2 m hm'
    have hz1 := (HV' 1).2 m hm'
    simp [he, hz0, hz1]
  have heFun : p.eFun α = fun q : ℝ × Space => realC (Nv p.R e q.1 q.2) := by
    funext q
    simp only [Params.eFun, Params.inlet, Fin.sum_univ_two, he, Nv_add, Nv_smul]
  have hΦ : ContDiff ℝ ∞ (p.eFun α) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν1 hm l).const_smul _
  have hM : 0 ≤ 8 * KL * CJ * (1 + p.H) * (p.ν ^ kJ)⁻¹ * ‖α‖ := by positivity
  by_cases hle : age p.R y ≤ p.H / 2
  · have hRne : p.R ≠ 0 := p.R_pos.ne'
    have hs0 : 0 < age p.R y := Axi.age_pos hRne hy
    rw [ringEnv1_of_mem hs0 hle]
    have hd : Differentiable ℝ (p.eFun α) := hΦ.differentiable (by simp)
    have hEfun_sl : (fun z : Space => p.eFun α (τ, z)) =
        fun z : Space => realCL (Nv p.R e τ z) := by
      funext z
      rw [heFun]
      rfl
    have hsl_Nv : DifferentiableAt ℝ (Nv p.R e τ) y :=
      (nvFderivBound p.R τ e y p.R_pos hy ((hecd.differentiable (by simp)) _)).1
    have hL : ‖dy j (p.eFun α) (τ, y)‖ ≤ ‖fderiv ℝ (Nv p.R e τ) y‖ := by
      have hdy_sl : dy j (p.eFun α) (τ, y) =
          fderiv ℝ (fun z : Space => p.eFun α (τ, z)) y (UnforcedLeray.coordinateVector j) :=
        (UnforcedLeray.Short.PartIIIb.Concrete.slice_fderiv hd τ y
          (UnforcedLeray.coordinateVector j)).symm
      have hf_clm : fderiv ℝ (fun z : Space => realCL (Nv p.R e τ z)) y =
          realCL.comp (fderiv ℝ (Nv p.R e τ) y) :=
        (realCL.hasFDerivAt.comp y hsl_Nv.hasFDerivAt).fderiv
      rw [hdy_sl, hEfun_sl, hf_clm, ContinuousLinearMap.comp_apply, realCL_apply, norm_realC]
      calc ‖fderiv ℝ (Nv p.R e τ) y (UnforcedLeray.coordinateVector j)‖
          ≤ ‖fderiv ℝ (Nv p.R e τ) y‖ * ‖(UnforcedLeray.coordinateVector j : Space)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (Nv p.R e τ) y‖ := by rw [norm_cv, mul_one]
    have hεpos : 0 ≤ p.R⁻¹ := inv_nonneg.2 p.R_pos.le
    have hε1 : p.R⁻¹ ≤ 1 := by
      have hRe : p.R⁻¹ = p.ε := by simp [Params.R]
      rw [hRe, hreg.eps_eq, Real.exp_le_one_iff]
      have := hreg.dm_le
      have := hreg.dm_pos
      have : 0 ≤ d / p.ν := div_nonneg (by linarith) hνpos.le
      rw [neg_div]
      linarith
    have hgrad := (nvFderivBound p.R τ e y p.R_pos hy ((hecd.differentiable (by simp)) _)).2
    set x := chart p.R τ y with hxdef
    have hx1 : x.1 = age p.R y := rfl
    have hx2 : x.2.2 = trans p.R y := rfl
    have hsx0 : 0 < x.1 := by rw [hx1]; exact hs0
    set E := Real.exp (-(κ * |x.2.2| / p.c)) with hEd
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    set J := CJ * (p.ν ^ kJ)⁻¹ * E with hJ
    have hJ0 : 0 ≤ J := by positivity
    have ha0 : ‖α 0‖ ≤ ‖α‖ := norm_le_pi_norm α 0
    have ha1 : ‖α 1‖ ≤ ‖α‖ := norm_le_pi_norm α 1
    have hjet : ∀ l ≤ 2, ‖iteratedFDeriv ℝ l e x‖ ≤ 2 * ‖α‖ * J := by
      intro l hl
      have hc0 : ContDiffAt ℝ l (α 0 • p.inletProfile 0) x :=
        ((hcd0.const_smul (α 0)).of_le (by exact_mod_cast le_top)).contDiffAt
      have hc1 : ContDiffAt ℝ l (α 1 • p.inletProfile 1) x :=
        ((hcd1.const_smul (α 1)).of_le (by exact_mod_cast le_top)).contDiffAt
      have hc0' : ContDiffAt ℝ l (p.inletProfile 0) x :=
        (hcd0.of_le (by exact_mod_cast le_top)).contDiffAt
      have hc1' : ContDiffAt ℝ l (p.inletProfile 1) x :=
        (hcd1.of_le (by exact_mod_cast le_top)).contDiffAt
      rw [he, iteratedFDeriv_add_apply hc0 hc1, iteratedFDeriv_const_smul_apply hc0',
        iteratedFDeriv_const_smul_apply hc1']
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul]
      have b0 := (HJ' 0).2 l hl x
      have b1 := (HJ' 1).2 l hl x
      rw [← hEd, ← hJ] at b0 b1
      have hn0 : 0 ≤ ‖iteratedFDeriv ℝ l (p.inletProfile 0) x‖ := norm_nonneg _
      have hn1 : 0 ≤ ‖iteratedFDeriv ℝ l (p.inletProfile 1) x‖ := norm_nonneg _
      calc ‖α 0‖ * ‖iteratedFDeriv ℝ l (p.inletProfile 0) x‖ +
            ‖α 1‖ * ‖iteratedFDeriv ℝ l (p.inletProfile 1) x‖
          ≤ ‖α‖ * J + ‖α‖ * J :=
            add_le_add (mul_le_mul ha0 b0 hn0 (norm_nonneg _))
              (mul_le_mul ha1 b1 hn1 (norm_nonneg _))
        _ = 2 * ‖α‖ * J := by ring
    have hsum : ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l e x‖ ≤ 4 * ‖α‖ * J := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have := hjet 0 (by norm_num)
      have := hjet 1 (by norm_num)
      linarith
    have hjl := HL e hecd x
    have hgq := gradProfileQuantity_le hεpos hε1 e x hsx0.le
    have hlin : 1 + |x.1| + |x.2.2| ≤ (1 + p.H) * (1 + |x.2.2|) := by
      rw [abs_of_pos hsx0]
      have : x.1 ≤ p.H / 2 := by rw [hx1]; exact hle
      have : 0 ≤ |x.2.2| := abs_nonneg _
      nlinarith
    have hcj : chartJet e x ≤
        KL * ((1 + p.H) * (1 + |x.2.2|)) * (4 * ‖α‖ * J) := by
      have : 0 ≤ ‖Axi.dS e x‖ := norm_nonneg _
      calc chartJet e x
          ≤ KL * (1 + |x.1| + |x.2.2|) *
              ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l e x‖ := by linarith
        _ ≤ KL * ((1 + p.H) * (1 + |x.2.2|)) * (4 * ‖α‖ * J) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlin hKL.le) hsum
              (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
    have hfd : ‖fderiv ℝ (Nv p.R e τ) y‖ ≤
        2 * x.1 * (KL * ((1 + p.H) * (1 + |x.2.2|)) * (4 * ‖α‖ * J)) :=
      hgrad.trans (hgq.trans (mul_le_mul_of_nonneg_left hcj (by linarith)))
    refine hL.trans (hfd.trans ?_)
    rw [hJ, hEd, hx1, hx2, pow_one]
    exact le_of_eq (by ring)
  · set T := (p.H / 2 + age p.R y) / 2 with hTdef
    have hHT : p.H / 2 < T := by rw [hTdef]; linarith [not_le.1 hle]
    have hTa : T < age p.R y := by rw [hTdef]; linarith [not_le.1 hle]
    have hvanT : ∀ m : ℝ × (ℝ × ℝ), T ≤ m.1 → e m = 0 :=
      fun m hm' => hvan m (hHT.trans_le hm')
    have hev : ∀ᶠ q in 𝓝 (τ, y), p.eFun α q = 0 := by
      have h1 := nv_eventually_zero p.R_pos hvanT (Or.inr hTa)
      have h2 := (continuous_snd.tendsto (τ, y)).eventually h1
      filter_upwards [h2] with q hq
      rw [heFun]
      simp [hq q.1, realC]
    rw [dy_eq_zero hev j, norm_zero]
    exact ringEnv1_nonneg hM _ _

/-- Cancellation of the ring volume factor `p.R ^ (8 / 11)` against `p.coord z = p.ε ^ (8 / 11) • A`. -/
theorem R_rpow_mul_norm_coord_le (p : Params) (z : p.Z) :
    p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖ ≤ ‖z‖ := by
  have hε0 : 0 < p.ε := p.ε_pos
  have hR0 : 0 < p.R := p.R_pos
  have hpi : ‖p.coord z‖ ≤ ‖(WithLp.toLp 2 (p.coord z) : E2)‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    exact PiLp.norm_apply_le (WithLp.toLp 2 (p.coord z)) i
  have hsmul : (WithLp.toLp 2 (p.coord z) : E2) =
      p.ε ^ (8 / 11 : ℝ) • cA p.period (z : Amb p.period) := by
    ext i
    simp [Params.coord]
  have hnorm : ‖(WithLp.toLp 2 (p.coord z) : E2)‖ =
      p.ε ^ (8 / 11 : ℝ) * ‖cA p.period (z : Amb p.period)‖ := by
    rw [hsmul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hε0.le _)]
  have hRε : p.R ^ (8 / 11 : ℝ) * p.ε ^ (8 / 11 : ℝ) = 1 := by
    rw [← Real.mul_rpow hR0.le hε0.le]
    have : p.R * p.ε = 1 := by
      simp [Params.R, inv_mul_cancel₀ hε0.ne']
    rw [this, Real.one_rpow]
  have hcA : ‖cA p.period (z : Amb p.period)‖ ≤ ‖z‖ := by
    have heq := norm_eq_normX_add (P := p.period) (ν := p.ν) z
    have hX0 : 0 ≤ B0412.normX (⟨cw p.period z, cw_mem_X z⟩ : X p.period p.ν q0E) := by
      rw [B0412.normX_eq_graphNormD]
      exact S1Sub.s1_graphNormD_nonneg _
    linarith
  calc p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖
      ≤ p.R ^ (8 / 11 : ℝ) * (p.ε ^ (8 / 11 : ℝ) * ‖cA p.period (z : Amb p.period)‖) := by
        gcongr
        exact hpi.trans_eq hnorm
    _ = (p.R ^ (8 / 11 : ℝ) * p.ε ^ (8 / 11 : ℝ)) * ‖cA p.period (z : Amb p.period)‖ := by ring
    _ = ‖cA p.period (z : Amb p.period)‖ := by rw [hRε, one_mul]
    _ ≤ ‖z‖ := hcA

/-- Bounding `phaseLpNorm P bgp W` from a phase-uniform slice bound on `eLpNorm (W (τ, ·)) (11 / 4) volume`. -/
theorem phaseLpNorm_bgp_le_of_slice {P B : ℝ} (hP : 0 < P) (hB : 0 ≤ B)
    {W : ℝ × Space → CVec3}
    (hslice : ∀ τ : ℝ, eLpNorm (fun y => W (τ, y)) (11 / 4) volume ≤ ENNReal.ofReal B) :
    phaseLpNorm P bgp W ≤ ENNReal.ofReal B := by
  set q : ℝ := 11 / 4 with hq
  have hq0 : 0 < q := by rw [hq]; norm_num
  have hbgp_eq : bgp = q := by unfold bgp; rw [hq]
  unfold phaseLpNorm
  rw [hbgp_eq]
  have hsl_int : ∀ τ : ℝ, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ q ≤ ENNReal.ofReal B ^ q := by
    intro τ
    have hτ := hslice τ
    rw [eleven_fourths, ← hq,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le] at hτ
    have hr := ENNReal.rpow_le_rpow hτ hq0.le
    rwa [one_div, ENNReal.rpow_inv_rpow hq0.ne'] at hr
  have hint_le : ∫⁻ τ in Ioc 0 P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ q ≤
      ENNReal.ofReal B ^ q * ENNReal.ofReal P := by
    calc ∫⁻ τ in Ioc 0 P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ q
        ≤ ∫⁻ _ in Ioc 0 P, ENNReal.ofReal B ^ q := setLIntegral_mono measurable_const
            (fun τ _ => hsl_int τ)
      _ = ENNReal.ofReal B ^ q * volume (Ioc 0 P) := setLIntegral_const _ _
      _ = ENNReal.ofReal B ^ q * ENNReal.ofReal P := by rw [Real.volume_Ioc, sub_zero]
  have hPne0 : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP).ne'
  have hPnetop : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmul : ENNReal.ofReal P⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ q ≤
      ENNReal.ofReal B ^ q := by
    rw [ENNReal.ofReal_inv_of_pos hP]
    calc (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ q
        ≤ (ENNReal.ofReal P)⁻¹ * (ENNReal.ofReal B ^ q * ENNReal.ofReal P) := by gcongr
      _ = ENNReal.ofReal B ^ q * ((ENNReal.ofReal P)⁻¹ * ENNReal.ofReal P) := by ring
      _ = ENNReal.ofReal B ^ q := by
          rw [ENNReal.inv_mul_cancel hPne0 hPnetop, mul_one]
  calc (ENNReal.ofReal P⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ q) ^ (1 / q)
      ≤ (ENNReal.ofReal B ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow hmul (by positivity)
    _ = ENNReal.ofReal B := by rw [one_div, ENNReal.rpow_rpow_inv hq0.ne']

/-- Global `Y_{q₀}` bound on `dy j (p.eFun (p.coord z))`:
`phaseLpNorm p.period bgp (dy j (p.eFun (p.coord z))) ≤ ENNReal.ofReal (C_de * (p.ν ^ k_de)⁻¹ * ‖z‖)`. -/
theorem inlet_dy_phaseLpNorm_le
    (Sig : ℝ) (lam : ℂ) (q : Planar.Profile) (hSig : 0 < Sig)
    (hq : Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C_de : ℝ) (k_de : ℕ) (ν_de : ℝ), 0 < C_de ∧ 0 < ν_de ∧ ν_de ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_de → p.ageCut = Sig → p.mode = q →
        ∀ (z : p.Z) (j : Fin 3),
          phaseLpNorm p.period bgp (dy j (p.eFun (p.coord z))) ≤
            ENNReal.ofReal (C_de * (p.ν ^ k_de)⁻¹ * ‖z‖) := by
  obtain ⟨B, κ, k, ν₀, hB, hκ, hν₀, hν₀1, HP⟩ := inlet_dy_ptw Sig lam q hSig hq dm dp hdm
  obtain ⟨K, hK, HK⟩ := eLpNorm_le_of_ringEnv1 1 hκ
  have hSig0 : 0 < 1 + Sig := by linarith
  refine ⟨K * B * (1 + Sig) ^ 2, k + 6, ν₀, by positivity, hν₀, hν₀1, ?_⟩
  intro p d hreg hν hS hm z j
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans hν₀1
  set u : ℝ := p.ν⁻¹ with hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact (one_le_inv₀ hνpos).2 hν1
  have hpow : ∀ m : ℕ, (p.ν ^ m)⁻¹ = u ^ m := fun m => by rw [hu, inv_pow]
  have hc : p.c = u ^ 2 := by rw [hreg.c_eq, hpow]
  have hc1 : 1 ≤ p.c := by
    rw [hc]
    exact one_le_pow₀ hu1
  have hHpos : 0 < p.H := p.H_pos
  have hH : 1 + p.H ≤ (1 + Sig) * u := by
    have e : p.H = Sig * u := by
      rw [Params.H, hS, hu, div_eq_mul_inv]
    rw [e]
    nlinarith
  have hRpos : 0 < p.R := p.R_pos
  refine phaseLpNorm_bgp_le_of_slice p.period_pos (by positivity) fun τ => ?_
  have hM : 0 ≤ B * (1 + p.H) * (p.ν ^ k)⁻¹ * ‖p.coord z‖ := by positivity
  refine (HK p.R p.c p.H _ (fun y => dy j (p.eFun (p.coord z)) (τ, y)) hRpos hc1 hHpos hM
    (HP p d hreg hν hS hm (p.coord z) j τ)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hRz : p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖ ≤ ‖z‖ := R_rpow_mul_norm_coord_le p z
  have hH0 : 0 ≤ 1 + p.H := by linarith
  rw [hpow, hpow, hc]
  calc K * (B * (1 + p.H) * u ^ k * ‖p.coord z‖) * (1 + p.H) * (u ^ 2) ^ (1 + 1) *
        p.R ^ (8 / 11 : ℝ)
      = K * B * (1 + p.H) * (1 + p.H) * u ^ k * (u ^ 2) ^ 2 *
          (p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖) := by ring
    _ ≤ K * B * ((1 + Sig) * u) * ((1 + Sig) * u) * u ^ k * (u ^ 2) ^ 2 * ‖z‖ := by
        gcongr
    _ = K * B * (1 + Sig) ^ 2 * u ^ (k + 6) * ‖z‖ := by ring

end UnforcedLeray.Short.IIb
