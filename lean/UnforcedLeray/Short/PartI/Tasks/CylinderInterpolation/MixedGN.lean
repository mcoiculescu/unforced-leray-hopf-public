import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.EtaZero
import UnforcedLeray.Lib.Cylinder.IBP
import UnforcedLeray.Lib.SobolevC.GagliardoNirenberg
import UnforcedLeray.Units.B0151.Linf

/-!
# Part I, task `PartI:T07/3`: the mixed Gagliardo-Nirenberg step on the cylinder

Source of record: `the November 2 reference manuscript`, lines 355-357. Proves
`UnforcedLeray.Short.PartI.CylMixedGN` of `Sub/T07.lean` exactly as stated.

Route. With `a = ∂_v u`, `b = ∂_v a` and `p = r`, the product `H = u |a|^{p-2} a` is `C¹` and
periodic with `∂_v H = |a|^p + (p-1) u |a|^{p-2} b`. Its cell integral vanishes (periodic FTC in `q`,
`CylCellEtaZero` in `η`), so `∫|a|^p ≤ (p-1) ∫ |a|^{p-2} |u b|`. Hölder with exponents
`p/(p-2)`, `Q` (`Q⁻¹ = s⁻¹ + t⁻¹`), and the power identity `eLpNorm (|a|^{p-2}) = ‖a‖_p^{p-2}`
give `‖a‖_p^p ≤ (p-1) ‖a‖_p^{p-2} ‖u‖_s ‖b‖_t`; dividing by `‖a‖_p^{p-2}` closes the estimate.
The case `p = 2` uses exponent `1` in place of `p/(p-2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### Derivative words -/

theorem mixedGN_dw_two (v : Bool) (u : Cyl.Plane → ℝ) :
    B0151.derivWord [v, v] u = B0151.derivWord [v] (B0151.derivWord [v] u) := by
  cases v <;> rfl

/-! ### Calculus for the direction derivative -/

theorem mixedGN_contDiff_one_oddPow {q : ℝ} (hq : 0 ≤ q) :
    ContDiff ℝ 1 (Sob.GN.oddPow q) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (Sob.GN.hasDerivAt_oddPow hq t).differentiableAt, ?_⟩
  have hd : deriv (Sob.GN.oddPow q) = fun t => (q + 1) * |t| ^ q := by
    funext t
    exact (Sob.GN.hasDerivAt_oddPow hq t).deriv
  rw [hd]
  exact continuous_const.mul (continuous_abs.rpow_const fun _ => Or.inr hq)

theorem mixedGN_dir_mul (v : Bool) {f g : Cyl.Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : Cyl.Plane) :
    B0151.derivWord [v] (fun y => f y * g y) z =
      B0151.derivWord [v] f z * g z + f z * B0151.derivWord [v] g z := by
  cases v with
  | true =>
    exact ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).mul (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv
  | false =>
    exact ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).mul (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

theorem mixedGN_dir_oddPow (v : Bool) {q : ℝ} (hq : 0 ≤ q) {f : Cyl.Plane → ℝ}
    (hf : Differentiable ℝ f) (z : Cyl.Plane) :
    B0151.derivWord [v] (fun y => Sob.GN.oddPow q (f y)) z =
      (q + 1) * |f z| ^ q * B0151.derivWord [v] f z := by
  cases v with
  | true =>
    exact ((Sob.GN.hasDerivAt_oddPow hq (f z)).comp z.1
      (Cyl.hasDerivAt_sliceQ hf z.1 z.2)).deriv
  | false =>
    exact ((Sob.GN.hasDerivAt_oddPow hq (f z)).comp z.2
      (Cyl.hasDerivAt_sliceEta hf z.1 z.2)).deriv

theorem mixedGN_ibp (v : Bool) {c : ℝ} (hc : 0 < c) {H : Cyl.Plane → ℝ} (hH : ContDiff ℝ 1 H)
    (hper : Cyl.IsPeriodic c H) {x : ℝ≥0∞} (hx0 : 0 < x) (hxtop : x ≠ ⊤)
    (hHx : MemLp H x (Cyl.cellμ c)) (hint : Integrable (B0151.derivWord [v] H) (Cyl.cellμ c)) :
    ∫ z, B0151.derivWord [v] H z ∂(Cyl.cellμ c) = 0 := by
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  cases v with
  | true =>
    exact Cyl.integral_cell_deriv_q_of_periodic (F' := Cyl.partialQ H) hc hper
      (fun q η => Cyl.hasDerivAt_sliceQ hd q η) hint
  | false =>
    exact cylCellEtaZero_proof c hc H hH x hx0 hxtop hHx hint

theorem mixedGN_periodic_dw (v : Bool) {c : ℝ} {f : Cyl.Plane → ℝ} (hf : Cyl.IsPeriodic c f) :
    Cyl.IsPeriodic c (B0151.derivWord [v] f) := by
  have hq : B0151.IsPeriodicQ c f := fun q η => hf (q, η)
  have h := B0151.periodic_derivWord hq [v]
  exact fun z => h z.1 z.2

theorem mixedGN_norm_oddPow {q : ℝ} (hq : 0 ≤ q) (t : ℝ) :
    ‖Sob.GN.oddPow q t‖ = ‖t‖ ^ (q + 1) := by
  unfold Sob.GN.oddPow
  simp only [norm_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) q),
    Real.rpow_add' (abs_nonneg t) (by linarith : (0:ℝ) < q + 1).ne', Real.rpow_one]
  ring

theorem mixedGN_ofReal_div_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    ENNReal.ofReal (p / q) * ENNReal.ofReal q = ENNReal.ofReal p := by
  rw [← ENNReal.ofReal_mul (div_nonneg hp hq.le), div_mul_cancel₀ p hq.ne']

/-! ### The main estimate -/

theorem cylMixedGN_proof : UnforcedLeray.Short.PartI.CylMixedGN := by
  intro c hc u hu hper v r s t hrtop hr2 hrs hsum hus hA hB
  rw [mixedGN_dw_two] at hB ⊢
  obtain ⟨p, hp⟩ : ∃ p : ℝ, r.toReal = p := ⟨_, rfl⟩
  have hrp : r = ENNReal.ofReal p := by rw [← hp, ENNReal.ofReal_toReal hrtop]
  have hp2 : 2 ≤ p := by
    rw [← hp]
    have := ENNReal.toReal_mono hrtop hr2
    simpa using this
  rw [hp]
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ p - 2 := by linarith
  have hq1 : 0 < p - 1 := by linarith
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0] at hr2
    simp at hr2
  -- the derivative words, as opaque functions
  obtain ⟨a, ha⟩ : ∃ a : Cyl.Plane → ℝ, B0151.derivWord [v] u = a := ⟨_, rfl⟩
  rw [ha] at hA hB ⊢
  obtain ⟨b, hb⟩ : ∃ b : Cyl.Plane → ℝ, B0151.derivWord [v] a = b := ⟨_, rfl⟩
  rw [hb] at hB ⊢
  set μ := Cyl.cellμ c with hμ
  have hua : ContDiff ℝ ∞ a := by rw [← ha]; exact B0151.contDiff_derivWord hu [v]
  have hper_a : Cyl.IsPeriodic c a := by rw [← ha]; exact mixedGN_periodic_dw v hper
  have hub : ContDiff ℝ ∞ b := by rw [← hb]; exact B0151.contDiff_derivWord hua [v]
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by simp)
  have ha1 : ContDiff ℝ 1 a := hua.of_le (by simp)
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hda : Differentiable ℝ a := hua.differentiable (by simp)
  have hca : Continuous a := hua.continuous
  have hcb : Continuous b := hub.continuous
  have hcu : Continuous u := hu.continuous
  have hNlt : eLpNorm a r μ < ⊤ := hA.eLpNorm_lt_top
  have hA_int : Integrable (fun z => ‖a z‖ ^ p) μ := by
    have h := hA.integrable_norm_rpow hr0 hrtop
    rw [hp] at h
    exact h
  -- Hölder data for `u b`
  have hst : ENNReal.HolderTriple s t ((s⁻¹ + t⁻¹)⁻¹) := ENNReal.HolderTriple.of s t
  have hUB : MemLp (fun z => u z * b z) ((s⁻¹ + t⁻¹)⁻¹) μ := MemLp.mul' hB hus
  have hUB_le : eLpNorm (fun z => u z * b z) ((s⁻¹ + t⁻¹)⁻¹) μ ≤
      eLpNorm u s μ * eLpNorm b t μ := by
    have h := eLpNorm_smul_le_mul_eLpNorm (φ := u) (f := b) (p := s) (q := t)
      (r := (s⁻¹ + t⁻¹)⁻¹) hB.1 hus.1
    exact h
  have hφ_meas : AEStronglyMeasurable (fun z => ‖a z‖ ^ (p - 2)) μ :=
    ((hca.norm.rpow_const fun _ => Or.inr hq0)).aestronglyMeasurable
  -- the key bound `∫ |a|^{p-2} u b`
  have hFb : eLpNorm (fun z => ‖a z‖ ^ (p - 2) * (u z * b z)) 1 μ ≤
      eLpNorm a r μ ^ (p - 2) * (eLpNorm u s μ * eLpNorm b t μ) := by
    rcases eq_or_lt_of_le hp2 with h2 | h2
    · -- the case `p = 2`
      have hp2' : p - 2 = 0 := by linarith
      have hst1 : s⁻¹ + t⁻¹ = 1 := by
        rw [hsum, hrp, ← h2]
        rw [ENNReal.ofReal_ofNat]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      have hst1' : ENNReal.HolderTriple s t 1 := (ENNReal.holderTriple_iff _ _ _).2 (by rw [inv_one, hst1])
      have h1 := eLpNorm_smul_le_mul_eLpNorm (φ := u) (f := b) (p := s) (q := t) (r := 1)
        hB.1 hus.1
      simp only [hp2', Real.rpow_zero, ENNReal.rpow_zero, one_mul]
      exact h1
    · -- the case `p > 2`
      have hxq : (0:ℝ) < p - 2 := by linarith
      have hPr : ENNReal.ofReal (p / (p - 2)) * ENNReal.ofReal (p - 2) = r := by
        rw [hrp, mixedGN_ofReal_div_mul hp0.le hxq]
      have hφ_eq : eLpNorm (fun z => ‖a z‖ ^ (p - 2)) (ENNReal.ofReal (p / (p - 2))) μ =
          eLpNorm a r μ ^ (p - 2) := by
        rw [eLpNorm_norm_rpow a hxq, hPr]
      have hsum1 : (ENNReal.ofReal (p / (p - 2)))⁻¹ + (s⁻¹ + t⁻¹) = 1 := by
        have hxpos : (0:ℝ) < p / (p - 2) := div_pos hp0 hxq
        have e : (2:ℝ≥0∞) * ENNReal.ofReal p⁻¹ = ENNReal.ofReal (2 * p⁻¹) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        have e2 : (p - 2) / p + 2 * p⁻¹ = 1 := by
          have hpne : p ≠ 0 := hp0.ne'
          field_simp
          ring
        rw [hsum, hrp, ← ENNReal.ofReal_inv_of_pos hxpos, inv_div,
          ← ENNReal.ofReal_inv_of_pos hp0, e,
          ← ENNReal.ofReal_add (div_nonneg hq0 hp0.le)
            (mul_nonneg (by norm_num) (inv_nonneg.2 hp0.le)), e2, ENNReal.ofReal_one]
      have hPQ : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 2))) ((s⁻¹ + t⁻¹)⁻¹) 1 :=
        (ENNReal.holderTriple_iff _ _ _).2 (by rw [inv_inv, inv_one]; exact hsum1)
      have hφ_mem : MemLp (fun z => ‖a z‖ ^ (p - 2)) (ENNReal.ofReal (p / (p - 2))) μ :=
        ⟨hφ_meas, by rw [hφ_eq]; exact ENNReal.rpow_lt_top_of_nonneg hq0 hNlt.ne⟩
      have hHöl := eLpNorm_smul_le_mul_eLpNorm (φ := fun z => ‖a z‖ ^ (p - 2))
        (f := fun z => u z * b z) (p := ENNReal.ofReal (p / (p - 2)))
        (q := (s⁻¹ + t⁻¹)⁻¹) (r := 1) hUB.1 hφ_meas
      calc eLpNorm (fun z => ‖a z‖ ^ (p - 2) * (u z * b z)) 1 μ
          ≤ eLpNorm (fun z => ‖a z‖ ^ (p - 2)) (ENNReal.ofReal (p / (p - 2))) μ *
              eLpNorm (fun z => u z * b z) ((s⁻¹ + t⁻¹)⁻¹) μ := hHöl
        _ = eLpNorm a r μ ^ (p - 2) * eLpNorm (fun z => u z * b z) ((s⁻¹ + t⁻¹)⁻¹) μ := by
            rw [hφ_eq]
        _ ≤ eLpNorm a r μ ^ (p - 2) * (eLpNorm u s μ * eLpNorm b t μ) :=
            mul_le_mul_of_nonneg_left hUB_le zero_le
  have hFc : Continuous (fun z => ‖a z‖ ^ (p - 2) * (u z * b z)) :=
    (hca.norm.rpow_const fun _ => Or.inr hq0).mul (hcu.mul hcb)
  have hF1 : MemLp (fun z => ‖a z‖ ^ (p - 2) * (u z * b z)) 1 μ :=
    ⟨hFc.aestronglyMeasurable, lt_of_le_of_lt hFb (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hq0 hNlt.ne)
      (ENNReal.mul_lt_top hus.eLpNorm_lt_top hB.eLpNorm_lt_top))⟩
  have hF_int : Integrable (fun z => ‖a z‖ ^ (p - 2) * (u z * b z)) μ :=
    memLp_one_iff_integrable.1 hF1
  -- the integrand `H = u |a|^{p-2} a`
  have hG1 : ContDiff ℝ 1 (fun z => Sob.GN.oddPow (p - 2) (a z)) :=
    (mixedGN_contDiff_one_oddPow hq0).comp ha1
  have hH1 : ContDiff ℝ 1 (fun z => u z * Sob.GN.oddPow (p - 2) (a z)) := hu1.mul hG1
  have hGd : Differentiable ℝ (fun z => Sob.GN.oddPow (p - 2) (a z)) :=
    hG1.differentiable (by norm_num)
  have hHper : Cyl.IsPeriodic c (fun z => u z * Sob.GN.oddPow (p - 2) (a z)) := by
    exact fun z => by
      show u (z.1 + c, z.2) * Sob.GN.oddPow (p - 2) (a (z.1 + c, z.2)) =
        u z * Sob.GN.oddPow (p - 2) (a z)
      rw [hper z, hper_a z]
  have hDH : B0151.derivWord [v] (fun z => u z * Sob.GN.oddPow (p - 2) (a z)) =
      fun z => ‖a z‖ ^ p + (p - 1) * (‖a z‖ ^ (p - 2) * (u z * b z)) := by
    funext z
    have hm : a z * Sob.GN.oddPow (p - 2) (a z) = ‖a z‖ ^ p := by
      rw [Sob.GN.mul_oddPow (p - 2) (a z) hq0, Real.norm_eq_abs,
        show p - 2 + 2 = p by ring]
    rw [mixedGN_dir_mul v hdu hGd z, mixedGN_dir_oddPow v hq0 hda z, ha, hb, hm]
    simp only [Real.norm_eq_abs]
    ring
  have hint : Integrable (B0151.derivWord [v] (fun z => u z * Sob.GN.oddPow (p - 2) (a z))) μ := by
    rw [hDH]
    exact hA_int.add (hF_int.const_mul (p - 1))
  -- the exponent `x` with `x⁻¹ = s⁻¹ + P1⁻¹`, `P1 = p/(p-1)`
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℝ≥0∞, P1 = ENNReal.ofReal (p / (p - 1)) := ⟨_, rfl⟩
  have hPr1 : ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) = r := by
    rw [hrp, mixedGN_ofReal_div_mul hp0.le hq1]
  have hG_mem : MemLp (fun z => Sob.GN.oddPow (p - 2) (a z)) P1 μ := by
    have hg : MemLp (fun z => ‖a z‖ ^ (p - 1)) P1 μ := by
      refine ⟨(hca.norm.rpow_const fun _ => Or.inr hq1.le).aestronglyMeasurable, ?_⟩
      rw [eLpNorm_norm_rpow a hq1, hP1, hPr1]
      exact ENNReal.rpow_lt_top_of_nonneg hq1.le hNlt.ne
    refine MemLp.of_le hg hG1.continuous.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    show ‖Sob.GN.oddPow (p - 2) (a z)‖ ≤ ‖‖a z‖ ^ (p - 1)‖
    rw [mixedGN_norm_oddPow hq0, show p - 2 + 1 = p - 1 by ring,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hP1ne : P1 ≠ 0 := by
    rw [hP1]; exact (ENNReal.ofReal_pos.2 (div_pos hp0 hq1)).ne'
  have hP1top : P1 ≠ ⊤ := by rw [hP1]; exact ENNReal.ofReal_ne_top
  have hs0 : s ≠ 0 := (lt_of_lt_of_le (by norm_num) (hr2.trans hrs)).ne'
  have hsum_ne : s⁻¹ + P1⁻¹ ≠ 0 := by
    intro h0
    exact (ENNReal.inv_ne_zero.2 hP1top) (add_eq_zero.1 h0).2
  have hsum_ne_top : s⁻¹ + P1⁻¹ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 hs0, ENNReal.inv_ne_top.2 hP1ne⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ≥0∞, x = (s⁻¹ + P1⁻¹)⁻¹ := ⟨_, rfl⟩
  have hsP : ENNReal.HolderTriple s P1 x := by rw [hx]; exact ENNReal.HolderTriple.of s P1
  have hx0 : 0 < x := by rw [hx]; exact ENNReal.inv_pos.2 hsum_ne_top
  have hxtop : x ≠ ⊤ := by rw [hx]; exact ENNReal.inv_ne_top.2 hsum_ne
  have hHx : MemLp (fun z => u z * Sob.GN.oddPow (p - 2) (a z)) x μ := MemLp.mul' hG_mem hus
  -- integration by parts
  have hzero := mixedGN_ibp v hc hH1 hHper hx0 hxtop hHx hint
  simp only [hDH] at hzero
  rw [integral_add hA_int (hF_int.const_mul (p - 1)), integral_const_mul] at hzero
  have hI : ∫ z, ‖a z‖ ^ p ∂μ = -((p - 1) * ∫ z, ‖a z‖ ^ (p - 2) * (u z * b z) ∂μ) :=
    eq_neg_of_add_eq_zero_left hzero
  have h3 : |∫ z, ‖a z‖ ^ (p - 2) * (u z * b z) ∂μ| ≤
      ∫ z, ‖‖a z‖ ^ (p - 2) * (u z * b z)‖ ∂μ := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_integral_norm _
  have hreal : ∫ z, ‖a z‖ ^ p ∂μ ≤ (p - 1) * ∫ z, ‖‖a z‖ ^ (p - 2) * (u z * b z)‖ ∂μ := by
    rw [hI]
    have e1 := mul_le_mul_of_nonneg_left (neg_le_abs (∫ z, ‖a z‖ ^ (p - 2) * (u z * b z) ∂μ))
      hq1.le
    rw [mul_neg] at e1
    have e2 := mul_le_mul_of_nonneg_left h3 hq1.le
    exact e1.trans e2
  -- lintegral form
  have hX : ∫⁻ z, ‖a z‖ₑ ^ p ∂μ = ENNReal.ofReal (∫ z, ‖a z‖ ^ p ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hA_int
      (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg _) _)]
    refine lintegral_congr fun z => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  have hY : eLpNorm (fun z => ‖a z‖ ^ (p - 2) * (u z * b z)) 1 μ =
      ENNReal.ofReal (∫ z, ‖‖a z‖ ^ (p - 2) * (u z * b z)‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal hF_int.norm
      (Filter.Eventually.of_forall fun z => norm_nonneg _)]
    exact lintegral_congr fun z => (ofReal_norm _).symm
  have hmain : ∫⁻ z, ‖a z‖ₑ ^ p ∂μ ≤
      ENNReal.ofReal (p - 1) * eLpNorm (fun z => ‖a z‖ ^ (p - 2) * (u z * b z)) 1 μ := by
    rw [hX, hY, ← ENNReal.ofReal_mul hq1.le]
    exact ENNReal.ofReal_le_ofReal hreal
  have hNp : eLpNorm a r μ ^ p = ∫⁻ z, ‖a z‖ₑ ^ p ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop, hp, ← ENNReal.rpow_mul,
      one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hfinal : eLpNorm a r μ ^ p ≤
      ENNReal.ofReal (p - 1) * (eLpNorm a r μ ^ (p - 2) * (eLpNorm u s μ * eLpNorm b t μ)) :=
    (hNp.le.trans hmain).trans (mul_le_mul_of_nonneg_left hFb zero_le)
  by_cases hN0 : eLpNorm a r μ = 0
  · rw [hN0]
    simp
  · have hc0 : eLpNorm a r μ ^ (p - 2) ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hN0) hNlt.ne).ne'
    have hcT : eLpNorm a r μ ^ (p - 2) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg hq0 hNlt.ne).ne
    have hsplit : eLpNorm a r μ ^ p = eLpNorm a r μ ^ 2 * eLpNorm a r μ ^ (p - 2) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ hN0 hNlt.ne]
      congr 1
      push_cast
      ring
    rw [hsplit] at hfinal
    have key : eLpNorm a r μ ^ 2 * eLpNorm a r μ ^ (p - 2) ≤
        (ENNReal.ofReal (p - 1) * (eLpNorm u s μ * eLpNorm b t μ)) * eLpNorm a r μ ^ (p - 2) := by
      calc eLpNorm a r μ ^ 2 * eLpNorm a r μ ^ (p - 2)
          ≤ ENNReal.ofReal (p - 1) * (eLpNorm a r μ ^ (p - 2) * (eLpNorm u s μ * eLpNorm b t μ)) :=
            hfinal
        _ = (ENNReal.ofReal (p - 1) * (eLpNorm u s μ * eLpNorm b t μ)) *
              eLpNorm a r μ ^ (p - 2) := by ring
    exact (ENNReal.mul_le_mul_iff_left hc0 hcT).1 key

end UnforcedLeray.Short.PartI
