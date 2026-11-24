import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1
import UnforcedLeray.Lib.Gaussian.MovingCell

/-!
# Part III-a, task `PartIII-a:T21/c5/3/1/1`: `D^#` periodization identity and `O(|y|⁻²)` decay (`SeedLamPDSharpDecay`)

Source of record: `the November 2 reference manuscript` (SP), lines 2896-2912
(`eq:short-causal-damped-complement`, `eq:short-causal-ampl-moving`).

## Proved results in this file

1. **Periodization bridge and `physAdj` vs `Gaussian.heatDilation`
   (`perSum_eq_periodize`, `physAdj_eq_pow_three_smul_heatDilation`,
   `perSum_physAdj_eq_smul_periodize_heatDilation`)**:
   Connects `perSum` with `Gaussian.periodize` and expresses `physAdj b L` for `b > 0` as
   `(b ^ 3) • Gaussian.heatDilation b L`.
2. **Continuity and `O((1 + |z₁| + |z₂|)⁻²)` decay of `Gaussian.dualGen L`
   (`continuous_dualGen`, `norm_dualGen_le_inv_sq`)**:
   For any `C²` planar kernel `L : ℝ × ℝ → ℂ` with `O((1 + |z₁| + |z₂|)⁻²)` bounds on `L`,
   `(1 + ‖z‖) ‖fderiv ℝ L z‖`, and `‖iteratedFDeriv ℝ 2 L z‖`, shows that
   `Gaussian.dualGen L` (`D^# L = ΔL - ½ y·∇L + L`) is continuous and satisfies
   `‖Gaussian.dualGen L z‖ ≤ (7 / 2 * C) * ((1 + |z.1| + |z.2|)⁻¹) ^ 2`.
3. **Termwise `ladLapCx` and `ladDt` of `perSum c (physAdj (clockA ν s) L)` and moving pullback
   (`contDiff_perSum_physAdj`, `ladLapCx_perSum_physAdj`, `hasDerivAt_perSum_physAdj_clockA`,
   `ladDt_physFrameLam0_eq`, `movLam0DualHeat_eq_inv_clockTheta_mul_perSum_dualGen`)**:
   Uses `Gaussian.laplacian_periodize`, `Gaussian.laplacian_heatDilation`, and
   `Gaussian.hasDerivAt_periodize_heatDilation` to differentiate the `c = ν⁻²`-periodization
   termwise in space and time, proving both `C²` spatial regularity and time differentiability of
   `physFrameLam0 κ ν r j` and the exact moving identity
   `movLam0DualHeat κ ν r j y = (clockTheta ν r : ℂ)⁻¹ * perSum d(r) (Gaussian.dualGen (κ.lamP j)) y`.
4. **Conditional assembly (`seedLamPDSharpDecay_of`)**:
   Proves `SeedLamPDSharpDecay κ` from `SeedLamPJet2Decay κ` (`C²` regularity and weighted
   second-jet `O((1 + |z₁| + |z₂|)⁻²)` decay of the Part I seed dual kernels `κ.lamP j`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace ComplCouplingHeat

/-! ## 1. Periodization bridge and `physAdj` vs `Gaussian.heatDilation` -/

/-- `perSum d Ψ` coincides with `Gaussian.periodize d Ψ` via `n ↦ -n` on `ℤ`. -/
theorem perSum_eq_periodize (d : ℝ) (Ψ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    perSum d Ψ y = Gaussian.periodize d Ψ y := by
  unfold perSum Gaussian.periodize
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  congr 1
  ext <;> simp [sub_eq_add_neg]

theorem perSum_eq_periodize_fun (d : ℝ) (Ψ : ℝ × ℝ → ℂ) :
    perSum d Ψ = Gaussian.periodize d Ψ :=
  funext (perSum_eq_periodize d Ψ)

/-- For `b > 0`, `physAdj b f z = (b ^ 3) • Gaussian.heatDilation b f z`. -/
theorem physAdj_eq_pow_three_smul_heatDilation {b : ℝ} (hb : 0 < b) (f : ℝ × ℝ → ℂ) (z : ℝ × ℝ) :
    physAdj b f z = (b ^ 3) • Gaussian.heatDilation b f z := by
  unfold physAdj Gaussian.heatDilation
  rw [smul_smul, ← Complex.real_smul]
  have hb0 : b ≠ 0 := hb.ne'
  have hscalar : b ^ 3 * b⁻¹ ^ 2 = b := by field_simp
  rw [hscalar]
  congr 2
  ext <;> simp [div_eq_inv_mul]

/-- For `b > 0`, `perSum c (physAdj b f) x = (b ^ 3) • Gaussian.periodize c (Gaussian.heatDilation b f) x`. -/
theorem perSum_physAdj_eq_smul_periodize_heatDilation {b : ℝ} (hb : 0 < b) (c : ℝ)
    (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    perSum c (physAdj b f) x =
      (b ^ 3) • Gaussian.periodize c (Gaussian.heatDilation b f) x := by
  rw [perSum_eq_periodize]
  unfold Gaussian.periodize
  simp_rw [physAdj_eq_pow_three_smul_heatDilation hb f]
  rw [tsum_const_smul'']

/-- For `C²` complex-valued planar fields, `ladLapCx` agrees with `Cyl.laplacian`. -/
theorem ladLapCx_eq_cyl_laplacian {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (z : ℝ × ℝ) :
    ladLapCx f z = Cyl.laplacian f z := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hQ : pdCx 0 f = Cyl.partialQ f := by
    funext w
    rw [Cyl.partialQ_eq_fderiv hd]
    rfl
  have hE : pdCx 1 f = Cyl.partialEta f := by
    funext w
    rw [Cyl.partialEta_eq_fderiv hd]
    rfl
  have hdQ : Differentiable ℝ (Cyl.partialQ f) :=
    (Cyl.contDiff_partialQ (n := 1) hf).differentiable (by norm_num)
  have hdE : Differentiable ℝ (Cyl.partialEta f) :=
    (Cyl.contDiff_partialEta (n := 1) hf).differentiable (by norm_num)
  unfold ladLapCx Cyl.laplacian
  rw [hQ, hE, Cyl.partialQ_eq_fderiv hdQ, Cyl.partialEta_eq_fderiv hdE]
  rfl

/-- `Cyl.laplacian` commutes with real scalar multiplication. -/
theorem cyl_laplacian_const_smul {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (a : ℝ) (z : ℝ × ℝ) :
    Cyl.laplacian (fun x => a • f x) z = a • Cyl.laplacian f z := by
  have hsmul : ContDiff ℝ 2 (fun x => a • f x) := hf.const_smul a
  rw [Gaussian.laplacian_eq_iteratedFDeriv hsmul, Gaussian.laplacian_eq_iteratedFDeriv hf]
  have hiter : iteratedFDeriv ℝ 2 (fun x => a • f x) z = a • iteratedFDeriv ℝ 2 f z := by
    change iteratedFDeriv ℝ 2 (a • f) z = a • iteratedFDeriv ℝ 2 f z
    exact iteratedFDeriv_const_smul_apply (hf.contDiffAt)
  rw [hiter, smul_apply, smul_apply, smul_add]

/-! ## 2. Continuity and `O((1 + |z₁| + |z₂|)⁻²)` decay of `Gaussian.dualGen L` -/

/-- Continuity of `Gaussian.dualGen L` (`D^# L = ΔL - ½ y·∇L + L`) for `C²` `L`. -/
theorem continuous_dualGen {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) :
    Continuous (Gaussian.dualGen L) := by
  have hLap : Continuous (Cyl.laplacian L) := by
    have heq : Cyl.laplacian L = fun z =>
        iteratedFDeriv ℝ 2 L z ![((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] +
        iteratedFDeriv ℝ 2 L z ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] :=
      funext (Gaussian.laplacian_eq_iteratedFDeriv hL)
    rw [heq]
    have hD2 : Continuous (iteratedFDeriv ℝ 2 L) :=
      hL.continuous_iteratedFDeriv (by norm_num)
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℂ
        ![((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))]).continuous.comp hD2).add
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℂ
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]).continuous.comp hD2)
  have hDil : Continuous (fun z : ℝ × ℝ => fderiv ℝ L z z) :=
    (hL.continuous_fderiv (by norm_num)).clm_apply continuous_id
  unfold Gaussian.dualGen
  exact (hLap.sub (hDil.const_smul (1 / 2 : ℝ))).add hL.continuous

/-- Pointwise `O((1 + |z₁| + |z₂|)⁻²)` bound for `Gaussian.dualGen L`. -/
theorem norm_dualGen_le_inv_sq {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) {C : ℝ}
    (h0 : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (h1 : ∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (h2 : ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (z : ℝ × ℝ) :
    ‖Gaussian.dualGen L z‖ ≤ (7 / 2 * C) * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by
  have hLap : ‖Cyl.laplacian L z‖ ≤ 2 * C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by
    calc ‖Cyl.laplacian L z‖ ≤ 2 * ‖iteratedFDeriv ℝ 2 L z‖ := Gaussian.norm_laplacian_le hL z
      _ ≤ 2 * (C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) := by linarith [h2 z]
      _ = 2 * C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by ring
  have hDil : ‖fderiv ℝ L z z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by
    refine ((fderiv ℝ L z).le_opNorm z).trans ?_
    refine le_trans ?_ (h1 z)
    have := norm_nonneg (fderiv ℝ L z)
    have := norm_nonneg z
    nlinarith
  have hDil' : ‖(1 / 2 : ℝ) • fderiv ℝ L z z‖ ≤ (1 / 2) * C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  unfold Gaussian.dualGen
  calc ‖Cyl.laplacian L z - (1 / 2 : ℝ) • fderiv ℝ L z z + L z‖
      ≤ ‖Cyl.laplacian L z - (1 / 2 : ℝ) • fderiv ℝ L z z‖ + ‖L z‖ := norm_add_le _ _
    _ ≤ ‖Cyl.laplacian L z‖ + ‖(1 / 2 : ℝ) • fderiv ℝ L z z‖ + ‖L z‖ := by
        linarith [norm_sub_le (Cyl.laplacian L z) ((1 / 2 : ℝ) • fderiv ℝ L z z)]
    _ ≤ (7 / 2 * C) * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by linarith [h0 z]

/-! ## 3. Termwise differentiation of `perSum c (physAdj (clockA ν s) L)` and moving identity -/

/-- From `O((1 + |z₁| + |z₂|)⁻²)` bounds on `L`, `(1 + ‖z‖) ‖fderiv ℝ L z‖`, and
`‖iteratedFDeriv ℝ 2 L z‖`, obtain the `O((1 + |z₁|)⁻²)` translate bounds required by
`UnforcedLeray.Gaussian`. -/
theorem translate_jet2_bounds {L : ℝ × ℝ → ℂ} {C : ℝ}
    (h0 : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (h1 : ∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (h2 : ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) :
    (∀ z : ℝ × ℝ, ‖L z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
    (∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
    (∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 L z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) := by
  have haux : ∀ {f : ℝ × ℝ → ℝ} (hf : ∀ z : ℝ × ℝ, f z ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
      (z : ℝ × ℝ), f z ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro f hf z
    refine (hf z).trans ?_
    rw [Lam0B.rpow_neg_two_eq _ (by positivity)]
    have h1' : (1 + |z.1| + |z.2|)⁻¹ ≤ (1 + |z.1|)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith [abs_nonneg z.2])
    have h2' : ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ ((1 + |z.1|)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1' 2
    calc C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ |C| * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + |z.1|)⁻¹) ^ 2 := mul_le_mul_of_nonneg_left h2' (abs_nonneg C)
  exact ⟨haux h0, haux h1, haux h2⟩

/-- `perSum c (physAdj a L)` is `C²` on `ℝ × ℝ` when `L` is `C²` with `O((1 + |z₁|)⁻²)` second jet. -/
theorem contDiff_perSum_physAdj {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) {C c a : ℝ}
    (hc : c ≠ 0) (ha : 0 < a)
    (h0 : ∀ z, ‖L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) :
    ContDiff ℝ 2 (perSum c (physAdj a L)) := by
  have heq : perSum c (physAdj a L) =
      fun x => (a ^ 3) • Gaussian.periodize c (Gaussian.heatDilation a L) x :=
    funext (perSum_physAdj_eq_smul_periodize_heatDilation ha c L)
  rw [heq]
  have hD : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∃ C' : ℝ, ∀ z,
      ‖iteratedFDeriv ℝ k (Gaussian.heatDilation a L) z‖ ≤ C' * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro k hk
    obtain ⟨C₀, hC₀⟩ := Gaussian.iteratedFDeriv_bounds_of h0 h1 h2 k hk
    exact ⟨_, Gaussian.norm_iteratedFDeriv_heatDilation_le (by norm_num) ha k hC₀⟩
  have hPer : ContDiff ℝ 2 (Gaussian.periodize c (Gaussian.heatDilation a L)) :=
    Gaussian.contDiff_periodize (s := 2) (by norm_num) hc
      (Gaussian.contDiff_heatDilation hL a) hD
  exact hPer.const_smul (a ^ 3)

/-- Spatial Laplacian of `perSum c (physAdj a L)`:
`ladLapCx (perSum c (physAdj a L)) x = (a ^ 2) • Gaussian.periodize c (Gaussian.heatDilation a (Cyl.laplacian L)) x`. -/
theorem ladLapCx_perSum_physAdj {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) {C c a : ℝ}
    (hc : c ≠ 0) (ha : 0 < a)
    (h0 : ∀ z, ‖L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (x : ℝ × ℝ) :
    ladLapCx (perSum c (physAdj a L)) x =
      (a ^ 2) • Gaussian.periodize c (Gaussian.heatDilation a (Cyl.laplacian L)) x := by
  have hCD : ContDiff ℝ 2 (perSum c (physAdj a L)) :=
    contDiff_perSum_physAdj hL hc ha h0 h1 h2
  rw [ladLapCx_eq_cyl_laplacian hCD x]
  have heq : perSum c (physAdj a L) =
      fun z => (a ^ 3) • Gaussian.periodize c (Gaussian.heatDilation a L) z :=
    funext (perSum_physAdj_eq_smul_periodize_heatDilation ha c L)
  have hD : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∃ C' : ℝ, ∀ z,
      ‖iteratedFDeriv ℝ k (Gaussian.heatDilation a L) z‖ ≤ C' * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro k hk
    obtain ⟨C₀, hC₀⟩ := Gaussian.iteratedFDeriv_bounds_of h0 h1 h2 k hk
    exact ⟨_, Gaussian.norm_iteratedFDeriv_heatDilation_le (by norm_num) ha k hC₀⟩
  have hPer : ContDiff ℝ 2 (Gaussian.periodize c (Gaussian.heatDilation a L)) :=
    Gaussian.contDiff_periodize (s := 2) (by norm_num) hc
      (Gaussian.contDiff_heatDilation hL a) hD
  rw [heq, cyl_laplacian_const_smul hPer (a ^ 3) x,
    Gaussian.laplacian_periodize (Gaussian.contDiff_heatDilation hL a) (s := 2) (by norm_num) hc hD x]
  have hterm : Gaussian.periodize c (Cyl.laplacian (Gaussian.heatDilation a L)) x =
      a⁻¹ • Gaussian.periodize c (Gaussian.heatDilation a (Cyl.laplacian L)) x := by
    unfold Gaussian.periodize
    rw [← tsum_const_smul'']
    congr 1
    funext n
    exact Gaussian.laplacian_heatDilation hL ha _
  rw [hterm, smul_smul]
  have ha0 : a ≠ 0 := ha.ne'
  congr 1
  field_simp

/-- Time derivative of `b ↦ perSum c (physAdj b L) x` at `b = a > 0`. -/
theorem hasDerivAt_perSum_physAdj_param {L : ℝ × ℝ → ℂ} (hL : Differentiable ℝ L) {C c a : ℝ}
    (hc : c ≠ 0) (ha : 0 < a)
    (h0 : ∀ z, ‖L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (x : ℝ × ℝ) :
    HasDerivAt (fun b => perSum c (physAdj b L) x)
      ((3 * a ^ 2) • Gaussian.periodize c (Gaussian.heatDilation a L) x -
        (a ^ 2) • Gaussian.periodize c (Gaussian.heatDilation a (Gaussian.dilationDrift L)) x) a := by
  have hpow : HasDerivAt (fun b : ℝ => b ^ 3) (3 * a ^ 2) a := by
    simpa using hasDerivAt_pow 3 a
  have hper := Gaussian.hasDerivAt_periodize_heatDilation hL (s := 2) (by norm_num) hc ha h0 h1 x
  have hsmul := hpow.smul hper
  have hev : (fun b => (b ^ 3) • Gaussian.periodize c (Gaussian.heatDilation b L) x) =ᶠ[𝓝 a]
      (fun b => perSum c (physAdj b L) x) := by
    filter_upwards [lt_mem_nhds ha] with b hb
    exact (perSum_physAdj_eq_smul_periodize_heatDilation hb c L x).symm
  refine (hsmul.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [smul_smul]
  have ha0 : a ≠ 0 := ha.ne'
  have hsc : a ^ 3 * -a⁻¹ = -(a ^ 2) := by field_simp
  rw [hsc]
  module

/-- Time derivative of `s ↦ perSum c (physAdj (clockA ν s) L) x` at `s = r` (`0 ≤ r`). -/
theorem hasDerivAt_perSum_physAdj_clockA {L : ℝ × ℝ → ℂ} (hL : Differentiable ℝ L)
    {C c ν r : ℝ} (hc : c ≠ 0) (hν : 0 < ν) (hr : 0 ≤ r)
    (h0 : ∀ z, ‖L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (x : ℝ × ℝ) :
    HasDerivAt (fun s => perSum c (physAdj (clockA ν s) L) x)
      (ν • ((3 * (clockA ν r) ^ 2) •
          Gaussian.periodize c (Gaussian.heatDilation (clockA ν r) L) x -
        ((clockA ν r) ^ 2) •
          Gaussian.periodize c
            (Gaussian.heatDilation (clockA ν r) (Gaussian.dilationDrift L)) x)) r := by
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hclock : HasDerivAt (clockA ν) ν r := by
    unfold clockA
    simpa using ((hasDerivAt_id r).const_mul ν).const_add 1
  exact (hasDerivAt_perSum_physAdj_param hL hc ha h0 h1 x).scomp r hclock

/-- For `0 < ν` and `0 ≤ r`, `s ↦ physFrameLam0 κ ν s j x` has `HasDerivWithinAt` on `Ici r`
at `r` equal to the `clockA`-chain-rule derivative of `perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν s) (κ.lamP j)) x`. -/
theorem hasDerivWithinAt_physFrameLam0 (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (j : Fin 2) (hL : Differentiable ℝ (κ.lamP j))
    {C : ℝ}
    (h0 : ∀ z, ‖κ.lamP j z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (x : ℝ × ℝ) :
    HasDerivWithinAt (fun s => physFrameLam0 κ ν s j x)
      (ν • ((3 * (clockA ν r) ^ 2) •
          Gaussian.periodize (ν ^ (-2 : ℝ)) (Gaussian.heatDilation (clockA ν r) (κ.lamP j)) x -
        ((clockA ν r) ^ 2) •
          Gaussian.periodize (ν ^ (-2 : ℝ))
            (Gaussian.heatDilation (clockA ν r) (Gaussian.dilationDrift (κ.lamP j))) x))
      (Ici r) r := by
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν (-2)).ne'
  have hder := (hasDerivAt_perSum_physAdj_clockA hL hc hν hr h0 h1 x).hasDerivWithinAt (s := Ici r)
  refine hder.congr (fun s hs => ?_) (physFrameLam0_eq_perSum_physAdj κ hν hr j x)
  exact physFrameLam0_eq_perSum_physAdj κ hν (hr.trans hs) j x

/-- Explicit formula for `ladDt (fun s x' => physFrameLam0 κ ν s j x') r x`. -/
theorem ladDt_physFrameLam0_eq (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (j : Fin 2) (hL : Differentiable ℝ (κ.lamP j))
    {C : ℝ}
    (h0 : ∀ z, ‖κ.lamP j z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (x : ℝ × ℝ) :
    ladDt (fun s x' => physFrameLam0 κ ν s j x') r x =
      ν • ((3 * (clockA ν r) ^ 2) •
          Gaussian.periodize (ν ^ (-2 : ℝ)) (Gaussian.heatDilation (clockA ν r) (κ.lamP j)) x -
        ((clockA ν r) ^ 2) •
          Gaussian.periodize (ν ^ (-2 : ℝ))
            (Gaussian.heatDilation (clockA ν r) (Gaussian.dilationDrift (κ.lamP j))) x) :=
  (hasDerivWithinAt_physFrameLam0 κ hν hr j hL h0 h1 x).derivWithin (uniqueDiffWithinAt_Ici r)

/-- Pointwise identity combining `3 • L - dilationDrift L + laplacian L = dualGen L` under
`Gaussian.periodize c (Gaussian.heatDilation a ·)`. -/
theorem periodize_heatDilation_dualGen {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) {C c a : ℝ}
    (hc : c ≠ 0) (ha : 0 < a)
    (h0 : ∀ z, ‖L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (x : ℝ × ℝ) :
    (3 : ℝ) • Gaussian.periodize c (Gaussian.heatDilation a L) x -
      Gaussian.periodize c (Gaussian.heatDilation a (Gaussian.dilationDrift L)) x +
      Gaussian.periodize c (Gaussian.heatDilation a (Cyl.laplacian L)) x =
      Gaussian.periodize c (Gaussian.heatDilation a (Gaussian.dualGen L)) x := by
  have hs0 : (0 : ℝ) ≤ 2 := by norm_num
  have hs1 : (1 : ℝ) < 2 := by norm_num
  have hsumL : Summable fun n : ℤ => Gaussian.heatDilation a L (x.1 - n * c, x.2) :=
    Gaussian.summable_periodize hs1 hc (Gaussian.norm_heatDilation_le hs0 ha h0) x
  have hsumD : Summable fun n : ℤ =>
      Gaussian.heatDilation a (Gaussian.dilationDrift L) (x.1 - n * c, x.2) :=
    Gaussian.summable_periodize hs1 hc
      (Gaussian.norm_heatDilation_le hs0 ha (Gaussian.norm_dilationDrift_le h0 h1)) x
  have hsumLap : Summable fun n : ℤ =>
      Gaussian.heatDilation a (Cyl.laplacian L) (x.1 - n * c, x.2) :=
    Gaussian.summable_periodize hs1 hc
      (Gaussian.norm_heatDilation_le hs0 ha (Gaussian.norm_laplacian_le_translate hL h2)) x
  unfold Gaussian.periodize
  rw [← (((hsumL.hasSum.const_smul (3 : ℝ)).sub hsumD.hasSum).add hsumLap.hasSum).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Gaussian.heatDilation_apply, Gaussian.dilationDrift, Gaussian.dualGen]
  module

/-- Exact moving identity for `movLam0DualHeat`:
`movLam0DualHeat κ ν r j y = (clockTheta ν r : ℂ)⁻¹ * perSum (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Gaussian.dualGen (κ.lamP j)) y`. -/
theorem movLam0DualHeat_eq_inv_clockTheta_mul_perSum_dualGen (κ : PlanarFrameKernels)
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (j : Fin 2)
    (hL : ContDiff ℝ 2 (κ.lamP j)) {C : ℝ}
    (h0 : ∀ z, ‖κ.lamP j z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 (κ.lamP j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (y : ℝ × ℝ) :
    movLam0DualHeat κ ν r j y =
      (clockTheta ν r : ℂ)⁻¹ *
        perSum (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Gaussian.dualGen (κ.lamP j)) y := by
  set a : ℝ := clockA ν r
  set c : ℝ := ν ^ (-2 : ℝ)
  set x : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2)
  have ha1 : 1 ≤ a := one_le_clockA hν.le hr
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have ha_ne : a ≠ 0 := ha.ne'
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsa_ne : Real.sqrt a ≠ 0 := hsa.ne'
  have hc : c ≠ 0 := (Real.rpow_pos_of_pos hν (-2)).ne'
  have hLd : Differentiable ℝ (κ.lamP j) := hL.differentiable (by norm_num)
  have hDt := ladDt_physFrameLam0_eq κ hν hr j hLd h0 h1 x
  have hLap : ladLapCx (physFrameLam0 κ ν r j) x =
      (a ^ 2) • Gaussian.periodize c (Gaussian.heatDilation a (Cyl.laplacian (κ.lamP j))) x := by
    have hcongr : physFrameLam0 κ ν r j = perSum c (physAdj a (κ.lamP j)) :=
      funext (physFrameLam0_eq_perSum_physAdj κ hν hr j)
    rw [hcongr]
    exact ladLapCx_perSum_physAdj hL hc ha h0 h1 h2 x
  have hcomb : ladDt (fun s x'' => physFrameLam0 κ ν s j x'') r x +
      (ν : ℂ) * ladLapCx (physFrameLam0 κ ν r j) x =
      (ν * a⁻¹) • perSum c (physAdj a (Gaussian.dualGen (κ.lamP j))) x := by
    rw [hDt, hLap, ← Complex.real_smul]
    have hsum := periodize_heatDilation_dualGen hL hc ha h0 h1 h2 x
    have hper := perSum_physAdj_eq_smul_periodize_heatDilation ha c (Gaussian.dualGen (κ.lamP j)) x
    rw [hper, ← hsum]
    simp only [smul_add, smul_sub, smul_smul]
    have hsc1 : ν * (3 * a ^ 2) = ν * a⁻¹ * a ^ 3 * 3 := by field_simp
    have hsc2 : ν * a ^ 2 = ν * a⁻¹ * a ^ 3 := by field_simp
    rw [hsc1, hsc2]
    module
  have hpull : perSum c (physAdj a (Gaussian.dualGen (κ.lamP j))) x =
      ((a : ℝ) : ℂ) * perSum (cellLen c a) (Gaussian.dualGen (κ.lamP j)) y := by
    rw [← physAdj_perSum_eq_perSum_physAdj ha (Gaussian.dualGen (κ.lamP j)) x]
    unfold physAdj
    congr 2
    ext
    · exact mul_div_cancel_left₀ y.1 hsa_ne
    · exact mul_div_cancel_left₀ y.2 hsa_ne
  unfold movLam0DualHeat movingPhi
  dsimp only
  change (((a ^ (2 : ℝ) : ℝ) : ℂ) *
    (((a⁻¹ : ℝ) : ℂ) *
      (ladDt (fun s x'' => physFrameLam0 κ ν s j x'') r x +
        (ν : ℂ) * ladLapCx (physFrameLam0 κ ν r j) x))) = _
  rw [hcomb, hpull, Complex.real_smul, Real.rpow_two]
  unfold clockTheta
  change (((a ^ 2 : ℝ) : ℂ) *
    (((a⁻¹ : ℝ) : ℂ) *
      (((ν * a⁻¹ : ℝ) : ℂ) *
        (((a : ℝ) : ℂ) * perSum (cellLen c a) (Gaussian.dualGen (κ.lamP j)) y)))) =
    ((((ν * a)⁻¹ : ℝ) : ℂ)⁻¹ * perSum (cellLen c a) (Gaussian.dualGen (κ.lamP j)) y)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha_ne
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  push_cast
  field_simp [haC, hνC]

/-! ## 4. Conditional assembly of `SeedLamPDSharpDecay` -/

/-- **Upstream Part I regularity and weighted second-jet decay hypothesis for `κ.lamP`
(`SeedLamPJet2Decay`)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), the planar dual profiles `κ.lamP j` are `C²` on
`ℝ × ℝ` and satisfy weighted first- and second-derivative `O((1 + |z₁| + |z₂|)⁻²)` bounds matching
`κ.lamP_decay`. -/
def SeedLamPJet2Decay (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  (∀ j : Fin 2, ContDiff ℝ 2 (κ.lamP j)) ∧
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ (j : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP j) z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) ∧
    (∀ (j : Fin 2) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ 2 (κ.lamP j) z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)

/-- Combined `C²` regularity and `0, 1, 2`-jet `O((1 + |z₁| + |z₂|)⁻²)` bounds for `κ.lamP` from
`SeedLamPJet2Decay κ` and `κ.lamP_decay`. -/
theorem seedLamP_jet2_bounds_of (κ : PlanarFrameKernels) (hJet : SeedLamPJet2Decay κ)
    (hκ : IsSeedKernels κ) :
    (∀ j : Fin 2, ContDiff ℝ 2 (κ.lamP j)) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (j : Fin 2) (z : ℝ × ℝ), ‖κ.lamP j z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) ∧
      (∀ (j : Fin 2) (z : ℝ × ℝ),
        (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP j) z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) ∧
      (∀ (j : Fin 2) (z : ℝ × ℝ),
        ‖iteratedFDeriv ℝ 2 (κ.lamP j) z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) := by
  obtain ⟨hCD, C₁, _hC₁0, hD1, hD2⟩ := hJet hκ
  obtain ⟨C₀, hD0⟩ := κ.lamP_decay
  set C : ℝ := max |C₀| C₁
  have hC0 : 0 ≤ C := le_trans (abs_nonneg C₀) (le_max_left _ _)
  refine ⟨hCD, C, hC0, fun j z => ?_, fun j z => ?_, fun j z => ?_⟩
  · refine (hD0 j z).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_abs_self C₀).trans (le_max_left _ _)) (by positivity)
  · refine (hD1 j z).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · refine (hD2 j z).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Conditional proof of `SeedLamPDSharpDecay κ` (`PartIII-a:T21/c5/3/1/1`) from
`SeedLamPJet2Decay κ`. -/
theorem seedLamPDSharpDecay_of (κ : PlanarFrameKernels) (hJet : SeedLamPJet2Decay κ) :
    SeedLamPDSharpDecay κ := by
  intro hκ
  obtain ⟨hCD, C, hC0, h0, h1, h2⟩ := seedLamP_jet2_bounds_of κ hJet hκ
  refine ⟨fun j => Gaussian.dualGen (κ.lamP j), 7 / 2 * C, by positivity,
    fun j => continuous_dualGen (hCD j),
    fun j z => norm_dualGen_le_inv_sq (hCD j) (h0 j) (h1 j) (h2 j) z,
    fun {ν r} hν hr _hd j y => ?_⟩
  obtain ⟨ht0, ht1, ht2⟩ := translate_jet2_bounds (h0 j) (h1 j) (h2 j)
  exact movLam0DualHeat_eq_inv_clockTheta_mul_perSum_dualGen κ hν hr j (hCD j) ht0 ht1 ht2 y

end ComplCouplingHeat

/-- Top-level alias for `ComplCouplingHeat.SeedLamPJet2Decay`. -/
abbrev SeedLamPJet2Decay (κ : PlanarFrameKernels) : Prop :=
  ComplCouplingHeat.SeedLamPJet2Decay κ

/-- Top-level conditional proof of `SeedLamPDSharpDecay κ` (`PartIII-a:T21/c5/3/1/1`) from
`SeedLamPJet2Decay κ`. -/
theorem seedLamPDSharpDecay_of (κ : PlanarFrameKernels) (hJet : SeedLamPJet2Decay κ) :
    SeedLamPDSharpDecay κ :=
  ComplCouplingHeat.seedLamPDSharpDecay_of κ hJet

end UnforcedLeray.Short.IIIa
