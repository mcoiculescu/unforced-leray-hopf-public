import UnforcedLeray.Units.B0079
import UnforcedLeray.Lib.PlanarSectors.GreenUnique
import UnforcedLeray.Lib.PlanarSectors.Profile

/-!
# Green inverse of `Δ_n` on radial profiles (INF12 target P4)


§5, Level P, target **P4**; blueprint units `B0011` (`paper/main.tex` lines 683–689,
`eq:st18-t00007`: `R = Δ₂⁻¹`, "the regular-at-zero, decaying-at-infinity Green inverse") and
`B0079` (lines 1366–1379, `eq:st18-t00060`: the Green formula for `Δ_n`, `n ≥ 1`, on `L²_M`).

For `n ≥ 1` and a profile `g` with `r g(r) ∈ L¹(0, ∞)` (`B0011.WProf`),
`greenN n g r = -(2n)⁻¹ ∫₀^∞ (min(r,ρ)/max(r,ρ))ⁿ g(ρ) ρ dρ`, which is the manuscript formula
`-(2n)⁻¹ [r⁻ⁿ ∫₀^r ρ^{n+1} g + rⁿ ∫_r^∞ ρ^{1-n} g]` (`greenN_eq_greenInv`, with `B0079.greenInv`).
The kernel `(min/max)ⁿ ≤ 1` makes every integral below absolutely convergent under `WProf`,
so no junk value of the Bochner integral occurs.

Main declarations (namespace `UnforcedLeray.Planar`):
* `greenN`, `greenN_eq_Psi`, `greenN_eq_greenInv`;
* `IsRadialPoissonSol n g ψ` (the integrated form of `Δ_nψ = g`, `B0079.IsDeltaNSol`) and
  `isRadialPoissonSol_greenN`;
* `tendsto_greenN_nhdsGT_zero`, `tendsto_greenN_atTop`: regular at `0`, decaying at `∞`;
* `eqOn_greenN_of_tendsto_mul` (weakest boundary conditions), `eqOn_greenN_of_tendsto`,
  `eqOn_greenN_of_bounded`: uniqueness;
* `norm_greenN_le_L2w`: for `g ∈ L²(profileMeasure M)`, `M > 1`, `r ≥ 2`,
  `|greenN n g r| ≤ C ‖g‖ (r^{1-M} + r⁻ⁿ (1 + log r)^{1/2})` (lines 1374–1377);
* `integral_greenN_mul_symm`: `∫ (Gf) g r dr = ∫ f (Gg) r dr` (symmetry of the Green operator);
* `tendsto_sq_mul_greenN_two`: `r² greenN 2 g r → -(1/4) ∫₀^∞ ρ³ g(ρ) dρ` (far field).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace UnforcedLeray.Planar

open UnforcedLeray.B0011 (WProf Psi Phi ker)

/-- The Green inverse of `Δ_n = ∂_r² + r⁻¹∂_r - n²r⁻²` (`paper/main.tex` lines 1368–1373):
`greenN n g r = -(2n)⁻¹ ∫₀^∞ (min(r,ρ)/max(r,ρ))ⁿ g(ρ) ρ dρ`. -/
def greenN (n : ℕ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(((2 * n : ℝ)⁻¹ : ℝ) : ℂ) *
    ∫ ρ in Ioi (0 : ℝ), (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * g ρ * ρ

/-- `ψ` solves `Δ_nψ = g` on `(0, ∞)` in integrated form (`B0079.IsDeltaNSol`). -/
abbrev IsRadialPoissonSol (n : ℕ) (g ψ : ℝ → ℂ) : Prop := B0079.IsDeltaNSol n g ψ

theorem greenN_eq_Psi (n : ℕ) (g : ℝ → ℂ) (r : ℝ) :
    greenN n g r = -(1 / (2 * (n : ℂ))) * Psi n g r := by
  rw [greenN, Psi]
  congr 1
  · push_cast
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
    simp only [B0011.ker]
    push_cast
    ring

/-- `greenN` is the manuscript formula `eq:st18-t00060` (`B0079.greenInv`) at `r ≥ 0`. -/
theorem greenN_eq_greenInv {n : ℕ} (hn : n ≠ 0) {g : ℝ → ℂ} (hg : WProf g) {r : ℝ}
    (hr : 0 ≤ r) : greenN n g r = B0079.greenInv n g r := by
  rw [greenN_eq_Psi, B0079.greenInv_eq_Psi hn hg hr]

/-- At `n = 2`, `greenN 2` is the Green inverse `R` of `eq:st18-t00007` (`B0011.R`) at
`r > 0`. -/
theorem greenN_two_eq_R {g : ℝ → ℂ} (hg : WProf g) {r : ℝ} (hr : 0 < r) :
    greenN 2 g r = B0011.R g r := by
  rw [greenN_eq_Psi, B0011.R_eq_Psi hg hr]
  norm_num

/-- **`Δ_n(greenN n g) = g`** on `(0, ∞)` (integrated form), for `n ≥ 1` and `r g ∈ L¹`. -/
theorem isRadialPoissonSol_greenN {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℂ} (hg : WProf g) :
    IsRadialPoissonSol n g (greenN n g) := by
  obtain ⟨hd, hc, hi⟩ := B0079.deltaN_solution_of_wprof (by omega : n ≠ 0) hg
  have he : greenN n g = fun t => -(1 / (2 * (n : ℂ))) * Psi n g t :=
    funext (greenN_eq_Psi n g)
  rw [he]
  exact ⟨fun t => -(1 / (2 * (n : ℂ))) * Phi n g t, hd, hc, hi⟩

/-- `greenN n g` is regular at `0`: it tends to `0` as `r → 0⁺`. -/
theorem tendsto_greenN_nhdsGT_zero {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℂ} (hg : WProf g) :
    Tendsto (greenN n g) (𝓝[>] 0) (𝓝 0) := by
  have h := (hg.tendsto_Psi_nhdsGT_zero (by omega : n ≠ 0)).const_mul (-(1 / (2 * (n : ℂ))))
  rw [mul_zero] at h
  exact h.congr fun r => (greenN_eq_Psi n g r).symm

/-- `greenN n g` decays at infinity. -/
theorem tendsto_greenN_atTop {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℂ} (hg : WProf g) :
    Tendsto (greenN n g) atTop (𝓝 0) := by
  have h := (hg.tendsto_Psi_atTop (by omega : n ≠ 0)).const_mul (-(1 / (2 * (n : ℂ))))
  rw [mul_zero] at h
  exact h.congr fun r => (greenN_eq_Psi n g r).symm

theorem tendsto_ofReal_pow_nhdsGT_zero {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ n) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun r : ℝ => (r : ℂ) ^ n) (𝓝 0) (𝓝 (((0 : ℝ) : ℂ) ^ n)) :=
    (Complex.continuous_ofReal.pow _).tendsto 0
  rw [Complex.ofReal_zero, zero_pow (by omega)] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_inv_ofReal_pow_atTop {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun r : ℝ => ((r : ℂ) ^ n)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => (r ^ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega))
  have := (Complex.continuous_ofReal.tendsto 0).comp h
  simpa [Function.comp_def] using this

/-- **Uniqueness, weakest form**: a solution `ψ` of `Δ_nψ = g` on `(0, ∞)` with `ψ(r) rⁿ → 0` as
`r → 0⁺` and `ψ(r) r⁻ⁿ → 0` as `r → ∞` is `greenN n g` on `(0, ∞)`. These two conditions
exclude exactly the homogeneous solutions `r⁻ⁿ` and `rⁿ`. -/
theorem eqOn_greenN_of_tendsto_mul {n : ℕ} (hn : 1 ≤ n) {g ψ : ℝ → ℂ} (hg : WProf g)
    (hψ : IsRadialPoissonSol n g ψ)
    (h0 : Tendsto (fun r : ℝ => ψ r * (r : ℂ) ^ n) (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto (fun r : ℝ => ψ r * ((r : ℂ) ^ n)⁻¹) atTop (𝓝 0)) :
    EqOn ψ (greenN n g) (Ioi 0) := by
  obtain ⟨ψ', hd, hc, hi⟩ := hψ
  obtain ⟨G', hdG, hcG, hiG⟩ := isRadialPoissonSol_greenN hn hg
  refine eqOn_of_deltaN hn (fun a b ha hb => hg.intervalIntegrable ha hb) hd hc hi hdG hcG hiG
    ?_ ?_
  · have hG := (tendsto_greenN_nhdsGT_zero hn hg).mul (tendsto_ofReal_pow_nhdsGT_zero hn)
    rw [mul_zero] at hG
    have h := h0.sub hG
    rw [sub_zero] at h
    exact h.congr fun r => by ring
  · have hG := (tendsto_greenN_atTop hn hg).mul (tendsto_inv_ofReal_pow_atTop hn)
    rw [mul_zero] at hG
    have h := hinf.sub hG
    rw [sub_zero] at h
    exact h.congr fun r => by ring

/-- **Uniqueness** (`paper/main.tex` lines 683–689 at `n = 2`; line 1369 for `n ≥ 1`): a solution
of `Δ_nψ = g` on `(0, ∞)` that tends to `0` at `0⁺` and at `∞` is `greenN n g`. -/
theorem eqOn_greenN_of_tendsto {n : ℕ} (hn : 1 ≤ n) {g ψ : ℝ → ℂ} (hg : WProf g)
    (hψ : IsRadialPoissonSol n g ψ) (h0 : Tendsto ψ (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto ψ atTop (𝓝 0)) : EqOn ψ (greenN n g) (Ioi 0) := by
  refine eqOn_greenN_of_tendsto_mul hn hg hψ ?_ ?_
  · have h := h0.mul (tendsto_ofReal_pow_nhdsGT_zero hn)
    rwa [mul_zero] at h
  · have h := hinf.mul (tendsto_inv_ofReal_pow_atTop hn)
    rwa [mul_zero] at h

/-- **Uniqueness among solutions regular at `0`** (`paper/main.tex` lines 683–689: "the
regular-at-zero, decaying-at-infinity Green inverse"): a solution of `Δ_nψ = g` on `(0, ∞)` that
is bounded near `0⁺` and tends to `0` at `∞` is `greenN n g`. -/
theorem eqOn_greenN_of_bounded {n : ℕ} (hn : 1 ≤ n) {g ψ : ℝ → ℂ} (hg : WProf g)
    (hψ : IsRadialPoissonSol n g ψ) (h0 : ψ =O[𝓝[>] 0] fun _ : ℝ => (1 : ℝ))
    (hinf : Tendsto ψ atTop (𝓝 0)) : EqOn ψ (greenN n g) (Ioi 0) := by
  refine eqOn_greenN_of_tendsto_mul hn hg hψ ?_ ?_
  · have hpow : (fun r : ℝ => (r : ℂ) ^ n) =O[𝓝[>] 0] fun r : ℝ => r ^ n :=
      Asymptotics.isBigO_of_le _ fun r => by rw [norm_pow, norm_pow, Complex.norm_real]
    refine (h0.mul hpow).trans_tendsto ?_
    have : Tendsto (fun r : ℝ => (1 : ℝ) * r ^ n) (𝓝 0) (𝓝 ((1 : ℝ) * (0 : ℝ) ^ n)) :=
      (continuous_const.mul (continuous_pow n)).tendsto (0 : ℝ)
    rw [zero_pow (by omega), mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have h := hinf.mul (tendsto_inv_ofReal_pow_atTop hn)
    rwa [mul_zero] at h

/-! ### Weighted bound at infinity -/

/-- `(eLpNorm F 2 μ).toReal² = ∫ ‖F‖²` (adapted from `NUE.Ang.SectorL2Aux.toReal_eLpNorm_two_sq`,
which is stated for Lebesgue measure on `ℂ`). -/
theorem toReal_eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℂ}
    (hF : AEStronglyMeasurable F μ) :
    (eLpNorm F 2 μ).toReal ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  have hm2 : AEStronglyMeasurable (fun x => ‖F x‖ ^ 2) μ := hF.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hm2, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.toReal_pow]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  norm_num

theorem norm_sq_Lp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : Lp ℂ 2 μ) : ‖h‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, toReal_eLpNorm_two_sq (Lp.aestronglyMeasurable h)]

/-- The real density of `profileMeasure`. -/
def profileNN (M : ℝ) (r : ℝ) : NNReal := Real.toNNReal (2 * π * r * (1 + r ^ 2) ^ M)

theorem profileMeasure_eq_nn (M : ℝ) :
    profileMeasure M = (volume.restrict (Ioi 0)).withDensity fun r => (profileNN M r : ℝ≥0∞) :=
  rfl

theorem measurable_profileNN (M : ℝ) : Measurable (profileNN M) := by
  unfold profileNN
  fun_prop

theorem coe_profileNN {M r : ℝ} (hr : 0 < r) :
    (profileNN M r : ℝ) = 2 * π * r * (1 + r ^ 2) ^ M :=
  Real.coe_toNNReal _ (by positivity)

/-- A profile in `L²(profileMeasure M)` is an `L²_M` profile in the sense of unit `B0079`. -/
theorem memL2M_of_memLp {M : ℝ} {w : ℝ → ℂ} (hw : MemLp w 2 (profileMeasure M)) :
    B0079.MemL2M M w := by
  refine ⟨(aestronglyMeasurable_profileMeasure_iff M).1 hw.1, ?_⟩
  have h1 := (memLp_two_iff_integrable_sq_norm hw.1).1 hw
  rw [profileMeasure_eq_nn, integrable_withDensity_iff_integrable_smul
    (measurable_profileNN M)] at h1
  refine (h1.const_mul (2 * π)⁻¹).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : (0 : ℝ) < s := hs
  rw [NNReal.smul_def, smul_eq_mul, coe_profileNN hs']
  field_simp

theorem integral_sq_profileMeasure {M : ℝ} (w : ℝ → ℂ) :
    ∫ r, ‖w r‖ ^ 2 ∂profileMeasure M =
      2 * π * ∫ s in Ioi (0 : ℝ), ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s := by
  rw [profileMeasure_eq_nn, integral_withDensity_eq_integral_smul (measurable_profileNN M),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  rw [NNReal.smul_def, smul_eq_mul, coe_profileNN hs']
  ring

/-- The `B0079` norm of a profile is its `L²(profileMeasure M)` norm divided by `√(2π)`. -/
theorem normL2M_eq {M : ℝ} (w : Lp ℂ 2 (profileMeasure M)) :
    B0079.normL2M M w = ‖w‖ / √(2 * π) := by
  have h := norm_sq_Lp_eq_integral w
  rw [integral_sq_profileMeasure] at h
  have hpi : 0 < 2 * π := by positivity
  have h2 : ∫ s in Ioi (0 : ℝ), ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s = ‖w‖ ^ 2 / (2 * π) := by
    rw [h]
    field_simp
  rw [B0079.normL2M, h2, Real.sqrt_div' _ hpi.le, Real.sqrt_sq (norm_nonneg _)]

/-- **Bound at infinity** (`paper/main.tex` lines 1374–1377): for `n ≥ 1` and `M > 1` there is
`C` such that for every profile `g ∈ L²(2π r ⟨r⟩^{2M} dr)` and every `r ≥ 2`,
`|greenN n g r| ≤ C ‖g‖ (r^{1-M} + r⁻ⁿ (1 + log r)^{1/2})`. -/
theorem norm_greenN_le_L2w {M : ℝ} (hM : 1 < M) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Lp ℂ 2 (profileMeasure M)) (r : ℝ), 2 ≤ r →
      ‖greenN n g r‖ ≤ C * ‖g‖ * (r ^ (1 - M) + (r ^ n)⁻¹ * √(1 + Real.log r)) := by
  obtain ⟨C, hC, hb⟩ := B0079.norm_greenInv_le_far hn hM
  refine ⟨C / √(2 * π), by positivity, fun g r hr => ?_⟩
  have hw := memL2M_of_memLp (Lp.memLp g)
  rw [greenN_eq_greenInv (by omega) (hw.wprof hM) (by linarith)]
  refine (hb g hw r hr).trans_eq ?_
  rw [normL2M_eq]
  ring

/-! ### Symmetry of the Green operator -/

theorem measurable_minmax_pow (n : ℕ) :
    Measurable fun z : ℝ × ℝ => (((min z.1 z.2 / max z.1 z.2) ^ n : ℝ) : ℂ) := by
  fun_prop

theorem norm_minmax_pow_le {n : ℕ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ‖(((min r ρ / max r ρ) ^ n : ℝ) : ℂ)‖ ≤ 1 := by
  have hmax : 0 < max r ρ := lt_max_of_lt_left hr
  have h0 : 0 ≤ min r ρ / max r ρ := div_nonneg (le_min hr.le hρ.le) hmax.le
  have h1 : min r ρ / max r ρ ≤ 1 := div_le_one_of_le₀ min_le_max hmax.le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 n)]
  exact pow_le_one₀ h0 h1

/-- **Symmetry of the Green operator**: for `r f, r g ∈ L¹(0,∞)`,
`∫₀^∞ (greenN n f) g r dr = ∫₀^∞ f (greenN n g) r dr` (the kernel `(min/max)ⁿ` is
symmetric; adapted from NonUniqueEuler `H/Sec4/Adjoint/Green.lean`, `integral_green_mul_symm`). -/
theorem integral_greenN_mul_symm (n : ℕ) {f g : ℝ → ℂ} (hf : WProf f) (hg : WProf g) :
    ∫ r in Ioi (0 : ℝ), greenN n f r * g r * r =
      ∫ r in Ioi (0 : ℝ), f r * greenN n g r * r := by
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  set c : ℂ := -(((2 * n : ℝ)⁻¹ : ℝ) : ℂ) with hc
  set F : ℝ → ℝ → ℂ := fun x y =>
    (((min x y / max x y) ^ n : ℝ) : ℂ) * f y * y * (g x * x) with hF
  have hint : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hb : Integrable (fun z : ℝ × ℝ => (z.1 * ‖g z.1‖) * (z.2 * ‖f z.2‖)) (μ.prod μ) :=
      hg.int.mul_prod hf.int
    refine hb.mono' ?_ ?_
    · have hKm : AEStronglyMeasurable
          (fun z : ℝ × ℝ => (((min z.1 z.2 / max z.1 z.2) ^ n : ℝ) : ℂ)) (μ.prod μ) :=
        (measurable_minmax_pow n).aestronglyMeasurable
      have hfm : AEStronglyMeasurable (fun z : ℝ × ℝ => f z.2) (μ.prod μ) := hf.meas.comp_snd
      have hgm : AEStronglyMeasurable (fun z : ℝ × ℝ => g z.1) (μ.prod μ) := hg.meas.comp_fst
      have hy : AEStronglyMeasurable (fun z : ℝ × ℝ => ((z.2 : ℝ) : ℂ)) (μ.prod μ) :=
        (Complex.continuous_ofReal.comp continuous_snd).aestronglyMeasurable
      have hx : AEStronglyMeasurable (fun z : ℝ × ℝ => ((z.1 : ℝ) : ℂ)) (μ.prod μ) :=
        (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable
      exact ((hKm.mul hfm).mul hy).mul (hgm.mul hx)
    · rw [hμ, Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with z hz
      have hx : (0 : ℝ) < z.1 := hz.1
      have hy : (0 : ℝ) < z.2 := hz.2
      have hk := norm_minmax_pow_le (n := n) hx hy
      change ‖(((min z.1 z.2 / max z.1 z.2) ^ n : ℝ) : ℂ) * f z.2 * (z.2 : ℂ) *
        (g z.1 * (z.1 : ℂ))‖ ≤ _
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_of_nonneg hy.le,
        Complex.norm_of_nonneg hx.le]
      have h1 : 0 ≤ ‖f z.2‖ * z.2 := by positivity
      have h2 : 0 ≤ ‖g z.1‖ * z.1 := by positivity
      calc ‖(((min z.1 z.2 / max z.1 z.2) ^ n : ℝ) : ℂ)‖ * ‖f z.2‖ * z.2 * (‖g z.1‖ * z.1)
          = ‖(((min z.1 z.2 / max z.1 z.2) ^ n : ℝ) : ℂ)‖ *
              ((‖f z.2‖ * z.2) * (‖g z.1‖ * z.1)) := by ring
        _ ≤ 1 * ((‖f z.2‖ * z.2) * (‖g z.1‖ * z.1)) := by gcongr
        _ = z.1 * ‖g z.1‖ * (z.2 * ‖f z.2‖) := by ring
  have hL : ∫ r in Ioi (0 : ℝ), greenN n f r * g r * r = c * ∫ x, ∫ y, F x y ∂μ ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [greenN, hF]
    rw [← hc, mul_assoc, mul_assoc, ← integral_mul_const]
  have hR : ∫ r in Ioi (0 : ℝ), f r * greenN n g r * r = c * ∫ y, ∫ x, F x y ∂μ ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [greenN, hF]
    rw [← hc]
    have e : ∀ I : ℂ, f y * (c * I) * (y : ℂ) = c * (I * (f y * y)) := fun I => by ring
    rw [e, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [min_comm y x, max_comm y x]
    ring
  rw [hL, hR, integral_integral_swap hint]

/-! ### Far field at `n = 2` -/

/-- **Far field** (`paper/main.tex` line 1150, the coefficient `𝔐` of the far field, and the
proof of `eq:st18-t00062`, lines 1417–1422): if `ρ³ g(ρ)` is integrable on `(0, ∞)`, then
`r² greenN 2 g r → -(1/4) ∫₀^∞ ρ³ g(ρ) dρ` as `r → ∞`. -/
theorem tendsto_sq_mul_greenN_two {g : ℝ → ℂ}
    (hg : IntegrableOn (fun ρ : ℝ => (ρ : ℂ) ^ 3 * g ρ) (Ioi 0)) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ 2 * greenN 2 g r) atTop
      (𝓝 (-(1 / 4) * ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ 3 * g ρ)) := by
  set c : ℝ → ℝ → ℝ := fun r ρ => r ^ 2 * (min r ρ / max r ρ) ^ 2 / ρ ^ 2 with hc
  have hc_le : ∀ r ρ : ℝ, 0 < r → 0 < ρ → c r ρ ≤ 1 := by
    intro r ρ hr hρ
    simp only [hc]
    rw [div_le_one (by positivity : (0 : ℝ) < ρ ^ 2)]
    rcases le_total r ρ with h | h
    · rw [min_eq_left h, max_eq_right h, div_pow, mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      have : r ^ 2 * r ^ 2 ≤ ρ ^ 2 * ρ ^ 2 := by
        have := pow_le_pow_left₀ hr.le h 2
        exact mul_le_mul this this (by positivity) (by positivity)
      linarith
    · rw [min_eq_right h, max_eq_left h, div_pow, mul_div_assoc', mul_div_cancel_left₀ _
        (by positivity : r ^ 2 ≠ 0)]
  have hc_nn : ∀ r ρ : ℝ, 0 ≤ c r ρ := fun r ρ => by
    simp only [hc]
    positivity
  have hc_eq : ∀ r ρ : ℝ, 0 < ρ → ρ ≤ r → c r ρ = 1 := by
    intro r ρ hρ h
    simp only [hc]
    have hr : 0 < r := hρ.trans_le h
    rw [min_eq_right h, max_eq_left h, div_pow]
    field_simp
  have hrep : ∀ r : ℝ, 0 < r → (r : ℂ) ^ 2 * greenN 2 g r =
      -(1 / 4) * ∫ ρ in Ioi (0 : ℝ), (c r ρ : ℂ) * ((ρ : ℂ) ^ 3 * g ρ) := by
    intro r hr
    have key : ∫ ρ in Ioi (0 : ℝ), (c r ρ : ℂ) * ((ρ : ℂ) ^ 3 * g ρ) =
        (r : ℂ) ^ 2 * ∫ ρ in Ioi (0 : ℝ), (((min r ρ / max r ρ) ^ 2 : ℝ) : ℂ) * g ρ * ρ := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
      have hρ' : (0 : ℝ) < ρ := hρ
      have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ'.ne'
      simp only [hc]
      push_cast
      field_simp
    rw [key, greenN]
    push_cast
    ring
  have hlim : Tendsto (fun r : ℝ => ∫ ρ in Ioi (0 : ℝ), (c r ρ : ℂ) * ((ρ : ℂ) ^ 3 * g ρ))
      atTop (𝓝 (∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ 3 * g ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ρ => ‖(ρ : ℂ) ^ 3 * g ρ‖) ?_ ?_ hg.norm ?_
    · filter_upwards [Ioi_mem_atTop 0] with r hr
      refine AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
      refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
      simp only [hc]
      fun_prop
    · filter_upwards [Ioi_mem_atTop 0] with r hr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc_nn r ρ)]
      calc c r ρ * ‖(ρ : ℂ) ^ 3 * g ρ‖ ≤ 1 * ‖(ρ : ℂ) ^ 3 * g ρ‖ := by
            gcongr
            exact hc_le r ρ hr hρ
        _ = ‖(ρ : ℂ) ^ 3 * g ρ‖ := one_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      have hρ' : (0 : ℝ) < ρ := hρ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ici_mem_atTop ρ] with r hr
      rw [hc_eq r ρ hρ' hr, Complex.ofReal_one, one_mul]
  have := hlim.const_mul (-(1 / 4 : ℂ))
  refine this.congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with r hr
  exact (hrep r hr).symm

end UnforcedLeray.Planar
