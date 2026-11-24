import UnforcedLeray.Short.PartIIb.Sub.T12_1_5

/-!
# Part II-b, leaf `PartII-b:T12/1/5/9` (`OneDDerivZeroLr`): du Bois-Reymond in `L^r(ℝ)`

Source of record: `the November 2 reference manuscript`, lines 1727-1731 (the axial
zero mode is a gradient, so its flux average has zero weak derivative and vanishes in `L^r`).

Target: `oneDDerivZeroLr : OneDDerivZeroLr` (`Sub/T12_1_5.lean`, definition at line 168), with no
added hypotheses. The proof copies `UnforcedLeray.Cyl.OneD.eq_zero_of_deriv`
(`Lib/CylinderB/Liouville1D.lean`, the `L²` case) with the Hölder pair `(r, r')`,
`r' = r/(r-1)`, in place of `(2, 2)`. Helpers carry the prefix `ddz_`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cyl.OneD (Test bump0 test_bump0 integral_bump0 exists_primitive)

/-- Real scalar multiplication written in the order used by `OneDDerivZeroLr`. -/
theorem ddz_mul_ofReal_eq (x : ℝ) (z : ℂ) : z * (x : ℂ) = x • z := by
  rw [Complex.real_smul]
  ring

/-- Hölder inequality in the exponent pair `(r', r)` for a real weight `u` against `v`. -/
theorem ddz_norm_integral_le {r r' : ℝ} (hrr : r.HolderConjugate r') {u : ℝ → ℝ} {v : ℝ → ℂ}
    (hu : MemLp u (ENNReal.ofReal r') volume) (hv : MemLp v (ENNReal.ofReal r) volume) :
    ‖∫ x, u x • v x‖ ≤
      (eLpNorm u (ENNReal.ofReal r') volume).toReal *
        (eLpNorm v (ENNReal.ofReal r) volume).toReal := by
  have : ENNReal.HolderTriple (ENNReal.ofReal r') (ENNReal.ofReal r) 1 :=
    hrr.symm.ennrealOfReal
  have h1 : eLpNorm (u • v) 1 volume ≤
      eLpNorm u (ENNReal.ofReal r') volume * eLpNorm v (ENNReal.ofReal r) volume :=
    eLpNorm_smul_le_mul_eLpNorm hv.1 hu.1
  have hm : AEStronglyMeasurable (u • v) volume := hu.1.smul hv.1
  calc ‖∫ x, u x • v x‖ ≤ ∫ x, ‖u x • v x‖ := norm_integral_le_integral_norm _
    _ = (eLpNorm (u • v) 1 volume).toReal := by
        show ∫ x, ‖(u • v) x‖ = _
        rw [integral_norm_eq_lintegral_enorm hm, eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (eLpNorm u (ENNReal.ofReal r') volume * eLpNorm v (ENNReal.ofReal r) volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hu.2.ne hv.2.ne) h1
    _ = _ := ENNReal.toReal_mul

/-- Dilation of `L^p` norms: `‖β(· / R)‖_p = R^{1/p} ‖β‖_p` for `R > 0` and a test `β`. -/
theorem ddz_eLpNorm_comp_div {β : ℝ → ℝ} (hβ : Test β) {p : ℝ≥0∞} (hp1 : p ≠ 0)
    (hp2 : p ≠ ⊤) {R : ℝ} (hR : 0 < R) :
    eLpNorm (fun x => β (x / R)) p volume =
      ENNReal.ofReal (R ^ p.toReal⁻¹) * eLpNorm β p volume := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm hp1 hp2 ((hβ.comp_div hR.ne').memLp p),
    MemLp.eLpNorm_eq_integral_rpow_norm hp1 hp2 (hβ.memLp p)]
  rw [Measure.integral_comp_div (fun y => ‖β y‖ ^ p.toReal) R, abs_of_pos hR, smul_eq_mul,
    Real.mul_rpow hR.le (integral_nonneg fun _ => by positivity)]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]

/-- Exponent identity `R⁻¹ R^{1/r'} = R^{-1/r}` for conjugate exponents. -/
theorem ddz_inv_mul_rpow {r r' : ℝ} (hsum : r⁻¹ + r'⁻¹ = 1) {R : ℝ} (hR : 0 < R) :
    R⁻¹ * R ^ r'⁻¹ = R ^ (-r⁻¹) := by
  have h : -r⁻¹ = r'⁻¹ - 1 := by linarith
  rw [h, Real.rpow_sub hR, Real.rpow_one, div_eq_inv_mul]

/-- If `0 ≤ x ≤ f n` for all `n` and `f n → 0`, then `x = 0`. -/
theorem ddz_eq_zero_of_le_tendsto {x : ℝ} (hx : 0 ≤ x) {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (h : ∀ n, x ≤ f n) : x = 0 :=
  le_antisymm (ge_of_tendsto' hf h) hx

/-- A test times an `L^r` function is integrable (`1 ≤ r`). -/
theorem ddz_integrable_smul {r : ℝ} (hr : 1 ≤ r) {ψ : ℝ → ℝ} (hψ : Test ψ) {v : ℝ → ℂ}
    (hv : MemLp v (ENNReal.ofReal r) volume) :
    Integrable (fun x => ψ x • v x) volume :=
  (hv.locallyIntegrable (ENNReal.one_le_ofReal.2 hr)).integrable_smul_left_of_hasCompactSupport
    hψ.continuous hψ.compact

/-- Core estimate: if `∫ v ψ' = 0` for all tests `ψ`, then `∫ θ v = 0` for every test `θ`. -/
theorem ddz_main {r r' : ℝ} (hrr : r.HolderConjugate r') (hr : 1 ≤ r) {v : ℝ → ℂ}
    (hv : MemLp v (ENNReal.ofReal r) volume)
    (h : ∀ ψ : ℝ → ℝ, Test ψ → ∫ x, deriv ψ x • v x = 0) (θ : ℝ → ℝ) (hθ : Test θ) :
    ∫ x, θ x • v x = 0 := by
  have hr0 : 0 < r := hrr.pos
  have hr'0 : 0 < r' := hrr.symm.pos
  have hsum : r⁻¹ + r'⁻¹ = 1 := hrr.inv_add_inv_eq_one
  have hp1 : ENNReal.ofReal r' ≠ 0 := (ENNReal.ofReal_pos.2 hr'0).ne'
  have hp2 : ENNReal.ofReal r' ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : ∀ R : ℝ, 0 < R →
      ‖∫ x, θ x • v x‖ ≤
        (‖∫ x, θ x‖ * (eLpNorm bump0 (ENNReal.ofReal r') volume).toReal *
          (eLpNorm v (ENNReal.ofReal r) volume).toReal) * R ^ (-r⁻¹) := by
    intro R hR
    set βR : ℝ → ℝ := fun x => R⁻¹ * bump0 (x / R) with hβR
    have hβ : Test βR := (test_bump0.comp_div hR.ne').const_mul R⁻¹
    have hint : ∫ x, βR x = 1 := by
      simp only [hβR]
      rw [integral_const_mul, Measure.integral_comp_div bump0 R, integral_bump0, abs_of_pos hR,
        smul_eq_mul, mul_one, inv_mul_cancel₀ hR.ne']
    set g : ℝ → ℝ := fun x => θ x - (∫ y, θ y) * βR x with hg
    have hgt : Test g := hθ.sub (hβ.const_mul _)
    have hg0 : ∫ x, g x = 0 := by
      simp only [hg]
      rw [integral_sub hθ.integrable (hβ.const_mul _).integrable, integral_const_mul, hint]
      ring
    obtain ⟨G, hG, hGd⟩ := exists_primitive hgt hg0
    have hzero := h G hG
    have hdG : _root_.deriv G = g := funext fun x => (hGd x).deriv
    rw [hdG] at hzero
    have hsplit : ∫ x, θ x • v x = (∫ y, θ y) • ∫ x, βR x • v x := by
      have e : (fun x => g x • v x) = fun x => θ x • v x - (∫ y, θ y) • (βR x • v x) := by
        funext x
        simp only [hg, sub_smul, mul_smul]
      have hi2 : Integrable (fun x => (∫ y, θ y) • (βR x • v x)) volume :=
        (ddz_integrable_smul hr hβ hv).smul (∫ y, θ y)
      rw [e, integral_sub (ddz_integrable_smul hr hθ hv) hi2, integral_smul] at hzero
      exact sub_eq_zero.1 hzero
    have hnβ : (eLpNorm βR (ENNReal.ofReal r') volume).toReal =
        R ^ (-r⁻¹) * (eLpNorm bump0 (ENNReal.ofReal r') volume).toReal := by
      have e : βR = R⁻¹ • fun x => bump0 (x / R) := rfl
      rw [e, eLpNorm_const_smul, ddz_eLpNorm_comp_div test_bump0 hp1 hp2 hR,
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hR.le _), toReal_enorm,
        Real.norm_of_nonneg (inv_nonneg.2 hR.le), ENNReal.toReal_ofReal hr'0.le,
        ← ddz_inv_mul_rpow hsum hR]
      ring
    have hbound : ‖∫ x, βR x • v x‖ ≤
        R ^ (-r⁻¹) * (eLpNorm bump0 (ENNReal.ofReal r') volume).toReal *
          (eLpNorm v (ENNReal.ofReal r) volume).toReal := by
      have h1 := ddz_norm_integral_le hrr (u := βR) (hβ.memLp _) hv
      rw [hnβ] at h1
      exact h1
    rw [hsplit, norm_smul]
    calc ‖∫ y, θ y‖ * ‖∫ x, βR x • v x‖
        ≤ ‖∫ y, θ y‖ * (R ^ (-r⁻¹) * (eLpNorm bump0 (ENNReal.ofReal r') volume).toReal *
            (eLpNorm v (ENNReal.ofReal r) volume).toReal) :=
          mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ = (‖∫ x, θ x‖ * (eLpNorm bump0 (ENNReal.ofReal r') volume).toReal *
            (eLpNorm v (ENNReal.ofReal r) volume).toReal) * R ^ (-r⁻¹) := by ring
  have hlim : Tendsto (fun n : ℕ =>
      (‖∫ x, θ x‖ * (eLpNorm bump0 (ENNReal.ofReal r') volume).toReal *
        (eLpNorm v (ENNReal.ofReal r) volume).toReal) * ((n : ℝ) + 1) ^ (-r⁻¹))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-r⁻¹)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (inv_pos.2 hr0)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h2 := h1.const_mul (‖∫ x, θ x‖ * (eLpNorm bump0 (ENNReal.ofReal r') volume).toReal *
        (eLpNorm v (ENNReal.ofReal r) volume).toReal)
    rw [mul_zero] at h2
    exact h2
  have hzero := ddz_eq_zero_of_le_tendsto (norm_nonneg _) hlim
    fun n => key ((n : ℝ) + 1) (by positivity)
  exact norm_eq_zero.1 hzero

/-- **Leaf `PartII-b:T12/1/5/9`**: the `L^r(ℝ)` du Bois-Reymond lemma, `1 < r`, `e ∈ L^r(ℝ; ℂ)`:
if `∫ e ζ' = 0` for every test `ζ`, then `∫ e χ = 0` for every test `χ`. -/
theorem oneDDerivZeroLr : OneDDerivZeroLr := by
  unfold OneDDerivZeroLr
  intro r hr e he hD χ hχ
  have hrr : r.HolderConjugate (Real.conjExponent r) := Real.HolderConjugate.conjExponent hr
  have hD' : ∀ ψ : ℝ → ℝ, Test ψ → ∫ x, deriv ψ x • e x = 0 := by
    intro ψ hψ
    have h0 := hD ψ hψ
    simpa only [ddz_mul_ofReal_eq] using h0
  have hmain := ddz_main hrr hr.le he hD' χ hχ
  simpa only [ddz_mul_ofReal_eq] using hmain

end UnforcedLeray.Short.IIb
