import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

/-!
# Sub-lemmas for `PartIII-b:C/srcL/8` (`xmtLinear`)

Source `the November 2 reference manuscript`
4766-4796, 4917-4937.  The old tensor is supported (through `χ_o`) on `ρ² < 5ν/6`; on the receiver
region `(ε|y'|)² > 5ν/6` the Newton kernel is separated from the source disk; on `(ε|y'|)² < ν`
the stream cutoff `χ_y` vanishes identically.  The two regions cover `ℝ³`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Homogeneity: `X^mt_{r M} = r X^mt_M` (source 4766-4791; `integral_smul` throughout, no
hypotheses). -/
def XmtSmulP : Prop :=
  ∀ (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (r : ℝ),
    Xmt c ν ε μ χo χy (r • M) = r • Xmt c ν ε μ χo χy M

/-- Phase-mean additivity (source 4766-4775): for `u > 1.2/ν` the slices of old tensors with finite
`N₀` are integrable (`Integrable.prod_right_ae`), and for `u ≤ 1.2/ν` the cutoff `χ_o(νu)` vanishes;
the radial change of variables `u = ρ⁻²` pulls null sets of `u` back to null sets of `ℝ²`. -/
def SigmaAddAE : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M M' : Chart → Mat3, OldThinFinite c ν M → OldThinFinite c ν M' →
      sigmaM c ν χo (M + M') =ᵐ[volume] sigmaM c ν χo M + sigmaM c ν χo M'

/-- The Cartesian source `Σ_M` is integrable on `ℝ²` (source 4766-4775, 4924-4936): `|Σ_M(x')| ≤
ρ⁻¹|E(ρ⁻²)|`, and in polar coordinates `∫ ρ⁻¹|E(ρ⁻²)| dx' = π ∫ u^{-3/2}|E(u)| du ≲ N₀(M)`. -/
def SigmaInt : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ∀ j k, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k)

/-- Additivity of the zero-width Newton field on the receiver region `x₁² + x₂² > 5ν/6`
(source 4776-4782): `Σ_M` is supported in `ρ² < 5ν/6` (`χ_o` vanishes for `νu ≤ 6/5`), so for fixed
`x` in the region the kernel `∂³N(x - t(x',0))`, `t ∈ (0,1]`, is bounded on the support; with
`SigmaAddAE`, `SigmaInt` and `integral_add` (inner, then the `t` integral with the weight
`t^{2μ+2}`). -/
def NewtonVAdd : Prop :=
  ∀ (c ν μ : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → 0 < μ → IsOutwardCutoff χo →
    ∀ M M' : Chart → Mat3, OldThinFinite c ν M → OldThinFinite c ν M' →
      ∀ x : Vec3, 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2 →
        newtonV c ν μ χo (M + M') x = newtonV c ν μ χo M x + newtonV c ν μ χo M' x

/-- The outward ray integral converges absolutely on the receiver region (source 4180-4183,
4917-4937): `|V_{μ,M}(x)| ≲ |x|^{-4}‖Σ_M‖_{L¹}` for large `|x|` (kernel `|∂³N| ≲ |x|^{-4}`, source
supported in a fixed disk), so `ρ Z_z(ρ,z)` is integrable on `(r,∞)`; the integrand is
measurable (continuous in `ρ` on the region by dominated convergence). -/
def StreamTailInt : Prop :=
  ∀ (c ν ε μ : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → 0 < ε → 0 < μ → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ∀ y : Vec3, 5 * ν / 6 < (ε * cylR y) ^ 2 →
        IntegrableOn (fun ρ : ℝ => ρ *
          (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (rayPt y ρ) 2) (Ioi (cylR y))

/-! ## Assembly -/

theorem chiYr_zero_of_ne_lt {ν ε : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (hε : ε ≠ 0) {r : ℝ}
    (hr : (ε * r) ^ 2 < ν) : chiYr ν ε χy r = 0 := by
  unfold chiYr
  split_ifs with h0
  · rfl
  · apply hχ.zero
    have hp : 0 < (ε * r) ^ 2 := by positivity
    rw [le_div_iff₀ hp]; linarith

theorem streamCut_zero_of_lt {ν ε : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (hε : ε ≠ 0)
    (Z : Vec3 → Vec3) (y : Vec3) (hy : (ε * cylR y) ^ 2 < ν) : streamCut ν ε χy Z y = 0 := by
  have h0 : chiYr ν ε χy (cylR y) = 0 := chiYr_zero_of_ne_lt hχ hε hy
  have hd : deriv (chiYr ν ε χy) (cylR y) = 0 := by
    have hopen : IsOpen {s : ℝ | (ε * s) ^ 2 < ν} := isOpen_lt (by fun_prop) continuous_const
    have hev : chiYr ν ε χy =ᶠ[nhds (cylR y)] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hy] with s hs using chiYr_zero_of_ne_lt hχ hε hs
    rw [hev.deriv_eq]; simp
  unfold streamCut
  rw [h0, hd]; simp

theorem cylR_rayPt_nonneg {y : Vec3} (hy : cylR y ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    cylR (rayPt y ρ) = ρ := by
  have hsq : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    unfold cylR; rw [Real.sq_sqrt (by positivity)]
  have h : (ρ * (y 0 / cylR y)) ^ 2 + (ρ * (y 1 / cylR y)) ^ 2 = ρ ^ 2 := by
    have : (ρ * (y 0 / cylR y)) ^ 2 + (ρ * (y 1 / cylR y)) ^ 2
        = ρ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) / cylR y ^ 2 := by ring
    rw [this, ← hsq]; field_simp
  have e0 : rayPt y ρ 0 = ρ * (y 0 / cylR y) := by simp [rayPt]
  have e1 : rayPt y ρ 1 = ρ * (y 1 / cylR y) := by simp [rayPt]
  show Real.sqrt (rayPt y ρ 0 ^ 2 + rayPt y ρ 1 ^ 2) = ρ
  rw [e0, e1, h, Real.sqrt_sq hρ]

theorem cylR_sq (y : Vec3) : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  unfold cylR; rw [Real.sq_sqrt (by positivity)]

/-- Additivity of the young field on the receiver region. -/
theorem youngW_add_of (hN : NewtonVAdd) {c ν ε μ : ℝ} {χo : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hμ : 0 < μ) (hχo : IsOutwardCutoff χo) {M M' : Chart → Mat3} (hM : OldThinFinite c ν M)
    (hM' : OldThinFinite c ν M') {y : Vec3} (hy : 5 * ν / 6 < (ε * cylR y) ^ 2) :
    youngW c ν ε μ χo (M + M') y = youngW c ν ε μ χo M y + youngW c ν ε μ χo M' y := by
  have hx : 5 * ν / 6 < (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 := by
    have : (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 = (ε * cylR y) ^ 2 := by
      rw [mul_pow, cylR_sq]; simp [Pi.smul_apply]; ring
    rw [this]; exact hy
  unfold youngW
  rw [hN c ν μ χo hc hν hμ hχo M M' hM hM' _ hx, smul_add]

theorem xmt_add_of (hN : NewtonVAdd) (hT : StreamTailInt) {c ν ε μ : ℝ} {χo χy : ℝ → ℝ}
    (h : LHyp c ν ε μ χo χy) {M M' : Chart → Mat3} (hM : OldThinFinite c ν M)
    (hM' : OldThinFinite c ν M') :
    Xmt c ν ε μ χo χy (M + M') = Xmt c ν ε μ χo χy M + Xmt c ν ε μ χo χy M' := by
  funext y
  have hεne : ε ≠ 0 := h.eps_pos.ne'
  by_cases hy0 : (ε * cylR y) ^ 2 < ν
  · simp only [Xmt, Pi.add_apply]
    rw [streamCut_zero_of_lt h.chiY hεne _ y hy0, streamCut_zero_of_lt h.chiY hεne _ y hy0,
      streamCut_zero_of_lt h.chiY hεne _ y hy0, add_zero]
  · have hy : 5 * ν / 6 < (ε * cylR y) ^ 2 := by
      have := h.nu_pos; linarith [not_lt.1 hy0]
    have hpos : 0 < cylR y := by
      rcases (Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2)).lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        have h2 : cylR y = 0 := h1.symm
        rw [h2] at hy
        have := h.nu_pos
        norm_num at hy; linarith
    have hZ : ∀ z : Vec3, 5 * ν / 6 < (ε * cylR z) ^ 2 →
        (youngW c ν ε μ χo (M + M') - youngW c ν ε (μ + 1) χo (M + M')) z =
          (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) z +
          (youngW c ν ε μ χo M' - youngW c ν ε (μ + 1) χo M') z := by
      intro z hz
      simp only [Pi.sub_apply]
      rw [youngW_add_of hN h.c_pos h.nu_pos h.mu_pos h.chiO hM hM' hz,
        youngW_add_of hN h.c_pos h.nu_pos (by linarith [h.mu_pos]) h.chiO hM hM' hz]
      abel
    have hψ : streamPsi (youngW c ν ε μ χo (M + M') - youngW c ν ε (μ + 1) χo (M + M')) y =
        streamPsi (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) y +
        streamPsi (youngW c ν ε μ χo M' - youngW c ν ε (μ + 1) χo M') y := by
      unfold streamPsi
      have hcongr : ∫ ρ in Ioi (cylR y), ρ *
          (youngW c ν ε μ χo (M + M') - youngW c ν ε (μ + 1) χo (M + M')) (rayPt y ρ) 2 =
          ∫ ρ in Ioi (cylR y), (ρ * (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)
            (rayPt y ρ) 2 + ρ * (youngW c ν ε μ χo M' - youngW c ν ε (μ + 1) χo M')
            (rayPt y ρ) 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
        have hρ0 : 0 ≤ ρ := le_trans hpos.le (le_of_lt hρ)
        have hray : 5 * ν / 6 < (ε * cylR (rayPt y ρ)) ^ 2 := by
          rw [cylR_rayPt_nonneg hpos.ne' hρ0]
          have : (ε * cylR y) ^ 2 ≤ (ε * ρ) ^ 2 := by
            apply pow_le_pow_left₀ (by have := h.eps_pos; positivity)
            exact mul_le_mul_of_nonneg_left (le_of_lt hρ) h.eps_pos.le
          linarith
        rw [hZ _ hray]
        simp [mul_add]
      rw [hcongr, integral_add (hT c ν ε μ χo h.c_pos h.nu_pos h.eps_pos h.mu_pos h.chiO M hM y hy)
        (hT c ν ε μ χo h.c_pos h.nu_pos h.eps_pos h.mu_pos h.chiO M' hM' y hy)]
      ring
    simp only [Xmt, streamCut, Pi.add_apply]
    rw [hZ y hy, hψ]
    simp only [smul_add, mul_add, add_smul]
    abel

theorem xmtLinear_of (hS : XmtSmulP) (hN : NewtonVAdd) (hT : StreamTailInt) : XmtLinear :=
  fun _ _ _ _ _ _ h _ _ hM hM' r => ⟨xmt_add_of hN hT h hM hM', hS _ _ _ _ _ _ _ r⟩

end UnforcedLeray.Short.PartIIIb.Concrete
