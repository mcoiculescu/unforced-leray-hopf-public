import UnforcedLeray.Lib.Train.Profile
import UnforcedLeray.Lib.Gaussian.PeriodizationCell
import UnforcedLeray.Analysis.GaussianVortex.PlanarIntegrals

/-!
# The Gaussian train datum `P_c v₀` (INF16 T1)


target T1; decision D8 (and D1 for the carrier). Blueprint units **B0140** (`eq:st18-t00140`,
`paper/main.tex` lines 2045–2057, 2131–2151: the datum `v(q,η,0) = ∑ₙ v₀(q - nc, η)`, its
decaying stream `ψ(0) = -2∑ₙ e^{-|z-(nc,0)|²/4}`, `c`-periodic and centrally odd), the datum part
of **B0141** (tex 2152–2161: "the Gaussian sums and all their derivatives converge uniformly,
belong to every `H^j(C_c)`, and have vorticity in `L¹ ∩ L^∞` with zero integral"; tex 2183:
"Gaussian summation makes the initial bounds uniform for `c ≥ 2`") and **B0169**
(`eq:st18-t00166`, tex 2528–2538: `|ω(q,η,0)| ≤ C exp(-λη + C₀λ²)`, uniformly in `c ≥ 2`).

**Conventions and junk values.**
* `datum c = Gaussian.periodize c v₀` is a `tsum`; it is summable for `c ≠ 0`
  (`summable_datum`).
* `jet j f z = iteratedFDeriv ℝ j f z` (Fréchet derivatives on `ℝ × ℝ`, sup norm on the
  domain); the manuscript's `D^j` up to norm equivalence. `datum` is `C^∞`
  (`datum_contDiff`), so the jets are genuine.
* `jap m z = (1 + η²)^m = ⟨η⟩^{2m}`; the weight is `√(jap m z) = ⟨η⟩^m`.
* Cell norms are taken over the centred cell `Cyl.cell c` with Lebesgue measure (`Cyl.cellμ`,
  "one unnormalized cell", tex 2109–2110) and are stated as `eLpNorm` in `ℝ≥0∞` together with
  `MemLp`, so no junk value of the Lebesgue integral enters (`wCellL2`). The scoping signature
  wrote a real-valued `cellL2 = √∫‖f‖²`, which is `0` on non-integrable `f`; it is not used.
* Uniformity: the constants depend only on the orders `j, m`, for every `c ≥ 2` (tex 2183).
* The tilt bound is stated for every real `λ`, which contains both the manuscript's `λ ≥ 0`
  case and its `η ↦ -η` case (`datum_tilt`, `datum_tilt_abs`).

Main declarations: `jap`, `jet`, `cellL2`, `wCellL2`, `datum`, `stream0`, `Vc_zero`,
`summable_datum`, `datum_periodic`, `datum_odd`, `datum_div`, `datum_curl`, `datum_contDiff`,
`jet_datum`, `datum_stream`, `datum_bounds`, `datum_tilt`, `datum_tilt_abs`,
`integral_cell_curl_datum` (zero vorticity mass), `abs_curl_datum_le` (vorticity in `L^∞`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal
open MeasureTheory

namespace UnforcedLeray.Train

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Gaussian (periodize periodize_add_period periodize_eq shiftVec)
open Real

/-! ### Notation of INF16 §5 -/

/-- `⟨η⟩^{2m} = (1 + η²)^m`. -/
def jap (m : ℕ) (z : Plane) : ℝ := (1 + z.2 ^ 2) ^ m

/-- The `j`-th Fréchet derivative `D^j f`. -/
def jet (j : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Plane → E) :
    Plane → ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) E :=
  fun z => iteratedFDeriv ℝ j f z

/-- The one-cell `L²` norm (unnormalized centred cell), in `ℝ≥0∞`. -/
def cellL2 {E : Type*} [NormedAddCommGroup E] (c : ℝ) (f : Plane → E) : ℝ≥0∞ :=
  eLpNorm f 2 (Cyl.cellμ c)

/-- The weighted one-cell `L²` norm `‖⟨η⟩^m f‖_{L²(cell)}`, in `ℝ≥0∞`. -/
def wCellL2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (m : ℕ)
    (f : Plane → E) : ℝ≥0∞ :=
  eLpNorm (fun z => Real.sqrt (jap m z) • f z) 2 (Cyl.cellμ c)

/-! ### The datum -/

/-- The train datum `v(q,η,0) = ∑ₙ v₀(q - nc, η) = P_c v₀` (tex lines 2141–2147). -/
def datum (c : ℝ) : Plane → Vec := periodize c v0

/-- The datum stream `ψ(0) = -2 ∑ₙ e^{-|z - (nc,0)|²/4} = P_c ψ₀` (tex lines 2050–2051). -/
def stream0 (c : ℝ) : Plane → ℝ := periodize c psi0

theorem datum_apply (c : ℝ) (z : Plane) : datum c z = ∑' n : ℤ, v0 (z.1 - n * c, z.2) := rfl

/-- `V_c(·, 0) = P_c v₀`: the periodized heat vortex starts at the datum (INF16 T2). -/
theorem Vc_zero (ν c : ℝ) : Vc ν c 0 = datum c := by
  rw [Vc, isoV_zero]; rfl

theorem v0_neg (w : Plane) : v0 (-w) = -v0 w := by
  rw [← isoV_zero 0]; exact isoV_neg 0 0 w

/-- The series defining the datum converges (tex line 2153). -/
theorem summable_datum {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    Summable (fun n : ℤ => v0 (z.1 - n * c, z.2)) := by
  have h := summable_isoV (ν := 1) one_pos hc le_rfl z
  rwa [isoV_zero] at h

/-- The datum is `c`-periodic (tex line 2051). -/
theorem datum_periodic (c : ℝ) : Cyl.IsPeriodic c (datum c) := fun z =>
  periodize_add_period c _ z.1 z.2

/-- The datum is centrally odd (tex lines 2051, 2188–2191). -/
theorem datum_odd (c : ℝ) (z : Plane) : datum c (-z) = -datum c z :=
  periodize_neg_of_odd v0_neg c z

/-- The datum is divergence free. -/
theorem datum_div {c : ℝ} (hc : c ≠ 0) (z : Plane) : Cyl.divergence (datum c) z = 0 := by
  rw [← Vc_zero 1 c]; exact Vc_div one_pos hc le_rfl z

/-- The datum vorticity is the periodized `ω₀ = (2 - |x|²/2) e^{-|x|²/4}` (tex 2138–2139). -/
theorem datum_curl {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    Cyl.curl (datum c) z = periodize c omega0 z := by
  rw [← Vc_zero 1 c, Vc_curl one_pos hc le_rfl z]
  have h1 : width 1 0 = 1 := by simp [width]
  rw [h1]
  congr 1
  funext w
  exact (omega0_eq_eExp w).symm

/-! ### Smoothness and termwise derivatives -/

theorem v0_translate_bound' : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) → ∃ C : ℝ, ∀ z : Plane,
    ‖iteratedFDeriv ℝ k v0 z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) :=
  fun k _ => v0_translate_bound k

/-- The datum is `C^∞` (tex line 2153: the Gaussian sums and all their derivatives converge). -/
theorem datum_contDiff {c : ℝ} (hc : c ≠ 0) : ContDiff ℝ ∞ (datum c) :=
  Gaussian.contDiff_periodize (N := ⊤) (s := 2) (by norm_num) hc contDiff_v0
    v0_translate_bound'

/-- Termwise differentiation: `D^j(P_c v₀) = P_c(D^j v₀)`. -/
theorem jet_datum {c : ℝ} (hc : c ≠ 0) (j : ℕ) : jet j (datum c) = periodize c (jet j v0) := by
  funext z
  have h := Gaussian.iteratedFDeriv_periodize (N := ⊤) (s := 2) (by norm_num) hc contDiff_v0
    v0_translate_bound' (m := j) le_top
  simp only [jet, datum]
  rw [h, periodize_eq]
  rfl

/-- The datum has the decaying stream `ψ(0) = P_c ψ₀`: `v(0) = ∇^⊥ψ(0) = (-∂_ηψ(0), ∂_qψ(0))`
(tex lines 2050–2051), with genuine partial derivatives. -/
theorem datum_stream {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    HasDerivAt (fun q => stream0 c (q, z.2)) (datum c z 1) z.1 ∧
    HasDerivAt (fun η => stream0 c (z.1, η)) (-datum c z 0) z.2 ∧
    datum c z = toVec (-partialEta (stream0 c) z, partialQ (stream0 c) z) := by
  obtain ⟨A₀, hA₀, hb₀⟩ := norm_iteratedFDeriv_psi0_le 0
  obtain ⟨A₁, hA₁, hb₁⟩ := norm_iteratedFDeriv_psi0_le 1
  obtain ⟨K, hK, hk⟩ := exp_neg_sq_div_eight_le_rpow
  have hdec : ∀ (B : ℝ), 0 ≤ B → ∀ w : Plane,
      B * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) ≤ B * K * (1 + |w.1|) ^ (-(2 : ℝ)) := by
    intro B hB w
    have h1 : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) ≤ Real.exp (-w.1 ^ 2 / 8) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg w.2])
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1.trans (hk w.1)) hB
  have h₀ : ∀ w : Plane, ‖psi0 w‖ ≤ A₀ * K * (1 + |w.1|) ^ (-(2 : ℝ)) := by
    intro w
    have := hb₀ w
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (hdec A₀ hA₀ w)
  have h₁ : ∀ w : Plane, ‖fderiv ℝ psi0 w‖ ≤ A₁ * K * (1 + |w.1|) ^ (-(2 : ℝ)) := by
    intro w
    have := hb₁ w
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (hdec A₁ hA₁ w)
  have hdiff : Differentiable ℝ psi0 := (contDiff_psi0 (n := 1)).differentiable one_ne_zero
  have hF := Gaussian.hasFDerivAt_tsum_translates hdiff (by norm_num) hc h₀ h₁ z
  simp_rw [fderiv_comp_sub] at hF
  have hst : stream0 c = fun y => ∑' n : ℤ, psi0 (y - shiftVec c n) := by
    funext y; exact periodize_eq c psi0 y
  -- summability of the derivative series
  have hsum : Summable (fun n : ℤ => fderiv ℝ psi0 (z - shiftVec c n)) := by
    refine Summable.of_norm_bounded
      ((Gaussian.summable_translate (s := 2) (by norm_num) hc z.1).mul_left (A₁ * K)) ?_
    intro n
    have := h₁ (z - shiftVec c n)
    rw [Gaussian.sub_shiftVec] at this ⊢
    exact this
  set D := ∑' n : ℤ, fderiv ℝ psi0 (z - shiftVec c n) with hD
  have hperp : perpL D = datum c z := by
    rw [hD, perpL.map_tsum hsum, datum, periodize_eq]
    congr 1
    funext n
    rw [v0_eq_perpL]
  have hq : HasDerivAt (fun q => stream0 c (q, z.2)) (D (1, 0)) z.1 := by
    have hc1 : HasDerivAt (fun q : ℝ => ((q, z.2) : Plane)) ((1, 0) : Plane) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    rw [hst]
    exact hF.comp_hasDerivAt z.1 hc1
  have he : HasDerivAt (fun η => stream0 c (z.1, η)) (D (0, 1)) z.2 := by
    have hc1 : HasDerivAt (fun η : ℝ => ((z.1, η) : Plane)) ((0, 1) : Plane) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    rw [hst]
    exact hF.comp_hasDerivAt z.2 hc1
  have h1 : datum c z 1 = D (1, 0) := by rw [← hperp, perpL_apply]; rfl
  have h0 : datum c z 0 = -D (0, 1) := by rw [← hperp, perpL_apply]; rfl
  refine ⟨h1 ▸ hq, by rw [h0, neg_neg]; exact he, ?_⟩
  rw [show partialQ (stream0 c) z = D (1, 0) from hq.deriv,
    show partialEta (stream0 c) z = D (0, 1) from he.deriv, ← h1, ← neg_eq_iff_eq_neg.2 h0,
    neg_neg]
  exact eq_toVec _

/-! ### Uniform weighted bounds -/

theorem two_le_sq {c : ℝ} (hc : 2 ≤ c) : 2 ≤ c ^ 2 := by nlinarith

theorem four_le_sq {c : ℝ} (hc : 2 ≤ c) : 4 ≤ c ^ 2 := by nlinarith

theorem sqrt_jap_mul_exp_le {m : ℕ} {K : ℝ}
    (hk : ∀ η : ℝ, Real.sqrt ((1 + η ^ 2) ^ m) * Real.exp (-η ^ 2 / 16) ≤ K) (z : Plane) :
    Real.sqrt (jap m z) * Real.exp (-z.2 ^ 2 / (4 * 2)) ≤ K := by
  have h1 : Real.exp (-z.2 ^ 2 / (4 * 2)) ≤ Real.exp (-z.2 ^ 2 / 16) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg z.2])
  exact (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)).trans (hk z.2)

/-- Weighted sup bound for every derivative of the datum, uniform in `c ≥ 2`. -/
theorem datum_jet_sup (j m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 2 ≤ c → ∀ z : Plane,
    Real.sqrt (jap m z) * ‖jet j (datum c) z‖ ≤ C := by
  obtain ⟨A, hA, hb⟩ := norm_iteratedFDeriv_v0_le j
  obtain ⟨K, hK, hk⟩ := weight_mul_exp_le m
  refine ⟨10 * A * K, by positivity, fun c hc z => ?_⟩
  have hc0 : c ≠ 0 := by linarith
  rw [jet_datum hc0]
  have hf : ∀ w : Plane, ‖jet j v0 w‖ ≤ A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 2)) := by
    intro w; rw [show (4 : ℝ) * 2 = 8 by norm_num]; exact hb w
  have h := Gaussian.norm_periodize_le_of_gauss (by norm_num : (0 : ℝ) < 2) (two_le_sq hc) hf z
  have hw := sqrt_jap_mul_exp_le hk z
  calc Real.sqrt (jap m z) * ‖periodize c (jet j v0) z‖
      ≤ Real.sqrt (jap m z) * (10 * A * Real.exp (-z.2 ^ 2 / (4 * 2))) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = 10 * A * (Real.sqrt (jap m z) * Real.exp (-z.2 ^ 2 / (4 * 2))) := by ring
    _ ≤ 10 * A * K := mul_le_mul_of_nonneg_left hw (by positivity)

/-- `eLpNorm f 2 μ ≤ √C` from `∫⁻ ‖f‖ₑ² ≤ C`. -/
theorem eLpNorm_two_le_of_lintegral {E : Type*} [NormedAddCommGroup E] {f : Plane → E}
    {μ : Measure Plane} {C : ℝ} (hC : 0 ≤ C) (h : ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- The weighted cell `L²` bound for every derivative of the datum, uniform in `c ≥ 2`, in
`lintegral` form. -/
theorem datum_jet_lintegral (j m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 2 ≤ c →
    ∫⁻ z in Cyl.cell c, ‖Real.sqrt (jap m z) • jet j (datum c) z‖ₑ ^ 2 ≤ ENNReal.ofReal C := by
  obtain ⟨A, hA, hb⟩ := norm_iteratedFDeriv_v0_le j
  obtain ⟨K, hK, hk⟩ := weight_mul_exp_le m
  refine ⟨40 * π * (A * K) ^ 2 * 4, by positivity, fun c hc => ?_⟩
  have hc0 : 0 < c := by linarith
  set φ : ℝ → ℝ := fun η => Real.sqrt ((1 + η ^ 2) ^ m) with hφ
  set F : Plane → ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) Vec :=
    fun w => φ w.2 • jet j v0 w with hF
  have hper : ∀ z, Real.sqrt (jap m z) • jet j (datum c) z = periodize c F z := by
    intro z
    rw [jet_datum hc0.ne', hF, Gaussian.periodize_weight_smul]
    rfl
  have hFb : ∀ w : Plane, ‖F w‖ ≤ (A * K) * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 4)) := by
    intro w
    rw [hF, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := hb w
    have h2 := hk w.2
    have hsplit : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) ≤
        Real.exp (-w.2 ^ 2 / 16) * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 4)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg w.1])
    have hφ0 : 0 ≤ φ w.2 := Real.sqrt_nonneg _
    have hE := Real.exp_pos (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 4))
    calc φ w.2 * ‖jet j v0 w‖ ≤ φ w.2 * (A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8)) :=
          mul_le_mul_of_nonneg_left h1 hφ0
      _ ≤ φ w.2 * (A * (Real.exp (-w.2 ^ 2 / 16) *
            Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 4)))) := by gcongr
      _ = A * (φ w.2 * Real.exp (-w.2 ^ 2 / 16)) *
            Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 4)) := by ring
      _ ≤ A * K * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 4)) := by gcongr
  have hFm : AEStronglyMeasurable F := by
    have hφc : Continuous fun w : Plane => φ w.2 :=
      Real.continuous_sqrt.comp (by fun_prop)
    have hjc : Continuous fun w : Plane => jet j v0 w :=
      contDiff_v0.continuous_iteratedFDeriv (n := ⊤) (by exact_mod_cast le_top)
    have hcont : Continuous F := hφc.smul hjc
    exact hcont.aestronglyMeasurable
  have hL := Gaussian.lintegral_cell_sq_norm_periodize_le_of_gauss (by norm_num : (0 : ℝ) < 4)
    hc0 (four_le_sq hc) hFm hFb
  have hG : Cyl.IsPeriodic c (fun z => ‖periodize c F z‖ₑ ^ 2) := fun z => by
    simp only
    rw [periodize_add_period]
  have hcell := Cyl.lintegral_strip_eq_cell hc0 hG 0
  rw [zero_add] at hcell
  simp_rw [hper]
  rw [← hcell]
  exact hL

/-- **Uniform datum bounds** (tex lines 2152–2153, 2183; INF16 T1 `datum_bounds`): for every
derivative order `j` and weight exponent `m` there is `C` such that for every `c ≥ 2`,
`⟨η⟩^m |D^j(P_c v₀)| ≤ C` pointwise, `⟨η⟩^m D^j(P_c v₀) ∈ L²(cell)` and
`‖⟨η⟩^m D^j(P_c v₀)‖_{L²(cell)} ≤ C`. -/
theorem datum_bounds (j m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 2 ≤ c →
    (∀ z : Plane, Real.sqrt (jap m z) * ‖jet j (datum c) z‖ ≤ C) ∧
    MemLp (fun z => Real.sqrt (jap m z) • jet j (datum c) z) 2 (Cyl.cellμ c) ∧
    wCellL2 c m (jet j (datum c)) ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁, h₁⟩ := datum_jet_sup j m
  obtain ⟨C₂, hC₂, h₂⟩ := datum_jet_lintegral j m
  refine ⟨max C₁ (Real.sqrt C₂), le_max_of_le_left hC₁, fun c hc => ?_⟩
  have hc0 : c ≠ 0 := by linarith
  have hE := eLpNorm_two_le_of_lintegral (μ := Cyl.cellμ c) hC₂ (h₂ c hc)
  have hmeas : AEStronglyMeasurable (fun z => Real.sqrt (jap m z) • jet j (datum c) z)
      (Cyl.cellμ c) := by
    have hφc : Continuous fun z : Plane => Real.sqrt (jap m z) :=
      Real.continuous_sqrt.comp (by unfold jap; fun_prop)
    have hjc : Continuous fun z : Plane => jet j (datum c) z :=
      (datum_contDiff hc0).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have hcont : Continuous (fun z => Real.sqrt (jap m z) • jet j (datum c) z) :=
      hφc.smul hjc
    exact hcont.aestronglyMeasurable
  refine ⟨fun z => (h₁ c hc z).trans (le_max_left _ _), ⟨hmeas, ?_⟩, ?_⟩
  · exact hE.trans_lt ENNReal.ofReal_lt_top
  · exact hE.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-! ### The vorticity: `L^∞`, zero mass, exponential tilt -/

/-- `|ω(q,η,0)| ≤ 40 e^{-η²/8}` uniformly in `c ≥ 2` (vorticity in `L^∞`, tex line 2154). -/
theorem abs_curl_datum_le {c : ℝ} (hc : 2 ≤ c) (z : Plane) :
    |Cyl.curl (datum c) z| ≤ 40 * Real.exp (-z.2 ^ 2 / (4 * 2)) := by
  have hc0 : c ≠ 0 := by linarith
  rw [datum_curl hc0]
  have hf : ∀ w : Plane, ‖omega0 w‖ ≤ 4 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 2)) :=
    fun w => by rw [Real.norm_eq_abs]; exact omega0_abs_le w
  have h := Gaussian.norm_periodize_le_of_gauss (by norm_num : (0 : ℝ) < 2) (two_le_sq hc) hf z
  rw [Real.norm_eq_abs] at h
  linarith

/-- **Exponential tilt** (`eq:st18-t00166`, tex lines 2528–2538, unit B0169):
`|ω(q,η,0)| ≤ C e^{-λη + C₀λ²}` for every real `λ`, uniformly in `c ≥ 2`. -/
theorem datum_tilt : ∃ C C₀ : ℝ, 0 ≤ C ∧ 0 ≤ C₀ ∧ ∀ c : ℝ, 2 ≤ c → ∀ (lam : ℝ) (z : Plane),
    |Cyl.curl (datum c) z| ≤ C * Real.exp (-lam * z.2 + C₀ * lam ^ 2) := by
  refine ⟨40, 2, by norm_num, by norm_num, fun c hc lam z => ?_⟩
  refine (abs_curl_datum_le hc z).trans ?_
  have h : Real.exp (-z.2 ^ 2 / (4 * 2)) ≤ Real.exp (-lam * z.2 + 2 * lam ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg (z.2 - 4 * lam)])
  linarith

/-- The tilt bound in the two-sided form `|ω(q,η,0)| ≤ C e^{-λ|η| + C₀λ²}`, `λ ≥ 0`
(tex line 2537: "the same holds with `η` replaced by `-η`"). -/
theorem datum_tilt_abs : ∃ C C₀ : ℝ, 0 ≤ C ∧ 0 ≤ C₀ ∧ ∀ c : ℝ, 2 ≤ c → ∀ lam : ℝ, 0 ≤ lam →
    ∀ z : Plane, |Cyl.curl (datum c) z| ≤ C * Real.exp (-lam * |z.2| + C₀ * lam ^ 2) := by
  obtain ⟨C, C₀, hC, hC₀, h⟩ := datum_tilt
  refine ⟨C, C₀, hC, hC₀, fun c hc lam _ z => ?_⟩
  rcases le_total 0 z.2 with hz | hz
  · rw [abs_of_nonneg hz]; exact h c hc lam z
  · rw [abs_of_nonpos hz]
    have := h c hc (-lam) z
    rwa [neg_neg, neg_sq, show lam * z.2 = -lam * -z.2 by ring] at this

/-- **Zero vorticity mass** of the datum over one cell (tex line 2154: zero integral). -/
theorem integral_cell_curl_datum {c : ℝ} (hc : 0 < c) :
    ∫ z in Cyl.cell c, Cyl.curl (datum c) z = 0 := by
  have hcurl : (fun z => Cyl.curl (datum c) z) = periodize c omega0 :=
    funext fun z => datum_curl hc.ne' z
  have hom : omega0 = GaussianVortex.vorticity := by
    funext w
    simp only [omega0, gauss0, GaussianVortex.vorticity, GaussianVortex.planarGaussian,
      GaussianVortex.radiusSq, neg_div]
  have hint : Integrable omega0 := by rw [hom]; exact GaussianVortex.integrable_vorticity
  have hG : Cyl.IsPeriodic c (periodize c omega0) := fun z => periodize_add_period c _ z.1 z.2
  have hcell := Cyl.integral_strip_eq_cell hc hG 0
  rw [zero_add] at hcell
  rw [hcurl, ← hcell]
  have h := Gaussian.integral_cell_periodize hint hc
  rw [Gaussian.cell] at h
  rw [h, hom]
  exact GaussianVortex.integral_vorticity_eq_zero

end UnforcedLeray.Train
