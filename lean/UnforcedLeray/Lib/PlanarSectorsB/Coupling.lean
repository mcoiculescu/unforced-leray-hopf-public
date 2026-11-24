import UnforcedLeray.Lib.PlanarSectors
import UnforcedLeray.Lib.Semigroups.SkewExp
import UnforcedLeray.Lib.Semigroups.Multiplication
import UnforcedLeray.Lib.SpecialFunctions.GammaTails
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Sector couplings on `L²_M` (INF12 target P6)


§5, Level P, target **P6**; plan `scoping/README.md` §5, Wave 2, block 2H (PLAN1); decision D7
(G1/G2 at `j = 0`, sector by sector, bounded generators) and bypass B1 of the note.

Manuscript (`paper/main.tex`): the generator `𝓛f = -Ω∂_ϑf - (Kf)·∇E₀` (lines 662–670,
`eq:st18-t00004`, blueprint unit `B0009`), with `E₀' = r k` (lines 639–647, `eq:st18-t00001`,
`eq:st18-t00002`). On the angular sector `f = w(r)e^{inϑ}` one has `Ω∂_ϑ f = inΩ w e^{inϑ}` and
`Kf = ∇^⊥(ψ e^{inϑ})` with `ψ = Δ_{|n|}⁻¹ w` (the Green formula `eq:st18-t00060`, lines
1366–1379, unit `B0079`), whose radial component is `-(in/r)ψ e^{inϑ}`, so
`-(Kf)·∇E₀ = in k(r) ψ(r) e^{inϑ}`. At `n = 2` this is the `2ikR` of `L₀` (lines 678–682,
`eq:st18-t00006`). The compactness of the coupling is the `j = 0` case of the claim "`A_E` is
compact on `H^j_M`" (lines 1206–1222, units `B0059`–`B0061`), proved here sector by sector.

Main declarations (namespace `UnforcedLeray.Planar`):
* `ProfL2 M = L²((0,∞), 2π r ⟨r⟩^{2M} dr)`, the profile space of one sector (P3);
* `wrep`, `crep`: the representers; `greenN_eq_inner` writes
  `greenN n w r = -(2n)⁻¹ ⟪crep_{n,r}, w⟫`, and `norm_greenN_le_wrep` gives the uniform bound
  `|greenN n w r| ≤ (2n)⁻¹ ‖wrep‖ ‖w‖` (all `r > 0`, all `n`);
* `couplingSec hM n`: `w ↦ i n k(r) greenN |n| w (r)` on `ProfL2 M` (`coeFn_couplingSec`),
  with `norm_couplingSec_le` (uniform in `n`), `couplingSec_zero`, `couplingSec_neg`,
  `isCompactOperator_couplingSec`, `tendsto_norm_couplingSec`;
* `omegaP M` (multiplication by `Ω`, selfadjoint), `transportSec M n = -(in) Ω` (skew-adjoint,
  `adjoint_transportSec`), `Lsec hM n = transportSec M n + couplingSec hM n`
  (`coeFn_Lsec`), and the uniform growth bound `norm_exp_Lsec_le`:
  `‖exp(t Lsec n)‖ ≤ e^{t B_M}` for `t ≥ 0`, with `B_M` independent of `n`.

No junk value enters a statement: `greenN 0 = 0` only through the factor `(2·0)⁻¹ = 0`, and the
coupling carries the factor `n`, so `couplingSec hM 0 = 0` is also the manuscript's statement
(radial vorticity has tangential velocity, line 1356, unit `B0078`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)

/-- The profile space `L²((0,∞), 2π r ⟨r⟩^{2M} dr)` of one angular sector of `L²_M` (P3). -/
abbrev ProfL2 (M : ℝ) : Type := Lp ℂ 2 (profileMeasure M)

theorem ae_profile_pos (M : ℝ) : ∀ᵐ r ∂profileMeasure M, (0 : ℝ) < r :=
  (profileMeasure_ac M).ae_le (ae_restrict_mem measurableSet_Ioi)

/-- Integrals against `profileMeasure M` are integrals over `(0, ∞)` against `2π r ⟨r⟩^{2M} dr`
(no integrability hypothesis: both sides are Bochner integrals of the same function). -/
theorem integral_profileMeasure (M : ℝ) (g : ℝ → ℂ) :
    ∫ s, g s ∂profileMeasure M =
      ∫ s in Ioi (0 : ℝ), ((2 * π * s * (1 + s ^ 2) ^ M : ℝ) : ℂ) * g s := by
  rw [profileMeasure_eq_nn, integral_withDensity_eq_integral_smul (measurable_profileNN M)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  rw [NNReal.smul_def, coe_profileNN hs', Complex.real_smul]

/-- Membership in `ProfL2 M` through the radial integral. -/
theorem memLp_profile_iff {M : ℝ} {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi 0))) :
    MemLp h 2 (profileMeasure M) ↔
      IntegrableOn (fun s => ‖h s‖ ^ 2 * (s * (1 + s ^ 2) ^ M)) (Ioi 0) := by
  have hm' : AEStronglyMeasurable h (profileMeasure M) :=
    (aestronglyMeasurable_profileMeasure_iff M).2 hm
  rw [memLp_two_iff_integrable_sq_norm hm', profileMeasure_eq_nn,
    integrable_withDensity_iff_integrable_smul (measurable_profileNN M)]
  constructor
  · intro h1
    refine (h1.const_mul (2 * π)⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    rw [NNReal.smul_def, smul_eq_mul, coe_profileNN hs']
    field_simp
  · intro h1
    refine (h1.const_mul (2 * π)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    rw [NNReal.smul_def, smul_eq_mul, coe_profileNN hs']
    ring

/-! ### Two integrability facts -/

/-- `s ⟨s⟩^{-2M}` is integrable on `(0,∞)` for `M > 1` (this is "`M > 1` makes the integral
bounded", `paper/main.tex` line 660). -/
theorem integrableOn_mul_one_add_sq_rpow_neg {M : ℝ} (hM : 1 < M) :
    IntegrableOn (fun s : ℝ => s * ((1 + s ^ 2) ^ M)⁻¹) (Ioi 0) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * M - 1)
    (by simp only [Module.finrank_self, Nat.cast_one]; linarith)
  refine h.integrableOn.mono' ?_ ?_
  · have hcont : Continuous (fun s : ℝ => s * ((1 + s ^ 2) ^ M)⁻¹) := by
      refine continuous_id.mul (Continuous.inv₀ ?_ ?_)
      · exact (continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun s => Or.inl (show (1 : ℝ) + s ^ 2 ≠ 0 by positivity))
      · intro s
        exact (Real.rpow_pos_of_pos (show (0 : ℝ) < 1 + s ^ 2 by positivity) M).ne'
    exact hcont.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hb : 0 < 1 + s ^ 2 := by positivity
    have h1 : s ≤ (1 + s ^ 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      calc s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs'.le).symm
        _ ≤ Real.sqrt (1 + s ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs, ← Real.rpow_neg hb.le]
    calc s * (1 + s ^ 2) ^ (-M) ≤ (1 + s ^ 2) ^ (1 / 2 : ℝ) * (1 + s ^ 2) ^ (-M) := by gcongr
      _ = (1 + s ^ 2) ^ (-(2 * M - 1) / 2) := by
        rw [← Real.rpow_add hb]
        ring_nf

/-- `s ⟨s⟩^{2a} e^{-c s²}` is integrable on `(0, ∞)` for every real `a` and `c > 0`
(substitution `u = s²` in `Special.integrableOn_one_add_rpow_mul_exp_neg`). -/
theorem integrableOn_mul_one_add_sq_rpow_mul_exp {a c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => s * ((1 + s ^ 2) ^ a * Real.exp (-(c * s ^ 2)))) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_rpow_iff' (fun u : ℝ => (1 + u) ^ a * Real.exp (-(c * u)))
    (p := 2) two_ne_zero).2 (Special.integrableOn_one_add_rpow_mul_exp_neg (M := a) hc)
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs' : (0 : ℝ) < s := hs
  simp only [smul_eq_mul]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]

/-- The coefficient `k(r) = (r²/4 - 2)e^{-r²/4}` (`eq:st18-t00002`, tex line 647) lies in every
profile space `ProfL2 M`. -/
theorem memLp_radialK_profile (M : ℝ) :
    MemLp (fun r => (radialK r : ℂ)) 2 (profileMeasure M) := by
  have hc : Continuous fun r => (radialK r : ℂ) :=
    Complex.continuous_ofReal.comp B0012.continuous_radialK
  refine (memLp_profile_iff hc.aestronglyMeasurable).2 ?_
  have h := (integrableOn_mul_one_add_sq_rpow_mul_exp (a := M + 2) (c := 1 / 2)
    (by norm_num)).const_mul 4
  refine h.mono' ((hc.norm.pow 2).mul (continuous_id.mul
    ((continuous_const.add (continuous_id.pow 2)).rpow_const
      (fun s => Or.inl (show (1 : ℝ) + s ^ 2 ≠ 0 by positivity))))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : (0 : ℝ) < s := hs
  have hb : 0 < 1 + s ^ 2 := by positivity
  have hP : 0 < (1 + s ^ 2) ^ M := Real.rpow_pos_of_pos hb M
  rw [Real.norm_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : radialK s ^ 2 = (s ^ 2 / 4 - 2) ^ 2 * Real.exp (-(1 / 2 * s ^ 2)) := by
    unfold radialK radialOmega
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hpow : (1 + s ^ 2) ^ (M + 2) = (1 + s ^ 2) ^ M * (1 + s ^ 2) ^ 2 := by
    rw [Real.rpow_add hb, Real.rpow_two]
  have hq : (s ^ 2 / 4 - 2) ^ 2 ≤ 4 * (1 + s ^ 2) ^ 2 := by nlinarith [sq_nonneg s]
  rw [hk, hpow]
  have he := (Real.exp_pos (-(1 / 2 * s ^ 2))).le
  calc (s ^ 2 / 4 - 2) ^ 2 * Real.exp (-(1 / 2 * s ^ 2)) * (s * (1 + s ^ 2) ^ M)
      ≤ (4 * (1 + s ^ 2) ^ 2) * Real.exp (-(1 / 2 * s ^ 2)) * (s * (1 + s ^ 2) ^ M) := by
        gcongr
    _ = 4 * (s * ((1 + s ^ 2) ^ M * (1 + s ^ 2) ^ 2 * Real.exp (-(1 / 2 * s ^ 2)))) := by ring

/-- `k` as an element of `ProfL2 M`. -/
def kProf (M : ℝ) : ProfL2 M := (memLp_radialK_profile M).toLp _

theorem coeFn_kProf (M : ℝ) : ⇑(kProf M) =ᵐ[profileMeasure M] fun r => (radialK r : ℂ) :=
  (memLp_radialK_profile M).coeFn_toLp

/-! ### The representers of the Green operator -/

/-- The weight `(2π)⁻¹ ⟨s⟩^{-2M}`: pairing against it in `ProfL2 M` is `∫₀^∞ · s ds`. -/
def wrep (M : ℝ) (s : ℝ) : ℝ := (2 * π)⁻¹ * ((1 + s ^ 2) ^ M)⁻¹

theorem wrep_pos (M s : ℝ) : 0 < wrep M s := by
  unfold wrep
  have : 0 < (1 + s ^ 2) ^ M := Real.rpow_pos_of_pos (by positivity) M
  positivity

theorem continuous_wrep (M : ℝ) : Continuous (wrep M) :=
  continuous_const.mul (((continuous_const.add (continuous_id.pow 2)).rpow_const
    (fun s => Or.inl (show (1 : ℝ) + s ^ 2 ≠ 0 by positivity))).inv₀
    (fun s => (Real.rpow_pos_of_pos (show (0 : ℝ) < 1 + s ^ 2 by positivity) M).ne'))

theorem memLp_wrep {M : ℝ} (hM : 1 < M) :
    MemLp (fun s => (wrep M s : ℂ)) 2 (profileMeasure M) := by
  have hc : Continuous fun s => (wrep M s : ℂ) := Complex.continuous_ofReal.comp (continuous_wrep M)
  refine (memLp_profile_iff hc.aestronglyMeasurable).2 ?_
  have hi : IntegrableOn (fun s : ℝ => (2 * π)⁻¹ ^ 2 * (s * ((1 + s ^ 2) ^ M)⁻¹)) (Ioi 0) :=
    (integrableOn_mul_one_add_sq_rpow_neg hM).const_mul ((2 * π)⁻¹ ^ 2)
  refine hi.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs' : (0 : ℝ) < s := hs
  have hP : 0 < (1 + s ^ 2) ^ M := Real.rpow_pos_of_pos (by positivity) M
  rw [Complex.norm_real, Real.norm_of_nonneg (wrep_pos M s).le, wrep]
  field_simp

/-- `wrep` as an element of `ProfL2 M` (`M > 1`). -/
def wrepLp {M : ℝ} (hM : 1 < M) : ProfL2 M := (memLp_wrep hM).toLp _

theorem coeFn_wrepLp {M : ℝ} (hM : 1 < M) :
    ⇑(wrepLp hM) =ᵐ[profileMeasure M] fun s => (wrep M s : ℂ) :=
  (memLp_wrep hM).coeFn_toLp

/-- The representer `crep_{n,r}(s) = (min(r,s)/max(r,s))ⁿ (2π)⁻¹ ⟨s⟩^{-2M}` of the kernel of
`greenN n` at `r`. -/
def crep (M : ℝ) (n : ℕ) (r s : ℝ) : ℂ := (((min r s / max r s) ^ n * wrep M s : ℝ) : ℂ)

theorem minmax_pow_nonneg {n : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 ≤ (min r s / max r s) ^ n :=
  pow_nonneg (minmax_nonneg hr hs) n

theorem minmax_pow_le_one {n : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (min r s / max r s) ^ n ≤ 1 :=
  pow_le_one₀ (minmax_nonneg hr hs) (div_le_one_of_le₀ min_le_max (lt_max_of_lt_left hr).le)

theorem norm_crep_le {M : ℝ} {n : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ‖crep M n r s‖ ≤ ‖(wrep M s : ℂ)‖ := by
  have hw := wrep_pos M s
  rw [crep, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (minmax_pow_nonneg hr hs) hw.le), Real.norm_of_nonneg hw.le]
  calc (min r s / max r s) ^ n * wrep M s ≤ 1 * wrep M s := by
        gcongr
        exact minmax_pow_le_one hr hs
    _ = wrep M s := one_mul _

theorem continuous_crep (M : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) : Continuous (crep M n r) :=
  Complex.continuous_ofReal.comp ((continuous_minmax_pow hr n).mul (continuous_wrep M))

theorem memLp_crep {M : ℝ} (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    MemLp (crep M n r) 2 (profileMeasure M) := by
  refine (memLp_wrep hM).of_le (continuous_crep M n hr).aestronglyMeasurable ?_
  filter_upwards [ae_profile_pos M] with s hs
  exact norm_crep_le hr hs

/-- `crep_{n,r}` as an element of `ProfL2 M`. -/
def crepLp {M : ℝ} (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r) : ProfL2 M :=
  (memLp_crep hM n hr).toLp _

theorem norm_crepLp_le {M : ℝ} (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖crepLp hM n hr‖ ≤ ‖wrepLp hM‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(memLp_crep hM n hr).coeFn_toLp, coeFn_wrepLp hM, ae_profile_pos M]
    with s h1 h2 hs
  rw [crepLp, h1, h2]
  exact norm_crep_le hr hs

/-- **Representer identity**: `∫₀^∞ (min(r,ρ)/max(r,ρ))ⁿ w(ρ) ρ dρ = ⟪crep_{n,r}, w⟫`. -/
theorem integral_minmax_eq_inner {M : ℝ} (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r)
    (w : ProfL2 M) :
    ∫ ρ in Ioi (0 : ℝ), (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * w ρ * ρ =
      ⟪crepLp hM n hr, w⟫_ℂ := by
  rw [L2.inner_def]
  have h1 : ∫ s, ⟪(crepLp hM n hr : ℝ → ℂ) s, w s⟫_ℂ ∂profileMeasure M =
      ∫ s, crep M n r s * w s ∂profileMeasure M := by
    apply integral_congr_ae
    filter_upwards [(memLp_crep hM n hr).coeFn_toLp] with s hs
    rw [crepLp, hs, RCLike.inner_apply', crep, Complex.conj_ofReal]
  rw [h1, integral_profileMeasure M (fun s => crep M n r s * w s)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  have hP : 0 < (1 + s ^ 2) ^ M := Real.rpow_pos_of_pos (by positivity) M
  have hP' : (((1 + s ^ 2) ^ M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hP.ne'
  have hpi : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  simp only [crep, wrep]
  push_cast
  field_simp

/-- **`greenN` as a pairing**: `greenN n w r = -(2n)⁻¹ ⟪crep_{n,r}, w⟫` for `r > 0`. -/
theorem greenN_eq_inner {M : ℝ} (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r) (w : ProfL2 M) :
    greenN n w r = -(((2 * n : ℝ)⁻¹ : ℝ) : ℂ) * ⟪crepLp hM n hr, w⟫_ℂ := by
  rw [greenN, integral_minmax_eq_inner hM n hr w]

/-- **Uniform Green bound** on `ProfL2 M`: `|greenN n w r| ≤ (2n)⁻¹ ‖wrep‖ ‖w‖` for every `r > 0`
(a uniform form of the bounds of `eq:st18-t00060`, tex lines 1374–1379). -/
theorem norm_greenN_le_wrep {M : ℝ} (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r) (w : ProfL2 M) :
    ‖greenN n w r‖ ≤ (2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖ := by
  rw [greenN_eq_inner hM n hr w, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), mul_assoc]
  gcongr
  exact (norm_inner_le_norm _ _).trans (by gcongr; exact norm_crepLp_le hM n hr)

/-- `greenN n w` is continuous on `(0, ∞)` for `w ∈ ProfL2 M`, `M > 1`. -/
theorem continuousOn_greenN {M : ℝ} (hM : 1 < M) (n : ℕ) (w : ProfL2 M) :
    ContinuousOn (greenN n w) (Ioi 0) := by
  have hw := (memL2M_of_memLp (Lp.memLp w)).wprof hM
  have h := ((hw.continuousOn_Psi n).mono Ioi_subset_Ici_self).const_smul (-(1 / (2 * (n : ℂ))))
  refine h.congr fun r _ => ?_
  rw [greenN_eq_Psi]
  rfl

theorem aestronglyMeasurable_greenN {M : ℝ} (hM : 1 < M) (n : ℕ) (w : ProfL2 M) :
    AEStronglyMeasurable (greenN n w) (profileMeasure M) :=
  (aestronglyMeasurable_profileMeasure_iff M).2
    ((continuousOn_greenN hM n w).aestronglyMeasurable measurableSet_Ioi)

/-- `greenN` is additive and homogeneous in its profile, for `ProfL2 M` arguments. -/
theorem greenN_congr {M : ℝ} (n : ℕ) {f g : ℝ → ℂ} (h : f =ᵐ[profileMeasure M] g) (r : ℝ) :
    greenN n f r = greenN n g r := by
  rw [greenN, greenN]
  congr 1
  refine integral_congr_ae ?_
  have h' : f =ᵐ[volume.restrict (Ioi 0)] g := (ac_profileMeasure M).ae_le h
  filter_upwards [h'] with s hs
  rw [hs]

theorem greenN_add {M : ℝ} (hM : 1 < M) (n : ℕ) (f g : ProfL2 M) {r : ℝ} (hr : 0 < r) :
    greenN n (⇑(f + g)) r = greenN n f r + greenN n g r := by
  rw [greenN_eq_inner hM n hr, greenN_eq_inner hM n hr, greenN_eq_inner hM n hr, inner_add_right]
  ring

theorem greenN_smul {M : ℝ} (hM : 1 < M) (n : ℕ) (c : ℂ) (f : ProfL2 M) {r : ℝ} (hr : 0 < r) :
    greenN n (⇑(c • f)) r = c * greenN n f r := by
  rw [greenN_eq_inner hM n hr, greenN_eq_inner hM n hr, inner_smul_right]
  ring

/-! ### The sector coupling -/

/-- The coefficient `i n k(r)` of the sector-`n` coupling. -/
def cplCoeff (n : ℤ) (r : ℝ) : ℂ := Complex.I * (n : ℂ) * (radialK r : ℂ)

theorem norm_cplCoeff (n : ℤ) (r : ℝ) : ‖cplCoeff n r‖ = |(n : ℝ)| * |radialK r| := by
  rw [cplCoeff, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_intCast]

/-- The bound constant `½ ‖wrep‖` of the coupling, uniform in `n`. -/
def cplConst {M : ℝ} (hM : 1 < M) : ℝ := 1 / 2 * ‖wrepLp hM‖

theorem cplConst_nonneg {M : ℝ} (hM : 1 < M) : 0 ≤ cplConst hM := by
  unfold cplConst; positivity

/-- Pointwise: `|i n k(r) greenN |n| w r| ≤ ½ ‖wrep‖ ‖w‖ |k(r)|`, uniformly in `n`. -/
theorem norm_cpl_le {M : ℝ} (hM : 1 < M) (n : ℤ) {r : ℝ} (hr : 0 < r) (w : ProfL2 M) :
    ‖cplCoeff n r * greenN n.natAbs w r‖ ≤ cplConst hM * ‖w‖ * |radialK r| := by
  rw [norm_mul, norm_cplCoeff]
  have hg := norm_greenN_le_wrep hM n.natAbs hr w
  have hn : |(n : ℝ)| = (n.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hn]
  rcases Nat.eq_zero_or_pos n.natAbs with h0 | hpos
  · rw [h0, Nat.cast_zero, zero_mul, zero_mul]
    have := cplConst_nonneg hM
    positivity
  · have hpos' : (0 : ℝ) < n.natAbs := by exact_mod_cast hpos
    calc (n.natAbs : ℝ) * |radialK r| * ‖greenN n.natAbs w r‖
        ≤ (n.natAbs : ℝ) * |radialK r| * ((2 * n.natAbs : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖) := by
          gcongr
      _ = cplConst hM * ‖w‖ * |radialK r| := by
          unfold cplConst
          field_simp

theorem memLp_cpl {M : ℝ} (hM : 1 < M) (n : ℤ) (w : ProfL2 M) :
    MemLp (fun r => cplCoeff n r * greenN n.natAbs w r) 2 (profileMeasure M) := by
  have hc : Continuous (cplCoeff n) := by
    unfold cplCoeff
    exact continuous_const.mul (Complex.continuous_ofReal.comp B0012.continuous_radialK)
  refine ((memLp_radialK_profile M).const_smul
      (((cplConst hM * ‖w‖ : ℝ)) : ℂ)).of_le
    (hc.aestronglyMeasurable.mul (aestronglyMeasurable_greenN hM n.natAbs w)) ?_
  filter_upwards [ae_profile_pos M] with r hr
  have hC : 0 ≤ cplConst hM * ‖w‖ := mul_nonneg (cplConst_nonneg hM) (norm_nonneg _)
  refine (norm_cpl_le hM n hr w).trans (le_of_eq ?_)
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hC,
    Complex.norm_real, Real.norm_eq_abs]

/-- The sector coupling as a linear map of `ProfL2 M`. -/
def couplingLin {M : ℝ} (hM : 1 < M) (n : ℤ) : ProfL2 M →ₗ[ℂ] ProfL2 M where
  toFun w := (memLp_cpl hM n w).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [ae_profile_pos M] with r hr
    simp only [Pi.add_apply]
    rw [greenN_add hM n.natAbs f g hr]
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [ae_profile_pos M] with r hr
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [greenN_smul hM n.natAbs c f hr]
    ring

theorem norm_couplingLin_le {M : ℝ} (hM : 1 < M) (n : ℤ) (w : ProfL2 M) :
    ‖couplingLin hM n w‖ ≤ cplConst hM * ‖kProf M‖ * ‖w‖ := by
  set c : ℂ := ((cplConst hM * ‖w‖ : ℝ) : ℂ) with hc
  have hC : 0 ≤ cplConst hM * ‖w‖ := mul_nonneg (cplConst_nonneg hM) (norm_nonneg _)
  have h : ‖couplingLin hM n w‖ ≤ ‖c • kProf M‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(memLp_cpl hM n w).coeFn_toLp, Lp.coeFn_smul c (kProf M), coeFn_kProf M,
      ae_profile_pos M] with r h1 h2 h3 hr
    show ‖((memLp_cpl hM n w).toLp _ : ProfL2 M) r‖ ≤ _
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
    refine (norm_cpl_le hM n hr w).trans (le_of_eq ?_)
    rw [norm_mul, hc, Complex.norm_real, Real.norm_of_nonneg hC, Complex.norm_real,
      Real.norm_eq_abs]
  rw [norm_smul, hc, Complex.norm_real, Real.norm_of_nonneg hC] at h
  calc ‖couplingLin hM n w‖ ≤ cplConst hM * ‖w‖ * ‖kProf M‖ := h
    _ = cplConst hM * ‖kProf M‖ * ‖w‖ := by ring

/-- **P6.** The sector-`n` coupling `w ↦ i n k(r) Δ_{|n|}⁻¹ w (r)` on `ProfL2 M`, i.e.
`-(Kf)·∇E₀` on `f = w(r)e^{inϑ}` (`paper/main.tex` lines 662–670 and 1366–1379). Its kernel
relative to `s ds` is `-(i sgn(n)/2) k(r) (min(r,s)/max(r,s))^{|n|}`. -/
def couplingSec {M : ℝ} (hM : 1 < M) (n : ℤ) : ProfL2 M →L[ℂ] ProfL2 M :=
  (couplingLin hM n).mkContinuous (cplConst hM * ‖kProf M‖) (norm_couplingLin_le hM n)

theorem coeFn_couplingSec {M : ℝ} (hM : 1 < M) (n : ℤ) (w : ProfL2 M) :
    ⇑(couplingSec hM n w) =ᵐ[profileMeasure M]
      fun r => Complex.I * (n : ℂ) * (radialK r : ℂ) * greenN n.natAbs w r :=
  (memLp_cpl hM n w).coeFn_toLp

/-- The coupling is bounded uniformly in the sector: `‖couplingSec hM n‖ ≤ ½ ‖wrep‖ ‖k‖`. -/
theorem norm_couplingSec_le {M : ℝ} (hM : 1 < M) (n : ℤ) :
    ‖couplingSec hM n‖ ≤ cplConst hM * ‖kProf M‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (cplConst_nonneg hM) (norm_nonneg _)) _

/-- Sector `0` has no coupling: radial vorticity has tangential velocity (`paper/main.tex`
line 1356, unit `B0078`(i)). -/
theorem couplingSec_zero {M : ℝ} (hM : 1 < M) : couplingSec hM 0 = 0 := by
  ext1 w
  rw [ContinuousLinearMap.zero_apply]
  apply Lp.ext
  filter_upwards [coeFn_couplingSec hM 0 w, Lp.coeFn_zero ℂ 2 (profileMeasure M)] with r h1 h2
  rw [h1, h2]
  simp

/-- Conjugate sectors: `couplingSec hM (-n) = -couplingSec hM n`. -/
theorem couplingSec_neg {M : ℝ} (hM : 1 < M) (n : ℤ) :
    couplingSec hM (-n) = -couplingSec hM n := by
  ext1 w
  apply Lp.ext
  filter_upwards [coeFn_couplingSec hM (-n) w, coeFn_couplingSec hM n w,
    Lp.coeFn_neg (couplingSec hM n w)] with r h1 h2 h3
  rw [h1, ContinuousLinearMap.neg_apply, h3, Pi.neg_apply, h2, Int.natAbs_neg]
  push_cast
  ring

/-! ### Compactness -/

/-- **P6, compactness** (`paper/main.tex` lines 1206–1222 at `j = 0`, via sector kernels; the
manuscript's Hilbert–Schmidt argument is replaced by weakly null sequences as in
`isCompactOperator_kR`). -/
theorem isCompactOperator_couplingSec {M : ℝ} (hM : 1 < M) (n : ℤ) :
    IsCompactOperator (couplingSec hM n) := by
  refine Infra.WeaklyNullCompact.isCompactOperator_of_forall_weaklyNull_of_norm_le_one _
    fun x hx hw => ?_
  set C : ℝ := cplConst hM with hC
  set F : ℕ → ℝ → ℝ := fun j r => ‖cplCoeff n r * greenN n.natAbs (x j) r‖ ^ 2 with hF
  have hsq : ∀ j, ‖couplingSec hM n (x j)‖ ^ 2 = ∫ r, F j r ∂profileMeasure M := by
    intro j
    rw [norm_sq_Lp_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_couplingSec hM n (x j)] with r hr
    rw [hr]
    simp only [hF, cplCoeff]
  have hk2 : Integrable (fun r => ‖(radialK r : ℂ)‖ ^ 2) (profileMeasure M) :=
    (memLp_two_iff_integrable_sq_norm (memLp_radialK_profile M).1).1 (memLp_radialK_profile M)
  have hlim : Tendsto (fun j => ∫ r, F j r ∂profileMeasure M) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := profileMeasure M) (F := F)
      (f := fun _ => (0 : ℝ)) (fun r => C ^ 2 * ‖(radialK r : ℂ)‖ ^ 2) ?_ (hk2.const_mul _) ?_ ?_
    · simpa using h
    · intro j
      have hc : Continuous (cplCoeff n) := by
        unfold cplCoeff
        exact continuous_const.mul (Complex.continuous_ofReal.comp B0012.continuous_radialK)
      exact ((hc.aestronglyMeasurable.mul
        (aestronglyMeasurable_greenN hM n.natAbs (x j))).norm.pow 2)
    · intro j
      filter_upwards [ae_profile_pos M] with r hr
      have hb := norm_cpl_le hM n hr (x j)
      have hb' : ‖cplCoeff n r * greenN n.natAbs (x j) r‖ ≤ C * |radialK r| := by
        calc _ ≤ cplConst hM * ‖x j‖ * |radialK r| := hb
          _ ≤ cplConst hM * 1 * |radialK r| := by
              gcongr
              · exact cplConst_nonneg hM
              · exact hx j
          _ = C * |radialK r| := by rw [mul_one]
      have hnn : 0 ≤ F j r := by simp only [hF]; positivity
      rw [Real.norm_of_nonneg hnn]
      simp only [hF]
      rw [Complex.norm_real, Real.norm_eq_abs, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hb' 2
    · filter_upwards [ae_profile_pos M] with r hr
      have h0 : Tendsto (fun j => greenN n.natAbs (x j) r) atTop (𝓝 0) := by
        have := (hw (crepLp hM n.natAbs hr)).const_mul (-(((2 * n.natAbs : ℝ)⁻¹ : ℝ) : ℂ))
        rw [mul_zero] at this
        exact this.congr fun j => (greenN_eq_inner hM n.natAbs hr (x j)).symm
      have h1 := ((h0.const_mul (cplCoeff n r)).norm.pow 2)
      simpa [hF] using h1
  have h2 : Tendsto (fun j => ‖couplingSec hM n (x j)‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hsq]
    exact hlim
  have h3 := ((Real.continuous_sqrt.tendsto 0).comp h2)
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at h3
  exact h3

end UnforcedLeray.Planar
