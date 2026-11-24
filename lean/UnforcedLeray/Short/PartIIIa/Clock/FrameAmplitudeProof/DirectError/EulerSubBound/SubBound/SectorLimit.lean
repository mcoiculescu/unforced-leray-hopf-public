import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad.Curl
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamQ
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi
import UnforcedLeray.Lib.PlanarSectorsB.BiotSavartSector
import UnforcedLeray.Lib.PlanarSectorsB.SectorSum
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Sector identity for the planar Biot-Savart velocity of a non-compact profile (helper for `PartIII-a:T21/c5/2/2/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 662-670,
788-803, 841-889 (the sector form of `K q`, `K q = ∇^⊥Ψ` with `Ψ = Δ_m⁻¹ q`).

For a sector function `q = φ(|y|)(y/|y|)^m`, `m ≠ 0`, with `φ` smooth on `(0,∞)`, `q` continuous,
bounded and integrable, and `r φ ∈ L¹(0,∞)`, the planar Biot-Savart velocity satisfies
`y · (K q)(y) = -i m Ψ(y)`, `Ψ = greenN |m| φ (|y|) (y/|y|)^m` (`dot_biotSavart_ofProfile_lim`).
For compactly supported profiles in `(0,∞)` this is `K q = ∇^⊥Ψ` (`PartI.biotSavart_eq_perpGrad`,
`PartI.secStreamQ`, `PartI.secStreamPsi`) and the rotation law of `Ψ`
(`Planar.fderiv_sector_rot`); the general case follows by truncating `φ` with smooth cutoffs
`χ_N → 1` and dominated convergence on both sides.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace PlanarDualSub

open UnforcedLeray UnforcedLeray.Planar.NUE

/-! ## 1. Smooth cutoffs `χ_N` with `χ_N = 1` on `[1/M, M]`, `M = N + 2` -/

/-- `M = N + 2`. -/
def cutM (N : ℕ) : ℝ := (N : ℝ) + 2

lemma cutM_pos (N : ℕ) : 0 < cutM N := by unfold cutM; positivity

lemma two_le_cutM (N : ℕ) : 2 ≤ cutM N := by
  unfold cutM; have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith

lemma inv_cutM_le (N : ℕ) : 1 / cutM N ≤ 1 / 2 := by
  rw [div_le_div_iff₀ (cutM_pos N) (by norm_num)]; linarith [two_le_cutM N]

/-- The bump with `χ_N = 1` on `[1/M, M]` and support `(1/(2M), M + 1/(2M))`. -/
def cutBump (N : ℕ) : ContDiffBump ((1 / cutM N + cutM N) / 2) where
  rIn := (cutM N - 1 / cutM N) / 2
  rOut := (cutM N - 1 / cutM N) / 2 + 1 / (2 * cutM N)
  rIn_pos := by linarith [two_le_cutM N, inv_cutM_le N]
  rIn_lt_rOut := by
    have : 0 < 1 / (2 * cutM N) := by have := cutM_pos N; positivity
    linarith

/-- The cutoff `χ_N`. -/
def cutoff (N : ℕ) (r : ℝ) : ℝ := cutBump N r

lemma cutoff_contDiff (N : ℕ) : ContDiff ℝ ∞ (cutoff N) := (cutBump N).contDiff

lemma cutoff_nonneg (N : ℕ) (r : ℝ) : 0 ≤ cutoff N r := (cutBump N).nonneg

lemma cutoff_le_one (N : ℕ) (r : ℝ) : cutoff N r ≤ 1 := (cutBump N).le_one

lemma cutoff_tsupport (N : ℕ) : tsupport (cutoff N) ⊆ Ioi 0 := by
  intro x hx
  have hx' : x ∈ Metric.closedBall ((1 / cutM N + cutM N) / 2) (cutBump N).rOut := by
    rw [← (cutBump N).tsupport_eq]; exact hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx'
  have h1 := (abs_le.1 hx').1
  have hM := cutM_pos N
  have hr : (cutBump N).rOut = (cutM N - 1 / cutM N) / 2 + 1 / (2 * cutM N) := rfl
  rw [hr] at h1
  have : 0 < 1 / (2 * cutM N) := by positivity
  have e : 1 / (2 * cutM N) = (1 / cutM N) / 2 := by field_simp
  show 0 < x
  linarith

lemma cutoff_hasCompactSupport (N : ℕ) : HasCompactSupport (cutoff N) :=
  (cutBump N).hasCompactSupport

lemma cutoff_eventually_one {r : ℝ} (hr : 0 < r) : ∀ᶠ N : ℕ in atTop, cutoff N r = 1 := by
  refine eventually_atTop.2 ⟨⌈r⌉₊ + ⌈1 / r⌉₊, fun N hN => ?_⟩
  have hN' : ((⌈r⌉₊ + ⌈1 / r⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at hN'
  have h1 : r ≤ ⌈r⌉₊ := Nat.le_ceil r
  have h2 : 1 / r ≤ ⌈1 / r⌉₊ := Nat.le_ceil (1 / r)
  have h3 : (0 : ℝ) ≤ ⌈r⌉₊ := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ⌈1 / r⌉₊ := Nat.cast_nonneg _
  have hM : r ≤ cutM N := by unfold cutM; linarith
  have hM' : 1 / r ≤ cutM N := by unfold cutM; linarith
  have hMpos := cutM_pos N
  have hinv : 1 / cutM N ≤ r := by
    rw [div_le_iff₀ hMpos]; rw [div_le_iff₀ hr] at hM'; linarith
  apply (cutBump N).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  have hr' : (cutBump N).rIn = (cutM N - 1 / cutM N) / 2 := rfl
  rw [hr']
  constructor <;> linarith

lemma tendsto_cutoff {r : ℝ} (hr : 0 < r) :
    Tendsto (fun N : ℕ => (cutoff N r : ℂ)) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((cutoff_eventually_one hr).mono fun N h => by simp [h])

lemma cutoff_zero (N : ℕ) : cutoff N 0 = 0 := by
  by_contra hne
  have : (0 : ℝ) ∈ tsupport (cutoff N) := subset_tsupport _ hne
  exact lt_irrefl (0 : ℝ) (mem_Ioi.1 (cutoff_tsupport N this))

/-! ## 2. Truncated profiles -/

/-- The truncated profile `χ_N φ`. -/
def truncProf (φ : ℝ → ℂ) (N : ℕ) (r : ℝ) : ℂ := (cutoff N r : ℂ) * φ r

lemma cutoffC_contDiff (N : ℕ) : ContDiff ℝ ∞ (fun r => (cutoff N r : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (cutoff_contDiff N)

lemma cutoffC_tsupport (N : ℕ) : tsupport (fun r => (cutoff N r : ℂ)) ⊆ Ioi 0 :=
  (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero (cutoff N)).trans
    (cutoff_tsupport N)

theorem smoothCpt_truncProf {φ : ℝ → ℂ} (hs : ContDiffOn ℝ ∞ φ (Ioi 0)) (N : ℕ) :
    PartI.SmoothCptFun (truncProf φ N) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro r
    by_cases hr : 0 < r
    · exact (cutoffC_contDiff N).contDiffAt.mul (hs.contDiffAt (Ioi_mem_nhds hr))
    · have hnot : r ∉ tsupport (fun r => (cutoff N r : ℂ)) := fun h => hr (cutoffC_tsupport N h)
      have hev := notMem_tsupport_iff_eventuallyEq.1 hnot
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with x hx
      simp only [truncProf]
      rw [show ((cutoff N x : ℝ) : ℂ) = 0 from hx, zero_mul]
  · exact ((cutoff_hasCompactSupport N).comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).mul_right
  · exact tsupport_mul_subset_left.trans (cutoffC_tsupport N)

lemma ofProfile_truncProf (m : ℤ) (φ : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    Ang.ofProfile m (truncProf φ N) z = (cutoff N ‖z‖ : ℂ) * Ang.ofProfile m φ z := by
  simp only [Ang.ofProfile, truncProf]; ring

lemma norm_ofProfile_truncProf_le (m : ℤ) (φ : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    ‖Ang.ofProfile m (truncProf φ N) z‖ ≤ ‖Ang.ofProfile m φ z‖ := by
  rw [ofProfile_truncProf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (cutoff_nonneg _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)

lemma ofProfile_zero_point {m : ℤ} (hm : m ≠ 0) (φ : ℝ → ℂ) : Ang.ofProfile m φ 0 = 0 := by
  simp [Ang.ofProfile, Ang.angPhase, zero_zpow m hm]

lemma tendsto_ofProfile_truncProf {m : ℤ} (hm : m ≠ 0) (φ : ℝ → ℂ) (z : ℂ) :
    Tendsto (fun N => Ang.ofProfile m (truncProf φ N) z) atTop (𝓝 (Ang.ofProfile m φ z)) := by
  by_cases hz : z = 0
  · subst hz
    simp only [ofProfile_zero_point hm]
    exact tendsto_const_nhds
  · simp only [ofProfile_truncProf]
    have := (tendsto_cutoff (norm_pos_iff.2 hz)).mul_const (Ang.ofProfile m φ z)
    simpa using this

/-! ## 3. The identity for compactly supported profiles: `y·(Kq) = -i m Ψ` -/

theorem dot_biotSavart_ofProfile_smoothCpt {m : ℤ} (hm : m ≠ 0) {φ : ℝ → ℂ}
    (hφ : PartI.SmoothCptFun φ) (y : ℂ) :
    (y.re : ℂ) * B0009.biotSavart (Ang.ofProfile m φ) 0 y +
      (y.im : ℂ) * B0009.biotSavart (Ang.ofProfile m φ) 1 y =
      -(Complex.I * m * Ang.ofProfile m (Planar.greenN m.natAbs φ) y) := by
  obtain ⟨hq, hqb⟩ := PartI.secStreamQ m φ hφ
  obtain ⟨hΨ, hlap, hdec⟩ := PartI.secStreamPsi m φ hφ hm
  have hS := PartI.biotSavart_eq_perpGrad hq hqb (Planar.integral_ofProfile_eq_zero hm φ) hΨ
    hlap hdec y
  set Ψ := Ang.ofProfile m (Planar.greenN m.natAbs φ) with hΨdef
  have hd : HasFDerivAt Ψ (fderiv ℝ Ψ y) y :=
    ((hΨ.differentiable (by simp)) y).hasFDerivAt
  have hrot := Planar.fderiv_sector_rot hd (fun θ => Planar.ofProfile_rot m _ θ y)
  have hIy : Complex.I * y = (-y.im) • (1 : ℂ) + y.re • Complex.I := by
    apply Complex.ext <;> simp
  have hL : fderiv ℝ Ψ y (Complex.I * y) =
      -y.im * fderiv ℝ Ψ y 1 + y.re * fderiv ℝ Ψ y Complex.I := by
    rw [hIy, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [hS.1, hS.2]
  linear_combination hL - hrot

/-! ## 4. Dominated convergence on both sides -/

theorem tendsto_biotSavart_trunc {φ : ℝ → ℂ} {m : ℤ} (hm : m ≠ 0)
    (hs : ContDiffOn ℝ ∞ φ (Ioi 0)) (hcont : Continuous (Ang.ofProfile m φ)) {K : ℝ}
    (hK : ∀ z, ‖Ang.ofProfile m φ z‖ ≤ K) (hint : Integrable (Ang.ofProfile m φ))
    (i : Fin 2) (y : ℂ) :
    Tendsto (fun N => B0009.biotSavart (Ang.ofProfile m (truncProf φ N)) i y) atTop
      (𝓝 (B0009.biotSavart (Ang.ofProfile m φ) i y)) := by
  simp only [B0009.biotSavart_apply]
  set g : ℂ → ℂ := fun z => ((‖Ang.ofProfile m φ z‖ : ℝ) : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp hcont.norm
  have hgK : ∀ z, ‖g z‖ ≤ K := by
    intro z; simp only [hg, Complex.norm_real, Real.norm_eq_abs, abs_norm]; exact hK z
  have hgi : Integrable g := hint.norm.ofReal
  have hdom := (PartI.BiotSavartCurlAux.integrable_conv_kernel (i := i) y hgc hgK hgi).norm
  refine tendsto_integral_of_dominated_convergence
    (fun z => ‖B0009.kernel i (y - z) * g z‖) (fun N => ?_) hdom (fun N => ?_) ?_
  · have hqN := (PartI.secStreamQ m (truncProf φ N) (smoothCpt_truncProf hs N)).1
    exact (((B0009.measurable_kernel i).comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hqN.continuous.aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    rw [norm_mul, norm_mul]
    gcongr
    simp only [hg, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact norm_ofProfile_truncProf_le m φ N z
  · exact Eventually.of_forall fun z => (tendsto_ofProfile_truncProf hm φ z).const_mul _

theorem tendsto_greenN_trunc {φ : ℝ → ℂ} (n : ℕ) (hc : ContinuousOn φ (Ioi 0))
    (hi : IntegrableOn (fun ρ => ‖φ ρ‖ * ρ) (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun N => Planar.greenN n (truncProf φ N) r) atTop (𝓝 (Planar.greenN n φ r)) := by
  unfold Planar.greenN
  refine Tendsto.const_mul _ ?_
  have hmm : Continuous (fun ρ : ℝ => ((((min r ρ / max r ρ) ^ n : ℝ)) : ℂ)) := by
    have hden : ∀ ρ : ℝ, max r ρ ≠ 0 := fun ρ => (lt_of_lt_of_le hr (le_max_left r ρ)).ne'
    exact Complex.continuous_ofReal.comp
      (((continuous_const.min continuous_id).div (continuous_const.max continuous_id) hden).pow n)
  have hbd : ∀ ρ : ℝ, 0 < ρ → ‖((((min r ρ / max r ρ) ^ n : ℝ)) : ℂ)‖ ≤ 1 := by
    intro ρ hρ
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hmax : 0 < max r ρ := lt_of_lt_of_le hr (le_max_left r ρ)
    have h0 : 0 ≤ min r ρ / max r ρ := div_nonneg (le_min hr.le hρ.le) hmax.le
    have h1 : min r ρ / max r ρ ≤ 1 := (div_le_one hmax).2 (min_le_max)
    rw [abs_of_nonneg (pow_nonneg h0 n)]
    exact pow_le_one₀ h0 h1
  refine tendsto_integral_of_dominated_convergence (fun ρ => ‖φ ρ‖ * ρ) (fun N => ?_) hi
    (fun N => ?_) ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ((hmm.continuousOn).mul ?_).mul Complex.continuous_ofReal.continuousOn
    exact ((cutoffC_contDiff N).continuous.continuousOn).mul hc
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρ' : (0 : ℝ) < ρ := hρ
    have h1 := hbd ρ hρ'
    have h2 : ‖truncProf φ N ρ‖ ≤ ‖φ ρ‖ := by
      simp only [truncProf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (cutoff_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)
    calc ‖((((min r ρ / max r ρ) ^ n : ℝ)) : ℂ) * truncProf φ N ρ * (ρ : ℂ)‖
        = ‖((((min r ρ / max r ρ) ^ n : ℝ)) : ℂ)‖ * ‖truncProf φ N ρ‖ * ρ := by
          rw [norm_mul, norm_mul, Complex.norm_of_nonneg hρ'.le]
      _ ≤ 1 * ‖φ ρ‖ * ρ := by gcongr
      _ = ‖φ ρ‖ * ρ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρ' : (0 : ℝ) < ρ := hρ
    simp only [truncProf]
    have := ((tendsto_cutoff hρ').mul_const (φ ρ)).const_mul
      ((((min r ρ / max r ρ) ^ n : ℝ)) : ℂ) |>.mul_const (ρ : ℂ)
    simpa [mul_assoc] using this

/-! ## 5. The limit identity -/

/-- **Sector form of `y · K q`** for non-compact profiles: `y·(Kq)(y) = -i m Ψ(y)`. -/
theorem dot_biotSavart_ofProfile_lim {φ : ℝ → ℂ} {m : ℤ} (hm : m ≠ 0)
    (hs : ContDiffOn ℝ ∞ φ (Ioi 0)) (hcont : Continuous (Ang.ofProfile m φ)) {K : ℝ}
    (hK : ∀ z, ‖Ang.ofProfile m φ z‖ ≤ K) (hint : Integrable (Ang.ofProfile m φ))
    (hi : IntegrableOn (fun ρ => ‖φ ρ‖ * ρ) (Ioi 0)) (y : ℂ) :
    (y.re : ℂ) * B0009.biotSavart (Ang.ofProfile m φ) 0 y +
      (y.im : ℂ) * B0009.biotSavart (Ang.ofProfile m φ) 1 y =
      -(Complex.I * m * Ang.ofProfile m (Planar.greenN m.natAbs φ) y) := by
  have hL : Tendsto (fun N =>
      (y.re : ℂ) * B0009.biotSavart (Ang.ofProfile m (truncProf φ N)) 0 y +
        (y.im : ℂ) * B0009.biotSavart (Ang.ofProfile m (truncProf φ N)) 1 y) atTop
      (𝓝 ((y.re : ℂ) * B0009.biotSavart (Ang.ofProfile m φ) 0 y +
        (y.im : ℂ) * B0009.biotSavart (Ang.ofProfile m φ) 1 y)) :=
    ((tendsto_biotSavart_trunc hm hs hcont hK hint 0 y).const_mul _).add
      ((tendsto_biotSavart_trunc hm hs hcont hK hint 1 y).const_mul _)
  have hR : Tendsto (fun N =>
      -(Complex.I * m * Ang.ofProfile m (Planar.greenN m.natAbs (truncProf φ N)) y)) atTop
      (𝓝 (-(Complex.I * m * Ang.ofProfile m (Planar.greenN m.natAbs φ) y))) := by
    refine (Tendsto.const_mul _ ?_).neg
    by_cases hy : y = 0
    · subst hy
      simp only [ofProfile_zero_point hm]
      exact tendsto_const_nhds
    · simp only [Ang.ofProfile]
      exact (tendsto_greenN_trunc _ hs.continuousOn hi (norm_pos_iff.2 hy)).mul_const _
  have heq : (fun N =>
      (y.re : ℂ) * B0009.biotSavart (Ang.ofProfile m (truncProf φ N)) 0 y +
        (y.im : ℂ) * B0009.biotSavart (Ang.ofProfile m (truncProf φ N)) 1 y) =
      (fun N => -(Complex.I * m * Ang.ofProfile m (Planar.greenN m.natAbs (truncProf φ N)) y)) :=
    funext fun N => dot_biotSavart_ofProfile_smoothCpt hm (smoothCpt_truncProf hs N) y
  rw [heq] at hL
  exact tendsto_nhds_unique hL hR

/-! ## 6. Conjugate sectors -/

theorem ofProfile_neg_eq_conj (m : ℤ) (g : ℝ → ℂ) (z : ℂ) :
    Ang.ofProfile (-m) g z = Ang.ofProfile m g (conj z) := by
  unfold Ang.ofProfile Ang.angPhase
  rw [Complex.norm_conj]
  by_cases hz : z = 0
  · subst hz
    by_cases hm : m = 0
    · subst hm; simp
    · simp [zero_zpow m hm, zero_zpow (-m) (neg_ne_zero.2 hm)]
  · congr 1
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    have hu : conj z / (‖z‖ : ℂ) = (z / (‖z‖ : ℂ))⁻¹ := by
      rw [inv_div, div_eq_div_iff hn hz, Complex.conj_mul']
      ring
    rw [hu, inv_zpow']

end PlanarDualSub

end UnforcedLeray.Short.IIIa
