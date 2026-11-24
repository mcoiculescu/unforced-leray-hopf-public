import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22_2_2
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.ProfContDiff
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.ProfOde
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Part III-a, task `PartIII-a:T22/2/2/1`: unconditional canonical solution representation

Source of record: `the November 2 reference manuscript` (SP), lines 1076-1150 and
3129-3215 (`Blueprint.Planar.IsCanonicalBranch` to `PartI.IsCanonicalSolution` bridge).

Given any `P : Blueprint.Planar.PlanarData` satisfying `Blueprint.Planar.IsPlanarReference P`:
1. The `X_G`-lift `U θ = toLp (P.canonical θ)` (`θ > 0`) is continuous on `(0, ∞)` by
   `hP.canonical.xg_continuous`.
2. Pairing the pointwise canonical equation `hP.canonical.equation` against smooth compactly
   supported radial cutoffs `ψ_k` of each oscillator eigenmode `B0094.oscBasis n` on `(0, ∞)`,
   integrating by parts via `Spine.DClassicalAux.interval_ibp`, differentiating under the compact
   spatial integral, integrating with `v^{-n}` over `[θ, θ']`, and passing `k → ∞` yields the
   `oscBasis n` Duhamel identity, hence `Spine.IsMildOnPos U` by `S_mild_interval` and
   `backward_gronwall`.
3. `Spine.mildIsStrong`, `Spine.mildSpatialSmoothing`, and `Spine.strongBootstrap` (with
   `PartI.greenEllipticRegularity`) upgrade `U` to `PartI.IsCanonicalSolution U`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Polynomial UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.IIIa.T22Sub

namespace CanonicalSolutionRepAux

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123
open UnforcedLeray.Cons.G3b UnforcedLeray.Short.Spine
open UnforcedLeray.Short.Spine.DClassicalAux UnforcedLeray.Short.Spine.CanonicalMild

/-! ### 1. Continuous `X_G` lift of `P.canonical` -/

private def canonicalCurve (P : PlanarData) (hP : IsPlanarReference P) (θ : ℝ) : XG :=
  if hθ : 0 < θ then
    (memLp_of_memXG (hP.canonical.memXG θ hθ)).toLp (P.canonical θ)
  else 0

private theorem canonicalCurve_eq_pos (P : PlanarData) (hP : IsPlanarReference P)
    {θ : ℝ} (hθ : 0 < θ) :
    canonicalCurve P hP θ =
      (memLp_of_memXG (hP.canonical.memXG θ hθ)).toLp (P.canonical θ) := by
  simp [canonicalCurve, hθ]

private theorem canonical_ae_canonicalCurve (P : PlanarData) (hP : IsPlanarReference P)
    (θ : ℝ) (hθ : 0 < θ) :
    P.canonical θ =ᵐ[xGMeasure] (canonicalCurve P hP θ : ℝ → ℂ) := by
  rw [canonicalCurve_eq_pos P hP hθ]
  exact (memLp_of_memXG (hP.canonical.memXG θ hθ)).coeFn_toLp.symm

private theorem continuousOn_canonicalCurve (P : PlanarData) (hP : IsPlanarReference P) :
    ContinuousOn (canonicalCurve P hP) (Ioi 0) := by
  intro θ₀ hθ₀
  apply ContinuousAt.continuousWithinAt
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hθ₀' : 0 < θ₀ := hθ₀
  refine (hP.canonical.xg_continuous θ₀ hθ₀').congr' ?_
  filter_upwards [Ioi_mem_nhds hθ₀'] with θ hθ
  have hθ' : 0 < θ := hθ
  have hae : (fun r => P.canonical θ r - P.canonical θ₀ r) =ᵐ[xGMeasure]
      (⇑(canonicalCurve P hP θ - canonicalCurve P hP θ₀) : ℝ → ℂ) := by
    filter_upwards [canonical_ae_canonicalCurve P hP θ hθ',
      canonical_ae_canonicalCurve P hP θ₀ hθ₀',
      Lp.coeFn_sub (canonicalCurve P hP θ) (canonicalCurve P hP θ₀)] with r h1 h2 hsub
    rw [h1, h2]
    exact hsub.symm
  exact gaussianNorm_eq_norm hae

/-! ### 2. Smooth radial cutoffs on `(0, ∞)` -/

private def sigmaCut (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

private theorem sigmaCut_contDiff : ContDiff ℝ ∞ sigmaCut :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

private theorem sigmaCut_zero_of_le {t : ℝ} (ht : t ≤ 1) : sigmaCut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem sigmaCut_one_of_ge {t : ℝ} (ht : 2 ≤ t) : sigmaCut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem sigmaCut_nonneg (t : ℝ) : 0 ≤ sigmaCut t :=
  Real.smoothTransition.nonneg _

private theorem sigmaCut_le_one (t : ℝ) : sigmaCut t ≤ 1 :=
  Real.smoothTransition.le_one _

private theorem sigmaCut_deriv_bounds :
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
      (∀ t : ℝ, |deriv sigmaCut t| ≤ M₁) ∧
      (∀ t : ℝ, |deriv (deriv sigmaCut) t| ≤ M₂) := by
  have hd1 : ContDiff ℝ ∞ (deriv sigmaCut) := (contDiff_infty_iff_deriv.mp sigmaCut_contDiff).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv sigmaCut)) := (contDiff_infty_iff_deriv.mp hd1).2
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hd1.continuous.continuousOn : ContinuousOn (deriv sigmaCut) (Icc 1 2))
  obtain ⟨B₂, hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hd2.continuous.continuousOn : ContinuousOn (deriv (deriv sigmaCut)) (Icc 1 2))
  refine ⟨max B₁ 0, max B₂ 0, le_max_right _ _, le_max_right _ _, fun t => ?_, fun t => ?_⟩
  · by_cases ht : t ∈ Icc (1 : ℝ) 2
    · exact (Real.norm_eq_abs _ ▸ hB₁ t ht).trans (le_max_left _ _)
    · have hz : deriv sigmaCut t = 0 := by
        rcases lt_or_ge t 1 with hlt | hge
        · have hev : sigmaCut =ᶠ[𝓝 t] fun _ => 0 := by
            filter_upwards [Iio_mem_nhds hlt] with s hs
            exact sigmaCut_zero_of_le (le_of_lt hs)
          rw [hev.deriv_eq, deriv_const]
        · have hgt : 2 < t := by
            by_contra hle
            exact ht ⟨hge, not_lt.mp hle⟩
          have hev : sigmaCut =ᶠ[𝓝 t] fun _ => 1 := by
            filter_upwards [Ioi_mem_nhds hgt] with s hs
            exact sigmaCut_one_of_ge (le_of_lt hs)
          rw [hev.deriv_eq, deriv_const]
      rw [hz, abs_zero]
      exact le_max_right _ _
  · by_cases ht : t ∈ Icc (1 : ℝ) 2
    · exact (Real.norm_eq_abs _ ▸ hB₂ t ht).trans (le_max_left _ _)
    · have hz : deriv (deriv sigmaCut) t = 0 := by
        rcases lt_or_ge t 1 with hlt | hge
        · have hev : sigmaCut =ᶠ[𝓝 t] fun _ => 0 := by
            filter_upwards [Iio_mem_nhds hlt] with s hs
            exact sigmaCut_zero_of_le (le_of_lt hs)
          simp [hev.deriv.deriv_eq]
        · have hgt : 2 < t := by
            by_contra hle
            exact ht ⟨hge, not_lt.mp hle⟩
          have hev : sigmaCut =ᶠ[𝓝 t] fun _ => 1 := by
            filter_upwards [Ioi_mem_nhds hgt] with s hs
            exact sigmaCut_one_of_ge (le_of_lt hs)
          simp [hev.deriv.deriv_eq]
      rw [hz, abs_zero]
      exact le_max_right _ _

private def cutScale (k : ℕ) : ℝ := (k : ℝ) + 3

private theorem three_le_cutScale (k : ℕ) : (3 : ℝ) ≤ cutScale k := by
  unfold cutScale
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

private theorem cutScale_pos (k : ℕ) : 0 < cutScale k :=
  lt_of_lt_of_le (by norm_num) (three_le_cutScale k)

private def etaCut (k : ℕ) (r : ℝ) : ℝ :=
  sigmaCut (cutScale k * r) * (1 - sigmaCut (r / cutScale k))

private theorem etaCut_contDiff (k : ℕ) : ContDiff ℝ ∞ (etaCut k) := by
  unfold etaCut
  exact (sigmaCut_contDiff.comp (contDiff_const.mul contDiff_id)).mul
    (contDiff_const.sub (sigmaCut_contDiff.comp (contDiff_id.div_const _)))

private theorem etaCut_nonneg (k : ℕ) (r : ℝ) : 0 ≤ etaCut k r :=
  mul_nonneg (sigmaCut_nonneg _) (sub_nonneg.2 (sigmaCut_le_one _))

private theorem etaCut_le_one (k : ℕ) (r : ℝ) : etaCut k r ≤ 1 := by
  calc etaCut k r ≤ 1 * 1 :=
        mul_le_mul (sigmaCut_le_one _) (sub_le_self _ (sigmaCut_nonneg _))
          (sub_nonneg.2 (sigmaCut_le_one _)) zero_le_one
    _ = 1 := one_mul 1

private theorem etaCut_zero_of_le (k : ℕ) {r : ℝ} (hr : r ≤ (cutScale k)⁻¹) :
    etaCut k r = 0 := by
  unfold etaCut
  have hN : 0 < cutScale k := cutScale_pos k
  have h1 : cutScale k * r ≤ 1 := by
    calc cutScale k * r ≤ cutScale k * (cutScale k)⁻¹ :=
          mul_le_mul_of_nonneg_left hr hN.le
      _ = 1 := mul_inv_cancel₀ hN.ne'
  rw [sigmaCut_zero_of_le h1, zero_mul]

private theorem etaCut_zero_of_ge (k : ℕ) {r : ℝ} (hr : 2 * cutScale k ≤ r) :
    etaCut k r = 0 := by
  unfold etaCut
  have hN : 0 < cutScale k := cutScale_pos k
  have h2 : 2 ≤ r / cutScale k := (le_div_iff₀ hN).2 hr
  rw [sigmaCut_one_of_ge h2, sub_self, mul_zero]

private theorem etaCut_eq_inner_of_lt_two (k : ℕ) {r : ℝ} (hr : r < 2) :
    etaCut k r = sigmaCut (cutScale k * r) := by
  unfold etaCut
  have hN3 : (3 : ℝ) ≤ cutScale k := three_le_cutScale k
  have hN0 : 0 < cutScale k := cutScale_pos k
  have h1 : r / cutScale k ≤ 1 := by
    rw [div_le_one hN0]
    linarith
  rw [sigmaCut_zero_of_le h1, sub_zero, mul_one]

private theorem etaCut_eq_outer_of_gt_one (k : ℕ) {r : ℝ} (hr : 1 < r) :
    etaCut k r = 1 - sigmaCut (r / cutScale k) := by
  unfold etaCut
  have hN3 : (3 : ℝ) ≤ cutScale k := three_le_cutScale k
  have h2 : 2 ≤ cutScale k * r := by nlinarith
  rw [sigmaCut_one_of_ge h2, one_mul]

private theorem etaCut_eq_one_on_mid (k : ℕ) {r : ℝ}
    (hr1 : 2 * (cutScale k)⁻¹ ≤ r) (hr2 : r ≤ cutScale k) :
    etaCut k r = 1 := by
  unfold etaCut
  have hN : 0 < cutScale k := cutScale_pos k
  have h_in : 2 ≤ cutScale k * r := by
    have := mul_le_mul_of_nonneg_left hr1 hN.le
    rwa [← mul_assoc, mul_comm (cutScale k) 2, mul_assoc, mul_inv_cancel₀ hN.ne', mul_one] at this
  have h_out : r / cutScale k ≤ 1 := (div_le_one hN).2 hr2
  rw [sigmaCut_one_of_ge h_in, sigmaCut_zero_of_le h_out, sub_zero, one_mul]

/-! ### 3. `oscillatorD` product rule, conjugation, and two-zone `X_G` convergence -/

private theorem oscillatorD_congr_nhds {f g : ℝ → ℂ} {r : ℝ} (h : f =ᶠ[𝓝 r] g) :
    oscillatorD f r = oscillatorD g r := by
  have h0 : f r = g r := h.eq_of_nhds
  have h1 : deriv f r = deriv g r := by rw [h.deriv_eq]
  have h2 : deriv (deriv f) r = deriv (deriv g) r := by rw [h.deriv.deriv_eq]
  unfold oscillatorD
  rw [h0, h1, h2]

private theorem oscillatorD_real_mul {α : ℝ → ℝ} {φ : ℝ → ℂ}
    (hα : ContDiff ℝ ∞ α) (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    oscillatorD (fun s => (α s : ℂ) * φ s) r =
      (α r : ℂ) * oscillatorD φ r +
        ((deriv (deriv α) r : ℝ) : ℂ) * φ r +
        2 * ((deriv α r : ℝ) : ℂ) * deriv φ r +
        ((deriv α r : ℝ) : ℂ) * φ r / (r : ℂ) +
        (((r / 2) * deriv α r : ℝ) : ℂ) * φ r := by
  have hdα1 : ∀ s, HasDerivAt (fun t => (α t : ℂ)) ((deriv α s : ℝ) : ℂ) s := fun s =>
    (((hα.differentiable (by simp)) s).hasDerivAt).ofReal_comp
  have hα' : ContDiff ℝ ∞ (deriv α) := (contDiff_infty_iff_deriv.mp hα).2
  have hdα2 : ∀ s, HasDerivAt (fun t => ((deriv α t : ℝ) : ℂ)) ((deriv (deriv α) s : ℝ) : ℂ) s :=
    fun s => (((hα'.differentiable (by simp)) s).hasDerivAt).ofReal_comp
  have hdφ1 : ∀ s, HasDerivAt φ (deriv φ s) s := fun s =>
    ((hφ.differentiable (by simp)) s).hasDerivAt
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hdφ2 : ∀ s, HasDerivAt (deriv φ) (deriv (deriv φ) s) s := fun s =>
    ((hφ'.differentiable (by simp)) s).hasDerivAt
  have hd1_fun : deriv (fun s => (α s : ℂ) * φ s) =
      fun s => ((deriv α s : ℝ) : ℂ) * φ s + (α s : ℂ) * deriv φ s := by
    funext s
    exact ((hdα1 s).mul (hdφ1 s)).deriv
  have hd2_r : deriv (deriv (fun s => (α s : ℂ) * φ s)) r =
      (((deriv (deriv α) r : ℝ) : ℂ) * φ r + ((deriv α r : ℝ) : ℂ) * deriv φ r) +
        (((deriv α r : ℝ) : ℂ) * deriv φ r + (α r : ℂ) * deriv (deriv φ) r) := by
    rw [hd1_fun]
    exact (((hdα2 r).mul (hdφ1 r)).add ((hdα1 r).mul (hdφ2 r))).deriv
  have hd1_r : deriv (fun s => (α s : ℂ) * φ s) r =
      ((deriv α r : ℝ) : ℂ) * φ r + (α r : ℂ) * deriv φ r := congrFun hd1_fun r
  unfold oscillatorD
  rw [hd2_r, hd1_r]
  simp only [div_eq_mul_inv]
  push_cast
  ring

private theorem oscillatorD_conj {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    oscillatorD (fun s => conj (ψ s)) r = conj (oscillatorD ψ r) := by
  have hclm : ∀ {g : ℝ → ℂ}, Differentiable ℝ g →
      deriv (fun s => conj (g s)) = fun s => conj (deriv g s) := by
    intro g hg
    funext s
    have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s
      (hg s).hasDerivAt).deriv
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using h
  have hd1 : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hψ' : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hd2 : Differentiable ℝ (deriv ψ) := hψ'.differentiable (by simp)
  have e1 : deriv (fun s => conj (ψ s)) = fun s => conj (deriv ψ s) := hclm hd1
  have e2 : deriv (deriv (fun s => conj (ψ s))) r = conj (deriv (deriv ψ) r) := by
    rw [e1]
    exact congrFun (hclm hd2) r
  unfold oscillatorD
  rw [e2, congrFun e1 r]
  simp [map_add, map_sub, map_mul, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_ofNat]

private theorem innerCut_deriv (N s : ℝ) :
    deriv (fun t => sigmaCut (N * t)) s = N * deriv sigmaCut (N * s) ∧
      deriv (deriv (fun t => sigmaCut (N * t))) s = N ^ 2 * deriv (deriv sigmaCut) (N * s) := by
  have hd1_sigma : Differentiable ℝ sigmaCut := sigmaCut_contDiff.differentiable (by simp)
  have hd2_sigma : Differentiable ℝ (deriv sigmaCut) :=
    ((contDiff_infty_iff_deriv.mp sigmaCut_contDiff).2).differentiable (by simp)
  have hf1 : ∀ t, HasDerivAt (fun u => sigmaCut (N * u)) (N * deriv sigmaCut (N * t)) t := by
    intro t
    have h := (hd1_sigma (N * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul N)
    refine h.congr_deriv ?_
    ring
  have heq1 : deriv (fun t => sigmaCut (N * t)) = fun t => N * deriv sigmaCut (N * t) :=
    funext fun t => (hf1 t).deriv
  refine ⟨congrFun heq1 s, ?_⟩
  rw [heq1]
  have h := ((hd2_sigma (N * s)).hasDerivAt.comp s ((hasDerivAt_id s).const_mul N)).const_mul N
  refine (h.congr_deriv ?_).deriv
  ring

private theorem outerCut_deriv (N s : ℝ) :
    deriv (fun t => 1 - sigmaCut (t / N)) s = -(N⁻¹ * deriv sigmaCut (s / N)) ∧
      deriv (deriv (fun t => 1 - sigmaCut (t / N))) s =
        -((N⁻¹) ^ 2 * deriv (deriv sigmaCut) (s / N)) := by
  have hd1_sigma : Differentiable ℝ sigmaCut := sigmaCut_contDiff.differentiable (by simp)
  have hd2_sigma : Differentiable ℝ (deriv sigmaCut) :=
    ((contDiff_infty_iff_deriv.mp sigmaCut_contDiff).2).differentiable (by simp)
  have hf1 : ∀ t, HasDerivAt (fun u => 1 - sigmaCut (u / N))
      (-(N⁻¹ * deriv sigmaCut (t / N))) t := by
    intro t
    have hlin : HasDerivAt (fun u : ℝ => u / N) N⁻¹ t := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const N⁻¹
    have h := (hasDerivAt_const t (1 : ℝ)).sub ((hd1_sigma (t / N)).hasDerivAt.comp t hlin)
    refine h.congr_deriv ?_
    ring
  have heq1 : deriv (fun t => 1 - sigmaCut (t / N)) =
      fun t => -(N⁻¹ * deriv sigmaCut (t / N)) :=
    funext fun t => (hf1 t).deriv
  refine ⟨congrFun heq1 s, ?_⟩
  rw [heq1]
  have hlin : HasDerivAt (fun u : ℝ => u / N) N⁻¹ s := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id s).mul_const N⁻¹
  have h := (((hd2_sigma (s / N)).hasDerivAt.comp s hlin).const_mul N⁻¹).neg
  refine (h.congr_deriv ?_).deriv
  ring

private theorem tendsto_toLp_zero_of_two_zone
    {E : ℕ → ℝ → ℂ} (hE : ∀ k, MemLp (E k) 2 xGMeasure)
    (hEm : ∀ k, ContinuousOn (E k) (Ioi 0))
    {H : ℝ → ℂ} (hH : MemLp H 2 xGMeasure) (hHm : Continuous H)
    {C_in C_out : ℝ} (_hCin : 0 ≤ C_in) (_hCout : 0 ≤ C_out)
    (h_in : ∀ k r, 0 < r → r ≤ 2 * (cutScale k)⁻¹ → ‖E k r‖ ≤ C_in)
    (h_out : ∀ k r, 2 * (cutScale k)⁻¹ < r → ‖E k r‖ ≤ (C_out / cutScale k) * ‖H r‖) :
    Tendsto (fun k => ‖(hE k).toLp (E k)‖) atTop (𝓝 0) := by
  let K_in : ℝ := C_in ^ 2 * (4 * Real.pi * Real.exp (1 / 4))
  have hKin : 0 ≤ K_in := by positivity
  have hIntH : IntegrableOn
      (fun r => ‖H r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) (Ioi 0) :=
    (memLp_iff_integrableOn hHm.aestronglyMeasurable).1 hH
  have hsq_le : ∀ k : ℕ, ‖(hE k).toLp (E k)‖ ^ 2 ≤
      (2 * (cutScale k)⁻¹) * K_in + (C_out / cutScale k) ^ 2 * ‖hH.toLp H‖ ^ 2 := by
    intro k
    have hN3 : (3 : ℝ) ≤ cutScale k := three_le_cutScale k
    have hN0 : 0 < cutScale k := cutScale_pos k
    set δ : ℝ := 2 * (cutScale k)⁻¹
    have hδ0 : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 := by
      have : (cutScale k)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) hN3
      linarith
    have hE_meas : AEStronglyMeasurable (E k) (volume.restrict (Ioi 0)) :=
      (hEm k).aestronglyMeasurable measurableSet_Ioi
    have hIntE : IntegrableOn
        (fun r => ‖E k r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) (Ioi 0) :=
      (memLp_iff_integrableOn hE_meas).1 (hE k)
    have hIntInd : IntegrableOn ((Ioc 0 δ).indicator (fun _ => K_in)) (Ioi 0) := by
      rw [integrableOn_indicator_iff measurableSet_Ioc]
      have hinter : Ioi (0 : ℝ) ∩ Ioc 0 δ = Ioc 0 δ :=
        inter_eq_right.2 (fun _ hx => hx.1)
      rw [inter_comm, hinter]
      exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hInd_val : ∫ r in Ioi (0 : ℝ), (Ioc 0 δ).indicator (fun _ => K_in) r = δ * K_in := by
      rw [setIntegral_indicator measurableSet_Ioc]
      have hinter : Ioi (0 : ℝ) ∩ Ioc 0 δ = Ioc 0 δ :=
        inter_eq_right.2 (fun _ hx => hx.1)
      rw [hinter, setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal hδ0.le, smul_eq_mul]
    rw [norm_sq_toLp (hE k)]
    calc ∫ r in Ioi (0 : ℝ), ‖E k r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)
        ≤ ∫ r in Ioi (0 : ℝ), ((Ioc 0 δ).indicator (fun _ => K_in) r +
            (C_out / cutScale k) ^ 2 * (‖H r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r))) := by
          refine setIntegral_mono_on hIntE (hIntInd.add (hIntH.const_mul _)) measurableSet_Ioi ?_
          intro r hr
          have hr0 : 0 < r := hr
          have hw_nn : 0 ≤ (radialGaussianWeight r)⁻¹ * r :=
            mul_nonneg (inv_nonneg.2 (radialGaussianWeight_pos r).le) hr0.le
          by_cases hrδ : r ≤ δ
          · have hmem : r ∈ Ioc 0 δ := ⟨hr0, hrδ⟩
            rw [indicator_of_mem hmem]
            have hr1 : r ≤ 1 := hrδ.trans hδ1
            have hw_le : (radialGaussianWeight r)⁻¹ * r ≤ 4 * Real.pi * Real.exp (1 / 4) := by
              rw [radialGaussianWeight_inv]
              have hsq1 : r ^ 2 ≤ 1 := by nlinarith
              have hexp : Real.exp (r ^ 2 / 4) ≤ Real.exp (1 / 4) :=
                Real.exp_le_exp.2 (by linarith)
              calc 4 * Real.pi * Real.exp (r ^ 2 / 4) * r
                  ≤ 4 * Real.pi * Real.exp (1 / 4) * 1 :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hexp (by positivity)) hr1 hr0.le
                      (by positivity)
                _ = 4 * Real.pi * Real.exp (1 / 4) := mul_one _
            have hEr : ‖E k r‖ ^ 2 ≤ C_in ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (h_in k r hr0 hrδ) 2
            have h1 : ‖E k r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) ≤ K_in :=
              mul_le_mul hEr hw_le hw_nn (sq_nonneg C_in)
            have h2 : 0 ≤ (C_out / cutScale k) ^ 2 *
                (‖H r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) := by positivity
            linarith
          · have hnot : r ∉ Ioc 0 δ := fun h => hrδ h.2
            rw [indicator_of_notMem hnot, zero_add]
            have hgt : δ < r := not_le.mp hrδ
            have hEr : ‖E k r‖ ^ 2 ≤ ((C_out / cutScale k) * ‖H r‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (h_out k r hgt) 2
            calc ‖E k r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)
                ≤ ((C_out / cutScale k) * ‖H r‖) ^ 2 * ((radialGaussianWeight r)⁻¹ * r) :=
                  mul_le_mul_of_nonneg_right hEr hw_nn
              _ = (C_out / cutScale k) ^ 2 * (‖H r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) := by
                  ring
      _ = (∫ r in Ioi (0 : ℝ), (Ioc 0 δ).indicator (fun _ => K_in) r) +
            (C_out / cutScale k) ^ 2 *
              ∫ r in Ioi (0 : ℝ), ‖H r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) := by
          rw [integral_add hIntInd (hIntH.const_mul _), integral_const_mul]
      _ = δ * K_in + (C_out / cutScale k) ^ 2 * ‖hH.toLp H‖ ^ 2 := by
          rw [hInd_val, norm_sq_toLp hH]
  have hinv : Tendsto (fun k : ℕ => (cutScale k)⁻¹) atTop (𝓝 0) := by
    have htop : Tendsto cutScale atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_inv_atTop_zero.comp htop
  have hdiv : Tendsto (fun k : ℕ => C_out / cutScale k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul C_out
  have hrhs : Tendsto (fun k : ℕ =>
      (2 * (cutScale k)⁻¹) * K_in + (C_out / cutScale k) ^ 2 * ‖hH.toLp H‖ ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (2 * (cutScale k)⁻¹) * K_in) atTop (𝓝 0) := by
      simpa using (hinv.const_mul 2).mul_const K_in
    have h2 : Tendsto (fun k : ℕ => (C_out / cutScale k) ^ 2 * ‖hH.toLp H‖ ^ 2) atTop (𝓝 0) := by
      simpa using (hdiv.pow 2).mul_const (‖hH.toLp H‖ ^ 2)
    simpa using h1.add h2
  have hsq0 : Tendsto (fun k : ℕ => ‖(hE k).toLp (E k)‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hsq_le hrhs
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq0
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun k => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-! ### 4. Cutoff approximation of each `oscBasis n` -/

private theorem profFun_X_mul (p : ℂ[X]) (r : ℝ) :
    profFun (Polynomial.X * p) r = (r : ℂ) ^ 2 * profFun p r := by
  simp only [profFun, eval_mul, eval_X]
  ring

private theorem mul_deriv_profFun (p : ℂ[X]) (r : ℝ) :
    (r : ℂ) * deriv (profFun p) r =
      2 * profFun p r +
        2 * profFun (Polynomial.X * (Polynomial.derivative p - (1 / 4 : ℂ) • p)) r := by
  rw [congrFun (oscProf_deriv_profFun p) r, oscProf_profFun_eq p r,
    profFun_X_mul, oscProf_profFun_eq _ r]
  ring

private theorem outer_zone_bound {a1 a2 a3 a4 a5 : ℂ} {n : ℕ} {M₁ M₂ N S₀ S₁ S₂ : ℝ}
    (hN0 : 0 < N) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hS₀ : 0 ≤ S₀) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hu1 : ‖a1‖ ≤ ((n : ℝ) / N) * S₁)
    (hu2 : ‖a2‖ ≤ (M₂ / N) * S₀)
    (hu3 : ‖a3‖ ≤ (4 * M₁ / N) * (S₀ + S₂))
    (hu4 : ‖a4‖ ≤ (M₁ / N) * S₀)
    (hu5 : ‖a5‖ ≤ (M₁ / N) * S₁) :
    ‖a1 - a2 - a3 - a4 - a5‖ ≤ (((n : ℝ) + M₂ + 6 * M₁) / N) * (S₀ + S₁ + S₂) := by
  have htri : ‖a1 - a2 - a3 - a4 - a5‖ ≤ ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
    exact add_le_add (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl) le_rfl
  have hsum : ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ ≤
      ((n : ℝ) / N) * S₁ + (M₂ / N) * S₀ + (4 * M₁ / N) * (S₀ + S₂) +
        (M₁ / N) * S₀ + (M₁ / N) * S₁ := by
    linarith
  have hdiff : (((n : ℝ) + M₂ + 6 * M₁) / N) * (S₀ + S₁ + S₂) -
      (((n : ℝ) / N) * S₁ + (M₂ / N) * S₀ + (4 * M₁ / N) * (S₀ + S₂) +
        (M₁ / N) * S₀ + (M₁ / N) * S₁) =
      (1 / N) * (((n : ℝ) + M₁) * S₀ + (M₂ + 5 * M₁) * S₁ +
        ((n : ℝ) + M₂ + 2 * M₁) * S₂) := by
    ring
  have hpos : 0 ≤ (1 / N) * (((n : ℝ) + M₁) * S₀ + (M₂ + 5 * M₁) * S₁ +
      ((n : ℝ) + M₂ + 2 * M₁) * S₂) := by
    positivity
  linarith

private theorem exists_oscBasis_approx (n : ℕ) :
    ∃ (ψ : ℕ → ℝ → ℂ) (a b : ℕ → ℝ) (hΨ : ∀ k, MemLp (ψ k) 2 xGMeasure)
      (hDΨ : ∀ k, MemLp (oscillatorD (ψ k)) 2 xGMeasure),
      (∀ k, 0 < a k ∧ a k ≤ b k) ∧
      (∀ k, ContDiff ℝ ∞ (ψ k)) ∧
      (∀ k r, r < a k → ψ k r = 0) ∧
      (∀ k r, b k < r → ψ k r = 0) ∧
      Tendsto (fun k => ‖(hΨ k).toLp (ψ k) - oscBasis n‖) atTop (𝓝 0) ∧
      Tendsto (fun k => ‖(hDΨ k).toLp (oscillatorD (ψ k)) + (n : ℂ) • (hΨ k).toLp (ψ k)‖)
        atTop (𝓝 0) := by
  obtain ⟨q, hq_osc, hlag_prof⟩ := osc_eigen n
  have hbasis_eq : oscBasis n = prof q := by rw [coe_oscBasis, hq_osc]
  have hlag : lag q = -(n : ℂ) • q := by
    apply prof_injective
    rw [hlag_prof, map_smul, neg_smul]
  let φ : ℝ → ℂ := profFun q
  have hφ_cd : ContDiff ℝ ∞ φ := oscProfContDiff_proof q
  have hφ_ode : ∀ r : ℝ, 0 < r → oscillatorD φ r = -(n : ℂ) * φ r := by
    intro r hr
    rw [oscProfOde_proof q r hr, hlag, profFun_smul, Pi.smul_apply, smul_eq_mul]
  let q₁ : ℂ[X] := Polynomial.derivative q - (1 / 4 : ℂ) • q
  let a : ℕ → ℝ := fun k => (cutScale k)⁻¹
  let b : ℕ → ℝ := fun k => 2 * cutScale k
  let ψ : ℕ → ℝ → ℂ := fun k r => (etaCut k r : ℂ) * φ r
  have hab : ∀ k, 0 < a k ∧ a k ≤ b k := by
    intro k
    have hN3 : (3 : ℝ) ≤ cutScale k := three_le_cutScale k
    have hN0 : 0 < cutScale k := cutScale_pos k
    refine ⟨inv_pos.2 hN0, ?_⟩
    have : a k ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have hψ_cd : ∀ k, ContDiff ℝ ∞ (ψ k) := fun k =>
    (Complex.ofRealCLM.contDiff.comp (etaCut_contDiff k)).mul hφ_cd
  have hψ_lt : ∀ k r, r < a k → ψ k r = 0 := by
    intro k r hr
    simp [ψ, etaCut_zero_of_le k hr.le]
  have hψ_gt : ∀ k r, b k < r → ψ k r = 0 := by
    intro k r hr
    simp [ψ, etaCut_zero_of_ge k hr.le]
  have hΨ : ∀ k, MemLp (ψ k) 2 xGMeasure := fun k =>
    testMemLp_proof (ψ k) (hψ_cd k).continuous (a k) (b k) (hψ_lt k) (hψ_gt k)
  have hosc_lt : ∀ k r, r < a k → oscillatorD (ψ k) r = 0 := by
    intro k r hr
    apply oscillatorD_eq_zero_of_eventually
    filter_upwards [Iio_mem_nhds hr] with s hs
    exact hψ_lt k s hs
  have hosc_gt : ∀ k r, b k < r → oscillatorD (ψ k) r = 0 := by
    intro k r hr
    apply oscillatorD_eq_zero_of_eventually
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact hψ_gt k s hs
  have hosc_cont : ∀ k, Continuous (oscillatorD (ψ k)) := by
    intro k
    refine continuous_iff_continuousAt.2 fun r => ?_
    by_cases hr : r < a k
    · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) r).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hr] with s hs
      exact hosc_lt k s hs
    · have hr0 : 0 < r := lt_of_lt_of_le (hab k).1 (not_lt.mp hr)
      have hcontOn : ContinuousOn (oscillatorD (ψ k)) (Ioi 0) :=
        smoothnessFacts_proof.2 (ψ k) (hψ_cd k).contDiffOn
      exact hcontOn.continuousAt (isOpen_Ioi.mem_nhds hr0)
  have hDΨ : ∀ k, MemLp (oscillatorD (ψ k)) 2 xGMeasure := fun k =>
    testMemLp_proof (oscillatorD (ψ k)) (hosc_cont k) (a k) (b k) (hosc_lt k) (hosc_gt k)
  -- Bounds on [0, 1] for qp q (r^2) and qp q₁ (r^2)
  have hqp0_cont : Continuous (fun r : ℝ => qp q (r ^ 2)) := by
    have h := (oscProfContDiff_proof (1 : ℂ[X]))
    unfold qp
    fun_prop
  have hqp1_cont : Continuous (fun r : ℝ => qp q₁ (r ^ 2)) := by
    unfold qp
    fun_prop
  obtain ⟨B₀', hB₀'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hqp0_cont.continuousOn : ContinuousOn (fun r : ℝ => qp q (r ^ 2)) (Icc 0 1))
  obtain ⟨B₁', hB₁'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hqp1_cont.continuousOn : ContinuousOn (fun r : ℝ => qp q₁ (r ^ 2)) (Icc 0 1))
  let B₀ : ℝ := max (max B₀' B₁') 0
  have hB₀_nn : 0 ≤ B₀ := le_max_right _ _
  have hφ_small : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
      ‖φ r‖ ≤ B₀ * r ^ 2 ∧ ‖deriv φ r‖ ≤ 4 * B₀ * r := by
    intro r hr0 hr1
    have hq0 : ‖qp q (r ^ 2)‖ ≤ B₀ :=
      (hB₀' r ⟨hr0, hr1⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hq1 : ‖qp q₁ (r ^ 2)‖ ≤ B₀ :=
      (hB₁' r ⟨hr0, hr1⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
    have hr_norm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0]
    constructor
    · rw [show φ r = (r : ℂ) * (r : ℂ) * qp q (r ^ 2) from oscProf_profFun_eq q r]
      rw [norm_mul, norm_mul, hr_norm]
      calc r * r * ‖qp q (r ^ 2)‖ ≤ r * r * B₀ :=
            mul_le_mul_of_nonneg_left hq0 (mul_nonneg hr0 hr0)
        _ = B₀ * r ^ 2 := by ring
    · rw [congrFun (oscProf_deriv_profFun q) r]
      have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h1 : ‖2 * (r : ℂ) * qp q (r ^ 2)‖ ≤ 2 * B₀ * r := by
        rw [norm_mul, norm_mul, h2norm, hr_norm]
        calc 2 * r * ‖qp q (r ^ 2)‖ ≤ 2 * r * B₀ :=
              mul_le_mul_of_nonneg_left hq0 (by positivity)
          _ = 2 * B₀ * r := by ring
      have h2 : ‖2 * ((r : ℂ) * (r : ℂ) * (r : ℂ)) * qp q₁ (r ^ 2)‖ ≤ 2 * B₀ * r := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, h2norm, hr_norm]
        have hr3 : r * r * r ≤ r := by nlinarith
        calc 2 * (r * r * r) * ‖qp q₁ (r ^ 2)‖ ≤ 2 * r * B₀ :=
              mul_le_mul (by linarith) hq1 (norm_nonneg _) (by positivity)
          _ = 2 * B₀ * r := by ring
      exact (norm_add_le _ _).trans (by linarith)
  -- Dominating profile H in X_G
  let H : ℝ → ℂ := fun r =>
    ((‖profFun q r‖ + ‖profFun (Polynomial.X * q) r‖ +
      ‖profFun (Polynomial.X * q₁) r‖ : ℝ) : ℂ)
  have hH_norm : ∀ r : ℝ, ‖H r‖ =
      ‖profFun q r‖ + ‖profFun (Polynomial.X * q) r‖ + ‖profFun (Polynomial.X * q₁) r‖ := by
    intro r
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hH_cont : Continuous H := by
    have hc0 := (oscProfContDiff_proof q).continuous.norm
    have hc1 := (oscProfContDiff_proof (Polynomial.X * q)).continuous.norm
    have hc2 := (oscProfContDiff_proof (Polynomial.X * q₁)).continuous.norm
    exact Complex.continuous_ofReal.comp ((hc0.add hc1).add hc2)
  have hH_lp : MemLp H 2 xGMeasure := by
    have hm1 : MemLp (fun r => ((‖profFun q r‖ : ℝ) : ℂ)) 2 xGMeasure :=
      (memLp_profFun q).norm.ofReal
    have hm2 : MemLp (fun r => ((‖profFun (Polynomial.X * q) r‖ : ℝ) : ℂ)) 2 xGMeasure :=
      (memLp_profFun (Polynomial.X * q)).norm.ofReal
    have hm3 : MemLp (fun r => ((‖profFun (Polynomial.X * q₁) r‖ : ℝ) : ℂ)) 2 xGMeasure :=
      (memLp_profFun (Polynomial.X * q₁)).norm.ofReal
    convert (hm1.add hm2).add hm3 using 1
    funext r
    simp [H]
  -- Step A: `‖toLp (ψ k) - oscBasis n‖ → 0`
  have hE1_lp : ∀ k, MemLp (fun r => ψ k r - φ r) 2 xGMeasure :=
    fun k => (hΨ k).sub (memLp_profFun q)
  have hE1_tendsto : Tendsto (fun k => ‖(hE1_lp k).toLp (fun r => ψ k r - φ r)‖) atTop (𝓝 0) := by
    refine tendsto_toLp_zero_of_two_zone hE1_lp
      (fun k => ((hψ_cd k).continuous.sub hφ_cd.continuous).continuousOn)
      hH_lp hH_cont hB₀_nn zero_le_one (fun k r hr0 hrδ => ?_) (fun k r hrδ => ?_)
    · have hN3 : (3 : ℝ) ≤ cutScale k := three_le_cutScale k
      have hr1 : r ≤ 1 := hrδ.trans (by
        have : (cutScale k)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) hN3
        linarith)
      have heta : |etaCut k r - 1| ≤ 1 := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [etaCut_le_one k r], by linarith [etaCut_nonneg k r]⟩
      have hrew : ψ k r - φ r = ((etaCut k r - 1 : ℝ) : ℂ) * φ r := by simp [ψ]; ring
      rw [hrew, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hrsq : r ^ 2 ≤ 1 := by nlinarith
      calc |etaCut k r - 1| * ‖φ r‖ ≤ 1 * (B₀ * r ^ 2) :=
            mul_le_mul heta (hφ_small hr0.le hr1).1 (norm_nonneg _) zero_le_one
        _ = B₀ * r ^ 2 := one_mul _
        _ ≤ B₀ * 1 := mul_le_mul_of_nonneg_left hrsq hB₀_nn
        _ = B₀ := mul_one _
    · by_cases hrN : r < cutScale k
      · have heta1 : etaCut k r = 1 := etaCut_eq_one_on_mid k hrδ.le hrN.le
        have hz : ψ k r - φ r = 0 := by simp [ψ, heta1]
        rw [hz, norm_zero]
        exact mul_nonneg (div_nonneg zero_le_one (cutScale_pos k).le) (norm_nonneg _)
      · have hrN' : cutScale k ≤ r := not_lt.mp hrN
        have hN3 : (3 : ℝ) ≤ cutScale k := three_le_cutScale k
        have hN0 : 0 < cutScale k := cutScale_pos k
        have hr1 : 1 ≤ r := by linarith
        have hr2 : cutScale k ≤ r ^ 2 := by nlinarith
        have h1_le : 1 ≤ (1 / cutScale k) * r ^ 2 := by
          rw [one_div_mul_eq_div, le_div_iff₀ hN0]
          linarith
        have heta : |etaCut k r - 1| ≤ 1 := by
          rw [abs_sub_le_iff]
          exact ⟨by linarith [etaCut_le_one k r], by linarith [etaCut_nonneg k r]⟩
        have hrew : ψ k r - φ r = ((etaCut k r - 1 : ℝ) : ℂ) * φ r := by simp [ψ]; ring
        have hXφ : r ^ 2 * ‖φ r‖ = ‖profFun (Polynomial.X * q) r‖ := by
          rw [profFun_X_mul, norm_mul, norm_pow, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
        rw [hrew, norm_mul, Complex.norm_real, Real.norm_eq_abs, hH_norm]
        calc |etaCut k r - 1| * ‖φ r‖
            ≤ 1 * ‖φ r‖ := mul_le_mul_of_nonneg_right heta (norm_nonneg _)
          _ ≤ ((1 / cutScale k) * r ^ 2) * ‖φ r‖ :=
              mul_le_mul_of_nonneg_right h1_le (norm_nonneg _)
          _ = (1 / cutScale k) * ‖profFun (Polynomial.X * q) r‖ := by rw [mul_assoc, hXφ]
          _ ≤ (1 / cutScale k) *
                (‖profFun q r‖ + ‖profFun (Polynomial.X * q) r‖ +
                  ‖profFun (Polynomial.X * q₁) r‖) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith [norm_nonneg (profFun q r), norm_nonneg (profFun (Polynomial.X * q₁) r)]
  have hΨ_conv : Tendsto (fun k => ‖(hΨ k).toLp (ψ k) - oscBasis n‖) atTop (𝓝 0) := by
    refine hE1_tendsto.congr fun k => ?_
    congr 1
    rw [hbasis_eq]
    show (hE1_lp k).toLp (fun r => ψ k r - φ r) = (hΨ k).toLp (ψ k) - (memLp_profFun q).toLp φ
    exact MemLp.toLp_sub (hΨ k) (memLp_profFun q)
  -- Step B: `‖toLp (oscillatorD (ψ k)) + n • oscBasis n‖ → 0`
  obtain ⟨M₁, M₂, hM₁, hM₂, hM₁_bd, hM₂_bd⟩ := sigmaCut_deriv_bounds
  let C_in2 : ℝ := (n : ℝ) * B₀ + 4 * M₂ * B₀ + 19 * M₁ * B₀
  let C_out2 : ℝ := (n : ℝ) + M₂ + 6 * M₁
  have hCin2 : 0 ≤ C_in2 := by positivity
  have hCout2 : 0 ≤ C_out2 := by positivity
  have hE2_lp : ∀ k, MemLp (fun r => oscillatorD (ψ k) r + (n : ℂ) * φ r) 2 xGMeasure :=
    fun k => (hDΨ k).add ((memLp_profFun q).const_smul (n : ℂ))
  have hE2_tendsto :
      Tendsto (fun k => ‖(hE2_lp k).toLp (fun r => oscillatorD (ψ k) r + (n : ℂ) * φ r)‖)
        atTop (𝓝 0) := by
    refine tendsto_toLp_zero_of_two_zone hE2_lp
      (fun k => ((hosc_cont k).add (continuous_const.mul hφ_cd.continuous)).continuousOn)
      hH_lp hH_cont hCin2 hCout2 (fun k r hr0 hrδ => ?_) (fun k r hrδ => ?_)
    · set N := cutScale k
      have hN3 : (3 : ℝ) ≤ N := three_le_cutScale k
      have hN0 : 0 < N := cutScale_pos k
      have hr1 : r ≤ 1 := hrδ.trans (by
        have : N⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) hN3
        linarith)
      have hr2 : r < 2 := by linarith
      have hev : ψ k =ᶠ[𝓝 r] fun s => (sigmaCut (N * s) : ℂ) * φ s := by
        filter_upwards [Iio_mem_nhds hr2] with s hs
        dsimp only [ψ, N]
        rw [etaCut_eq_inner_of_lt_two k hs]
      rw [oscillatorD_congr_nhds hev,
        oscillatorD_real_mul (α := fun s => sigmaCut (N * s))
          (sigmaCut_contDiff.comp (contDiff_const.mul contDiff_id)) hφ_cd r,
        hφ_ode r hr0, (innerCut_deriv N r).1, (innerCut_deriv N r).2]
      have hNr : N * r ≤ 2 := by
        have := mul_le_mul_of_nonneg_left hrδ hN0.le
        rwa [← mul_assoc, mul_comm N 2, mul_assoc, mul_inv_cancel₀ hN0.ne', mul_one] at this
      have hN_le : N ≤ 2 / r := (le_div_iff₀ hr0).2 (by linarith)
      have hN2_le : N ^ 2 ≤ 4 / r ^ 2 :=
        (pow_le_pow_left₀ hN0.le hN_le 2).trans_eq (by ring)
      obtain ⟨hφ_bd, hdφ_bd⟩ := hφ_small hr0.le hr1
      have hrsq : r ^ 2 ≤ 1 := by nlinarith
      have hφ1 : ‖φ r‖ ≤ B₀ := hφ_bd.trans (mul_le_of_le_one_right hB₀_nn hrsq)
      have hr_norm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
      have hrew : ((sigmaCut (N * r) : ℝ) : ℂ) * (-(n : ℂ) * φ r) +
            ((N ^ 2 * deriv (deriv sigmaCut) (N * r) : ℝ) : ℂ) * φ r +
            2 * ((N * deriv sigmaCut (N * r) : ℝ) : ℂ) * deriv φ r +
            ((N * deriv sigmaCut (N * r) : ℝ) : ℂ) * φ r / (r : ℂ) +
            (((r / 2) * (N * deriv sigmaCut (N * r)) : ℝ) : ℂ) * φ r + (n : ℂ) * φ r =
          ((1 - sigmaCut (N * r) : ℝ) : ℂ) * ((n : ℂ) * φ r) +
            ((N ^ 2 * deriv (deriv sigmaCut) (N * r) : ℝ) : ℂ) * φ r +
            ((2 * (N * deriv sigmaCut (N * r)) : ℝ) : ℂ) * deriv φ r +
            ((N * deriv sigmaCut (N * r) : ℝ) : ℂ) * (φ r / (r : ℂ)) +
            (((r / 2) * (N * deriv sigmaCut (N * r)) : ℝ) : ℂ) * φ r := by
        push_cast
        ring
      rw [hrew]
      have ht1 : ‖((1 - sigmaCut (N * r) : ℝ) : ℂ) * ((n : ℂ) * φ r)‖ ≤ (n : ℝ) * B₀ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast,
          abs_of_nonneg (sub_nonneg.2 (sigmaCut_le_one _))]
        have h1s : 1 - sigmaCut (N * r) ≤ 1 := sub_le_self _ (sigmaCut_nonneg _)
        calc (1 - sigmaCut (N * r)) * ((n : ℝ) * ‖φ r‖)
            ≤ 1 * ((n : ℝ) * B₀) :=
              mul_le_mul h1s (mul_le_mul_of_nonneg_left hφ1 (Nat.cast_nonneg n))
                (by positivity) zero_le_one
          _ = (n : ℝ) * B₀ := one_mul _
      have ht2 : ‖((N ^ 2 * deriv (deriv sigmaCut) (N * r) : ℝ) : ℂ) * φ r‖ ≤ 4 * M₂ * B₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg N)]
        calc N ^ 2 * |deriv (deriv sigmaCut) (N * r)| * ‖φ r‖
            ≤ (4 / r ^ 2) * M₂ * (B₀ * r ^ 2) :=
              mul_le_mul (mul_le_mul hN2_le (hM₂_bd _) (abs_nonneg _) (by positivity)) hφ_bd
                (norm_nonneg _) (by positivity)
          _ = 4 * M₂ * B₀ := by field_simp [hr0.ne']
      have ht3 : ‖((2 * (N * deriv sigmaCut (N * r)) : ℝ) : ℂ) * deriv φ r‖ ≤ 16 * M₁ * B₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg two_pos.le, abs_of_nonneg hN0.le]
        calc 2 * (N * |deriv sigmaCut (N * r)|) * ‖deriv φ r‖
            ≤ 2 * ((2 / r) * M₁) * (4 * B₀ * r) :=
              mul_le_mul (mul_le_mul_of_nonneg_left
                (mul_le_mul hN_le (hM₁_bd _) (abs_nonneg _) (by positivity)) two_pos.le)
                hdφ_bd (norm_nonneg _) (by positivity)
          _ = 16 * M₁ * B₀ := by field_simp [hr0.ne']; ring
      have ht4 : ‖((N * deriv sigmaCut (N * r) : ℝ) : ℂ) * (φ r / (r : ℂ))‖ ≤ 2 * M₁ * B₀ := by
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg hN0.le, hr_norm]
        have hdiv : ‖φ r‖ / r ≤ B₀ * r := (div_le_iff₀ hr0).2 (hφ_bd.trans_eq (by ring))
        calc N * |deriv sigmaCut (N * r)| * (‖φ r‖ / r)
            ≤ (2 / r) * M₁ * (B₀ * r) :=
              mul_le_mul (mul_le_mul hN_le (hM₁_bd _) (abs_nonneg _) (by positivity))
                hdiv (by positivity) (by positivity)
          _ = 2 * M₁ * B₀ := by field_simp [hr0.ne']
      have ht5 : ‖(((r / 2) * (N * deriv sigmaCut (N * r)) : ℝ) : ℂ) * φ r‖ ≤ M₁ * B₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (by positivity), abs_of_nonneg hN0.le]
        have hrN_half : (r / 2) * N ≤ 1 := by linarith
        calc r / 2 * (N * |deriv sigmaCut (N * r)|) * ‖φ r‖
            = ((r / 2) * N) * |deriv sigmaCut (N * r)| * ‖φ r‖ := by ring
          _ ≤ 1 * M₁ * B₀ :=
              mul_le_mul (mul_le_mul hrN_half (hM₁_bd _) (abs_nonneg _) zero_le_one)
                hφ1 (norm_nonneg _) (by positivity)
          _ = M₁ * B₀ := by ring
      calc ‖((1 - sigmaCut (N * r) : ℝ) : ℂ) * ((n : ℂ) * φ r) +
              ((N ^ 2 * deriv (deriv sigmaCut) (N * r) : ℝ) : ℂ) * φ r +
              ((2 * (N * deriv sigmaCut (N * r)) : ℝ) : ℂ) * deriv φ r +
              ((N * deriv sigmaCut (N * r) : ℝ) : ℂ) * (φ r / (r : ℂ)) +
              (((r / 2) * (N * deriv sigmaCut (N * r)) : ℝ) : ℂ) * φ r‖
          ≤ (n : ℝ) * B₀ + 4 * M₂ * B₀ + 16 * M₁ * B₀ + 2 * M₁ * B₀ + M₁ * B₀ := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ht5)
            refine (norm_add_le _ _).trans (add_le_add ?_ ht4)
            refine (norm_add_le _ _).trans (add_le_add ?_ ht3)
            exact (norm_add_le _ _).trans (add_le_add ht1 ht2)
        _ = C_in2 := by unfold C_in2; ring
    · set N := cutScale k
      have hN3 : (3 : ℝ) ≤ N := three_le_cutScale k
      have hN0 : 0 < N := cutScale_pos k
      by_cases hrN : r < N
      · have hev : ψ k =ᶠ[𝓝 r] φ := by
          filter_upwards [Ioo_mem_nhds hrδ hrN] with s hs
          simp [ψ, etaCut_eq_one_on_mid k hs.1.le hs.2.le]
        have hr0 : 0 < r := lt_trans (by positivity) hrδ
        rw [oscillatorD_congr_nhds hev, hφ_ode r hr0]
        simp only [neg_mul, neg_add_cancel, norm_zero]
        exact mul_nonneg (div_nonneg hCout2 hN0.le) (norm_nonneg _)
      · have hrN' : N ≤ r := not_lt.mp hrN
        have hr1 : 1 < r := by linarith
        have hr0 : 0 < r := by linarith
        have hev : ψ k =ᶠ[𝓝 r] fun s => ((1 - sigmaCut (s / N) : ℝ) : ℂ) * φ s := by
          filter_upwards [Ioi_mem_nhds hr1] with s hs
          dsimp only [ψ, N]
          rw [etaCut_eq_outer_of_gt_one k hs]
        rw [oscillatorD_congr_nhds hev,
          oscillatorD_real_mul (α := fun s => 1 - sigmaCut (s / N))
            (contDiff_const.sub (sigmaCut_contDiff.comp (contDiff_id.div_const N))) hφ_cd r,
          hφ_ode r hr0, (outerCut_deriv N r).1, (outerCut_deriv N r).2, hH_norm]
        set S₀ := ‖profFun q r‖
        set S₁ := ‖profFun (Polynomial.X * q) r‖
        set S₂ := ‖profFun (Polynomial.X * q₁) r‖
        have hS₀ : 0 ≤ S₀ := norm_nonneg _
        have hS₁ : 0 ≤ S₁ := norm_nonneg _
        have hS₂ : 0 ≤ S₂ := norm_nonneg _
        have hr_norm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
        have hXφ : r ^ 2 * S₀ = S₁ := by
          dsimp [S₀, S₁]
          rw [profFun_X_mul, norm_mul, norm_pow, hr_norm]
        have hrdφ : r * ‖deriv φ r‖ ≤ 2 * S₀ + 2 * S₂ := by
          have hm := mul_deriv_profFun q r
          have hnorm := congrArg norm hm
          rw [norm_mul, hr_norm] at hnorm
          rw [hnorm]
          refine (norm_add_le _ _).trans ?_
          have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
          rw [norm_mul, norm_mul, h2norm]
        have hdφ_le : ‖deriv φ r‖ ≤ 2 * S₀ + 2 * S₂ := by
          calc ‖deriv φ r‖ ≤ r * ‖deriv φ r‖ := le_mul_of_one_le_left (norm_nonneg _) hr1.le
            _ ≤ 2 * S₀ + 2 * S₂ := hrdφ
        have hr2_ge : N ≤ r ^ 2 := by nlinarith
        have h1_le_r2N : 1 ≤ r ^ 2 / N := (le_div_iff₀ hN0).2 (by linarith)
        have hinv_sq : (N⁻¹) ^ 2 ≤ N⁻¹ := by
          have hinv1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
          nlinarith [inv_pos.2 hN0]
        have hrew : ((1 - sigmaCut (r / N) : ℝ) : ℂ) * (-(n : ℂ) * φ r) +
              ((-((N⁻¹) ^ 2 * deriv (deriv sigmaCut) (r / N)) : ℝ) : ℂ) * φ r +
              2 * ((-(N⁻¹ * deriv sigmaCut (r / N)) : ℝ) : ℂ) * deriv φ r +
              ((-(N⁻¹ * deriv sigmaCut (r / N)) : ℝ) : ℂ) * φ r / (r : ℂ) +
              (((r / 2) * -(N⁻¹ * deriv sigmaCut (r / N)) : ℝ) : ℂ) * φ r + (n : ℂ) * φ r =
            (sigmaCut (r / N) : ℂ) * ((n : ℂ) * φ r) -
              (((N⁻¹) ^ 2 * deriv (deriv sigmaCut) (r / N) : ℝ) : ℂ) * φ r -
              ((2 * (N⁻¹ * deriv sigmaCut (r / N)) : ℝ) : ℂ) * deriv φ r -
              ((N⁻¹ * deriv sigmaCut (r / N) : ℝ) : ℂ) * (φ r / (r : ℂ)) -
              (((r / 2) * (N⁻¹ * deriv sigmaCut (r / N)) : ℝ) : ℂ) * φ r := by
          push_cast
          ring
        rw [hrew]
        have hu1 : ‖(sigmaCut (r / N) : ℂ) * ((n : ℂ) * φ r)‖ ≤ ((n : ℝ) / N) * S₁ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sigmaCut_nonneg _),
            Complex.norm_natCast]
          calc sigmaCut (r / N) * ((n : ℝ) * S₀)
              ≤ (r ^ 2 / N) * ((n : ℝ) * S₀) :=
                mul_le_mul_of_nonneg_right ((sigmaCut_le_one _).trans h1_le_r2N) (by positivity)
            _ = ((n : ℝ) / N) * (r ^ 2 * S₀) := by ring
            _ = ((n : ℝ) / N) * S₁ := by rw [hXφ]
        have hu2 : ‖(((N⁻¹) ^ 2 * deriv (deriv sigmaCut) (r / N) : ℝ) : ℂ) * φ r‖ ≤
            (M₂ / N) * S₀ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
          calc (N⁻¹) ^ 2 * |deriv (deriv sigmaCut) (r / N)| * S₀
              ≤ N⁻¹ * M₂ * S₀ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul hinv_sq (hM₂_bd _) (abs_nonneg _) (inv_pos.2 hN0).le) hS₀
            _ = (M₂ / N) * S₀ := by ring
        have hu3 : ‖((2 * (N⁻¹ * deriv sigmaCut (r / N)) : ℝ) : ℂ) * deriv φ r‖ ≤
            (4 * M₁ / N) * (S₀ + S₂) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_nonneg two_pos.le, abs_of_nonneg (inv_pos.2 hN0).le]
          calc 2 * (N⁻¹ * |deriv sigmaCut (r / N)|) * ‖deriv φ r‖
              ≤ 2 * (N⁻¹ * M₁) * (2 * S₀ + 2 * S₂) :=
                mul_le_mul (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hM₁_bd _) (inv_pos.2 hN0).le) two_pos.le)
                  hdφ_le (norm_nonneg _) (by positivity)
            _ = (4 * M₁ / N) * (S₀ + S₂) := by ring
        have hu4 : ‖((N⁻¹ * deriv sigmaCut (r / N) : ℝ) : ℂ) * (φ r / (r : ℂ))‖ ≤
            (M₁ / N) * S₀ := by
          rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (inv_pos.2 hN0).le, hr_norm]
          have hdiv : S₀ / r ≤ S₀ := div_le_self hS₀ hr1.le
          calc N⁻¹ * |deriv sigmaCut (r / N)| * (S₀ / r)
              ≤ (N⁻¹ * M₁) * S₀ :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hM₁_bd _) (inv_pos.2 hN0).le)
                  hdiv (by positivity) (by positivity)
            _ = (M₁ / N) * S₀ := by ring
        have hu5 : ‖(((r / 2) * (N⁻¹ * deriv sigmaCut (r / N)) : ℝ) : ℂ) * φ r‖ ≤
            (M₁ / N) * S₁ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_nonneg (by positivity), abs_of_nonneg (inv_pos.2 hN0).le]
          have hr_half : r / 2 ≤ r ^ 2 := by nlinarith
          calc r / 2 * (N⁻¹ * |deriv sigmaCut (r / N)|) * S₀
              ≤ r ^ 2 * (N⁻¹ * M₁) * S₀ :=
                mul_le_mul_of_nonneg_right (mul_le_mul hr_half
                  (mul_le_mul_of_nonneg_left (hM₁_bd _) (inv_pos.2 hN0).le)
                  (by positivity) (by positivity)) hS₀
            _ = (M₁ / N) * (r ^ 2 * S₀) := by ring
            _ = (M₁ / N) * S₁ := by rw [hXφ]
        exact outer_zone_bound hN0 hM₁ hM₂ hS₀ hS₁ hS₂ hu1 hu2 hu3 hu4 hu5
  have hDΨ_base :
      Tendsto (fun k => ‖(hDΨ k).toLp (oscillatorD (ψ k)) + (n : ℂ) • oscBasis n‖)
        atTop (𝓝 0) := by
    refine hE2_tendsto.congr fun k => ?_
    congr 1
    rw [hbasis_eq]
    change (hE2_lp k).toLp (fun r => oscillatorD (ψ k) r + (n : ℂ) * φ r) =
      (hDΨ k).toLp (oscillatorD (ψ k)) + (n : ℂ) • (memLp_profFun q).toLp φ
    have hsm : (n : ℂ) • (memLp_profFun q).toLp φ =
        ((memLp_profFun q).const_smul (n : ℂ)).toLp (fun r => (n : ℂ) * φ r) := by
      exact (MemLp.toLp_const_smul (n : ℂ) (memLp_profFun q)).symm
    rw [hsm]
    exact MemLp.toLp_add (hDΨ k) ((memLp_profFun q).const_smul (n : ℂ))
  have hDΨ_conv :
      Tendsto (fun k => ‖(hDΨ k).toLp (oscillatorD (ψ k)) + (n : ℂ) • (hΨ k).toLp (ψ k)‖)
        atTop (𝓝 0) := by
    have hsum := hDΨ_base.add (hΨ_conv.const_mul (n : ℝ))
    rw [mul_zero, add_zero] at hsum
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hsum
    have hsplit : (hDΨ k).toLp (oscillatorD (ψ k)) + (n : ℂ) • (hΨ k).toLp (ψ k) =
        ((hDΨ k).toLp (oscillatorD (ψ k)) + (n : ℂ) • oscBasis n) +
          (n : ℂ) • ((hΨ k).toLp (ψ k) - oscBasis n) := by
      rw [smul_sub]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Complex.norm_natCast]
  exact ⟨ψ, a, b, hΨ, hDΨ, hab, hψ_cd, hψ_lt, hψ_gt, hΨ_conv, hDΨ_conv⟩

/-! ### 5. Pairing against compactly supported radial test functions and scalar Duhamel -/

private theorem setIntegral_Ioi_eq_intervalIntegral_of_supp
    {F : ℝ → ℂ} {a b P_pt Q_pt : ℝ} (ha : 0 < P_pt) (hPa : P_pt < a) (hab : a ≤ b)
    (hbQ : b < Q_pt) (hFa : ∀ r, r < a → F r = 0) (hFb : ∀ r, b < r → F r = 0) :
    ∫ r in Ioi (0 : ℝ), F r = ∫ r in P_pt..Q_pt, F r := by
  have hPQ : P_pt ≤ Q_pt := ((hPa.trans_le hab).trans hbQ).le
  have h1 : ∫ r in Ioi (0 : ℝ), F r = ∫ r, F r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hr0 : r ≤ 0 := not_lt.mp hr
    exact hFa r (lt_of_le_of_lt hr0 (ha.trans hPa))
  have h2 : ∫ r in Ioc P_pt Q_pt, F r = ∫ r, F r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rcases lt_or_ge r a with hra | har
    · exact hFa r hra
    · have hQr : Q_pt < r := by
        by_contra hrQ
        exact hr ⟨lt_of_lt_of_le hPa har, not_lt.mp hrQ⟩
      exact hFb r (hbQ.trans hQr)
  rw [intervalIntegral.integral_of_le hPQ, h1, ← h2]

private theorem inner_toLp_eq_intervalIntegral
    {f g : ℝ → ℂ} (hf : MemLp f 2 xGMeasure) (hg : MemLp g 2 xGMeasure)
    {a b P_pt Q_pt : ℝ} (hP : 0 < P_pt) (hPa : P_pt < a) (hab : a ≤ b) (hbQ : b < Q_pt)
    (hga : ∀ r, r < a → g r = 0) (hgb : ∀ r, b < r → g r = 0) :
    ⟪hg.toLp g, hf.toLp f⟫_ℂ = ∫ r in P_pt..Q_pt, f r * conj (g r) * wC r := by
  rw [← pairing_eq_inner, pairing_toLp]
  have hcongr : ∫ r in Ioi (0 : ℝ), f r * conj (g r) * (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ) =
      ∫ r in Ioi (0 : ℝ), f r * conj (g r) * wC r := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    unfold wC wDens
    rw [radialGaussianWeight_inv]
  rw [hcongr]
  exact setIntegral_Ioi_eq_intervalIntegral_of_supp hP hPa hab hbQ
    (fun r hr => by simp [hga r hr]) (fun r hr => by simp [hgb r hr])

private theorem hasDerivAt_inner_test (P : PlanarData) (hP : IsPlanarReference P)
    {ψ : ℝ → ℂ} {a b : ℝ} (hab : 0 < a ∧ a ≤ b) (hψ : ContDiff ℝ ∞ ψ)
    (hψa : ∀ r, r < a → ψ r = 0) (hψb : ∀ r, b < r → ψ r = 0)
    (hΨ : MemLp ψ 2 xGMeasure) (hDΨ : MemLp (oscillatorD ψ) 2 xGMeasure)
    {v₀ : ℝ} (hv₀ : 0 < v₀) :
    HasDerivAt (fun v => ⟪hΨ.toLp ψ, canonicalCurve P hP v⟫_ℂ)
      (-⟪hΨ.toLp ψ, B0012.L0 (canonicalCurve P hP v₀)⟫_ℂ -
        (v₀ : ℂ)⁻¹ * ⟪hDΨ.toLp (oscillatorD ψ), canonicalCurve P hP v₀⟫_ℂ) v₀ := by
  set P_pt : ℝ := a / 2
  set Q_pt : ℝ := b + 1
  have hPpos : 0 < P_pt := by dsimp [P_pt]; linarith [hab.1]
  have hPa : P_pt < a := by dsimp [P_pt]; linarith [hab.1]
  have hbQ : b < Q_pt := by dsimp [Q_pt]; linarith
  have hPQ : P_pt ≤ Q_pt := ((hPa.trans_le hab.2).trans hbQ).le
  -- Step 1: on `v > 0`, `⟪Ψ, U v⟫ = ∫_{P_pt}^{Q_pt} P.canonical v r * conj (ψ r) * wC r`
  let F : ℝ → ℝ → ℂ := fun v r => P.canonical v r * conj (ψ r) * wC r
  let F' : ℝ → ℝ → ℂ := fun v r => deriv (fun t => P.canonical t r) v * conj (ψ r) * wC r
  have heq_on_pos : ∀ v : ℝ, 0 < v →
      ⟪hΨ.toLp ψ, canonicalCurve P hP v⟫_ℂ = ∫ r in P_pt..Q_pt, F v r := by
    intro v hv
    rw [canonicalCurve_eq_pos P hP hv]
    exact inner_toLp_eq_intervalIntegral (memLp_of_memXG (hP.canonical.memXG v hv)) hΨ
      hPpos hPa hab.2 hbQ hψa hψb
  -- Step 2: differentiate `v ↦ ∫_{P_pt}^{Q_pt} F v r` at `v₀`
  let s_nhd : Set ℝ := Icc (v₀ / 2) (2 * v₀)
  have hs_nhds : s_nhd ∈ 𝓝 v₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  let W2 : ℝ × ℝ → ℂ := fun z => P.canonical z.1 z.2
  have hWsm : ContDiffOn ℝ ∞ W2 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := hP.canonical.smooth
  have hfd : ContinuousOn (fderiv ℝ W2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    hWsm.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hKsub : s_nhd ×ˢ Icc P_pt Q_pt ⊆ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    rintro ⟨v, r⟩ ⟨hv, hr⟩
    exact ⟨lt_of_lt_of_le (half_pos hv₀) hv.1, lt_of_lt_of_le hPpos hr.1⟩
  have hF'_expr : ∀ v ∈ s_nhd, ∀ r ∈ Icc P_pt Q_pt,
      HasDerivAt (fun t => W2 (t, r)) (fderiv ℝ W2 (v, r) (1, 0)) v := by
    intro v hv r hr
    have hpt : (v, r) ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := hKsub ⟨hv, hr⟩
    have hdiff : DifferentiableAt ℝ W2 (v, r) :=
      ((hWsm (v, r) hpt).contDiffAt (hopen.mem_nhds hpt)).differentiableAt (by simp)
    exact hdiff.hasFDerivAt.comp_hasDerivAt v
      (HasDerivAt.prodMk (hasDerivAt_id' v) (hasDerivAt_const v r))
  have hc_ψw : Continuous (fun r : ℝ => conj (ψ r) * wC r) :=
    (Complex.continuous_conj.comp hψ.continuous).mul continuous_wC
  have hG_cont : ContinuousOn
      (fun z : ℝ × ℝ => fderiv ℝ W2 z (1, 0) * (conj (ψ z.2) * wC z.2))
      (s_nhd ×ˢ Icc P_pt Q_pt) :=
    ((hfd.mono hKsub).clm_apply continuousOn_const).mul
      (hc_ψw.comp continuous_snd).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG_cont
  have hv₀_mem : v₀ ∈ s_nhd := ⟨by linarith, by linarith⟩
  have hFv_cont : ∀ v ∈ s_nhd, ContinuousOn (F v) (uIcc P_pt Q_pt) := by
    intro v hv
    rw [uIcc_of_le hPQ]
    have hv_pos : 0 < v := by linarith [hv.1]
    have hslice := ((smoothnessFacts_proof.1 P.canonical hP.canonical.smooth).1 v hv_pos).continuousOn
    exact ((hslice.mono (fun r hr => lt_of_lt_of_le hPpos hr.1)).mul
      (Complex.continuous_conj.comp hψ.continuous).continuousOn).mul continuous_wC.continuousOn
  have hF'v₀_cont : ContinuousOn (F' v₀) (uIcc P_pt Q_pt) := by
    rw [uIcc_of_le hPQ]
    have hslice' := (smoothnessFacts_proof.1 P.canonical hP.canonical.smooth).2 v₀ hv₀
    exact ((hslice'.mono (fun r hr => lt_of_lt_of_le hPpos hr.1)).mul
      (Complex.continuous_conj.comp hψ.continuous).continuousOn).mul continuous_wC.continuousOn
  have hLeib := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := P_pt) (b := Q_pt) (μ := volume) (x₀ := v₀) (s := s_nhd) (bound := fun _ => M)
    hs_nhds
    (by
      filter_upwards [hs_nhds] with v hv
      have hc : ContinuousOn (F v) (uIoc P_pt Q_pt) :=
        (hFv_cont v hv).mono uIoc_subset_uIcc
      exact hc.aestronglyMeasurable measurableSet_uIoc)
    (hFv_cont v₀ hv₀_mem).intervalIntegrable
    ((hF'v₀_cont.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun r hr v hv => by
      rw [uIoc_of_le hPQ] at hr
      have hr_cc : r ∈ Icc P_pt Q_pt := ⟨hr.1.le, hr.2⟩
      have hd_eq : deriv (fun t => P.canonical t r) v = fderiv ℝ W2 (v, r) (1, 0) :=
        (hF'_expr v hv r hr_cc).deriv
      have hrew : F' v r = fderiv ℝ W2 (v, r) (1, 0) * (conj (ψ r) * wC r) := by
        dsimp [F']
        rw [hd_eq, mul_assoc]
      rw [hrew]
      exact hM (v, r) ⟨hv, hr_cc⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun r hr v hv => by
      rw [uIoc_of_le hPQ] at hr
      have hr_cc : r ∈ Icc P_pt Q_pt := ⟨hr.1.le, hr.2⟩
      have hd := hF'_expr v hv r hr_cc
      have hd_eq : deriv (fun t => P.canonical t r) v = fderiv ℝ W2 (v, r) (1, 0) := hd.deriv
      have hmul := (hd.mul_const (conj (ψ r))).mul_const (wC r)
      simpa only [F', hd_eq] using hmul)).2
  -- Step 3: identify `∫ F' v₀` with `-⟪Ψ, L₀(U v₀)⟫ - v₀⁻¹ ⟪DΨ, U v₀⟫`
  have hL0_eq : ⟪hΨ.toLp ψ, B0012.L0 (canonicalCurve P hP v₀)⟫_ℂ =
      ∫ r in P_pt..Q_pt, generatorL0 (P.canonical v₀) r * conj (ψ r) * wC r := by
    have hv₀_cont : ContinuousOn (P.canonical v₀) (Ioi 0) :=
      ((smoothnessFacts_proof.1 P.canonical hP.canonical.smooth).1 v₀ hv₀).continuousOn
    have hL0_ae := (l0ClassicalAe_proof (canonicalCurve P hP v₀) (P.canonical v₀)
      (canonical_ae_canonicalCurve P hP v₀ hv₀) hv₀_cont).1
    have hgen_lp : MemLp (generatorL0 (P.canonical v₀)) 2 xGMeasure :=
      (Lp.memLp (B0012.L0 (canonicalCurve P hP v₀))).ae_eq hL0_ae
    have htoLp_eq : B0012.L0 (canonicalCurve P hP v₀) =
        hgen_lp.toLp (generatorL0 (P.canonical v₀)) := by
      apply Lp.ext
      exact hL0_ae.trans hgen_lp.coeFn_toLp.symm
    rw [htoLp_eq]
    exact inner_toLp_eq_intervalIntegral hgen_lp hΨ hPpos hPa hab.2 hbQ hψa hψb
  have hD_eq : ⟪hDΨ.toLp (oscillatorD ψ), canonicalCurve P hP v₀⟫_ℂ =
      ∫ r in P_pt..Q_pt, oscillatorD (P.canonical v₀) r * conj (ψ r) * wC r := by
    have hosc_a : ∀ r, r < a → oscillatorD ψ r = 0 := by
      intro r hr
      apply oscillatorD_eq_zero_of_eventually
      filter_upwards [Iio_mem_nhds hr] with s hs
      exact hψa s hs
    have hosc_b : ∀ r, b < r → oscillatorD ψ r = 0 := by
      intro r hr
      apply oscillatorD_eq_zero_of_eventually
      filter_upwards [Ioi_mem_nhds hr] with s hs
      exact hψb s hs
    rw [canonicalCurve_eq_pos P hP hv₀,
      inner_toLp_eq_intervalIntegral (memLp_of_memXG (hP.canonical.memXG v₀ hv₀)) hDΨ
        hPpos hPa hab.2 hbQ hosc_a hosc_b]
    let ψc : ℝ → ℂ := fun s => conj (ψ s)
    have hψc : ContDiff ℝ ∞ ψc := Complex.conjCLE.contDiff.comp hψ
    have hψc_P : ψc P_pt = 0 := by simp [ψc, hψa P_pt hPa]
    have hψc_Q : ψc Q_pt = 0 := by simp [ψc, hψb Q_pt hbQ]
    have hdψc_P : deriv ψc P_pt = 0 := by
      have hev : ψc =ᶠ[𝓝 P_pt] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hPa] with s hs
        simp [ψc, hψa s hs]
      rw [hev.deriv_eq, deriv_const]
    have hdψc_Q : deriv ψc Q_pt = 0 := by
      have hev : ψc =ᶠ[𝓝 Q_pt] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds hbQ] with s hs
        simp [ψc, hψb s hs]
      rw [hev.deriv_eq, deriv_const]
    have hg_cd : ContDiffOn ℝ ∞ (P.canonical v₀) (Ioi 0) :=
      (smoothnessFacts_proof.1 P.canonical hP.canonical.smooth).1 v₀ hv₀
    have hibp := interval_ibp hψc hg_cd hPpos hPQ hψc_P hψc_Q hdψc_P hdψc_Q
    have hL : ∫ r in P_pt..Q_pt, P.canonical v₀ r * conj (oscillatorD ψ r) * wC r =
        ∫ r in P_pt..Q_pt, oscillatorD ψc r * P.canonical v₀ r * wC r := by
      apply intervalIntegral.integral_congr
      intro r _
      dsimp [ψc]
      rw [oscillatorD_conj hψ r]
      ring
    have hR : ∫ r in P_pt..Q_pt, ψc r * oscillatorD (P.canonical v₀) r * wC r =
        ∫ r in P_pt..Q_pt, oscillatorD (P.canonical v₀) r * conj (ψ r) * wC r := by
      apply intervalIntegral.integral_congr
      intro r _
      dsimp [ψc]
      ring
    rw [hL, hibp, hR]
  have hint_eq : ∫ r in P_pt..Q_pt, F' v₀ r =
      -⟪hΨ.toLp ψ, B0012.L0 (canonicalCurve P hP v₀)⟫_ℂ -
        (v₀ : ℂ)⁻¹ * ⟪hDΨ.toLp (oscillatorD ψ), canonicalCurve P hP v₀⟫_ℂ := by
    have hg_cd : ContDiffOn ℝ ∞ (P.canonical v₀) (Ioi 0) :=
      (smoothnessFacts_proof.1 P.canonical hP.canonical.smooth).1 v₀ hv₀
    have hgen_cont : ContinuousOn (generatorL0 (P.canonical v₀)) (Ioi 0) :=
      (l0ClassicalAe_proof (canonicalCurve P hP v₀) (P.canonical v₀)
        (canonical_ae_canonicalCurve P hP v₀ hv₀) hg_cd.continuousOn).2
    have hosc_cont : ContinuousOn (oscillatorD (P.canonical v₀)) (Ioi 0) :=
      smoothnessFacts_proof.2 (P.canonical v₀) hg_cd
    have hsub_pos : uIcc P_pt Q_pt ⊆ Ioi 0 := by
      rw [uIcc_of_le hPQ]
      exact fun r hr => lt_of_lt_of_le hPpos hr.1
    have hint1 : IntervalIntegrable
        (fun r => generatorL0 (P.canonical v₀) r * conj (ψ r) * wC r) volume P_pt Q_pt :=
      (((hgen_cont.mono hsub_pos).mul
        (Complex.continuous_conj.comp hψ.continuous).continuousOn).mul
        continuous_wC.continuousOn).intervalIntegrable
    have hint2 : IntervalIntegrable
        (fun r => oscillatorD (P.canonical v₀) r * conj (ψ r) * wC r) volume P_pt Q_pt :=
      (((hosc_cont.mono hsub_pos).mul
        (Complex.continuous_conj.comp hψ.continuous).continuousOn).mul
        continuous_wC.continuousOn).intervalIntegrable
    have hcongr : ∫ r in P_pt..Q_pt, F' v₀ r =
        ∫ r in P_pt..Q_pt, (-(generatorL0 (P.canonical v₀) r * conj (ψ r) * wC r) -
          (v₀ : ℂ)⁻¹ * (oscillatorD (P.canonical v₀) r * conj (ψ r) * wC r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 < r := hsub_pos hr
      have heqn := hP.canonical.equation v₀ hv₀ r hr0
      have hderiv : deriv (fun t => P.canonical t r) v₀ =
          -(generatorL0 (P.canonical v₀) r + (v₀ : ℂ)⁻¹ * oscillatorD (P.canonical v₀) r) := by
        linear_combination -heqn
      dsimp [F']
      rw [hderiv]
      ring
    have hint1_neg : IntervalIntegrable
        (fun r => -(generatorL0 (P.canonical v₀) r * conj (ψ r) * wC r)) volume P_pt Q_pt :=
      hint1.neg
    have hint2_mul : IntervalIntegrable
        (fun r => (v₀ : ℂ)⁻¹ * (oscillatorD (P.canonical v₀) r * conj (ψ r) * wC r))
        volume P_pt Q_pt :=
      hint2.const_mul _
    rw [hcongr, intervalIntegral.integral_sub hint1_neg hint2_mul,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, hL0_eq, hD_eq]
  rw [← hint_eq]
  refine hLeib.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hv₀] with v hv
  exact heq_on_pos v hv

private theorem coeff_duhamel_canonicalCurve (P : PlanarData) (hP : IsPlanarReference P)
    (n : ℕ) {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    ⟪oscBasis n, canonicalCurve P hP θ⟫_ℂ =
      expMult (Real.log θ' - Real.log θ) n * ⟪oscBasis n, canonicalCurve P hP θ'⟫_ℂ +
        ∫ v in θ..θ', expMult (Real.log v - Real.log θ) n *
          ⟪oscBasis n, B0012.L0 (canonicalCurve P hP v)⟫_ℂ := by
  let U := canonicalCurve P hP
  have hUc : ContinuousOn U (Icc θ θ') :=
    (continuousOn_canonicalCurve P hP).mono (fun v hv => lt_of_lt_of_le hθ hv.1)
  obtain ⟨ψ, a, b, hΨ, hDΨ, hab, hψ_cd, hψ_lt, hψ_gt, hΨ_conv, hDΨ_conv⟩ :=
    exists_oscBasis_approx n
  let Ψ : ℕ → XG := fun k => (hΨ k).toLp (ψ k)
  let DΨ : ℕ → XG := fun k => (hDΨ k).toLp (oscillatorD (ψ k))
  let R : ℕ → XG := fun k => DΨ k + (n : ℂ) • Ψ k
  -- For each `k`, integrate the scalar ODE on `[θ, θ']`
  have hlog : ContinuousOn (fun v : ℝ => Real.log v) (Icc θ θ') :=
    ContinuousOn.log continuousOn_id (fun v hv => (lt_of_lt_of_le hθ hv.1).ne')
  have hwc : ContinuousOn (fun v : ℝ => ((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ))
      (Icc θ θ') :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlog))
  have hvinv : ContinuousOn (fun v : ℝ => (v : ℂ)⁻¹) (Icc θ θ') :=
    ContinuousOn.inv₀ Complex.continuous_ofReal.continuousOn
      (fun v hv => Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hθ hv.1).ne')
  have h_approx_duhamel : ∀ k : ℕ,
      ⟪Ψ k, U θ⟫_ℂ = expMult (Real.log θ' - Real.log θ) n * ⟪Ψ k, U θ'⟫_ℂ +
        ∫ v in θ..θ', expMult (Real.log v - Real.log θ) n *
          (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ) := by
    intro k
    have hL0c : ContinuousOn (fun v => ⟪Ψ k, B0012.L0 (U v)⟫_ℂ) (Icc θ θ') :=
      (innerSL ℂ (Ψ k)).continuous.comp_continuousOn (B0012.L0.continuous.comp_continuousOn hUc)
    have hRc : ContinuousOn (fun v => ⟪R k, U v⟫_ℂ) (Icc θ θ') :=
      (innerSL ℂ (R k)).continuous.comp_continuousOn hUc
    have hgc : ContinuousOn (fun v : ℝ =>
        -(((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) *
          (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ))) (Icc θ θ') :=
      (hwc.mul (hL0c.add (hvinv.mul hRc))).neg
    have hG : ∀ v ∈ uIcc θ θ',
        HasDerivAt (fun u : ℝ => ((Real.exp (-(n : ℝ) * Real.log u) : ℝ) : ℂ) * ⟪Ψ k, U u⟫_ℂ)
          (-(((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) *
            (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ))) v := by
      intro v hv
      rw [uIcc_of_le hθθ'] at hv
      have hvpos : 0 < v := lt_of_lt_of_le hθ hv.1
      have hw : HasDerivAt (fun u : ℝ => Real.exp (-(n : ℝ) * Real.log u))
          (Real.exp (-(n : ℝ) * Real.log v) * (-(n : ℝ) * v⁻¹)) v :=
        ((Real.hasDerivAt_log hvpos.ne').const_mul (-(n : ℝ))).exp
      have hc := hasDerivAt_inner_test P hP (hab k) (hψ_cd k) (hψ_lt k) (hψ_gt k)
        (hΨ k) (hDΨ k) hvpos
      refine (hw.ofReal_comp.mul hc).congr_deriv ?_
      have hR_inner : ⟪R k, U v⟫_ℂ = ⟪DΨ k, U v⟫_ℂ + (n : ℂ) * ⟪Ψ k, U v⟫_ℂ := by
        dsimp [R]
        rw [inner_add_left, inner_smul_left, Complex.conj_natCast]
      rw [hR_inner]
      push_cast
      ring
    have hint : IntervalIntegrable (fun v : ℝ =>
        -(((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) *
          (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ))) volume θ θ' := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hθθ']
      exact hgc
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint
    rw [intervalIntegral.integral_neg] at hFTC
    have hGθ : ((Real.exp (-(n : ℝ) * Real.log θ) : ℝ) : ℂ) * ⟪Ψ k, U θ⟫_ℂ =
        ((Real.exp (-(n : ℝ) * Real.log θ') : ℝ) : ℂ) * ⟪Ψ k, U θ'⟫_ℂ +
          ∫ v in θ..θ', ((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) *
            (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ) := by
      linear_combination hFTC
    have hE1 : ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) *
        ((Real.exp (-(n : ℝ) * Real.log θ) : ℝ) : ℂ) = 1 := by
      have h := expMult_log_sub hθ le_rfl n
      rwa [expMult_log_self] at h
    have hE2 : ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) *
        (((Real.exp (-(n : ℝ) * Real.log θ') : ℝ) : ℂ) * ⟪Ψ k, U θ'⟫_ℂ) =
        expMult (Real.log θ' - Real.log θ) n * ⟪Ψ k, U θ'⟫_ℂ := by
      rw [← mul_assoc, expMult_log_sub hθ hθθ' n]
    have hE3 : ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) *
        (∫ v in θ..θ', ((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) *
            (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ)) =
        ∫ v in θ..θ', expMult (Real.log v - Real.log θ) n *
          (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hθθ'] at hv
      dsimp only
      rw [← expMult_log_sub hθ hv.1 n]
      ring
    have hself : ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) *
        (((Real.exp (-(n : ℝ) * Real.log θ) : ℝ) : ℂ) * ⟪Ψ k, U θ⟫_ℂ) = ⟪Ψ k, U θ⟫_ℂ := by
      rw [← mul_assoc, hE1, one_mul]
    rw [← hself, hGθ, mul_add, hE2, hE3]
  -- Pass `k → ∞`
  obtain ⟨M_U', hM_U'⟩ := isCompact_Icc.exists_bound_of_continuousOn hUc.norm
  let M_U : ℝ := max M_U' 0
  have hM_U_nn : 0 ≤ M_U := le_max_right _ _
  have hU_bd : ∀ v ∈ Icc θ θ', ‖U v‖ ≤ M_U := by
    intro v hv
    have h1 := hM_U' v hv
    rw [Real.norm_of_nonneg (norm_nonneg (U v))] at h1
    exact h1.trans (le_max_left _ _)
  have hΨ_lim : Tendsto Ψ atTop (𝓝 (oscBasis n)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hΨ_conv
  have hLHS : Tendsto (fun k => ⟪Ψ k, U θ⟫_ℂ) atTop (𝓝 ⟪oscBasis n, U θ⟫_ℂ) :=
    ((continuous_id.inner continuous_const).tendsto (oscBasis n)).comp hΨ_lim
  have hRHS1 : Tendsto (fun k => expMult (Real.log θ' - Real.log θ) n * ⟪Ψ k, U θ'⟫_ℂ) atTop
      (𝓝 (expMult (Real.log θ' - Real.log θ) n * ⟪oscBasis n, U θ'⟫_ℂ)) :=
    (((continuous_id.inner continuous_const).tendsto (oscBasis n)).comp hΨ_lim).const_mul _
  have hexp_cont : ContinuousOn (fun v : ℝ => expMult (Real.log v - Real.log θ) n) (Icc θ θ') := by
    have h1 : ContinuousOn (fun v : ℝ => Real.log v - Real.log θ) (Icc θ θ') :=
      continuousOn_log_sub (fun v hv => lt_of_lt_of_le hθ hv.1)
    have hmax : ContinuousOn (fun v : ℝ => max (Real.log v - Real.log θ) 0) (Icc θ θ') :=
      continuous_max.comp_continuousOn (h1.prodMk continuousOn_const)
    unfold expMult
    exact Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_neg.comp (hmax.mul continuousOn_const) (mapsTo_univ _ _)))
  have hint_lim : Tendsto (fun k =>
      ∫ v in θ..θ', expMult (Real.log v - Real.log θ) n *
        (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ))
      atTop
      (𝓝 (∫ v in θ..θ', expMult (Real.log v - Real.log θ) n *
        ⟪oscBasis n, B0012.L0 (U v)⟫_ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    let err : ℕ → ℝ := fun k =>
      (θ' - θ) * (‖Ψ k - oscBasis n‖ * (‖B0012.L0‖ * M_U) + θ⁻¹ * ‖R k‖ * M_U)
    have herr0 : Tendsto err atTop (𝓝 0) := by
      have h1 := hΨ_conv.mul_const (‖B0012.L0‖ * M_U)
      have h2 := (hDΨ_conv.const_mul θ⁻¹).mul_const M_U
      have h3 := (h1.add h2).const_mul (θ' - θ)
      simpa [err] using h3
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) herr0
    have hIk : IntervalIntegrable (fun v => expMult (Real.log v - Real.log θ) n *
        (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ)) volume θ θ' := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hθθ']
      exact hexp_cont.mul
        (((innerSL ℂ (Ψ k)).continuous.comp_continuousOn
          (B0012.L0.continuous.comp_continuousOn hUc)).add
          (hvinv.mul ((innerSL ℂ (R k)).continuous.comp_continuousOn hUc)))
    have hI0 : IntervalIntegrable (fun v => expMult (Real.log v - Real.log θ) n *
        ⟪oscBasis n, B0012.L0 (U v)⟫_ℂ) volume θ θ' := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hθθ']
      exact hexp_cont.mul ((innerSL ℂ (oscBasis n)).continuous.comp_continuousOn
        (B0012.L0.continuous.comp_continuousOn hUc))
    rw [← intervalIntegral.integral_sub hIk hI0]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := ‖Ψ k - oscBasis n‖ * (‖B0012.L0‖ * M_U) + θ⁻¹ * ‖R k‖ * M_U) (fun v hv => ?_)).trans ?_
    · rw [uIoc_of_le hθθ'] at hv
      have hvI : v ∈ Icc θ θ' := ⟨hv.1.le, hv.2⟩
      have hv0 : 0 < v := lt_of_lt_of_le hθ hvI.1
      have hsub_inner : expMult (Real.log v - Real.log θ) n *
            (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ) -
          expMult (Real.log v - Real.log θ) n * ⟪oscBasis n, B0012.L0 (U v)⟫_ℂ =
        expMult (Real.log v - Real.log θ) n *
          (⟪Ψ k - oscBasis n, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ) := by
        rw [inner_sub_left]
        ring
      rw [hsub_inner, norm_mul]
      have hexp_le : ‖expMult (Real.log v - Real.log θ) n‖ ≤ 1 := norm_expMult_le _ _
      have h1 : ‖⟪Ψ k - oscBasis n, B0012.L0 (U v)⟫_ℂ‖ ≤
          ‖Ψ k - oscBasis n‖ * (‖B0012.L0‖ * M_U) := by
        calc ‖⟪Ψ k - oscBasis n, B0012.L0 (U v)⟫_ℂ‖
            ≤ ‖Ψ k - oscBasis n‖ * ‖B0012.L0 (U v)‖ := norm_inner_le_norm _ _
          _ ≤ ‖Ψ k - oscBasis n‖ * (‖B0012.L0‖ * ‖U v‖) :=
              mul_le_mul_of_nonneg_left (B0012.L0.le_opNorm _) (norm_nonneg _)
          _ ≤ ‖Ψ k - oscBasis n‖ * (‖B0012.L0‖ * M_U) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hU_bd v hvI) (norm_nonneg _)) (norm_nonneg _)
      have h2 : ‖(v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ‖ ≤ θ⁻¹ * ‖R k‖ * M_U := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hv0.le]
        have hvinv_le : v⁻¹ ≤ θ⁻¹ := inv_anti₀ hθ hvI.1
        calc v⁻¹ * ‖⟪R k, U v⟫_ℂ‖
            ≤ θ⁻¹ * (‖R k‖ * ‖U v‖) :=
              mul_le_mul hvinv_le (norm_inner_le_norm _ _) (norm_nonneg _) (inv_pos.2 hθ).le
          _ ≤ θ⁻¹ * (‖R k‖ * M_U) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hU_bd v hvI) (norm_nonneg _)) (inv_pos.2 hθ).le
          _ = θ⁻¹ * ‖R k‖ * M_U := by ring
      calc ‖expMult (Real.log v - Real.log θ) n‖ *
            ‖⟪Ψ k - oscBasis n, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ‖
          ≤ 1 * (‖Ψ k - oscBasis n‖ * (‖B0012.L0‖ * M_U) + θ⁻¹ * ‖R k‖ * M_U) :=
            mul_le_mul hexp_le ((norm_add_le _ _).trans (add_le_add h1 h2))
              (norm_nonneg _) zero_le_one
        _ = ‖Ψ k - oscBasis n‖ * (‖B0012.L0‖ * M_U) + θ⁻¹ * ‖R k‖ * M_U := one_mul _
    · rw [abs_of_nonneg (sub_nonneg.2 hθθ'), mul_comm]
  have hRHS := hRHS1.add hint_lim
  have hLHS' : Tendsto (fun k => expMult (Real.log θ' - Real.log θ) n * ⟪Ψ k, U θ'⟫_ℂ +
      ∫ v in θ..θ', expMult (Real.log v - Real.log θ) n *
        (⟪Ψ k, B0012.L0 (U v)⟫_ℂ + (v : ℂ)⁻¹ * ⟪R k, U v⟫_ℂ))
      atTop (𝓝 ⟪oscBasis n, U θ⟫_ℂ) :=
    hLHS.congr h_approx_duhamel
  exact tendsto_nhds_unique hLHS' hRHS

/-! ### 6. Vector Duhamel, `IsMildOnPos`, and `IsCanonicalSolution` -/

private theorem vector_duhamel_canonicalCurve (P : PlanarData) (hP : IsPlanarReference P)
    {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    canonicalCurve P hP θ = expD (Real.log θ' - Real.log θ) (canonicalCurve P hP θ') +
      ∫ v in θ..θ', expD (Real.log v - Real.log θ) (B0012.L0 (canonicalCurve P hP v)) := by
  let U := canonicalCurve P hP
  have hUc : ContinuousOn U (Icc θ θ') :=
    (continuousOn_canonicalCurve P hP).mono (fun v hv => lt_of_lt_of_le hθ hv.1)
  have hF : ContinuousOn (fun v : ℝ => B0012.L0 (U v)) (Icc θ θ') :=
    B0012.L0.continuous.comp_continuousOn hUc
  have hint := intervalIntegrable_expD_log hθ hθθ' hF
  apply ext_inner_basis oscBasis
  intro n
  have hinner : ⟪oscBasis n, ∫ v in θ..θ', expD (Real.log v - Real.log θ) (B0012.L0 (U v))⟫_ℂ =
      ∫ v in θ..θ', ⟪oscBasis n, expD (Real.log v - Real.log θ) (B0012.L0 (U v))⟫_ℂ := by
    have h := (innerSL ℂ (oscBasis n)).intervalIntegral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    exact h.symm
  rw [inner_add_right, hinner, inner_expD]
  simp only [inner_expD]
  exact coeff_duhamel_canonicalCurve P hP n hθ hθθ'

private theorem isMildOnPos_canonicalCurve (P : PlanarData) (hP : IsPlanarReference P) :
    IsMildOnPos (canonicalCurve P hP) := by
  intro θ θ' hθ hθθ'
  let U := canonicalCurve P hP
  have hUc : ContinuousOn U (Icc θ θ') :=
    (continuousOn_canonicalCurve P hP).mono (fun v hv => lt_of_lt_of_le hθ hv.1)
  have hSc : ContinuousOn (fun v => S v θ' (U θ')) (Icc θ θ') :=
    continuousOn_S_left hθ (U θ')
  have hZc : ContinuousOn (fun v => ‖U v - S v θ' (U θ')‖) (Icc θ θ') :=
    (hUc.sub hSc).norm
  have hineq : ∀ s ∈ Icc θ θ',
      ‖U s - S s θ' (U θ')‖ ≤ ‖B0012.L0‖ * ∫ v in s..θ', ‖U v - S v θ' (U θ')‖ := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hθ hs.1
    have hsub : Icc s θ' ⊆ Icc θ θ' := Icc_subset_Icc hs.1 le_rfl
    have hF1 : ContinuousOn (fun v => B0012.L0 (U v)) (Icc s θ') :=
      B0012.L0.continuous.comp_continuousOn (hUc.mono hsub)
    have hF2 : ContinuousOn (fun v => B0012.L0 (S v θ' (U θ'))) (Icc s θ') :=
      B0012.L0.continuous.comp_continuousOn (hSc.mono hsub)
    have hI1 : IntervalIntegrable (fun v => expD (Real.log v - Real.log s) (B0012.L0 (U v)))
        volume s θ' := intervalIntegrable_expD_log hs0 hs.2 hF1
    have hI2 : IntervalIntegrable
        (fun v => expD (Real.log v - Real.log s) (B0012.L0 (S v θ' (U θ')))) volume s θ' :=
      intervalIntegrable_expD_log hs0 hs.2 hF2
    have hcongr : ∫ v in s..θ', expD (Real.log v - Real.log s)
          (B0012.L0 (U v - S v θ' (U θ'))) =
        (∫ v in s..θ', expD (Real.log v - Real.log s) (B0012.L0 (U v))) -
          ∫ v in s..θ', expD (Real.log v - Real.log s) (B0012.L0 (S v θ' (U θ'))) := by
      rw [← intervalIntegral.integral_sub hI1 hI2]
      apply intervalIntegral.integral_congr
      intro v _
      simp only [map_sub]
    have hdiff : U s - S s θ' (U θ') = ∫ v in s..θ', expD (Real.log v - Real.log s)
        (B0012.L0 (U v - S v θ' (U θ'))) := by
      have hvd : U s = expD (Real.log θ' - Real.log s) (U θ') +
          ∫ v in s..θ', expD (Real.log v - Real.log s) (B0012.L0 (U v)) :=
        vector_duhamel_canonicalCurve P hP hs0 hs.2
      rw [hcongr, hvd, S_mild_interval hs0 hs.2 (U θ')]
      abel
    have hbd : ‖∫ v in s..θ', expD (Real.log v - Real.log s)
          (B0012.L0 (U v - S v θ' (U θ')))‖ ≤
        ∫ v in s..θ', ‖B0012.L0‖ * ‖U v - S v θ' (U θ')‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hs.2
      · apply Filter.Eventually.of_forall
        intro v _
        calc ‖expD (Real.log v - Real.log s) (B0012.L0 (U v - S v θ' (U θ')))‖
            ≤ ‖expD (Real.log v - Real.log s)‖ * ‖B0012.L0 (U v - S v θ' (U θ'))‖ :=
              (expD (Real.log v - Real.log s)).le_opNorm _
          _ ≤ 1 * (‖B0012.L0‖ * ‖U v - S v θ' (U θ')‖) :=
              mul_le_mul (norm_expD_le _) (B0012.L0.le_opNorm _) (norm_nonneg _) zero_le_one
          _ = ‖B0012.L0‖ * ‖U v - S v θ' (U θ')‖ := one_mul _
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hs.2]
        exact continuousOn_const.mul (hZc.mono hsub)
    rw [hdiff]
    exact hbd.trans (le_of_eq (intervalIntegral.integral_const_mul _ _))
  have hG := backward_gronwall (norm_nonneg _) hZc (fun _ _ => norm_nonneg _) hineq
  exact sub_eq_zero.1 (norm_eq_zero.1 (hG θ ⟨le_rfl, hθθ'⟩))

private theorem idpow_zero_half_apply (f : (IDpow (((0 : ℕ) : ℝ) / 2)).domain) :
    IDpow (((0 : ℕ) : ℝ) / 2) f = (f : XG) := by
  have h0 : ((0 : ℕ) : ℝ) / 2 = 0 := by norm_num
  apply ext_inner_basis oscBasis
  intro n
  have h1 : (1 + (n : ℝ)) ^ (((0 : ℕ) : ℝ) / 2) = 1 := by rw [h0, Real.rpow_zero]
  rw [inner_IDpow, idMult, h1, Complex.ofReal_one, one_mul]

private theorem isCanonicalSolution_canonicalCurve (P : PlanarData) (hP : IsPlanarReference P) :
    UnforcedLeray.Short.PartI.IsCanonicalSolution (canonicalCurve P hP) := by
  let U := canonicalCurve P hP
  have hMild : IsMildOnPos U := isMildOnPos_canonicalCurve P hP
  have hStrong : IsStrongOnPos U :=
    mildIsStrong UnforcedLeray.Short.PartI.greenEllipticRegularity U hMild
  have hXGj : IsXGjContinuous U :=
    mildSpatialSmoothing UnforcedLeray.Short.PartI.greenEllipticRegularity U hMild
  have hSmoothAll : IsSmoothAllXGj U :=
    strongBootstrap UnforcedLeray.Short.PartI.greenEllipticRegularity U hXGj hStrong
  obtain ⟨U₀, hU₀_eq, hU₀_smooth⟩ := hSmoothAll 0
  have hU_smooth : ContDiffOn ℝ ∞ U (Ioi 0) := by
    refine hU₀_smooth.congr fun θ hθ => ?_
    obtain ⟨h, hid⟩ := hU₀_eq θ hθ
    rw [← hid, idpow_zero_half_apply]
  refine ⟨fun θ hθ => (hStrong θ hθ).choose, hU_smooth, fun θ hθ => ?_⟩
  have hd := (hStrong θ hθ).choose_spec.deriv
  rw [hd, neg_neg]
  rfl

end CanonicalSolutionRepAux

/-- Unconditional standing bridge `HasCanonicalSolutionRep P` (`PartIII-a:T22/2/2/1`):
every `Blueprint.Planar.IsPlanarReference P` lifts via `toLp` to a strong `X_G`-valued canonical
solution `PartI.IsCanonicalSolution V` representing `P.canonical` a.e. on `(0, ∞)`. -/
theorem hasCanonicalSolutionRep_proof :
    ∀ P : UnforcedLeray.Blueprint.Planar.PlanarData,
      UnforcedLeray.Blueprint.Planar.IsPlanarReference P →
        UnforcedLeray.Short.IIIa.T22Sub.HasCanonicalSolutionRep P :=
  fun P hP =>
    ⟨CanonicalSolutionRepAux.canonicalCurve P hP,
      CanonicalSolutionRepAux.isCanonicalSolution_canonicalCurve P hP,
      CanonicalSolutionRepAux.canonical_ae_canonicalCurve P hP⟩

end UnforcedLeray.Short.IIIa.T22Sub
