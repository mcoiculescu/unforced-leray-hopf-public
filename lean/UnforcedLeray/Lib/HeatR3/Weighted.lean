import UnforcedLeray.Lib.HeatR3.Anisotropic
import UnforcedLeray.Lib.ConvIneq.YoungGroup

/-!
# Weighted bounds for the heat flow on the line (INF05 T19, data with moments)


the weighted heat bounds "without Taylor subtraction" of B0181 (tex 2795–2801,
`eq:st18-t00179`) for the initial-data term, and the kernel input of B0180 (tex 2736–2793):

`‖η^m ∂^b_η e^{θ∂²}f‖_{L^p} ≤ Σ_{k ≤ m} C θ^{(k-b)/2} ‖G_{4θ}‖_{L^p} ‖ξ^{m-k}f‖_{L¹}`
(`eLpNorm_pow_mul_iteratedDeriv_lineHeat_le`), and for `θ ≥ 1` the manuscript's power
`‖η^m ∂^b e^{θ∂²}f‖_{L^p} ≤ C θ^{(m-b-1)/2 + 1/(2p)} Σ_{k ≤ m} ‖ξ^k f‖_{L¹}`
(`eLpNorm_pow_mul_iteratedDeriv_lineHeat_le_large`), `1 ≤ p ≤ ∞`.

Proof: `η^m = Σ_k binom(m,k) (η - ξ)^k ξ^{m-k}` under the heat integral
(`pow_mul_iteratedDeriv_lineHeat`), Young's `L^p ⋆ L¹` inequality
(`Conv.eLpNorm_convolution_le_L1`) for each term, and the weighted kernel bound
`‖x^k∂^bG_θ‖_{L^p} ≤ Cθ^{(k-b)/2}‖G_{4θ}‖_{L^p}` (`eLpNorm_pow_mul_iteratedDeriv_lineGauss_le`).

Not built here: the Taylor expansion with remainder of B0180 (`eq:st18-t00176`–`00178`), the
source (Duhamel) part with mixed moments, and the time derivatives `∂_s^ℓ`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real
open scoped ENNReal

/-- The weighted line kernel `x^k ∂^b G_θ(x)`. -/
def wKer (k b : ℕ) (θ : ℝ) (x : ℝ) : ℝ := x ^ k * iteratedDeriv b (lineGauss θ) x

theorem continuous_wKer (k b : ℕ) (θ : ℝ) : Continuous (wKer k b θ) :=
  (continuous_pow k).mul ((contDiff_lineGauss (n := b) θ).continuous_iteratedDeriv b le_rfl)

theorem lineGauss_le {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    lineGauss θ η ≤ (4 * π * θ) ^ (-((1 : ℕ) : ℝ) / 2) := by
  rw [lineGauss_eq]; exact Gaussian.gaussKernel_le hθ _

theorem abs_wKer_le (k b : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ x, |wKer k b θ x| ≤ M := by
  obtain ⟨C, hC0, hC⟩ := abs_pow_mul_iteratedDeriv_lineGauss_le k b
  refine ⟨C * θ ^ (((k : ℝ) - b) / 2) * (4 * π * (4 * θ)) ^ (-((1 : ℕ) : ℝ) / 2), fun x => ?_⟩
  rw [wKer, abs_mul, abs_pow, ← Real.norm_eq_abs (iteratedDeriv b (lineGauss θ) x)]
  refine (hC hθ x).trans ?_
  exact mul_le_mul_of_nonneg_left (lineGauss_le (by positivity) x) (by positivity)

/-- **The binomial expansion under the heat integral.** For `θ > 0` and `f` with
`ξ^k f ∈ L¹`, `k ≤ m`:
`η^m ∂^b e^{θ∂²}f(η) = Σ_{k ≤ m} binom(m,k) ∫ (η-ξ)^k ∂^bG_θ(η-ξ) ξ^{m-k}f(ξ) dξ`. -/
theorem pow_mul_iteratedDeriv_lineHeat {m b : ℕ} {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ}
    (hf : ∀ k ≤ m, Integrable (fun ξ => ξ ^ k * f ξ)) (η : ℝ) :
    η ^ m * iteratedDeriv b (lineHeat θ f) η =
      ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * ∫ ξ, wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ) := by
  have hf0 : Integrable f := by simpa using hf 0 (Nat.zero_le m)
  rw [iteratedDeriv_lineHeat hθ hf0 b]
  simp only
  have hint : ∀ k ∈ Finset.range (m + 1),
      Integrable (fun ξ => (m.choose k : ℝ) * (wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ))) := by
    intro k hk
    obtain ⟨M, hM⟩ := abs_wKer_le k b hθ
    have h1 : Integrable (fun ξ => wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ)) :=
      (hf (m - k) (Nat.sub_le m k)).bdd_mul
        ((continuous_wKer k b θ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        (Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hM _)
    exact h1.const_mul _
  rw [← integral_const_mul]
  have hpt : ∀ ξ, η ^ m * (iteratedDeriv b (lineGauss θ) (η - ξ) * f ξ) =
      ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * (wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ)) := by
    intro ξ
    have hη : η ^ m = ((η - ξ) + ξ) ^ m := by ring_nf
    rw [hη, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [wKer]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]

/-- **INF05 T19, weighted heat bound** (B0181, tex 2795–2801, initial-data term). For every
`m, b` there is `C` such that for `θ > 0`, `f` with `ξ^k f ∈ L¹` (`k ≤ m`) and `1 ≤ p ≤ ∞`:
`‖η^m ∂^b e^{θ∂²}f‖_{L^p} ≤ Σ_{k ≤ m} C θ^{(k-b)/2} ‖G_{4θ}‖_{L^p} ‖ξ^{m-k}f‖_{L¹}`. -/
theorem eLpNorm_pow_mul_iteratedDeriv_lineHeat_le (m b : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {θ : ℝ}, 0 < θ → ∀ {f : ℝ → ℝ}, (∀ k ≤ m, Integrable (fun ξ => ξ ^ k * f ξ)) →
      ∀ {p : ℝ≥0∞}, 1 ≤ p →
        eLpNorm (fun η => η ^ m * iteratedDeriv b (lineHeat θ f) η) p volume ≤
          ∑ k ∈ Finset.range (m + 1), ENNReal.ofReal (C * θ ^ (((k : ℝ) - b) / 2)) *
            eLpNorm (lineGauss (4 * θ)) p volume *
              eLpNorm (fun ξ => ξ ^ (m - k) * f ξ) 1 volume := by
  have hK : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {θ : ℝ}, 0 < θ → ∀ p : ℝ≥0∞,
      eLpNorm (fun η => η ^ k * iteratedDeriv b (lineGauss θ) η) p volume ≤
        ENNReal.ofReal (C * θ ^ (((k : ℝ) - b) / 2)) * eLpNorm (lineGauss (4 * θ)) p volume :=
    fun k => eLpNorm_pow_mul_iteratedDeriv_lineGauss_le k b
  choose Ck hCk0 hCk using hK
  set C := ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * Ck k + 1 with hC
  have hC0 : 0 < C := by
    have : 0 ≤ ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * Ck k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (hCk0 k).le
    linarith
  have hCk_le : ∀ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * Ck k ≤ C := by
    intro k hk
    have : (m.choose k : ℝ) * Ck k ≤ ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * Ck k :=
      Finset.single_le_sum (f := fun k => (m.choose k : ℝ) * Ck k)
        (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hCk0 k).le) hk
    linarith
  refine ⟨C, hC0, fun {θ} hθ {f} hf {p} hp => ?_⟩
  -- the summands
  set T : ℕ → ℝ → ℝ := fun k η =>
    (m.choose k : ℝ) * ∫ ξ, wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ) with hT
  have hrep : (fun η => η ^ m * iteratedDeriv b (lineHeat θ f) η) =
      ∑ k ∈ Finset.range (m + 1), T k := by
    funext η
    rw [pow_mul_iteratedDeriv_lineHeat hθ hf η, Finset.sum_apply]
  have hTmeas : ∀ k ∈ Finset.range (m + 1), AEStronglyMeasurable (T k) volume := by
    intro k hk
    obtain ⟨M, hM⟩ := abs_wKer_le k b hθ
    have hg := hf (m - k) (Nat.sub_le m k)
    have hc : Continuous fun η => ∫ ξ, wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ) :=
      continuous_of_dominated
        (fun η => (((continuous_wKer k b θ).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hg.1)
        (fun η => Eventually.of_forall fun ξ => by
          rw [norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
        (hg.norm.const_mul M)
        (Eventually.of_forall fun ξ =>
          ((continuous_wKer k b θ).comp (continuous_id.sub continuous_const)).mul
            continuous_const)
    exact (continuous_const.mul hc).aestronglyMeasurable
  rw [hrep]
  refine (eLpNorm_sum_le hTmeas hp).trans (Finset.sum_le_sum fun k hk => ?_)
  -- one summand
  have hg := hf (m - k) (Nat.sub_le m k)
  have hconv : eLpNorm (fun η => ∫ ξ, wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ)) p volume ≤
      eLpNorm (fun ξ => ξ ^ (m - k) * f ξ) 1 volume * eLpNorm (wKer k b θ) p volume := by
    have hrep' : (fun η => ∫ ξ, wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ)) =
        fun η => ∫ ξ, (fun ξ => ξ ^ (m - k) * f ξ) (η - ξ) • wKer k b θ ξ :=
      funext fun η => integral_kernel_right_eq _ (fun ξ => ξ ^ (m - k) * f ξ) η
    rw [hrep']
    exact Conv.eLpNorm_convolution_le_L1 (μ := volume) (K := fun ξ => ξ ^ (m - k) * f ξ)
      (f := wKer k b θ) hg.1 (continuous_wKer k b θ).aestronglyMeasurable hp
  have hT : T k = (m.choose k : ℝ) • fun η => ∫ ξ, wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ) :=
    rfl
  rw [hT, eLpNorm_const_smul, Real.enorm_natCast]
  have hw := hCk k hθ p
  calc (m.choose k : ℝ≥0∞) *
        eLpNorm (fun η => ∫ ξ, wKer k b θ (η - ξ) * (ξ ^ (m - k) * f ξ)) p volume
      ≤ (m.choose k : ℝ≥0∞) * (eLpNorm (fun ξ => ξ ^ (m - k) * f ξ) 1 volume *
          (ENNReal.ofReal (Ck k * θ ^ (((k : ℝ) - b) / 2)) *
            eLpNorm (lineGauss (4 * θ)) p volume)) := by
        gcongr
        exact hconv.trans (mul_le_mul_right hw _)
    _ = ENNReal.ofReal ((m.choose k : ℝ) * Ck k * θ ^ (((k : ℝ) - b) / 2)) *
          eLpNorm (lineGauss (4 * θ)) p volume *
            eLpNorm (fun ξ => ξ ^ (m - k) * f ξ) 1 volume := by
        rw [mul_assoc ((m.choose k : ℝ)), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
        ring
    _ ≤ ENNReal.ofReal (C * θ ^ (((k : ℝ) - b) / 2)) *
          eLpNorm (lineGauss (4 * θ)) p volume *
            eLpNorm (fun ξ => ξ ^ (m - k) * f ξ) 1 volume := by
        gcongr
        exact hCk_le k hk

/-- `‖G_t‖_{L^p} = c_p t^{-(1 - 1/p)/2}` as an extended real. -/
theorem eLpNorm_lineGauss_eq {t : ℝ} (ht : 0 < t) (p : ℝ≥0∞) :
    eLpNorm (lineGauss t) p volume = ENNReal.ofReal (Gaussian.derivLpConst 1 0 p *
      t ^ (-((0 : ℕ) : ℝ) / 2 - (1 : ℝ) / 2 * (1 - (1 / p).toReal))) := by
  have h := eLpNorm_iteratedDeriv_lineGauss 0 ht p
  have hfin := (memLp_iteratedDeriv_lineGauss 0 ht p).eLpNorm_ne_top
  rw [iteratedDeriv_zero] at h hfin
  rw [← h, ENNReal.ofReal_toReal hfin]

/-- **INF05 T19, weighted heat bound with the manuscript's power** (B0181, tex 2795–2801,
`eq:st18-t00179`, initial-data term, `ℓ = 0`). For fixed `m, b` and `1 ≤ p ≤ ∞` there is `C`
such that for `θ ≥ 1` and `f` with `ξ^k f ∈ L¹` (`k ≤ m`):
`‖η^m ∂^b e^{θ∂²}f‖_{L^p} ≤ C θ^{(m-b-1)/2 + 1/(2p)} Σ_{k ≤ m} ‖ξ^{m-k}f‖_{L¹}`
(with `1/p = (1/p).toReal`, which is `0` at `p = ∞`). -/
theorem eLpNorm_pow_mul_iteratedDeriv_lineHeat_le_large (m b : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {θ : ℝ}, 1 ≤ θ → ∀ {f : ℝ → ℝ},
      (∀ k ≤ m, Integrable (fun ξ => ξ ^ k * f ξ)) →
        eLpNorm (fun η => η ^ m * iteratedDeriv b (lineHeat θ f) η) p volume ≤
          ENNReal.ofReal (C * θ ^ (((m : ℝ) - b - 1) / 2 + (1 / p).toReal / 2)) *
            ∑ k ∈ Finset.range (m + 1), eLpNorm (fun ξ => ξ ^ (m - k) * f ξ) 1 volume := by
  obtain ⟨C, hC0, hmain⟩ := eLpNorm_pow_mul_iteratedDeriv_lineHeat_le m b
  set cp := Gaussian.derivLpConst 1 0 p
  set e : ℝ := -((0 : ℕ) : ℝ) / 2 - (1 : ℝ) / 2 * (1 - (1 / p).toReal) with he
  have hq : (1 / p).toReal ≤ 1 := by
    have h1 : 1 / p ≤ 1 := by rw [one_div]; exact ENNReal.inv_le_one.mpr hp
    have := ENNReal.toReal_mono ENNReal.one_ne_top h1
    rwa [ENNReal.toReal_one] at this
  have he0 : e ≤ 0 := by
    rw [he]; have := ENNReal.toReal_nonneg (a := 1 / p); push_cast; linarith
  refine ⟨C * |cp| + 1, by positivity, fun {θ} hθ {f} hf => ?_⟩
  have hθ0 : 0 < θ := by linarith
  refine (hmain hθ0 hf hp).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [eLpNorm_lineGauss_eq (by positivity) p, ← ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  -- the scalar inequality
  have h1 : θ ^ (((k : ℝ) - b) / 2) ≤ θ ^ (((m : ℝ) - b) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hθ (by have : (k : ℝ) ≤ m := Nat.cast_le.mpr hk'; linarith)
  have h2 : (4 * θ) ^ e ≤ θ ^ e := Real.rpow_le_rpow_of_nonpos hθ0 (by linarith) he0
  have h3 : θ ^ (((m : ℝ) - b) / 2) * θ ^ e =
      θ ^ (((m : ℝ) - b - 1) / 2 + (1 / p).toReal / 2) := by
    rw [← Real.rpow_add hθ0]; congr 1; rw [he]; push_cast; ring
  have hcp : cp * (4 * θ) ^ e ≤ |cp| * θ ^ e :=
    (mul_le_mul_of_nonneg_right (le_abs_self cp) (Real.rpow_nonneg (by positivity) _)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg cp))
  calc C * θ ^ (((k : ℝ) - b) / 2) * (cp * (4 * θ) ^ e)
      ≤ C * θ ^ (((m : ℝ) - b) / 2) * (|cp| * θ ^ e) := by
        exact (mul_le_mul_of_nonneg_left hcp (by positivity)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC0.le) (by positivity))
    _ = C * |cp| * (θ ^ (((m : ℝ) - b) / 2) * θ ^ e) := by ring
    _ ≤ (C * |cp| + 1) * (θ ^ (((m : ℝ) - b) / 2) * θ ^ e) := by
        gcongr; linarith
    _ = (C * |cp| + 1) * θ ^ (((m : ℝ) - b - 1) / 2 + (1 / p).toReal / 2) := by rw [h3]

end UnforcedLeray.Heat
