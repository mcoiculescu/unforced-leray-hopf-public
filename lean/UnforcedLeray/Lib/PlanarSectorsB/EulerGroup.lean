import UnforcedLeray.Lib.PlanarSectorsB.SectorSum
import UnforcedLeray.Lib.Semigroups.BanachExp
import UnforcedLeray.Lib.Semigroups.ExpSemigroup
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The sector-sum Euler group on `L²_M` and `𝒳_{0,M}` (INF12 target P7, part 2)


§5, Level P, target **P7** (`eulerSemigroup`, `eulerSemigroup_add`,
`continuous_eulerSemigroup_apply`, the Duhamel form with respect to the transport); decision D7
(the linear evolution is *defined* as `⊕ₙ exp(t𝓛ₙ)`, as in NonUniqueEuler `sectorExp`,

{Semigroup,BanachExp}.lean`).

Manuscript (`paper/main.tex`): the generator `𝓛` of `eq:st18-t00004` (lines 662–670, unit
`B0009`), the transport group `T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)` and its bounded perturbation
(`eq:st18-t00050`–`t00051`, lines 1228–1245, units `B0062`–`B0064`), at `j = 0`, where the
transport is the isometric multiplication `e^{-inΩt}` on sector `n` (scoping note §4, B1);
radial vorticity is stationary (line 1356, unit `B0078`(i); `eq:st18-t00073`, lines 1561–1567,
unit `B0101`), so the evolution preserves `∫ f` and acts on `𝒳_{0,M}` (lines 653–660).

Main declarations (namespace `UnforcedLeray.Planar`):
* `expSec hM t n = exp(t 𝓛ₙ)`, `norm_expSec_le`: `‖exp(t𝓛ₙ)‖ ≤ e^{|t| B_M}` for all `t ∈ ℝ`, `n`;
  `expSec_zero_sector`: `exp(t𝓛₀) = 1`; `expSec_eq_duhamel`: the sector Duhamel formula with
  respect to the transport `-inΩ`;
* `eulerGroupW hM t = ⊕ₙ exp(t𝓛ₙ)` on `L²_M`: `secProf_eulerGroupW`, `eulerGroupW_zero`,
  `eulerGroupW_add` (group law, all `s, t ∈ ℝ`), `norm_eulerGroupW_le`,
  `continuous_eulerGroupW_apply`, `massCLM_eulerGroupW` (mass conservation);
* `eulerSemigroup hM t : X0 hM →L[ℂ] X0 hM` (**P7**), `coe_eulerSemigroup_apply`,
  `eulerSemigroup_zero`, `eulerSemigroup_add`, `norm_eulerSemigroup_le`,
  `continuous_eulerSemigroup_apply`, and the packaged `Infra.ExpSemigroup` `eulerExpSemigroup`.

Not built here (see the report of the block): the dilation conjugacy `𝓛_a = a⁻²J_a𝓛J_a⁻¹`
(B0102) and the identification of `eulerGroupW` with the classical transport-plus-Biot–Savart
evolution of Cartesian data.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

/-! ### Sector exponentials -/

/-- `exp(t 𝓛ₙ)` on the profile space of sector `n`. -/
def expSec {M : ℝ} (hM : 1 < M) (t : ℝ) (n : ℤ) : ProfL2 M →L[ℂ] ProfL2 M :=
  NormedSpace.exp ((t : ℂ) • Lsec hM n)

/-- **Uniform growth bound for all real times**: `‖exp(t𝓛ₙ)‖ ≤ e^{|t| B_M}`. -/
theorem norm_expSec_le {M : ℝ} (hM : 1 < M) (t : ℝ) (n : ℤ) :
    ‖expSec hM t n‖ ≤ Real.exp (|t| * lsecBound hM) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact norm_exp_Lsec_le hM n ht
  · have hS : ContinuousLinearMap.adjoint (-transportSec M n) = -(-transportSec M n) := by
      rw [map_neg, adjoint_transportSec]
    have h := Infra.norm_exp_skew_add_le (K := -couplingSec hM n) hS (neg_nonneg.2 ht)
    have e : ((-t : ℝ) : ℂ) • (-transportSec M n + -couplingSec hM n) = (t : ℂ) • Lsec hM n := by
      rw [Lsec, Complex.ofReal_neg, neg_smul, ← smul_neg, neg_add, neg_neg, neg_neg]
    rw [abs_of_nonpos ht, expSec, ← e]
    refine h.trans (Real.exp_le_exp.2 ?_)
    rw [norm_neg]
    exact mul_le_mul_of_nonneg_left (norm_couplingSec_le hM n) (neg_nonneg.2 ht)

/-- Sector `0` is stationary: `exp(t𝓛₀) = 1`. -/
theorem expSec_zero_sector {M : ℝ} (hM : 1 < M) (t : ℝ) : expSec hM t 0 = 1 := by
  rw [expSec, Lsec_zero, smul_zero, NormedSpace.exp_zero]

theorem expSec_add {M : ℝ} (hM : 1 < M) (s t : ℝ) (n : ℤ) :
    expSec hM (s + t) n = expSec hM s n * expSec hM t n :=
  Infra.BanachExp.exp_smul_add (Lsec hM n) s t

theorem expSec_zero {M : ℝ} (hM : 1 < M) (n : ℤ) : expSec hM 0 n = 1 := by
  rw [expSec, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

/-- **Duhamel with respect to the transport** on sector `n` (`paper/main.tex` line 1245, the
bounded perturbation of the transport group, here sector-wise and exact):
`exp(t𝓛ₙ) = exp(t(-inΩ)) + ∫₀ᵗ exp((t-τ)(-inΩ)) Cₙ exp(τ𝓛ₙ) dτ`. -/
theorem expSec_eq_duhamel {M : ℝ} (hM : 1 < M) (t : ℝ) (n : ℤ) :
    expSec hM t n = NormedSpace.exp ((t : ℂ) • transportSec M n) +
      ∫ τ in (0 : ℝ)..t, NormedSpace.exp (((t - τ : ℝ) : ℂ) • transportSec M n) *
        couplingSec hM n * expSec hM τ n :=
  Infra.BanachExp.exp_add_eq_duhamel (transportSec M n) (couplingSec hM n) t

/-! ### The group on `L²_M` -/

/-- **The sector-sum Euler group** `⊕ₙ exp(t𝓛ₙ)` on `L²_M` (decision D7; defined for all real
`t`, since each `𝓛ₙ` is bounded and the bound `e^{|t|B_M}` is uniform in `n`). -/
def eulerGroupW {M : ℝ} (hM : 1 < M) (t : ℝ) : L2w M →L[ℂ] L2w M :=
  sectorSum (expSec hM t) (norm_expSec_le hM t) (Real.exp_pos _).le

theorem secProf_eulerGroupW {M : ℝ} (hM : 1 < M) (t : ℝ) (f : L2w M) (n : ℤ) :
    secProf M n (eulerGroupW hM t f) = expSec hM t n (secProf M n f) :=
  secProf_sectorSum _ _ _ f n

theorem hasSum_eulerGroupW {M : ℝ} (hM : 1 < M) (t : ℝ) (f : L2w M) :
    HasSum (fun n => secEmb M n (expSec hM t n (secProf M n f))) (eulerGroupW hM t f) :=
  hasSum_sectorSum _ _ _ f

theorem norm_eulerGroupW_le {M : ℝ} (hM : 1 < M) (t : ℝ) :
    ‖eulerGroupW hM t‖ ≤ Real.exp (|t| * lsecBound hM) :=
  norm_sectorSum_le _ _ _

theorem eulerGroupW_zero {M : ℝ} (hM : 1 < M) : eulerGroupW hM 0 = 1 := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [secProf_eulerGroupW, expSec_zero, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.one_apply]

/-- **Group law** `e^{(s+t)𝓛} = e^{s𝓛} e^{t𝓛}` for all real `s, t`. -/
theorem eulerGroupW_add {M : ℝ} (hM : 1 < M) (s t : ℝ) :
    eulerGroupW hM (s + t) = eulerGroupW hM s ∘L eulerGroupW hM t := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [ContinuousLinearMap.comp_apply, secProf_eulerGroupW, secProf_eulerGroupW,
    secProf_eulerGroupW, expSec_add, ContinuousLinearMap.mul_apply]

/-- **Strong continuity**: `t ↦ e^{t𝓛} f` is continuous on `ℝ` (Tannery's theorem on the
Parseval series, since each sector exponential is norm continuous and the sector norms are
summable). -/
theorem continuous_eulerGroupW_apply {M : ℝ} (hM : 1 < M) (f : L2w M) :
    Continuous fun t => eulerGroupW hM t f := by
  rw [continuous_iff_continuousAt]
  intro t0
  set p : ℤ → ProfL2 M := fun n => secProf M n f with hp
  have key : ∀ t, ‖eulerGroupW hM t f - eulerGroupW hM t0 f‖ ^ 2 =
      ∑' n, ‖expSec hM t n (p n) - expSec hM t0 n (p n)‖ ^ 2 := by
    intro t
    rw [norm_sq_eq_tsum]
    congr 1
    funext n
    rw [map_sub, secProf_eulerGroupW, secProf_eulerGroupW]
  set K : ℝ := Real.exp ((|t0| + 1) * lsecBound hM) with hK
  have hB := lsecBound_nonneg hM
  have hlim : Tendsto (fun t => ∑' n, ‖expSec hM t n (p n) - expSec hM t0 n (p n)‖ ^ 2)
      (𝓝 t0) (𝓝 (∑' _ : ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n => (2 * K) ^ 2 * ‖p n‖ ^ 2) ?_ ?_ ?_
    · exact (hasSum_norm_sq_secProf f).summable.mul_left _
    · intro n
      have hc : ContinuousAt (fun t => expSec hM t n) t0 :=
        (Infra.BanachExp.hasDerivAt_exp_smul (Lsec hM n) t0).1.continuousAt
      have hc' : ContinuousAt (fun t => expSec hM t n (p n)) t0 :=
        hc.clm_apply continuousAt_const
      have h3 : ContinuousAt (fun t => ‖expSec hM t n (p n) - expSec hM t0 n (p n)‖ ^ 2) t0 :=
        ((hc'.sub (continuousAt_const (y := expSec hM t0 n (p n)))).norm).pow 2
      have h2 := h3.tendsto
      simpa using h2
    · filter_upwards [Metric.ball_mem_nhds t0 one_pos] with t ht n
      have hd : |t - t0| < 1 := by
        have := Metric.mem_ball.1 ht
        rwa [Real.dist_eq] at this
      have hta : |t| ≤ |t0| + 1 := by
        have := abs_sub_abs_le_abs_sub t t0
        linarith
      have hE : ∀ s : ℝ, |s| ≤ |t0| + 1 → ‖expSec hM s n‖ ≤ K := fun s hs =>
        (norm_expSec_le hM s n).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hs hB))
      have h1 : ‖expSec hM t n (p n) - expSec hM t0 n (p n)‖ ≤ 2 * K * ‖p n‖ := by
        calc ‖expSec hM t n (p n) - expSec hM t0 n (p n)‖
            ≤ ‖expSec hM t n (p n)‖ + ‖expSec hM t0 n (p n)‖ := norm_sub_le _ _
          _ ≤ ‖expSec hM t n‖ * ‖p n‖ + ‖expSec hM t0 n‖ * ‖p n‖ :=
              add_le_add ((expSec hM t n).le_opNorm _) ((expSec hM t0 n).le_opNorm _)
          _ ≤ K * ‖p n‖ + K * ‖p n‖ := by
              gcongr
              · exact hE t hta
              · exact hE t0 (by linarith)
          _ = 2 * K * ‖p n‖ := by ring
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖expSec hM t n (p n) - expSec hM t0 n (p n)‖ ^ 2 ≤ (2 * K * ‖p n‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = (2 * K) ^ 2 * ‖p n‖ ^ 2 := by ring
  rw [tsum_zero] at hlim
  have h2 : Tendsto (fun t => ‖eulerGroupW hM t f - eulerGroupW hM t0 f‖) (𝓝 t0) (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp (hlim.congr fun t => (key t).symm)
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h
  exact tendsto_iff_norm_sub_tendsto_zero.2 h2

/-- **Mass conservation**: `∫ e^{t𝓛} f = ∫ f` (only sector `0` carries mass, and it is
stationary: `paper/main.tex` lines 1356 and 1561–1567). -/
theorem massCLM_eulerGroupW {M : ℝ} (hM : 1 < M) (t : ℝ) (f : L2w M) :
    massCLM hM (eulerGroupW hM t f) = massCLM hM f := by
  rw [massCLM_eq_secEmb_zero hM (eulerGroupW hM t f), massCLM_eq_secEmb_zero hM f,
    secProf_eulerGroupW, expSec_zero_sector, ContinuousLinearMap.one_apply]

theorem eulerGroupW_mem_X0 {M : ℝ} (hM : 1 < M) (t : ℝ) (f : L2w M) (hf : f ∈ X0 hM) :
    eulerGroupW hM t f ∈ X0 hM := by
  have hf' : massCLM hM f = 0 := hf
  show massCLM hM (eulerGroupW hM t f) = 0
  rw [massCLM_eulerGroupW, hf']

/-! ### The group on `𝒳_{0,M}` -/

/-- **P7.** The Euler evolution `e^{t𝓛} = ⊕ₙ exp(t𝓛ₙ)` on `𝒳_{0,M} = {f ∈ L²_M : ∫ f = 0}`
(`paper/main.tex` lines 653–670 at `j = 0`; decision D7). -/
def eulerSemigroup {M : ℝ} (hM : 1 < M) (t : ℝ) : X0 hM →L[ℂ] X0 hM :=
  Infra.ExpSemigroup.restrictOp (eulerGroupW hM t) (X0 hM) (eulerGroupW_mem_X0 hM t)

@[simp] theorem coe_eulerSemigroup_apply {M : ℝ} (hM : 1 < M) (t : ℝ) (f : X0 hM) :
    (eulerSemigroup hM t f : L2w M) = eulerGroupW hM t f := rfl

theorem eulerSemigroup_zero {M : ℝ} (hM : 1 < M) : eulerSemigroup hM 0 = 1 := by
  ext1 f
  apply Subtype.ext
  rw [coe_eulerSemigroup_apply, eulerGroupW_zero, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.one_apply]

/-- **P7, group law** (`eulerSemigroup_add`), for all real `s, t` (in particular `s, t ≥ 0`). -/
theorem eulerSemigroup_add {M : ℝ} (hM : 1 < M) (s t : ℝ) :
    eulerSemigroup hM (s + t) = eulerSemigroup hM s * eulerSemigroup hM t := by
  ext1 f
  apply Subtype.ext
  rw [coe_eulerSemigroup_apply, eulerGroupW_add, ContinuousLinearMap.mul_apply,
    coe_eulerSemigroup_apply, coe_eulerSemigroup_apply, ContinuousLinearMap.comp_apply]

theorem norm_eulerSemigroup_le {M : ℝ} (hM : 1 < M) (t : ℝ) :
    ‖eulerSemigroup hM t‖ ≤ Real.exp (|t| * lsecBound hM) :=
  (Infra.ExpSemigroup.norm_restrictOp_le _ _ _).trans (norm_eulerGroupW_le hM t)

/-- **P7, strong continuity** (`continuous_eulerSemigroup_apply`). -/
theorem continuous_eulerSemigroup_apply {M : ℝ} (hM : 1 < M) (f : X0 hM) :
    Continuous fun t => eulerSemigroup hM t f :=
  (continuous_eulerGroupW_apply hM (f : L2w M)).subtype_mk _

/-- The sector profiles of `e^{t𝓛} f` are `exp(t𝓛ₙ) f_n`. -/
theorem secProf_eulerSemigroup {M : ℝ} (hM : 1 < M) (t : ℝ) (f : X0 hM) (n : ℤ) :
    secProf M n (eulerSemigroup hM t f : L2w M) = expSec hM t n (secProf M n f) :=
  secProf_eulerGroupW hM t f n

/-- The Euler evolution on `𝒳_{0,M}` as an exponentially bounded strongly continuous semigroup
(`Infra.ExpSemigroup`, INF07 T7.1), with `‖e^{t𝓛}‖ ≤ e^{B_M t}`. -/
def eulerExpSemigroup {M : ℝ} (hM : 1 < M) : Infra.ExpSemigroup (X0 hM) where
  T := eulerSemigroup hM
  T_zero := eulerSemigroup_zero hM
  T_add s t _ _ := by
    rw [eulerSemigroup_add]
    rfl
  T_cont x := (continuous_eulerSemigroup_apply hM x).continuousOn
  M := 1
  ω := lsecBound hM
  M_nonneg := zero_le_one
  T_le t ht := by
    rw [one_mul, mul_comm]
    have h := norm_eulerSemigroup_le hM t
    rwa [abs_of_nonneg ht] at h

end UnforcedLeray.Planar
