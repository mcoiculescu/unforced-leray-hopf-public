import UnforcedLeray.Lib.PlanarSectorsB.EulerGroup

/-!
# The whole-plane Duhamel form of the Euler group with respect to the transport (INF12 P7)


§5, Level P, target **P7** (`eulerSemigroup_duhamel_transport`: "mild form with respect to the
transport group"); decision D7 (all evolutions are sector sums at `j = 0`).

Manuscript (`paper/main.tex`): the transport group `T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)` and the bounded
perturbation `𝓛 = -Ω∂_ϑ + A_E`, `A_Ef = -(Kf)·∇E₀` (`eq:st18-t00050`–`t00051`, lines
1228–1245, units `B0062`–`B0064`; generator `eq:st18-t00004`, lines 662–670, unit `B0009`). On
the sector `w(r)e^{inϑ}` the transport is `e^{-inΩ(r)t}` (generator `transportSec M n = -inΩ`)
and `A_E` is `couplingSec hM n` (`Coupling.lean`).

Main declarations (namespace `UnforcedLeray.Planar`):
* `transportExpSec M t n = exp(t(-inΩ))`, `norm_transportExpSec_le` (`≤ 1` for all real `t`:
  the transport is skew-adjoint);
* `transportGroupW M t = ⊕ₙ exp(t(-inΩ))` on `L²_M` (the transport group, sector form):
  `secProf_transportGroupW`, `norm_transportGroupW_le` (`≤ 1`), `transportGroupW_zero`,
  `transportGroupW_add`, `continuous_transportGroupW_apply`;
* `couplingW hM = ⊕ₙ couplingSec hM n` (the bounded perturbation `A_E` on `L²_M`),
  `secProf_couplingW`, `norm_couplingW_le`;
* **`eulerGroupW_eq_duhamel`**: `e^{t𝓛}f = T(t)f + ∫₀ᵗ T(t-τ) A_E e^{τ𝓛}f dτ` in `L²_M`, for all
  `t ∈ ℝ` and `f ∈ L²_M` (hence for `f ∈ 𝒳_{0,M}`: `eulerSemigroup_eq_duhamel`).

The identification of `transportExpSec` with the multiplication by `e^{-inΩ(r)t}`, and of
`transportGroupW` with the differential rotation `f(r, ϑ - Ω(r)t)` on each sector, is in
`TransportFormula.lean` (`coeFn_transportExpSec`, `coeFn_transportGroupW_secEmb`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

/-! ### The transport group -/

/-- The sector transport evolution `exp(t(-inΩ))` (multiplication by `e^{-inΩ(r)t}`). -/
def transportExpSec (M : ℝ) (t : ℝ) (n : ℤ) : ProfL2 M →L[ℂ] ProfL2 M :=
  NormedSpace.exp ((t : ℂ) • transportSec M n)

/-- The transport is isometric-type: `‖exp(t(-inΩ))‖ ≤ 1` for every real `t`. -/
theorem norm_transportExpSec_le (M t : ℝ) (n : ℤ) : ‖transportExpSec M t n‖ ≤ 1 := by
  rcases le_total 0 t with ht | ht
  · exact Infra.norm_exp_skew_le_one (adjoint_transportSec M n) ht
  · have hS : ContinuousLinearMap.adjoint (-transportSec M n) = -(-transportSec M n) := by
      rw [map_neg, adjoint_transportSec]
    have h := Infra.norm_exp_skew_le_one hS (neg_nonneg.2 ht)
    have e : ((-t : ℝ) : ℂ) • (-transportSec M n) = (t : ℂ) • transportSec M n := by
      rw [Complex.ofReal_neg, neg_smul, smul_neg, neg_neg]
    rw [e] at h
    exact h

theorem continuous_transportExpSec (M : ℝ) (n : ℤ) :
    Continuous fun t => transportExpSec M t n :=
  continuous_iff_continuousAt.2 fun s =>
    (Infra.BanachExp.hasDerivAt_exp_smul (transportSec M n) s).1.continuousAt

/-- **The transport group** `T(t) = ⊕ₙ e^{-inΩt}` on `L²_M` (`paper/main.tex` lines 1228–1245,
sector form). -/
def transportGroupW (M : ℝ) (t : ℝ) : L2w M →L[ℂ] L2w M :=
  sectorSum (transportExpSec M t) (norm_transportExpSec_le M t) zero_le_one

theorem secProf_transportGroupW (M t : ℝ) (f : L2w M) (n : ℤ) :
    secProf M n (transportGroupW M t f) = transportExpSec M t n (secProf M n f) :=
  secProf_sectorSum _ _ _ f n

theorem norm_transportGroupW_le (M t : ℝ) : ‖transportGroupW M t‖ ≤ 1 :=
  norm_sectorSum_le _ _ _

theorem transportGroupW_zero (M : ℝ) : transportGroupW M 0 = 1 := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [secProf_transportGroupW, transportExpSec, Complex.ofReal_zero, zero_smul,
    NormedSpace.exp_zero]
  rfl

theorem transportGroupW_add (M s t : ℝ) :
    transportGroupW M (s + t) = transportGroupW M s ∘L transportGroupW M t := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [ContinuousLinearMap.comp_apply, secProf_transportGroupW, secProf_transportGroupW,
    secProf_transportGroupW, transportExpSec, Infra.BanachExp.exp_smul_add]
  rfl

/-- **Strong continuity of the transport group** (Tannery's theorem on the Parseval series, as
in `continuous_eulerGroupW_apply`). -/
theorem continuous_transportGroupW_apply (M : ℝ) (f : L2w M) :
    Continuous fun t => transportGroupW M t f := by
  rw [continuous_iff_continuousAt]
  intro t0
  set p : ℤ → ProfL2 M := fun n => secProf M n f with hp
  have key : ∀ t, ‖transportGroupW M t f - transportGroupW M t0 f‖ ^ 2 =
      ∑' n, ‖transportExpSec M t n (p n) - transportExpSec M t0 n (p n)‖ ^ 2 := by
    intro t
    rw [norm_sq_eq_tsum]
    congr 1
    funext n
    rw [map_sub, secProf_transportGroupW, secProf_transportGroupW]
  have hlim : Tendsto (fun t => ∑' n, ‖transportExpSec M t n (p n) -
      transportExpSec M t0 n (p n)‖ ^ 2) (𝓝 t0) (𝓝 (∑' _ : ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => 2 ^ 2 * ‖p n‖ ^ 2) ?_ ?_ ?_
    · exact (hasSum_norm_sq_secProf f).summable.mul_left _
    · intro n
      have hc' : ContinuousAt (fun t => transportExpSec M t n (p n)) t0 :=
        (continuous_transportExpSec M n).continuousAt.clm_apply continuousAt_const
      have h3 : ContinuousAt
          (fun t => ‖transportExpSec M t n (p n) - transportExpSec M t0 n (p n)‖ ^ 2) t0 :=
        ((hc'.sub (continuousAt_const (y := transportExpSec M t0 n (p n)))).norm).pow 2
      simpa using h3.tendsto
    · refine Eventually.of_forall fun t n => ?_
      have h1 : ‖transportExpSec M t n (p n) - transportExpSec M t0 n (p n)‖ ≤ 2 * ‖p n‖ := by
        calc ‖transportExpSec M t n (p n) - transportExpSec M t0 n (p n)‖
            ≤ ‖transportExpSec M t n (p n)‖ + ‖transportExpSec M t0 n (p n)‖ := norm_sub_le _ _
          _ ≤ 1 * ‖p n‖ + 1 * ‖p n‖ :=
              add_le_add
                (((transportExpSec M t n).le_opNorm _).trans
                  (mul_le_mul_of_nonneg_right (norm_transportExpSec_le M t n) (norm_nonneg _)))
                (((transportExpSec M t0 n).le_opNorm _).trans
                  (mul_le_mul_of_nonneg_right (norm_transportExpSec_le M t0 n) (norm_nonneg _)))
          _ = 2 * ‖p n‖ := by ring
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖transportExpSec M t n (p n) - transportExpSec M t0 n (p n)‖ ^ 2
          ≤ (2 * ‖p n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = 2 ^ 2 * ‖p n‖ ^ 2 := by ring
  rw [tsum_zero] at hlim
  have h2 : Tendsto (fun t => ‖transportGroupW M t f - transportGroupW M t0 f‖) (𝓝 t0)
      (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp (hlim.congr fun t => (key t).symm)
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h
  exact tendsto_iff_norm_sub_tendsto_zero.2 h2

/-! ### The bounded perturbation -/

/-- **The perturbation** `A_Ef = -(Kf)·∇E₀` on `L²_M`, sector form `⊕ₙ couplingSec hM n`
(`paper/main.tex` lines 1228–1245, unit `B0062`, at `j = 0`). -/
def couplingW {M : ℝ} (hM : 1 < M) : L2w M →L[ℂ] L2w M :=
  sectorSum (couplingSec hM) (norm_couplingSec_le hM)
    (mul_nonneg (cplConst_nonneg hM) (norm_nonneg _))

theorem secProf_couplingW {M : ℝ} (hM : 1 < M) (f : L2w M) (n : ℤ) :
    secProf M n (couplingW hM f) = couplingSec hM n (secProf M n f) :=
  secProf_sectorSum _ _ _ f n

theorem norm_couplingW_le {M : ℝ} (hM : 1 < M) : ‖couplingW hM‖ ≤ lsecBound hM :=
  norm_sectorSum_le _ _ _

/-! ### The Duhamel formula -/

/-- Continuity of `τ ↦ T(φ τ)(g τ)` for a strongly continuous, uniformly bounded family `T` and
continuous `g`, `φ`. -/
theorem continuous_apply_of_strong {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : ℝ → E →L[ℂ] E} (hT : ∀ x, Continuous fun s => T s x) {C : ℝ} (hC : ∀ s, ‖T s‖ ≤ C)
    {g : ℝ → E} (hg : Continuous g) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous fun τ => T (φ τ) (g τ) := by
  rw [continuous_iff_continuousAt]
  intro τ0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun τ => ‖g τ - g τ0‖) (𝓝 τ0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hg.tendsto τ0)
  have h2 : Tendsto (fun τ => ‖T (φ τ) (g τ0) - T (φ τ0) (g τ0)‖) (𝓝 τ0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (((hT (g τ0)).comp hφ).tendsto τ0)
  have h3 : Tendsto (fun τ => C * ‖g τ - g τ0‖ + ‖T (φ τ) (g τ0) - T (φ τ0) (g τ0)‖) (𝓝 τ0)
      (𝓝 0) := by
    simpa using (h1.const_mul C).add h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun τ => ?_) h3
  calc ‖T (φ τ) (g τ) - T (φ τ0) (g τ0)‖
      = ‖T (φ τ) (g τ - g τ0) + (T (φ τ) (g τ0) - T (φ τ0) (g τ0))‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ ‖T (φ τ) (g τ - g τ0)‖ + ‖T (φ τ) (g τ0) - T (φ τ0) (g τ0)‖ := norm_add_le _ _
    _ ≤ C * ‖g τ - g τ0‖ + ‖T (φ τ) (g τ0) - T (φ τ0) (g τ0)‖ := by
        gcongr
        exact ((T (φ τ)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))

/-- **P7, the mild form with respect to the transport group** (`paper/main.tex` lines
1228–1245, the bounded-perturbation Duhamel formula, here on the whole of `L²_M`):
`e^{t𝓛}f = T(t)f + ∫₀ᵗ T(t-τ) A_E e^{τ𝓛}f dτ` for every `t ∈ ℝ`. -/
theorem eulerGroupW_eq_duhamel {M : ℝ} (hM : 1 < M) (t : ℝ) (f : L2w M) :
    eulerGroupW hM t f = transportGroupW M t f +
      ∫ τ in (0 : ℝ)..t, transportGroupW M (t - τ) (couplingW hM (eulerGroupW hM τ f)) := by
  have hcont : Continuous fun τ =>
      transportGroupW M (t - τ) (couplingW hM (eulerGroupW hM τ f)) :=
    continuous_apply_of_strong (continuous_transportGroupW_apply M)
      (fun s => norm_transportGroupW_le M s)
      ((couplingW hM).continuous.comp (continuous_eulerGroupW_apply hM f))
      (continuous_const.sub continuous_id)
  apply eq_of_secProf
  intro n
  rw [map_add, ← (secProf M n).intervalIntegral_comp_comm (hcont.intervalIntegrable 0 t),
    secProf_eulerGroupW, secProf_transportGroupW]
  simp only [secProf_transportGroupW, secProf_couplingW, secProf_eulerGroupW]
  rw [expSec_eq_duhamel, ContinuousLinearMap.add_apply]
  congr 1
  set p := secProf M n f
  set A : ℝ → ProfL2 M →L[ℂ] ProfL2 M := fun τ =>
    NormedSpace.exp (((t - τ : ℝ) : ℂ) • transportSec M n) * couplingSec hM n * expSec hM τ n
  have hA : Continuous A := by
    have h1 : Continuous fun τ : ℝ => transportExpSec M (t - τ) n :=
      (continuous_transportExpSec M n).comp (continuous_const.sub continuous_id)
    have h2 : Continuous fun τ : ℝ => expSec hM τ n :=
      continuous_iff_continuousAt.2 fun s =>
        (Infra.BanachExp.hasDerivAt_exp_smul (Lsec hM n) s).1.continuousAt
    exact (h1.mul continuous_const).mul h2
  calc (∫ τ in (0 : ℝ)..t, A τ) p
      = ContinuousLinearMap.apply ℂ (ProfL2 M) p (∫ τ in (0 : ℝ)..t, A τ) := rfl
    _ = ∫ τ in (0 : ℝ)..t, ContinuousLinearMap.apply ℂ (ProfL2 M) p (A τ) :=
        ((ContinuousLinearMap.apply ℂ (ProfL2 M) p).intervalIntegral_comp_comm
          (hA.intervalIntegrable 0 t)).symm
    _ = _ := rfl

/-- The Duhamel form on `𝒳_{0,M}` (values in `L²_M`). -/
theorem eulerSemigroup_eq_duhamel {M : ℝ} (hM : 1 < M) (t : ℝ) (f : X0 hM) :
    (eulerSemigroup hM t f : L2w M) = transportGroupW M t f +
      ∫ τ in (0 : ℝ)..t, transportGroupW M (t - τ)
        (couplingW hM (eulerSemigroup hM τ f : L2w M)) :=
  eulerGroupW_eq_duhamel hM t f

end UnforcedLeray.Planar
