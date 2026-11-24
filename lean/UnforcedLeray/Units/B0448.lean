import UnforcedLeray.Units.B0448.Norm
import UnforcedLeray.Units.B0448.Symbol
import UnforcedLeray.Units.B0448.Fundamental
import UnforcedLeray.Units.B0448.Representation
import UnforcedLeray.Units.B0448.Distribution

/-!
# B0448 `eq:free-stress-22`: the causal resolvent kernel


manuscript `paper/main.tex` lines 7663–7680:

> Choose a time cutoff equal to one near zero and set `H = χW`. The right side
> `F = (∂_t − Δ_z + 1)H` has the same bound. The causal inverse kernel is
> `K(t,z) = 1_{t>0} e^{-t} H_t(z)`. It belongs to `L^{q'}` precisely when `q > 5/2`, because
> `‖K‖_{L^{q'}}^{q'} = C ∫_0^∞ e^{-q't} t^{-3(q'-1)/2} dt` (eq:free-stress-22). The identity
> `H = K*F` is distributionally valid. Its uniqueness follows, for example, because the Fourier
> symbol `iω + |ξ|² + 1` has no real zero.

Every assertion is proved (no hypotheses beyond the manuscript's). Modules:

| Claim | Module | Declarations |
|---|---|---|
| `K(t,z) = 1_{t>0} e^{-t} H_t(z)` | `B0448/Norm` | `kernel` (= drafted `Gaussian.causalKernel 3`), `kernel_of_pos`, `kernel_of_nonpos` |
| eq:free-stress-22 | `B0448/Norm` | `lintegral_rpow_kernel`, `eLpNorm_rpow_kernel`, `normConst_pos` |
| `K ∈ L^{q'}` iff `q > 5/2` | `B0448/Norm` | `memLp_kernel_iff`, `eLpNorm_kernel_lt_top_iff` |
| symbol without real zero | `B0448/Symbol` | `resolventOp`, `symbolT`, `one_le_re_symbolT`, `fourier_resolventOpT` |
| uniqueness | `B0448/Symbol` | `resolventOp_injective` (on `𝓢'`), `eq_of_resolventOp_eq` (on `L^p`) |
| `K` is the causal inverse kernel | `B0448/Fundamental` | `integral_kerC_mul_cexp`, `integral_kerC_sub_mul_resolventOpT` |
| `H = K * F` (tested in `𝓢'`) | `B0448/Representation` | `kernelConv`, `ae_eq_kernelConv` |
| `H = K * F` (tested against `C_c^∞`) | `B0448/Distribution` | `resolventOp_eq_of_compactSupport`, `ae_eq_kernelConv_of_compactSupport` |

Conventions. Space-time is `ST = WithLp 2 (ℝ × ℝ³)` (time first) for the distributional part,
and `ℝ × ℝ³` for the norm computation; `kerC = K ∘ ofLp` transports `K`. The operator
`resolventOp T = ∂_t T − Σ_i ∂_{z_i}² T + T` acts on Mathlib's tempered distributions
`𝓢'(ST, ℂ)`; `L^p` functions enter through `Lp.toTemperedDistribution`. "Distributionally" is
the manuscript's hypothesis `F = (∂_t − Δ_z + 1)H` tested against `C_c^∞` functions (compactly
supported Schwartz functions `φ`, with `Lᵗφ = −∂_tφ − Δ_zφ + φ`); `resolventOp_eq_of_compactSupport`
upgrades it to `𝓢'`, where the symbol argument runs. `q' = q/(q-1)` is encoded by
`q.HolderConjugate q'` (`1 < q < ∞`). The theorem holds for every `H, F ∈ L^q`; the manuscript's
compact time support of `H = χW` is not needed.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0448

open MeasureTheory Set
open scoped ENNReal SchwartzMap

/-- **B0448, the whole unit (tex 7663–7680).** For Hölder conjugate `q, q'`:
1. eq:free-stress-22: `‖K‖_{L^{q'}}^{q'} = C ∫_0^∞ e^{-q't} t^{-3(q'-1)/2} dt` with `C > 0`;
2. `K ∈ L^{q'}(ℝ × ℝ³)` iff `q > 5/2`;
3. uniqueness: `∂_t − Δ_z + 1` is injective on tempered distributions;
4. `H = K * F`: if `H, F ∈ L^q(ℝ × ℝ³)` and `F = (∂_t − Δ_z + 1)H` in distributions (against
   every `C_c^∞` test), then `H(X) = ∫ K(X − Y) F(Y) dY` for a.e. `X`. -/
theorem causal_resolvent_kernel {q q' : ℝ} (hqq' : q.HolderConjugate q') :
    (0 < normConst q' ∧
      eLpNorm kernel (ENNReal.ofReal q') volume ^ q' = ENNReal.ofReal (normConst q') *
        ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-q' * t) * t ^ (-(3 * (q' - 1) / 2)))) ∧
    (MemLp kernel (ENNReal.ofReal q') volume ↔ 5 / 2 < q) ∧
    Function.Injective (resolventOp : 𝓢'(ST, ℂ) → 𝓢'(ST, ℂ)) ∧
    (∀ H F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ST),
      (∀ φ : 𝓢(ST, ℂ), HasCompactSupport φ →
        ∫ X, resolventOpT φ X * H X = ∫ X, φ X * F X) →
        (H : ST → ℂ) =ᵐ[volume] kernelConv F) := by
  refine ⟨⟨normConst_pos hqq'.symm.left_pos, eLpNorm_rpow_kernel hqq'.symm.left_pos⟩,
    memLp_kernel_iff hqq', resolventOp_injective, fun H F hHF => ?_⟩
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.2 hqq'.lt.le⟩
  exact ae_eq_kernelConv_of_compactSupport hHF

end UnforcedLeray.B0448
