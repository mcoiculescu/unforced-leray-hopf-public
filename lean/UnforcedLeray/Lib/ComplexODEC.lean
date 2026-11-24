import UnforcedLeray.Lib.ComplexODEC.Regular
import UnforcedLeray.Lib.ComplexODEC.Mode
import UnforcedLeray.Lib.ComplexODEC.Quadrupole
import UnforcedLeray.Lib.ComplexODEC.Bounds
import UnforcedLeray.Lib.ComplexODEC.O10Tail
import UnforcedLeray.Lib.ComplexODEC.Assembly
import UnforcedLeray.Lib.ComplexODEC.SectorOne
import UnforcedLeray.Lib.ComplexODEC.Velocity

/-!
# Linear ODE with complex parameters, part 3: regularity of the growing mode and the
interface `GaussianGrowingMode` (Wave 3 block 3F PLAN2 part 1: INF18 O9–O15)

Main file of the third INF18 layer of the Lean build plan

targets O9–O15 in `scoping/INF10-INF12-INF18-Planar.md` §5 Level O, bypasses B3 and B4 of §4;
decision D17: `GaussianGrowingMode` is the frozen interface of Proposition
`prop:gaussian-existence`). It builds on `Lib/ComplexODE` (O1–O3), `Lib/ComplexODEB` (O4–O8,
in particular the whole-line mode `Rayleigh.Evans.exists_wholeLine_growing_mode`), the planar
layers `Lib/PlanarSectors` (P1–P5, P9) and `Lib/PlanarSectorsB` (P6–P7), and the helper
`Units/B0034/Radial` (the radial form of the Rayleigh equation). The annular unit
`Units/B0034.lean` itself is not imported: its copies of the Evans drafts clash with
`Lib/ComplexODE`, and `Lib/ComplexODEB` already contains its content (O4–O7).

Manuscript: `paper/main.tex` lines 962--982 (Proposition `prop:gaussian-existence`, blueprint
unit B0058) and 1128--1192 (§`sec:st18-1294`, units B0051--B0057).

| Target | Module | Main declarations |
|---|---|---|
| O12 regular solution in `s = r²` (B4) | `Regular`, `Mode` | `avgPow`, `contDiff_avgPow`, `regSol`, `regSol_eq`, `contDiff_regSol`, `regSol_ode`, **`exists_regular_solution`**; `kappa`, `regB`, `regLog`, `isSolOn_regLog`, **`exists_mode_eq_regLog`**, `modeRadial_eq` |
| O9 Green representation (B3) | `Mode` | `WholeLineData`, `modeRadial`, `modeVort`, `wprof_modeVort`, `isRadialPoissonSol_modeRadial`, **`mode_eq_green`** |
| O10 endpoint orders, far field | `Quadrupole`, `O10Tail` | **`modeRadial_orders_zero`**, **`tendsto_sq_mul_modeRadial`**, **`exists_norm_iteratedDeriv_modeRadial_asymptotic_remainder_bound`** |
| O11 nonzero quadrupole (B3) | `Quadrupole` | `modeQuadrupole`, `norm_modeRadial_le_half`, **`modeQuadrupole_ne_zero`**, `farField_ne_zero` |
| O13 no nonreal modes at `n = 1` (B3) | `SectorOne` | `pot1`, `sol1`, `isSolOn_sol1`, `norm_mul_Phi_one_le`, **`sector_one_eigen_eq_zero`** |
| O14 Gaussian derivative bounds | `Bounds` | `DerivBoundUpTo`, `DerivBoundUpTo.mul`, `derivBound_kappa`, `regB_iteratedDeriv_add_two`, `derivBound_regB`, `modeQ`, `modeQ_eq`, **`contDiff_modeQ`**, **`norm_iteratedFDeriv_modeQ_le`** |
| O15 assembly (D17) | `Assembly`, `Velocity`, this file | `memLp_modeVort_profile`, `memLp_modeVort_XG`, `memLp_modeQ_wMeasure`, `integral_modeQ`, `Lsec_modeVort`, `L0_modeVort`, `Lsec_conj_modeVort`, `modeStream`, `norm_fderiv_modeStream_le`, `memLp_fderiv_modeStream`, **`Planar.GaussianGrowingMode`**, **`Planar.exists_gaussianGrowingMode`** |

Deviations from the scoping signatures (§5 of the scoping note):
* O12: `exists_regular_solution` is a real-variable statement: for every smooth coefficient
  the regular equation `4(s b'' + 3 b') = a b`, `b(0) = 1`, has a `C^∞` solution on all of
  `ℝ` (Volterra equation, Picard iteration with factorial bounds, smoothness bootstrap), in
  place of a holomorphic solution on a small disc. `mode_eq_regular_near_zero` becomes the
  global identity `exists_mode_eq_regLog` (`F(t) = β₀ e^{2t} b(e^{2t})` for all `t`), proved
  by a Wronskian at `t → -∞` and uniqueness for `F'' = V F`; it needs no endpoint orders.
* O9 is stated for the radial profile `φ = F ∘ log` of a `WholeLineData c F` (the output of
  O8), with `greenN 2` of the vorticity `h = κ_c(r²) φ`.
* O10 gives the orders at `0⁺`, the far-field limit, and the radial Gaussian remainder bounds.
  `O10Tail` proves that every radial derivative of both `r²φ + 𝔐/4` and
  `φ + (𝔐/4)r⁻²` is bounded on `r≥1` by a polynomial times the sharp `exp(-r²/4)`
  envelope, from the actual `WholeLineData` supplied by O8.
* O14 is proved for `q`; the same bounds for `U_G h_X` (the adjoint eigenfunction) are
  **not proved**.
* O15: "`Kq ∈ L²`" is recorded for the streamfunction `Ψ = φ e^{2iϑ}` (`Ψ` smooth,
  `‖∇Ψ(y)‖ ≤ K (1+|y|)^{-3}`, `∇Ψ ∈ L²(ℝ²)`, tex line 1181); the identification of the
  Biot–Savart velocity `Kq` with `∇^⊥Ψ` is target P8 and is **not proved**.

* O13 is stated for `n = 1` only (`Lsec hM 1`); `n = -1` follows by conjugation and is not
  restated.

Status: a draft; every listed declaration compiles. Theorem A is not proved, and the audit items

-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK)

/-- **The growing Gaussian mode** (Proposition `prop:gaussian-existence`, tex lines 962--982,
blueprint unit B0058; scoping target O15, decision D17).

Data: the phase speed `c`, the radial streamfunction `φ`, the vorticity profile
`h = Δ₂φ = kφ/(Ω - c)` and the mode `q = h(r) e^{2iϑ}` on `ℂ = ℝ²`; the eigenvalue is
`λ = -2ic = γ + iω`. Fields:
* speeds and growth rate: `Im c > 0`, `0 < Re c < 1`, `γ > 0`, `-2 < ω < 0` (tex lines
  963, 969--970, eq. `st18-t00042`);
* the radial mode: `φ` smooth on `(0, ∞)`, `(Ω - c)Δ₂φ - kφ = 0`, nonzero, regular and
  decaying (`φ → 0` at `0⁺` and `∞`, `φ = O(r²)`, `φ' = O(r)` at `0⁺`), `φ = R h` (tex lines
  964--966, 1145--1153, 1181--1183);
* far field and quadrupole: `r²φ → -𝔐/4`, `𝔐 = ∫₀^∞ r³ h ≠ 0` (tex lines 971, 1150,
  eq. `st18-t00047`);
* the mode: `q = ofProfile 2 h` is `C^∞`, all its derivatives are bounded by a polynomial
  times `e^{-|y|²/4}`, `q ≠ 0`, `q` is integrable and `∫ q = 0` (tex lines 971--976, 1187);
* spaces: `q ∈ L²_M` and `h ∈ L²(⟨r⟩^{2M} 2πr dr)` for every `M`, `h ∈ X_G` (tex lines
  977--978);
* eigenvalue equations: `L₀ h = λ h` on `X_G` and `𝓛₂ h = λ h` on every sector profile space
  `L²_M`, `M > 1` (tex lines 968--969, 1188--1189); the conjugate profile is a sector `-2`
  eigenvector with eigenvalue `λ̄` (tex lines 979--980);
* velocity: the streamfunction `Ψ = φ e^{2iϑ}` is `C^∞`, `‖∇Ψ(y)‖ ≤ K(1+|y|)^{-3}` and
  `∇Ψ ∈ L²(ℝ²)` (tex lines 977, 1181); `∇^⊥Ψ` is the velocity of `q` once P8 identifies it
  with the Biot–Savart convolution. -/
structure GaussianGrowingMode where
  /-- The phase speed. -/
  c : ℂ
  /-- The radial streamfunction `φ`. -/
  φ : ℝ → ℂ
  /-- The vorticity profile `h = Δ₂φ = kφ/(Ω - c)`. -/
  h : ℝ → ℂ
  /-- The mode `q = h(r) e^{2iϑ}` on `ℂ = ℝ²`. -/
  q : ℂ → ℂ
  im_pos : 0 < c.im
  re_pos : 0 < c.re
  re_lt_one : c.re < 1
  growth_pos : 0 < (-2 * Complex.I * c).re
  freq_gt : -2 < (-2 * Complex.I * c).im
  freq_lt : (-2 * Complex.I * c).im < 0
  φ_smooth : ContDiffOn ℝ ∞ φ (Ioi 0)
  φ_rayleigh : ∀ r : ℝ, 0 < r →
    ((radialOmega r : ℂ) - c) * B0034.radialDelta2 φ r - (radialK r : ℂ) * φ r = 0
  φ_ne_zero : ∃ r : ℝ, 0 < r ∧ φ r ≠ 0
  φ_tendsto_zero : Tendsto φ (𝓝[>] 0) (𝓝 0)
  φ_tendsto_atTop : Tendsto φ atTop (𝓝 0)
  φ_orders_zero : ∃ C : ℝ, ∀ r ∈ Ioc (0 : ℝ) 1, ‖φ r‖ ≤ C * r ^ 2 ∧ ‖deriv φ r‖ ≤ C * r
  h_mul : ∀ r : ℝ, h r * ((radialOmega r : ℂ) - c) = (radialK r : ℂ) * φ r
  φ_eq_green : ∀ r : ℝ, 0 < r → φ r = greenN 2 h r
  far_field : Tendsto (fun r : ℝ => (r : ℂ) ^ 2 * φ r) atTop
    (𝓝 (-(1 / 4) * ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 3 * h r))
  quadrupole_ne_zero : ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 3 * h r ≠ 0
  q_eq : q = NUE.Ang.ofProfile 2 h
  q_smooth : ContDiff ℝ ∞ q
  q_bound : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
    ‖iteratedFDeriv ℝ k q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-‖y‖ ^ 2 / 4)
  q_ne_zero : q ≠ 0
  q_integrable : Integrable q volume
  integral_q : ∫ y, q y = 0
  q_memLp : ∀ M : ℝ, MemLp q 2 (wMeasure M)
  h_memLp_profile : ∀ M : ℝ, MemLp h 2 (profileMeasure M)
  h_memLp_XG : MemLp h 2 B0010.xGMeasure
  L0_eigen : L0 (h_memLp_XG.toLp h) = (-2 * Complex.I * c) • h_memLp_XG.toLp h
  Lsec_eigen : ∀ {M : ℝ} (hM : 1 < M),
    Lsec hM 2 ((h_memLp_profile M).toLp h) = (-2 * Complex.I * c) • (h_memLp_profile M).toLp h
  conj_memLp_profile : ∀ M : ℝ, MemLp (fun r => conj (h r)) 2 (profileMeasure M)
  Lsec_conj_eigen : ∀ {M : ℝ} (hM : 1 < M),
    Lsec hM (-2) ((conj_memLp_profile M).toLp fun r => conj (h r)) =
      conj (-2 * Complex.I * c) • (conj_memLp_profile M).toLp fun r => conj (h r)
  /-- The streamfunction `Ψ = φ e^{2iϑ}`. -/
  Ψ : ℂ → ℂ
  Ψ_eq : Ψ = NUE.Ang.ofProfile 2 φ
  Ψ_smooth : ContDiff ℝ ∞ Ψ
  velocity_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℂ, ‖fderiv ℝ Ψ y‖ ≤ K / (1 + ‖y‖) ^ 3
  velocity_memLp : MemLp (fderiv ℝ Ψ) 2 volume

namespace GaussianGrowingMode

/-- The eigenvalue `λ = -2ic = γ + iω` (tex line 969). -/
def eigenvalue (G : GaussianGrowingMode) : ℂ := -2 * Complex.I * G.c

/-- `q ∈ 𝒳_{0,M}` for `M > 1` (tex line 977; decision D7: `j = 0`). -/
theorem mem_X0 (G : GaussianGrowingMode) {M : ℝ} (hM : 1 < M) :
    (G.q_memLp M).toLp G.q ∈ X0 hM := by
  rw [mem_X0_iff]
  rw [← G.integral_q]
  refine integral_congr_ae ?_
  exact (volume_ac M).ae_le (G.q_memLp M).coeFn_toLp

end GaussianGrowingMode

/-- **O15** (Proposition `prop:gaussian-existence`, tex lines 962--982, unit B0058): a growing
Gaussian mode exists. Its proof assembles O8 (`Rayleigh.Evans.exists_wholeLine_growing_mode`)
with O9–O12 and O14 of this layer. -/
theorem exists_gaussianGrowingMode : Nonempty GaussianGrowingMode := by
  obtain ⟨c, him, hre0, hre1, -, F, hmode, -, hsmooth, h1, h2, h3, h4⟩ :=
    Rayleigh.Evans.exists_wholeLine_growing_mode
  have hF : ComplexODEC.WholeLineData c F := ⟨hmode, hsmooth, h1, h2, h3, h4⟩
  obtain ⟨g1, g2, g3⟩ := Rayleigh.Evans.growthRate_bounds him hre0 hre1
  obtain ⟨t, ht⟩ := hmode.nonzero
  exact ⟨{
    c := c
    φ := ComplexODEC.modeRadial F
    h := ComplexODEC.modeVort c F
    q := ComplexODEC.modeQ c F
    im_pos := him
    re_pos := hre0
    re_lt_one := hre1
    growth_pos := g1
    freq_gt := g2
    freq_lt := g3
    φ_smooth := ComplexODEC.contDiffOn_modeRadial hF
    φ_rayleigh := fun r hr => ComplexODEC.modeRadial_rayleigh hF hr
    φ_ne_zero := ⟨Real.exp t, Real.exp_pos t, by
      simpa [ComplexODEC.modeRadial, Real.log_exp] using ht⟩
    φ_tendsto_zero := ComplexODEC.tendsto_modeRadial_nhdsGT_zero hF
    φ_tendsto_atTop := ComplexODEC.tendsto_modeRadial_atTop hF
    φ_orders_zero := ComplexODEC.modeRadial_orders_zero hF
    h_mul := ComplexODEC.modeVort_mul hF
    φ_eq_green := fun r hr => ComplexODEC.mode_eq_green hF r hr
    far_field := ComplexODEC.tendsto_sq_mul_modeRadial hF
    quadrupole_ne_zero := ComplexODEC.modeQuadrupole_ne_zero hF
    q_eq := rfl
    q_smooth := ComplexODEC.contDiff_modeQ hF
    q_bound := ComplexODEC.norm_iteratedFDeriv_modeQ_le hF
    q_ne_zero := ComplexODEC.modeQ_ne_zero hF
    q_integrable := ComplexODEC.integrable_modeQ hF
    integral_q := ComplexODEC.integral_modeQ hF
    q_memLp := ComplexODEC.memLp_modeQ_wMeasure hF
    h_memLp_profile := ComplexODEC.memLp_modeVort_profile hF
    h_memLp_XG := ComplexODEC.memLp_modeVort_XG hF
    L0_eigen := ComplexODEC.L0_modeVort hF
    Lsec_eigen := fun hM => ComplexODEC.Lsec_modeVort hF hM
    conj_memLp_profile := ComplexODEC.memLp_conj_modeVort_profile hF
    Lsec_conj_eigen := fun hM => ComplexODEC.Lsec_conj_modeVort hF hM
    Ψ := ComplexODEC.modeStream F
    Ψ_eq := rfl
    Ψ_smooth := ComplexODEC.contDiff_modeStream hF
    velocity_bound := ComplexODEC.norm_fderiv_modeStream_le hF
    velocity_memLp := ComplexODEC.memLp_fderiv_modeStream hF }⟩

end UnforcedLeray.Planar
