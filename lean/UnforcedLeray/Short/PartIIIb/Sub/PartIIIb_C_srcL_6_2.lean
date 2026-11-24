import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6

/-!
# Decomposition of `XSZDecay` (task `PartIII-b:C/srcL/6/2`)

Source 4776-4791, 4917-4937: derivative decay of `Z = W^mt_μ - W^mt_{μ+1}` away from the axis.
The difference is reduced to the individual zero-width Young fields.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Homogeneity bounds for the Newton kernel `N(x) = 1/(4π|x|)` (degree `-1`, `C^∞` off `0`):
`|D^m N(w)| ≤ C_m |w|^{-1-m}` for `w ≠ 0` (prove by scaling and compactness of the unit sphere,
or by induction with explicit derivatives of `(Σ x_i²)^{-1/2}`). -/
def XSNewtonHomog : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, ∀ w : Vec3, w ≠ 0 →
    ‖iteratedFDeriv ℝ m newtonN w‖ ≤ C * ‖w‖ ^ (-(1 + (m : ℝ)))

/-- Each zero-width Young field is `C^∞` on the outward region (source 4776-4782: for
`x = εy` with `(εr)² > 5ν/6` and `t ∈ (0,1]`, `|x'|² < 5ν/6` the kernel argument `x - t(x',0)`
stays away from `0`; `∫|sigmaM| < ∞` from `OldThinFinite`; differentiate under the integral
sign in `t` and `x'`, using Fubini to merge them or two applications of the parametric theorem
`Lib/Kernels/ParamIntegral.lean`).  (Consequently `XSZSmooth` follows for the difference.) -/
def XSYoungWSmooth : Prop :=
  ∀ (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < ε → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (youngW c ν ε μ χo M) (outReg ν ε)

/-- Derivative decay of each zero-width Young field on `{a ≤ r²}`, `a > 5ν/(6ε²)` (source
4776-4791: `D^k_y[ε² V(εy)] = ε^{2+k} (D^k V)(εy)`, `D^k V(x)` is the `t, x'` integral of
`D^{3+k} N(x - t(x',0))` against `sigmaM`, `|x'|² < 5ν/6`, so for large `|x|` the kernel
argument has norm `≥ |x|/2` and `XSNewtonHomog` gives `|x|^{-4-k}`; for bounded `|x|` in the
region the kernel stays at positive distance from `0`, giving a finite bound by continuity of the
derivatives on a compact set; `∫|sigmaM| < ∞` from `OldThinFinite`). -/
def XSYoungWDecay : Prop :=
  ∀ (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < ε → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M →
    ∀ a : ℝ, 5 * ν / (6 * ε ^ 2) < a → ∀ k : ℕ, ∃ C : ℝ, ∀ w : Vec3, a ≤ cylR w ^ 2 →
      ‖iteratedFDeriv ℝ k (youngW c ν ε μ χo M) w‖ ≤ C * (1 + ‖w‖) ^ (-(4 + (k : ℝ)))

theorem xsZDecay_of (hS : XSYoungWSmooth) (hD : XSYoungWDecay) : XSZDecay := by
  intro c ν ε μ χo M hc hν hε hμ hχ hM a ha k
  obtain ⟨C1, h1⟩ := hD c ν ε μ χo M hc hν hε hμ hχ hM a ha k
  obtain ⟨C2, h2⟩ := hD c ν ε (μ + 1) χo M hc hν hε (by linarith) hχ hM a ha k
  refine ⟨C1 + C2, fun w hw => ?_⟩
  have hwU : w ∈ outReg ν ε := by
    have : 5 * ν / (6 * ε ^ 2) < cylR w ^ 2 := lt_of_lt_of_le ha hw
    exact this
  have hU := isOpen_outReg ν ε
  have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have s1 := (hS c ν ε μ χo M hc hν hε hμ hχ hM).of_le hle
  have s2 := (hS c ν ε (μ + 1) χo M hc hν hε (by linarith) hχ hM).of_le hle
  have e := iteratedFDerivWithin_sub_apply (s1 w hwU) (s2 w hwU) hU.uniqueDiffOn hwU
  rw [iteratedFDerivWithin_of_isOpen k hU hwU, iteratedFDerivWithin_of_isOpen k hU hwU,
    iteratedFDerivWithin_of_isOpen k hU hwU] at e
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := h1 w hw
  have := h2 w hw
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
