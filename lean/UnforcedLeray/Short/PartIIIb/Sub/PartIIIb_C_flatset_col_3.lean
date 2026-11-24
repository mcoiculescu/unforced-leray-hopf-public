import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting

/-!
# `FlatXiRegular` from five source facts (decomposition of `PartIII-b:C/flatset/col/3`)

Source of record `the November 2 reference manuscript`: 4610
(`ξ_B(s) = s^{-μ}∫₀^s t^μ 𝒰(s,t) g_B(t) dt`), 4614-4615 (`g_B = O(s^{3/2})`, `ξ_B = O(s^{5/2})`).
Matrix bounds are stated entrywise (`|B s i j| ≤ C s^{3/2}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **(1) `B = O(s^{3/2})`** (source 4614-4615, 4957-4958): for `A` an affine element
(`|(s∂_s)^j A| ≤ M e^{as s} s^{5/2}`, `IsAffElem.bdd`) and `B = Bmat ν μ χf A = (χ_f A)' + μ χ_f A/s`,
`|B s i j| ≤ C s^{3/2}` on `0 < s ≤ 1`.  Route: `|A(s)|, |s A'(s)| ≤ M e^{|as|} s^{5/2}` from
`IsAffElem.bdd` (`affTerm`, `sDerivIter 1 = s • deriv`); `deriv (Ay ν χf A) s = ν χf'(νs) A s +
χf(νs) A'(s)` with `χf` smooth, range `[0,1]` (`IsSourceCutoffC`); `Bmat = deriv + (μ/s)•Ay`. -/
def FlatBSmall : Prop :=
  ∀ (ν μ as : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → IsSourceCutoffC χf → IsAffElem as A →
    ∃ C : ℝ, ∀ s ∈ Ioc (0 : ℝ) 1, ∀ i j, |Bmat ν μ χf A s i j| ≤ C * s ^ (3 / 2 : ℝ)

/-- **(2) `Bmat` is continuous on `(0,∞)`** (source 4957-4958; `A` is `C^6` there, `χf` smooth). -/
def FlatBContinuous : Prop :=
  ∀ (ν μ as : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → IsSourceCutoffC χf → IsAffElem as A →
    ContinuousOn (Bmat ν μ χf A) (Ioi 0)

/-- **(3) `g_B = O(s^{3/2})` in `X_{m,c}`** (source 4605-4608, 4614): `g_B = -½(d-ie)H - ½(d+ie)H̄ -
βR` (`gBD_apply`), so `‖g_B(s)‖ ≤ (|d|+|e|+|β|)(B s)(2‖H s‖+‖R s‖)` (`norm_conjX`), with `H, R`
continuous hence bounded on `[0,1]` (`GaussSources.H_cont`, `R_cont`), `|d|,|e|,|β| ≤ C·max_ij|B_ij|`. -/
def FlatGBSmall : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ),
    (∀ s ∈ Ioc (0 : ℝ) 1, ∀ i j, |B s i j| ≤ C * s ^ (3 / 2 : ℝ)) →
      ∃ C' : ℝ, ∀ s ∈ Ioc (0 : ℝ) 1, ‖gBD D B s‖ ≤ C' * s ^ (3 / 2 : ℝ)

/-- **(4) `ξ_B = O(s^{5/2})`** (source 4610, 4614-4615): `‖ξ s‖ ≤ s^{-μ}∫₀^s t^μ ‖𝒰(s,t)‖ ‖g(t)‖ dt`
with `‖𝒰(s,t)‖ ≤ C₁` on `0 ≤ t ≤ s ≤ 1` (`TrainEvolution.locBdd 1`), `‖(t:ℂ)^(μ:ℂ)‖ = t^μ`
(`Complex.norm_cpow_eq_rpow_re_of_pos`), `norm_integral_le_of_norm_le`, `∫₀^s t^{μ+3/2}dt =
s^{μ+5/2}/(μ+5/2)`. -/
def FlatXiSmall : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ),
    0 < μ → (∀ s ∈ Ioc (0 : ℝ) 1, ‖gBD D B s‖ ≤ C * s ^ (3 / 2 : ℝ)) →
      ∃ C' : ℝ, ∀ s ∈ Ioc (0 : ℝ) 1, ‖xiD D (μ : ℂ) B s‖ ≤ C' * s ^ (5 / 2 : ℝ)

/-- **(5) `ξ_B` is continuous on `(0,∞)`** (source 4610): for `B` continuous on `(0,∞)` with
`g_B = O(s^{3/2})`, `s ↦ ξ_B(s)` is continuous.  Route: `t ↦ gBD D B t` is continuous on `(0,∞)`
(`gBD_apply`, `H_cont`, `R_cont`, continuity of `Bd, Be, Bbeta`); for `s < S` write
`∫_{Ioc 0 s} = ∫_{Ioc 0 S} 1_{t ≤ s}(…)` and dominated convergence
(`continuousOn_of_dominated` / `tendsto_integral_filter_of_dominated_convergence`) with joint
continuity `TrainEvolution.jointCont`, domination `C₁ t^μ‖g(t)‖` (integrable on `(0,S]`,
`TrainEvolution.locBdd S`); the factor `s^{-μ}` is continuous on `(0,∞)`. -/
def FlatXiContinuous : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ),
    0 < μ → ContinuousOn B (Ioi 0) →
      (∀ s ∈ Ioc (0 : ℝ) 1, ∀ i j, |B s i j| ≤ C * s ^ (3 / 2 : ℝ)) →
      ContinuousOn (xiD D (μ : ℂ) B) (Ioi 0)

/-- `FlatXiRegular` from the five leaves. -/
theorem flatXiRegular_of (h1 : FlatBSmall) (h2 : FlatBContinuous) (h3 : FlatGBSmall)
    (h4 : FlatXiSmall) (h5 : FlatXiContinuous) : FlatXiRegular := by
  intro κ ν c m _ _ tr D μ as χf A hν hμ hχ hA
  obtain ⟨C, hC⟩ := h1 ν μ as χf A hν hχ hA
  obtain ⟨C', hC'⟩ := h3 κ ν c m tr D (Bmat ν μ χf A) C hC
  exact ⟨h5 κ ν c m tr D μ (Bmat ν μ χf A) C hμ (h2 ν μ as χf A hν hχ hA) hC,
    h4 κ ν c m tr D μ (Bmat ν μ χf A) C' hμ hC'⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
