import UnforcedLeray.Short.Spine.Objects
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Units.B0146
import UnforcedLeray.Lib.Train.Params

/-!
# Part I output: the planar train and the Gaussian instability

Source: `the November 2 reference manuscript`, Part I (lines 231-1180), with the
parameter conventions of lines 247-259.

`PartIOutput` is what Parts II-III consume:
* the Gaussian planar reference (growing eigenpair on `X_G`, `-2 < ω < 0`, quadrupole
  `M_q ≠ 0`, `ℓ(H) ≠ 0`, adjoint, canonical branch, and the Mellin function `J` holomorphic and
  not identically zero on `Re μ > -3/2`): `prop:short-gaussian-seed` (lines 592-634),
  `prop:short-canonical` (lines 1075-1150), `cor:short-mellin` (lines 1155-1180);
* the exact periodic train: existence (Gallay-Slijepcevic, lines 270-288) and the estimates of
  `sct:train` (lines 290-324) and the uniform bounds quoted at lines 2036-2040.

All statements are about the library's actual train `B0140.TrainSol ν c` (`IsTrain`), whose
initial datum is the nonlinear train, not the sum of independently evolving vortices, in the
Gallay-Slijepcevic class `PartI.IsBUCTrain` (bounded derivatives on every `[0,S] × ℝ²`; source lines
270-288, `Short/PartI/TrainClass.lean`): the bare `IsTrain` is pointwise in the age `s` and does not
make the train estimates true or derivable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar

/-! ## The Gaussian instability -/

/-- The Mellin function `𝒥(μ) = ∫₀^∞ θ^{μ+1/2} 𝔐(V_can(θ)) dθ` for complex `μ`
(`cor:short-mellin`, lines 1155-1160), principal powers of `θ > 0`. -/
def mellinJC (P : PlanarData) (μ : ℂ) : ℂ :=
  ∫ θ in Ioi (0 : ℝ), (θ : ℂ) ^ (μ + 1 / 2) * quadrupole (P.canonical θ)

/-- The planar reference of Part I: `prop:short-gaussian-seed` (lines 592-634: growing pair
`λ = γ + iω`, `γ > 0`, `-2 < ω < 0`, eigenvector `q`, `M_q = 𝔐(q) ≠ 0`, `ℓ(H) = M_q/J_q ≠ 0`,
Gaussian adjoint `q†`), `prop:short-canonical` (lines 1075-1100: `V_can` with the asymptotics
and `κ = ℓ(Dq)`) and `cor:short-mellin` (lines 1155-1180: `𝒥` holomorphic and not identically
zero on `Re μ > -3/2`, all integrals absolutely convergent). The library's `IsPlanarReference`
carries the eigenpair, adjoint, oscillator domain and canonical branch. -/
structure GaussianInstability (P : PlanarData) : Prop where
  reference : IsPlanarReference P
  frequency : P.eigenvalue.im ∈ Ioo (-2 : ℝ) 0
  quadrupole_ne : quadrupole P.mode ≠ 0
  strain_ne : P.strainCoupling ≠ 0
  mellin_integrable : ∀ μ : ℂ, -(3 / 2) < μ.re →
    IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (μ + 1 / 2) * quadrupole (P.canonical θ)) (Ioi 0)
  mellin_holomorphic : DifferentiableOn ℂ (mellinJC P) {μ : ℂ | -(3 / 2) < μ.re}
  mellin_nonzero : ∃ μ : ℂ, -(3 / 2) < μ.re ∧ mellinJC P μ ≠ 0

/-! ## Norms on the unnormalized cell `C_c` (line 252) -/

/-- `‖f‖_{L²(cell)} ≤ B` on the unnormalized cell `[-c/2,c/2) × ℝ`, with convergence of the
integral (so the bound is never a junk-value `0`). -/
def CellL2Le {E : Type*} [NormedAddCommGroup E] (c : ℝ) (f : ℝ × ℝ → E) (B : ℝ) : Prop :=
  0 ≤ B ∧ IntegrableOn (fun z => ‖f z‖ ^ 2) (Cyl.cell c) ∧
    ∫ z in Cyl.cell c, ‖f z‖ ^ 2 ≤ B ^ 2

/-- The normalized horizontal average `f̄(η) = c⁻¹ ∫ f(q, η) dq` over one period, as a function
on the plane (line 252: "A bar denotes the normalized horizontal average"). -/
def horizontalMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    (f : ℝ × ℝ → E) (z : ℝ × ℝ) : E :=
  c⁻¹ • ∫ q in (-c / 2)..(c / 2), f (q, z.2)

/-- The comparison error `e = v - V_c^p` of `sct:train` (line 341): the train minus the
periodized isolated vortices `V_c^p = ∑_n ∇^⊥ψ^p(q - nc, η, s)` (the library's
`B0146.periodicVelocity`). -/
def trainError {ν c : ℝ} (T : B0140.TrainSol ν c) (s : ℝ) : ℝ × ℝ → Train.Vec :=
  fun z => T.v s z - Train.toVec (B0146.periodicVelocity ν c s z)

/-! ## Lemma `sct:train` (lines 290-324) -/

/-- `sct:comparison` (lines 297-304): for `c = ν^{-ρ}`, `ρ > 1/2`, every `j`, and
`1 ≤ a(s) ≤ c²` (`a = 1 + νs`):
`‖D^j(v - V_c^p)(s)‖₂ ≤ C_j ν⁻¹ a^{-2-j/2} e^{-b_j c²/a}` and
`‖D^j(v - V_c^p)(s)‖_∞ ≤ C_j ν⁻¹ a^{-(5+j)/2} e^{-b_j c²/a}`, for small `ν`. -/
def TrainComparison : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C b ν₀ : ℝ, 0 < C ∧ 0 < b ∧ 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (ν ^ (-ρ)), PartI.IsBUCTrain T → ∀ s : ℝ, 0 ≤ s →
      1 + ν * s ≤ (ν ^ (-ρ)) ^ 2 →
        CellL2Le (ν ^ (-ρ)) (iteratedFDeriv ℝ j (trainError T s))
            (C * ν⁻¹ * (1 + ν * s) ^ (-2 - (j : ℝ) / 2) *
              Real.exp (-(b * (ν ^ (-ρ)) ^ 2 / (1 + ν * s)))) ∧
        ∀ z, ‖iteratedFDeriv ℝ j (trainError T s) z‖ ≤
          C * ν⁻¹ * (1 + ν * s) ^ (-((5 : ℝ) + j) / 2) *
            Real.exp (-(b * (ν ^ (-ρ)) ^ 2 / (1 + ν * s)))

/-- `‖v(s)‖₂ ≤ C a(s)⁻¹` for `s ≤ s_c` (line 316), `s_c = (c²-1)/ν`. -/
def TrainEnergyPre : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (ν ^ (-ρ)), PartI.IsBUCTrain T → ∀ s : ℝ, 0 ≤ s →
      s ≤ ((ν ^ (-ρ)) ^ 2 - 1) / ν →
        CellL2Le (ν ^ (-ρ)) (T.v s) (C * (1 + ν * s)⁻¹)

/-- `‖v(s)‖₂ ≤ C c⁻² (s/s_c)^{-3/4}` for `s ≥ s_c` (line 317). -/
def TrainEnergyPost : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (ν ^ (-ρ)), PartI.IsBUCTrain T → ∀ s : ℝ,
      ((ν ^ (-ρ)) ^ 2 - 1) / ν ≤ s →
        CellL2Le (ν ^ (-ρ)) (T.v s)
          (C * ((ν ^ (-ρ)) ^ 2)⁻¹ * (s / (((ν ^ (-ρ)) ^ 2 - 1) / ν)) ^ (-(3 / 4 : ℝ)))

/-- `∫_{s₀}^∞ ∑_{j=1}^{k+1} ‖D^jv(s)‖_∞ ds ≤ C_k/(ν a(s₀)) + C_k e_c` when `a(s₀) ≤ c²`
(line 318-319), `e_c = (νc²)⁻¹`. Stated for each `j` with a measurable-free majorant
`M` of `s ↦ ‖D^jv(s)‖_∞`, so no junk value of `⨆` or of a divergent integral enters. -/
def TrainStrainIntegral : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ k : ℕ, ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (ν ^ (-ρ)), PartI.IsBUCTrain T → ∀ s₀ : ℝ, 0 ≤ s₀ →
      1 + ν * s₀ ≤ (ν ^ (-ρ)) ^ 2 → ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 →
        ∃ M : ℝ → ℝ, (∀ s, s₀ ≤ s → ∀ z, ‖iteratedFDeriv ℝ j (T.v s) z‖ ≤ M s) ∧
          IntegrableOn M (Ici s₀) ∧
          ∫ s in Ioi s₀, M s ≤ C / (ν * (1 + ν * s₀)) + C * (ν * (ν ^ (-ρ)) ^ 2)⁻¹

/-- `∫_{s₀}^∞ ‖ṽ(s)‖₂ ds ≤ (C/ν)(1 + log(c²/a(s₀)))` when `a(s₀) ≤ c²` (lines 320-321),
`ṽ = v - v̄` the complement of the horizontal average. -/
def TrainFluctuationIntegral : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (ν ^ (-ρ)), PartI.IsBUCTrain T → ∀ s₀ : ℝ, 0 ≤ s₀ →
      1 + ν * s₀ ≤ (ν ^ (-ρ)) ^ 2 →
        ∃ M : ℝ → ℝ, (∀ s, s₀ ≤ s →
            CellL2Le (ν ^ (-ρ)) (fun z => T.v s z - horizontalMean (ν ^ (-ρ)) (T.v s) z) (M s)) ∧
          IntegrableOn M (Ici s₀) ∧
          ∫ s in Ioi s₀, M s ≤
            C / ν * (1 + Real.log ((ν ^ (-ρ)) ^ 2 / (1 + ν * s₀)))

/-- The uniform derivative bounds quoted from the train estimates (`short-bg:train-uniform`,
line 2038): `sup_s ∑_{j≤3} ‖D^jv_c(s)‖_∞ ≤ C`, for the train with `c = ν^{-2}`. -/
def TrainUniform : Prop :=
  ∃ C ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (Train.per ν), PartI.IsBUCTrain T → ∀ s : ℝ, 0 ≤ s →
    ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (T.v s) z‖ ≤ C

/-- The all-age train estimates of Part I that Parts II-III consume (`sct:train` lines 290-324 and
`short-bg:train-uniform` line 2038). They are NOT needed to compose the four parts (Parts II and
III quantify over every train), only inside the proofs of `PartIIOutput` and `PartIIIOutput`; the
Part I area proves them as `Short.PartI.TrainComparison`, `TrainStrainIntegral`, ... (same
statements in that area's formulation). -/
def PartIEstimates : Prop :=
  TrainComparison ∧ TrainEnergyPre ∧ TrainEnergyPost ∧ TrainStrainIntegral ∧
    TrainFluctuationIntegral ∧ TrainUniform

/-- The existence of the exact train with `c = ν^{-2}` in the Gallay-Slijepcevic class
`PartI.IsBUCTrain`, for small `ν` (Gallay-Slijepcevic, lines 270-288). -/
def TrainBUCExistence : Prop :=
  ∃ ν₀ > 0, ∀ ν ∈ Ioc 0 ν₀, PartI.TrainBUCSolvable ν (Train.per ν)

/-- **Part I output used by the composition**: the Gaussian planar reference
(`prop:short-gaussian-seed`, `prop:short-canonical`, `cor:short-mellin`) and the existence of the
exact train with `c = ν^{-2}` for small `ν`, in the BUC class (Gallay-Slijepcevic, lines 270-288). -/
def PartIOutput : Prop :=
  (∃ P : PlanarData, GaussianInstability P) ∧ TrainBUCExistence

end UnforcedLeray.Short.Spine
