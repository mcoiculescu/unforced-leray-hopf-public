import UnforcedLeray.Short.PartIIIa.Defs
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part III-a, module `near/full-clock.tex` (SP 2818-3105): the full moving evolution

Statements of `prop:short-full-clock` (SP 2837-2852) and of the scaling inequalities
`eq:short-causal-scales` (SP 2982-2989), about the evolution of the linearised vorticity
equation around the ACTUAL train, characterised by `IsLinearisedFlow` (`Defs.lean`).

The train. "The actual planar train" (SP 2826) is the train of Proposition `sct:train`, the unique
global mild solution in `BUC` (SP 270-288). `B0140.IsTrain` alone does not determine it (no
uniqueness, no time-local bounds), and both estimates below use train bounds beyond `IsTrain`:
the rescaled-train comparison with the periodized Gaussian (SP 2866-2871) and the uniform bounds
of the rescaled train and its first two derivatives (SP 3050-3051), and the existence of the
evolution uses a bounded perturbation `B(t)` (velocity bounds, SP 2819-2836). So both statements
quantify over trains of the BUC class, `PartI.IsBUCTrain tr` (`Short/PartI/TrainClass.lean`); the
predicate `FullFlowExists` is stated for any train.

Omitted (documented in the report): `eq:short-causal-stable-moving` (SP 2951-2955), the
relative bound of the moving full complement `𝓑` (it is stated in terms of the Gaussian seed
vectors `E(z)`, `Λ(z)` of Part I; to be added when Part I exports them), and the extension of
the weak-source bound from the dense subspace `X_{m,c}^0` to all of `Z^{-1}_{m,c}` by continuity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `M_s = ⌈m/2 + |Re κ| + 2⌉` (SP 2843). -/
def weakDegree (m : ℝ) (κ : ℂ) : ℕ := ⌈m / 2 + |κ.re| + 2⌉₊

/-- The core endpoint `H = s_b = ν⁻¹((νb)⁻¹ - 1)` (SP 2829, 2977). -/
def coreEnd (ν b : ℝ) : ℝ := ν⁻¹ * ((ν * b)⁻¹ - 1)

/-- Existence of the full evolution (SP 2819-2836): for every datum `f ∈ X_{m,c}` of zero
circulation at every age `t ≥ 0` there is a weak linearised flow from `f`. -/
def FullFlowExists (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure c m) →
    HasZeroCirculation c f → ∃ w u, IsLinearisedFlow ν c m tr t f w u

/-- **`eq:short-causal-scales`** (SP 2982-2989). For `m ≥ 0`, `a ≥ 1`, `d > 0`, `c = √a d`
(measurable representatives):
`‖J_a‖_{X_{m,d}→X_{m,c}} ≤ a^{(m-3)/2}`, `‖J_a⁻¹‖_{X_{m,c}→X_{m,d}} ≤ a^{3/2}`,
`‖J_a⁻¹‖_{(H^1_{-m,c})^*→(H^1_{-m,d})^*} ≤ a^{3/2}`. -/
def ScalingBounds : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ a d : ℝ, 1 ≤ a → 0 < d →
    (∀ W : ℝ × ℝ → ℂ, Measurable W →
      xNorm (d * Real.sqrt a) m (Jscale a W) ≤
        ENNReal.ofReal (a ^ ((m - 3) / 2)) * xNorm d m W) ∧
    (∀ f : ℝ × ℝ → ℂ, Measurable f →
      xNorm d m (JscaleInv a f) ≤ ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * xNorm (d * Real.sqrt a) m f) ∧
    (∀ f : ℝ × ℝ → ℂ, Measurable f →
      negNorm d m (JscaleInv a f) ≤
        ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * negNorm (d * Real.sqrt a) m f)

/-- **`prop:short-full-clock`, first estimate, `eq:short-causal-long-forward`** (SP 2837-2845,
3064-3069). For every planar reference `P` (G1-G4), `m > 8`, and `b` large: with `c = ν^{-2}`, for
small `ν`, every actual train `tr` (BUC class, SP 270-288; the comparison SP 2866-2871 is used):
the evolution exists, and every weak linearised flow `w`
from a zero-circulation datum `f ∈ X_{m,c}` at age `t ≥ 0` satisfies, on `b ≤ θ(s) ≤ θ(t) ≤ ν⁻¹`
(`θ(s) = (ν(1+νs))⁻¹`, `a(s) = 1+νs`, `d = c/√a`),
`‖J_{a_s}⁻¹ w(s)‖_{X_{m,d_s}} ≤ C_b e^{γ(θ_t-θ_s)} (θ_t/θ_s)^{Re κ} ‖J_{a_t}⁻¹ f‖_{X_{m,d_t}}`
(the moving-coordinate form `‖U_mov(θ, r₀)‖_{X_{m,d(r₀)}→X_{m,d(θ)}}`; no parity restriction). -/
def FullClockLongForward : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
        FullFlowExists ν (ν ^ (-2 : ℝ)) m tr ∧
        ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
          ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (JscaleInv (clockA ν s) (w s)) ≤
                ENNReal.ofReal (C * Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν s)) *
                    (clockTheta ν t / clockTheta ν s) ^ P.kappa.re) *
                  xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (JscaleInv (clockA ν t) f)

/-- **`prop:short-full-clock`, weak-source estimate, `eq:short-causal-weak-forward`**
(SP 2837-2852, 3081-3094), for every actual train `tr` of the BUC class (SP 270-288; the rescaled
train bounds SP 3050-3051 are used). On `0 < t < s ≤ H = ν⁻¹((νb)⁻¹ - 1)`, for every zero-circulation datum
`f ∈ X_{m,c}`:
`(g(t)/g(s)) ‖U(s,t)f‖_{X_{m,c}} ≤ C_b ν^{-M_s}{1 + (s-t)^{-1/2}} ‖f‖_{Z^{-1}_{m,c}}`,
`M_s = ⌈m/2 + |Re κ| + 2⌉` (stated on the dense subspace of `Z^{-1}_{m,c}` of zero-circulation
`X_{m,c}` data; the weak-source extension is by density). -/
def FullClockWeakForward : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t s : ℝ, 0 < t → t < s → s ≤ coreEnd ν b →
          ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
              ENNReal.ofReal (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
                  xNorm (ν ^ (-2 : ℝ)) m (w s) ≤
                ENNReal.ofReal (C * ν ^ (-(weakDegree m P.kappa : ℝ)) *
                    (1 + (s - t) ^ (-1 / 2 : ℝ))) *
                  negNorm (ν ^ (-2 : ℝ)) m f

end UnforcedLeray.Short.IIIa
