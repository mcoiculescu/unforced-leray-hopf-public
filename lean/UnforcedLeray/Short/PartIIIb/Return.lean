import UnforcedLeray.Short.PartIIIb.Basic
import UnforcedLeray.Short.PartIIIb.Scalar
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# The operators of the exact return system at one regime (lines 5785-5833)

`ReturnOps` collects, for one choice of the Floquet parameter `μ` at fixed geometry, the
operators that the source names in "The exact two-block equation" (lines 5785-5833):

| field | source object | where defined |
|---|---|---|
| `M` | exact multiplier `M = M_U` (incl. normalisation maps) | 3868-3870, 4147, 5780 |
| `S`, `SN` | full tensor inverse `S_μ`, near inverse `S_N` | 4143-4145, 3912-3920 |
| `R` | physical body inverse `R_μ` (with the Leray projection) | 4143, 5780 |
| `Yf`, `hf`, `Ef` | Ward fields `Y[T]`, `h[T]`, unprojected residual `E[T]` | 4171-4177, 4276-4280 |
| `Lj` | complete old-thin-to-young-jet map `𝓛` | 4796-4812 (`source-class:L`) |
| `hA`, `FA`, `EA`, `rA` | physical affine fields `ĥ_A, F_A, E_A, 𝔯_A` | 4985-5010 |
| `DNinv` | `D_N⁻¹`, `D_N = I + M S_N` | 3921-3925, 5792 |
| `Tc`, `wc` | components `(T, w)` of the graph `𝓔_ν = {T = M w}` | 5640-5650 |
| `P`, `Q`, `Lg` | `𝒫`, `𝒬`, `L` | 5812-5820 |
| `aMu`, `Lam`, `Kflat` | `a_μ`, `Λ_{μ,ν}`, `𝒦^flat_{μ,ν}` | 4880-4905 |

These are the *outputs* of the earlier modules (Ward, physical affine, source class, repair)
that the closing argument uses.  Their concrete realisation (cylinder spaces, train
multiplier, separated kernels) lives in the modules of Parts I-III-a; here each is a field
whose defining identities are the source's own displayed definitions
(`ReturnOps.IsGraphLift`).  The results of the modules enter as `Prop`s over `ReturnOps`
(`Statements.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- Operators of the exact return system at one regime. -/
structure ReturnOps (Vel Str Src Aff Gam : Type)
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel]
    [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src]
    [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff]
    [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam] where
  M : Vel →ₗ[ℝ] Str
  S : Str →ₗ[ℝ] Vel
  SN : Str →ₗ[ℝ] Vel
  R : Src →ₗ[ℝ] Vel
  Yf : Str →ₗ[ℝ] Vel
  hf : Str →ₗ[ℝ] Vel
  Ef : Str →ₗ[ℝ] Src
  Lj : Str →ₗ[ℝ] Aff
  hA : Aff →ₗ[ℝ] Vel
  FA : Aff →ₗ[ℝ] Src
  EA : Aff →ₗ[ℝ] Src
  rA : Aff →ₗ[ℝ] Src
  DNinv : Str →ₗ[ℝ] Str
  Tc : Gam →ₗ[ℝ] Str
  wc : Gam →ₗ[ℝ] Vel
  P : Aff →L[ℝ] Gam
  Q : Gam →L[ℝ] Gam
  Lg : Gam →L[ℝ] Aff
  aMu : Aff
  Lam : Aff →L[ℝ] ℝ
  Kflat : Aff →L[ℝ] Aff

namespace ReturnOps

variable {Vel Str Src Aff Gam : Type}
  [NormedAddCommGroup Vel] [NormedSpace ℝ Vel]
  [NormedAddCommGroup Str] [NormedSpace ℝ Str]
  [NormedAddCommGroup Src] [NormedSpace ℝ Src]
  [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff]
  [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
  (o : ReturnOps Vel Str Src Aff Gam)

/-- `D = I + M S_μ` (line 5780, 5794). -/
def D : Str →ₗ[ℝ] Str := LinearMap.id + o.M ∘ₗ o.S

/-- `D_N = I + M S_N` (line 5794). -/
def DN : Str →ₗ[ℝ] Str := LinearMap.id + o.M ∘ₗ o.SN

/-- `S_far = S_μ - S_N` (line 5794). -/
def Sfar : Str →ₗ[ℝ] Vel := o.S - o.SN

/-- The error velocity `v_Q(T) = S_far T + Y[T] + R_μ(E[T] - E_{LT} - r_{LT})` (line 5812). -/
def vQ : Str →ₗ[ℝ] Vel :=
  o.Sfar + o.Yf + o.R ∘ₗ (o.Ef - o.EA ∘ₗ o.Lj - o.rA ∘ₗ o.Lj)

/-- `H T = M (Y + h - h_{LT})` (line 5810). -/
def Hop : Str →ₗ[ℝ] Str := o.M ∘ₗ (o.Yf + o.hf - o.hA ∘ₗ o.Lj)

/-- The near graph lift `𝒥(v) = (D_N⁻¹ M v, v - S_N D_N⁻¹ M v)` (lines 5799-5803), as the pair of
its components. -/
def Jlift (v : Vel) : Str × Vel :=
  (o.DNinv (o.M v), v - o.SN (o.DNinv (o.M v)))

/-- `D_N⁻¹` is a two-sided inverse of `D_N` (the content of `near:equation-comparison` at
the level of linear algebra). -/
def IsNearInverse : Prop :=
  (∀ T, o.DNinv (o.DN T) = T) ∧ (∀ T, o.DN (o.DNinv T) = T)

/-- The graph `𝓔_ν = {(T, w) : T = M w}` (line 5640) and the defining formulas of
`L`, `𝒫`, `𝒬` (lines 5812-5820): `L(T,w) = LT`, `𝒫A = 𝒥(R F_A)`, `𝒬(T,w) = -𝒥(v_Q(T))`. -/
def IsGraphLift : Prop :=
  (∀ V, o.Tc V = o.M (o.wc V)) ∧
  (∀ V, o.Lg V = o.Lj (o.Tc V)) ∧
  (∀ x, (o.Tc (o.P x), o.wc (o.P x)) = o.Jlift (o.R (o.FA x))) ∧
  (∀ V, (o.Tc (o.Q V), o.wc (o.Q V)) =
      -(o.Jlift (o.vQ (o.Tc V))))

/-- Graph embedding is injective (a graph element is determined by its two components). -/
def IsGraphInj : Prop := ∀ V V' : Gam, o.Tc V = o.Tc V' → o.wc V = o.wc V' → V = V'

/-- Ward identity on the multiplier range, `eq:ward:stress-normal` (lines 4300-4303), in the
form used at 5798: `D M (Y + h) = M Y + M R_μ E`. -/
def WardStressNormal : Prop :=
  ∀ T, o.D (o.M (o.Yf T + o.hf T)) = o.M (o.Yf T) + o.M (o.R (o.Ef T))

/-- Physical affine lifting identity (Lemma `ret:physical-affine`, lines 5001-5008) in the form
used at line 5798: `D M ĥ_A = M R_μ (F_A + E_A + 𝔯_A)`. -/
def PhysAffineIdentity : Prop :=
  ∀ A, o.D (o.M (o.hA A)) = o.M (o.R (o.FA A + o.EA A + o.rA A))

/-- Nilpotency of the change of unknown `H` (lines 5811, 4305-4325): `H² = 0`, so
`(I + H)⁻¹ = I - H`. -/
def HNilpotent : Prop := ∀ T, o.Hop (o.Hop T) = 0

end ReturnOps

end UnforcedLeray.Short.PartIIIb
