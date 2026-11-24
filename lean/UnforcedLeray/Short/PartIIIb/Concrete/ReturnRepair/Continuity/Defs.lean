import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates

/-!
# Operator-norm continuity on the concrete return sequence: the window and the leaves
(source 5684-5685, 5701-5704, 5918-5920)

Source of record: `the November 2 reference manuscript` (73 pages).

`ConcreteReturnNormContinuity D G` (`Concrete/ReturnRepair.lean`) asks, for large `n`, that
`z ↦ 𝒫, L, 𝒬, a_μ, Λ_{μ,ν}` at `μ = μ_n(z)` be norm continuous on `[-1,1]`.  The source proves
it in one sentence for each fixed geometry: "Continuity follows from the resolvent identity, the
dominated separated dilation kernels and the polynomial near inverse; the products and finite
conormal affine construction are continuous" (5701-5704), and "All estimates are locally uniform
in real `μ`; kernels, resolvent identities, the near inverse and affine formulas give
operator-norm continuity for each fixed geometry" (5918-5920; the claim itself is 5684-5685).

At the levels where the near layer `D_N` is a unit, `𝒫 = 𝒥R_μF_A`, `𝒬 = -𝒥 v_Q Tc`,
`L = 𝓛 Tc` with `𝒥 v = (D_N⁻¹Mv, v - S_N D_N⁻¹Mv)` and
`v_Q = (S_μ - S_N) + Y + R_μ(Ẽ - E_{𝓛} - 𝔯_{𝓛})` (source 5790-5818, `ReturnBase.toOps`).  So the
"products" are continuous once the primary operators are.  This file states, for the concrete
sequence, the continuity in `μ` of each primary operator that enters `𝒫, L, 𝒬, a_μ, Λ`, on the
Floquet window `μ_n([-1,1])` of level `n` (`SeqData.win`), for large `n`:

| leaf | operator | source |
|---|---|---|
| `SopCont` | `S_μ = R_μℙdiv` (`Sop`) | resolvent identity `S_μ - S_μ' = (μ'-μ)R_μS_μ'`; 4145, 1556-1583, 5701-5702 |
| `RopCont` | `R_μ = D_μ⁻¹ℙ` (`Rop`) | resolvent identity of `T_ε = (μ - A_ε)⁻¹P_ε`; 1675-1677, 4139-4146 |
| `WardYCont`, `WardECont` | Ward fields `Y[T]`, `Ẽ_μ[T]` (`wardOps`) | dominated separated dilation kernels; 4161-4303, 5702 |
| `NearSNCont` | near inverse `S_N = S_ε - S_far` (`nearOpsAt … .SN`) | resolvent identity and the masked kernel; 3888-3920, 5702-5703 |
| `LjCont` | `𝓛` (`LjOp`; `Lpt` depends on `μ` through `W^mt_μ`) | kernels; 4776-4796, 5919 |
| `FACont`, `EACont` | `F_A`, `E_A` (`FAOp`, `EAOp`; affine in `μ` through `B = (A^y)' + μA^y/s`) | 4957-4985, 5703 |
| `RACont` | `𝔯_A` (`rAOp`) | 5001-5050, 5703 |
| `AMuCont` | `a_μ = s^{5/2}D₀/(μ+5/2)` (`aMuOp`) | 4807-4811 |
| `LamCont` | `Λ_{μ,ν}` (`LamOp`, `LamFun`) | 4812-4815, 5919 |

`M = M_U` (`multOp`) and `ĥ_A` (`hAOp`) do not depend on `μ`.  `S_N` enters through
`SNop = (nearOpsAt …).SNG` and `D_N⁻¹ = (nearOpsAt …).DNinvG`, both fixed transports of the
near operator `S_N : Z → H` (with `D_N = I + M_US_N` a unit on the window, "the polynomial near
inverse", 5703); the reduction is `Continuity/Compose.lean`.

The window is the image `μ_n([-1,1])` (source 5944-5947: "The background and geometry stay fixed
as `μ_n(z) = σ₀ + z/(2|log ν_n|)`, `-1 ≤ z ≤ 1`, varies"); the pinned operators exist there for
large `n` (`SeqData.RepairStanding.pins`).

Each leaf `X` is stated as `SeqData.XCont D : Prop`; the targets `theorem xCont (D : SeqData)
{dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.XCont` are queued (`PartIII-b:C/cont/*`);
`AMuCont` is proved in `Continuity/AMu.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace SeqData

variable (D : SeqData)

/-- **The Floquet window of level `n`** (source 5944-5947): `μ_n([-1,1])`,
`μ_n(z) = σ₀ + z/(2|log ν_n|)`. -/
def win (n : ℕ) : Set ℝ := D.mu n '' Icc (-1 : ℝ) 1

/-- `z ↦ μ_n(z) = σ₀ + z/(2|log ν_n|)` is continuous (source 5946). -/
theorem continuous_mu (n : ℕ) : Continuous (D.mu n) := by
  unfold SeqData.mu muWin
  exact continuous_const.add (continuous_id.div_const _)

theorem mu_mem_win {n : ℕ} {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : D.mu n z ∈ D.win n :=
  mem_image_of_mem _ hz

/-- A family continuous on the window is continuous in `z` on `[-1,1]` at `μ = μ_n(z)`. -/
theorem continuousOn_comp_mu {E : Type} [TopologicalSpace E] {f : ℝ → E} {n : ℕ}
    (h : ContinuousOn f (D.win n)) : ContinuousOn (fun z => f (D.mu n z)) (Icc (-1 : ℝ) 1) :=
  h.comp (D.continuous_mu n).continuousOn (mapsTo_image _ _)

/-! ## The leaves (large `n`, continuity in operator norm on `μ_n([-1,1])`) -/

/-- **`S_μ` is norm continuous in `μ`** (source 5701-5702, 5918-5920: the resolvent identity
`S_μ - S_μ' = (μ'-μ)R_μS_μ'` with `R_μ` bounded on the window; `S_μ = R_μℙdiv` is the weak
stress inverse, 4145, 1556-1583): for large `n`, `μ ↦ Sop` is continuous on `μ_n([-1,1])`. -/
def SopCont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => Sop D.Pl D.K (D.level n) μ) (D.win n)

/-- **`R_μ` is norm continuous in `μ`** (source 5701-5702, 5918-5920; `R_μ = D_μ⁻¹ℙ`, the transport
`bodyG` of the real form of `T_ε = (μ - A_ε)⁻¹P_ε`, 1675-1677, 4139-4146): for large `n`,
`μ ↦ Rop` is continuous on `μ_n([-1,1])`. -/
def RopCont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => Rop D.Pl (D.level n) μ) (D.win n)

/-- **The Ward field `Y[T]` is norm continuous in `μ`** (source 4161-4303, 5701-5702: dominated
separated dilation kernels): for large `n`, `μ ↦ (wardOps …).1 : LStr → LVel` is continuous on
`μ_n([-1,1])`. -/
def WardYCont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => (wardOps D.Pl D.K (D.level n) μ).1) (D.win n)

/-- **The Ward residual `Ẽ_μ[T]` is norm continuous in `μ`** (source 4161-4303, 5701-5702): for
large `n`, `μ ↦ (wardOps …).2.2 : LStr → LSrc` is continuous on `μ_n([-1,1])`. -/
def WardECont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => (wardOps D.Pl D.K (D.level n) μ).2.2) (D.win n)

/-- **The near inverse `S_N = S_ε - S_far` is norm continuous in `μ`** (source 3888-3920, 5701-5703:
the resolvent identity for `S_ε` and the dominated separated kernel of the far mask): for large
`n`, `μ ↦ (nearOpsAt …).SN : Z → H` is continuous on `μ_n([-1,1])`. -/
def NearSNCont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => (nearOpsAt D.Pl D.K (D.level n) μ).SN) (D.win n)

/-- **`𝓛` is norm continuous in `μ`** (source 4776-4796, 5918-5920: `𝓛_{μ,ν}M` is read from
`X^mt_{μ,M} = 𝒞_{χ_y}(W^mt_μ - W^mt_{μ+1})`, whose kernel carries `t^{2μ+2}`): for large `n`,
`μ ↦ LjOp : LStr → 𝒜` is continuous on `μ_n([-1,1])`. -/
def LjCont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => LjOp D.Pl D.K (D.level n) μ) (D.win n)

/-- **`F_A` is norm continuous in `μ`** (source 4957-4985, 5703: `F_A = s^{3/2}f_A` depends on `μ`
only through `B = (A^y)' + μA^y/s`, affinely): for large `n`, `μ ↦ FAOp : 𝒜 → LSrc` is
continuous on `μ_n([-1,1])`. -/
def FACont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => FAOp D.K (D.level n) μ) (D.win n)

/-- **`E_A` is norm continuous in `μ`** (source 4957-4985, 5703: `E_A = s^{3/2}e_A`, affine in `μ`
through `B`): for large `n`, `μ ↦ EAOp : 𝒜 → LSrc` is continuous on `μ_n([-1,1])`. -/
def EACont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => EAOp D.K (D.level n) μ) (D.win n)

/-- **`𝔯_A` is norm continuous in `μ`** (source 5001-5050, 5703: the exact unprojected residual
`𝔯_A = D_μĥ_A + div M_Uĥ_A - F_A - E_A - ∇_y(sΨ_A)`): for large `n`, `μ ↦ rAOp : 𝒜 → LSrc` is
continuous on `μ_n([-1,1])`. -/
def RACont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => rAOp D.Pl D.K (D.level n) μ) (D.win n)

/-- **`a_μ` is continuous in `μ`** (source 4807-4811: `a_μ(s) = s^{5/2}D₀/(μ+5/2)`): for large `n`,
`μ ↦ aMuOp ∈ 𝒜` is continuous on `μ_n([-1,1])`. -/
def AMuCont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => aMuOp D.K μ) (D.win n)

/-- **`Λ_{μ,ν}` is norm continuous in `μ`** (source 4812-4815, 5918-5920:
`Λ_{μ,ν}(A) = -(3π/16)ε³ν^{5+2μ}Re[iN_ν𝒥(μ)a₀(B_{μ,ν}[A])]`): for large `n`, `μ ↦ LamOp : 𝒜 → ℝ`
is continuous on `μ_n([-1,1])`. -/
def LamCont : Prop :=
  ∀ᶠ n : ℕ in atTop, ContinuousOn (fun μ => LamOp D.Pl D.K (D.level n) μ) (D.win n)

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
