import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_1.Window
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.FlatPin

/-!
# `ORG:D3/flat-inputs`: clause 1 of `FlatLimit` from the uniform flat inputs

Source of record: `the November 2 reference manuscript` (73 pages): young map
4334-4553 (finite band 4386-4431, uniform tested estimate 4432-4460, young source theorem
4461-4553), signed old-stress response 4556-4735 (class amplitude 4624-4661, scalar estimate
4628-4690, all moments 4637-4693), flat limit 4821-4916 (clause 1, proof 4846-4911).

Why the fixed-`μ` conditionals `FlatClassAmplitudeC`, `FlatScalarEstimateC`, `FlatAllMomentsC`
(`Concrete/YoungFlat.lean`) are not applied directly: they hold one `μ` fixed along the sequence,
with constants depending on `μ`, while the flat limit needs `μ = μ_n(z)` (moving with `n`) and
constants uniform in `z ∈ [-1,1]` ("uniformly for `μ ∈ K`", 4825).  The inputs are therefore
restated uniformly in the window, and their passage to the scalar estimate is the separate
statement `FlatScalarChain` (the C/flat algebra redone with window-uniform constants).

Why the inputs are stated for actual settings `S` and not for `D.flat n`: `D.flat n` is free data
of `SeqData`; the target pins it only through `IsFlatDuhamelColumn` (its stress `𝔗` on the old
region `u > 1.2/ν`).  The inputs speak about the young package, the sources and the frozen pair,
so they are stated for the actual flat settings `levelFlat FI χ̂_o ε_n` of pinned data `FI`
(`IsActualSeq`), with kernels `κ` of the planar seed linked to `D.Pl` (`SeedLink`).

* `FlatUnif.Inputs D S` : the seven inputs, uniform in the window;
* `FlatUnif.FlatInputsHold D` : they hold for every actual sequence (groups G1-G4);
* `FlatUnif.FlatNewtonComparison D` : `‖𝒦^flat A - ℓ_μ(𝔗A) a_μ‖ ≤ C A_*[ν + P e^{-γ'/√ν} +
  P e^{-4a_s/(5ν)}]‖A‖` (4846-4909);
* `FlatUnif.FlatScalarUniform D` : `|ℓ_μ(𝔗A) - Λ(A)| ≤ C A_*[ω + ν + P e^{-γ'/√ν}]‖A‖`
  (4628-4632 at `B = B_{μ,ν}[A]`, 4910-4911);
* `FlatUnif.FlatScalarChain` : the inputs give the uniform scalar estimate;
* `FlatUniformHyp D`, `flatLimitKflatPart_of_hyp` : the assembly of clause 1.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace FlatUnif

open ConcreteYF

/-- `ν_n` of the phase-locked sequence. -/
abbrev nu (D : SeqData) (n : ℕ) : ℝ := retNu D.Pl D.σ₀ n

/-- `A_* = ε³|N_ν|ν^{5+2μ}` at level `n`, window point `z` (source 4821-4845). -/
abbrev Ast (D : SeqData) (n : ℕ) (z : ℝ) : ℝ :=
  Astar D.Pl.eigenvalue D.Pl.kappa (mellinC D.Pl.eigenvalue D.Pl.strainCoupling (planarJ D.Pl)
    (D.σ₀ : ℂ)) D.σ₀ (retNu D.Pl D.σ₀ n) z

/-- The pin of the target (`IsFlatDuhamelColumn` at large levels, window points). -/
def ColumnPin (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearInst.Kflat.IsFlatDuhamelColumn (D.flat n)
    (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf

/-- `ℓ_μ(M) = ε³ I_T(M)/(8(μ+3/2))`, `I_T(M) = ∫ χ̂_o(νu) u^{-3/2} (1/c)∫_cell (2M_zz - M_rr)`
at level `n` (source 4584-4587), as a functional of a stress `M` on the chart.  For the actual
flat setting `S` of the level, `ℓ_μ(frakT S ν μ χf A) = S.ellMuC λ κ μ (B_{μ,ν}[A])`; it reads `M`
only on `u ≥ 1.2/ν` (`χ̂_o = 0` on `(-∞,1.2]`). -/
def ellMuAt (D : SeqData) (n : ℕ) (μ : ℝ) (M : Chart → Mat3) : ℝ :=
  retEps D.Pl D.σ₀ n ^ 3 *
    (∫ s in Ioi (0 : ℝ), D.K.χo (retNu D.Pl D.σ₀ n * s) * s ^ (-(3 / 2 : ℝ)) *
      cellInt (cOf (retNu D.Pl D.σ₀ n)) (fun p => 2 * M (s, p) 2 2 - M (s, p) 0 0)) /
    (8 * (μ + 3 / 2))

/-- The planar kernels `κ` are those of the Part I seed and their dual row reads the strain mode
as the planar reference does: `∫ λ₀ H₀ = ℓ₊(H₀) = ℓ(H)` (source 4614-4618, 4650-4654; `D.Pl`
`strainCoupling`, G4).  This fixes the normalization of the frozen pair against `N_ν`, `𝒥`. -/
def SeedLink (D : SeqData) (κ : IIIa.PlanarFrameKernels) : Prop :=
  IIIa.IsSeedKernels κ ∧
    (∫ y, κ.lamP 0 y * FlatSettingInst.hMode 1 y) = D.Pl.strainCoupling

/-- `S n` is the actual flat setting of level `n` for large `n` (source 4557-4612; same pin as
`SeqData.IsActualFlat`): `S n = actualFlatSetting FI χ̂_o ε_n` for pinned data `FI` of the train of
the level at `c_n = ν_n⁻²`. -/
def IsActualSeq (D : SeqData) (κ : IIIa.PlanarFrameKernels) (m : ℝ) [Fact (1 < m)]
    (S : ℕ → FlatSetting) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ FI : FlatSettingInst.FlatInstData κ (retNu D.Pl D.σ₀ n)
      (cOf (retNu D.Pl D.σ₀ n)) m (D.train n),
    S n = levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)

/-- **The seven flat inputs, uniform in the window** `μ = μ_n(z)`, `z ∈ [-1,1]`, large `n`, for the
class `𝓑_{a_s}` (`0 < a_s < γ/16`, 4738-4740).  Fields: `ConcreteYF.FlatGaussComparison`,
`FlatOldAnisotropy`, `FlatEarlierOld`, `FlatITIntegrable`, `FlatTestedSourceNorm`, `FlatStateAtH`,
`FlatLaterOutput` with one constant for all window points. -/
structure Inputs (D : SeqData) (S : ℕ → FlatSetting) : Prop where
  /-- Direct/dual Gaussian comparison (source 4650-4654); it does not involve `μ`. -/
  gauss : FlatGaussComparison S (nu D) D.Pl.strainCoupling
  /-- Old-output anisotropy law (source 4524-4534, 4669-4672, real form 4719-4722). -/
  oldAniso : ∃ (ωcan : ℕ → ℝ) (C : ℝ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧
    ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
      |(S n).IT (fun s => if nu D n ^ (-(3 / 2 : ℝ)) ≤ s then
            (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) -
          (3 * Real.pi / (2 * (S n).c)) * (D.mu n z + 3 / 2) * nu D n ^ (3 + 2 * D.mu n z) *
            (((S n).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z : ℂ) (nu D n) B) *
              Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ)).im| ≤
        C * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
          (S n).c) * (nu D n + ωcan n)) * bNorm D.K.as B
  /-- Earlier-old part (source 4686-4688, "by the full forward gain estimate"). -/
  earlierOld : ∀ γ' : ℝ, 0 < γ' → γ' < D.Pl.eigenvalue.re →
    ∃ (C : ℝ) (k N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
      |(S n).IT (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
            (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0)| ≤
        C * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) / (S n).c) *
          ((nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n))) * bNorm D.K.as B
  /-- Integrability of the two pieces of the `I_T` integrand (source 4672-4690). -/
  itInt : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
    Integrable (fun s => (S n).ITdens (fun s => if nu D n ^ (-(3 / 2 : ℝ)) ≤ s then
        (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s)
      (volume.restrict (Ioi (0 : ℝ))) ∧
    Integrable (fun s => (S n).ITdens (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
        (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s)
      (volume.restrict (Ioi (0 : ℝ)))
  /-- Tested source norm `‖g_B‖_𝓘 ≤ C‖B‖_a`, `α = 1.1` (source 4665-4667). -/
  tested : ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
    testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
      ((S n).gB B) ≤ C * bNorm D.K.as B
  /-- State at `H = 2/ν` (young source theorem 4490-4496, frozen pair 4407-4412). -/
  stateAtH : ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
    ‖duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / nu D n)‖ ≤
      C * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖ *
        testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
          ((S n).gB B)
  /-- Young later output, `k = 0, 1` (source 4421-4439, 4660-4668, 4687-4693). -/
  laterOutput : ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ B, IsBclass D.K.as (nu D n) B →
      (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) k B ≤
        C * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) / (S n).c) *
          nu D n ^ k * (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ *
            ‖duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / nu D n)‖ +
            testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
              ((S n).gB B))

/-- `P` holds for every actual flat sequence of `D` (standing hypotheses, seed kernels linked to
`D.Pl`, weight `m > 8` of `X_{m,c}`, source 4349-4350). -/
def ForActual (D : SeqData) (P : (ℕ → FlatSetting) → Prop) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ κ : IIIa.PlanarFrameKernels, SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m → ∀ S : ℕ → FlatSetting, IsActualSeq D κ m S → P S

/-- Group G1 (source 4386-4460, 4421-4439, 4490-4496): state at `H` and later output. -/
def GroupYoung (D : SeqData) : Prop :=
  ForActual D fun S => (∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (nu D n) B →
      ‖duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / nu D n)‖ ≤
        C * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖ *
          testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
            ((S n).gB B)) ∧
    (∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ B, IsBclass D.K.as (nu D n) B →
        (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) k B ≤
          C * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * nu D n ^ k * (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ *
              ‖duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / nu D n)‖ +
              testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
                ((S n).gB B)))

/-- Group G2 (source 4650-4654): the Gaussian comparison. -/
def GroupGauss (D : SeqData) : Prop :=
  ForActual D fun S => FlatGaussComparison S (nu D) D.Pl.strainCoupling

/-- Group G3 (source 4524-4534, 4719-4722, 4686-4688): old anisotropy and earlier-old part. -/
def GroupOld (D : SeqData) : Prop :=
  ForActual D fun S =>
    (∃ (ωcan : ℕ → ℝ) (C : ℝ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧
      ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
        |(S n).IT (fun s => if nu D n ^ (-(3 / 2 : ℝ)) ≤ s then
              (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) -
            (3 * Real.pi / (2 * (S n).c)) * (D.mu n z + 3 / 2) * nu D n ^ (3 + 2 * D.mu n z) *
              (((S n).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z : ℂ) (nu D n) B) *
                Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ)).im| ≤
          C * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * (nu D n + ωcan n)) * bNorm D.K.as B) ∧
    (∀ γ' : ℝ, 0 < γ' → γ' < D.Pl.eigenvalue.re →
      ∃ (C : ℝ) (k N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
        |(S n).IT (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
              (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0)| ≤
          C * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * ((nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n))) * bNorm D.K.as B)

/-- Group G4 (source 4665-4667, 4672-4690): tested source norm and `I_T` integrability. -/
def GroupTested (D : SeqData) : Prop :=
  ForActual D fun S =>
    (∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
      testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
        ((S n).gB B) ≤ C * bNorm D.K.as B) ∧
    (∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
      Integrable (fun s => (S n).ITdens (fun s => if nu D n ^ (-(3 / 2 : ℝ)) ≤ s then
          (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s)
        (volume.restrict (Ioi (0 : ℝ))) ∧
      Integrable (fun s => (S n).ITdens (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
          (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s)
        (volume.restrict (Ioi (0 : ℝ))))

/-- The seven inputs hold for every actual flat sequence of `D`. -/
def FlatInputsHold (D : SeqData) : Prop := ForActual D (Inputs D)

/-- The four groups give the inputs. -/
theorem flatInputsHold_of {D : SeqData} (h1 : GroupYoung D) (h2 : GroupGauss D) (h3 : GroupOld D)
    (h4 : GroupTested D) : FlatInputsHold D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨y1, y2⟩ := h1 dm dp hst κ hκ m hm S hS
  obtain ⟨o1, o2⟩ := h3 dm dp hst κ hκ m hm S hS
  obtain ⟨t1, t2⟩ := h4 dm dp hst κ hκ m hm S hS
  exact ⟨h2 dm dp hst κ hκ m hm S hS, o1, o2, t2, t1, y1, y2⟩

/-- **Newton/Taylor comparison** (source 4846-4909): for `M = 𝔗_{μ,ν}A`,
`‖𝓛_{μ,ν}M - a_μℓ_μ(M)‖_𝒜 ≤ C A_*[ν + P_νe^{-γ'/√ν} + P_νe^{-4a_s/(5ν)}]‖A‖_𝒜`, read on the
pinned `𝒦^flat = 𝓛𝔗` of the regime (`KflatOp`, `aMuOp`), for every `0 < γ' < γ`. -/
def FlatNewtonComparison (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ColumnPin D →
  ∀ γ' : ℝ, 0 < γ' → γ' < D.Pl.eigenvalue.re →
  ∃ (C : ℝ) (k N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ A : AffSp D.K.as,
    ‖KflatOp D.K (D.level n) (D.mu n z) A -
        ellMuAt D n (D.mu n z) (frakT (D.flat n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) •
          aMuOp D.K (D.mu n z)‖ ≤
      C * Ast D n z * (nu D n + (nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n)) +
        (nu D n)⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / nu D n)) * ‖A‖

/-- **Uniform scalar estimate at `B = B_{μ,ν}[A]`** (source 4628-4632, proof 4662-4690; used at
4910-4911): `|ℓ_μ(𝔗_{μ,ν}A) - Λ_{μ,ν}(A)| ≤ C A_*[ω_can + ν + P_νe^{-γ'/√ν}]‖A‖_𝒜`, for every
`0 < γ' < γ`. -/
def FlatScalarUniform (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ColumnPin D →
  ∀ γ' : ℝ, 0 < γ' → γ' < D.Pl.eigenvalue.re →
  ∃ (ωcan : ℕ → ℝ) (C : ℝ) (k N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧
    ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ A : AffSp D.K.as,
      |ellMuAt D n (D.mu n z) (frakT (D.flat n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) -
          LamFun D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling (planarJ D.Pl)
            (retEps D.Pl D.σ₀ n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)| ≤
        C * Ast D n z * (ωcan n + nu D n + (nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n))) *
          ‖A‖

/-- **The inputs give the uniform scalar estimate** (source 4624-4632, 4643-4690): the C/flat
chain (class amplitude 4643-4661, scalar estimate 4662-4690) with window-uniform constants, the
class bound `B_{μ,ν}[A] ∈ 𝓑_{a_s}`, `‖B‖_{a_s} ≤ C‖A‖_𝒜` (4757-4758, 4863-4864), an actual flat
sequence of `D` and the identification of its `𝔗` with that of `D.flat n` on the old region
(both are the forced column, `IsFlatDuhamelColumn`, 4761-4763). -/
def FlatScalarChain : Prop := ∀ D : SeqData, FlatInputsHold D → FlatScalarUniform D

end FlatUnif

/-- **The uniform flat hypotheses of clause 1 of the flat limit** (source 4554-4735, 4846-4909):
the seven inputs for every actual flat sequence, and the Newton/Taylor comparison. -/
structure FlatUniformHyp (D : SeqData) : Prop where
  inputs : FlatUnif.FlatInputsHold D
  newton : FlatUnif.FlatNewtonComparison D

/-- **Clause 1 of `FlatLimit`** (source 4821-4845, proof 4846-4911) from the uniform hypotheses
and the uniform scalar chain: `𝒦^flat A - Λ(A)a_μ = (𝒦^flat A - ℓ_μ(𝔗A)a_μ) + (ℓ_μ(𝔗A) - Λ(A))a_μ`,
`‖a_μ‖_𝒜 ≤ C` (`norm_aMuOp_le`), `γ' = γ/2`. -/
theorem flatLimitKflatPart_of_hyp (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hflat : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearInst.Kflat.IsFlatDuhamelColumn (D.flat n)
      (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)))
    (hU : FlatUniformHyp D) (hC : FlatUnif.FlatScalarChain) : FlatLimitKflatPart D G := by
  have hγ : 0 < D.Pl.eigenvalue.re := hst.gamma_pos
  have hγ1 : 0 < D.Pl.eigenvalue.re / 2 := by linarith
  have hγ2 : D.Pl.eigenvalue.re / 2 < D.Pl.eigenvalue.re := by linarith
  obtain ⟨C1, k1, N1, H1⟩ := hU.newton dm dp hst hflat _ hγ1 hγ2
  obtain ⟨ω, C2, k2, N2, hω, H2⟩ := hC D hU.inputs dm dp hst hflat _ hγ1 hγ2
  set Ca : ℝ := (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
    (frob (fun i j => Dzero i j) / (5 / 2)) with hCa
  have hCa0 : 0 ≤ Ca := mul_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg (by norm_num) _)
    (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
  have hC0 : 0 ≤ |C2| * Ca := mul_nonneg (abs_nonneg _) hCa0
  have E4 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds one_pos)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hst.near.and (hst.pins.and
    ((mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt).and E4)))
  refine ⟨fun n => |ω n|, 1 + |C1| + |C2| * Ca, D.Pl.eigenvalue.re / 2, max N0 (max N1 N2),
    max k1 k2, ?_, by have := abs_nonneg C1; linarith, hγ1, hγ2, ?_⟩
  · have h := (continuous_abs.tendsto (0 : ℝ)).comp hω
    simpa [Function.comp_def] using h
  intro k hk n hn z hz
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hnear, hpins, hmu, hν1⟩ := hN0 n hn0
  have hnear := hnear z hz
  have hpins := hpins z hz
  have hmu := hmu z hz
  set ν : ℝ := retNu D.Pl D.σ₀ n with hνdef
  set μ : ℝ := D.mu n z with hμdef
  have hν : 0 < ν := retNu_pos _ _ _
  have hμ0 : 0 < μ := by have := hst.sigma_pos; linarith [hmu.1]
  have hP1 : 1 ≤ ν⁻¹ := by rw [one_le_inv₀ hν]; exact hν1.le
  have hk1 : ν⁻¹ ^ k1 ≤ ν⁻¹ ^ k := pow_le_pow_right₀ hP1 (le_trans (le_max_left _ _) hk)
  have hk2 : ν⁻¹ ^ k2 ≤ ν⁻¹ ^ k := pow_le_pow_right₀ hP1 (le_trans (le_max_right _ _) hk)
  set e1 : ℝ := Real.exp (-(D.Pl.eigenvalue.re / 2) / Real.sqrt ν) with he1
  set e2 : ℝ := Real.exp (-(4 * D.K.as / 5) / ν) with he2
  have he10 : 0 ≤ e1 := (Real.exp_pos _).le
  have he20 : 0 ≤ e2 := (Real.exp_pos _).le
  have hp10 : 0 ≤ ν⁻¹ ^ k1 := pow_nonneg (inv_nonneg.2 hν.le) _
  have hp20 : 0 ≤ ν⁻¹ ^ k2 := pow_nonneg (inv_nonneg.2 hν.le) _
  set a : ℝ := FlatUnif.Ast D n z with ha
  have ha0 : 0 ≤ a := by
    rw [ha]
    unfold FlatUnif.Ast Astar epsCube
    have : 0 ≤ ν ^ (5 + 2 * muWin D.σ₀ ν z) := Real.rpow_nonneg hν.le _
    have h2 : 0 ≤ ν ^ (D.Pl.kappa.re - 5 - 2 * D.σ₀) := Real.rpow_nonneg hν.le _
    positivity
  set T : ℝ := ν + |ω n| + ν⁻¹ ^ k * e1 + ν⁻¹ ^ k * e2 with hT
  have hT0 : 0 ≤ T := by
    have := mul_nonneg (pow_nonneg (inv_nonneg.2 hν.le) k) he10
    have := mul_nonneg (pow_nonneg (inv_nonneg.2 hν.le) k) he20
    have := abs_nonneg (ω n)
    linarith
  have hT1 : ν + ν⁻¹ ^ k1 * e1 + ν⁻¹ ^ k1 * e2 ≤ T := by
    have := mul_le_mul_of_nonneg_right hk1 he10
    have := mul_le_mul_of_nonneg_right hk1 he20
    have := abs_nonneg (ω n)
    linarith
  have hT10 : 0 ≤ ν + ν⁻¹ ^ k1 * e1 + ν⁻¹ ^ k1 * e2 := by
    have := mul_nonneg hp10 he10
    have := mul_nonneg hp10 he20
    linarith
  have hT2 : |ω n + ν + ν⁻¹ ^ k2 * e1| ≤ T := by
    have h1 := mul_le_mul_of_nonneg_right hk2 he10
    have h2 := mul_nonneg hp20 he10
    have h3 := mul_nonneg (pow_nonneg (inv_nonneg.2 hν.le) k) he20
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (ω n)]
    · linarith [le_abs_self (ω n)]
  have hK : (concreteOps D.Pl D.K (D.level n) μ).Kflat = KflatOp D.K (D.level n) μ := by
    rw [concreteOps_eq _ _ _ _ hnear]
    rfl
  have haMu : ‖aMuOp D.K μ‖ ≤ Ca := norm_aMuOp_le D.K hst.as_pos.le hμ0
  have hM0 : 0 ≤ (1 + |C1| + |C2| * Ca) * a * T :=
    mul_nonneg (mul_nonneg (by have := abs_nonneg C1; linarith) ha0) hT0
  show ‖(concreteOps D.Pl D.K (D.level n) μ).Kflat -
      (concreteOps D.Pl D.K (D.level n) μ).Lam.smulRight (concreteOps D.Pl D.K (D.level n) μ).aMu‖ ≤
    (1 + |C1| + |C2| * Ca) * a * T
  rw [hK, concreteOps_aMu _ _ _ _ hnear]
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun A => ?_
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply]
  set ℓ : ℝ := FlatUnif.ellMuAt D n μ (frakT (D.flat n) ν μ D.K.χf (affIota D.K.as A)) with hℓ
  set Λ : ℝ := LamFun D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling (planarJ D.Pl)
    (retEps D.Pl D.σ₀ n) ν μ D.K.χf (affIota D.K.as A) with hΛ
  have hΛA : (concreteOps D.Pl D.K (D.level n) μ).Lam A = Λ := lam_apply_eq hnear hpins A
  rw [hΛA]
  have hx : 0 ≤ ‖A‖ := norm_nonneg _
  have h1 : ‖KflatOp D.K (D.level n) μ A - ℓ • aMuOp D.K μ‖ ≤
      C1 * a * (ν + ν⁻¹ ^ k1 * e1 + ν⁻¹ ^ k1 * e2) * ‖A‖ := H1 n hn1 z hz A
  have h2 : |ℓ - Λ| ≤ C2 * a * (ω n + ν + ν⁻¹ ^ k2 * e1) * ‖A‖ := H2 n hn2 z hz A
  have h1' : ‖KflatOp D.K (D.level n) μ A - ℓ • aMuOp D.K μ‖ ≤ |C1| * a * T * ‖A‖ := by
    refine h1.trans ?_
    have e : C1 * a * (ν + ν⁻¹ ^ k1 * e1 + ν⁻¹ ^ k1 * e2) * ‖A‖ =
        C1 * (a * (ν + ν⁻¹ ^ k1 * e1 + ν⁻¹ ^ k1 * e2) * ‖A‖) := by ring
    have e' : |C1| * a * T * ‖A‖ = |C1| * (a * T * ‖A‖) := by ring
    rw [e, e']
    exact mul_le_mul (le_abs_self _)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT1 ha0) hx)
      (mul_nonneg (mul_nonneg ha0 hT10) hx) (abs_nonneg _)
  have h2' : |ℓ - Λ| ≤ |C2| * a * T * ‖A‖ := by
    refine h2.trans ((le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT2
      (mul_nonneg (abs_nonneg _) ha0)) hx
  have hsplit : KflatOp D.K (D.level n) μ A - Λ • aMuOp D.K μ =
      (KflatOp D.K (D.level n) μ A - ℓ • aMuOp D.K μ) + (ℓ - Λ) • aMuOp D.K μ := by
    rw [sub_smul]
    abel
  rw [hsplit]
  have h3 : ‖(ℓ - Λ) • aMuOp D.K μ‖ ≤ |C2| * a * T * ‖A‖ * Ca := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul h2' haMu (norm_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) ha0) hT0) hx)
  have e : (1 + |C1| + |C2| * Ca) * a * T * ‖A‖ =
      |C1| * a * T * ‖A‖ + |C2| * a * T * ‖A‖ * Ca + a * T * ‖A‖ := by ring
  rw [e]
  have h4 : 0 ≤ a * T * ‖A‖ := mul_nonneg (mul_nonneg ha0 hT0) hx
  exact (norm_add_le _ _).trans (by linarith)

end UnforcedLeray.Short.PartIIIb.Concrete
