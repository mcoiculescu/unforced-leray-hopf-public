import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.FlatUniform
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5Org

/-!
# `PartIII-b:IIIb-D3/2/G6/org`: the uniform scalar chain `FlatUnif.FlatScalarChain`

Source of record: `the November 2 reference manuscript` (73 pages): class amplitude
4624-4626 (proof 4643-4661), scalar estimate 4628-4632 (proof 4662-4684), `B_{μ,ν}[A]` and
`‖B_{μ,ν}[A]‖_{𝓑_{a_s}} ≤ C_K‖A‖_𝒜` 4755-4760, `𝔗_{μ,ν}A` 4761-4763, `Λ_{μ,ν}` 4812-4815, use at
4908-4910 ("The uniform scalar estimate in the preceding section replaces `ℓ_μ(M)` by `Λ_{μ,ν}(A)`").

The fixed-`μ` conditionals of `Concrete/YoungFlat.lean` hold one `μ` along the sequence; here
`μ = μ_n(z)` moves with `n` inside the window `[σ₀/2, (σ₀+1/4)/2]` (`mu_eventually_mem`), so their
per-`n` lemmas are reused with window-uniform constants:

* `ClassAmpWindow` (leaf): the class amplitude with one constant on the window (adapt
  `ConcreteYF.FlatAmp.flatClassAmplitudeC_of`, `Sub/PartIII-b_C_flat_1.lean:473`);
* `ScalarWindow` (leaf): the scalar estimate with one constant on the window (adapt
  `ConcreteYF.flatScalarEstimateC`, `Concrete/FlatScalar.lean:161`; `‖𝒥(μ)‖ ≤ C_j`);
* `BmatBclass` (leaf): `B_{μ,ν}[A] ∈ 𝓑_{a_s}`, `‖B_{μ,ν}[A]‖_{a_s} ≤ C‖A‖_𝒜` (4757-4760);
* `EllMuAtCongr` (leaf): `ℓ_μ` reads its stress only a.e. on the old region `u > 1.2/ν`;
* `ActualSeqPinned` (organizer): an actual flat sequence with seed kernels linked to `D.Pl`, `m > 8`,
  and its column pin (`IsFlatDuhamelColumn`, 4761-4763);
* `FlatRealization`: the flat near operators of the level are realized by their pins and the age
  force `F_A` has a coefficient in `H` (3866-3914, 4079-4086, 1675-1677, 4969-4985); proved here
  (`flatRealization_of`) from `FlatUnif.G5.FlatNearUnit` (`D₀` a unit, G5's leaf), as in
  `FlatUnif.G5.kflatPin_of`.

Both column pins (the actual sequence and `D.flat n`, `ColumnPin`) read the same zero-entrance forced
column of a realization (`oldIdent`), so `𝔗` of the two settings agree a.e. on the old region, and
`ℓ_μ(𝔗A) = ellMuC (S n) (B_{μ,ν}[A])` by unfolding the actual setting (`level_ellMuC`).

Assembly: `flatScalarChain_of`; the task `PartIII-b:IIIb-D3/2/G6` states
`flatScalarChain := FlatUnif.G6.flatScalarChain_of classAmpWindow scalarWindow bmatBclass
ellMuAtCongr actualSeqPinned flatNearUnit` (`flatNearUnit` the theorem of G5 proving
`FlatUnif.G5.FlatNearUnit D`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6

open ConcreteYF

/-! ## Leaves -/

/-- **Window-uniform class amplitude** (source 4624-4626, proof 4643-4661): for a viscosity
sequence `ν_n → 0`, `c_n = ν_n⁻²`, measurable frozen-pair pairings `t ↦ ℓ_{+,νt,c}H_{t,c}`,
`ℓ_{+,νt,c}H̄_{t,c}`, `ℓ_{+,νt,c}R_{t,c}` (4645-4648), `0 < a < γ/16` (4586) and the direct/dual
Gaussian comparison (4650-4654), `|a_{ν,+}(B) - a₀(B)| ≤ Cν‖B‖_a` on `𝓑_a` with one constant for all
`μ = μ_n(z)` in a window `[lo, hi] ⊂ (0, ∞)` (majorant `t^{μ+3/2} ≤ t^{lo+3/2} + t^{hi+3/2}`). -/
def ClassAmpWindow : Prop :=
  ∀ (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (μ : ℕ → ℝ → ℝ) (lam κ ell : ℂ) (a lo hi : ℝ),
    0 < lam.re → 0 < a → a < lam.re / 16 → 0 < lo →
    (∀ n, 0 < ν n) → Tendsto ν atTop (𝓝 0) →
    (∀ᶠ n : ℕ in atTop, (S n).c = (ν n)⁻¹ ^ 2) →
    (∀ᶠ n : ℕ in atTop, Measurable (fun t => (S n).pk.ell true t ((S n).Hper t)) ∧
      Measurable (fun t => (S n).pk.ell true t ((S n).conjX ((S n).Hper t))) ∧
      Measurable (fun t => (S n).pk.ell true t ((S n).Rper t))) →
    (∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, μ n z ∈ Icc lo hi) →
    FlatGaussComparison S ν ell →
    ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass a (ν n) B →
      ‖(S n).aNuC lam κ (μ n z : ℂ) (ν n) B - aZero lam ell (μ n z : ℂ) B‖ ≤ C * ν n * bNorm a B

/-- **Window-uniform scalar estimate** (source 4628-4632, proof 4662-4684): from the window-uniform
class amplitude, the old anisotropy law (4669-4672, real form 4719-4722), the earlier-old bound
(4686-4688) and the integrability of the two pieces of `I_T` (split at `u_o = ν^{-3/2}`), with
`c = ν⁻²`, `ε³ > 0`, `μ = μ_n(z) ∈ [lo, hi] ⊂ (0, ∞)` and `‖𝒥(μ)‖ ≤ C_j` on the window:
`|ℓ_μ(M_B) + (3π/16)ε³ν^{5+2μ} Re[i a₀(B) N_ν 𝒥(μ)]| ≤ C A_*[ω_can + ν + P_νe^{-γ'/√ν}]‖B‖_a`. -/
def ScalarWindow : Prop :=
  ∀ (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (μ : ℕ → ℝ → ℝ) (lam κ ell : ℂ) (J : ℂ → ℂ)
    (a lo hi Cj : ℝ), 0 < lo → (∀ n, 0 < ν n) →
    (∀ᶠ n : ℕ in atTop, (S n).c = (ν n)⁻¹ ^ 2 ∧ 0 < (S n).eps3) →
    (∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, μ n z ∈ Icc lo hi) →
    (∀ x ∈ Icc lo hi, ‖J (x : ℂ)‖ ≤ Cj) →
    (∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass a (ν n) B →
      ‖(S n).aNuC lam κ (μ n z : ℂ) (ν n) B - aZero lam ell (μ n z : ℂ) B‖ ≤
        C * ν n * bNorm a B) →
    (∃ (ωcan : ℕ → ℝ) (C : ℝ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧
      ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass a (ν n) B →
        |(S n).IT (fun s => if ν n ^ (-(3 / 2 : ℝ)) ≤ s then
              (S n).Mcell s ((S n).xi (μ n z : ℂ) B s) else fun _ => 0) -
            (3 * Real.pi / (2 * (S n).c)) * (μ n z + 3 / 2) * ν n ^ (3 + 2 * μ n z) *
              (((S n).aNuC lam κ (μ n z : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ n z : ℂ)).im| ≤
          C * ((‖Nnu lam κ (ν n)‖ * ν n ^ (3 + 2 * μ n z) / (S n).c) * (ν n + ωcan n)) *
            bNorm a B) →
    (∀ γ' : ℝ, 0 < γ' → γ' < lam.re →
      ∃ (C : ℝ) (k N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass a (ν n) B →
        |(S n).IT (fun s => if s < ν n ^ (-(3 / 2 : ℝ)) then
              (S n).Mcell s ((S n).xi (μ n z : ℂ) B s) else fun _ => 0)| ≤
          C * (‖Nnu lam κ (ν n)‖ * ν n ^ (3 + 2 * μ n z) / (S n).c) *
            ((ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B) →
    (∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass a (ν n) B →
      Integrable (fun s => (S n).ITdens (fun s => if ν n ^ (-(3 / 2 : ℝ)) ≤ s then
          (S n).Mcell s ((S n).xi (μ n z : ℂ) B s) else fun _ => 0) s)
        (volume.restrict (Ioi (0 : ℝ))) ∧
      Integrable (fun s => (S n).ITdens (fun s => if s < ν n ^ (-(3 / 2 : ℝ)) then
          (S n).Mcell s ((S n).xi (μ n z : ℂ) B s) else fun _ => 0) s)
        (volume.restrict (Ioi (0 : ℝ)))) →
    ∀ γ' : ℝ, 0 < γ' → γ' < lam.re →
      ∃ (ωcan : ℕ → ℝ) (C : ℝ) (k N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧
        ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass a (ν n) B →
          |(S n).ellMuC lam κ (μ n z) B + (3 * Real.pi / 16) *
              ((S n).eps3 * ν n ^ (5 + 2 * μ n z)) *
              (Complex.I * aZero lam ell (μ n z : ℂ) B * Nnu lam κ (ν n) * J (μ n z : ℂ)).re| ≤
            C * ((S n).eps3 * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ n z)) *
              (ωcan n + ν n + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B

/-- **`B_{μ,ν}[A]` lies in the class, with `‖B_{μ,ν}[A]‖_{a_s} ≤ C‖A‖_𝒜`** (source 4755-4760; the
cutoff derivative is included in `B`): for a source cutoff profile `χ̂_f` (`1` on `t ≤ 1`, `0` on
`t ≥ 1.1`), `0 < ν`, `0 ≤ μ ≤ 1` and `A ∈ 𝒜`, `B = (χ_fA)' + (μ/s)χ_fA` is measurable, trace free,
without mixed azimuthal entries, supported in `(0, 1.1/ν)`, and `e^{-a_s s}s^{-3/2}|B(s)| ≤ C‖A‖_𝒜`
(`bmat_pointwise`, `Sub/PartIII-b_IIIb-D3_1/BmatSharp.lean:97`). -/
def BmatBclass : Prop :=
  ∀ χ : ℝ → ℝ, IsSourceCutoffC χ → ∀ as : ℝ, ∃ Cb : ℝ, 0 ≤ Cb ∧
    ∀ (ν μ : ℝ), 0 < ν → 0 ≤ μ → μ ≤ 1 → ∀ A : AffSp as,
      IsBclass as ν (Bmat ν μ χ (affIota as A)) ∧
        bNorm as (Bmat ν μ χ (affIota as A)) ≤ Cb * ‖A‖

/-- **`ℓ_μ` reads its stress only on the old region** (source 4584-4587, 4766-4770): `χ̂_o = 0` on
`(-∞, 1.2]` (`D.K.hχo`), so `ℓ_μ(M) = ε³I_T(M)/(8(μ+3/2))` depends only on the class of `M` a.e. for
`du × dq/c dη` on `u > 1.2/ν` (`oldMeasure`). -/
def EllMuAtCongr : Prop :=
  ∀ (D : SeqData) (n : ℕ) (μ : ℝ) (M M' : Chart → Mat3),
    M =ᵐ[oldMeasure (cOf (nu D n)) (nu D n)] M' → ellMuAt D n μ M = ellMuAt D n μ M'

/-! ## Existence leaves -/

/-- **An actual flat sequence with its column pin** (source 4349-4356, 4557-4612, 4761-4763): under
the standing hypotheses there are planar kernels `κ` of the Part I seed linked to `D.Pl`
(`SeedLink`, 4614-4618, 4650-4654), a weight `m > 8` of `X_{m,c}` (4349-4350) and settings `S n`
that are, for large `n`, the actual flat settings `levelFlat FI χ̂_o ε_n` of pinned data `FI` of
`D.train n` (`TrainEvolution`, `FrozenPair`, `GaussSources`), whose stress readout is the forced
flat column (`IsFlatDuhamelColumn`, as for `D.flat n` in `ColumnPin`) at the window points. -/
def ActualSeqPinned (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp →
    ∃ (κ : IIIa.PlanarFrameKernels) (m : ℝ) (_ : Fact (1 < m)) (S : ℕ → FlatSetting),
      SeedLink D κ ∧ 8 < m ∧ IsActualSeq D κ m S ∧
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearInst.Kflat.IsFlatDuhamelColumn (S n)
        (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf

/-- **The flat near operators of the level are realized** (source 3866-3914, 3943-3951, 4079-4086,
1675-1677, 4969-4985): under the standing hypotheses, for large `n` and window points, there are
near operators `o` with the train multiplier `M₀` of `D.train n` (`IsFlatMult`), the free causal stress
inverse `S₀` (`IsFreeStress`) and `D₀ = I + M₀S₀` invertible, a real form `R₀` of the flat body inverse
`T₀` (`IsBodyTransport`), and for every `A ∈ 𝒜` a coefficient `h ∈ H` of the Gaussian age force `F_A`
(`affCoef`).  These are the data for which `IsFlatDuhamelColumn` pins `𝔗`. -/
def FlatRealization (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∃ (mZ ρb : ℝ) (o : NearInst.NearOps (cOf (nu D n)) mZ ρb)
      (R0 : Hsp (cOf (nu D n)) →L[ℝ] Hsp (cOf (nu D n))),
      NearInst.IsFlatMult o.M0 (D.train n) ∧ NearInst.IsFreeStress o.S0 (nu D n) (D.mu n z) ∧
      NearInst.IsBodyTransport R0
        (PartIIa.T0flat (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (nu D n) (D.mu n z : ℂ)) ∧
      IsUnit o.D0 ∧
      ∀ A : AffSp D.K.as, ∃ h : Hsp (cOf (nu D n)),
        (h : Chart → UnforcedLeray.Axi.Merid) =ᵐ[UnforcedLeray.Axi.ageμ (cOf (nu D n)) (-3 / 2)]
          NearInst.Kflat.affCoef (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)

/-! ## Helpers -/

/-- The fields of an actual level setting used by the chain: `c = ν⁻²`, `ε³ > 0`, and the
measurability of the frozen-pair pairings (continuity fields of `FrozenPair`, `GaussSources`). -/
theorem level_facts {ν m : ℝ} [Fact (1 < m)] {κ : IIIa.PlanarFrameKernels}
    {tr : B0140.TrainSol ν (cOf ν)} (hν : 0 < ν)
    (FI : FlatSettingInst.FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (S' : FlatSetting) (hS' : S' = levelFlat hν FI χo ε) :
    (S'.c = ν⁻¹ ^ 2 ∧ 0 < S'.eps3) ∧
      (Measurable (fun t => S'.pk.ell true t (S'.Hper t)) ∧
        Measurable (fun t => S'.pk.ell true t (S'.conjX (S'.Hper t))) ∧
        Measurable (fun t => S'.pk.ell true t (S'.Rper t))) := by
  subst hS'
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  refine ⟨⟨?_, pow_pos hε 3⟩, ((FI.pair.ell_cont true).clm_apply FI.src.H_cont).measurable,
    ((FI.pair.ell_cont true).clm_apply
      (FlatSettingInst.continuous_conjX.comp FI.src.H_cont)).measurable,
    ((FI.pair.ell_cont true).clm_apply FI.src.R_cont).measurable⟩
  show cOf ν = ν⁻¹ ^ 2
  rw [cOf, inv_pow]

/-- On an actual level setting, `ℓ_μ(M_B)` of the setting at `B = B_{μ,ν}[A]` is `ellMuAt` of its
stress `𝔗A` (source 4584-4587, 4761-4763), and `ε³` is `ε_n³`. -/
theorem level_ellMuC (D : SeqData) (n : ℕ) {m : ℝ} [Fact (1 < m)]
    {κk : IIIa.PlanarFrameKernels}
    (FI : FlatSettingInst.FlatInstData κk (retNu D.Pl D.σ₀ n) (cOf (retNu D.Pl D.σ₀ n)) m
      (D.train n))
    (S' : FlatSetting)
    (hS' : S' = levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n))
    (lam κ : ℂ) (μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    S'.ellMuC lam κ μ (Bmat (nu D n) μ χf A) = ellMuAt D n μ (frakT S' (nu D n) μ χf A) ∧
      S'.eps3 = retEps D.Pl D.σ₀ n ^ 3 := by
  subst hS'
  exact ⟨rfl, rfl⟩

/-- **Two column pins, one realization: the stresses agree on the old region** (source 4761-4763,
4084-4086): with `b = R₀h - S₀D₀⁻¹M₀R₀h` (`flatColumn_solves`), both pins give `v⊗b + b⊗v`. -/
theorem oldIdent {S S' : FlatSetting} {c ν : ℝ} {hc : 0 < c} {tr : B0140.TrainSol ν c}
    {μ as : ℝ} {χf : ℝ → ℝ} (hχf : IsSourceCutoffC χf)
    (hS : NearInst.Kflat.IsFlatDuhamelColumn S hc tr μ as χf)
    (hS' : NearInst.Kflat.IsFlatDuhamelColumn S' hc tr μ as χf)
    {mZ ρb : ℝ} (o : NearInst.NearOps c mZ ρb) (R0 : Hsp c →L[ℝ] Hsp c)
    (hM0 : NearInst.IsFlatMult o.M0 tr) (hS0 : NearInst.IsFreeStress o.S0 ν μ)
    (hR0 : NearInst.IsBodyTransport R0 (PartIIa.T0flat hc ν (μ : ℂ))) (hD0 : IsUnit o.D0)
    {A : ℝ → Mat3} (hA : IsAffElem as A) (h : Hsp c)
    (hh : (h : Chart → UnforcedLeray.Axi.Merid) =ᵐ[UnforcedLeray.Axi.ageμ c (-3 / 2)]
      NearInst.Kflat.affCoef ν μ χf A) :
    frakT S ν μ χf A =ᵐ[oldMeasure c ν] frakT S' ν μ χf A := by
  obtain ⟨-, hb⟩ := NearInst.Kflat.flatColumn_solves o R0 hD0 h
  exact (hS hχf mZ ρb o R0 hM0 hS0 hR0 hD0 A hA h _ hh hb).trans
    (hS' hχf mZ ρb o R0 hM0 hS0 hR0 hD0 A hA h _ hh hb).symm

/-- `A_* = ε_n³|N_ν|ν^{5+2μ}` at `μ = μ_n(z)` (source 4821-4845, 5936-5940). -/
theorem ast_eq (D : SeqData) (n : ℕ) (z : ℝ) :
    Ast D n z = retEps D.Pl D.σ₀ n ^ 3 * ‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
      nu D n ^ (5 + 2 * D.mu n z) := by
  rw [retEps_cube_eq D n]
  rfl

/-- **The realization from the unit `D₀`** (source 3866-3914, 3943-3951, 1675-1677, 4969-4985):
the pinned near operators `nearOpsAt` of the level (`RegimePins.near`: `IsFlatMult`, `IsFreeStress`),
`D₀` a unit (`FlatUnif.G5.FlatNearUnit`), the real form `R₀` of `T₀` (`NearInst.Body.bodyRealForms`)
and `h = π^{-1/2} srcIso F_A` (`FAOp_spec`, `srcCoefAE`), as in `FlatUnif.G5.kflatPin_of`. -/
theorem flatRealization_of (D : SeqData) (hU : G5.FlatNearUnit D) : FlatRealization D := by
  intro dm dp hst
  obtain ⟨ν₄, hν₄, hBR⟩ := NearInst.Body.bodyRealForms (NearInst.winK D.σ₀)
    (NearInst.isCompact_winK _) (NearInst.winK_sub hst.sigma_pos hst.sigma_lt) dm dp hst.dm_pos
  filter_upwards [NearInst.seq_levels D hst.omega_ne hst.sigma_pos hst.sigma_lt hst.actual
    hst.inlet hν₄, hst.pins, hU dm dp hst] with n hlev hpins hD0 z hz
  obtain ⟨hL, -, hνn, -, hμ⟩ := hlev
  obtain ⟨R0, hR0⟩ : ∃ R0 : Hsp (cOf (nu D n)) →L[ℝ] Hsp (cOf (nu D n)), NearInst.IsBodyTransport R0
      (PartIIa.T0flat (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (nu D n) (D.mu n z : ℂ)) :=
    (hBR _ _ hL.regime hνn _ (hμ z hz)).2
  have hP := hpins z hz
  have hAN := (nearOpsAt_spec hP.near).1
  have hFA : ∀ A, (FAOp D.K (D.level n) (D.mu n z) A : Chart → UnforcedLeray.Axi.Merid)
      =ᵐ[srcMeasure (cOf (D.level n).ν)]
        FAcoef (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A) := FAOp_spec hP.fA
  refine ⟨D.K.mZ, (D.level n).ρb D.Pl D.K, nearOpsAt D.Pl D.K (D.level n) (D.mu n z), R0,
    hAN.flat, hAN.free, hR0, hD0 z hz, fun A => ⟨(Real.sqrt Real.pi)⁻¹ •
      NearInst.srcIso (cOf (nu D n)) (FAOp D.K (D.level n) (D.mu n z) A), ?_⟩⟩
  exact NearInst.Kflat.srcCoefAE (cOf (nu D n)) (FAOp D.K (D.level n) (D.mu n z) A) _ (hFA A)

/-! ## The assembly -/

/-- **The uniform scalar chain from the leaves** (source 4624-4632, 4643-4684, 4755-4763,
4812-4815, 4908-4910). -/
theorem flatScalarChain_of (hA : ClassAmpWindow) (hS : ScalarWindow) (hB : BmatBclass)
    (hE : EllMuAtCongr) (hSeq : ∀ D : SeqData, ActualSeqPinned D)
    (hU : ∀ D : SeqData, G5.FlatNearUnit D) : FlatScalarChain := by
  intro D hIn dm dp hst hcol γ' hγ0 hγ1
  obtain ⟨κk, m, hm1, S, hκ, hm8, hSact, hSpin⟩ := hSeq D dm dp hst
  have hI : Inputs D S := hIn dm dp hst κk hκ m hm8 S hSact
  have hσ0 : 0 < D.σ₀ := hst.sigma_pos
  have hσ1 : D.σ₀ < 1 / 4 := hst.sigma_lt
  have hlo : 0 < D.σ₀ / 2 := by linarith
  have hwin := mu_eventually_mem D hst.omega_ne hσ0 hσ1
  obtain ⟨Cj, -, hCj⟩ := mellinJ_bound hst.planar (lo := D.σ₀ / 2) (hi := (D.σ₀ + 1 / 4) / 2) hlo
  have hJ : ∀ x ∈ Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2), ‖planarJ D.Pl (x : ℂ)‖ ≤ Cj := by
    intro x hx
    show ‖D.Pl.mellinJ ((x : ℂ).re)‖ ≤ Cj
    rw [Complex.ofReal_re]
    exact hCj x hx
  have hlev : ∀ᶠ n : ℕ in atTop, ((S n).c = (nu D n)⁻¹ ^ 2 ∧ 0 < (S n).eps3) ∧
      (Measurable (fun t => (S n).pk.ell true t ((S n).Hper t)) ∧
        Measurable (fun t => (S n).pk.ell true t ((S n).conjX ((S n).Hper t))) ∧
        Measurable (fun t => (S n).pk.ell true t ((S n).Rper t))) := by
    filter_upwards [hSact] with n hn
    obtain ⟨FI, hFI⟩ := hn
    exact level_facts (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps_pos D.coeff_ne n) (S n) hFI
  have hamp := hA S (nu D) D.mu D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling D.K.as
    (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hst.gamma_pos hst.as_pos hst.as_lt hlo
    (fun n => retNu_pos D.Pl D.σ₀ n) (retNu_tendsto D.σ₀ hst.omega_ne)
    (hlev.mono fun _ h => h.1.1) (hlev.mono fun _ h => h.2) hwin hI.gauss
  obtain ⟨ω, C, k, N1, hω, hsc⟩ := hS S (nu D) D.mu D.Pl.eigenvalue D.Pl.kappa
    D.Pl.strainCoupling (planarJ D.Pl) D.K.as (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) Cj hlo
    (fun n => retNu_pos D.Pl D.σ₀ n) (hlev.mono fun _ h => h.1) hwin hJ hamp hI.oldAniso
    hI.earlierOld hI.itInt γ' hγ0 hγ1
  obtain ⟨Cb, hCb0, hBcl⟩ := hB D.K.χf hst.chiF D.K.as
  have hcol' : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearInst.Kflat.IsFlatDuhamelColumn
      (D.flat n) (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf := hcol
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    (hSact.and (hSpin.and (hcol'.and ((flatRealization_of D (hU D) dm dp hst).and hwin))))
  refine ⟨fun n => |ω n|, |C| * Cb, k, max N0 N1, ?_, ?_⟩
  · have h := (continuous_abs.tendsto (0 : ℝ)).comp hω
    simpa [Function.comp_def] using h
  intro n hn z hz A
  obtain ⟨⟨FI, hFI⟩, hSp, hDp, hRe, hw⟩ := hN0 n (le_trans (le_max_left _ _) hn)
  have hn1 : N1 ≤ n := le_trans (le_max_right _ _) hn
  have hμw := hw z hz
  have hμ0 : 0 ≤ D.mu n z := by linarith [hμw.1]
  have hμ1 : D.mu n z ≤ 1 := by linarith [hμw.2]
  obtain ⟨hBc, hBn⟩ := hBcl (nu D n) (D.mu n z) (retNu_pos D.Pl D.σ₀ n) hμ0 hμ1 A
  have hmain := hsc n hn1 z hz _ hBc
  obtain ⟨mZ, ρb, o, R0, hM0, hS0, hR0, hD0, hh⟩ := hRe z hz
  obtain ⟨h, hh'⟩ := hh A
  have hid := oldIdent hst.chiF (hSp z hz) (hDp z hz) o R0 hM0 hS0 hR0 hD0 (affIota_mem _ A) h hh'
  obtain ⟨hlv, heps⟩ := level_ellMuC D n FI (S n) hFI D.Pl.eigenvalue D.Pl.kappa (D.mu n z)
    D.K.χf (affIota D.K.as A)
  have hell : ellMuAt D n (D.mu n z)
      (frakT (D.flat n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) =
      (S n).ellMuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z)
        (Bmat (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) := by
    rw [hlv]
    exact (hE D n (D.mu n z) _ _ hid).symm
  have hre : (Complex.I * Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ) *
      aZero D.Pl.eigenvalue D.Pl.strainCoupling (D.mu n z : ℂ)
        (Bmat (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A))) =
      Complex.I * aZero D.Pl.eigenvalue D.Pl.strainCoupling (D.mu n z : ℂ)
        (Bmat (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) *
        Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ) := by ring
  have hL : ellMuAt D n (D.mu n z)
      (frakT (D.flat n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) -
      LamFun D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling (planarJ D.Pl)
        (retEps D.Pl D.σ₀ n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A) =
      (S n).ellMuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z)
          (Bmat (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) +
        (3 * Real.pi / 16) * ((S n).eps3 * nu D n ^ (5 + 2 * D.mu n z)) *
        (Complex.I * aZero D.Pl.eigenvalue D.Pl.strainCoupling (D.mu n z : ℂ)
          (Bmat (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) *
          Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ)).re := by
    rw [hell, heps]
    unfold LamFun
    rw [hre]
    ring
  rw [hL, ast_eq D n z, heps]
  rw [heps] at hmain
  set X : ℝ := retEps D.Pl D.σ₀ n ^ 3 * ‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
    nu D n ^ (5 + 2 * D.mu n z) with hX
  set P : ℝ := (nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n)) with hPdef
  set bN : ℝ := bNorm D.K.as (Bmat (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) with hbN
  have hνn : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hX0 : 0 ≤ X := by
    have he : 0 < retEps D.Pl D.σ₀ n := retEps_pos D.coeff_ne n
    have hp : 0 ≤ nu D n ^ (5 + 2 * D.mu n z) := Real.rpow_nonneg hνn.le _
    positivity
  have hP0 : 0 ≤ P := by positivity
  have hbN0 : 0 ≤ bN := ENNReal.toReal_nonneg
  have hY : |ω n + nu D n + P| ≤ |ω n| + nu D n + P := by
    have h1 := abs_add_le (ω n + nu D n) P
    have h2 := abs_add_le (ω n) (nu D n)
    rw [abs_of_nonneg hP0] at h1
    rw [abs_of_pos hνn] at h2
    linarith
  have h1 : C * X * (ω n + nu D n + P) * bN ≤ |C| * X * |ω n + nu D n + P| * bN := by
    have := le_abs_self (C * X * (ω n + nu D n + P) * bN)
    rwa [abs_mul, abs_mul, abs_mul, abs_of_nonneg hX0, abs_of_nonneg hbN0] at this
  have h2 : |C| * X * |ω n + nu D n + P| * bN ≤ |C| * X * (|ω n| + nu D n + P) * bN :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hY (mul_nonneg (abs_nonneg _) hX0)) hbN0
  have h3 : |C| * X * (|ω n| + nu D n + P) * bN ≤ |C| * X * (|ω n| + nu D n + P) * (Cb * ‖A‖) :=
    mul_le_mul_of_nonneg_left hBn
      (mul_nonneg (mul_nonneg (abs_nonneg _) hX0) (by positivity))
  calc _ ≤ C * X * (ω n + nu D n + P) * bN := hmain
    _ ≤ |C| * X * (|ω n| + nu D n + P) * (Cb * ‖A‖) := h1.trans (h2.trans h3)
    _ = |C| * Cb * X * (|ω n| + nu D n + P) * ‖A‖ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6
