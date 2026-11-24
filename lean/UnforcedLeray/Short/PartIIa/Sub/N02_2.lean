import UnforcedLeray.Short.PartIIa.Sub.N02

/-!
# Part II-a, task `PartII-a:N02/2`: stream fields of band potentials are `ε`-solenoidal (conditional)

Source of record: `the November 2 reference manuscript`, lines 1730-1732
("exact counterparts ... the first has zero exact divergence"). Target:
`NearStreamMember` (`Sub/N02.lean`): for every complex band potential `ψ` (`IsCTest c ψ`),
`streamC ε ψ = (-ψ_η, (∂_q - εK)ψ + εψ)` is in `L²(measureH c)` and its class lies in
`solenoidalHC ε c = (span {toLp (cgrad ε Φ) : Φ real profile test})ᗮ`.

## Route

For a real profile test `Φ` (with complexification `Φc`), the pairing is
`⟪toLp (cgrad ε Φ), toLp (streamC ε ψ)⟫ = ∫ (D_εΦ)(-ψ_η) + Φ_η ((∂_q - εK)ψ + εψ) d(measureH c)`
(`cgrad` is real, so the inner product has no conjugation; `InnerCgradStream`). With the weight
`w = s^{-3/2}` (`IntegralMeasureHCell`) the integrand splits (`integrand_identity` in
`Tasks/N02LerayComparison/StreamMember/Identity.lean`) into
`∂_q(Φ_η ψ) - ∂_η(Φ_q ψ) + ε (K(Φ ψ_η) + ∂_η(Φ(ψ - Kψ)))`, and each term integrates to zero over
the cell (`IbpQCell`, `IbpEtaCell`, `IbpKCell`: `∂_q` by `c`-periodicity, `∂_η` by compact support
in `η`, `K` with `K = 2s∂_s + η∂_η` anti-self-adjoint for `s^{-3/2} ds dq dη`). The functions
differentiated are again complex band tests (`CTestFderiv`, `CTestAlgebra`, `CTestOpK`), so every
term is integrable (`BandIntegrable`). The `L²` membership is `StreamMemLp`.

Below, the leaves are `Prop`s; `nearStreamMember_of` is the proved assembly. Lower-level leaves
(`CTestAgeScale`, `PdAgeScale`, the one-dimensional fundamental-theorem facts, the three Fubini
reorderings and the unweighted `s`-integration by parts) are also stated here; they are used inside
the proofs of the top-level leaves (their tasks list them as dependencies) and not by the assembly.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### Closure of complex band tests (`IsCTest`) under the operations that occur -/

/-- **Directional derivatives of complex band tests are complex band tests** (task
`PartII-a:N02/2/1`): smooth (`ContDiff.fderiv_right`), `c`-periodic (`fderiv` of a `q`-periodic
function is `q`-periodic, as `B0226.fderiv_qPeriodic` for `ℂ`-valued functions), and supported in the
same closed band (the band set is closed, so `F` vanishes near a point outside it and `fderiv F` is
zero there; `fderiv_of_notMem_tsupport`). In particular `pdS F, pdQ F, pdEta F` are band tests. -/
def CTestFderiv : Prop :=
  ∀ (c : ℝ) (F : Profile → ℂ), IsCTest c F → ∀ v : Profile,
    IsCTest c (fun p => fderiv ℝ F p v)

/-- **Algebra of complex band tests** (task `PartII-a:N02/2/2`): (1) a real profile test is a
complex band test (`Complex.ofRealCLM`); (2) sums and (3) differences of complex band tests are
complex band tests (take the union `s₀ = min, s₁ = max, L = max` of the two bands); (4) a smooth
`c`-periodic function (no band hypothesis) times a complex band test is a complex band test. -/
def CTestAlgebra : Prop :=
  (∀ (c : ℝ) (Φ : Profile → ℝ), IsProfileTest c Φ → IsCTest c (fun p => (Φ p : ℂ))) ∧
  (∀ (c : ℝ) (F G : Profile → ℂ), IsCTest c F → IsCTest c G → IsCTest c (fun p => F p + G p)) ∧
  (∀ (c : ℝ) (F G : Profile → ℂ), IsCTest c F → IsCTest c G → IsCTest c (fun p => F p - G p)) ∧
  (∀ (c : ℝ) (F G : Profile → ℂ), IsCTest c F → ContDiff ℝ ∞ G → QPeriodic c G →
    IsCTest c (fun p => G p * F p))

/-- **`K F` of a complex band test is a complex band test** (task `PartII-a:N02/2/3`):
`K F = 2 s ∂_s F + η ∂_η F` (`opK_eq` in `StreamMember/Identity.lean`), a sum of the band tests
`pdS F, pdEta F` (`CTestFderiv`) multiplied by the smooth `q`-independent coefficients `s`, `η`
(`CTestAlgebra`). -/
def CTestOpK : Prop :=
  ∀ (c : ℝ) (F : Profile → ℂ), IsCTest c F → IsCTest c (opK F)

/-- **Age scaling preserves complex band tests** (task `PartII-a:N02/2/4`; the complex analog of
`B0226.isProfileTest_ageScale`): for every real exponent `a`, `s ↦ s^a F` is again a complex band
test. Smoothness: `s^a` is smooth where `s > 0`, and `F` vanishes for `s < s₀`. -/
def CTestAgeScale : Prop :=
  ∀ (c a : ℝ) (F : Profile → ℂ), IsCTest c F →
    IsCTest c (fun p => ((p.1 ^ a : ℝ) : ℂ) * F p)

/-- **Integrability of band tests on the cell** (task `PartII-a:N02/2/5`): a complex band test
`G` is integrable on `cell c` (continuous, vanishing outside the compact box
`[s₀, s₁] × [0, c] × [-L, L]` inside the cell), and so is `s^{-3/2} G` (apply the first part to
the band test `s^{-3/2} G`, `CTestAgeScale`). -/
def BandIntegrable : Prop :=
  ∀ (c : ℝ) (G : Profile → ℂ), IsCTest c G →
    IntegrableOn G (cell c) ∧
      IntegrableOn (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * G p) (cell c)

/-- **Product rule for the age weight** (task `PartII-a:N02/2/6`): for `C^∞` `F` and `p` with
`s > 0`, the derivatives of `s^a F` are `∂_s(s^a F) = a s^{a-1} F + s^a ∂_s F`,
`∂_q(s^a F) = s^a ∂_q F`, `∂_η(s^a F) = s^a ∂_η F` (`Real.hasStrictDerivAt_rpow_const` or
`Real.contDiffAt_rpow_const_of_ne` for the derivative of `s ↦ s^a` at `s > 0`). -/
def PdAgeScale : Prop :=
  ∀ (a : ℝ) (F : Profile → ℂ), ContDiff ℝ ∞ F → ∀ p : Profile, 0 < p.1 →
    pdS (fun x => ((x.1 ^ a : ℝ) : ℂ) * F x) p =
        ((a * p.1 ^ (a - 1) : ℝ) : ℂ) * F p + ((p.1 ^ a : ℝ) : ℂ) * pdS F p ∧
      pdQ (fun x => ((x.1 ^ a : ℝ) : ℂ) * F x) p = ((p.1 ^ a : ℝ) : ℂ) * pdQ F p ∧
      pdEta (fun x => ((x.1 ^ a : ℝ) : ℂ) * F x) p = ((p.1 ^ a : ℝ) : ℂ) * pdEta F p

/-! ### One-dimensional facts, slices and Fubini reorderings on the cell -/

/-- **Fundamental theorem on the line / half line** (task `PartII-a:N02/2/7`): a `C^∞` function
`h : ℝ → ℂ` vanishing outside `[a, b]` has `∫ h' = 0`, and also `∫_{(r,∞)} h' = 0` for `r ≤ a`
(`h' = 0` on `(-∞, a]`). Proof: both integrals equal `∫_{a}^{b} h' = h b - h a = 0`
(`intervalIntegral.integral_deriv_eq_sub`, `intervalIntegral.integral_eq_integral_of_support_subset`
or `setIntegral_eq_integral_of_forall_compl_eq_zero`), and `h a = h b = 0` by continuity. -/
def IntegralDerivZero : Prop :=
  ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h → ∀ a b : ℝ, (∀ t, h t ≠ 0 → t ∈ Icc a b) →
    (∫ t, deriv h t = 0) ∧ (∀ r : ℝ, r ≤ a → ∫ t in Ioi r, deriv h t = 0)

/-- **Fundamental theorem for a `c`-periodic function** (task `PartII-a:N02/2/8`):
`∫_{(0,c]} h' = h c - h 0 = 0` (for `c ≤ 0` the interval is empty). -/
def IntegralDerivPeriodic : Prop :=
  ∀ (c : ℝ) (h : ℝ → ℂ), ContDiff ℝ ∞ h → (∀ t, h (t + c) = h t) →
    ∫ t in Ioc (0 : ℝ) c, deriv h t = 0

/-- **Partial derivatives are derivatives of the coordinate slices** (task `PartII-a:N02/2/9`):
`pdS F (s,q,η) = d/dt F(t,q,η)|_{t=s}` and the same for `q`, `η` (chain rule through
`t ↦ (t, q, η)` etc.; `F` is differentiable). -/
def PartialDerivSlice : Prop :=
  ∀ (F : Profile → ℂ), ContDiff ℝ ∞ F → ∀ s q η : ℝ,
    pdS F (s, q, η) = deriv (fun t : ℝ => F (t, q, η)) s ∧
      pdQ F (s, q, η) = deriv (fun t : ℝ => F (s, t, η)) q ∧
      pdEta F (s, q, η) = deriv (fun t : ℝ => F (s, q, t)) η

/-- **Fubini on the cell, order `(s, q, η)`** (task `PartII-a:N02/2/10`): for `G` integrable on the
cell `Ioi 0 ×ˢ Ioc 0 c ×ˢ univ`, the cell integral is the iterated integral with `η` innermost
(`MeasureTheory.setIntegral_prod` applied twice, or `integral_prod` for the restricted measures
`Measure.prod_restrict`). -/
def CellFubiniEta : Prop :=
  ∀ (c : ℝ) (G : Profile → ℂ), IntegrableOn G (cell c) →
    ∫ p in cell c, G p =
      ∫ s in Ioi (0 : ℝ), ∫ q in Ioc (0 : ℝ) c, ∫ η : ℝ, G (s, q, η)

/-- **Fubini on the cell, order `(s, η, q)`** (task `PartII-a:N02/2/11`): the same with `q`
innermost (first `CellFubiniEta`-type unfolding, then `MeasureTheory.integral_integral_swap` for the
`(q, η)` slice, which is integrable for almost every `s`). -/
def CellFubiniQ : Prop :=
  ∀ (c : ℝ) (G : Profile → ℂ), IntegrableOn G (cell c) →
    ∫ p in cell c, G p =
      ∫ s in Ioi (0 : ℝ), ∫ η : ℝ, ∫ q in Ioc (0 : ℝ) c, G (s, q, η)

/-- **Fubini on the cell, order `(q, η, s)`** (task `PartII-a:N02/2/12`): the same with `s`
innermost. -/
def CellFubiniS : Prop :=
  ∀ (c : ℝ) (G : Profile → ℂ), IntegrableOn G (cell c) →
    ∫ p in cell c, G p =
      ∫ q in Ioc (0 : ℝ) c, ∫ η : ℝ, ∫ s in Ioi (0 : ℝ), G (s, q, η)

/-- **Unweighted `s`-integration by parts on the cell** (task `PartII-a:N02/2/13`): for a complex
band test `G`, `∫_{cell} ∂_s G = 0` (`BandIntegrable`, `CTestFderiv` for `∂_s G`, `CellFubiniS`,
`PartialDerivSlice`, `IntegralDerivZero` for `t ↦ G(t, q, η)`, which vanishes outside
`[s₀, s₁] ⊂ (0, ∞)`). -/
def IbpSCell : Prop :=
  ∀ (c : ℝ) (G : Profile → ℂ), IsCTest c G → ∫ p in cell c, pdS G p = 0

/-! ### The top-level leaves used by the assembly -/

/-- **`q`-integration by parts with the weight** (task `PartII-a:N02/2/15`): for a complex band test
`F`, `∫_{cell} s^{-3/2} ∂_q F = 0` (`c`-periodicity). `BandIntegrable` (weighted part, applied to
the band test `∂_q F`, `CTestFderiv`), `CellFubiniQ`, the weight is a constant factor of the
`q`-integral (`integral_const_mul`), `PartialDerivSlice`, `IntegralDerivPeriodic` for
`t ↦ F(s, t, η)`. -/
def IbpQCell : Prop :=
  ∀ (c : ℝ) (F : Profile → ℂ), IsCTest c F →
    ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ F p = 0

/-- **`η`-integration by parts with the weight** (task `PartII-a:N02/2/14`): for a complex band test
`F`, `∫_{cell} s^{-3/2} ∂_η F = 0` (`CellFubiniEta`, the weight is a constant factor of the
`η`-integral, `PartialDerivSlice`, `IntegralDerivZero` for `t ↦ F(s, q, t)`, supported in
`[-L, L]`). -/
def IbpEtaCell : Prop :=
  ∀ (c : ℝ) (F : Profile → ℂ), IsCTest c F →
    ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdEta F p = 0

/-- **`K` is anti-self-adjoint for `s^{-3/2} ds dq dη`** (task `PartII-a:N02/2/16`): for a complex
band test `F`, `∫_{cell} s^{-3/2} (K F) = 0`, `K = 2s∂_s + η∂_η`. Proof: on `s > 0`
`s^{-3/2} K F = 2 ∂_s(s^{-1/2} F) + s^{-3/2} ∂_η(η F)`: indeed
`2 ∂_s(s^{-1/2} F) = 2 s^{-1/2} ∂_sF - s^{-3/2} F` (`PdAgeScale`, `s^{-3/2} s = s^{-1/2}`) and
`∂_η(η F) = F + η ∂_ηF`. The first term integrates to zero by `IbpSCell` for the band test
`s^{-1/2} F` (`CTestAgeScale`), the second by `IbpEtaCell` for the band test `η F`
(`CTestAlgebra`); split the integral using `BandIntegrable`. -/
def IbpKCell : Prop :=
  ∀ (c : ℝ) (F : Profile → ℂ), IsCTest c F →
    ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK F p = 0

/--
`Tasks/N02LerayComparison/StreamMember/IntegralMeasureHCell.lean`; the analog of
`B0226.integral_measureH_ageScale`): `∫ G d(measureH c) = ∫_{cell} s^{-3/2} G ds dq dη`, by
`integral_withDensity_eq_integral_toReal_smul` (`measurable_weightH`, `ae_weightH_lt_top`) and
`ENNReal.toReal_ofReal` on the cell, where `s > 0`. -/
def IntegralMeasureHCell : Prop :=
  ∀ (c : ℝ) (G : Profile → ℂ),
    ∫ p, G p ∂(measureH c) = ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * G p

/-- **`L²` membership of the stream field** (task `PartII-a:N02/2/18`): `streamC ε ψ` is continuous
(its components are `-ψ_η`, `ψ_q - εKψ + εψ`, continuous by `CTestFderiv`, `CTestOpK`) and vanishes
outside the band, hence is in `L²(measureH c)` (`NearGradMemberAux.memLp_of_band`,
`NearGradMemberAux.continuous_mk` in `Tasks/N02LerayComparison/GradMember.lean`). -/
def StreamMemLp : Prop :=
  ∀ (ε c : ℝ) (ψ : Profile → ℂ), IsCTest c ψ → MemLp (streamC ε ψ) 2 (measureH c)

/--
`Tasks/N02LerayComparison/StreamMember/InnerCgradStream.lean`):
for a real profile test `Φ` with complexification `Φc`, and `C^∞` `ψ`,
`⟪cgrad ε Φ p, streamC ε ψ p⟫ = ∂_q(Φc_η ψ) - ∂_η(Φc_q ψ) + ε (K(Φc ψ_η) + ∂_η(Φc (ψ - Kψ)))`.
Proof: `inner` on `EuclideanSpace ℂ (Fin 2)` is `∑ conj(u i) v i` and `cgrad` is real-valued;
`(Deps ε Φ p : ℂ) = pdQ Φc p - ε opK Φc p` and `(Axi.dEta Φ p : ℂ) = pdEta Φc p` (chain rule through
`Complex.ofRealCLM`; `fderiv_ofReal` is `HasFDerivAt.comp`); then `integrand_identity`
(`Tasks/N02LerayComparison/StreamMember/Identity.lean`) is exactly this formula. -/
def InnerCgradStream : Prop :=
  ∀ (ε c : ℝ) (Φ : ProfileTest c) (Φc : Profile → ℂ), (∀ x, Φc x = (Φ.1 x : ℂ)) →
    ∀ (ψ : Profile → ℂ), ContDiff ℝ ∞ ψ → ∀ p : Profile,
      inner ℂ (cgrad ε Φ.1 p) (streamC ε ψ p) =
        pdQ (fun x => pdEta Φc x * ψ x) p - pdEta (fun x => pdQ Φc x * ψ x) p
          + (ε : ℂ) * (opK (fun x => Φc x * pdEta ψ x) p
              + pdEta (fun x => Φc x * (ψ x - opK ψ x)) p)

/-! ### The conditional theorem -/

/-- **Stream fields of band potentials are `ε`-solenoidal, conditional on the leaves** (task
`PartII-a:N02/2`). -/
theorem nearStreamMember_of
    (hFd : CTestFderiv) (hAlg : CTestAlgebra) (hK : CTestOpK) (hInt : BandIntegrable)
    (hQ : IbpQCell) (hEta : IbpEtaCell) (hKc : IbpKCell)
    (hMeas : IntegralMeasureHCell) (hMem : StreamMemLp) (hIn : InnerCgradStream) :
    NearStreamMember := by
  intro ε c ψ hψ
  refine ⟨hMem ε c ψ hψ, ?_⟩
  -- the pairing with every real gradient vanishes
  have key : ∀ Φ : ProfileTest c,
      ∫ p, inner ℂ (cgrad ε Φ.1 p) (streamC ε ψ p) ∂(measureH c) = 0 := by
    intro Φ
    obtain ⟨Φc, hΦc⟩ : ∃ Φc : Profile → ℂ, Φc = fun y => (Φ.1 y : ℂ) := ⟨_, rfl⟩
    have hΦC : IsCTest c Φc := hΦc ▸ hAlg.1 c Φ.1 Φ.2
    have hΦq : IsCTest c (pdQ Φc) := hFd c Φc hΦC (0, 1, 0)
    have hΦe : IsCTest c (pdEta Φc) := hFd c Φc hΦC (0, 0, 1)
    have hψe : IsCTest c (pdEta ψ) := hFd c ψ hψ (0, 0, 1)
    have hψK : IsCTest c (opK ψ) := hK c ψ hψ
    have hsub : IsCTest c (fun x => ψ x - opK ψ x) := hAlg.2.2.1 c ψ (opK ψ) hψ hψK
    have hF1 : IsCTest c (fun x => pdEta Φc x * ψ x) :=
      hAlg.2.2.2 c ψ (pdEta Φc) hψ hΦe.smooth hΦe.periodic
    have hF2 : IsCTest c (fun x => pdQ Φc x * ψ x) :=
      hAlg.2.2.2 c ψ (pdQ Φc) hψ hΦq.smooth hΦq.periodic
    have hF3 : IsCTest c (fun x => Φc x * pdEta ψ x) :=
      hAlg.2.2.2 c (pdEta ψ) Φc hψe hΦC.smooth hΦC.periodic
    have hF4 : IsCTest c (fun x => Φc x * (ψ x - opK ψ x)) :=
      hAlg.2.2.2 c _ Φc hsub hΦC.smooth hΦC.periodic
    have i1 : IntegrableOn (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        pdQ (fun x => pdEta Φc x * ψ x) p) (cell c) := (hInt c _ (hFd c _ hF1 (0, 1, 0))).2
    have i2 : IntegrableOn (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        pdEta (fun x => pdQ Φc x * ψ x) p) (cell c) := (hInt c _ (hFd c _ hF2 (0, 0, 1))).2
    have i3 : IntegrableOn (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        opK (fun x => Φc x * pdEta ψ x) p) (cell c) := (hInt c _ (hK c _ hF3)).2
    have i4 : IntegrableOn (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        pdEta (fun x => Φc x * (ψ x - opK ψ x)) p) (cell c) :=
      (hInt c _ (hFd c _ hF4 (0, 0, 1))).2
    rw [hMeas c]
    have e : ∀ p : Profile, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          inner ℂ (cgrad ε Φ.1 p) (streamC ε ψ p) =
        (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ (fun x => pdEta Φc x * ψ x) p
          - ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdEta (fun x => pdQ Φc x * ψ x) p)
          + (ε : ℂ) * (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => Φc x * pdEta ψ x) p
            + ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
              pdEta (fun x => Φc x * (ψ x - opK ψ x)) p) := by
      intro p
      rw [hIn ε c Φ Φc (fun x => by rw [hΦc]) ψ hψ.smooth p]
      ring
    simp_rw [e]
    have j1 := hQ c _ hF1
    have j2 := hEta c _ hF2
    have j3 := hKc c _ hF3
    have j4 := hEta c _ hF4
    have k12 : Integrable (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        pdQ (fun x => pdEta Φc x * ψ x) p - ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        pdEta (fun x => pdQ Φc x * ψ x) p) (volume.restrict (cell c)) := i1.sub i2
    have k34 : Integrable (fun p => (ε : ℂ) * (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        opK (fun x => Φc x * pdEta ψ x) p + ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        pdEta (fun x => Φc x * (ψ x - opK ψ x)) p)) (volume.restrict (cell c)) :=
      (i3.add i4).const_mul (ε : ℂ)
    rw [integral_add k12 k34, integral_sub i1 i2, integral_const_mul, integral_add i3 i4,
      j1, j2, j3, j4]
    simp
  -- orthogonality to the span of the generators
  show _ ∈ (Submodule.span ℂ _)ᗮ
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨Φ, hmΦ, rfl⟩ := hg
    rw [L2.inner_def]
    rw [← key Φ]
    refine integral_congr_ae ?_
    filter_upwards [hmΦ.coeFn_toLp, (hMem ε c ψ hψ).coeFn_toLp] with p h1 h2
    rw [h1, h2]
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

end UnforcedLeray.Short.PartIIa
