import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Column
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps
import UnforcedLeray.Short.PartIIIb.NearInst
import UnforcedLeray.Short.PartI.TrainClass

/-!
# The leaves of `IsFlatDuhamelColumn` for the concrete flat setting (source 3420-3446,
4594-4615, 1650-1689, 4761-4763)

Source of record: `the November 2 reference manuscript` (73 pages).

`Kflat.IsFlatDuhamelColumn S hc tr μ as χf` says that the Duhamel readout `𝔗A = M_{B[A]}` of the
flat setting `S` (`B = B_{μ,ν}[A]`, 4757-4758) is a.e. the polarized stress `v⊗b + b⊗v` of the
forced column `b = R₀h - S₀M₀b` of the near operators.  For the concrete setting
`actualFlatSetting D χo ε` (`Setting.lean`) the proof (`Assembly.lean`) is: both columns are
zero-entrance forced columns of the same equation with the force `f_A` (`forceC`), and such columns
are unique.  The leaves:

* (a) `FlatForceCurl` : the vorticity of `f_B` is `g_B` (4597-4608);
* (b) the Duhamel column `K_cξ_B` is a forced column: `FlatXiRegular` (4614-4615),
  `KcPathEnergy` (energy class), `FlatColumnVorticity` (the Duhamel formula 4610 in weak vorticity
  form, from the pin of `𝒰`), `VorticityToVelocity` (3511-3514: "the velocity equation follows from
  its curl and divergence equations"), `FlatForceLocal` (local integrability of `f_A`) and
  `FlatForceDecay` (Gaussian decay of `f_A` in `η`; together: `f_A` is `L²` on age bands);
* (c) `BodyColumnFlat` : `R₀h` is the free forced column with force `s⁻¹h` (1650-1656, 1684-1689,
  `B0225.R0_Ms_ae`); the rest of (c) (`b = R₀h - S₀M₀b` solves the train equation) is proved from
  `IsFreeStress`, `IsFlatMult` (`operatorColumn_of`, `Assembly.lean`);
* (d) `FlatHomogeneousUnique` (`Column.lean`, 3541-3545), obtained from `IIIa.PolyCausal`
  (`flatHomogeneousUnique_of_polyCausal`, `Assembly.lean`);
* (e) the `Mcell` readout is definitional (`frakT_actual`, `Assembly.lean`).

Existence of the pinned data (`FlatInstData`) and the field `src_bdd` of
`ConcreteYF.FlatSettingHyp` are the statements `TrainEvolutionExists`, `FrozenPairExists`,
`GaussSourcesExist`, `FlatSrcBdd` below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart
  flowIntegrand trainVel)

/-- The affine force `f_{B_{μ,ν}[A]} = f_A` as a complex meridional field on the chart
(source 4594-4596, 4976; `F_A = s^{3/2} f_A`, 4993). -/
def forceC (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Fin 2 → ℂ :=
  NearInst.velC fun p => merOf (fA ν μ χ A p.1 p.2)

/-- The Duhamel column `b_B = K_cξ_B` (source 4610-4612), complexified, as a field on the chart. -/
def kcCol {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (D : FlatInstData κ ν c m tr) (μ : ℂ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : Chart → Fin 2 → ℂ :=
  NearInst.velC fun p => kcMer (xiD D μ B p.1) p.2

/-! ## (a) The vorticity of the force -/

/-- The `j`-th lattice term `(B_mer x_j)·∇V_j + B_mer V_j` of `-f_B` (meridional components;
source 4594-4596, 4976; `f_A = -Σ_j fTerm`, componentwise `merOf`). -/
def fTerm (ν s : ℝ) (B : Mat3) (j : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x)) + merApply B (Vj ν s j x)

/-- The curl of one lattice term at `y = x_j`, closed form: with `W = B_mer y`,
`curl[(W·∇)V + B_mer V] = (W·∇)E + (tr B_mer)E = rE'(r)(β + (d(y₁²-y₂²) + 2e y₁y₂)/r²) + 2βE(r)`
(`div V = 0`, `E` radial; `β, d, e` of source 4599-4601). -/
def curlTermProf (a : ℝ) (B : Mat3) (y : ℝ × ℝ) : ℝ :=
  gaussRdE a (planeR y) * (ConcreteYF.Bbeta B +
      (Bd B * (y.1 ^ 2 - y.2 ^ 2) + Be B * (2 * y.1 * y.2)) / (y.1 ^ 2 + y.2 ^ 2)) +
    2 * ConcreteYF.Bbeta B * gaussE a (planeR y)

/-- **(a1) The curl of one lattice term** (source 4597-4608, the computation behind "the
vorticity source is `g_B`"): `∂_q(fTerm)_η - ∂_η(fTerm)_q = curlTermProf a B x_j`, `a = 1 + νs`.
Route: `Vj = φ(|x_j|²) J x_j`, `φ = a⁻²e^{-|·|/(4a)}`; `fTerm` is `φ·(polynomial in x_j)` in closed
form (`fderiv` of `Vj` by `HasFDerivAt` of products, as in `curl_Vj`); differentiate in `q` and `η`
(`HasDerivAt`, `hasDerivAt_gaussLin`), and compare with `gaussE`, `gaussRdE` (`gaussRdE a r =
-a⁻²(r²/(2a))(4 - r²/(2a))e^{-r²/(4a)}`, from `deriv (gaussE a)`); at `x_j = 0` both sides are
`2βE(0)` (`gaussRdE a 0 = 0`). -/
def FlatCurlTerm : Prop :=
  ∀ (ν s : ℝ) (B : Mat3) (j : ℤ) (x : ℝ × ℝ), 0 ≤ ν → 0 ≤ s →
    deriv (fun q => (fTerm ν s B j (q, x.2)).2) x.1 -
        deriv (fun η => (fTerm ν s B j (x.1, η)).1) x.2 =
      curlTermProf (ageA ν s) B (xj ν j x)

/-- **(a) The vorticity of `f_B` is `g_B`** (source 4597-4608: with
`B_mer = βI + (d e; e -d) + ω J`, `B_φφ = -2β`, "the antisymmetric contribution is a periodic
gradient, annihilated by `P₀`. The vorticity source is `g_B = -½(d-ie)H_{s,c} - ½(d+ie)H̄_{s,c} -
βR_{s,c}`").  For every matrix `B` at age `s > 0` (here `B = B_{μ,ν}[A](s)`, `Bmat`) and
`c = ν⁻²` (`cOf`), in the weak cylinder form of `curl f = ∂_q f_z - ∂_η f_r` used by
`IIIa.IsBiotSavart`: `∫_cell (f_r ∂_ηψ - f_z ∂_qψ) = ∫_cell g_B ψ` for every cylinder test `ψ`. -/
def FlatForceCurl : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s →
    ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (cOf ν) ψ →
      IntegrableOn (fun x => merOf (fA ν μ χ A s x) 0 * B0579.pd 1 ψ x -
          merOf (fA ν μ χ A s x) 1 * B0579.pd 0 ψ x) (B0579.cell (cOf ν)) ∧
      ((∫ x in B0579.cell (cOf ν), (merOf (fA ν μ χ A s x) 0 * B0579.pd 1 ψ x -
          merOf (fA ν μ χ A s x) 1 * B0579.pd 0 ψ x) : ℝ) : ℂ) =
        ∫ x in B0579.cell (cOf ν), gBProf ν (cOf ν) s (Bmat ν μ χ A s) x * (ψ x : ℂ)

/-- **Local integrability of the affine force** (source 4594-4596, 4988: "the sums and their
required derivatives converge by Gaussian decay"): `f_A` is integrable on every age band
`s₁ ≤ s ≤ s₂`, `s₁ > 0`, times a bounded part `|η| ≤ R` of the cell. -/
def FlatForceLocal : Prop :=
  ∀ (ν μ as : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → IsSourceCutoffC χ → IsAffElem as A →
    ∀ s₁ s₂ R : ℝ, 0 < s₁ → ∀ i,
      IntegrableOn (fun p => forceC ν μ χ A p i)
        (Icc s₁ s₂ ×ˢ (B0579.cell (cOf ν) ∩ {x | |x.2| ≤ R}))

/-- **Decay of the affine force in `η`** (source 4594-4596, 4988: "the sums and their required
derivatives converge by Gaussian decay"; 3426-3440: the force of the causal problem lies in `𝒯`):
on every age band `s₁ ≤ s ≤ s₂`, `s₁ > 0`, the components of `f_A` on the cell are bounded by
`C/(1 + η²)`.  Route: every lattice term is `≤ C e^{-|x_j|²/(8a₂)}` with `x_j = (q - jc, η)`,
`a₂ = 1 + νs₂` (the bounds of `Proofs/FlatTermBound.lean`, `ft_term_pt`), and
`e^{-|x_j|²/(8a₂)} = e^{-(q-jc)²/(8a₂)} e^{-η²/(8a₂)}`; sum over `j` for `|q| ≤ c/2`.  With
`FlatForceLocal` this gives `f_A ∈ L²` on every band (`forceC_memLp_band`, `ForceBand.lean`), the
force hypothesis of `VorticityToVelocity`. -/
def FlatForceDecay : Prop :=
  ∀ (ν μ as : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → IsSourceCutoffC χ → IsAffElem as A →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → ∃ C : ℝ, ∀ s ∈ Icc s₁ s₂, ∀ x ∈ B0579.cell (cOf ν), ∀ i,
      ‖forceC ν μ χ A (s, x) i‖ ≤ C / (1 + x.2 ^ 2)

/-! ## (b) The Duhamel column is a forced column -/

/-- **(b1) Regularity and entrance of `ξ_B`** (source 4614-4615: "Since `g_B = O(s^{3/2})` near
zero, `ξ_B = O_{X_{m,c}}(s^{5/2})`"; 4610): `s ↦ ξ_B(s)` is continuous on `(0,∞)` into `X_{m,c}` and
`‖ξ_B(s)‖ ≤ C s^{5/2}` on `0 < s ≤ 1`.  Route: `|B(s)| ≤ C s^{3/2}` on `0 < s ≤ 1` (from `IsAffElem`:
`|(s∂_s)^jA| ≤ C s^{5/2}`, and the cutoff), `H, R` continuous (`GaussSources`), `𝒰` bounded and
jointly strongly continuous (`TrainEvolution.locBdd`, `.jointCont`), dominated convergence. -/
def FlatXiRegular : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ContinuousOn (xiD D (μ : ℂ) (Bmat ν μ χf A)) (Ioi 0) ∧
      ∃ C : ℝ, ∀ s ∈ Ioc (0 : ℝ) 1, ‖xiD D (μ : ℂ) (Bmat ν μ χf A) s‖ ≤ C * s ^ (5 / 2 : ℝ)

/-- **(b2) `K_cξ` lies in the energy class** (source 3426-3430, 4614-4615 "this causal column has
finite-energy entrance"): for a path `ξ` in `X_{m,c}`, continuous on `(0,∞)`, zero on `s ≤ 0`,
`O(s^{5/2})` at `0`, the chart field `velC (K_cξ)` has a weak gradient `G` with the six energy
clauses.  Route: `kcLp` is `realBiotSavartKernelCLM` after `reX` (continuous); a jointly measurable
representative of `s ↦ kcLp (ξ s)` (`Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_
continuousOn`) and `lebRep_congr`, `lebRep_stronglyMeasurable` give `measurable`; `G` from
`B0583.velGradQ`, `velGradEta` (real parts, `realBiotSavart_hasWeakDerivs`), with
`norm_velocity_le`, `norm_velGradQ_le`, `norm_velGradEta_le` for `energyLoc`, `zeroEntrance`
(`∫₀¹ s^{-3/2} s^5 ds < ∞`); `divFree` from `IIIa.CTE.velocityIsBiotSavart_one`. -/
def KcPathEnergy : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (ξ : ℝ → Xmc c m),
    ContinuousOn ξ (Ioi 0) → (∀ s, s ≤ 0 → ξ s = 0) →
    (∃ C : ℝ, ∀ s ∈ Ioc (0 : ℝ) 1, ‖ξ s‖ ≤ C * s ^ (5 / 2 : ℝ)) →
      ∃ G : Chart → Fin 2 → Fin 2 → ℂ,
        IsEnergyField c (NearInst.velC fun p => kcMer (ξ p.1) p.2) G

/-- **(b3) The Duhamel formula in weak vorticity form** (source 4610:
`ξ_B(s) = s^{-μ}∫₀^s t^μ 𝒰(s,t)g_B(t)dt`; 4464-4467: `(∂_s + μ/s)w = L_{ν,c}(s)w + f`): for every
cylinder test `φ` and `s > 0`,
`s^μ⟨ξ_B(s), φ⟩ = ∫₀^s t^μ⟨g_B(t), φ⟩dt + ∫₀^s r^μ ⟨L(r)ξ_B(r), φ⟩dr`, with
`⟨L(r)ω, φ⟩ = ∫_cell flowIntegrand` (the linearised vorticity operator around the actual train,
`IIIa.IsLinearisedFlow`), both integrands integrable on `(0, s]`.  Route: the pin
`TrainEvolution.flow` (`ConcreteYF.IsTrainPkg`) gives
`⟨𝒰(r,t)x, φ⟩ = ⟨x, φ⟩ + ∫_t^r ⟨L(ρ)𝒰(ρ,t)x, φ⟩dρ`; `𝒰(r,t)g_B(t)` is real (`TrainEvolution.real`,
`gBD_real`), so its Biot-Savart velocity is `kcC` (`isBiotSavart_kc`, uniqueness
`IIIa.CTE.BiotSavartUnique`); `ω ↦ ⟨L(r)ω, φ⟩` is a continuous real-linear form on real `X_{m,c}`
(it commutes with the Bochner integral of `xiD_apply`); Fubini in `(t, ρ)`. -/
def FlatColumnVorticity : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, xFn (gBD D (Bmat ν μ χf A) t) x * (φ x : ℂ)) (Ioc 0 s) ∧
      IntegrableOn (fun r : ℝ => ((r : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, flowIntegrand tr (xFn (xiD D (μ : ℂ) (Bmat ν μ χf A) r))
            (kcC (xiD D (μ : ℂ) (Bmat ν μ χf A) r)) r φ x) (Ioc 0 s) ∧
      ((s : ℂ) ^ (μ : ℂ)) * ∫ x in B0579.cell c,
          xFn (xiD D (μ : ℂ) (Bmat ν μ χf A) s) x * (φ x : ℂ) =
        (∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, xFn (gBD D (Bmat ν μ χf A) t) x * (φ x : ℂ)) +
        ∫ r in Ioc 0 s, ((r : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, flowIntegrand tr (xFn (xiD D (μ : ℂ) (Bmat ν μ χf A) r))
            (kcC (xiD D (μ : ℂ) (Bmat ν μ χf A) r)) r φ x

/-- **(b4) From the vorticity equation to the velocity equation** (source 3511-3514: "The velocity
equation follows from its curl and divergence equations: after testing in age the discrepancy is
spatial `H⁻¹`, curl-free and divergence-free; its Fourier transform is supported only at zero and
must vanish. This retains the horizontal mean"; 4610-4612).  Abstract form: if `b` is in the energy
class and is, at every age, the Biot-Savart velocity of `ω(s)`; `g(s)` is the weak curl of the force
`f`, which is in `L²` on every age band `[s₁,s₂] × cell` (source 3426-3440: the force lies in the
class `𝒯`; local integrability is not enough, the constant force `f = (1,0)` refutes the statement
with it, see `Sub/PartIII-b_C_flatset_col_6/VtvFluxRefute.lean`); and `ω` satisfies the Duhamel vorticity identity of `FlatColumnVorticity`
with velocity `b`, then `b` is a forced column with force `f` around the actual train.
Route: for a divergence-free test `Φ` (`IsFlatTest`) write `Φ = ∇^⊥ζ`,
`ζ(s,q,η) = -∫_{-∞}^η Φ_q(s,q,η')dη'` (smooth, periodic, `∇ζ` compactly supported; `ζ` constant for
`η` large: the flux, i.e. the horizontal mean, is handled by the cutoff `ζχ(η/R)`, whose error is
`O(R^{-1/2})` against `b ∈ L²`); `⟨b, ∇^⊥ζ⟩ = -⟨ω, ζ⟩` (`IsBiotSavart`), `⟨f, ∇^⊥ζ⟩ = -⟨g, ζ⟩`,
`⟨v⊗b + b⊗v, ∇∇^⊥ζ⟩ = -⟨ω, v·∇ζ⟩ + ⟨b·∇E, ζ⟩` (pure test-function algebra with `div v = 0`,
`E = curl v`: the coefficient of `b` is `∇(v₂∂_qζ - v₁∂_ηζ - Eζ)`, killed by `div b = 0`);
time-dependent tests from the integrated identity by Fubini (`d/ds⟨ω,φ⟩ = -(μ/s)⟨ω,φ⟩ +
s^{-μ}d/ds(s^μ⟨ω,φ⟩)`). -/
def VorticityToVelocity : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    0 < ν → 0 < c → UnforcedLeray.Short.PartI.IsBUCTrain tr → IsEnergyField c b G →
    (∀ s, 0 < s → IsBiotSavart c (ω s) (fun x => b (s, x))) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → ∀ i,
      MemLp (fun p => f p i) 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c))) →
    (∀ s, 0 < s → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, g s x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, (f (s, x) 0 * (B0579.pd 1 ψ x : ℂ) -
          f (s, x) 1 * (B0579.pd 0 ψ x : ℂ))) →
    (∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, g t x * (φ x : ℂ)) (Ioc 0 s) ∧
      IntegrableOn (fun r : ℝ => ((r : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, flowIntegrand tr (ω r) (fun x => b (r, x)) r φ x) (Ioc 0 s) ∧
      ((s : ℂ) ^ (μ : ℂ)) * ∫ x in B0579.cell c, ω s x * (φ x : ℂ) =
        (∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) * ∫ x in B0579.cell c, g t x * (φ x : ℂ)) +
        ∫ r in Ioc 0 s, ((r : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, flowIntegrand tr (ω r) (fun x => b (r, x)) r φ x) →
    (∀ s, 0 < s → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      IntegrableOn (fun x => ω s x * (ψ x : ℂ)) (B0579.cell c)) →
    ∀ Φ, IsFlatTest c Φ →
      IntegrableOn (forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ p = 0

/-! ## (c) The free body column -/

/-- **(c) `R₀h` is the zero-entrance free column with force `s⁻¹h`** (source 1650-1656:
`A₀ = -S + νsΔ`, `T₀ = (μ - A₀)⁻¹P₀`; 1684-1689: "The flat equation is `(∂_s + μ/s - νΔ)b = ...`.
Pairing it with `s^{-1/2}b̄` gives the coercive constant `Re μ + 1/4`"; `B0225.R0_Ms_ae`:
`R₀(μ)M_s g(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ)dσ`).  If `R0` is the real form of
`T0flat = B0225.R0 ∘ P₀` (`IsBodyTransport`) and `h = s f` a.e., then `R0 h` has a representative
in the energy class solving `∂_s b + (μ/s)b - νΔb = P₀f` against divergence-free tests.  Route:
transposition `⟨R₀(μ)P₀h, (μ - A₀*)ζ⟩ = ⟨h, ζ⟩` from the Laplace transform of the explicit
semigroup `B0224.T0` (`B0225.R0_apply`, `R0_ae_eq`), `P₀ζ = ζ` for divergence-free `ζ`
(`PepsC 0 c` is the orthogonal projection onto `solenoidalHC 0 c`); the energy identity
`(Re μ + 1/4)‖b‖²_H + ν‖∇b‖²_{H_T} ≤ ‖h‖_H‖b‖_H` for the gradient (density of nice forces); a null
set of ages for `divFree`, `weakGrad` (`IIIa.CausalNullModification`). -/
def BodyColumnFlat : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 → ∀ R0 : Hsp c →L[ℝ] Hsp c,
    NearInst.IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)) →
    ∀ (h : Hsp c) (f : Chart → Fin 2 → ℂ),
      (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i, NearInst.velC h p i = (p.1 : ℂ) * f p i) →
      ∃ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 h) ∧
          IsForcedColumn c ν (μ : ℂ) (fun _ _ _ => 0) f b G

/-! ## Existence of the pinned data and the source bound -/

/-- **The actual train evolution exists** (source 2819-2836: Volterra iteration around the actual
train; 4349-4352): for `m > 8`, small `ν`, `c = ν⁻²` and every train of the BUC class there is a
`TrainEvolution` (the pinned operator family on `X_{m,c}`).  Route: the unit-strip Volterra
evolution `Exist.actualTrainVolterraData` (`Sub/T21_3_Strip.lean`, `Sub/T21_3_Horizon.lean`) on real
zero-circulation data, glued over strips (`fullFlowExists_of_family`), complexified (`x = Re x +
i Im x`); bounded and strongly continuous (Gronwall on the strips); parity and zero circulation are
preserved (the train is odd, `B0140.IsTrain.odd`; `ZeroCirculationPreserved`); `cocycle`, `real` by
uniqueness of weak flows. -/
def TrainEvolutionExists : Prop :=
  ∀ m : ℝ, 8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ (c : ℝ), c = cOf ν →
    ∀ (_ : Fact (1 < m)) (tr : UnforcedLeray.B0140.TrainSol ν c),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → Nonempty (TrainEvolution m tr)

/-- **The frozen pair exists** (source 2894-2912, 4352-4356): for planar kernels of the Part I
seed with the uniform frame facts (`IIIa.PerFrameFactsAll`, task `PartIII-a:T21/c1/b`), for
`m > 8`, small `ν` and `c = ν⁻²`, the formulas `frozenQ`, `frozenEll` define a `FrozenPair`.  Route:
`J_aP_de_±` lies in `X_{m,c}` (Gaussian tails of `e_±`; zero circulation `∫q = 0`; central evenness of
the angular-two mode); `|frozenEll f| ≤ K a^{3/2}‖f‖` (`PerFrameFacts`, third field, and
`IIIa.ScalingBounds`); `gram` is `PerFrameFacts`' first field at the band age (`θ ≥ 1/(3ν) ≥ b` for
`ν` small); `conj_q`, `conj_ell` from `e₁ = ē₀`, `λ₁ = λ̄₀` (`IIIa.IsSeedKernels`); continuity in the
age by dominated convergence. -/
def FrozenPairExists : Prop :=
  ∀ κ : IIIa.PlanarFrameKernels, IIIa.IsSeedKernels κ → IIIa.PerFrameFactsAll κ →
    ∀ m : ℝ, 8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ (c : ℝ), c = cOf ν →
      ∀ (_ : Fact (1 < m)), Nonempty (FrozenPair κ ν c m)

/-- **The Gaussian sources lie in `X_{m,c}`** (source 4562-4570: "The vorticity sources are
centrally even and have zero circulation"): for `ν > 0`, `c = ν⁻²`, `m > 1`, the periodizations
`HProf ν c s`, `RProf ν c s` are (the planar functions of) elements of `X_{m,c}`, continuous in `s`.
Route: `|hMode a x|, |rMode a x| ≤ C(1+|x|²)² e^{-|x|²/(4a)}` with `a = srcA ν s ∈ [1, ∞)`, summable
lattice sums (`Concrete/SummableProof.lean`), `L²(⟨x⟩^{2m})` on the cell; zero circulation
`∫_cell P_c g = ∫_ℝ² g = 0` (angular integral of `e^{2iϑ}`; `∫(rE' + 2E)r dr = [r²E]₀^∞ = 0`);
central evenness `g(-x) = g(x)`; continuity in `s` by dominated convergence. -/
def GaussSourcesExist : Prop :=
  ∀ (ν m : ℝ) [Fact (1 < m)], 0 < ν → Nonempty (GaussSources ν (cOf ν) m)

/-- **The sources are bounded on the source band uniformly in the viscosity** (field `src_bdd` of
`ConcreteYF.FlatSettingHyp`; source 4565-4574: `a(t) = 1 + νt ≤ 2.1` on `0 ≤ t ≤ 1.1/ν`, the
periodic images are at distance `≥ c/2 ≥ 1/2` from the cell). -/
def FlatSrcBdd : Prop :=
  ∀ (m : ℝ) [Fact (1 < m)], ∃ C : ℝ, ∀ ν : ℝ, 0 < ν → ν ≤ 1 →
    ∀ S : GaussSources ν (cOf ν) m, ∀ t ∈ Icc (0 : ℝ) (1.1 / ν), ‖S.H t‖ ≤ C ∧ ‖S.R t‖ ≤ C

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
