import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2
import UnforcedLeray.Lib.Sobolev.WeakDeriv

/-!
# `PartIII-a:T21/2/7/2/1/1`: interior smoothing of a weak reverse-time adjoint (vocabulary, leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061
(the reverse-time adjoint `-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)` and its weighted energies `E_j`, the
squared weighted `H^j_{-m}` norms), 3062-3071 (the energy inequalities `E_0' + β E_1 ≤ C E_0`,
`E_1' + β E_2 ≤ C(E_1 + E_0)`), 3052-3058 (the adjoint localized interaction maps `X_{-m}` to
`H^1_{-m}`: a nonlocal term of order `-1`; near/far splitting of the Biot-Savart kernel, the
horizontal mean), 3044-3050 (the periodic weight `p_d`, its logarithmic derivatives, bounded train
coefficients), 270-288 and 2866-2870 (the train: smooth, `BUC`, every fixed weighted derivative
norm).

## The route

`AdjointInteriorSmooth m` (`Sub/PartIII-a_T21_2_7_2_1.lean`) asks for a version of a weak adjoint
`φ` (`IsAdjointWeak`) jointly `C^∞` on `(t, s) × ℝ²`.  The term `K_c^T(φ∇E)` is not local in `x`:
its time derivatives pair `∂_r^j(φ∇E)` with the Biot-Savart kernel on the whole cylinder, so they
need `∂_r^j φ` globally in a weighted space and every weighted derivative of the train at the
fixed `ν`.  The time-local bounds `LadTrainBdd` (bounded `v`, `⟨x⟩^{m+2}|∇E|` bounded) give neither:
they control `∇E` but no derivative of it.  The smoothing is therefore done globally in space, in
the weighted scale `H^k_{-m,c}` of SP 3060-3061, with the weighted jets `TrainSTJets` of the train:

1. `AdjTestedDeriv` (the distributional form of `IsAdjointWeak.weak`): `d/dr ∫ φ(r)ψ = -∫ φ(r)Aψ`
   for every cylinder test `ψ` (leaf `AdjTestedDerivOf`);
2. `IsCellJet`, `AdjHkOn`: `φ(r) ∈ H^k_{-m,c}` with `c`-periodic weak derivatives in `X_{-m,c}`, and
   `φ ∈ C(I; H^k_{-m,c})`; the base `k = 0` is `IsAdjointWeak` itself (`adjHkOn_zero_of_weak`);
3. the bootstrap step `C((t,s); H^k) → C((t,s); H^{k+1})` (leaf `AdjHkStep`), then all time
   derivatives from the equation (`IsAdjTimeJets`, leaf `AdjTimeJetsOf`);
4. Sobolev embedding with the almost-everywhere bookkeeping: the time jets give a jointly
   measurable version in `H^∞_loc((t,s) × ℝ²)` (`IsSTSobolevLoc`, leaf `TimeJetsSTSobolev`), which
   has a `C^∞` version (`STSobolevSmoothRep`), equal to `φ(r)` almost everywhere for every `r`
   (`STRepSliceAe`).
The conclusion with the jets as hypothesis is `AdjointInteriorSmoothJets` (the analytic core).
The jets come from the `BUC` class (`TrainSTJetsOfBUC`, SP 270-288, 2866-2870; the conclusion for
`BUC` trains is `AdjointInteriorSmoothBUC`), and the `BUC` class from the bounds `LadTrainBdd`
(`TrainBUCOfBdd`, the uniqueness of SP 270-288).  The assemblies are in `Assembly.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The train at a fixed viscosity -/

/-- **Every weighted space-time derivative of the train is bounded on `[0, S]`** (SP 270-288: the
train is smooth and in `BUC`; SP 2866-2870: every fixed weighted derivative norm).  All joint
`(ρ, x)`-derivatives of the velocity are bounded on `[0, S] × ℝ²`, and all joint derivatives of
positive order of the vorticity `E` are bounded with the weight `(1 + x₂²)^{(m+1)/2}` (derivatives
within `[0, ∞) × ℝ²`, one-sided at the age `0`, as in `B0140.IsTrain.smooth_v`).  These are the
coefficient bounds of the smoothing to all orders: the derivatives of `v` in the transport term, and
`⟨x⟩^m ∂^j∇E ∈ L¹ ∩ L²` of the cell for the adjoint localized interaction `K_c^T(φ ∂^j∇E)`,
`φ ∈ X_{-m,c}` (SP 3052-3058). -/
def TrainSTJets {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m S : ℝ) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤ C ∧
      (1 + x.2 ^ 2) ^ ((m + 1) / 2) *
        ‖iteratedFDerivWithin ℝ (n + 1)
          (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
          (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤ C

/-! ## Spatial jets in the weighted scale -/

/-- **`f ∈ H^k_{-m,c}` with its derivative fields** (SP 3060-3061: `E_j` is the squared weighted
`H^j_{-m}` norm; on the cell the periodic weight `p_d` of SP 3044-3047 and `⟨x⟩^{2m}` are
equivalent, so this is `Cyl.H` of `Lib/CylinderB/Space.lean` with the weight `ρw^{-m}`, up to
equivalent norms).  `D w` is the periodic weak derivative `∂^w f` (the word convention of
`adjSpatial`: `D (j :: w) = ∂_j (D w)`, tested by `HasWeakCellDerivC` against the cylinder tests),
and every field of order `≤ k` is `c`-periodic and lies in `X_{-m,c}`. -/
structure IsCellJet (c m : ℝ) (k : ℕ) (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ) :
    Prop where
  base : D [] = f
  periodic : ∀ w : List (Fin 2), w.length ≤ k → ∀ x : ℝ × ℝ, D w (x.1 + c, x.2) = D w x
  memX : ∀ w : List (Fin 2), w.length ≤ k → MemLp (D w) 2 (B0579.cellMeasure c (-m))
  deriv : ∀ (j : Fin 2) (w : List (Fin 2)), w.length < k →
    HasWeakCellDerivC c j (D w) (D (j :: w))

/-- **`φ ∈ C(I; H^k_{-m,c})`**: every slice `φ(r)`, `r ∈ I`, lies in `H^k_{-m,c}` with derivative
fields `D r`, and every field `r ↦ D r w`, `|w| ≤ k`, is continuous into `X_{-m,c}` within `I`. -/
def AdjHkOn (c m : ℝ) (k : ℕ) (I : Set ℝ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∃ D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ, (∀ r ∈ I, IsCellJet c m k (φ r) (D r)) ∧
    ∀ w : List (Fin 2), w.length ≤ k → ∀ r ∈ I,
      Tendsto (fun r' => xNorm c (-m) (D r' w - D r w)) (𝓝[I] r) (𝓝 0)

/-- **Time jets** `Φ j = ∂_r^j φ` on `I`: every `Φ j` lies in `C(I; H^k_{-m,c})` for every `k`, and
`Φ (j + 1)` is the derivative of `Φ j` within `I`, in `X_{-m,c}`. -/
def IsAdjTimeJets (c m : ℝ) (I : Set ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ) : Prop :=
  (∀ j k : ℕ, AdjHkOn c m k I (Φ j)) ∧
    ∀ j : ℕ, ∀ r ∈ I, Tendsto (fun r' => xNorm c (-m)
        (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r x) - Φ (j + 1) r x))
      (𝓝[I \ {r}] r) (𝓝 0)

/-! ## The differentiated weak equation -/

/-- **The differentiated weak equation** (SP 3060; the distributional form of `IsAdjointWeak.weak`
on `(t, s) × C_c`): for every cylinder test `ψ` (any circulation) with kernel velocity `uψ = K_cψ`,
the tested right-hand side `r ↦ ∫ φ(r) Aψ(r)` (`Aψ = νΔψ - v·∇ψ - (K_cψ)·∇E`, `adjIntegrand`) is
continuous on `[t, s]`, and `d/dr ∫ φ(r)ψ = -∫ φ(r)Aψ(r)` within `[t, s]`.  Tested against
`η(r)ψ(x)`, `η ∈ C_c^∞((t, s))`, this is `-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)` in distributions. -/
def AdjTestedDeriv {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
    ContinuousOn (fun r => ∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x) (Icc t s) ∧
      ∀ r ∈ Icc t s, HasDerivWithinAt (fun r' => ∫ x in B0579.cell c, φ r' x * (ψ x : ℂ))
        (-∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x) (Icc t s) r

/-! ## Local Sobolev classes on open sets of space-time -/

section OpenDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- An open set `U` as a test domain of `Lib/Sobolev`: the tests `C_c^∞` with `tsupport ⊆ U`,
pairing measure `μ|_U`, directions `dir`.  The fundamental lemma is Mathlib's open-set version
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
def openTestDomain (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {n : ℕ} (dir : Fin n → E)
    (U : Set E) (hU : IsOpen U) : UnforcedLeray.Sob.TestDomain E n where
  μ := μ.restrict U
  dir := dir
  Adm φ := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U
  smooth h := h.1
  deriv_mem h v := ⟨UnforcedLeray.Sob.contDiff_dirDeriv h.1 v, h.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩
  supp {φ} h := ⟨tsupport φ, h.2.1, Eventually.of_forall fun _ hx =>
    image_eq_zero_of_notMem_tsupport hx⟩
  finite := inferInstance
  ae_zero g hg hφ := by
    have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := μ.restrict U)
      (hg.locallyIntegrableOn U) (fun ψ hψ hψc hψU => by
        simpa only [smul_eq_mul] using hφ ψ ⟨hψ, hψc, hψU⟩)
    filter_upwards [key, ae_restrict_mem hU.measurableSet] with x h1 h2
    simpa using h1 h2

end OpenDomain

/-- The space-time coordinate directions of `ℝ × ℝ²`: `∂_r`, `∂_{x₁}`, `∂_{x₂}`. -/
def stDir : Fin 3 → ℝ × (ℝ × ℝ) := ![(1, (0, 0)), (0, (1, 0)), (0, (0, 1))]

/-- An open set of space-time as a test domain (Lebesgue measure, tests `C_c^∞(U)`). -/
def stDomain (U : Set (ℝ × (ℝ × ℝ))) (hU : IsOpen U) :
    UnforcedLeray.Sob.TestDomain (ℝ × (ℝ × ℝ)) 3 :=
  openTestDomain volume stDir U hU

/-- **`F ∈ H^∞_loc(U)`** on an open set `U` of space-time: `F ∈ L²_loc(U)`, and for every word `l`
in the coordinate directions the weak derivative `∂^l F` (`Sob.HasWeakDeriv` for the tests
`C_c^∞(U)`) exists in `L²_loc(U)`. -/
def IsSTSobolevLoc (U : Set (ℝ × (ℝ × ℝ))) (hU : IsOpen U) (F : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  (∀ K : Set (ℝ × (ℝ × ℝ)), IsCompact K → K ⊆ U → MemLp F 2 (volume.restrict K)) ∧
    ∀ l : List (Fin 3), ∃ g : ℝ × (ℝ × ℝ) → ℂ,
      (∀ K : Set (ℝ × (ℝ × ℝ)), IsCompact K → K ⊆ U → MemLp g 2 (volume.restrict K)) ∧
        UnforcedLeray.Sob.HasWeakDeriv (stDomain U hU) (l.map stDir) F g

/-! ## The leaves -/

/-- **A bounded train is the `BUC` train** (SP 270-288: the Gallay-Slijepčević solution is the
unique global mild solution in `BUC`, smooth for positive time; a train with the time-local bounds
`LadTrainBdd` on every `[0, S]` has bounded velocity and a bounded Lipschitz vorticity, hence a
bounded uniformly continuous velocity, and a bounded classical solution with decaying pressure is
mild).  Not derivable from `B0140.IsTrain` alone (`Short/PartI/TrainClass.lean`). -/
def TrainBUCOfBdd (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → UnforcedLeray.Short.PartI.IsBUCTrain tr

/-- **The weighted jets of the `BUC` train at a fixed viscosity** (SP 270-288, 2866-2870): the
spatial derivatives of `v` are bounded (`IsBUCTrain`); its time derivatives through the vorticity
equation `∂_ρE = νΔE - v·∇E` and `v = K_cE` (zero circulation, decaying stream); the weight on
the vorticity derivatives by interpolation between `⟨x⟩^{m+2}|∇E| ≤ C` (`LadTrainBdd`) and the
unweighted bounds of the higher derivatives. -/
def TrainSTJetsOfBUC (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → ∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S

/-- **(1a) The tested right-hand side is continuous** (SP 3060): for a weak adjoint and every
cylinder test `ψ` with kernel velocity `uψ`, `r ↦ ∫ φ(r) Aψ(r)` is continuous on `[t, s]`:
`φ ∈ C([t, s]; X_{-m,c})` (`IsAdjointWeak.strongCont`), and the multiplier
`Aψ(r) = νΔψ - v(r)·∇ψ - uψ·∇E(r)` is bounded in `X_{m,c}` uniformly on `[t, s]` (`v` bounded and
`⟨x⟩^{m+2}|∇E|` bounded by `LadTrainBdd`, `uψ` in `L²` plus its bounded mean shear, `ψ` vanishing
for `|x₂|` large) and converges pointwise as `r' → r` (smoothness of the train); weighted
Cauchy-Schwarz and dominated convergence. -/
def AdjTestedRhsCont (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
        IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
        ContinuousOn (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr (φ r) r ψ uψ x)
          (Icc t s)

/-- **(1) The differentiated weak equation** (SP 3060): the weak identity `IsAdjointWeak.weak`
`∫ φ(r)ψ = ∫ gψ + ∫_r^s ∫ φ(r')Aψ(r') dr'` with a continuous tested right-hand side
(`AdjTestedRhsCont`) gives `AdjTestedDeriv` by the fundamental theorem of calculus. -/
def AdjTestedDerivOf (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ

/-- **(3) One step of the spatial bootstrap** (SP 3060-3071 with SP 3052-3058): a weak adjoint in
`C((t, s); H^k_{-m,c})` lies in `C((t, s); H^{k+1}_{-m,c})`.  The weighted energies `E_j` satisfy
`E_j' + βE_{j+1} ≤ C(E_j + ⋯ + E_0)` in the reverse time (diffusion-weight errors through the
logarithmic derivatives of the weight, SP 3044-3050; Reynolds cancellation of the transport term;
the adjoint localized interaction is of order `-1`, `K_c^T(·∇E) : H^j_{-m} → H^{j+1}_{-m}`,
SP 3052-3058, with the weighted jets of the train), integrated against a time cutoff on every
`[a, b] ⊂ (t, s)`; the weak solution is regularized in `x` to justify the energy identity. -/
def AdjHkStep (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      ∀ k : ℕ, AdjHkOn (ν ^ (-2 : ℝ)) m k (Ioo t s) φ →
        AdjHkOn (ν ^ (-2 : ℝ)) m (k + 1) (Ioo t s) φ

/-- **The time derivatives from the equation** (SP 3060: `-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)`): a weak
adjoint in `C((t, s); H^k_{-m,c})` for every `k` has time jets `Φ`, `Φ 0 = φ`: `Φ 1 = -(νΔφ + v·∇φ -
K_c^T(φ∇E))` (from `AdjTestedDeriv`, integrating by parts on the cylinder), and
`Φ (j+1) = Σ_i (j choose i) L^{(i)}(r) Φ (j-i)` for the operator family
`L(r) = -(νΔ + v(r)·∇ - K_c^T(·∇E(r)))`, smooth in `r` from `H^{k+2}_{-m,c}` to `H^k_{-m,c}` by the
space-time jets of the train. -/
def AdjTimeJetsOf (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      (∀ k : ℕ, AdjHkOn (ν ^ (-2 : ℝ)) m k (Ioo t s) φ) →
      ∃ Φ : ℕ → ℝ → ℝ × ℝ → ℂ, Φ 0 = φ ∧ IsAdjTimeJets (ν ^ (-2 : ℝ)) m (Ioo t s) Φ

/-- **(4a) Space-time Sobolev regularity from the time jets**: time jets on `(t, s)` have a jointly
measurable version `F` (`F(r, ·) = Φ 0 r` almost everywhere for every `r`) in
`H^∞_loc((t, s) × ℝ²)`.  The weak derivative `∂_r^j ∂_x^w F` is the field `w` of `Φ j`: integrate by
parts in `r` against the `X_{-m,c}`-derivatives and in `x` against the periodic weak derivatives
(periodize the space-time test in `x₁`); on compact sets the weight of `X_{-m,c}` is bounded below. -/
def TimeJetsSTSobolev : Prop :=
  ∀ (c m t s : ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ), 0 < c → t < s →
    IsAdjTimeJets c m (Ioo t s) Φ →
    ∃ F : ℝ × (ℝ × ℝ) → ℂ, (∀ r ∈ Ioo t s, (fun x => F (r, x)) =ᵐ[volume] Φ 0 r) ∧
      IsSTSobolevLoc (Ioo t s ×ˢ univ) (isOpen_Ioo.prod isOpen_univ) F

/-- **(4b) Sobolev embedding on an open set of space-time**: `H^∞_loc(U)` has a `C^∞` version on
`U` (multiply by cutoffs `ζ ∈ C_c^∞(U)`, transfer to `ℝ³`, `H^{k+2}(ℝ³) ⊂ C^k`
(`Sob.W.exists_contDiff_rep`), and glue: continuous versions equal almost everywhere on an open
set agree there). -/
def STSobolevSmoothRep : Prop :=
  ∀ (U : Set (ℝ × (ℝ × ℝ))) (hU : IsOpen U) (F : ℝ × (ℝ × ℝ) → ℂ), IsSTSobolevLoc U hU F →
    ∃ F' : ℝ × (ℝ × ℝ) → ℂ, ContDiffOn ℝ ∞ F' U ∧ ∀ᵐ p ∂volume, p ∈ U → F' p = F p

/-- **(4c) The slices of a continuous version**: if `F'` is continuous on `(t, s) × ℝ²` and equal
almost everywhere there to a version `F` of a path `f ∈ C((t, s); X_{-m,c})` of `c`-periodic
functions, then `F'(r, ·) = f(r)` almost everywhere for EVERY `r ∈ (t, s)` (Fubini for almost every
`r`; then continuity: `F'(r_n, ·) → F'(r, ·)` uniformly on compacts and `f(r_n) → f(r)` in `L²_loc`,
by periodicity and the lower bound of the weight on compacts). -/
def STRepSliceAe : Prop :=
  ∀ (c m t s : ℝ) (f : ℝ → ℝ × ℝ → ℂ) (F F' : ℝ × (ℝ × ℝ) → ℂ), 0 < c → t < s →
    AdjHkOn c m 0 (Ioo t s) f → (∀ r ∈ Ioo t s, (fun x => F (r, x)) =ᵐ[volume] f r) →
    ContinuousOn F' (Ioo t s ×ˢ univ) → (∀ᵐ p ∂volume, p ∈ Ioo t s ×ˢ univ → F' p = F p) →
    ∀ r ∈ Ioo t s, (fun x => F' (r, x)) =ᵐ[volume] f r

/-- **Interior parabolic regularity with the weighted jets of the train** (SP 3060-3061,
3052-3058, 2866-2870): `AdjointInteriorSmooth m` for trains with every weighted space-time
derivative bounded on every `[0, S]` (`TrainSTJets`).  This is the analytic core; the train
hypothesis is supplied by `TrainSTJetsOfBUC` (BUC trains), or by any restatement of the smoothing
chain that carries the jets of the train (e.g. `TrainJointJets` of
`Sub/PartIII-a_T21_2_7_2_1_2.lean`, which implies `TrainSTJets`: `E = curl v`). -/
def AdjointInteriorSmoothJets (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∃ φ' : ℝ → ℝ × ℝ → ℂ, (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] φ r) ∧
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ)

/-- **Interior parabolic regularity for the `BUC` train** (SP 3060-3061, 3052-3058; the train of
SP 270-288): `AdjointInteriorSmooth m` for the trains of the class `PartI.IsBUCTrain`. -/
def AdjointInteriorSmoothBUC (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∃ φ' : ℝ → ℝ × ℝ → ℂ, (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] φ r) ∧
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ)

/-! ## The base of the bootstrap -/

/-- **The base `k = 0`**: a weak adjoint lies in `C((t, s); X_{-m,c})` (the fields `memX`, `periodic`
and `strongCont` of `IsAdjointWeak`; the jets are the slices themselves). -/
theorem adjHkOn_zero_of_weak {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsAdjointWeak ν c m tr t s g φ) :
    AdjHkOn c m 0 (Ioo t s) φ := by
  refine ⟨fun r _ => φ r, fun r hr => ⟨rfl, fun _ _ x => hφ.periodic r ⟨hr.1.le, hr.2⟩ x,
    fun _ _ => hφ.memX r ⟨hr.1.le, hr.2.le⟩, fun _ _ hw => absurd hw (Nat.not_lt_zero _)⟩,
    fun _ _ r hr => ?_⟩
  exact (hφ.strongCont r ⟨hr.1.le, hr.2.le⟩).mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)

end UnforcedLeray.Short.IIIa
