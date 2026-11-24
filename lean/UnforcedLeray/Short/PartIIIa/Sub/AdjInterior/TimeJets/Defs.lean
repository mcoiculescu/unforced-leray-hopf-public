import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# `PartIII-a:T21/2/7/2/1/1/6`: the time jets of a smooth weak adjoint (vocabulary, leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061
(the reverse-time adjoint `-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)` and its weighted energies), 3052-3058
(the adjoint localized interaction `K_c^T(·∇E)`: localized source in `L¹ ∩ L²` by weighted
Cauchy-Schwarz, near/far split of the periodic Biot-Savart kernel, the horizontal mean), 270-288
and 2866-2870 (the train: smooth, every fixed weighted space-time derivative bounded).

## The route

`AdjTimeJetsOf m` (`Sub/AdjInterior/Defs.lean`) asks, for a weak adjoint `φ` in
`C((t, s); H^k_{-m,c})` for every `k`, for time jets `Φ` with `Φ 0 = φ`, `Φ (j + 1) = ∂_rΦ j` in
`X_{-m,c}`, each `Φ j` in `C((t, s); H^k_{-m,c})` for every `k`.  The equation of SP 3060 is
`∂_rφ = L(r)φ`, `L(r) = -(νΔ + v(r)·∇ - K_c^T(·∇E(r)))`; its age derivatives are the operators
`L^{(i)}(r) = -([i = 0]νΔ + ∂_r^i v(r)·∇ - K_c^T(·∂_r^i∇E(r)))` (`adjLop`), and the jets are
`Φ (j + 1) = Σ_{i ≤ j} (j choose i) L^{(i)}(r) Φ (j - i)` (`tjSeq`, Leibniz).  Everything is
classical in `x` because every `Φ j` is in `H^∞_{-m,c}`; only the age needs an argument:

* `AdjHkAll`: one family of derivative fields for all orders (from `AdjHkOn` for every `k` by the
  uniqueness of weak derivatives `WeakCellAeUnique`, leaf `AdjHkAllOf`);
* `HasXDerivOn`: the `X_{-m,c}`-derivative (the second clause of `IsAdjTimeJets`);
* the first derivative (`AdjTimeDerivBase`): `AdjTestedDeriv` and integration by parts on the
  cylinder (`AdjLopTested`, with the kernel velocity `kerVel` of the test, `KerVelIsBS`) give
  `d/dr ∫ φ(r)ψ = ∫ (L^{(0)}(r)φ(r))ψ`, and a continuous tested derivative is the `X`-derivative
  (`XDerivOfTested`, FTC for the `X_{-m,c}`-valued integral and the separation of `X_{-m,c}` by
  cylinder tests);
* the upgrade (`XDerivUpgrade`): an `X`-derivative between two `H^∞` families is the derivative of
  every field (`TestedOfXDeriv`, `XDerivOfTested`, integration by parts word by word);
* the operators preserve `C(I; H^∞_{-m,c})` (`AdjLopSmooth`) and obey the product rule
  `∂_r(L^{(i)}Ψ) = L^{(i+1)}Ψ + L^{(i)}∂_rΨ` (`AdjLopDeriv`): Leibniz fields with the smooth
  coefficients `∂_r^i v` (`LeibCellJet`, `AdjHkAllCoeffMul`, `CoeffMulDeriv`), and the kernel
  adjoint `kerAdj` (`Sub/T21_2_1/KernelDefs.lean`) of the weighted localized source
  `∂_r^i∇E · Ψ`, which commutes with derivatives and is bounded from `L¹ ∩ L²` into `X_{-m,c}`
  (`KerAdjXBound`, `KerAdjSubAE`, `KerVelConv`, `KerVelPairDeriv`, `KerAdjWeakDeriv`,
  `KerAdjPeriodic`, `WeightedMulL12`, `AdjHkAllKerMul`, `KerMulDeriv`); the coefficient bounds are
  those of `TrainSTJets` (`SliceJetBounds`, `TrainVCoeff`, `TrainECoeff`);
* the induction on `j` is abstract (`tjSeq_spec`, `Abstract.lean`); the assemblies are in
  `Assembly.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## All-orders jets and `X`-derivatives -/

/-- **`f ∈ C(I; H^k_{-m,c})` for every `k`, with one family of derivative fields `D`** (SP 3060-3061:
the energies `E_j` of every order): every slice `f r`, `r ∈ I`, is a cell jet of every order with
the fields `D r` (`IsCellJet`, word convention `D r (j :: w) = ∂_j (D r w)`), and every field
`r ↦ D r w` is continuous into `X_{-m,c}` within `I`. -/
def AdjHkAll (c m : ℝ) (I : Set ℝ) (f : ℝ → ℝ × ℝ → ℂ) (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) :
    Prop :=
  (∀ r ∈ I, ∀ k : ℕ, IsCellJet c m k (f r) (D r)) ∧
    ∀ w : List (Fin 2), ∀ r ∈ I,
      Tendsto (fun r' => xNorm c (-m) (D r' w - D r w)) (𝓝[I] r) (𝓝 0)

theorem adjHkOn_of_adjHkAll {c m : ℝ} {I : Set ℝ} {f : ℝ → ℝ × ℝ → ℂ}
    {D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ} (h : AdjHkAll c m I f D) (k : ℕ) :
    AdjHkOn c m k I f :=
  ⟨D, fun r hr => h.1 r hr k, fun w _ r hr => h.2 w r hr⟩

/-- **`f' = ∂_r f` in `X_{-m,c}` on `I`**: the difference quotients converge in `X_{-m,c}` (the
second clause of `IsAdjTimeJets`). -/
def HasXDerivOn (c m : ℝ) (I : Set ℝ) (f f' : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∀ r ∈ I, Tendsto (fun r' => xNorm c (-m)
      (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x)) (𝓝[I \ {r}] r) (𝓝 0)

theorem isAdjTimeJets_iff (c m : ℝ) (I : Set ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ) :
    IsAdjTimeJets c m I Φ ↔
      (∀ j k : ℕ, AdjHkOn c m k I (Φ j)) ∧ ∀ j : ℕ, HasXDerivOn c m I (Φ j) (Φ (j + 1)) :=
  Iff.rfl

/-! ## The operator family -/

/-- `∂_r^i v_l(r, x)`, the `i`-th age derivative of the train velocity (SP 270-288: smooth on
`[0, ∞) × ℝ²`). -/
def vJet {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) (r : ℝ) (x : ℝ × ℝ)
    (l : Fin 2) : ℝ :=
  iteratedDeriv i (fun ρ => tr.v ρ x l) r

/-- `∂_r^i ∂_l E(r, x)`, the `i`-th age derivative of the gradient of the train vorticity. -/
def eJet {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) (r : ℝ) (l : Fin 2)
    (x : ℝ × ℝ) : ℝ :=
  iteratedDeriv i (fun ρ => B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) x) r

/-- **The operator family** `L^{(i)}(r)` (SP 3060: `-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)`, so
`∂_rφ = L^{(0)}(r)φ`; `L^{(i)}` has the `i`-th age derivatives of the coefficients):
`L^{(i)}(r)D = -([i = 0]ν(D [0,0] + D [1,1]) + Σ_l ∂_r^i v_l(r) D [l] - K_c^T(∂_r^i∇E(r) D []))`
acting on derivative fields `D` (`D [] = f`, `D [l] = ∂_l f`, `D [l, l] = ∂_l² f`), with the
kernel adjoint `kerAdj c` of the localized source (SP 3052-3058). -/
def adjLop {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) (r : ℝ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  -((if i = 0 then (ν : ℂ) * (D [0, 0] x + D [1, 1] x) else 0) +
      ∑ l : Fin 2, ((vJet tr i r x l : ℝ) : ℂ) * D [l] x -
      kerAdj c (fun l y => ((eJet tr i r l y : ℝ) : ℂ) * D [] y) x)

/-! ## Coefficients and Leibniz fields -/

/-- The word `∂^w a` of spatial derivatives of a real coefficient (`B0579.pd`;
`rSpatial (j :: w) a = ∂_j (rSpatial w a)`, the word convention of `IsCellJet`). -/
def rSpatial : List (Fin 2) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], a => a
  | j :: w, a => B0579.pd j (rSpatial w a)

/-- The splittings of a word, `∂^w (a b) = Σ_{(α, β)} ∂^α a ∂^β b`: the new letter goes to either
factor. -/
def wordSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2))
  | [] => [([], [])]
  | j :: w => (wordSplits w).flatMap fun p => [(j :: p.1, p.2), (p.1, j :: p.2)]

/-- **The Leibniz fields** of `A f` from the fields `D` of `f`:
`leib A D w = Σ_{(α, β) ∈ wordSplits w} ∂^α A · D β`. -/
def leib (A : ℝ × ℝ → ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (w : List (Fin 2)) (x : ℝ × ℝ) : ℂ :=
  ((wordSplits w).map fun p => ((rSpatial p.1 A x : ℝ) : ℂ) * D p.2 x).sum

/-- **A smooth coefficient family on `I`** (the transport coefficients `∂_r^i v`, SP 270-288): for
`r ∈ I`, `a r` is smooth and `c`-periodic, every spatial derivative is bounded, and continuous in
`r` uniformly in `x`. -/
def IsSmoothCoeff (c : ℝ) (I : Set ℝ) (a : ℝ → ℝ × ℝ → ℝ) : Prop :=
  (∀ r ∈ I, ContDiff ℝ ∞ (a r) ∧ ∀ x : ℝ × ℝ, a r (x.1 + c, x.2) = a r x) ∧
    ∀ w : List (Fin 2), ∀ r ∈ I, (∃ C : ℝ, ∀ x : ℝ × ℝ, |rSpatial w (a r) x| ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ r' in 𝓝[I] r, ∀ x : ℝ × ℝ,
        |rSpatial w (a r') x - rSpatial w (a r) x| ≤ ε

/-- `(1 + x₂²)^{(m+1)/2}`, the weight of the vorticity jets in `TrainSTJets`. -/
def ejWeight (m : ℝ) (x : ℝ × ℝ) : ℝ := (1 + x.2 ^ 2) ^ ((m + 1) / 2)

/-- **A weighted coefficient family on `I`** (the vorticity-gradient jets `∂_r^i∇E`, SP 2866-2870:
every fixed weighted derivative norm): smooth and `c`-periodic, every spatial derivative bounded
with the weight `ejWeight m`, and continuous in `r` in that weighted sup norm. -/
def IsWeightedCoeff (c m : ℝ) (I : Set ℝ) (G : ℝ → Fin 2 → ℝ × ℝ → ℝ) : Prop :=
  (∀ r ∈ I, ∀ l : Fin 2, ContDiff ℝ ∞ (G r l) ∧ ∀ x : ℝ × ℝ, G r l (x.1 + c, x.2) = G r l x) ∧
    ∀ (w : List (Fin 2)) (l : Fin 2), ∀ r ∈ I,
      (∃ C : ℝ, ∀ x : ℝ × ℝ, ejWeight m x * |rSpatial w (G r l) x| ≤ C) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ r' in 𝓝[I] r, ∀ x : ℝ × ℝ,
          ejWeight m x * |rSpatial w (G r' l) x - rSpatial w (G r l) x| ≤ ε

/-- **`a' = ∂_r a` uniformly with the weight `wt`**: `wt |(a(r') - a(r))/(r' - r) - a'(r)| → 0`
uniformly in `x` (`wt = 1` for the velocity, `wt = ejWeight m` for the vorticity jets). -/
def HasCoeffDeriv (I : Set ℝ) (wt : ℝ × ℝ → ℝ) (a a' : ℝ → ℝ × ℝ → ℝ) : Prop :=
  ∀ r ∈ I, ∀ ε : ℝ, 0 < ε → ∀ᶠ r' in 𝓝[I \ {r}] r, ∀ x : ℝ × ℝ,
    wt x * |(r' - r)⁻¹ * (a r' x - a r x) - a' r x| ≤ ε

/-! ## Generic leaves: jets, `X`-derivatives -/

/-- **(1) One family of fields for all orders**: `f ∈ C(I; H^k_{-m,c})` for every `k` has one
family `D` of derivative fields for all orders (take the fields of word `w` from `AdjHkOn |w|`;
fields of different orders agree a.e. on the cell by induction on the word with the uniqueness
of weak derivatives `WeakCellAeUnique` (`Sub/PartIII-a_T21_2_7_2_1_2_1_3_3.lean`, accepted), and
`HasWeakCellDerivC` only sees a.e. classes). -/
def AdjHkAllOf : Prop :=
  ∀ (c m : ℝ) (I : Set ℝ) (f : ℝ → ℝ × ℝ → ℂ), 0 < c →
    (∀ k : ℕ, AdjHkOn c m k I f) → ∃ D, AdjHkAll c m I f D

/-- **(2) A continuous tested derivative is the `X_{-m,c}`-derivative** (Pettis; SP 3060): if
`f' ∈ C((a, b); X_{-m,c})` and `d/dr ∫ f(r)ψ = ∫ f'(r)ψ` for every cylinder test `ψ`, then
`f(r') - f(r) = ∫_r^{r'} f'` in `X_{-m,c}` (FTC for the tested functions, the test pairing is a
continuous functional `AdjPairing`, and the tests separate `X_{-m,c}`, `LocCylUniq`), so the
difference quotients converge to `f'(r)` in `X_{-m,c}`. -/
def XDerivOfTested : Prop :=
  ∀ (c m a b : ℝ) (f f' : ℝ → ℝ × ℝ → ℂ), 0 < c →
    (∀ r ∈ Ioo a b, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ioo a b, MemLp (f' r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ioo a b, Tendsto (fun r' => xNorm c (-m) (f' r' - f' r)) (𝓝[Ioo a b] r) (𝓝 0)) →
    (∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∀ r ∈ Ioo a b,
      HasDerivAt (fun r' => ∫ x in B0579.cell c, f r' x * (ψ x : ℂ))
        (∫ x in B0579.cell c, f' r x * (ψ x : ℂ)) r) →
    HasXDerivOn c m (Ioo a b) f f'

/-- **(3) An `X_{-m,c}`-derivative is a tested derivative**: `|∫ hψ| ≤ ‖h‖_{X_{-m,c}} ‖ψ‖_{X_{m,c}}`
for a cylinder test `ψ` (weighted Cauchy-Schwarz, `WeightedCS`), applied to the difference
quotient minus `f'(r)`. -/
def TestedOfXDeriv : Prop :=
  ∀ (c m a b : ℝ) (f f' : ℝ → ℝ × ℝ → ℂ), 0 < c →
    (∀ r ∈ Ioo a b, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ioo a b, MemLp (f' r) 2 (B0579.cellMeasure c (-m))) →
    HasXDerivOn c m (Ioo a b) f f' →
    ∀ χ : ℝ × ℝ → ℝ, B0579.IsCylTest c χ → ∀ r ∈ Ioo a b,
      HasDerivAt (fun r' => ∫ x in B0579.cell c, f r' x * (χ x : ℂ))
        (∫ x in B0579.cell c, f' r x * (χ x : ℂ)) r

/-- **The upgrade**: an `X_{-m,c}`-derivative between two `C(I; H^∞_{-m,c})` families is the
`X_{-m,c}`-derivative of every derivative field (proved from `XDerivOfTested` and
`TestedOfXDeriv` by induction on the word, `xDerivUpgrade_of`). -/
def XDerivUpgrade : Prop :=
  ∀ (c m a b : ℝ) (f f' : ℝ → ℝ × ℝ → ℂ) (D D' : ℝ → List (Fin 2) → ℝ × ℝ → ℂ), 0 < c →
    AdjHkAll c m (Ioo a b) f D → AdjHkAll c m (Ioo a b) f' D' →
    HasXDerivOn c m (Ioo a b) f f' →
    ∀ w : List (Fin 2), HasXDerivOn c m (Ioo a b) (fun r => D r w) (fun r => D' r w)

/-- **(4) Linear combinations of `C(I; H^∞_{-m,c})` families** (with the combined fields), and the
zero family. -/
def AdjHkAllLinear : Prop :=
  ∀ (c m : ℝ) (I : Set ℝ),
    AdjHkAll c m I (fun _ _ => 0) (fun _ _ _ => 0) ∧
      ∀ (f g : ℝ → ℝ × ℝ → ℂ) (D E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (α β : ℂ),
        AdjHkAll c m I f D → AdjHkAll c m I g E →
        AdjHkAll c m I (fun r x => α * f r x + β * g r x)
          (fun r w x => α * D r w x + β * E r w x)

/-- **(5) Linear combinations of `X_{-m,c}`-derivatives** (all slices in `X_{-m,c}`, so the
triangle inequality applies), and the zero family. -/
def HasXDerivOnLinear : Prop :=
  ∀ (c m : ℝ) (I : Set ℝ),
    HasXDerivOn c m I (fun _ _ => 0) (fun _ _ => 0) ∧
      ∀ (f f' g g' : ℝ → ℝ × ℝ → ℂ) (α β : ℂ),
        (∀ r ∈ I, MemLp (f r) 2 (B0579.cellMeasure c (-m)) ∧
          MemLp (f' r) 2 (B0579.cellMeasure c (-m)) ∧
          MemLp (g r) 2 (B0579.cellMeasure c (-m)) ∧
          MemLp (g' r) 2 (B0579.cellMeasure c (-m))) →
        HasXDerivOn c m I f f' → HasXDerivOn c m I g g' →
        HasXDerivOn c m I (fun r x => α * f r x + β * g r x)
          (fun r x => α * f' r x + β * g' r x)

/-! ## The first age derivative -/

/-- **(6) The kernel velocity of a test is its kernel Biot-Savart velocity** (SP 3052-3057:
`kerVelFarField_of kerNearFar`, `kerVelDivFree_of`, `kerVelCurl_of`, all accepted). -/
def KerVelIsBS : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ (kerVel d ψ)

/-- **(7) The classical equation, tested** (SP 3060: integration by parts on the cylinder): for a
cell jet `D` of order `2` of `f` and a cylinder test `ψ`,
`∫ (L^{(0)}(r)D) ψ = -∫ f (νΔψ - v(r)·∇ψ - (K_cψ)·∇E(r))`.  Here
`∫ (D [0,0] + D [1,1])ψ = ∫ fΔψ` (twice `HasWeakCellDerivC`), `∫ Σ_l v_l D [l] ψ = -∫ f v·∇ψ`
(`HasWeakCellDerivC` against the cylinder test `v_l(r)ψ`, `div v = 0`), and
`∫ K_c^T(∇E f)ψ = ∫ f (K_cψ)·∇E` (`KerAdjFubini`; `∇E(r) f ∈ L¹` by `LadTrainBdd` and weighted
Cauchy-Schwarz). -/
def AdjLopTested (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ r : ℝ, 0 < r → ∀ (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      IsCellJet (ν ^ (-2 : ℝ)) m 2 f D →
      ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjLop tr 0 r D x * (ψ x : ℂ) =
          -∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr f r ψ (kerVel (ν ^ (-2 : ℝ)) ψ) x

/-- **The first age derivative** (SP 3060): for a weak adjoint with the differentiated weak
equation and fields `D` of all orders on `(t, s)`, `∂_rφ = L^{(0)}(r)φ` in `X_{-m,c}` (proved from
`XDerivOfTested`, `KerVelIsBS`, `AdjLopTested`, `AdjLopSmooth`, `adjTimeDerivBase_of`). -/
def AdjTimeDerivBase (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      ∀ D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ, AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo t s) φ D →
        HasXDerivOn (ν ^ (-2 : ℝ)) m (Ioo t s) φ (fun r => adjLop tr 0 r (D r))

/-! ## The operators on `C(I; H^∞_{-m,c})` -/

/-- **The operators preserve `C(I; H^∞_{-m,c})`** (SP 3060, 3052-3058, 2866-2870; proved from the
coefficient and kernel leaves, `adjLopSmooth_of`). -/
def AdjLopSmooth (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ a b : ℝ, 0 ≤ a → ∀ (i : ℕ) (f : ℝ → ℝ × ℝ → ℂ) (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ),
      AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) f D →
      ∃ D', AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) (fun r => adjLop tr i r (D r)) D'

/-- **The product rule** `∂_r(L^{(i)}Ψ) = L^{(i+1)}Ψ + L^{(i)}∂_rΨ` (SP 3060; proved from the
coefficient and kernel leaves, `adjLopDeriv_of`). -/
def AdjLopDeriv (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ a b : ℝ, 0 ≤ a → ∀ (i : ℕ) (f f' : ℝ → ℝ × ℝ → ℂ)
      (D D' : ℝ → List (Fin 2) → ℝ × ℝ → ℂ),
      AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) f D → AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) f' D' →
      (∀ w : List (Fin 2),
        HasXDerivOn (ν ^ (-2 : ℝ)) m (Ioo a b) (fun r => D r w) (fun r => D' r w)) →
      HasXDerivOn (ν ^ (-2 : ℝ)) m (Ioo a b) (fun r => adjLop tr i r (D r))
        (fun r x => adjLop tr (i + 1) r (D r) x + adjLop tr i r (D' r) x)

/-! ## Leaves of the operator statements: coefficients -/

/-- **(8) The product rule against a smooth periodic coefficient**: for `A` smooth, `c`-periodic,
with `A` and `∂_jA` bounded, and `g' = ∂_j g` weakly with `g, g' ∈ X_{-m,c}`, the product `A g` has
weak derivative `∂_jA g + A g'` (test `Aψ`, a cylinder test, and `∂_j(Aψ) = ∂_jA ψ + A ∂_jψ`). -/
def CoeffWeakDeriv : Prop :=
  ∀ (c m : ℝ) (j : Fin 2) (A : ℝ × ℝ → ℝ) (g g' : ℝ × ℝ → ℂ), 0 < c →
    ContDiff ℝ ∞ A → (∀ x : ℝ × ℝ, A (x.1 + c, x.2) = A x) →
    (∃ C : ℝ, ∀ x : ℝ × ℝ, |A x| ≤ C) → (∃ C : ℝ, ∀ x : ℝ × ℝ, |B0579.pd j A x| ≤ C) →
    MemLp g 2 (B0579.cellMeasure c (-m)) → MemLp g' 2 (B0579.cellMeasure c (-m)) →
    HasWeakCellDerivC c j g g' →
    HasWeakCellDerivC c j (fun x => (A x : ℂ) * g x)
      (fun x => (B0579.pd j A x : ℂ) * g x + (A x : ℂ) * g' x)

/-- **(9) Leibniz fields**: a smooth `c`-periodic coefficient with every derivative bounded, times
a cell jet of every order, is a cell jet of every order with the fields `leib A D` (induction on
the word with `CoeffWeakDeriv`; `rSpatial α A` is smooth, periodic and bounded with its
derivatives). -/
def LeibCellJet : Prop :=
  ∀ (c m : ℝ) (A : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ), 0 < c →
    ContDiff ℝ ∞ A → (∀ x : ℝ × ℝ, A (x.1 + c, x.2) = A x) →
    (∀ w : List (Fin 2), ∃ C : ℝ, ∀ x : ℝ × ℝ, |rSpatial w A x| ≤ C) →
    (∀ k : ℕ, IsCellJet c m k f D) →
    ∀ k : ℕ, IsCellJet c m k (fun x => (A x : ℂ) * f x) (leib A D)

/-- **(10) Products with a smooth coefficient family preserve `C(I; H^∞_{-m,c})`** (pointwise
`LeibCellJet`; continuity in `r` from the uniform continuity of the coefficient derivatives and
of the fields in `X_{-m,c}`). -/
def AdjHkAllCoeffMul : Prop :=
  ∀ (c m : ℝ) (I : Set ℝ) (a : ℝ → ℝ × ℝ → ℝ) (f : ℝ → ℝ × ℝ → ℂ)
    (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ), 0 < c →
    IsSmoothCoeff c I a → AdjHkAll c m I f D →
    AdjHkAll c m I (fun r x => (a r x : ℂ) * f r x) (fun r => leib (a r) (D r))

/-- **(11) Age derivative of a product with a smooth coefficient**:
`∂_r(A f) = (∂_rA) f + A ∂_r f` in `X_{-m,c}`, for `A` with uniform difference quotients. -/
def CoeffMulDeriv : Prop :=
  ∀ (c m a b : ℝ) (A A' : ℝ → ℝ × ℝ → ℝ) (f f' : ℝ → ℝ × ℝ → ℂ), 0 < c →
    IsSmoothCoeff c (Ioo a b) A → IsSmoothCoeff c (Ioo a b) A' →
    HasCoeffDeriv (Ioo a b) (fun _ => 1) A A' →
    (∀ r ∈ Ioo a b, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ioo a b, MemLp (f' r) 2 (B0579.cellMeasure c (-m))) →
    HasXDerivOn c m (Ioo a b) f f' →
    HasXDerivOn c m (Ioo a b) (fun r x => (A r x : ℂ) * f r x)
      (fun r x => (A' r x : ℂ) * f r x + (A r x : ℂ) * f' r x)

/-! ## Leaves of the operator statements: the kernel adjoint -/

/-- **(12) The kernel adjoint is bounded from `L¹ ∩ L²` into `X_{-m,c}`** (SP 3054-3056, `m > 1`:
`KerAdjSplit` and `XNormSplitLe`, uniformly in the cell length `d ≥ 1`; measurability from the
split). -/
def KerAdjXBound (m : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 1 ≤ d → ∀ F : Fin 2 → ℝ × ℝ → ℂ,
    (∀ l, IntegrableOn (F l) (B0579.cell d) ∧ MemLp (F l) 2 (volume.restrict (B0579.cell d))) →
    MemLp (kerAdj d F) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (kerAdj d F) ≤ ENNReal.ofReal C * ∑ l : Fin 2,
        (eLpNorm (F l) 1 (volume.restrict (B0579.cell d)) +
          eLpNorm (F l) 2 (volume.restrict (B0579.cell d)))

/-- **(13) The kernel adjoint is linear almost everywhere** (both sides are elements of
`X_{-2,d}` by `KerAdjXBound 2` with the same test pairings `∫ F·K_dψ`, `KerAdjFubini`; the tests
separate, `LocCylUniq`). -/
def KerAdjSubAE : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ F F' : Fin 2 → ℝ × ℝ → ℂ,
    (∀ l, IntegrableOn (F l) (B0579.cell d) ∧ MemLp (F l) 2 (volume.restrict (B0579.cell d))) →
    (∀ l, IntegrableOn (F' l) (B0579.cell d) ∧ MemLp (F' l) 2 (volume.restrict (B0579.cell d))) →
    ∀ α β : ℂ, (fun y => α * kerAdj d F y + β * kerAdj d F' y) =ᵐ[volume.restrict (B0579.cell d)]
      kerAdj d (fun l y => α * F l y + β * F' l y)

/-- **(14) The kernel velocity is a convolution on the cylinder** (`Cyl.integral_cell_mul_comp_sub`,
with `B0579.cell d = Cyl.cell d`, `cell_eq` of `Sub/T21_2_1/Kernel/AdjFubini.lean`; `ψ` and `K_d`
are `d`-periodic, `KerNearFar`): `K_dψ(x) = ∫_{C_d} K_d(z) ψ(x - z) dz`. -/
def KerVelConv : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ (x : ℝ × ℝ) (l : Fin 2),
    kerVel d ψ x l = ∫ z in B0579.cell d, kerD d z l * ψ (x - z)

/-- **(15) Integration by parts against the kernel velocity** (SP 3052-3058, translation invariance
of the periodic kernel): if `G = ∂_j F` weakly with `F, G ∈ L¹(C_d)`, then
`∫ F (K_d∂_jψ)_l = -∫ G (K_dψ)_l` for every cylinder test `ψ` (`KerVelConv` for both kernel
velocities; Fubini on `C_d × C_d`, absolutely convergent since `ψ` is bounded with bounded
`η`-support and `K_d` is integrable near `0` and bounded off it, `KerNearFar`; the translated test
`ψ(· - z)` is a cylinder test with `∂_j(ψ(· - z)) = (∂_jψ)(· - z)`, so
`∫ F (∂_jψ)(· - z) = -∫ G ψ(· - z)`). -/
def KerVelPairDeriv : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ (j : Fin 2) (F G : ℝ × ℝ → ℂ), IntegrableOn F (B0579.cell d) →
    IntegrableOn G (B0579.cell d) → HasWeakCellDerivC d j F G →
    ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ l : Fin 2,
      ∫ x in B0579.cell d, F x * ((kerVel d (B0579.pd j ψ) x l : ℝ) : ℂ) =
        -∫ x in B0579.cell d, G x * ((kerVel d ψ x l : ℝ) : ℂ)

/-- **(16) Derivatives commute with the kernel adjoint** (SP 3052-3058, translation invariance of
the periodic kernel): if `G = ∂_j F` weakly with `F, G ∈ L¹(C_d)`, then `K_d^T G = ∂_j K_d^T F`
weakly.  (`∫ K_d^T F ∂_jψ = ∫ F·K_d∂_jψ` by `KerAdjFubini`; `K_d∂_jψ(x) = ∫ K_d(z) ∂_jψ(x - z)dz`,
`Cyl.integral_cell_mul_comp_sub`; Fubini and `∫ F ∂_jψ(· - z) = -∫ G ψ(· - z)`, the translated
test being a cylinder test.) -/
def KerAdjWeakDeriv : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ (j : Fin 2) (F G : Fin 2 → ℝ × ℝ → ℂ),
    (∀ l, IntegrableOn (F l) (B0579.cell d) ∧ IntegrableOn (G l) (B0579.cell d) ∧
      HasWeakCellDerivC d j (F l) (G l)) →
    HasWeakCellDerivC d j (kerAdj d F) (kerAdj d G)

/-- **(17) The kernel adjoint is `d`-periodic** (`KerNearFar`: `K_d` is `d`-periodic). -/
def KerAdjPeriodic : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ (F : Fin 2 → ℝ × ℝ → ℂ) (y : ℝ × ℝ),
    kerAdj d F (y.1 + d, y.2) = kerAdj d F y

/-- **(18) Weighted Cauchy-Schwarz for the localized source** (SP 3053-3054): if
`(1 + x₂²)^{(m+1)/2}|A| ≤ B` on the cell and `f ∈ X_{-m,c}`, then `A f ∈ L¹ ∩ L²(C_c)` with
`‖A f‖₁ + ‖A f‖₂ ≤ K B ‖f‖_{X_{-m,c}}` (on the cell `⟨x⟩^{2m} ≤ C_{c,m}(1 + x₂²)^m` for `m ≥ 0`,
`≤ (1 + x₂²)^m` for `m < 0`, and `(1 + x₂²)^{-1}` is integrable on the cell). -/
def WeightedMulL12 : Prop :=
  ∀ c m : ℝ, 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) (B : ℝ),
    AEStronglyMeasurable A (volume.restrict (B0579.cell c)) →
    MemLp f 2 (B0579.cellMeasure c (-m)) →
    (∀ x ∈ B0579.cell c, ejWeight m x * |A x| ≤ B) →
    IntegrableOn (fun x => (A x : ℂ) * f x) (B0579.cell c) ∧
      MemLp (fun x => (A x : ℂ) * f x) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => (A x : ℂ) * f x) 1 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => (A x : ℂ) * f x) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (K * B) * xNorm c (-m) f

/-- **(19) The kernel term preserves `C(I; H^∞_{-m,c})`** (SP 3052-3058, `m > 1`): the fields of
`K_c^T(G f)` are `K_c^T` of the Leibniz fields of `G f` (`LeibCellJet`, `KerAdjWeakDeriv`), in
`X_{-m,c}` by `WeightedMulL12` and `KerAdjXBound`, periodic by `KerAdjPeriodic`, continuous in `r`
by `KerAdjSubAE`, `KerAdjXBound` and `WeightedMulL12`. -/
def AdjHkAllKerMul (m : ℝ) : Prop :=
  ∀ (c : ℝ) (I : Set ℝ) (G : ℝ → Fin 2 → ℝ × ℝ → ℝ) (f : ℝ → ℝ × ℝ → ℂ)
    (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ), 1 ≤ c →
    IsWeightedCoeff c m I G → AdjHkAll c m I f D →
    AdjHkAll c m I (fun r => kerAdj c (fun l y => (G r l y : ℂ) * f r y))
      (fun r w => kerAdj c (fun l => leib (G r l) (D r) w))

/-- **(20) Age derivative of the kernel term** (SP 3052-3058, `m > 1`):
`∂_r K_c^T(G f) = K_c^T(∂_rG f) + K_c^T(G ∂_r f)` in `X_{-m,c}` (`KerAdjSubAE`: the difference
quotient minus the candidate is `K_c^T` of
`(DQ f - f') G(r') + f'(G(r') - G(r)) + f(DQ G - G')`, small in `L¹ ∩ L²` by `WeightedMulL12`;
then `KerAdjXBound`). -/
def KerMulDeriv (m : ℝ) : Prop :=
  ∀ (c a b : ℝ) (G G' : ℝ → Fin 2 → ℝ × ℝ → ℝ) (f f' : ℝ → ℝ × ℝ → ℂ), 1 ≤ c →
    IsWeightedCoeff c m (Ioo a b) G → IsWeightedCoeff c m (Ioo a b) G' →
    (∀ l : Fin 2, HasCoeffDeriv (Ioo a b) (ejWeight m) (fun r => G r l) (fun r => G' r l)) →
    (∀ r ∈ Ioo a b, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ioo a b, MemLp (f' r) 2 (B0579.cellMeasure c (-m))) →
    HasXDerivOn c m (Ioo a b) f f' →
    HasXDerivOn c m (Ioo a b) (fun r => kerAdj c (fun l y => (G r l y : ℂ) * f r y))
      (fun r x => kerAdj c (fun l y => (G' r l y : ℂ) * f r y) x +
        kerAdj c (fun l y => (G r l y : ℂ) * f' r y) x)

/-! ## Leaves of the operator statements: the train -/

/-- **(21) Age jets of a jointly smooth function with bounded weighted derivatives** (calculus): if
`V` is `C^∞` on `(0, ∞) × ℝ²` and `wt · ‖D^n V‖` is bounded on `(0, S) × ℝ²` for every `n` and `S`
(`wt > 0`), then for every `i` the age jet `A r x = ∂_r^i V(r, x)` is smooth in `x` for `r > 0`,
every spatial derivative `∂^w A r` is bounded with the weight `wt` and continuous in `r` in the
weighted sup norm, and `∂_r^{i+1} V` is the weighted-uniform age derivative of `A`
(`∂_x^w ∂_r^i V(r, x)` is `D^{i+|w|}V(r, x)` applied to unit vectors; mean value and Taylor in
`r`). -/
def SliceJetBounds : Prop :=
  ∀ (V : ℝ × (ℝ × ℝ) → ℝ) (wt : ℝ × ℝ → ℝ), (∀ x : ℝ × ℝ, 0 < wt x) →
    ContDiffOn ℝ ∞ V (Ioi 0 ×ˢ univ) →
    (∀ (n : ℕ) (S : ℝ), ∃ C : ℝ, ∀ ρ ∈ Ioo (0 : ℝ) S, ∀ x : ℝ × ℝ,
      wt x * ‖iteratedFDeriv ℝ n V (ρ, x)‖ ≤ C) →
    ∀ (a b : ℝ), 0 ≤ a → ∀ i : ℕ,
      (∀ r ∈ Ioo a b, ContDiff ℝ ∞ (fun x => iteratedDeriv i (fun ρ => V (ρ, x)) r)) ∧
      (∀ (w : List (Fin 2)), ∀ r ∈ Ioo a b,
        (∃ C : ℝ, ∀ x : ℝ × ℝ,
          wt x * |rSpatial w (fun y => iteratedDeriv i (fun ρ => V (ρ, y)) r) x| ≤ C) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ r' in 𝓝[Ioo a b] r, ∀ x : ℝ × ℝ,
          wt x * |rSpatial w (fun y => iteratedDeriv i (fun ρ => V (ρ, y)) r') x -
            rSpatial w (fun y => iteratedDeriv i (fun ρ => V (ρ, y)) r) x| ≤ ε) ∧
      HasCoeffDeriv (Ioo a b) wt (fun r x => iteratedDeriv i (fun ρ => V (ρ, x)) r)
        (fun r x => iteratedDeriv (i + 1) (fun ρ => V (ρ, x)) r)

/-- **(22) The velocity jets are smooth coefficients** (SP 270-288; `TrainSTJets`: every joint
derivative of `v` is bounded on `[0, S] × ℝ²`; for `r > 0` the derivatives within `[0, ∞) × ℝ²`
are the derivatives; `∂_x^w ∂_r^i v_l` is a component of `D^{i+|w|}v` applied to unit vectors,
periodic by `periodic_v`; mean value and Taylor in `r`). -/
def TrainVCoeff (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) → ∀ a b : ℝ, 0 ≤ a → ∀ (i : ℕ) (l : Fin 2),
      IsSmoothCoeff (ν ^ (-2 : ℝ)) (Ioo a b) (fun r x => vJet tr i r x l) ∧
        HasCoeffDeriv (Ioo a b) (fun _ => 1) (fun r x => vJet tr i r x l)
          (fun r x => vJet tr (i + 1) r x l)

/-- **(23) The vorticity-gradient jets are weighted coefficients** (SP 2866-2870; `TrainSTJets`:
every joint derivative of positive order of `E` is bounded with the weight
`(1 + x₂²)^{(m+1)/2}`; `∂_x^w ∂_r^i ∂_l E` has order `i + |w| + 1 ≥ 1`). -/
def TrainECoeff (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) → ∀ a b : ℝ, 0 ≤ a → ∀ i : ℕ,
      IsWeightedCoeff (ν ^ (-2 : ℝ)) m (Ioo a b) (fun r l x => eJet tr i r l x) ∧
        ∀ l : Fin 2, HasCoeffDeriv (Ioo a b) (ejWeight m) (fun r x => eJet tr i r l x)
          (fun r x => eJet tr (i + 1) r l x)

end UnforcedLeray.Short.IIIa
