import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Lib.Train.VortexBounds
import UnforcedLeray.Lib.Train.Params
import UnforcedLeray.Units.B0140

/-!
# Part I, task `PartI:T08`: the differentiated energy inequality (statement and decomposition)

Source of record: `the November 2 reference manuscript`, lines 341-359 (proof of
Lemma `sct:train`):

> Write `e = v - V_c^p`, use slow time `σ = νs`, and choose an integer `N ≥ 3` ... For
> `0 < δ ≤ (4N)^{-1}` set `E_N² = ∑_{j=0}^N (δa)^j ‖D^j e‖₂²`. On the bootstrap interval
> `‖∇e‖_∞ ≤ a^{-2}`, differentiated energy and one integration by parts on the stress give
> `(E_N²)' + ∑_{j=0}^N (δa)^j ‖∇D^j e‖₂² ≤ C_N/(νa²) E_N² + C_N ν^{-2} a^{-5} e^{-b_N c²/a}`.
> Here differentiated transport is controlled by `‖[D^j, e·∇]e‖₂ ≤ C_j ‖∇e‖_∞ ‖D^j e‖₂`. Its
> constants are independent of the period ... The differentiated weights are absorbed by the
> preceding derivative's dissipation.

together with lines 326-339 (the residual `div Q`, `Q = ∑_{i≠j} V_i ⊗ V_j`, and the bounds
`‖D^jV_c^p‖_∞ ≤ C_j a^{-(3+j)/2}`, `‖D^jQ‖₂ ≤ C_j a^{-(5+j)/2} e^{-b_j c²/a}`) and lines 261-288
(the train: datum in `BUC ∩ H^k` for every `k`, the finite-energy mild solution).

## Conventions

* `a = Train.width ν s = 1 + νs` (line 253); `e = trainErr tr s = v(s) - V_c^p(s)`
  (`V_c^p = Train.Vc`, line 294); the pressure error `π = p - p_c` (`errPressure`).
* **Norms of jets.** `‖D^j f‖₂²` is the Euclidean (Hilbert-Schmidt) norm of the tensor of all
  `j`-th partials, `jetEnergy c j f = ∫_cell ∑_{|w|=j} ∑_k (∂_w f_k)²`, the sum over the `2^j`
  ordered coordinate words `w` (`wordsOfLength`, `B0151.derivWord`; `true` is `∂_q`, `false` is
  `∂_η`). The energy method needs this Hilbert norm: its square is differentiable in time and
  `∑_k ‖∂_k D^j f‖₂² = ‖D^{j+1} f‖₂²` exactly, so `‖∇D^j e‖₂² = jetEnergy c (j+1) e`. It is
  equivalent to `Train.cellL2 c (Train.jet j f)²` (operator norm of the Fréchet jet) up to a
  constant depending only on `j` (`CylJetWord`, `Sub/T07.lean`), whose square is a maximum of
  quadratic forms and is not differentiable in time in general.
* **Slow time.** The source's `(E_N²)'` is the derivative in `σ = νs`. The statement records the
  derivative `D` in the age `s` (`HasDerivAt` of the real function `s ↦ E_N²(s)`) and uses
  `ν⁻¹ D = dE_N²/dσ`.
* Cell integrals are real Bochner integrals over the centred cell `Cyl.cell c`; the conclusion
  asserts that every word derivative of `e` is in `L²(cell)`, so no integral is a junk value.
* The bootstrap hypothesis `‖∇e(s)‖_∞ ≤ a^{-2}` is imposed on each first partial of each
  component (`|∂_β e_k| ≤ a^{-2}`); this is implied by the source's hypothesis for any norm on
  `∇e` that dominates the entries, so the statement is (up to constants) the source's.
* Constants `C, b` depend only on `N`: not on `ν ∈ (0,1]`, `c ≥ 1`, `δ ∈ (0, 1/(4N)]`, the
  train or the age.

## Decomposition (all leaves are `Prop`s below; `differentiated_energy_inequality_of` assembles)

1. `TrainErrBasic`: smoothness, periodicity, zero divergence, bounded word derivatives of `e`;
   smoothness of `V_c^p` and of the entries of `Q_c` (periodic).
2. `TrainErrJetL2`: every word derivative of `e(s)` is in `L²(cell)` (lines 261-288, 344).
3. `TrainPressureRegular`: `π(s)` is smooth, periodic, bounded and `∇π(s) ∈ H^∞(cell)`.
4. `TrainJetEnergyBalance` (cell energy derivative): `d/ds ‖D^j e‖₂² = 2(ν⟨D^j e, D^jΔe⟩ -
   ⟨D^j e, D^j A⟩ - ⟨D^j e, D^j∇π⟩ - ⟨D^j e, D^j div Q⟩)`, `A = v·∇v - V_c·∇V_c` (from the error
   equation `PartI:T06`).
5. `JetViscousIBP` (jet viscous IBP): `⟨D^j f, D^jΔf⟩ = -‖D^{j+1} f‖₂²`.
6. `JetPressureOrth` (pressure orthogonality): `⟨D^j f, D^j∇P⟩ = 0` for `div f = 0`.
7. `JetTransportBound` (commutator bound via `PartI:T07`): the transport pairing with
   `(V+f)·∇(V+f) - V·∇V` is bounded by `A_j (‖∇f‖_∞ ‖D^j f‖² + ∑_{i=1}^{j+1} ‖D^iV‖_∞
   ‖D^{j+1-i} f‖ ‖D^j f‖)`.
8. `TransportWeightSum` (real analysis): the weights `(δa)^j` turn 7 with
   `‖D^iV_c‖_∞ ≤ C_i a^{-(3+i)/2}` (`Train.Vc_bounds`) into `C a^{-2} E_N²`.
9. `JetForcingIBP` (one integration by parts on the stress and Cauchy-Schwarz):
   `|⟨D^j f, D^j div Q⟩| ≤ ‖D^{j+1} f‖₂ ‖D^j Q‖₂`.
10. `VcStressJetBound` (forcing jet bound via `Train.Vc_bounds`):
   `‖D^jQ_c‖₂² ≤ B a^{-(5+j)} e^{-b c²/a}` on the centred cell.
11. `EnergyClosure` (real analysis): product rule for the weights, absorption of the weight
   derivative (`Nδ ≤ 1/4`) and of the forcing (AM-GM) into the dissipation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-! ### Vocabulary -/

/-- The word derivative `∂_w f_k` of the `k`-th component of a meridional field (`true` is `∂_q`,
`false` is `∂_η`, the head of the word is applied last). -/
def wordComp (w : List Bool) (f : Plane → Vec) (k : Fin 2) : Plane → ℝ :=
  B0151.derivWord w (fun x => f x k)

/-- The `j`-th jet pairing on one unnormalized centred cell,
`⟨D^j f, D^j g⟩ = ∫_cell ∑_{|w|=j} ∑_k ∂_w f_k ∂_w g_k`. -/
def jetPair (c : ℝ) (j : ℕ) (f g : Plane → Vec) : ℝ :=
  ∫ z in Cyl.cell c, ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w f k z * wordComp w g k z

/-- `‖D^j f‖₂²` on one cell, with the Euclidean norm of the tensor of `j`-th partials. -/
def jetEnergy (c : ℝ) (j : ℕ) (f : Plane → Vec) : ℝ := jetPair c j f f

/-- `‖D^j Q‖₂²` on one cell for a `2 × 2` tensor field. -/
def matEnergy (c : ℝ) (j : ℕ) (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∫ z in Cyl.cell c, ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ∑ l : Fin 2,
    B0151.derivWord w (fun x => Q x k l) z ^ 2

/-- `E_N² = ∑_{j=0}^N (δa)^j ‖D^j f‖₂²` (line 344). -/
def weightedEnergy (c δ a : ℝ) (N : ℕ) (f : Plane → Vec) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), (δ * a) ^ j * jetEnergy c j f

/-- The dissipation `∑_{j=0}^N (δa)^j ‖∇D^j f‖₂² = ∑_{j=0}^N (δa)^j ‖D^{j+1} f‖₂²` (line 348). -/
def weightedDissipation (c δ a : ℝ) (N : ℕ) (f : Plane → Vec) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), (δ * a) ^ j * jetEnergy c (j + 1) f

/-- A smooth `c`-periodic meridional field with every word derivative in `L²(cell)`. -/
def CellSmoothL2 (c : ℝ) (f : Plane → Vec) : Prop :=
  ContDiff ℝ ∞ f ∧ Cyl.IsPeriodic c f ∧
    ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w f k) 2 (Cyl.cellμ c)

/-- The comparison error `e = v - V_c^p` at age `s` (line 341). -/
def trainErr {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) : Plane → Vec :=
  fun z => tr.v s z - Vc ν c s z

/-- The pressure error `π = p - p_c^p` at age `s` (`p_c^p = Train.pc`, the summed isolated radial
pressures in the decaying gauge). -/
def errPressure {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) : Plane → ℝ :=
  fun z => tr.p s z - pc ν c s z

/-- The transport bracket `A = v·∇v - V_c·∇V_c = (V_c·∇)e + (e·∇)V_c + (e·∇)e` of the error
equation (`PartI:T06`, `train_error_equation`). -/
def advDiff {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) : Plane → Vec :=
  fun z => Train.advection (tr.v s) z - Train.advection (Vc ν c s) z

/-! ### The target -/

/-- **The differentiated energy inequality** (source lines 341-359). For `N ≥ 3` there are
`C_N, b_N > 0` such that for every viscosity `0 < ν ≤ 1`, period `c ≥ 1`, weight parameter
`0 < δ ≤ (4N)^{-1}`, train `tr` of the BUC class and age `s > 0` with `a = 1 + νs ≤ c²` at which
the bootstrap bound `|∂_β e_k| ≤ a^{-2}` holds (`e = v - V_c^p`):
all word derivatives of `e(s)` are in `L²(cell)`, `E_N²` is differentiable at `s` with derivative
`D` (in the age), and, with `(E_N²)' = ν⁻¹ D` the slow-time derivative (`σ = νs`),
`(E_N²)' + ∑_{j≤N} (δa)^j ‖∇D^j e‖₂² ≤ C_N/(νa²) E_N² + C_N ν^{-2} a^{-5} e^{-b_N c²/a}`. -/
def DifferentiatedEnergyInequality : Prop :=
  ∀ N : ℕ, 3 ≤ N → ∃ C b : ℝ, 0 < C ∧ 0 < b ∧
    ∀ ν c δ : ℝ, 0 < ν → ν ≤ 1 → 1 ≤ c → 0 < δ → δ ≤ 1 / (4 * N) →
    ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ s : ℝ, 0 < s → width ν s ≤ c ^ 2 →
      (∀ (β : Bool) (k : Fin 2) (z : Plane),
        |wordComp [β] (trainErr tr s) k z| ≤ (width ν s ^ 2)⁻¹) →
      (∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (trainErr tr s) k) 2 (Cyl.cellμ c)) ∧
      ∃ D : ℝ, HasDerivAt (fun r => weightedEnergy c δ (width ν r) N (trainErr tr r)) D s ∧
        ν⁻¹ * D + weightedDissipation c δ (width ν s) N (trainErr tr s) ≤
          C / (ν * width ν s ^ 2) * weightedEnergy c δ (width ν s) N (trainErr tr s) +
            C / (ν ^ 2 * width ν s ^ 5) * Real.exp (-(b * c ^ 2 / width ν s))

/-! ### Leaves: the train -/

/-- **Leaf 1: basic properties of the error** (lines 261-288, 294, 326-329). At every age
`s > 0` with `a(s) ≤ c²` of a train of the BUC class: `e(s)` is smooth, `c`-periodic and divergence free, and each
word derivative of each component is bounded (`IsBUCTrain` bounds the derivatives of `v` on
`[0, s]`; `Train.Vc_bounds` those of `V_c^p`); `V_c^p(s)` is smooth; the entries of
`Q_c(s) = ∑_{i≠j} V_i ⊗ V_j` are smooth and `c`-periodic. -/
def TrainErrBasic : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    ContDiff ℝ ∞ (trainErr tr s) ∧ Cyl.IsPeriodic c (trainErr tr s) ∧
    (∀ z : Plane, Cyl.divergence (trainErr tr s) z = 0) ∧
    (∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w (trainErr tr s) k z| ≤ M) ∧
    ContDiff ℝ ∞ (Vc ν c s) ∧
    (∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Qc ν c s z k l)) ∧
    (∀ k l : Fin 2, Cyl.IsPeriodic c (fun z => Qc ν c s z k l))

/-- **Leaf 2: the error has all derivatives in `L²(cell)`** (lines 261-288: the datum is in
`BUC ∩ H^k` for every `k` and the train is the finite-energy mild solution; line 344: `E_N` is
finite). At every age `s > 0` with `a(s) ≤ c²` of a train of the BUC class, every word derivative of every
component of `e(s) = v(s) - V_c^p(s)` is in `L²` of one cell. -/
def TrainErrJetL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (trainErr tr s) k) 2 (Cyl.cellμ c)

/-- **Leaf 3: regularity of the pressure error** (lines 266-270: the bounded periodic pressure
choice; with lines 326-329 for `p_c^p`). At every age `s > 0` with `a(s) ≤ c²`, `π(s) = p(s) - p_c^p(s)` is smooth,
`c`-periodic and bounded, and every word derivative of `∇π(s)` is in `L²(cell)`. -/
def TrainPressureRegular : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    ContDiff ℝ ∞ (errPressure tr s) ∧ Cyl.IsPeriodic c (errPressure tr s) ∧
    (∃ M : ℝ, ∀ z : Plane, |errPressure tr s z| ≤ M) ∧
    ∀ (w : List Bool) (k : Fin 2),
      MemLp (wordComp w (Train.gradS (errPressure tr s)) k) 2 (Cyl.cellμ c)

/-- **Leaf 4: the cell energy derivative ("differentiated energy", line 346)**. At every age
`s > 0` with `a(s) ≤ c²` and order `j`, `r ↦ ‖D^j e(r)‖₂²` is differentiable at `s` and, by the error equation
`∂_s e = νΔe - A - ∇π - div Q_c` (`PartI:T06`, lines 326-329),
`d/ds ‖D^j e‖₂² = 2 (ν⟨D^j e, D^jΔe⟩ - ⟨D^j e, D^j A⟩ - ⟨D^j e, D^j∇π⟩ - ⟨D^j e, D^j div Q_c⟩)`. -/
def TrainJetEnergyBalance : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    ∀ j : ℕ,
      HasDerivAt (fun r => jetEnergy c j (trainErr tr r))
        (2 * (ν * jetPair c j (trainErr tr s) (Train.vecLaplacian (trainErr tr s))
          - jetPair c j (trainErr tr s) (advDiff tr s)
          - jetPair c j (trainErr tr s) (Train.gradS (errPressure tr s))
          - jetPair c j (trainErr tr s) (Train.matDiv (Qc ν c s)))) s

/-! ### Leaves: integration by parts and the transport estimate on the cylinder -/

/-- **Leaf 5: jet viscous integration by parts** (line 348, the dissipation term). For a smooth
`c`-periodic field with all word derivatives in `L²(cell)`,
`⟨D^j f, D^jΔf⟩ = -∑_k ‖∂_k D^j f‖₂² = -‖D^{j+1} f‖₂²`. -/
def JetViscousIBP : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Plane → Vec, CellSmoothL2 c f → ∀ j : ℕ,
    jetPair c j f (Train.vecLaplacian f) = -jetEnergy c (j + 1) f

/-- **Leaf 6: pressure orthogonality.** For a divergence-free `f` as in leaf 5 and a smooth
`c`-periodic bounded `P` with `∇P ∈ H^∞(cell)`, `⟨D^j f, D^j∇P⟩ = 0` for every `j` (integrate
`∂_k` by parts onto `∂_k D^j f_k = D^j div f = 0`; for `j = 0` the boundary terms
`∫_q P f₂(q, ±R) dq` tend to `0`). -/
def JetPressureOrth : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Plane → Vec, CellSmoothL2 c f → (∀ z : Plane, Cyl.divergence f z = 0) →
    ∀ P : Plane → ℝ, ContDiff ℝ ∞ P → Cyl.IsPeriodic c P → (∃ M : ℝ, ∀ z : Plane, |P z| ≤ M) →
    (∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (Train.gradS P) k) 2 (Cyl.cellμ c)) →
    ∀ j : ℕ, jetPair c j f (Train.gradS P) = 0

/-- **Leaf 7: the differentiated transport estimate** (lines 352-358). For `j` there is `A_j`,
independent of the period `c ≥ 1`, such that for a smooth periodic divergence-free `V` with
`|∂_w V_k| ≤ M_{|w|}` and a divergence-free `f` as in leaf 5 with bounded word derivatives and
`|∂_β f_k| ≤ G`,
`|⟨D^j f, D^j((V+f)·∇(V+f) - V·∇V)⟩| ≤ A_j (G ‖D^j f‖² + ∑_{i=1}^{j+1} M_i ‖D^{j+1-i} f‖ ‖D^j f‖)`.
(The bracket is `(V·∇)f + (f·∇)V + (f·∇)f`; the terms `(V·∇)D^j f`, `(f·∇)D^j f` pair to zero by
zero divergence; `‖[D^j, f·∇]f‖₂ ≤ C_j ‖∇f‖_∞ ‖D^j f‖₂` by the period-independent
Gagliardo-Nirenberg inequality `CylGN` (`PartI:T07`) applied to `∇f`; the Leibniz terms of the
two cross products carry `‖D^iV‖_∞`.) -/
def JetTransportBound : Prop :=
  ∀ j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ c : ℝ, 1 ≤ c → ∀ V f : Plane → Vec,
    ContDiff ℝ ∞ V → Cyl.IsPeriodic c V → (∀ z : Plane, Cyl.divergence V z = 0) →
    CellSmoothL2 c f → (∀ z : Plane, Cyl.divergence f z = 0) →
    (∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w f k z| ≤ M) →
    ∀ (G : ℝ) (M : ℕ → ℝ),
      (∀ (β : Bool) (k : Fin 2) (z : Plane), |wordComp [β] f k z| ≤ G) →
      (∀ (w : List Bool) (k : Fin 2) (z : Plane), |wordComp w V k z| ≤ M w.length) →
      |jetPair c j f (fun z => Train.advection (fun x => V x + f x) z - Train.advection V z)| ≤
        A * (G * jetEnergy c j f +
          ∑ i ∈ Finset.Icc 1 (j + 1),
            M i * Real.sqrt (jetEnergy c (j + 1 - i) f) * Real.sqrt (jetEnergy c j f))

/-- **Leaf 8: the weights in the transport sum** (pure real analysis; lines 344, 349). If
`|T_j| ≤ A_j (a^{-2} J_j + ∑_{i=1}^{j+1} Cv_i a^{-(3+i)/2} √J_{j+1-i} √J_j)` for `j ≤ N`, then
`∑_{j≤N} (δa)^j |T_j| ≤ K a^{-2} ∑_{j≤N} (δa)^j J_j` with `K` depending on `N, A, Cv` only
(`0 < δ ≤ 1`, `a ≥ 1`; `(δa)^j a^{-(3+i)/2} = δ^{(i-1)/2} a^{-2} (δa)^{(j+l)/2}`, `l = j+1-i`). -/
def TransportWeightSum : Prop :=
  ∀ (N : ℕ) (A Cv : ℕ → ℝ), (∀ j, 0 ≤ A j) → (∀ i, 0 ≤ Cv i) → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (δ a : ℝ) (J T : ℕ → ℝ), 0 < δ → δ ≤ 1 → 1 ≤ a → (∀ j, 0 ≤ J j) →
      (∀ j ≤ N, |T j| ≤ A j * ((a ^ 2)⁻¹ * J j +
        ∑ i ∈ Finset.Icc 1 (j + 1),
          Cv i * a ^ (-(3 + (i : ℝ)) / 2) * Real.sqrt (J (j + 1 - i)) * Real.sqrt (J j))) →
      ∑ j ∈ Finset.range (N + 1), (δ * a) ^ j * |T j| ≤
        K / a ^ 2 * ∑ j ∈ Finset.range (N + 1), (δ * a) ^ j * J j

/-- **Leaf 9: one integration by parts on the stress** (line 346). For `f` as in leaf 5 and a
smooth `c`-periodic tensor field `Q` with all word derivatives in `L²(cell)`,
`|⟨D^j f, D^j div Q⟩| = |∑ ∫ ∂_k D^j f_l D^j Q_{kl}| ≤ ‖D^{j+1} f‖₂ ‖D^j Q‖₂`. -/
def JetForcingIBP : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Plane → Vec, CellSmoothL2 c f →
    ∀ Q : Plane → Matrix (Fin 2) (Fin 2) ℝ, (∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Q z k l)) →
    (∀ k l : Fin 2, Cyl.IsPeriodic c (fun z => Q z k l)) →
    (∀ (w : List Bool) (k l : Fin 2),
      MemLp (B0151.derivWord w (fun z => Q z k l)) 2 (Cyl.cellμ c)) →
    ∀ j : ℕ, |jetPair c j f (Train.matDiv Q)| ≤
      Real.sqrt (jetEnergy c (j + 1) f) * Real.sqrt (matEnergy c j Q)

/-- **Leaf 10: the forcing jet bound** (lines 331-335, `Train.Vc_bounds`, weight `m = 0`,
transported from the cell `(0, c] × ℝ` to the centred cell by periodicity). For `N` there are
`B ≥ 0`, `b > 0` with: every word derivative of every entry of `Q_c(s)` is in `L²(cell)` and
`‖D^jQ_c(s)‖₂² ≤ B a^{-(5+j)} e^{-b c²/a}` for `j ≤ N`, whenever `1 ≤ a = 1 + νs ≤ c²`. -/
def VcStressJetBound : Prop :=
  ∀ N : ℕ, ∃ B b : ℝ, 0 ≤ B ∧ 0 < b ∧
    ∀ ν c s : ℝ, 0 < ν → 1 ≤ c → 0 < s → width ν s ≤ c ^ 2 →
      (∀ (w : List Bool) (k l : Fin 2),
        MemLp (B0151.derivWord w (fun z => Qc ν c s z k l)) 2 (Cyl.cellμ c)) ∧
      ∀ j ≤ N, matEnergy c j (Qc ν c s) ≤
        B / width ν s ^ (5 + j) * Real.exp (-(b * c ^ 2 / width ν s))

/-- **Leaf 11: the real-analysis closure** (lines 344-350, 358-359). Let `J_j(r) ≥ 0`
(`J_j = ‖D^j e‖₂²`) be differentiable at `s > 0` for `j ≤ N` with
`J_j'(s) = 2(-ν J_{j+1}(s) - T_j - F_j)`, let the transport satisfy
`∑_{j≤N} (δa)^j |T_j| ≤ K a^{-2} E` and the forcing `|F_j| ≤ √J_{j+1} √(B a^{-(5+j)} X)`, where
`a = 1 + νs`, `E = ∑_{j≤N} (δa)^j J_j(s)`, `0 < δ ≤ 1`, `Nδ ≤ 1/4`. Then `E_N²(r) =
∑_{j≤N} (δa(r))^j J_j(r)` is differentiable at `s` with a derivative `D` such that
`ν⁻¹ D + ∑_{j≤N} (δa)^j J_{j+1}(s) ≤ 2K/(νa²) E + 2(N+1)B/(ν²a⁵) X`. (Product rule; the weight
derivative `jδν(δa)^{j-1} J_j` is at most `ν/4 (δa)^{j-1} J_j`, absorbed by the dissipation of
order `j-1`; `2ν⁻¹√J√Y ≤ J/2 + 2ν⁻²Y` for the forcing; `δ^j ≤ 1`.) -/
def EnergyClosure : Prop :=
  ∀ (N : ℕ) (ν δ s K B X : ℝ) (J : ℕ → ℝ → ℝ) (T F : ℕ → ℝ),
    0 < ν → 0 < s → 0 < δ → (N : ℝ) * δ ≤ 1 / 4 → δ ≤ 1 → 0 ≤ K → 0 ≤ B → 0 ≤ X →
    (∀ j, 0 ≤ J j s) →
    (∀ j ≤ N, HasDerivAt (J j) (2 * (ν * -J (j + 1) s - T j - F j)) s) →
    ∑ j ∈ Finset.range (N + 1), (δ * width ν s) ^ j * |T j| ≤
      K / width ν s ^ 2 * ∑ j ∈ Finset.range (N + 1), (δ * width ν s) ^ j * J j s →
    (∀ j ≤ N, |F j| ≤ Real.sqrt (J (j + 1) s) * Real.sqrt (B / width ν s ^ (5 + j) * X)) →
    ∃ D : ℝ, HasDerivAt (fun r => ∑ j ∈ Finset.range (N + 1), (δ * width ν r) ^ j * J j r) D s ∧
      ν⁻¹ * D + ∑ j ∈ Finset.range (N + 1), (δ * width ν s) ^ j * J (j + 1) s ≤
        2 * K / (ν * width ν s ^ 2) * ∑ j ∈ Finset.range (N + 1), (δ * width ν s) ^ j * J j s +
          2 * ((N : ℝ) + 1) * B / (ν ^ 2 * width ν s ^ 5) * X

/-! ### Assembly -/

theorem jetEnergy_nonneg (c : ℝ) (j : ℕ) (f : Plane → Vec) : 0 ≤ jetEnergy c j f := by
  unfold jetEnergy jetPair
  exact integral_nonneg fun z => Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun k _ =>
    mul_self_nonneg _

/-- `Train.Vc_bounds` with weight `m = 0`, in the word notation. -/
theorem Vc_word_bound (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ width ν s →
    width ν s ≤ c ^ 2 → ∀ w : List Bool, w.length = i → ∀ (k : Fin 2) (z : Plane),
      |wordComp w (Vc ν c s) k z| ≤ C * width ν s ^ (-(3 + (i : ℝ)) / 2) := by
  obtain ⟨C, b, hC, -, h⟩ := Train.Vc_bounds i 0
  refine ⟨C, hC, fun ν c s hc ha1 hac w hw k z => ?_⟩
  have := (h ν c s hc ha1 hac).1 w hw k z
  simpa [wordComp] using this

/-- **`PartI:T08`, conditional**: the differentiated energy inequality from the eleven leaves. -/
theorem differentiated_energy_inequality_of
    (h1 : TrainErrBasic) (h2 : TrainErrJetL2) (h3 : TrainPressureRegular)
    (h4 : TrainJetEnergyBalance) (h5 : JetViscousIBP) (h6 : JetPressureOrth)
    (h7 : JetTransportBound) (h8 : TransportWeightSum) (h9 : JetForcingIBP)
    (h10 : VcStressJetBound) (h11 : EnergyClosure) :
    DifferentiatedEnergyInequality := by
  intro N hN
  unfold JetTransportBound at h7
  choose A hA0 hA using h7
  choose Cv hCv0 hCv using Vc_word_bound
  obtain ⟨K, hK0, hK⟩ := h8 N A Cv hA0 hCv0
  obtain ⟨B, b, hB0, hb, hQ⟩ := h10 N
  refine ⟨2 * K + 2 * ((N : ℝ) + 1) * B + 1, b, by positivity, hb, ?_⟩
  intro ν c δ hν hν1 hc hδ hδN tr htr s hs hac hboot
  have hc0 : 0 < c := by linarith
  have hνs : 0 ≤ ν * s := (mul_pos hν hs).le
  have ha1 : 1 ≤ width ν s := by
    simp only [Train.width]; linarith
  have hw : 0 < width ν s := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNδ : (N : ℝ) * δ ≤ 1 / 4 := by
    calc (N : ℝ) * δ ≤ N * (1 / (4 * N)) := mul_le_mul_of_nonneg_left hδN hNpos.le
      _ = 1 / 4 := by field_simp
  have hδ1 : δ ≤ 1 := by
    have h3N : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have : 1 / (4 * (N : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  obtain ⟨hes, hep, hed, heb, hVs, hQs, hQp⟩ := h1 ν c hν hc tr htr s hs hac
  have hL2 := h2 ν c hν hc tr htr s hs hac
  have hcs : CellSmoothL2 c (trainErr tr s) := ⟨hes, hep, hL2⟩
  obtain ⟨hπs, hπp, hπb, hπL2⟩ := h3 ν c hν hc tr htr s hs hac
  obtain ⟨hQL2, hQb⟩ := hQ ν c s hν hc hs hac
  refine ⟨hL2, ?_⟩
  -- the derivative of each jet energy: viscous term by parts, pressure term zero
  have hder : ∀ j ≤ N, HasDerivAt (fun r => jetEnergy c j (trainErr tr r))
      (2 * (ν * -jetEnergy c (j + 1) (trainErr tr s)
        - jetPair c j (trainErr tr s) (advDiff tr s)
        - jetPair c j (trainErr tr s) (Train.matDiv (Qc ν c s)))) s := by
    intro j _
    have hbal := h4 ν c hν hc tr htr s hs hac j
    rw [h5 c hc0 (trainErr tr s) hcs j,
      h6 c hc0 (trainErr tr s) hcs hed (errPressure tr s) hπs hπp hπb hπL2 j, sub_zero] at hbal
    exact hbal
  -- the transport bracket, `v = V_c + e`
  have hvsum : tr.v s = fun x => Vc ν c s x + trainErr tr s x :=
    funext fun x => by simp only [trainErr]; abel
  have hadv : advDiff tr s = fun z =>
      Train.advection (fun x => Vc ν c s x + trainErr tr s x) z - Train.advection (Vc ν c s) z := by
    unfold advDiff
    rw [hvsum]
  have hT : ∀ j ≤ N, |jetPair c j (trainErr tr s) (advDiff tr s)| ≤
      A j * ((width ν s ^ 2)⁻¹ * jetEnergy c j (trainErr tr s) +
        ∑ i ∈ Finset.Icc 1 (j + 1), Cv i * width ν s ^ (-(3 + (i : ℝ)) / 2) *
          Real.sqrt (jetEnergy c (j + 1 - i) (trainErr tr s)) *
          Real.sqrt (jetEnergy c j (trainErr tr s))) := by
    intro j _
    rw [hadv]
    exact hA j c hc (Vc ν c s) (trainErr tr s) hVs (Train.Vc_periodic ν c s)
      (fun z => Train.Vc_div hν hc0.ne' hs.le z) hcs hed heb (width ν s ^ 2)⁻¹
      (fun i => Cv i * width ν s ^ (-(3 + (i : ℝ)) / 2)) hboot
      (fun w k z => hCv w.length ν c s hc0 ha1 hac w rfl k z)
  have hTsum := hK δ (width ν s) (fun j => jetEnergy c j (trainErr tr s))
    (fun j => jetPair c j (trainErr tr s) (advDiff tr s)) hδ hδ1 ha1
    (fun j => jetEnergy_nonneg c j _) hT
  -- the forcing
  have hF : ∀ j ≤ N, |jetPair c j (trainErr tr s) (Train.matDiv (Qc ν c s))| ≤
      Real.sqrt (jetEnergy c (j + 1) (trainErr tr s)) *
        Real.sqrt (B / width ν s ^ (5 + j) * Real.exp (-(b * c ^ 2 / width ν s))) := by
    intro j hj
    exact (h9 c hc0 (trainErr tr s) hcs (Qc ν c s) hQs hQp hQL2 j).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQb j hj)) (Real.sqrt_nonneg _))
  -- the closure
  obtain ⟨D, hD, hineq⟩ := h11 N ν δ s K B (Real.exp (-(b * c ^ 2 / width ν s)))
    (fun j r => jetEnergy c j (trainErr tr r))
    (fun j => jetPair c j (trainErr tr s) (advDiff tr s))
    (fun j => jetPair c j (trainErr tr s) (Train.matDiv (Qc ν c s)))
    hν hs hδ hNδ hδ1 hK0 hB0 (Real.exp_pos _).le (fun j => jetEnergy_nonneg c j _) hder hTsum hF
  refine ⟨D, hD, hineq.trans ?_⟩
  have hE : 0 ≤ weightedEnergy c δ (width ν s) N (trainErr tr s) :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (pow_nonneg (mul_nonneg hδ.le hw.le) _) (jetEnergy_nonneg c j _)
  have hKC : 2 * K ≤ 2 * K + 2 * ((N : ℝ) + 1) * B + 1 := by
    have : 0 ≤ 2 * ((N : ℝ) + 1) * B := by positivity
    linarith
  have hBC : 2 * ((N : ℝ) + 1) * B ≤ 2 * K + 2 * ((N : ℝ) + 1) * B + 1 := by linarith
  have hX : 0 ≤ Real.exp (-(b * c ^ 2 / width ν s)) := (Real.exp_pos _).le
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hKC (by positivity)) hE
  · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hBC (by positivity)) hX

end UnforcedLeray.Short.PartI
