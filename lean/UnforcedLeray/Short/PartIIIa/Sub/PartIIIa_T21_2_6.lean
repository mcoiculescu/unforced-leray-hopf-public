import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Units.B0147

/-!
# Part III-a, `PartIII-a:T21/2/6`: the rescaled BUC train is uniformly bounded (decomposition)

Source of record: `the November 2 reference manuscript` (SP), lines 3050-3051
("The rescaled train and its first two derivatives are uniformly bounded for `θ ≥ b`"), from
lines 2866-2873 ("The rescaled train differs from the periodized Gaussian by
`C e_c e^{-bθ/e_c}` in every fixed weighted derivative norm on `θ ≥ b > 0`. This follows by
rescaling the train error, interpolating its Gaussian-small unweighted norm with a larger fixed
weighted norm, and absorbing the resulting fixed powers into the Gaussian. The required region is
contained in `1 ≤ a ≤ c²`."), with Lemma `sct:train` (SP 290-336: `ψ^p = -2a⁻¹e^{-|x|²/(4a)}`,
`V_c^p = Σ_n ∇^⊥ψ^p(q-nc,η,s)`, `‖D^j(v - V_c^p)(s)‖_∞ ≤ C_jν⁻¹a^{-(5+j)/2}e^{-b_jc²/a}` on
`1 ≤ a ≤ c²`, `‖D^jV_c^p‖_∞ ≤ C_ja^{-(3+j)/2}`) and, for the "larger fixed weighted norm", Lemma
`sct:heat` (SP 437-459: `sct:fluctuation`, `sct:expansion`) with `sct:mean` (SP 397-404).

## The class of the train

`RescaledTrainBounds m` (`Clock/WeakSmoothing/Adjoint.lean`) quantified over every
`B0140.TrainSol ν ν⁻²`; since `ORG:train-class-IIIa/sub` it carries `PartI.IsBUCTrain tr` and is
the same statement as `RescaledTrainBoundsBUC m`.  The train of the source is the
Gallay-Slijepcevic train in `BUC`
(SP 261-288); every Part I estimate (`Short/PartI/StatementsTrain.lean`) is stated for the class
`PartI.IsBUCTrain`, and `B0140.IsTrain` alone carries no time-uniform bound (`PartI/TrainClass.lean`).
`RescaledTrainBoundsBUC m` is therefore `RescaledTrainBounds m` with `PartI.IsBUCTrain tr →` after
the train binder.  The consumers of `RescaledTrainBounds` (`AdjointLocalizedBound`,
`AdjointEnergyIneqs`, `LocalizedSourceBounds`, `MovingWeakStrong`, `WeakSmoothingPhys`) are
restricted to BUC trains accordingly.

## The route

With `a = clockA ν r`, `θ = (νa)⁻¹ ≥ b`, `c = ν⁻²`, `d = c/√a`:
* rescaling (`MovingTrainVJet`, `MovingTrainEJet`): `D^jV(y) = a^{3/2}(√a)^j (D^jv)(√a y)`,
  `D^jE_mov(y) = a²(√a)^j (D^jE)(√a y)`;
* the velocity (`RescaledVelPhys`): `‖D^jv(r)‖_∞ ≤ ‖D^j(v - V_c^p)‖_∞ + ‖D^jV_c^p‖_∞
  ≤ C a^{-(3+j)/2}`, since `ν⁻¹a⁻¹e^{-b_jc²/a} ≤ ν⁻¹c⁻²/b_j = ν³/b_j` (`e^{-x} ≤ 1/x`) and
  `a ≤ (νb)⁻¹ ≤ c²`;
* the vorticity (`RescaledVortPhys`): `E = curl V_c^p + curl(v - V_c^p)`; the Gaussian part is the
  periodized unit Gaussian vorticity on the moving cell (`GaussVortMoving`, from `DatumCurlScale`,
  `DatumCurlLattice`, `CenteredLatticeWeighted`, `DatumCurlWeighted`); the error part
  (`VortErrMoving`) interpolates `w|F| ≤ (|F|)^{1/2} (w²|F|)^{1/2}` between the Gaussian-small sup
  bound of `D^{j+1}(v - V_c^p)` (`PartI.TrainComparison`, `CurlJetBound`) and the polynomial
  weighted bound of the train (`TrainWeightedJetPoly`, from `FluctJetWeighted`, `MeanJetWeighted`,
  `MeanVecFormula`, `MeanStreamJetBound`, `VcWeightedJet`) and of `V_c^p` (`VcWeightedJet`); the
  fixed powers are absorbed by `e^{-b c²/(2a)} ≤ e^{-bν⁻³/2}` (`ExpPolyAbsorb`).

## Contents

* the target `RescaledTrainBoundsBUC` and the weakening `rescaledTrainBoundsBUC_of_all`;
* the leaf statements (Props) listed above;
* the assembly `rescaledTrainBoundsBUC_of` (proved here).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The target -/

/-- **The rescaled BUC train is uniformly bounded** (SP 3050-3051, from SP 2866-2873 and Lemma
`sct:train`, SP 290-336): `RescaledTrainBounds m` for the Gallay-Slijepcevic train of the source
(SP 261-288), i.e. with the class hypothesis `PartI.IsBUCTrain tr`.  For `b` large and `ν` small,
on `θ(r) ≥ b`, the rescaled velocity `V = a^{3/2}v(√a·)` and its first two derivatives are bounded,
and the rescaled vorticity `E_mov = a²E(√a·)` and its first three derivatives are bounded with the
weight `⟨y⟩^{m+2}` on the moving cell `C_{d}`, `d = c/√a`. -/
def RescaledTrainBoundsBUC (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r →
      b ≤ clockTheta ν r →
      (∀ j : ℕ, j ≤ 2 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j (movingTrainV tr r) y‖ ≤ C) ∧
      (∀ j : ℕ, j ≤ 3 → ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
        B0579.jb y ^ ((m + 2) / 2) * ‖iteratedFDeriv ℝ j (movingTrainE tr r) y‖ ≤ C)

/-- `RescaledTrainBounds m` (now stated for BUC trains) is `RescaledTrainBoundsBUC m`. -/
theorem rescaledTrainBoundsBUC_of_all (m : ℝ) (h : RescaledTrainBounds m) :
    RescaledTrainBoundsBUC m := h

/-- The converse identification, for consumers stated with `RescaledTrainBounds m`. -/
theorem rescaledTrainBounds_of_BUC (m : ℝ) (h : RescaledTrainBoundsBUC m) :
    RescaledTrainBounds m := h

/-! ## First level: rescaling and the physical bounds -/

/-- **Rescaling of the velocity jets** (SP 2854-2873; `movingTrainV tr r y = a^{3/2}v(r, √a y)`):
`‖D^jV(y)‖ ≤ a^{3/2}(√a)^j ‖D^jv(r)(√a y)‖`, `a = clockA ν r` (the `Fin 2 → ℝ` sup norm of `V` is at
most the Euclidean norm of `v`).  Pure calculus; `v(r)` is `C^∞` for `r ≥ 0`
(`B0238.contDiff_Vc`). -/
def MovingTrainVJet : Prop :=
  ∀ ν c : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, ∀ r : ℝ, 0 ≤ r →
    ∀ (j : ℕ) (y : ℝ × ℝ),
      ‖iteratedFDeriv ℝ j (movingTrainV tr r) y‖ ≤
        (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j) *
          ‖iteratedFDeriv ℝ j (tr.v r)
            (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖

/-- **Rescaling of the vorticity jets** (SP 2854-2873; `movingTrainE tr r y = a²E(r, √a y)`):
`‖D^jE_mov(y)‖ ≤ a²(√a)^j ‖D^jE(r)(√a y)‖`, `a = clockA ν r`.  Pure calculus. -/
def MovingTrainEJet : Prop :=
  ∀ ν c : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, ∀ r : ℝ, 0 ≤ r →
    ∀ (j : ℕ) (y : ℝ × ℝ),
      ‖iteratedFDeriv ℝ j (movingTrainE tr r) y‖ ≤
        (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j) *
          ‖iteratedFDeriv ℝ j (UnforcedLeray.B0238.Ec tr r)
            (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖

/-- **The physical velocity bound** (SP 290-336 `sct:comparison` sup line and
`‖D^jV_c^p‖_∞ ≤ C_ja^{-(3+j)/2}`, SP 2866-2873): for `b` large and `ν` small, on `θ(r) ≥ b`
(so `1 ≤ a ≤ c²`), `‖D^jv(r)‖_∞ ≤ C a^{-(3+j)/2}` for `j ≤ 2`, the BUC train at `c = ν⁻²`. -/
def RescaledVelPhys : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ × ℝ,
          ‖iteratedFDeriv ℝ j (tr.v r) x‖ ≤
            C * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹

/-- **The physical weighted vorticity bound, read on the moving cell** (SP 2866-2873, 3050-3054):
for `b` large and `ν` small, on `θ(r) ≥ b`, for `j ≤ 3` and `y` in the moving cell `C_d`,
`d = c/√a`: `⟨y⟩^{m+2}|D^jE(r)(√a y)| ≤ C a^{-2-j/2}` (`jb y = ⟨y⟩²`). -/
def RescaledVortPhys (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∀ j : ℕ, j ≤ 3 → ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
          B0579.jb y ^ ((m + 2) / 2) *
              ‖iteratedFDeriv ℝ j (UnforcedLeray.B0238.Ec tr r)
                (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ ≤
            C * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹

/-! ## Second level: calculus and Gaussian leaves -/

/-- **Weighted jets of the periodized vortex** (SP 327-336, `eq:st18-t00145`; `Train.Vc_bounds`
with the transverse weight `(1 + η²/a)^k`, transported to `iteratedFDeriv` as in
`Spine.vcRegularity_proof`): `(1 + η²/a)^k ‖D^jV_c^p(s)(x)‖ ≤ C a^{-(3+j)/2}` on `1 ≤ a ≤ c²`. -/
def VcWeightedJet : Prop :=
  ∀ k j : ℕ, ∃ C : ℝ, ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s → clockA ν s ≤ c ^ 2 →
    ∀ x : ℝ × ℝ,
      (1 + x.2 ^ 2 / clockA ν s) ^ k * ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν c s) x‖ ≤
        C * (clockA ν s ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν s) ^ j)⁻¹

/-- **Jets of the curl** (calculus): `curl u = ∂_qu₂ - ∂_ηu₁` is a norm-`≤ 2` linear image of
`Du`, so `‖D^j curl u‖ ≤ 2‖D^{j+1}u‖` for smooth `u`. -/
def CurlJetBound : Prop :=
  ∀ u : ℝ × ℝ → EuclideanSpace ℝ (Fin 2), ContDiff ℝ ∞ u → ∀ (j : ℕ) (x : ℝ × ℝ),
    ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl u) x‖ ≤ 2 * ‖iteratedFDeriv ℝ (j + 1) u x‖

/-- **Absorption of fixed powers into the Gaussian** (SP 2869-2871): `x^N e^{-βx} ≤ N!/β^N`
for `β > 0`, `x ≥ 0` (from `(βx)^N/N! ≤ e^{βx}`). -/
def ExpPolyAbsorb : Prop :=
  ∀ (N : ℕ) (β x : ℝ), 0 < β → 0 ≤ x →
    x ^ N * Real.exp (-(β * x)) ≤ (N.factorial : ℝ) / β ^ N

/-- **Scaling of the Gaussian vorticity** (SP 2866-2867; `V_c^p(z) = a^{-3/2}·datum_{c/√a}(z/√a)`,
`Spine.vcReg_Vc_scale`): `‖D^j curl V_c^p(s)(√a y)‖ ≤ a^{-2}(√a)^{-j}‖D^j curl datum_d(y)‖`,
`d = c/√a`, `datum_d = P_d v₀` the periodized unit Gaussian vortex (`Train.datum`). -/
def DatumCurlScale : Prop :=
  ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s → ∀ (j : ℕ) (y : ℝ × ℝ),
    ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c s))
        (Real.sqrt (clockA ν s) * y.1, Real.sqrt (clockA ν s) * y.2)‖ ≤
      (clockA ν s ^ 2 * Real.sqrt (clockA ν s) ^ j)⁻¹ *
        ‖iteratedFDeriv ℝ j
          (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum (cellLen c (clockA ν s)))) y‖

/-- **Word derivatives of the periodized unit Gaussian vorticity are lattice sums of
polynomial-times-Gaussian profiles** (SP 262-264, 327-336; `B0147.GP`, `B0147.GP_U`,
`B0147.GP.derivWord_lattice`): for every word `w` there is `g ∈ GP` with
`D_w curl(datum_d) = Σ_n g(· - nd e₁)` for every period `d ≠ 0`. -/
def DatumCurlLattice : Prop :=
  ∀ w : List Bool, ∃ g : ℝ × ℝ → ℝ, UnforcedLeray.B0147.GP g ∧ ∀ d : ℝ, d ≠ 0 →
    UnforcedLeray.B0151.derivWord w
        (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) =
      UnforcedLeray.B0146.latticeSum d g

/-- **Weighted lattice sums on the centered cell** (SP 2866-2867, 3044: the periodized Gaussian
in the weighted norm of the moving cell): for `|g(y)| ≤ Ke^{-β|y|²}` and `L ≥ 1`,
`⟨y⟩^{2k}|Σ_n g(y - nLe₁)| ≤ C(K, β, k)` on `C_L = [-L/2, L/2) × ℝ` (there
`(y₁ - nL)² ≥ y₁²` for every `n`). -/
def CenteredLatticeWeighted : Prop :=
  ∀ (K β : ℝ), 0 ≤ K → 0 < β → ∀ k : ℕ, ∃ C : ℝ, ∀ g : ℝ × ℝ → ℝ,
    UnforcedLeray.B0147.GBound K β g → ∀ L : ℝ, 1 ≤ L → ∀ y ∈ B0579.cell L,
      B0579.jb y ^ k * |UnforcedLeray.B0146.latticeSum L g y| ≤ C

/-- **The periodized unit Gaussian vorticity in every fixed weighted derivative norm on the
centered cell** (SP 2866-2867): `⟨y⟩^{2k}‖D^j curl datum_d(y)‖ ≤ C` on `C_d`, uniformly in
`d ≥ 1`. -/
def DatumCurlWeighted : Prop :=
  ∀ k j : ℕ, ∃ C : ℝ, ∀ d : ℝ, 1 ≤ d → ∀ y ∈ B0579.cell d,
    B0579.jb y ^ k *
      ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y‖ ≤ C

/-- **The Gaussian part of the rescaled vorticity** (SP 2866-2867, 3050-3051): on `1 ≤ a ≤ c²`
(`d = c/√a ≥ 1`), `⟨y⟩^{2k}|D^j curl V_c^p(s)(√a y)| ≤ C a^{-2-j/2}` on the moving cell. -/
def GaussVortMoving : Prop :=
  ∀ k j : ℕ, ∃ C : ℝ, ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s → clockA ν s ≤ c ^ 2 →
    ∀ y ∈ B0579.cell (cellLen c (clockA ν s)),
      B0579.jb y ^ k *
          ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c s))
            (Real.sqrt (clockA ν s) * y.1, Real.sqrt (clockA ν s) * y.2)‖ ≤
        C * (clockA ν s ^ 2 * Real.sqrt (clockA ν s) ^ j)⁻¹

/-! ## Second level: the train error -/

/-- **The polynomial weighted bound of the train** (the "larger fixed weighted norm" of
SP 2869-2870; from `sct:fluctuation` SP 439-446, `sct:expansion` SP 447-459 with `sct:mean`
SP 397-404 for `s > 0`, and the datum `v(0) = P_cv₀`, SP 261-264, at `s = 0`): for every `k, j`
there are `C, N, ν₀` with `(1 + η²)^k ‖D^jv(s)(x)‖ ≤ Cν^{-N}(1+s)^N` for the BUC train at
`c = ν⁻²`, `ν ≤ ν₀`, every age `s ≥ 0`. -/
def TrainWeightedJetPoly : Prop :=
  ∀ k j : ℕ, ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ × ℝ,
        (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤ C * ν⁻¹ ^ N * (1 + s) ^ N

/-- **The weighted fluctuation jets** (`sct:fluctuation`, SP 439-446, `ℓ = 0`, sup part, with
`P e^{-κνs/c²} ≤ P ≤ Cν^{-N}` at `c = ν⁻²`): `(1 + η²)^k‖D^j\tilde v(s)(x)‖ ≤ Cν^{-N}`, `s > 0`. -/
def FluctJetWeighted : Prop :=
  ∀ k j : ℕ, ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
        (1 + x.2 ^ 2) ^ k *
            ‖iteratedFDeriv ℝ j
              (UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s)) x‖ ≤
          C * ν⁻¹ ^ N

/-- **The mean velocity is the transverse derivative of the mean stream** (`sct:mean`,
SP 397-404: `\bar v₁ = -S_η`, `\bar v₂ = 0`), with the smoothness of the slice `η ↦ S(s, η)` for
`s > 0`. -/
def MeanVecFormula : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s →
      ContDiff ℝ ∞ (fun η => UnforcedLeray.Short.PartI.meanStream tr s η) ∧
      ∀ η : ℝ, UnforcedLeray.Short.PartI.hmean c (tr.v s) η =
        UnforcedLeray.Train.toVec
          (-deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η, 0)

/-- **Weighted pointwise bounds of the mean stream derivatives** (`sct:expansion`, last display,
SP 456-459 with `ℓ = 0`, `p = ∞`, `m ∈ {0, 2k}`; continuity of the slice from `sct:mean`):
`(1 + η²)^k|∂_η^bS(s, η)| ≤ Cν^{-N}(1+s)^N` for the BUC train at `c = ν⁻²`, `s > 0`. -/
def MeanStreamJetBound : Prop :=
  ∀ k b : ℕ, ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ η : ℝ,
        (1 + η ^ 2) ^ k *
            |iteratedDeriv b (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
          C * ν⁻¹ ^ N * (1 + s) ^ N

/-- **The weighted mean jets** (SP 397-404, 447-459): the mean `x ↦ \bar v(s, x₂)` is `C^∞`
and `(1 + η²)^k‖D^j\bar v(s)(x)‖ ≤ Cν^{-N}(1+s)^N`, `s > 0`. -/
def MeanJetWeighted : Prop :=
  ∀ k j : ℕ, ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s →
        ContDiff ℝ ∞
            (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) x.2) ∧
          ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ k *
              ‖iteratedFDeriv ℝ j
                (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) x.2)
                x‖ ≤
            C * ν⁻¹ ^ N * (1 + s) ^ N

/-- **The error part of the rescaled vorticity** (SP 2868-2871: "rescaling the train error,
interpolating its Gaussian-small unweighted norm with a larger fixed weighted norm, and absorbing
the resulting fixed powers into the Gaussian"): for every `k`, for `b` large and `ν` small, on
`θ(r) ≥ b`, `j ≤ 3`, on the moving cell,
`⟨y⟩^{2k}|D^j curl(v - V_c^p)(r)(√a y)| ≤ C a^{-2-j/2}`. -/
def VortErrMoving : Prop :=
  ∀ k : ℕ, ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∀ j : ℕ, j ≤ 3 → ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
          B0579.jb y ^ k *
              ‖iteratedFDeriv ℝ j
                (UnforcedLeray.Cyl.curl
                  (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x))
                (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ ≤
            C * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹

/-! ## Assembly -/

/-- **Assembly** (SP 3050-3051): the rescaling of the jets and the two physical bounds give the
uniform bound of the rescaled BUC train. -/
theorem rescaledTrainBoundsBUC_of (m : ℝ) (hV1 : MovingTrainVJet) (hE1 : MovingTrainEJet)
    (hV : RescaledVelPhys) (hE : RescaledVortPhys m) : RescaledTrainBoundsBUC m := by
  obtain ⟨b₁, hb₁⟩ := hV
  obtain ⟨b₂, hb₂⟩ := hE
  refine ⟨max b₁ b₂, fun b hb => ?_⟩
  obtain ⟨C₁, ν₁, hν₁, h₁⟩ := hb₁ b (le_trans (le_max_left _ _) hb)
  obtain ⟨C₂, ν₂, hν₂, h₂⟩ := hb₂ b (le_trans (le_max_right _ _) hb)
  refine ⟨max C₁ C₂, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν tr hbuc r hr hθ => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hνa : ν ∈ Ioc 0 ν₁ := ⟨hν.1, le_trans hν.2 (min_le_left _ _)⟩
  have hνb : ν ∈ Ioc 0 ν₂ := ⟨hν.1, le_trans hν.2 (min_le_right _ _)⟩
  have ha : 0 < clockA ν r := by
    unfold clockA
    have := mul_nonneg hνpos.le hr
    linarith
  have hsq : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha
  refine ⟨fun j hj y => ?_, fun j hj y hy => ?_⟩
  · have hK : 0 < clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j :=
      mul_pos (Real.rpow_pos_of_pos ha _) (pow_pos hsq _)
    calc ‖iteratedFDeriv ℝ j (movingTrainV tr r) y‖
        ≤ (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j) *
            ‖iteratedFDeriv ℝ j (tr.v r)
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ :=
          hV1 ν _ hνpos tr r hr j y
      _ ≤ (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j) *
            (C₁ * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹) :=
          mul_le_mul_of_nonneg_left (h₁ ν hνa tr hbuc r hr hθ j hj _) hK.le
      _ = C₁ := by
          rw [mul_comm C₁, ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
      _ ≤ max C₁ C₂ := le_max_left _ _
  · have hK : 0 < clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j :=
      mul_pos (pow_pos ha _) (pow_pos hsq _)
    have hjb : 0 ≤ B0579.jb y ^ ((m + 2) / 2) := by
      apply Real.rpow_nonneg
      unfold B0579.jb
      positivity
    calc B0579.jb y ^ ((m + 2) / 2) * ‖iteratedFDeriv ℝ j (movingTrainE tr r) y‖
        ≤ B0579.jb y ^ ((m + 2) / 2) *
            ((clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j) *
              ‖iteratedFDeriv ℝ j (UnforcedLeray.B0238.Ec tr r)
                (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖) :=
          mul_le_mul_of_nonneg_left (hE1 ν _ hνpos tr r hr j y) hjb
      _ = (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j) *
            (B0579.jb y ^ ((m + 2) / 2) *
              ‖iteratedFDeriv ℝ j (UnforcedLeray.B0238.Ec tr r)
                (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖) := by ring
      _ ≤ (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j) *
            (C₂ * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹) :=
          mul_le_mul_of_nonneg_left (h₂ ν hνb tr hbuc r hr hθ j hj y hy) hK.le
      _ = C₂ := by
          rw [mul_comm C₂, ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
      _ ≤ max C₁ C₂ := le_max_right _ _

end UnforcedLeray.Short.IIIa
