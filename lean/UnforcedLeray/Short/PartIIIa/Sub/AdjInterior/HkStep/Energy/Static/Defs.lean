import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: the static energy inequality (vocabulary and leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
("Reynolds cancellation and differentiated weighted energy give `E_0' + β E_1 ≤ C E_0`,
`E_1' + β E_2 ≤ C (E_1 + E_0)`; the diffusion-weight errors have coefficient `C_m β` and the
transport and compact terms have coefficient `C_b`"), 3044-3050 (the weight and its logarithmic
derivatives, `AdjWeightGrad`, proved: `adjWeightGrad`), 3052-3058 (the adjoint localized
interaction is of order `-1`; here it enters only through the given jet `Dχ` of `χ`).

The target is `StaticMollEnergy m` (`Energy/Defs.lean`): at one age, for `G = ρ_n ⋆ φ`,
`-energyRate c m j G (mollRate ν v n φ χ) + β N_{j+1}(G) ≤ C (N_j(G) + M²)` uniformly in `n`.

## Route

`mollRate ν v n φ χ = -(ν ΔG + T - ρ_n ⋆ χ)` with `ΔG = stLap G` and the transport term
`T = stTrans v n φ = Σ_l (∂_lρ_n) ⋆ (v_l φ)` (`mollRate_eq_st`, `rfl`).  For a word `w`,
`|w| ≤ j ≤ k + 1`, and `F = ∂^w G`:
* diffusion (`Assembly.lean`): `∂^w ΔG = Δ ∂^w G` (`StAdjComm`), and the weighted integration by
  parts `StCellIbp` with `H = ∂_l F` gives `⟨F, ∂_l∂_l F⟩ ≤ -‖∂_lF‖² + 2|m| ‖F‖ ‖∂_lF‖`
  (the diffusion-weight error of SP 3067-3068);
* the compact term: `∂^w(ρ_n ⋆ χ) = ρ_n ⋆ Dχ w` (`st_adjSpatial_cellMoll_jet`), bounded by
  `CellMollBound`;
* transport (`StTransWord`, `Transport.lean`): `T = v·∇G + R` with the Friedrichs remainder
  `R = stFriedRem v n φ`; `⟨F, v·∇F⟩` is bounded by `‖F‖²` (Reynolds cancellation, `StReynolds`), the
  commutator `∂^w(v·∇G) - v·∇∂^wG` is of order `|w|` (`StTransComm`, `Comm.lean`), and
  `‖∂^u R‖ ≤ C M` for `|u| ≤ k` uniformly in `n` (`StFriedJet`, `Fried.lean`, from the level-zero
  bound `StFriedZero` (`FriedZero.lean`: `StFriedPointwise`, the moment bound `StMolMoment`,
  `CellConvBound`), the derivation rule `StFriedDeriv` (`FriedDeriv.lean`) and the word Leibniz
  rule `st_word_leibniz` of `Algebra.lean`); for `|w| = k + 1` one derivative of `∂^w R` is moved
  onto `F` by `StCellIbp`;
* the algebra (`Assembly.lean`): Young's inequality absorbs the first-order terms, each word of
  length `1..j+1` is `l :: w'` with `|w'| ≤ j` exactly once, so `Σ_{|w| ≤ j} ‖∇∂^wG‖² = N_{j+1} - N_0`,
  and `β = ν`.
`Of.lean` composes everything: `staticMollEnergy_of_leaves` (the six leaves `(1)`-`(6)` below and
the shared mollifier leaves of `HkStep/Shared.lean`, with `KTWeakLeibniz`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Vocabulary -/

/-- `ΔF = ∂₀∂₀F + ∂₁∂₁F`: the diffusion part of `mollRate`. -/
def stLap (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => adjSpatial [0, 0] F x + adjSpatial [1, 1] F x

/-- The coefficient fields of a slice velocity: `stVel v l x = v(x)_l`. -/
def stVel (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℝ × ℝ → ℝ :=
  fun l x => v x l

/-- `a·∇F = Σ_l a_l ∂_l F` for real coefficient fields `a_l` (with `a = stVel v`: the transport
`v·∇F`). -/
def stGrad (a : Fin 2 → ℝ × ℝ → ℝ) (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => ∑ l : Fin 2, ((a l x : ℝ) : ℂ) * pdCx l F x

/-- The transport part of `mollRate`: `∇·(ρ_n ⋆ (vφ)) = Σ_l (∂_lρ_n) ⋆ (v_l φ)`. -/
def stTrans (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (n : ℕ) (φ : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => ∑ l : Fin 2, cellConv (B0579.pd l (molKer n)) (fun y => ((v y l : ℝ) : ℂ) * φ y) x

theorem mollRate_eq_st (ν : ℝ) (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (n : ℕ)
    (φ χ : ℝ × ℝ → ℂ) :
    mollRate ν v n φ χ = fun x =>
      -((ν : ℂ) * stLap (cellMoll n φ) x + stTrans v n φ x - cellMoll n χ x) := rfl

/-- The Friedrichs remainder `R_n = ∇·(ρ_n ⋆ (vφ)) - v·∇(ρ_n ⋆ φ)`. -/
def stFriedRem (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (n : ℕ) (φ : ℝ × ℝ → ℂ) :
    ℝ × ℝ → ℂ :=
  fun x => stTrans v n φ x - stGrad (stVel v) (cellMoll n φ) x

/-- The Friedrichs commutator with real coefficient fields `a`:
`Σ_l [(∂_lρ_n) ⋆ (a_l f) - a_l ((∂_lρ_n) ⋆ f)]`, pointwise
`∫ Σ_l ∂_lρ_n(y) (a_l(x - y) - a_l(x)) f(x - y) dy`. -/
def stFried (n : ℕ) (a : Fin 2 → ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => ∑ l : Fin 2,
    (cellConv (B0579.pd l (molKer n)) (fun y => ((a l y : ℝ) : ℂ) * f y) x -
      ((a l x : ℝ) : ℂ) * cellConv (B0579.pd l (molKer n)) f x)

/-- The derivative word `∂^u a` of real coefficient fields, componentwise (`pdWordR`). -/
def stCoefWord (u : List (Fin 2)) (a : Fin 2 → ℝ × ℝ → ℝ) : Fin 2 → ℝ × ℝ → ℝ :=
  fun l => pdWordR u (a l)

/-- The Leibniz splittings of a word: `∂_j` of `B(∂^{p.1}a, ∂^{p.2}f)` gives the two splittings
`(p.1, j :: p.2)` and `(j :: p.1, p.2)`; the first splitting of `w` is `([], w)` (`2^|w|` in all,
with multiplicity). -/
def stSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2))
  | [] => [([], [])]
  | j :: w => (stSplits w).flatMap fun p => [(p.1, j :: p.2), (j :: p.1, p.2)]

/-! ## The leaves (task ids `PartIII-a:T21/2/7/2/1/1/5/18/2/<k>`) -/

/-- **(1) Mixed partials of smooth fields commute** (calculus; SP 3060-3071 differentiate the
equation: `∂^w` commutes with `Δ` and with `∂_l`).  For a smooth complex field `F`,
`∂^w ∂_l F = ∂_l ∂^w F`.  Proof: induction on `w`; the step is
`pdCx k (pdCx l H) = pdCx l (pdCx k H)` for the smooth `H = adjSpatial w F`:
`pdCx k (pdCx l H) y = fderiv ℝ (fderiv ℝ H) y (dir k) (dir l)` (`fderiv_clm_apply`), and the second
derivative of a `C²` map is symmetric (`ContDiffAt.isSymmSndFDerivAt`, `minSmoothness_le_ofNat` /
`le_rfl` for `ℝ`). -/
def StAdjComm : Prop :=
  ∀ (F : ℝ × ℝ → ℂ), ContDiff ℝ ∞ F → ∀ (w : List (Fin 2)) (l : Fin 2),
    adjSpatial w (pdCx l F) = pdCx l (adjSpatial w F)

/-- **(2) Weighted integration by parts on the cell** (SP 3044-3050, 3067-3068: the
diffusion-weight errors through the logarithmic derivatives of the weight).  For smooth
`c`-periodic `F, H` with `F, H, ∂_l F, ∂_l H ∈ X_{-m,c}`:
`|Re⟨F, ∂_l H⟩ + Re⟨∂_l F, H⟩| ≤ 2|m| ‖F‖ ‖H‖` (`ipX`, `xNorm`).  Proof: with `w = jb^{-m}` (the
density of `cellMeasure c (-m)`, `integral_withDensity_eq_integral_smul`) and `Φ = w F H̄`,
`∂_lΦ = (∂_l w) F H̄ + w ∂_lF H̄ + w F conj(∂_l H)` (product rule, `pdCx` of `conj ∘ H` is
`conj ∘ pdCx H`); `∫_{C_c} ∂_lΦ = 0`: for `l = 0` by `UnforcedLeray.Cyl.integral_cell_deriv_q`
(`Lib/Cylinder/IBP.lean`) with the seam term `Φ(c/2, η) - Φ(-c/2, η) = 0` (`F`, `H` periodic,
`jb(c/2, η) = jb(-c/2, η)`), for `l = 1` by `UnforcedLeray.Cyl.integral_cell_deriv_eta` (`Φ` and
`∂_1Φ` integrable on the cell: products of two `X_{-m,c}` fields with the weight, and
`|∂_l w| ≤ 2|m| w`, `adjWeightGrad`, `Sub/T21_2_7/WeightGrad.lean`); take real parts and bound
`|∫ (∂_l w) F H̄| ≤ 2|m| ∫ w |F||H| ≤ 2|m| ‖F‖ ‖H‖` (Hölder, `integral_mul_le_Lp_mul_Lq_of_nonneg`).
The same computation is the core of `CellInterpSmooth` (`HkStep/Defs.lean`). -/
def StCellIbp : Prop :=
  ∀ (c m : ℝ) (l : Fin 2) (F H : ℝ × ℝ → ℂ), 0 < c → ContDiff ℝ ∞ F → ContDiff ℝ ∞ H →
    (∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x) → (∀ x : ℝ × ℝ, H (x.1 + c, x.2) = H x) →
    MemLp F 2 (B0579.cellMeasure c (-m)) → MemLp H 2 (B0579.cellMeasure c (-m)) →
    MemLp (pdCx l F) 2 (B0579.cellMeasure c (-m)) →
    MemLp (pdCx l H) 2 (B0579.cellMeasure c (-m)) →
    |ipX c m F (pdCx l H) + ipX c m (pdCx l F) H| ≤
      2 * |m| * (xNorm c (-m) F).toReal * (xNorm c (-m) H).toReal

/-- **(3) Reynolds cancellation of the transport term** (SP 3062-3064: "Reynolds cancellation";
`div v = 0`, SP 270-288).  For a slice velocity `v` (`SliceVel`: smooth, periodic, divergence free,
`‖v‖ ≤ Av 0`) and a smooth periodic `F` with all partials in `X_{-m,c}`:
`|Re⟨F, v·∇F⟩| ≤ 2|m| Av 0 ‖F‖²`.  Proof: `Re(F conj(v_l∂_lF)) = ½ v_l ∂_l|F|²`, so
`2 Re⟨F, v·∇F⟩ = Σ_l [Re⟨F, ∂_l(v_l F)⟩ + Re⟨∂_lF, v_l F⟩]` (`∂_l(v_lF) = (∂_lv_l)F + v_l∂_lF`,
`Σ_l ∂_l v_l = divergence v = 0`: `Cyl.partialQ_eq_fderiv`, `Cyl.partialEta_eq_fderiv`; and
`Σ_l Re⟨∂_lF, v_lF⟩ = Re⟨v·∇F, F⟩ = Re⟨F, v·∇F⟩`); each bracket is bounded by
`2|m| ‖F‖ ‖v_lF‖ ≤ 2|m| Av 0 ‖F‖²` by `StCellIbp` with `H = v_l F` (`|v_l| ≤ ‖v‖ ≤ Av 0`,
`norm_iteratedFDeriv_zero`; `∂_l(v_lF) ∈ X` since `|∂_l v_l| ≤ Av 1`). -/
def StReynolds : Prop :=
  ∀ (c m : ℝ) (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (Av : ℕ → ℝ) (F : ℝ × ℝ → ℂ), 0 < c →
    SliceVel c v Av → ContDiff ℝ ∞ F → (∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x) →
    (∀ w : List (Fin 2), MemLp (adjSpatial w F) 2 (B0579.cellMeasure c (-m))) →
    |ipX c m F (stGrad (stVel v) F)| ≤ 2 * |m| * Av 0 * (xNorm c (-m) F).toReal ^ 2

/-- **(4) Derivative words of the slice velocity** (calculus; SP 270-288, 2866-2870: every
derivative of the train is bounded).  For `SliceVel c v Av`, every `∂^u v_l` (`pdWordR u (stVel v l)`)
is smooth, `c`-periodic, bounded by `Av |u|` and `Av (|u| + 1)`-Lipschitz (sup norm of `ℝ × ℝ`).
Proof: `pdWordR u f x = iteratedFDeriv ℝ |u| f x (fun i => B0579.dir (u.get i))` (induction:
`iteratedFDeriv_succ_apply_left`, `fderiv` of the evaluation of a multilinear map at fixed vectors),
`‖B0579.dir j‖ = 1`, so `|pdWordR u f x| ≤ ‖iteratedFDeriv ℝ |u| f x‖`
(`ContinuousMultilinearMap.le_opNorm`), and `‖iteratedFDeriv ℝ i (stVel v l) x‖ ≤
‖iteratedFDeriv ℝ i v x‖` (`stVel v l = EuclideanSpace.proj l ∘ v`,
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left`, `‖proj l‖ ≤ 1`); the same for `fderiv` of
`pdWordR u f` (`norm_fderiv_iteratedFDeriv`), and the mean value inequality
(`Convex.norm_image_sub_le_of_norm_fderiv_le` on `univ`).  Periodicity: translation commutes with
`fderiv` (`fderiv_comp_add_right`). -/
def StVelWords : Prop :=
  ∀ (c : ℝ) (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (Av : ℕ → ℝ), SliceVel c v Av →
    ∀ (u : List (Fin 2)) (l : Fin 2),
      ContDiff ℝ ∞ (pdWordR u (stVel v l)) ∧
      (∀ x : ℝ × ℝ, pdWordR u (stVel v l) (x.1 + c, x.2) = pdWordR u (stVel v l) x) ∧
      (∀ x : ℝ × ℝ, |pdWordR u (stVel v l) x| ≤ Av u.length) ∧
      ∀ x y : ℝ × ℝ, |pdWordR u (stVel v l) x - pdWordR u (stVel v l) y| ≤
        Av (u.length + 1) * ‖x - y‖

/-- **(5) The first moment of `∇ρ_n` is bounded uniformly in `n`** (the scaling of the mollifier;
Friedrichs' lemma).  Every `∂_l ρ_n` is continuous, vanishes outside the closed unit ball, and
`∫ |∂_lρ_n(y)| ‖y‖ dy ≤ C` with `C` independent of `n`.  Proof: continuity from
`ContDiffBump.contDiff_normed`; `ρ_n` vanishes on the open set `{‖y‖ > 1/(n+1)}`
(`ContDiffBump.support_normed_eq`: the support is `ball 0 (1/(n+1))`), so does its derivative
(`Filter.EventuallyEq.fderiv_eq`).  Moment: `molBump n x = molBump 0 ((n + 1) • x)` (unfold the
coercion of `ContDiffBump` to `ContDiffBump.toFun`: both have `rOut / rIn = 2`, and
`(molBump n).rIn⁻¹ = 2 (n + 1)`), hence `molKer n x = (n + 1)² molKer 0 ((n + 1) • x)`
(`ContDiffBump.normed_def`, `MeasureTheory.Measure.integral_comp_smul`, `finrank ℝ (ℝ × ℝ) = 2`), so
`∂_l molKer n x = (n + 1)³ (∂_l molKer 0)((n + 1) • x)` and the substitution `y ↦ (n + 1) • y` gives
`∫ |∂_l molKer n y| ‖y‖ dy = ∫ |∂_l molKer 0 z| ‖z‖ dz`, finite (continuous with compact support,
`ContDiffBump.hasCompactSupport_normed`, `HasCompactSupport.fderiv_apply`). -/
def StMolMoment : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (l : Fin 2),
    Continuous (B0579.pd l (molKer n)) ∧
    (∀ y : ℝ × ℝ, 1 < ‖y‖ → B0579.pd l (molKer n) y = 0) ∧
    Integrable (fun y : ℝ × ℝ => |B0579.pd l (molKer n) y| * ‖y‖) ∧
      ∫ y : ℝ × ℝ, |B0579.pd l (molKer n) y| * ‖y‖ ≤ C

/-- **(6) Friedrichs' commutator, pointwise** (the regularization of SP 3060-3071; the transport term
of the mollified equation is `v·∇(ρ_n ⋆ φ)` up to a remainder of order zero).  For continuous,
bounded, `L`-Lipschitz coefficient fields `a_l` and a `c`-periodic `f ∈ X_{-m,c}`: `stFried n a f` is
continuous and `|stFried n a f x| ≤ L |(K_n ⋆ |f|)(x)|` with `K_n(y) = Σ_l |∂_lρ_n(y)| ‖y‖`.  Proof:
`f` is locally integrable on the plane (`CellPeriodicLocInt`), so
`y ↦ ∂_lρ_n(y) a_l(x - y) f(x - y)` and `y ↦ ∂_lρ_n(y) f(x - y)` are integrable
(`HasCompactSupport.convolutionExists_left` with `cellConv_eq_convolution`; `∂_lρ_n` continuous with
compact support: `ContDiffBump.contDiff_normed`, `hasCompactSupport_normed`,
`HasCompactSupport.fderiv_apply`), and `stFried n a f x = Σ_l ∫ ∂_lρ_n(y) (a_l(x - y) - a_l(x))
f(x - y) dy` (`integral_sub`, `integral_mul_left`); bound the integrand by
`|∂_lρ_n(y)| L ‖y‖ |f(x - y)|` (`norm_integral_le_integral_norm`, `integral_mono`) and note
`K_n ⋆ |f|` is the real nonnegative `∫ K_n(y) |f(x - y)| dy` (`integral_ofReal`).  Continuity:
`HasCompactSupport.continuous_convolution_left`. -/
def StFriedPointwise : Prop :=
  ∀ (c m : ℝ) (n : ℕ) (a : Fin 2 → ℝ × ℝ → ℝ) (A L : ℝ) (f : ℝ × ℝ → ℂ), 0 < c →
    (∀ l, Continuous (a l)) → (∀ l (x : ℝ × ℝ), |a l x| ≤ A) →
    (∀ l (x y : ℝ × ℝ), |a l x - a l y| ≤ L * ‖x - y‖) →
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → MemLp f 2 (B0579.cellMeasure c (-m)) →
    Continuous (stFried n a f) ∧
      ∀ x : ℝ × ℝ, ‖stFried n a f x‖ ≤
        L * ‖cellConv (fun y => ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖)
          (fun y => ((‖f y‖ : ℝ) : ℂ)) x‖

/-! ## Intermediate statements (proved from the leaves) -/

/-- **Friedrichs' commutator at level zero** (proved: `stFriedZero_of`, `FriedZero.lean`, from
`StFriedPointwise`, `StMolMoment` and `CellConvBound`).  There is
`C = C(c, m)` such that for every `n`, coefficient fields `a_l` continuous, bounded and
`L`-Lipschitz, and every `c`-periodic `f ∈ X_{-m,c}`: `stFried n a f ∈ X_{-m,c}` and
`‖stFried n a f‖ ≤ C L ‖f‖`.  (`K_n = Σ_l |∂_lρ_n| ‖·‖` is continuous, vanishes outside the unit
ball, `∫ K_n ≤ 2 C_mom`; `CellConvBound` for `K_n ⋆ |f|`.) -/
def StFriedZero : Prop :=
  ∀ c m : ℝ, 0 < c → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : ℕ) (a : Fin 2 → ℝ × ℝ → ℝ) (A L : ℝ) (f : ℝ × ℝ → ℂ),
      (∀ l, Continuous (a l)) → (∀ l (x : ℝ × ℝ), |a l x| ≤ A) →
      (∀ l (x y : ℝ × ℝ), |a l x - a l y| ≤ L * ‖x - y‖) →
      (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → MemLp f 2 (B0579.cellMeasure c (-m)) →
      MemLp (stFried n a f) 2 (B0579.cellMeasure c (-m)) ∧
        (xNorm c (-m) (stFried n a f)).toReal ≤ C * L * (xNorm c (-m) f).toReal

/-- **The derivation rule of the Friedrichs commutator** (proved: `stFriedDeriv_of`,
`FriedDeriv.lean`).
For smooth `c`-periodic coefficient fields `a_l` with `a_l` and `∂_j a_l` bounded and a
`c`-periodic `f ∈ X_{-m,c}`: `stFried n a f` is smooth, and if `g = ∂_j f` weakly
(`HasWeakCellDerivC`, `g` periodic in `X_{-m,c}`) then
`∂_j (stFried n a f) = stFried n (∂_j a) f + stFried n a g`.  Proof: `(∂_lρ_n) ⋆ h = ∂_l(ρ_n ⋆ h)`
(`CellConvDeriv` with the word `[l]`; `molKer n` smooth with compact support:
`ContDiffBump.contDiff_normed`, `hasCompactSupport_normed`); `∂_j∂_l(ρ_n ⋆ h) = ∂_l∂_j(ρ_n ⋆ h)`
(`StAdjComm`) `= ∂_l(ρ_n ⋆ ∂_jh)` (`CellMollWeakDeriv`) for `h = f` and for `h = a_l f` with
`∂_j(a_l f) = a_l g + (∂_ja_l) f` (`KTWeakLeibniz`, `HkStep/KT/Defs.lean`); `ρ_n ⋆` is additive on
periodic fields of `X_{-m,c}` (`integral_add`, `CellPeriodicLocInt`), the product rule for
`a_l · ((∂_lρ_n) ⋆ f)`, and smoothness from `CellConvDeriv` / `CellMollSmooth`. -/
def StFriedDeriv : Prop :=
  ∀ (c m : ℝ) (n : ℕ) (a : Fin 2 → ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ), 0 < c →
    (∀ l, ContDiff ℝ ∞ (a l)) → (∀ l (x : ℝ × ℝ), a l (x.1 + c, x.2) = a l x) →
    (∃ A : ℝ, ∀ l (x : ℝ × ℝ), |a l x| ≤ A ∧ ∀ j : Fin 2, |B0579.pd j (a l) x| ≤ A) →
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → MemLp f 2 (B0579.cellMeasure c (-m)) →
    ContDiff ℝ ∞ (stFried n a f) ∧
      ∀ (j : Fin 2) (g : ℝ × ℝ → ℂ), (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) →
        MemLp g 2 (B0579.cellMeasure c (-m)) → HasWeakCellDerivC c j f g →
        pdCx j (stFried n a f) = fun x =>
          stFried n (fun l => B0579.pd j (a l)) f x + stFried n a g x

/-- **The commutator of `∂^w` with the transport is of order `|w|`** (proved: `stTransComm_of`,
`Comm.lean`; Leibniz; SP 3060-3071:
"differentiated weighted energy").  For `SliceVel c v Av` and a smooth `G` with all partials in
`X_{-m,c}`, for `|w| ≤ k`: `∂^w(v·∇G) - v·∇∂^wG ∈ X_{-m,c}` with norm
`≤ C Σ_{|u| ≤ |w|} ‖∂^uG‖`, `C = C(k, Av)`.  Proof: the derivation rule
`∂_j(a·∇H) = (∂_ja)·∇H + a·∇(∂_jH)` (product rule and `StAdjComm` for `∂_j∂_lH = ∂_l∂_jH`) and
`st_word_leibniz` (`Algebra.lean`, with `B = stGrad`, `D u = adjSpatial u G`) give
`∂^w(v·∇G) = Σ_{p ∈ stSplits w} (∂^{p.1}v)·∇(∂^{p.2}G)`; the head splitting `([], w)` is `v·∇∂^wG`
(`st_splits_cons_head`), the others have `|p.1| ≥ 1`, so `∂_l∂^{p.2}G = ∂^{l :: p.2}G` is a word of
length `≤ |w|`; bound each term by `StVelWords` (`|∂^{p.1}v_l| ≤ Av |p.1|`). -/
def StTransComm : Prop :=
  ∀ (c m : ℝ) (k : ℕ) (Av : ℕ → ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)), SliceVel c v Av →
    ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ ∞ G →
    (∀ w : List (Fin 2), MemLp (adjSpatial w G) 2 (B0579.cellMeasure c (-m))) →
    ∀ w : List (Fin 2), w.length ≤ k →
      MemLp (fun x => adjSpatial w (stGrad (stVel v) G) x - stGrad (stVel v) (adjSpatial w G) x) 2
          (B0579.cellMeasure c (-m)) ∧
        (xNorm c (-m) (fun x => adjSpatial w (stGrad (stVel v) G) x -
            stGrad (stVel v) (adjSpatial w G) x)).toReal ≤
          C * ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal

/-- **Friedrichs' lemma at every level `≤ k`** (proved: `stFriedJet_of`, `Fried.lean`).  For
`SliceVel c v Av` and a level-`k` jet `D` of `φ` bounded by `M ≥ 0`: for every `n` and `|u| ≤ k`,
`∂^u R_n ∈ X_{-m,c}` with `‖∂^u R_n‖ ≤ C M`, `R_n = stFriedRem v n φ`, `C = C(c, m, k, Av)`. -/
def StFriedJet : Prop :=
  ∀ (c m : ℝ) (k : ℕ) (Av : ℕ → ℝ), 0 < c → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)), SliceVel c v Av →
    ∀ (φ : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (M : ℝ), 0 ≤ M → IsCellJet c m k φ D →
    (∀ w : List (Fin 2), w.length ≤ k → xNorm c (-m) (D w) ≤ ENNReal.ofReal M) →
    ∀ (n : ℕ) (u : List (Fin 2)), u.length ≤ k →
      MemLp (adjSpatial u (stFriedRem v n φ)) 2 (B0579.cellMeasure c (-m)) ∧
        (xNorm c (-m) (adjSpatial u (stFriedRem v n φ))).toReal ≤ C * M

/-- **The transport term, word by word** (proved: `stTransWord_of`, `Transport.lean`; SP 3062-3066
"Reynolds cancellation", the transport terms with coefficient `C_b`).  For `SliceVel c v Av`, a
level-`k` jet `D` of `φ` bounded by `M ≥ 0`, `G = ρ_n ⋆ φ` and `|w| ≤ k + 1`:
`2 Re⟨∂^wG, ∂^w T⟩ ≤ C (N_{|w|}(G) + M²) + C M Σ_l ‖∂_l∂^wG‖`, `T = stTrans v n φ`,
`C = C(c, m, k, Av)` independent of `n`. -/
def StTransWord : Prop :=
  ∀ (c m : ℝ) (k : ℕ) (Av : ℕ → ℝ), 0 < c → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)), SliceVel c v Av →
    ∀ (φ : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (M : ℝ), 0 ≤ M → IsCellJet c m k φ D →
    (∀ w : List (Fin 2), w.length ≤ k → xNorm c (-m) (D w) ≤ ENNReal.ofReal M) →
    ∀ (n : ℕ) (w : List (Fin 2)), w.length ≤ k + 1 →
      2 * ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stTrans v n φ)) ≤
        C * (cellEnergy c m w.length (cellMoll n φ) + M ^ 2) +
          C * M * ∑ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal

end UnforcedLeray.Short.IIIa
