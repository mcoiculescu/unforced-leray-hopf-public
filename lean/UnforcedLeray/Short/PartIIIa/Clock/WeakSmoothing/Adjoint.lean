import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing

/-!
# Part III-a full clock, weak smoothing: the reverse-time adjoint (SP 3044-3075)

Source of record: `the November 2 reference manuscript` (SP).

The moving equation `W_z = G(z)W`, `G = θ⁻¹D + L_{ν,c}(z)`, `D = Δ + ½y·∇ + 2` (SP 2854-2865,
`eq:short-causal-moving`) is the exact substitution `w(s,x) = a⁻² W(z, x/√a)` of the physical
linearised equation of `IsLinearisedFlow` (`Defs.lean`). Its reverse-time adjoint is therefore the
same substitution of the physical adjoint, and we impose the weak formulation in the physical
variables, where the cell `C_c` is fixed (in moving variables the cell length `d(z)` moves,
`d_z/d = -1/(2θ)`, SP 2860):

* `IsKernelBiotSavart`: `u = K_cψ`, the periodic-kernel Biot-Savart velocity of a real test `ψ` of
  ANY circulation (div-free, `curl u = ψ`, and `u` minus the mean shear `-(∫ψ)/(2c) sign(η) e_q` is
  in `L²`; SP 2875-2896, 3052-3057 "including the horizontal mean").
* `adjSpatial`, `adjDt`, `AdjHigherCont`: the words `∂^w` of spatial derivatives, the time derivative
  `∂_rφ` within `[t, s)`, and the regularity `φ ∈ C¹([t, s); H^3_{-m,c})` of the adjoint used by the
  energies `E_1`, `E_2` (SP 3060-3073).
* `adjIntegrand`, `IsAdjointFlow`: the weak reverse-time solution `φ` on `[t, s]` with terminal
  datum `g` of `-∂_rφ = A^*φ`, `A ω = νΔω - v·∇ω - (K_cω)·∇E` (actual train `(v, E)`), tested
  against `ψ ∈ IsCylTest c` through `∫ φ Aψ`; the adjoint of the interaction is the adjoint
  localized interaction `K_c^T(φ∇E)` (pinned by testing also against nonzero-circulation `ψ`, so
  that the constants are exact adjoint solutions, `A^*1 = 0`).
* `movingPhi`, `physAdj`: the moving adjoint `Φ(z(r)) = a⁻¹φ(r, √a·)` on the cell of length
  `d(r) = c/√a`, dual to `W = J_a⁻¹ w` (`∫_{C_d} WΦ = ∫_{C_c} wφ`, SP 3036-3037), and its inverse
  `g = a G(·/√a)` at the terminal age.
* `adjE0`, `adjE1`, `adjE2`, `revE0`, `revE1`, `revE2`: the energies `E_j`, squared
  `p_d`-weighted `H^j_{-m}` (homogeneous) norms, weight `p_d⁻¹ = periodicWeight (-m) d`
  (SP 3044-3047, 3060-3061), as functions of the reverse moving time `ζ = z_s - z`.
* `movingTrainE`, `movingTrainV`: the rescaled actual train `E_mov = a²E(√a·)`, `V = a^{3/2}v(√a·)`,
  the coefficients of `L_{ν,c}(z)` after the substitution (SP 2854-2873, 3050-3051).

Props (each a leaf of `PartIII-a:T21/2`):
* `PeriodicWeightLogBounds` (SP 3044-3050), `RescaledTrainBounds` (SP 2866-2873, 3050-3051),
  `AdjointLocalizedBound` (SP 3052-3058), `AdjointEnergyIneqs` (SP 3060-3071), `AdjointExists`
  (parabolic existence of the adjoint used at SP 3060), `XNormDuality`, `AdjointTerminalBound`,
  `AdjointPairingBound` (SP 3036-3040, 3044, 3074-3075; `AdjointDuality` is their conjunction),
  `AdjointEnergyChain` (the scalar step SP 3072-3073).

The conditional theorem `movingWeakStrong_of` is in `MovingOfAdjoint.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Calculus notation -/

/-- The classical partial derivative `∂_k Φ` of a complex field on the plane (`k = 0`: `∂_{y₁}`,
`k = 1`: `∂_{y₂}`); `B0579.pd` is the real version. -/
def pdCx (k : Fin 2) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ := fderiv ℝ Φ y (B0579.dir k)

/-! ## The kernel Biot-Savart velocity of a test (SP 2875-2896, 3052-3057) -/

/-- The mean shear of circulation `Γ` on `C_c`: `-(Γ/(2c)) sign(η) e_q`, the far field (horizontal
mean) of the periodic Biot-Savart kernel. -/
def meanShear (c Γ : ℝ) (x : ℝ × ℝ) (j : Fin 2) : ℝ :=
  if j = 0 then -(Γ / (2 * c)) * Real.sign x.2 else 0

/-- `u = K_cψ`, the periodic-kernel Biot-Savart velocity of a real field `ψ` of arbitrary
circulation `Γ = ∫_{C_c} ψ`: `div u = 0`, `curl u = ∂_q u_η - ∂_η u_q = ψ` in distributions on
the cylinder, and `u - meanShear c Γ ∈ L²(C_c)` (this pins the horizontal mean; for `Γ = 0` it is
`IsBiotSavart`). -/
def IsKernelBiotSavart (c : ℝ) (ψ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → Fin 2 → ℝ) : Prop :=
  (∀ j, MemLp (fun x => u x j - meanShear c (∫ y in B0579.cell c, ψ y) x j) 2
      (volume.restrict (B0579.cell c))) ∧
  (∀ φ, B0579.IsCylTest c φ →
    ∫ x in B0579.cell c, (u x 0 * B0579.pd 0 φ x + u x 1 * B0579.pd 1 φ x) = 0) ∧
  (∀ φ, B0579.IsCylTest c φ → ∫ x in B0579.cell c, ψ x * φ x =
      ∫ x in B0579.cell c, (u x 0 * B0579.pd 1 φ x - u x 1 * B0579.pd 0 φ x))

/-! ## Higher regularity of the adjoint (SP 3060-3073) -/

/-- The word `∂^w Ψ = ∂_{k₁} ⋯ ∂_{k_n} Ψ` of spatial derivatives of a complex field, `w = [k₁, …, k_n]`
(`pdCx`, so `adjSpatial [] Ψ = Ψ`). -/
def adjSpatial : List (Fin 2) → (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ
  | [], Ψ => Ψ
  | k :: w, Ψ => pdCx k (adjSpatial w Ψ)

/-- The time derivative `∂_rφ(r, x)` of an adjoint on `[t, s)`, taken within `[t, s)` (one-sided at
the age `t`, where the reverse-time evolution ends). -/
def adjDt (t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  derivWithin (fun r' => φ r' x) (Ico t s) r

/-- **`φ ∈ C¹([t, s); H^3_{-m,c})`, `∂_rφ ∈ C([t, s); H^1_{-m,c})`** (SP 3060-3073). The source uses the
weighted energies `E_1`, `E_2` as classical quantities of the reverse time (SP 3060-3073: `E_1' +
β_min E_2 ≤ C_b(E_1 + E_0)` is integrated), so that `r ↦ φ(r)`, `∂_kφ(r)` are differentiable in
`X_{-m,c}`. This is: for every word `w` of at most three spatial derivatives `∂^wφ ∈ C([t, s);
X_{-m,c})`, and for every word of at most one spatial derivative `∂^w∂_rφ ∈ C([t, s); X_{-m,c})`
(`∂_rφ = -νΔφ - v·∇φ + K_c^T(φ∇E)` has two derivatives more than the data, SP 3052-3058). No
`∂_r²φ` is asked: `IsBUCTrain` bounds only the spatial derivatives of `v`. -/
def AdjHigherCont (c m t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∀ r ∈ Ico t s, ∀ w : List (Fin 2),
    (w.length ≤ 3 →
      MemLp (adjSpatial w (φ r)) 2 (B0579.cellMeasure c (-m)) ∧
      Tendsto (fun r' => xNorm c (-m) (adjSpatial w (φ r') - adjSpatial w (φ r)))
        (𝓝[Ico t s] r) (𝓝 0)) ∧
    (w.length ≤ 1 →
      MemLp (adjSpatial w (adjDt t s φ r)) 2 (B0579.cellMeasure c (-m)) ∧
      Tendsto (fun r' => xNorm c (-m)
          (adjSpatial w (adjDt t s φ r') - adjSpatial w (adjDt t s φ r)))
        (𝓝[Ico t s] r) (𝓝 0))

/-! ## The reverse-time adjoint (physical variables) -/

/-- The tested adjoint right-hand side at age `r`: `φ · Aψ = φ (νΔψ - v·∇ψ - (K_cψ)·∇E)`, with
`A` the linearised generator of `IsLinearisedFlow` acting on the real test `ψ` with kernel
velocity `uψ = K_cψ`, so that `∫ φ Aψ = ∫ (A^*φ) ψ`. -/
def adjIntegrand {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℂ) (r : ℝ)
    (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ) (x : ℝ × ℝ) : ℂ :=
  φ x * ((ν * lapP ψ x - (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) -
      (uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
        uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x) : ℝ) : ℂ)

/-- `φ` is a weak reverse-time solution on `[t, s]` in `X_{-m,c}` of the adjoint linearised
vorticity equation `-∂_rφ = A^*φ = νΔφ + v·∇φ - K_c^T(φ∇E)` around the actual train, with terminal
datum `g` at age `s` (SP 3060; the reverse-time adjoint of `eq:short-causal-moving`, SP 2861, in
physical variables). The adjoint is smooth before the terminal age (parabolic smoothing), lies in
`C([t, s); H^1_{-m,c})` there, is `c`-periodic, and is tested against every `ψ ∈ IsCylTest c` (any
circulation) with its kernel velocity `K_cψ`.

`memH1` and `strongContH1` are the regularity behind the energy `E_1` of SP 3060-3071. The source
treats `E_1`, the squared weighted `H^1_{-m}` energy, as a finite function of the reverse time which
satisfies `E_1' + β_min E_2 ≤ C_b(E_1 + E_0)` and is integrated after multiplying by the reverse time
(SP 3067-3073), so it is continuous before the terminal age. By SP 3036-3037, 3044 the moving energy
is a rescaling of the physical one with an equivalent weight, and in physical variables this is
`φ ∈ C([t, s); H^1_{-m,c})`. It is not a consequence of the other fields: on the unbounded cylinder
the joint smoothness gives only local continuity in `(r, x)`, and the tails `|x₂| → ∞` of the
gradient energy are controlled by the energy inequality itself. The statement is one-sided at the
age `t`, where the reverse-time evolution ends. It is proved for weak solutions by the leaf
`AdjointWeakH1Cont` (`Sub/PartIIIa_T21_2_7_2.lean`).

`higherCont` (`AdjHigherCont`) is the regularity of SP 3060-3073 beyond `E_1`: the source uses `E_1'`
and `E_2` as classical quantities, which needs `φ ∈ C¹([t, s); H^3_{-m,c})` (differentiability of
`r ↦ φ(r)`, `∂_kφ(r)` in `X_{-m,c}`, and the product rule for the weighted energies). It is proved
for weak solutions by the leaf `AdjointWeakHigherCont` (`Sub/PartIIIa_T21_2_7_2.lean`), which uses
the weighted jets of the train (`TrainJetsBdd`). -/
structure IsAdjointFlow (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ)
    (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop where
  terminal : φ s =ᵐ[volume.restrict (B0579.cell c)] g
  memX : ∀ r ∈ Icc t s, MemLp (φ r) 2 (B0579.cellMeasure c (-m))
  strongCont : ∀ r ∈ Icc t s,
    Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Icc t s] r) (𝓝 0)
  periodic : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x
  smooth : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ r)
  jointSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)
  memH1 : ∀ r ∈ Ico t s, ∀ k : Fin 2, MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure c (-m))
  strongContH1 : ∀ r ∈ Ico t s, ∀ k : Fin 2,
    Tendsto (fun r' => xNorm c (-m) (pdCx k (φ r') - pdCx k (φ r))) (𝓝[Ico t s] r) (𝓝 0)
  higherCont : AdjHigherCont c m t s φ
  integrable : ∀ ψ uψ, B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ → ∀ r ∈ Icc t s,
    IntegrableOn (adjIntegrand tr (φ r) r ψ uψ) (B0579.cell c)
  timeIntegrable : ∀ ψ uψ, B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
    IntervalIntegrable (fun r => ∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x) volume t s
  weak : ∀ ψ uψ, B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ → ∀ r ∈ Icc t s,
    ∫ x in B0579.cell c, φ r x * (ψ x : ℂ) =
      (∫ x in B0579.cell c, g x * (ψ x : ℂ)) +
        ∫ r' in r..s, ∫ x in B0579.cell c, adjIntegrand tr (φ r') r' ψ uψ x

/-! ## Moving variables (SP 2854-2865, 3036-3037) -/

/-- The moving adjoint `Φ(z(r)) = a⁻¹ φ(r, √a ·)`, `a = a(r)`, on the cell of length
`d(r) = c/√a`; dual to `W = J_a⁻¹ w`: `∫_{C_d} W Φ = ∫_{C_c} w φ`. -/
def movingPhi (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (y : ℝ × ℝ) : ℂ :=
  (((clockA ν r)⁻¹ : ℝ) : ℂ) *
    φ r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)

/-- The physical terminal datum `g(x) = a G(x/√a)` of a moving datum `G` on the cell of length
`c/√a` (so that `movingPhi` of `g` at that age is `G`). -/
def physAdj (a : ℝ) (G : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ((a : ℝ) : ℂ) * G (x.1 / Real.sqrt a, x.2 / Real.sqrt a)

/-- The age at moving time `z`: `r = z/(1-νz)`, the inverse of `z = r/a(r)` (SP 2857). -/
def ageOfZ (ν z : ℝ) : ℝ := z / (1 - ν * z)

/-- The age at reverse moving time `ζ` from the terminal age `s`: `z(r) = z_s - ζ`. -/
def revAge (ν s ζ : ℝ) : ℝ := ageOfZ ν (movingZ ν s - ζ)

/-- The rescaled actual train vorticity `E_mov(r) = J_a⁻¹E(r)`, `E_mov(y) = a² E(r, √a y)`, the
coefficient of the moving interaction `(K_dW)·∇E_mov` in `L_{ν,c}(z)` (SP 2861-2873). -/
def movingTrainE {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (y : ℝ × ℝ) : ℝ :=
  clockA ν r ^ 2 *
    UnforcedLeray.B0238.Ec tr r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)

/-- The rescaled actual train velocity `V(r, y) = a^{3/2} v(r, √a y)`, the transport coefficient
`-V·∇W` of `L_{ν,c}(z)` and the velocity of `movingTrainE` (SP 2861-2873). -/
def movingTrainV {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (y : ℝ × ℝ) :
    Fin 2 → ℝ :=
  fun j => clockA ν r ^ (3 / 2 : ℝ) *
    tr.v r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) j

/-! ## The weighted energies (SP 3044-3047, 3060-3061) -/

/-- `E_0 = ∫_{C_d} p_d⁻¹ |Φ|²` (`p_d⁻¹ = periodicWeight (-m) d`). -/
def adjE0 (d m : ℝ) (Φ : ℝ × ℝ → ℂ) : ℝ :=
  ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖Φ y‖ ^ 2

/-- `E_1 = Σ_k ∫_{C_d} p_d⁻¹ |∂_kΦ|²`. -/
def adjE1 (d m : ℝ) (Φ : ℝ × ℝ → ℂ) : ℝ :=
  ∑ k : Fin 2, ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2

/-- `E_2 = Σ_{k,l} ∫_{C_d} p_d⁻¹ |∂_k∂_lΦ|²`. -/
def adjE2 (d m : ℝ) (Φ : ℝ × ℝ → ℂ) : ℝ :=
  ∑ k : Fin 2, ∑ l : Fin 2,
    ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k (pdCx l Φ) y‖ ^ 2

/-- `E_0(ζ)` of the moving adjoint at reverse moving time `ζ` (age `revAge ν s ζ`, cell
`d = c/√a`). -/
def revE0 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) : ℝ :=
  adjE0 (cellLen c (clockA ν (revAge ν s ζ))) m (movingPhi ν φ (revAge ν s ζ))

/-- `E_1(ζ)` of the moving adjoint. -/
def revE1 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) : ℝ :=
  adjE1 (cellLen c (clockA ν (revAge ν s ζ))) m (movingPhi ν φ (revAge ν s ζ))

/-- `E_2(ζ)` of the moving adjoint. -/
def revE2 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) : ℝ :=
  adjE2 (cellLen c (clockA ν (revAge ν s ζ))) m (movingPhi ν φ (revAge ν s ζ))

theorem periodicWeight_nonneg (m d : ℝ) (y : ℝ × ℝ) : 0 ≤ periodicWeight m d y := by
  unfold periodicWeight
  exact Real.rpow_nonneg (by positivity) _

theorem adjE0_nonneg (d m : ℝ) (Φ : ℝ × ℝ → ℂ) : 0 ≤ adjE0 d m Φ :=
  integral_nonneg fun _ => mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _)

theorem adjE1_nonneg (d m : ℝ) (Φ : ℝ × ℝ → ℂ) : 0 ≤ adjE1 d m Φ :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _)

theorem adjE2_nonneg (d m : ℝ) (Φ : ℝ × ℝ → ℂ) : 0 ≤ adjE2 d m Φ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _)

/-! ## The leaf statements -/

/-- **Log-derivative bounds of the periodic weight** (SP 3044-3050). For every `m` there is `C`
with, for every `d > 0`: `|∂_k log p_d| ≤ C` and `|∂_k∂_l log p_d| ≤ C` on the plane, and on the
cell `|y·∇ log p_d| ≤ C` and `|d ∂_d log p_d| ≤ C`. With `d_z/d = -1/(2θ)` (SP 2860) the last one
is `|∂_z log p_{d(z)}| ≤ C/(2θ)`. -/
def PeriodicWeightLogBounds : Prop :=
  ∀ m : ℝ, ∃ C : ℝ, ∀ d : ℝ, 0 < d →
    (∀ y : ℝ × ℝ, ∀ k : Fin 2,
      |B0579.pd k (fun x => Real.log (periodicWeight m d x)) y| ≤ C) ∧
    (∀ y : ℝ × ℝ, ∀ k l : Fin 2,
      |B0579.pd k (B0579.pd l (fun x => Real.log (periodicWeight m d x))) y| ≤ C) ∧
    (∀ y ∈ B0579.cell d,
      |y.1 * B0579.pd 0 (fun x => Real.log (periodicWeight m d x)) y +
        y.2 * B0579.pd 1 (fun x => Real.log (periodicWeight m d x)) y| ≤ C) ∧
    (∀ y ∈ B0579.cell d, |d * deriv (fun d' => Real.log (periodicWeight m d' y)) d| ≤ C)

/-- **The rescaled train is uniformly bounded** (SP 3050-3051, from the comparison with the
periodized Gaussian in every fixed weighted derivative norm, SP 2866-2873): for `b` large and
`ν` small, on `θ(r) ≥ b`, the rescaled velocity and its first two derivatives are bounded, and
the rescaled vorticity and its first three derivatives are bounded with the weight
`⟨y⟩^{m+2}` on the cell (this gives the weighted Cauchy-Schwarz bounds of SP 3053-3054).
The train is in the BUC class `PartI.IsBUCTrain` (SP 270-288): the comparison with the periodized
Gaussian is a property of the source train, not of an arbitrary `B0140.TrainSol`
(`Short/PartI/TrainClass.lean`); this is the statement `RescaledTrainBoundsBUC` of
`Sub/PartIIIa_T21_2_6.lean`. -/
def RescaledTrainBounds (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r →
      b ≤ clockTheta ν r →
      (∀ j : ℕ, j ≤ 2 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j (movingTrainV tr r) y‖ ≤ C) ∧
      (∀ j : ℕ, j ≤ 3 → ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
        B0579.jb y ^ ((m + 2) / 2) * ‖iteratedFDeriv ℝ j (movingTrainE tr r) y‖ ≤ C)

/-- **The adjoint localized interaction** (SP 3052-3058): for `b` large and `ν` small, on
`θ(r) ≥ b`, every `Φ ∈ X_{-m,d}` (`d = d(r)`) has an adjoint localized interaction
`χ = K_d^T(Φ∇E_mov)`, characterised by `∫ χ ψ = ∫ Φ (K_dψ)·∇E_mov` for every test `ψ` of the
moving cell (any circulation, kernel velocity `K_dψ`), with
`‖χ‖_{H^1_{-m,d}} ≤ C ‖Φ‖_{X_{-m,d}}` uniformly, for BUC trains (`PartI.IsBUCTrain`,
SP 270-288; the localized source is bounded through `RescaledTrainBounds`). -/
def AdjointLocalizedBound (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r →
      b ≤ clockTheta ν r → ∀ Φ : ℝ × ℝ → ℂ,
        MemLp Φ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) →
        ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
          (∀ j, HasWeakCellDerivC (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j χ (gχ j)) ∧
          h1Norm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m χ gχ ≤
            ENNReal.ofReal C * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ ∧
          ∀ ψ uψ, B0579.IsCylTest (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ψ →
            IsKernelBiotSavart (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ψ uψ →
            ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)), χ y * (ψ y : ℂ) =
              ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
                Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
                  uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ)

/-- **The weighted energy inequalities of the reverse-time adjoint** (SP 3060-3071; Reynolds
cancellation of the moving-cell seam, SP 2945-2946, 3062). For `b` large and `ν` small, on
`0 < s - t ≤ 1`, `θ(s) ≥ b`: the moving adjoint of any terminal datum `G ∈ X_{-m,d_s}` has, in the
reverse moving time `ζ ∈ [0, Δz]`, `E_0` continuous on `[0, Δz]`, `E_1` continuous on `(0, Δz]`,
and `E_0' + β_min E_1 ≤ C_b E_0`, `E_1' + β_min E_2 ≤ C_b(E_1 + E_0)` on `(0, Δz)`
(`β_min = ν a_t`).  For BUC trains (`PartI.IsBUCTrain`, SP 270-288): the transport and compact
terms have the coefficient `C_b` through the rescaled-train bounds (SP 3050-3051, 3064-3066). -/
def AdjointEnergyIneqs (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t s : ℝ, 0 ≤ t → t < s → s - t ≤ 1 → b ≤ clockTheta ν s →
        ∀ G : ℝ × ℝ → ℂ,
          MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
          ∀ φ : ℝ → ℝ × ℝ → ℂ,
            IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
            ContinuousOn (revE0 ν (ν ^ (-2 : ℝ)) m φ s) (Icc 0 (deltaZ ν t s)) ∧
            ContinuousOn (revE1 ν (ν ^ (-2 : ℝ)) m φ s) (Ioc 0 (deltaZ ν t s)) ∧
            (∀ ζ ∈ Ioo 0 (deltaZ ν t s), ∃ D : ℝ,
              HasDerivAt (revE0 ν (ν ^ (-2 : ℝ)) m φ s) D ζ ∧
              D + betaMin ν t * revE1 ν (ν ^ (-2 : ℝ)) m φ s ζ ≤
                C * revE0 ν (ν ^ (-2 : ℝ)) m φ s ζ) ∧
            (∀ ζ ∈ Ioo 0 (deltaZ ν t s), ∃ D : ℝ,
              HasDerivAt (revE1 ν (ν ^ (-2 : ℝ)) m φ s) D ζ ∧
              D + betaMin ν t * revE2 ν (ν ^ (-2 : ℝ)) m φ s ζ ≤
                C * (revE1 ν (ν ^ (-2 : ℝ)) m φ s ζ + revE0 ν (ν ^ (-2 : ℝ)) m φ s ζ))

/-- **Existence of the reverse-time adjoint** (used at SP 3060; linear parabolic existence for the
adjoint of the actual linearised operator): for `ν` small and the trains of the BUC class
`PartI.IsBUCTrain` (SP 270-288, 2819-2836: the construction needs `sup |v| < ∞` and the weighted
decay of `∇E` on `[0, s]`, which `B0140.IsTrain` does not give, `Short/PartI/TrainClass.lean`),
every terminal datum `G ∈ X_{-m,d_s}` at age `s` has a weak reverse-time adjoint solution on
`[t, s]`.  (The form of `AdjointWeakExistsBUC`, `Sub/T21_2_7/AdjWeakDefs.lean`, and of
`LinAdjDualityBUC`, `Sub/T21_2_3/LinAdjDualitySub.lean`.) -/
def AdjointExists (m : ℝ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∃ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ

/-- **Duality of `X_{m,d}` and `X_{-m,d}`** under the unweighted pairing (SP 2823-2826, 3074),
applied to `W(z_s) = J_{a_s}⁻¹ w(s)` (which lies in `X_{m,d_s}` by `eq:short-causal-scales`,
SP 3030-3035): `‖W‖_{X_{m,d}} ≤ sup_{‖G‖_{X_{-m,d}} ≤ 1} |∫_{C_d} W G|`. -/
def XNormDuality (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    ∀ t s : ℝ, 0 ≤ t → t ≤ s → ∀ f : ℝ × ℝ → ℂ,
      MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
      ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (JscaleInv (clockA ν s) (w s)) ≤
          ⨆ (G : ℝ × ℝ → ℂ)
            (_ : MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)))
            (_ : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m) G ≤ 1),
            ENNReal.ofReal ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
              JscaleInv (clockA ν s) (w s) y * G y‖

/-- **Terminal energy** (equivalence of `p_d` and `⟨y⟩^{2m}` on the cell, SP 3044): the moving
adjoint at the terminal age (`ζ = 0`, where it equals `G`) has
`E_0(0) ≤ C_m ‖G‖²_{X_{-m,d_s}}`. -/
def AdjointTerminalBound (m : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        revE0 ν (ν ^ (-2 : ℝ)) m φ s 0 ≤
          C * (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m) G).toReal ^ 2

/-- **The duality pairing** (SP 3036-3040, 3044, 3074-3075): for the weak linearised flow `w`
from a zero-circulation `f` at age `t` and the reverse-time adjoint `φ` with terminal datum
`physAdj a_s G`, `∫_{C_{d_s}} W(z_s) G = ∫_{C_c} w(s) g = ∫_{C_c} f φ(t) = ∫_{C_{d_t}} J_{a_t}⁻¹f Φ(z_t)`,
hence `|∫ W(z_s) G| ≤ ‖J_{a_t}⁻¹f‖_{(H^1_{-m,d_t})^*} ‖Φ(z_t)‖_{H^1_{-m,d_t}}
≤ ‖J_{a_t}⁻¹f‖_{(H^1_{-m,d_t})^*} C_m (E_0 + E_1)^{1/2}(Δz)` (`ζ = Δz` is the age `t`).
For `ν ≤ ν₀` and the trains of the BUC class `PartI.IsBUCTrain` (SP 270-288): the middle
equality is the weak duality `LinAdjDualityBUC` (`Sub/T21_2_3/LinAdjDualitySub.lean`), which needs
`sup |v| < ∞` and the weighted decay of `∇E` on the whole cell (the cutoff commutator and the
interaction `∫ (K_cw·∇E)φ`, `φ ∈ X_{-m}`), not given by `B0140.IsTrain`
(`Short/PartI/TrainClass.lean`). -/
def AdjointPairingBound (m : ℝ) : Prop :=
  ∃ (C ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
            ENNReal.ofReal ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
                JscaleInv (clockA ν s) (w s) y * G y‖ ≤
              negNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (JscaleInv (clockA ν t) f) *
                ENNReal.ofReal (C * Real.sqrt (revE0 ν (ν ^ (-2 : ℝ)) m φ s (deltaZ ν t s) +
                  revE1 ν (ν ^ (-2 : ℝ)) m φ s (deltaZ ν t s)))

/-- **Duality** (SP 3036-3040, 3044, 3074-3075): the three duality facts consumed by the moving
weak-to-strong bound (`XNormDuality`, `AdjointTerminalBound` hold for every train; the pairing
bound is the BUC `∃ ν₀` form). -/
def AdjointDuality (m : ℝ) : Prop :=
  XNormDuality m ∧ AdjointTerminalBound m ∧ AdjointPairingBound m

/-- **The scalar energy chain** (SP 3072-3073): "integrate the first inequality and then the
inequality for `rE_1(r)`". For `0 < β ≤ 1`, `0 < Δ ≤ 1`, nonnegative `E_0` continuous on `[0, Δ]`,
`E_1` continuous on `(0, Δ]` (it may blow up at the terminal time `0`), with
`E_0' + βE_1 ≤ CE_0` and `E_1' + βE_2 ≤ C(E_1 + E_0)` on `(0, Δ)`:
`E_0(Δ) ≤ K E_0(0)` and `E_1(Δ) ≤ K (βΔ)⁻¹ E_0(0)`, `K = K(C)`. (`β ≤ 1` is
`β_min ≤ θ(s)⁻¹ ≤ b⁻¹`; it absorbs the term `CΔ²E_0(0)` into `(βΔ)⁻¹E_0(0)`.) -/
def AdjointEnergyChain : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ K : ℝ, 0 ≤ K ∧ ∀ β Δ : ℝ, 0 < β → β ≤ 1 → 0 < Δ → Δ ≤ 1 →
    ∀ e₀ e₁ e₂ : ℝ → ℝ, ContinuousOn e₀ (Icc 0 Δ) → ContinuousOn e₁ (Ioc 0 Δ) →
      (∀ ζ ∈ Icc 0 Δ, 0 ≤ e₀ ζ) → (∀ ζ ∈ Ioc 0 Δ, 0 ≤ e₁ ζ) → (∀ ζ ∈ Ioo 0 Δ, 0 ≤ e₂ ζ) →
      (∀ ζ ∈ Ioo 0 Δ, ∃ D : ℝ, HasDerivAt e₀ D ζ ∧ D + β * e₁ ζ ≤ C * e₀ ζ) →
      (∀ ζ ∈ Ioo 0 Δ, ∃ D : ℝ, HasDerivAt e₁ D ζ ∧ D + β * e₂ ζ ≤ C * (e₁ ζ + e₀ ζ)) →
      e₀ Δ ≤ K * e₀ 0 ∧ e₁ Δ ≤ K * (β * Δ)⁻¹ * e₀ 0

end UnforcedLeray.Short.IIIa
