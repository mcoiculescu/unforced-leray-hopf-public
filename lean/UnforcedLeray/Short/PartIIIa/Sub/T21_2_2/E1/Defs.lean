import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Part III-a, `PartIII-a:T21/2/2/3`: the `E_1` inequality of the reverse-time adjoint, the leaves

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
(`E_1' + β_min E_2 ≤ C_b(E_1 + E_0)`), with the moving equation and `d_z/d = -1/(2θ)` at
2854-2865 (`eq:short-causal-moving`), the Reynolds cancellation of the dilation seam at 2945-2957,
the duality `J_a` at 3029-3037, the periodic weight at 3044-3047, the rescaled-train bounds at
3050-3051 and the adjoint localized interaction at 3052-3058.

## The computation (SP 3060-3071 made explicit)

At reverse moving time `ζ ∈ (0, Δz)` put `r = revAge ν s ζ ∈ (t, s)`, `a = a(r)`,
`β = θ(r)⁻¹ = ν a`, `d = c/√a`, `Φ = movingPhi ν φ r` (`mvPhi`), `w = p_d⁻¹ = periodicWeight (-m) d`,
`V = movingTrainV tr r`, `E_mov = movingTrainE tr r`.

1. *Classical moving adjoint equation* (`MovAdjEquation`; SP 2858-2862 with `D^# = Δ - ½y·∇ + 1`,
   SP 2909-2911, and the adjoint interaction of SP 3052-3058): `∂_ζΦ = β(ΔΦ - ½y·∇Φ + Φ) + V·∇Φ - χ`,
   `χ = K_d^T(Φ∇E_mov)` (`IsAdjInteraction`). Derived from `IsAdjointFlow.weak` and `jointSmooth`
   by `dr/dζ = -a²`, `x = √a y`.
2. *Differentiated weighted energy with Reynolds cancellation* (`E1MovingDeriv`; SP 2860,
   2945-2957, 3062): on the moving cell `C_{d(ζ)}`, `d_ζ = dβ/2`. Differentiating
   `E_1 = Σ_k ∫_{C_d} w|∂_kΦ|²` gives Reynolds' boundary term `d_ζ Σ_k ∫_ℝ w|∂_kΦ|²(d/2, η) dη`; the
   dilation part `-(β/2)y·∇∂_kΦ` of `∂_ζ∂_kΦ`, integrated by parts on the cell, gives
   `(β/2)∫(2w + y·∇w)|∂_kΦ|²` and the seam term `-(βd/2)Σ_k ∫_ℝ w|∂_kΦ|²(d/2, η) dη`, which cancels
   Reynolds' term. The remaining part of `∂_ζ∂_kΦ` is `xiRed`. The result is `e1Rate`.
3. *Integrations by parts on the periodic cell* (`E1DiffusionIBP`, `E1TransportIBP`; no seam terms:
   all factors are `d`-periodic): diffusion `∫ w Re(conj Φ_k ΔΦ_k) = -Σ_l ∫ w|∂_lΦ_k|² - Σ_l ∫ ∂_lw
   Re(conj Φ_k ∂_lΦ_k)` and transport `2∫ w Re(conj Φ_k V·∇Φ_k) = -∫(V·∇w + w div V)|Φ_k|²`.
4. *Bounds* (`E1RemainderBound`, `AdjChiDerivBound`): with `|∇ log w|, |y·∇ log w|, |d∂_d log w| ≤ C_m`
   (`PeriodicWeightLogBounds`), `|V|, |∇V| ≤ C_b` (`RescaledTrainBounds`) and
   `Σ_k ∫ w|∂_kχ|² ≤ K E_0` (`AdjointLocalizedBound`), `e1Rate + β E_2 ≤ K(E_1 + E_0)`; with
   `β ≥ β_min` this is `E_1' + β_min E_2 ≤ C_b(E_1 + E_0)`.

The regularity used to make every integral absolutely convergent is split off: `MovAdjBasicReg`
(from the fields of `IsAdjointFlow`) and `MovAdjHigherReg` (weighted `H^2`, `H^3` integrability).
Both are rescalings of fields of `IsAdjointFlow`: `memX`, `memH1` for the first and `higherCont`
(`φ ∈ C¹([t, s); H^3_{-m,c})`, SP 3060-3073, `AdjHigherCont`) for the second, by `x = √a y` and the
equivalence of `p_d⁻¹` with `⟨y⟩^{-2m}` on the cell; there is no parabolic estimate in them, no
hypothesis on the train is needed. The classical equation `MovAdjEquation` needs the interaction
`χ = ∂_rφ + νΔφ + v·∇φ` to be the adjoint localized interaction, i.e. the weak equation with
continuity of `r ↦ ∫ φ(r)(uψ·∇E(r))`, which needs the tail bound of `∇E`: `MovAdjEquation` has the
time-local train bounds `LadTrainBdd` (as `AdjWCtx`, `Sub/T21_2_3/AdjWeakSmooth.lean`): this is the
hypothesis `hB` of `MovAdjEquation`, the only leaf that needs it. The
differentiation of the energies uses `AdjXDiff` (`Sub/T21_2_2/AdjXDiff.lean`). `MovingTrainVReg` records that the rescaled
velocity is `C^1` and `d`-periodic.

Note on the form of step 2: the non-integrated-by-parts intermediate `2∫ w Re(conj Φ_k ∂_ζΦ_k)`
contains `w Re(conj Φ_k y·∇Φ_k)`, which need not be integrable for a terminal datum that is only in
`X_{-m}`; so the leaf states the derivative after the Reynolds/seam cancellation.

All names live in the namespace `UnforcedLeray.Short.IIIa.AdjE1` (the parallel `E_0` decomposition
`PartIII-a:T21/2/2/2` may define its own versions).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-! ## Differential operators on complex fields of the plane -/

/-- The Laplacian `ΔΦ = ∂_1²Φ + ∂_2²Φ` of a complex field. -/
def lapC (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ := pdCx 0 (pdCx 0 Φ) y + pdCx 1 (pdCx 1 Φ) y

/-- The dilation `y·∇Φ`. -/
def radC (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  (y.1 : ℂ) * pdCx 0 Φ y + (y.2 : ℂ) * pdCx 1 Φ y

/-- The transport `V·∇Φ` by a real vector field `V`. -/
def transC (V : ℝ × ℝ → Fin 2 → ℝ) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  (V y 0 : ℂ) * pdCx 0 Φ y + (V y 1 : ℂ) * pdCx 1 Φ y

/-- `(∂_kV)·∇Φ`. -/
def dTransC (V : ℝ × ℝ → Fin 2 → ℝ) (Φ : ℝ × ℝ → ℂ) (k : Fin 2) (y : ℝ × ℝ) : ℂ :=
  (B0579.pd k (fun x => V x 0) y : ℂ) * pdCx 0 Φ y +
    (B0579.pd k (fun x => V x 1) y : ℂ) * pdCx 1 Φ y

/-- The reverse moving adjoint generator without the interaction (SP 2858-2862, 2909-2911):
`β D^#Φ + V·∇Φ = β(ΔΦ - ½ y·∇Φ + Φ) + V·∇Φ`, `β = θ⁻¹`. It is the adjoint of
`θ⁻¹D - V·∇`, `D = Δ + ½y·∇ + 2`, for the pairing `∫_{C_d} WΦ` (`V` divergence free). -/
def adjGen (β : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  (β : ℂ) * (lapC Φ y - (1 / 2 : ℂ) * radC Φ y + Φ y) + transC V Φ y

/-- `χ` is the adjoint localized interaction `K_d^T(Φ∇E_mov)` of `Φ` on the cell of length `d`
(SP 3052-3058), in the weak form used by `AdjointLocalizedBound`: `∫ χψ = ∫ Φ (K_dψ)·∇E_mov` for
every test `ψ` of the cell (any circulation) with its kernel velocity. -/
def IsAdjInteraction (d : ℝ) (Em : ℝ × ℝ → ℝ) (Φ χ : ℝ × ℝ → ℂ) : Prop :=
  ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
    ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
      ∫ y in B0579.cell d, Φ y * ((uψ y 0 * B0579.pd 0 Em y + uψ y 1 * B0579.pd 1 Em y : ℝ) : ℂ)

/-! ## Reverse moving time -/

/-- The moving adjoint at reverse moving time `ζ` (age `revAge ν s ζ`). `revE_j ν c m φ s ζ` is
`adjE_j (mvLen ν c s ζ) m (mvPhi ν φ s ζ)` by definition. -/
def mvPhi (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) : ℝ × ℝ → ℂ := movingPhi ν φ (revAge ν s ζ)

/-- The moving cell length `d = c/√a` at reverse moving time `ζ`. -/
def mvLen (ν c s ζ : ℝ) : ℝ := cellLen c (clockA ν (revAge ν s ζ))

/-- The diffusion coefficient `β = θ⁻¹ = ν a` at reverse moving time `ζ` (SP 3062). -/
def mvBeta (ν s ζ : ℝ) : ℝ := ν * clockA ν (revAge ν s ζ)

/-- The regime of the adjoint-flow leaves: `ν > 0`, `0 ≤ t < s`, `φ` the adjoint flow on `[t, s]`
of a terminal datum `physAdj a_s G`, `G ∈ X_{-m,d_s}` (SP 3060), at `ζ ∈ (0, Δz)`. -/
def AdjFlowAt (m ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ) : Prop :=
  0 < ν ∧ 0 ≤ t ∧ t < s ∧
    (∃ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) ∧
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ) ∧
    ζ ∈ Ioo 0 (deltaZ ν t s)

/-! ## The energy rate -/

/-- `∂_ζ w` for `w = p_{d(ζ)}⁻¹ = periodicWeight (-m) d`, with `d_ζ = dβ/2` (SP 2860:
`d_z/d = -1/(2θ)`, `ζ = z_s - z`). -/
def dtW (m d β : ℝ) (y : ℝ × ℝ) : ℝ :=
  deriv (fun d' => periodicWeight (-m) d' y) d * (d * β / 2)

/-- The part of `∂_ζ∂_kΦ` left after removing the dilation `-(β/2) y·∇∂_kΦ`:
`β(Δ∂_kΦ + ½∂_kΦ) + V·∇∂_kΦ + (∂_kV)·∇Φ - ∂_kχ` (from `∂_k` of the moving adjoint equation). -/
def xiRed (β : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ χ : ℝ × ℝ → ℂ) (k : Fin 2) (y : ℝ × ℝ) : ℂ :=
  (β : ℂ) * (lapC (pdCx k Φ) y + (1 / 2 : ℂ) * pdCx k Φ y) + transC V (pdCx k Φ) y +
    dTransC V Φ k y - pdCx k χ y

/-- The derivative of `E_1` after Reynolds' cancellation of the dilation seam (SP 2945-2957, 3062):
`Σ_k [∫ ∂_ζw |∂_kΦ|² + 2∫ w Re(conj(∂_kΦ) xiRed_k) + (β/2) ∫ (2w + y·∇w) |∂_kΦ|²]` on `C_d`. -/
def e1Rate (m d β : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ χ : ℝ × ℝ → ℂ) : ℝ :=
  ∑ k : Fin 2,
    ((∫ y in B0579.cell d, dtW m d β y * ‖pdCx k Φ y‖ ^ 2) +
      2 * (∫ y in B0579.cell d,
        periodicWeight (-m) d y * ((starRingEnd ℂ) (pdCx k Φ y) * xiRed β V Φ χ k y).re) +
      β / 2 * ∫ y in B0579.cell d,
        (2 * periodicWeight (-m) d y + (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
          y.2 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖pdCx k Φ y‖ ^ 2)

/-! ## Regularity of a moving slice -/

/-- Low-order regularity of a moving slice `Φ` on the cell of length `d`: smooth, `d`-periodic,
`w|Φ|²` and `w|∂_kΦ|²` integrable (`E_0, E_1 < ∞`). -/
structure MovRegLow (m d : ℝ) (Φ : ℝ × ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  periodic : ∀ y : ℝ × ℝ, Φ (y.1 + d, y.2) = Φ y
  int0 : IntegrableOn (fun y => periodicWeight (-m) d y * ‖Φ y‖ ^ 2) (B0579.cell d)
  int1 : ∀ k : Fin 2,
    IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) (B0579.cell d)

/-- Higher regularity of a moving slice: `w|∂_k∂_lΦ|²` (`E_2 < ∞`) and `w|∂_j∂_k∂_lΦ|²`
integrable on the cell. -/
structure MovRegHigh (m d : ℝ) (Φ : ℝ × ℝ → ℂ) : Prop where
  int2 : ∀ k l : Fin 2,
    IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx k (pdCx l Φ) y‖ ^ 2) (B0579.cell d)
  int3 : ∀ j k l : Fin 2,
    IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx j (pdCx k (pdCx l Φ)) y‖ ^ 2)
      (B0579.cell d)

/-! ## The leaves -/

/-- **Leaf 1: the rescaled train velocity** (SP 2861-2873): for `r ≥ 0` and `a(r) > 0`,
`V = movingTrainV tr r` is `C^1` and periodic with the moving cell length `d = c/√a`
(from `IsTrain.smooth_v`, `IsTrain.periodic_v`). -/
def MovingTrainVReg : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ), 0 ≤ r → 0 < clockA ν r →
    ContDiff ℝ 1 (movingTrainV tr r) ∧
      ∀ y : ℝ × ℝ, movingTrainV tr r (y.1 + cellLen c (clockA ν r), y.2) = movingTrainV tr r y

/-- **Leaf 2: the classical reverse moving adjoint equation** (SP 2854-2862, 2909-2911, 3036-3037,
3052-3060), for a train with the time-local bounds `LadTrainBdd` on every `[0, S]` (SP 270-288,
2866-2873: bounded velocity, `⟨x⟩^{m+2}|∇E|` bounded on the cell; consumers have `IsBUCTrain` and
`ladTrainBddAll`): at every `ζ ∈ (0, Δz)` the moving adjoint satisfies, pointwise,
`∂_ζΦ = θ⁻¹(ΔΦ - ½y·∇Φ + Φ) + V·∇Φ - χ` with `χ` a `C^1`, `d`-periodic adjoint localized
interaction `K_d^T(Φ∇E_mov)` of `Φ`. -/
def MovAdjEquation (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∃ χ : ℝ × ℝ → ℂ, ContDiff ℝ 1 χ ∧
      (∀ y : ℝ × ℝ, χ (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, y.2) = χ y) ∧
      IsAdjInteraction (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (movingTrainE tr (revAge ν s ζ))
        (mvPhi ν φ s ζ) χ ∧
      ∀ y : ℝ × ℝ, HasDerivAt (fun ζ' => mvPhi ν φ s ζ' y)
        (adjGen (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y - χ y) ζ

/-- **Leaf 3: low-order regularity of the moving adjoint** (SP 3036-3037, 3044-3047, 3060): from
`IsAdjointFlow.smooth`, `periodic`, `memX`, `memH1` by `x = √a y` and the equivalence of
`p_d⁻¹` with `⟨y⟩^{-2m}` on the cell. -/
def MovAdjBasicReg (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    MovRegLow m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvPhi ν φ s ζ)

/-- **Leaf 4: weighted `H^2`, `H^3` regularity of the moving adjoint before the terminal age**
(SP 3060-3071: `E_2` appears there as a finite quantity). From `IsAdjointFlow.higherCont`
(`∂^wφ(r) ∈ X_{-m,c}` for `|w| ≤ 3`, `r ∈ [t, s)`) by `x = √a y` and the equivalence of `p_d⁻¹`
with `⟨y⟩^{-2m}` on the cell; the parabolic regularity itself is the leaf `AdjointWeakHigherCont`
(`Sub/PartIIIa_T21_2_7_2.lean`). -/
def MovAdjHigherReg (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    MovRegHigh m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvPhi ν φ s ζ)

/-- **Leaf 5: the differentiated weighted energy on the moving cell, with Reynolds' cancellation
of the dilation seam** (SP 2860, 2945-2957, 3060-3062): if `χ` is the interaction in the moving
equation at `ζ` (`C^1`, `d`-periodic, `w|∂_kχ|²` integrable), then `E_1` has derivative
`e1Rate` at `ζ`. -/
def E1MovingDeriv (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ 1 χ →
      (∀ y : ℝ × ℝ, χ (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, y.2) = χ y) →
      (∀ y : ℝ × ℝ, HasDerivAt (fun ζ' => mvPhi ν φ s ζ' y)
        (adjGen (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y - χ y) ζ) →
      (∀ k : Fin 2, IntegrableOn
        (fun y => periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y * ‖pdCx k χ y‖ ^ 2)
        (B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ))) →
      HasDerivAt (revE1 ν (ν ^ (-2 : ℝ)) m φ s)
        (e1Rate m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ))
          (mvPhi ν φ s ζ) χ) ζ

/-- **Leaf 6: the derivative of the adjoint interaction** (SP 3052-3058, from
`AdjointLocalizedBound`: `K_d^T(Φ∇E_mov)` maps `X_{-m,d}` to `H^1_{-m,d}` uniformly; with the
equivalence of `p_d⁻¹` and `⟨y⟩^{-2m}` on the cell): for `b` large, `ν` small, `θ(r) ≥ b`, every
`C^1`, `d`-periodic adjoint interaction `χ` of a continuous `Φ` with `E_0(Φ) < ∞` has
`Σ_k ∫ w|∂_kχ|² ≤ K E_0(Φ)`, for BUC trains (`PartI.IsBUCTrain`, SP 270-288, as in
`AdjointLocalizedBound`). Stated for `0 ≤ m` as in the source (the weight comparison fails for
`m < 0`). -/
def AdjChiDerivBound (m : ℝ) : Prop :=
  0 ≤ m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (K ν₀ : ℝ), 0 ≤ K ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r →
      b ≤ clockTheta ν r → ∀ Φ χ : ℝ × ℝ → ℂ, Continuous Φ →
        IntegrableOn
          (fun y => periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) y * ‖Φ y‖ ^ 2)
          (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))) →
        ContDiff ℝ 1 χ →
        (∀ y : ℝ × ℝ, χ (y.1 + cellLen (ν ^ (-2 : ℝ)) (clockA ν r), y.2) = χ y) →
        IsAdjInteraction (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (movingTrainE tr r) Φ χ →
        (∀ k : Fin 2, IntegrableOn
          (fun y => periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) y * ‖pdCx k χ y‖ ^ 2)
          (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))) ∧
        ∑ k : Fin 2, ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
            periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) y * ‖pdCx k χ y‖ ^ 2 ≤
          K * adjE0 (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m Φ

/-- **Leaf 7: the diffusion integration by parts on the periodic cell** (SP 3062, 3067-3069; the
seam terms cancel by `d`-periodicity of `w` and `Φ`, the terms at `|η| → ∞` vanish by
integrability): `∫ w Re(conj Φ_k ΔΦ_k) = -Σ_l ∫ w|∂_lΦ_k|² - Σ_l ∫ ∂_lw Re(conj Φ_k ∂_lΦ_k)`,
`Φ_k = ∂_kΦ`, with the integrands integrable. -/
def E1DiffusionIBP (m : ℝ) : Prop :=
  ∀ (d : ℝ) (Φ : ℝ × ℝ → ℂ), 0 < d → MovRegLow m d Φ → MovRegHigh m d Φ → ∀ k : Fin 2,
    IntegrableOn (fun y => periodicWeight (-m) d y *
        ((starRingEnd ℂ) (pdCx k Φ y) * lapC (pdCx k Φ) y).re) (B0579.cell d) ∧
      (∀ l : Fin 2, IntegrableOn (fun y => B0579.pd l (periodicWeight (-m) d) y *
        ((starRingEnd ℂ) (pdCx k Φ y) * pdCx l (pdCx k Φ) y).re) (B0579.cell d)) ∧
      ∫ y in B0579.cell d, periodicWeight (-m) d y *
          ((starRingEnd ℂ) (pdCx k Φ y) * lapC (pdCx k Φ) y).re =
        -(∑ l : Fin 2, ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx l (pdCx k Φ) y‖ ^ 2) -
          ∑ l : Fin 2, ∫ y in B0579.cell d, B0579.pd l (periodicWeight (-m) d) y *
            ((starRingEnd ℂ) (pdCx k Φ y) * pdCx l (pdCx k Φ) y).re

/-- **Leaf 8: the transport integration by parts on the periodic cell** (SP 2954-2956, 3068):
for a `C^1`, `d`-periodic velocity with `|V|, |∇V| ≤ C`,
`2∫ w Re(conj Φ_k V·∇Φ_k) = -∫ (V·∇w + w div V)|Φ_k|²`, with the integrands integrable. -/
def E1TransportIBP (m : ℝ) : Prop :=
  ∀ (d CV : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ : ℝ × ℝ → ℂ), 0 < d → ContDiff ℝ 1 V →
    (∀ y : ℝ × ℝ, V (y.1 + d, y.2) = V y) →
    (∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j V y‖ ≤ CV) →
    MovRegLow m d Φ → MovRegHigh m d Φ → ∀ k : Fin 2,
      IntegrableOn (fun y => periodicWeight (-m) d y *
        ((starRingEnd ℂ) (pdCx k Φ y) * transC V (pdCx k Φ) y).re) (B0579.cell d) ∧
      IntegrableOn (fun y => (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
          V y 1 * B0579.pd 1 (periodicWeight (-m) d) y + periodicWeight (-m) d y *
            (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) *
          ‖pdCx k Φ y‖ ^ 2) (B0579.cell d) ∧
      2 * ∫ y in B0579.cell d, periodicWeight (-m) d y *
          ((starRingEnd ℂ) (pdCx k Φ y) * transC V (pdCx k Φ) y).re =
        -∫ y in B0579.cell d, (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
          V y 1 * B0579.pd 1 (periodicWeight (-m) d) y + periodicWeight (-m) d y *
            (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) *
          ‖pdCx k Φ y‖ ^ 2

/-- **Leaf 9: the bound of the energy rate** (SP 3062-3071: "the diffusion-weight errors have
coefficient `C_mβ` and the transport and compact terms have coefficient `C_b`"): for `0 < β ≤ 1`,
a `C^1` periodic velocity with `|V|, |∇V| ≤ C_V` and an interaction with
`Σ_k ∫ w|∂_kχ|² ≤ K_χ E_0`, `e1Rate + β E_2 ≤ K(E_1 + E_0)` with `K` depending only on
`m, C_V, K_χ`. -/
def E1RemainderBound (m : ℝ) : Prop :=
  ∀ CV Kχ : ℝ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ (d β : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ χ : ℝ × ℝ → ℂ), 0 < d → 0 < β → β ≤ 1 →
      ContDiff ℝ 1 V → (∀ y : ℝ × ℝ, V (y.1 + d, y.2) = V y) →
      (∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j V y‖ ≤ CV) →
      MovRegLow m d Φ → MovRegHigh m d Φ → ContDiff ℝ 1 χ →
      (∀ k : Fin 2, IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx k χ y‖ ^ 2)
        (B0579.cell d)) →
      ∑ k : Fin 2, ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k χ y‖ ^ 2 ≤
        Kχ * adjE0 d m Φ →
      e1Rate m d β V Φ χ + β * adjE2 d m Φ ≤ K * (adjE1 d m Φ + adjE0 d m Φ)

end UnforcedLeray.Short.IIIa.AdjE1
