import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Part III-a, `PartIII-a:T21/2/2/2`: the `E_0` inequality of the reverse-time adjoint, decomposed

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3066
(`E_0' + β_min E_1 ≤ C_b E_0`, "Reynolds cancellation and differentiated weighted energy"), with
the moving equation `eq:short-causal-moving` (SP 2854-2865, `d_z/d = -1/(2θ)`), the adjoint
operator `D^# = Δ - ½ y·∇ + 1` (SP 2919-2921), the Reynolds seam cancellation (SP 2945-2957), the
periodic weight bounds (SP 3044-3050), the rescaled train bounds (SP 3050-3051) and the adjoint
localized interaction (SP 3052-3058).

## The computation (SP 3060-3066)

Let `Φ(ζ) = revPhi ν φ s ζ` be the moving adjoint at reverse moving time `ζ = z_s - z`, on the
moving cell `C_d`, `d = d(ζ) = revCell`, `θ = θ(ζ) = revTheta`, and `w = p_d⁻¹ =
periodicWeight (-m) d`. The reverse moving adjoint equation (the adjoint of
`W_z = (θ⁻¹D + L_{ν,c})W` in the duality `∫_{C_d} WΦ`) is
`∂_ζΦ = θ⁻¹ D^#Φ + V·∇Φ - χ`, `χ = K_d^T(Φ∇E_mov)` (`MovingAdjointEq`). Along `ζ` the cell
dilates, `∂_ζ d = d/(2θ)`. Reynolds' boundary term for `d/dζ ∫_{C_{d(ζ)}}` and the seam term of
`-½θ⁻¹ y·∇` cancel; equivalently, after the change of variables to a fixed cell the dilation
part of `D^#` is absorbed, and (`AdjE0Reynolds`)
`E_0' = ∫ [(d/(2θ)) ∂_d w + θ⁻¹ w + (2θ)⁻¹ y·∇w] |Φ|² + 2 ∫ w Re(Φ̄ (∂_ζΦ + (2θ)⁻¹ y·∇Φ))`.
With the equation, `∂_ζΦ + (2θ)⁻¹ y·∇Φ = θ⁻¹(ΔΦ + Φ) + V·∇Φ - χ` (`adjPsi`). The remaining
integrations by parts on the periodic cell have no seam (`CellLapIBP`, `CellTransportIBP`,
assembled in `CellRateReduce`), and the weight, train and interaction bounds give
`E_0' + θ⁻¹ E_1 ≤ C_b E_0` (`CellRateEstimate`), with `β_min = ν a_t ≤ ν a = θ⁻¹`.

Everything here lives in the namespace `UnforcedLeray.Short.IIIa.E0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-! ## Moving variables at reverse moving time `ζ` (SP 2854-2865, 3060) -/

/-- The moving adjoint `Φ(ζ) = a⁻¹ φ(r, √a ·)` at reverse moving time `ζ`, age
`r = revAge ν s ζ` (SP 2861, 3036-3037). -/
def revPhi (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) : ℝ × ℝ → ℂ :=
  movingPhi ν φ (revAge ν s ζ)

/-- The moving cell length `d(ζ) = c/√a(r)` (SP 2857). -/
def revCell (ν c s ζ : ℝ) : ℝ := cellLen c (clockA ν (revAge ν s ζ))

/-- The heat clock `θ(ζ) = (ν a(r))⁻¹` at reverse moving time `ζ` (SP 2856). -/
def revTheta (ν s ζ : ℝ) : ℝ := clockTheta ν (revAge ν s ζ)

/-- The classical reverse-time derivative `∂_ζΦ(ζ, y)`. -/
def revDt (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) (y : ℝ × ℝ) : ℂ :=
  deriv (fun ζ' => revPhi ν φ s ζ' y) ζ

/-! ## Differential operators on complex fields of the plane -/

/-- The Laplacian `ΔΦ = ∂₀∂₀Φ + ∂₁∂₁Φ`. -/
def lapCx (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  pdCx 0 (pdCx 0 Φ) y + pdCx 1 (pdCx 1 Φ) y

/-- The dilation field `y·∇Φ`. -/
def dilCx (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  (y.1 : ℂ) * pdCx 0 Φ y + (y.2 : ℂ) * pdCx 1 Φ y

/-- The transport `V·∇Φ` by a real field `V`. -/
def transCx (V : ℝ × ℝ → Fin 2 → ℝ) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  (V y 0 : ℂ) * pdCx 0 Φ y + (V y 1 : ℂ) * pdCx 1 Φ y

/-- `D^#Φ = ΔΦ - ½ y·∇Φ + Φ`, the adjoint of `D = Δ + ½ y·∇ + 2` (SP 2919-2921). -/
def dSharp (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  lapCx Φ y - (1 / 2 : ℂ) * dilCx Φ y + Φ y

/-- `χ` is the adjoint localized interaction `K_d^T(Φ∇E)` of `Φ` on the cell of length `d`:
`∫ χψ = ∫ Φ (K_dψ)·∇E` for every cylinder test `ψ` of any circulation with its kernel velocity
(SP 3052-3058; this is the last clause of `AdjointLocalizedBound` with `E = E_mov`). -/
def IsAdjInteraction (d : ℝ) (E : ℝ × ℝ → ℝ) (Φ χ : ℝ × ℝ → ℂ) : Prop :=
  ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest d ψ →
    IsKernelBiotSavart d ψ uψ →
    ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
      ∫ y in B0579.cell d, Φ y * ((uψ y 0 * B0579.pd 0 E y + uψ y 1 * B0579.pd 1 E y : ℝ) : ℂ)

/-! ## The weight `w = p_d⁻¹` (SP 3044-3050) -/

/-- `y·∇w`, `w = periodicWeight (-m) d`. -/
def wDil (m d : ℝ) (y : ℝ × ℝ) : ℝ :=
  y.1 * B0579.pd 0 (periodicWeight (-m) d) y + y.2 * B0579.pd 1 (periodicWeight (-m) d) y

/-- `∂_d w`, the derivative of the weight in the cell length. -/
def wDd (m d : ℝ) (y : ℝ × ℝ) : ℝ :=
  deriv (fun d' => periodicWeight (-m) d' y) d

/-- A smooth `d`-periodic nonnegative weight with `|∂_k w| ≤ K w`. -/
structure CellWeight (d K : ℝ) (w : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 1 w
  periodic : ∀ y : ℝ × ℝ, w (y.1 + d, y.2) = w y
  nonneg : ∀ y : ℝ × ℝ, 0 ≤ w y
  grad : ∀ (y : ℝ × ℝ) (k : Fin 2), |B0579.pd k w y| ≤ K * w y

/-- The bounds on `w = p_d⁻¹` used at SP 3060-3066, consequences of `PeriodicWeightLogBounds`
(SP 3044-3050): `|∇w| ≤ Kw` on the plane and, on the cell, `|y·∇w| ≤ Kw` and `|d ∂_d w| ≤ Kw`
(the last is `|∂_ζ log p_{d(ζ)}| ≤ K/(2θ)` with `∂_ζ d = d/(2θ)`); `∂_d w` is continuous in `y`. -/
structure WeightHyp (m K d : ℝ) : Prop where
  base : CellWeight d K (periodicWeight (-m) d)
  dil : ∀ y ∈ B0579.cell d, |wDil m d y| ≤ K * periodicWeight (-m) d y
  dlen : ∀ y ∈ B0579.cell d, |d * wDd m d y| ≤ K * periodicWeight (-m) d y
  dlenCont : Continuous (wDd m d)

/-- A smooth `d`-periodic field with finite `E_0` and `E_1` (as integrable integrands). -/
structure CellField (m d : ℝ) (Φ : ℝ × ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ 2 Φ
  periodic : ∀ y : ℝ × ℝ, Φ (y.1 + d, y.2) = Φ y
  int0 : IntegrableOn (fun y => periodicWeight (-m) d y * ‖Φ y‖ ^ 2) (B0579.cell d)
  int1 : ∀ k : Fin 2,
    IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) (B0579.cell d)

/-- A `C¹`, `d`-periodic, divergence-free drift bounded by `CV` (the rescaled train velocity,
SP 2954-2955, 3050-3051). -/
structure CellDrift (d CV : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) : Prop where
  smooth : ContDiff ℝ 1 V
  periodic : ∀ y : ℝ × ℝ, V (y.1 + d, y.2) = V y
  divFree : ∀ y : ℝ × ℝ,
    B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y = 0
  bound : ∀ (y : ℝ × ℝ) (k : Fin 2), |V y k| ≤ CV

/-! ## The energy rate -/

/-- `w Re(Φ̄ Ψ)` with `w = periodicWeight (-m) d`. -/
def wRe (m d : ℝ) (Φ Ψ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℝ :=
  periodicWeight (-m) d y * (starRingEnd ℂ (Φ y) * Ψ y).re

/-- The rate of `E_0` after Reynolds' cancellation (SP 2945-2946, 3060-3062):
`∫ [(d/(2θ)) ∂_d w + θ⁻¹ w + (2θ)⁻¹ y·∇w] |Φ|² + 2 ∫ w Re(Φ̄ Ψ)`, where `Ψ` is the derivative of
`Φ` along the dilation of the cell, `Ψ = ∂_ζΦ + (2θ)⁻¹ y·∇Φ`. -/
def rate0 (m d θ : ℝ) (Φ Ψ : ℝ × ℝ → ℂ) : ℝ :=
  (∫ y in B0579.cell d, (d / (2 * θ) * wDd m d y + θ⁻¹ * periodicWeight (-m) d y +
      (2 * θ)⁻¹ * wDil m d y) * ‖Φ y‖ ^ 2) +
    2 * ∫ y in B0579.cell d, wRe m d Φ Ψ y

/-- `Ψ = θ⁻¹(ΔΦ + Φ) + V·∇Φ - χ`: by the moving adjoint equation this is
`∂_ζΦ + (2θ)⁻¹ y·∇Φ` (SP 2861, 2919-2921, 3060). -/
def adjPsi (θ : ℝ) (Φ χ : ℝ × ℝ → ℂ) (V : ℝ × ℝ → Fin 2 → ℝ) (y : ℝ × ℝ) : ℂ :=
  ((θ⁻¹ : ℝ) : ℂ) * (lapCx Φ y + Φ y) + transCx V Φ y - χ y

/-- The rate after the integrations by parts of the diffusion and the transport (no seam terms:
`Φ, w, V` are `d`-periodic):
`∫ [(d/(2θ)) ∂_d w + 3θ⁻¹ w + (2θ)⁻¹ y·∇w - V·∇w] |Φ|² - 2θ⁻¹ E_1
 - 2θ⁻¹ Σ_k ∫ ∂_k w Re(Φ̄ ∂_kΦ) - 2 ∫ w Re(Φ̄ χ)`. -/
def rate0Reduced (m d θ : ℝ) (Φ χ : ℝ × ℝ → ℂ) (V : ℝ × ℝ → Fin 2 → ℝ) : ℝ :=
  (∫ y in B0579.cell d, (d / (2 * θ) * wDd m d y + 3 * θ⁻¹ * periodicWeight (-m) d y +
      (2 * θ)⁻¹ * wDil m d y -
      (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
        V y 1 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖Φ y‖ ^ 2) -
    2 * θ⁻¹ * adjE1 d m Φ -
    2 * θ⁻¹ * (∑ k : Fin 2, ∫ y in B0579.cell d,
      B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re) -
    2 * ∫ y in B0579.cell d, wRe m d Φ χ y

/-! ## The leaves -/

/-- **The reverse moving adjoint equation** (SP 2854-2865 `eq:short-causal-moving`, its adjoint
`D^#` SP 2919-2921, the adjoint localized interaction SP 3052-3058, used at SP 3060). For the
weak reverse-time adjoint `φ` of `IsAdjointFlow` and `ζ ∈ (0, Δz)`, the moving adjoint
`Φ = revPhi ν φ s ζ` satisfies, for every adjoint localized interaction `χ ∈ X_{-m,d}` of `Φ`
(with `E = E_mov(r)`), for `ν ≤ 1` and a train with the time-local bounds `LadTrainBdd` on every
`[0, S]` (SP 270-288; needed for the classical form of the weak equation), `∂_ζΦ(ζ, y) = θ⁻¹ D^#Φ(y) + V·∇Φ(y) - χ(y)` for a.e. `y` in the cell,
`V = V(r)` the rescaled train velocity. (Derivation: the classical form
`-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)` of `IsAdjointFlow.weak` on the smooth range `[t, s)`, the
substitution `Φ = a⁻¹φ(r, √a ·)` with `dr/dζ = -a²`, and uniqueness of `χ` tested against all
cylinder tests.) -/
def MovingAdjointEq (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ → ν ≤ 1 →
      (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s), ∀ χ : ℝ × ℝ → ℂ,
        MemLp χ 2 (B0579.cellMeasure (revCell ν (ν ^ (-2 : ℝ)) s ζ) (-m)) →
        IsAdjInteraction (revCell ν (ν ^ (-2 : ℝ)) s ζ) (movingTrainE tr (revAge ν s ζ))
          (revPhi ν φ s ζ) χ →
        ∀ᵐ y ∂(volume.restrict (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ))),
          HasDerivAt (fun ζ' => revPhi ν φ s ζ' y)
            ((((revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dSharp (revPhi ν φ s ζ) y +
              transCx (movingTrainV tr (revAge ν s ζ)) (revPhi ν φ s ζ) y - χ y) ζ

/-- **Differentiated weighted energy with Reynolds' cancellation** (SP 2945-2946, 2860, 3060-3062).
For the weak reverse-time adjoint and `ζ ∈ (0, Δz)`: with `Φ, d, θ` at `ζ`,
`Ψ = ∂_ζΦ + (2θ)⁻¹ y·∇Φ`, the integrand `w Re(Φ̄ Ψ)` is integrable on the cell and
`E_0'(ζ) = rate0 m d θ Φ Ψ`. Reynolds' boundary term `∂_ζ d · ∫ w|Φ|²(d/2, ·)` of the moving
cell (`∂_ζ d = d/(2θ)`) cancels the seam term `-(d/(2θ)) ∫ w|Φ|²(d/2, ·)` of the dilation part of
`D^#`; equivalently, under `y = (d(ζ)/d(ζ₀)) u` the cell is fixed and the dilation is absorbed. -/
def AdjE0Reynolds (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s),
        IntegrableOn (wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ)
            (fun y => revDt ν φ s ζ y +
              (((2 * revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dilCx (revPhi ν φ s ζ) y))
          (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ)) ∧
        HasDerivAt (revE0 ν (ν ^ (-2 : ℝ)) m φ s)
          (rate0 m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revTheta ν s ζ) (revPhi ν φ s ζ)
            (fun y => revDt ν φ s ζ y +
              (((2 * revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dilCx (revPhi ν φ s ζ) y)) ζ

/-- **Regularity of the moving adjoint at a fixed age** (SP 3060; `IsAdjointFlow.smooth`,
`periodic`, `memX`, `memH1` transported by `Φ = a⁻¹φ(r, √a ·)` to the cell of length
`d = c/√a`, with `p_d⁻¹ ≤ (π²/4)^m ⟨y⟩^{-2m}` on the cell, SP 3044). -/
def RevPhiReg (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ → ∀ r ∈ Ico t s,
        CellField m (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (movingPhi ν φ r) ∧
        MemLp (movingPhi ν φ r) 2
          (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))

/-- **The rescaled train velocity** `V(r) = a^{3/2} v(r, √a ·)` is `C¹`, `d`-periodic
(`d = c/√a`) and divergence free, for `r ≥ 0` (SP 2861-2873, 2954-2955; from
`IsTrain.smooth_v`, `periodic_v`, `solenoidal`). -/
def MovingTrainReg : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 0 < c → ∀ (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ), 0 ≤ r →
    ContDiff ℝ 1 (movingTrainV tr r) ∧
    (∀ y : ℝ × ℝ, movingTrainV tr r (y.1 + cellLen c (clockA ν r), y.2) = movingTrainV tr r y) ∧
    ∀ y : ℝ × ℝ, B0579.pd 0 (fun x => movingTrainV tr r x 0) y +
      B0579.pd 1 (fun x => movingTrainV tr r x 1) y = 0

/-- **The weight bounds** (SP 3044-3050): one constant `K` for all cell lengths `d > 0`. -/
def AdjWeightBounds (m : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 < d → WeightHyp m K d

/-- **Equivalence of the periodic weight** (SP 3044, "the equivalent periodic weight"):
`⟨y⟩^{-2m} ≤ p_d⁻¹` on the plane (`|sin x| ≤ |x|`) and `p_d⁻¹ ≤ (π²/4)^m ⟨y⟩^{-2m}` on the cell
(Jordan's inequality on `|π y₁/d| ≤ π/2`); `jb y = ⟨y⟩²`. -/
def AdjWeightEquiv (m : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d →
    (∀ y : ℝ × ℝ, B0579.jb y ^ (-m) ≤ periodicWeight (-m) d y) ∧
    ∀ y ∈ B0579.cell d, periodicWeight (-m) d y ≤ (Real.pi ^ 2 / 4) ^ m * B0579.jb y ^ (-m)

/-- **The adjoint interaction in the energy norm** (SP 3052-3058, with SP 3044): in the regime of
`AdjointLocalizedBound`, every `Φ ∈ X_{-m,d}` has an adjoint localized interaction `χ` with
`∫ w|χ|² ≤ C_X E_0(Φ)`, for BUC trains (`PartI.IsBUCTrain`, SP 270-288, as in
`AdjointLocalizedBound`). -/
def AdjChiWeighted (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (CX ν₀ : ℝ), 0 ≤ CX ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r →
      b ≤ clockTheta ν r → ∀ Φ : ℝ × ℝ → ℂ,
        MemLp Φ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) →
        ∃ χ : ℝ × ℝ → ℂ,
          MemLp χ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
          AEStronglyMeasurable χ
            (volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))) ∧
          IsAdjInteraction (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (movingTrainE tr r) Φ χ ∧
          IntegrableOn
            (fun y => periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) y * ‖χ y‖ ^ 2)
            (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))) ∧
          ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
              periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) y * ‖χ y‖ ^ 2 ≤
            CX * adjE0 (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m Φ

/-- **Weighted integration by parts of the diffusion on the periodic cell** (SP 3060-3062,
"differentiated weighted energy"; no seam term since `w, Φ` are `d`-periodic):
`∫ w Re(Φ̄ ΔΦ) = -Σ_k ∫ w|∂_kΦ|² - Σ_k ∫ ∂_k w Re(Φ̄ ∂_kΦ)`. -/
def CellLapIBP : Prop :=
  ∀ (d K : ℝ) (w : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℂ), 0 < d → CellWeight d K w →
    ContDiff ℝ 2 Φ → (∀ y : ℝ × ℝ, Φ (y.1 + d, y.2) = Φ y) →
    IntegrableOn (fun y => w y * ‖Φ y‖ ^ 2) (B0579.cell d) →
    (∀ k : Fin 2, IntegrableOn (fun y => w y * ‖pdCx k Φ y‖ ^ 2) (B0579.cell d)) →
    IntegrableOn (fun y => w y * (starRingEnd ℂ (Φ y) * lapCx Φ y).re) (B0579.cell d) →
    ∫ y in B0579.cell d, w y * (starRingEnd ℂ (Φ y) * lapCx Φ y).re =
      -(∑ k : Fin 2, ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) -
        ∑ k : Fin 2, ∫ y in B0579.cell d, B0579.pd k w y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re

/-- **Weighted integration by parts of the transport on the periodic cell** (SP 2954-2955,
"radial Euler transport preserves the weight"; `div V = 0`, no seam term):
`∫ w Re(Φ̄ V·∇Φ) = -½ ∫ (V·∇w) |Φ|²`. -/
def CellTransportIBP : Prop :=
  ∀ (d K CV : ℝ) (w : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℂ) (V : ℝ × ℝ → Fin 2 → ℝ), 0 < d →
    CellWeight d K w → ContDiff ℝ 1 Φ → (∀ y : ℝ × ℝ, Φ (y.1 + d, y.2) = Φ y) →
    IntegrableOn (fun y => w y * ‖Φ y‖ ^ 2) (B0579.cell d) →
    (∀ k : Fin 2, IntegrableOn (fun y => w y * ‖pdCx k Φ y‖ ^ 2) (B0579.cell d)) →
    CellDrift d CV V →
    ∫ y in B0579.cell d, w y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re =
      -(1 / 2) * ∫ y in B0579.cell d,
        (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y) * ‖Φ y‖ ^ 2

/-- **The rate after the integrations by parts** (SP 3060-3062): for `Ψ = adjPsi θ Φ χ V`,
`rate0 = rate0Reduced` (split `2∫ w Re(Φ̄Ψ)` into its four parts, apply `CellLapIBP` and
`CellTransportIBP`). -/
def CellRateReduce : Prop :=
  ∀ (m K CV d θ : ℝ) (Φ χ : ℝ × ℝ → ℂ) (V : ℝ × ℝ → Fin 2 → ℝ), 0 < d → 0 < θ →
    WeightHyp m K d → CellField m d Φ → CellDrift d CV V →
    AEStronglyMeasurable χ (volume.restrict (B0579.cell d)) →
    IntegrableOn (fun y => periodicWeight (-m) d y * ‖χ y‖ ^ 2) (B0579.cell d) →
    IntegrableOn (wRe m d Φ (adjPsi θ Φ χ V)) (B0579.cell d) →
    rate0 m d θ Φ (adjPsi θ Φ χ V) = rate0Reduced m d θ Φ χ V

/-- **The rate estimate** (SP 3062-3066: "the diffusion-weight errors have coefficient `C_m β`
and the transport and compact terms have coefficient `C_b`"): for `θ ≥ 1`,
`rate0Reduced + θ⁻¹ E_1 ≤ C E_0` with `C = C(K, C_V, C_X)` (Young on the cross term and on the
interaction term). -/
def CellRateEstimate : Prop :=
  ∀ (m K CV CX : ℝ), 0 ≤ K → 0 ≤ CV → 0 ≤ CX → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (d θ : ℝ) (Φ χ : ℝ × ℝ → ℂ) (V : ℝ × ℝ → Fin 2 → ℝ), 0 < d → 1 ≤ θ →
      WeightHyp m K d → CellField m d Φ → CellDrift d CV V →
      AEStronglyMeasurable χ (volume.restrict (B0579.cell d)) →
      IntegrableOn (fun y => periodicWeight (-m) d y * ‖χ y‖ ^ 2) (B0579.cell d) →
      ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖χ y‖ ^ 2 ≤ CX * adjE0 d m Φ →
      rate0Reduced m d θ Φ χ V + θ⁻¹ * adjE1 d m Φ ≤ C * adjE0 d m Φ

end UnforcedLeray.Short.IIIa.E0
