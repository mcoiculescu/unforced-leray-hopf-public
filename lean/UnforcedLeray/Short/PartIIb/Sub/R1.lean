import UnforcedLeray.Short.PartIIb.StatementsNonlinear
import UnforcedLeray.Short.PartIIa.StatementsRing

/-!
# Part II-b, task `PartII-b:R1`: the raw residual family (conditional)

Source of record: `the November 2 reference manuscript`, lines 2042-2046
(`‖F_R‖_{C_τ W^{1,p}} ≤ 𝒫_ν ε^{3/11}`, Part I `sct:residual-bound`, proof lines 1241-1336 of
Proposition `sct:lift`, `V_0 = U_raw` the solenoidal lift of the train), line 2519 and line 5200
of `paper/main.tex` (`g = 𝔓F_R`, `background:eq:2.15`).

Target (`StatementsNonlinear.lean`, not changed): `RawResidualFamily`, i.e. for every regime
`BgRegime p d dm dp` with `p.ν ≤ ν₀` there is `g : p.Y` with `p.RawRel g` and
`‖g‖ ≤ C (p.ν ^ k)⁻¹ p.ε ^ (3/11)`.

## Mathematical proof

Put `ψ, π` for the stream and pressure profiles of the actual train `p.train`, `R = p.R = ε⁻¹`,
`c = p.c = ν⁻²`, `F = ringResidual R ν ψ π` (the similarity residual `F_R` of
`PartII-a/StatementsRing.lean`).

1. (*Part I residual bound.*) `RingResidualBound` at `ρ = 2`, exponent `11/4` gives `F` periodic of
   period `2c/R = p.period` with `sup_τ ‖F(τ)‖_{L^{11/4}} ≤ C₁ (1 + c + ν⁻¹)^{d₁} ε^{3/11}`
   (`1 - 2/(11/4) = 3/11`), `F(τ)` continuous in `L^{11/4}`.
2. (*Weak identity.*) The lifted fields `U = U_raw`, `P` (similarity pressure) are `C^∞` across the
   axis, `div U = 0`, `F = L₀U + (U·∇)U + ∇P` off the axis (`RawResidualWeakIdentity`). Integrating
   by parts against solenoidal phase tests `Φ` (`τ`-periodicity, compact support in `y`,
   `div U = 0`, `div Φ = 0`) gives
   `⟪Φ, F⟫ = ⟪L₀ᵗΦ, U_raw⟫ - ⟪(U_raw·∇)Φ, U_raw⟫`, which is the right side of `RawRel`.
3. (*Leray projection.*) `g := 𝔓F` in the force space `Y_{q₀}` (real, solenoidal, `𝒪`-invariant
   since `F` is axisymmetric without swirl), `⟪Φ, 𝔓F⟫ = ⟪Φ, F⟫` for solenoidal `Φ`,
   `‖𝔓F‖_Y ≤ K sup_τ ‖F(τ)‖_{L^{q₀}}` with `K` independent of the period.
4. (*Constants.*) `1 + c + ν⁻¹ ≤ 3ν⁻²` for `ν ≤ 1`, so `k = 2 d₁`; `ν ≤ dm` and `d ≥ dm`
   give `R = e^{d/ν} ≥ e ≥ 2`.

Proved here, from the Props below: `lerayOfPeriodicLp_of` (steps 3, from `SliceFieldElem` and
`LerayOnForce`), `rawResidualWeakIdentity_of` (step 2, from `RawIsRingLift`, `RingLiftSmoothExt`,
`RingResidualCartesianNS`, `SmoothResidualWeakForm`), and `rawResidualFamily_of` (steps 1, 4).
The unconditional leaf lemmas are queued as tasks `PartII-b:R1/1 ... R1/8`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.Short.PartIIa

/-! ## The objects -/

/-- The stream profile `ψ` of the actual train of `p` (chart order `(q, η, s)`). -/
def trainStream (p : Params) : ProfilePoint → ℝ := UnforcedLeray.B0190.trainProfile p.train.ψ

/-- The pressure profile of the actual train of `p`. -/
def trainPressure (p : Params) : ProfilePoint → ℝ := UnforcedLeray.B0190.trainProfile p.train.p

/-- The similarity residual `F_R` of the raw lift of `p`, as a complex field on `ℝ × ℝ³`. -/
def rawResidualC (p : Params) (x : ℝ × Space) : CVec3 :=
  realC (ringResidual p.R p.ν (trainStream p) (trainPressure p) x.1 x.2)

/-! ## Step 3: the Leray projection of a periodic `L^{11/4}` field -/

/-- **Slice field as an element of `Y_{q₀}`** (SP 2042-2046, 5200): a `P`-periodic field
`F : ℝ → L^{11/4}(ℝ³;ℝ³)`, continuous in `L^{11/4}`, defines an element `f` of
`Y_{q₀} = L^{q₀}(ℝ/Pℤ; L^{q₀}(ℝ³;ℂ³))` (normalised Haar measure) whose pairing with every phase
test `Φ` is the period average `⟪Φ, F⟫ = P⁻¹∫₀ᴾ∫ Φ·F`, with `‖f‖ ≤ sup_τ ‖F(τ)‖_{L^{q₀}}`
(probability measure), `f` real (pairings with real tests are real) and, if every slice is
axisymmetric without swirl, `𝒪`-invariant. Lean: `Lib/PhaseSpace/Test.lean` (`testElem`,
`IsSliceTest`, `SliceCont`, `Yq`), `Units/B0412` (`phasePair`, `phasePairing_apply`). -/
def SliceFieldElem : Prop :=
  ∀ (p : Params) (F : ℝ → SpatialField),
    (∀ τ, F (τ + p.period) = F τ) →
    (∀ τ, MemLp (F τ) q0E volume) →
    (∀ τ₀, Tendsto (fun τ => (eLpNorm (F τ - F τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) →
    ∃ f : Yq p.period q0E,
      (∀ Φ, IsPhaseTest p.period Φ →
        phasePair p.period q0E Φ f = pairF p.period Φ (fun x => realC (F x.1 x.2))) ∧
      (∀ B : ℝ, (∀ τ, (eLpNorm (F τ) q0E volume).toReal ≤ B) → ‖f‖ ≤ B) ∧
      f ∈ realSub p.period q0E ∧
      ((∀ τ, IsAxisymmetricNoSwirl (F τ)) → f ∈ Osym p.period q0E)

/-- **Leray projection on the force space** (`B0414`, `B0421`, `B0415`; SP 5085, 5385): there is
`K > 0`, independent of the period, such that every real `𝒪`-invariant `f ∈ Y_{q₀}` has a
projection `g` in `p.Y = Y_{q₀,σ} ∩ {real} ∩ {𝒪-invariant}` with `‖g‖ ≤ K‖f‖` and
`⟪Φ, g⟫ = ⟪Φ, f⟫` for every solenoidal phase test `Φ`. Lean: `PhaseSpace.lerayY`,
`norm_lerayY_le`, `lerayY_isPhaseSolenoidal` (`Lib/LerayC/PhaseSol.lean`), `lerayY_actY`
(`Units/B0415/Commute.lean`), `Units/B0414/PhaseOrthogonal.lean`. -/
def LerayOnForce : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (p : Params) (f : Yq p.period q0E),
    f ∈ realSub p.period q0E → f ∈ Osym p.period q0E →
      ∃ g : p.Y, ‖g‖ ≤ K * ‖f‖ ∧ ∀ Φ, IsSolTest p.period Φ →
        phasePair p.period q0E Φ (g : Yq p.period q0E) = phasePair p.period q0E Φ f

/-- **The Leray step** (steps 3 above): a `P`-periodic field `F` with slices in `L^{11/4}`,
continuous in `L^{11/4}`, `sup_τ ‖F(τ)‖_{11/4} ≤ B` and axisymmetric without swirl has a projection
`g ∈ p.Y` with `⟪Φ, g⟫ = ⟪Φ, F⟫` for solenoidal phase tests and `‖g‖ ≤ K B`, `K` universal. -/
def LerayOfPeriodicLp : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (p : Params) (F : ℝ → SpatialField) (B : ℝ),
    (∀ τ, F (τ + p.period) = F τ) →
    (∀ τ, MemLp (F τ) q0E volume) →
    (∀ τ₀, Tendsto (fun τ => (eLpNorm (F τ - F τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) →
    (∀ τ, (eLpNorm (F τ) q0E volume).toReal ≤ B) →
    (∀ τ, IsAxisymmetricNoSwirl (F τ)) →
    ∃ g : p.Y, (∀ Φ, IsSolTest p.period Φ →
        phasePair p.period q0E Φ (g : Yq p.period q0E) =
          pairF p.period Φ (fun x => realC (F x.1 x.2))) ∧
      ‖g‖ ≤ K * B

theorem lerayOfPeriodicLp_of (h₁ : SliceFieldElem) (h₂ : LerayOnForce) : LerayOfPeriodicLp := by
  obtain ⟨K, hK, H⟩ := h₂
  refine ⟨K, hK, fun p F B hper hmem hcont hB hax => ?_⟩
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := h₁ p F hper hmem hcont
  obtain ⟨g, hg1, hg2⟩ := H p f hf3 (hf4 hax)
  refine ⟨g, fun Φ hΦ => ?_, ?_⟩
  · rw [hg2 Φ hΦ, hf1 Φ hΦ.1]
  · exact hg1.trans (mul_le_mul_of_nonneg_left (hf2 B hB) hK.le)

/-- The ring residual is axisymmetric without swirl (it is `A(ϱ, y₃) e_r + B(ϱ, y₃) e_z` after the
dilation `y ↦ e^{τ/2} y`; `Axi.liftMer`, `physResidualField`, `Lib/AxisymmetricB/Unitary.lean`). -/
def RingResidualAxisymmetric : Prop :=
  ∀ (R ν : ℝ) (ψ pr : ProfilePoint → ℝ) (τ : ℝ),
    IsAxisymmetricNoSwirl (ringResidual R ν ψ pr τ)

/-! ## Step 2: the weak identity for `U_raw` -/

/-- **`U_raw` is the ring lift of the train** (SP 1196-1338, `eq:m3-ring-lift`; B0186, B0190):
off the axis, `p.raw τ y = simProfile 1 (liftVelocity R ψ) τ y` for `R = ε⁻¹`, `ψ` the stream of
the actual train, which is the BUC train of Part I (SP 270-288, 2040; `PartI.IsBUCTrain`, the
field `train_buc` of `BgRegime`). Lean: `Cons.C03.Concrete.Params.raw_eq_off_axis`,
`B0190.simProfile_liftVelocity_eq_Nv`, `Cons/C03Background/RawLift.lean`. -/
def RawIsRingLift : Prop :=
  ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → ∀ (τ : ℝ) (y : Space), Axi.ϱ y ≠ 0 →
    p.raw τ y = UnforcedLeray.B0190.simProfile 1 (UnforcedLeray.B0185.liftVelocity p.R (trainStream p)) τ y

/-- **Smooth extension of the similarity lift** (SP 1214, 1305-1322, 1243-1246, 1315-1318:
`RingAxisSmooth`, `RingSolenoidal`, `RingDSS`): for `ν < ν₀`, `c = ν⁻²`, `R ≥ 2`, the similarity
velocity `U` and pressure `P` of the lift agree off the axis with `C^∞` functions on `ℝ × ℝ³`
(`U(τ, y) = e^{τ/2}u(e^τ, e^{τ/2}y)`, `P = e^τ π(e^τ, e^{τ/2}y)`), `U` is `2c/R`-periodic in `τ`
and `div_y U = 0`. -/
def RingLiftSmoothExt : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : ProfilePoint → ℝ,
    IsExactPlanarTrain ν (ν ^ (-(2 : ℝ))) ψ pr → ∀ R : ℝ, 2 ≤ R →
      ∃ (U : ℝ × Space → CVec3) (Pw : ℝ × Space → ℂ),
        ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ Pw ∧
        (∀ x : ℝ × Space, U (x.1 + 2 * ν ^ (-(2 : ℝ)) / R, x.2) = U x) ∧
        (∀ x : ℝ × Space, ∑ j : Fin 3, dy j U x j = 0) ∧
        ∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 →
          U x = realC (UnforcedLeray.B0190.simProfile 1
            (UnforcedLeray.B0185.liftVelocity R ψ) x.1 x.2) ∧
          Pw x = ((UnforcedLeray.B0190.simProfile 2
            (UnforcedLeray.B0185.liftPressure R pr) x.1 x.2 : ℝ) : ℂ)

/-- **The residual of the lift is the Cartesian Navier-Stokes residual** (SP 1263, the formula
`F_R = s^{3/2} r`; `B0187`, `Lib/Axisymmetric/Cylindrical.lean` `liftMerD`; INF23): for any `C^∞`
`U`, `P` agreeing off the axis with the similarity lift of an exact train, at every point off the
axis `F_R = L₀U + (U·∇)U + ∇P` with `L₀ = T₀ - νΔ - ½` (`B0411.L0`), i.e.
`e^{3τ/2}(∂_t u + u·∇u - νΔu + ∇π)(e^τ, e^{τ/2}y)`. Stated for `ν, c > 0`, the source regime
(SP 261-288: the BUC train of viscosity `ν > 0` is smooth for positive time); the consumer
`rawResidualWeakIdentity_of` supplies `p.ν_pos`, `p.c_pos`. -/
def RingResidualCartesianNS : Prop :=
  ∀ (ν c R : ℝ) (ψ pr : ProfilePoint → ℝ), 0 < ν → 0 < c → 2 ≤ R → IsExactPlanarTrain ν c ψ pr →
    ∀ (U : ℝ × Space → CVec3) (Pw : ℝ × Space → ℂ), ContDiff ℝ ∞ U → ContDiff ℝ ∞ Pw →
      (∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 →
        U x = realC (UnforcedLeray.B0190.simProfile 1
          (UnforcedLeray.B0185.liftVelocity R ψ) x.1 x.2) ∧
        Pw x = ((UnforcedLeray.B0190.simProfile 2
          (UnforcedLeray.B0185.liftPressure R pr) x.1 x.2 : ℝ) : ℂ)) →
      ∀ (τ : ℝ) (y : Space), Axi.ϱ y ≠ 0 →
        realC (ringResidual R ν ψ pr τ y) =
          L0 ν U (τ, y) + advT U U (τ, y) + gradT Pw (τ, y)

/-- **The integration by parts** (`Units/B0411/Operators.lean` Lagrange identities): for a `C^∞`
`P`-periodic divergence-free `U`, a `C^∞` scalar `Pw` and a field `Fc` equal to
`L₀U + (U·∇)U + ∇Pw` off the axis, and any `U'` equal to `U` off the axis (the axis is a null set),
`⟪Φ, Fc⟫ = ⟪L₀ᵗΦ, U'⟫ - ⟪(U'·∇)Φ, U'⟫` for every solenoidal phase test `Φ`. -/
def SmoothResidualWeakForm : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ (U : ℝ × Space → CVec3) (Pw : ℝ × Space → ℂ),
    ContDiff ℝ ∞ U → ContDiff ℝ ∞ Pw →
    (∀ x : ℝ × Space, U (x.1 + P, x.2) = U x) →
    (∀ x : ℝ × Space, ∑ j : Fin 3, dy j U x j = 0) →
    ∀ (U' Fc : ℝ × Space → CVec3),
      (∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 →
        U' x = U x ∧ Fc x = L0 ν U x + advT U U x + gradT Pw x) →
      ∀ Φ, IsSolTest P Φ →
        pairF P (L0T ν Φ) U' - pairF P (advT U' Φ) U' = pairF P Φ Fc

/-- **The weak identity for the raw residual** (SP 2042-2046, `paper/main.tex` 5200): for
`ν < ν₀`, `c = ν⁻²`, `R ≥ 2`, and every solenoidal phase test `Φ`,
`⟪L₀ᵗΦ, U_raw⟫ - ⟪(U_raw·∇)Φ, U_raw⟫ = ⟪Φ, F_R⟫`, for the BUC train of Part I (SP 270-288, 2040). -/
def RawResidualWeakIdentity : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ → p.c = (p.ν ^ 2)⁻¹ →
    2 ≤ p.R →
    ∀ Φ, IsSolTest p.period Φ →
      pairF p.period (L0T p.ν Φ) p.Ufun - pairF p.period (advT p.Ufun Φ) p.Ufun =
        pairF p.period Φ (rawResidualC p)

/-- `c = (ν²)⁻¹` is `ν ^ (-2)` as a real power. -/
theorem inv_sq_eq_rpow_neg_two {ν : ℝ} (hν : 0 < ν) : (ν ^ 2)⁻¹ = ν ^ (-(2 : ℝ)) := by
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- The actual train of `p`, when it is the BUC train, is an exact planar train at `c = p.c`. -/
theorem isExactPlanarTrain_params (p : Params) (hb : UnforcedLeray.Short.PartI.IsBUCTrain p.train) :
    IsExactPlanarTrain p.ν p.c (trainStream p) (trainPressure p) :=
  ⟨p.train, hb, rfl, rfl⟩

/-- Under `c = (ν²)⁻¹`, the actual train is an exact planar train at `c = ν ^ (-2)`. -/
theorem isExactPlanarTrain_params_rpow (p : Params) (hb : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hc : p.c = (p.ν ^ 2)⁻¹) :
    IsExactPlanarTrain p.ν (p.ν ^ (-(2 : ℝ))) (trainStream p) (trainPressure p) := by
  rw [← inv_sq_eq_rpow_neg_two p.ν_pos, ← hc]
  exact isExactPlanarTrain_params p hb

/-- The period `2 ν^{-2}/R` is `p.period` when `c = (ν²)⁻¹`. -/
theorem period_eq_rpow (p : Params) (hc : p.c = (p.ν ^ 2)⁻¹) :
    2 * p.ν ^ (-(2 : ℝ)) / p.R = p.period := by
  rw [← inv_sq_eq_rpow_neg_two p.ν_pos, ← hc]
  exact p.period_eq.symm

theorem rawResidualWeakIdentity_of (h₁ : RawIsRingLift) (h₂ : RingLiftSmoothExt)
    (h₃ : RingResidualCartesianNS) (h₄ : SmoothResidualWeakForm) : RawResidualWeakIdentity := by
  obtain ⟨ν₀, hν₀, H⟩ := h₂
  refine ⟨ν₀, hν₀, fun p hb hν hc hR Φ hΦ => ?_⟩
  obtain ⟨U, Pw, hU, hPw, hper, hdiv, hext⟩ :=
    H p.ν ⟨p.ν_pos, hν⟩ (trainStream p) (trainPressure p)
      (isExactPlanarTrain_params_rpow p hb hc) p.R hR
  refine h₄ p.period p.ν p.period_pos U Pw hU hPw
    (fun x => by rw [← period_eq_rpow p hc]; exact hper x) hdiv p.Ufun (rawResidualC p) ?_ Φ hΦ
  intro x hx
  refine ⟨?_, ?_⟩
  · show realC (p.raw x.1 x.2) = U x
    rw [(hext x hx).1, h₁ p hb x.1 x.2 hx]
  · exact h₃ p.ν p.c p.R (trainStream p) (trainPressure p) p.ν_pos p.c_pos hR
      (isExactPlanarTrain_params p hb) U Pw hU hPw hext x.1 x.2 hx

/-- `q₀ = 11/4` as a Lebesgue exponent is `ENNReal.ofReal (11/4)`. -/
theorem q0E_eq_ofReal : q0E = ENNReal.ofReal (11 / 4) := rfl

/-- `1 + c + ν⁻¹ ≤ 3 (ν²)⁻¹` for `0 < ν ≤ 1`, `c = (ν²)⁻¹`. -/
theorem one_add_inv_le {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    1 + ν ^ (-(2 : ℝ)) + ν⁻¹ ≤ 3 * (ν ^ 2)⁻¹ := by
  rw [← inv_sq_eq_rpow_neg_two hν]
  have h1 : 1 ≤ (ν ^ 2)⁻¹ := by
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  have h2 : ν⁻¹ ≤ (ν ^ 2)⁻¹ := by
    rw [inv_le_inv₀ hν (by positivity)]
    nlinarith
  linarith

theorem rawResidualFamily_of (h₁ : RingResidualBound) (h₂ : RawResidualWeakIdentity)
    (h₃ : LerayOfPeriodicLp) (h₄ : RingResidualAxisymmetric) : RawResidualFamily := by
  intro dm dp hdm
  obtain ⟨ν₁, hν₁, C₁, d₁, H1⟩ := h₁ 2 (11 / 4) (by norm_num) (by norm_num)
  obtain ⟨ν₂, hν₂, H2⟩ := h₂
  obtain ⟨K, hK, H3⟩ := h₃
  have hC₁ : 0 < max C₁ 1 := lt_max_of_lt_right one_pos
  refine ⟨K * max C₁ 1 * 3 ^ d₁, 2 * d₁, min (min (ν₁ / 2) (ν₂ / 2)) (min 1 dm), by positivity,
    lt_min (lt_min (by linarith) (by linarith)) (lt_min one_pos hdm), ?_⟩
  intro p d hreg hν
  have hνpos := p.ν_pos
  have hν1 : p.ν < ν₁ :=
    lt_of_le_of_lt (hν.trans ((min_le_left _ _).trans (min_le_left _ _))) (by linarith)
  have hν2 : p.ν < ν₂ :=
    lt_of_le_of_lt (hν.trans ((min_le_left _ _).trans (min_le_right _ _))) (by linarith)
  have hν3 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν4 : p.ν ≤ dm := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hR : 2 ≤ p.R := by
    have hd : 1 ≤ d / p.ν := by
      rw [le_div_iff₀ hνpos]
      linarith [hreg.dm_le]
    have hR' : p.R = Real.exp (d / p.ν) := by
      rw [Params.R, hreg.eps_eq, neg_div, Real.exp_neg, inv_inv]
    rw [hR']
    have := Real.add_one_le_exp (d / p.ν)
    linarith
  obtain ⟨hper, G, hmem, hG, hbd, hcont⟩ :=
    H1 p.ν ⟨hνpos, hν1⟩ (trainStream p) (trainPressure p)
      (isExactPlanarTrain_params_rpow p hreg.train_buc hc) p.R hR
  set B₀ : ℝ := polyConst C₁ d₁ p.ν (p.ν ^ (-(2 : ℝ))) * (p.R⁻¹) ^ (1 - 2 / (11 / 4 : ℝ))
    with hB₀
  obtain ⟨g, hg1, hg2⟩ := H3 p (ringResidual p.R p.ν (trainStream p) (trainPressure p)) B₀
    (fun τ => by rw [← period_eq_rpow p hc]; exact hper τ)
    (fun τ => by rw [q0E_eq_ofReal]; exact hmem τ)
    (fun τ₀ => by
      rw [q0E_eq_ofReal]
      refine squeeze_zero (fun τ => ENNReal.toReal_nonneg) (fun τ => ?_) (hcont τ₀)
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg))
    (fun τ => by
      rw [q0E_eq_ofReal]
      refine le_trans ?_ (hbd τ)
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg))
    (fun τ => h₄ _ _ _ _ τ)
  refine ⟨g, fun Φ hΦ => ?_, ?_⟩
  · rw [hg1 Φ hΦ]
    exact (H2 p hreg.train_buc hν2 hc hR Φ hΦ).symm
  · refine hg2.trans ?_
    have hε : p.R⁻¹ = p.ε := by rw [Params.R, inv_inv]
    have hex : (1 : ℝ) - 2 / (11 / 4 : ℝ) = 3 / 11 := by norm_num
    have hE : 0 ≤ p.ε ^ (3 / 11 : ℝ) := Real.rpow_nonneg p.ε_pos.le _
    have hX : (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ ≤ 3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹) := by
      calc (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ ≤ (3 * (p.ν ^ 2)⁻¹) ^ d₁ := by
            apply pow_le_pow_left₀ (by positivity) (one_add_inv_le hνpos hν3)
        _ = 3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹) := by
            rw [mul_pow, inv_pow, ← pow_mul]
    have hXn : 0 ≤ (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ := by
      apply pow_nonneg
      have : 0 < p.ν ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hνpos _
      have : 0 < p.ν⁻¹ := inv_pos.2 hνpos
      linarith
    rw [hB₀, hε, hex, polyConst]
    calc K * (C₁ * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ * p.ε ^ (3 / 11 : ℝ))
        ≤ K * (max C₁ 1 * (3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹)) * p.ε ^ (3 / 11 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply mul_le_mul_of_nonneg_right _ hE
          calc C₁ * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁
              ≤ max C₁ 1 * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hXn
            _ ≤ max C₁ 1 * (3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹)) :=
                mul_le_mul_of_nonneg_left hX hC₁.le
      _ = K * max C₁ 1 * 3 ^ d₁ * (p.ν ^ (2 * d₁))⁻¹ * p.ε ^ (3 / 11 : ℝ) := by ring

end UnforcedLeray.Short.IIb
