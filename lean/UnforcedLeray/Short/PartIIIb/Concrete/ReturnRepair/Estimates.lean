import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIa.StressSpaces

/-!
# The repair estimates on the concrete sequence and `ErrorFamilyBounds` (source 5111-5707)

Source of record: `the November 2 reference manuscript` (73 pages).

For `S = concreteReturnSeq D G` (`Concrete/ReturnInst.lean`) the error velocity of
`repair:complete-graph-error` is (source 5670-5671, 5807; `ReturnOps.vQ`)
`v_Q(T) = S_far T + Y[T] + R_μ(E[T] - E_{𝓛T} - 𝔯_{𝓛T})`.
The proof of the proposition (5687-5697) splits it exactly as follows, with `T = (T₁, T₂) = M_Uw`
(thin and repair components, 5377-5379):

* `S_far T + Y[T]` (`ageVel`): the early-source and late-output regions and the two stream
  transitions — `repair:age-error` (5301-5372) for the stress and the velocity bounds 5569-5605;
* the repair response `E[(0,T₂)]` — `repair:body-error` (5196-5299);
* the thin response `E[(T₁,0)] - E_{𝓛T}` — `repair:thin-complete` (5374-5506);
* the final subtraction `𝔯_{𝓛T}` — `repair:actual-affine-remainder` (5507-5525);

and `R_μ` maps body forces back with `‖g⁻¹M_UR_μf‖_Z ≤ P_νR⁻¹‖f‖_{Y_2}`,
`R⁻¹‖g⁻¹R_μf‖_{Y_2} ≤ P_νR⁻¹‖f‖_{Y_2}` (5540-5547, 5621-5622).  Thin sources are measured by
`A = ‖g⁻¹T‖_Z`, repair sources by `G(w)` (5622-5623).

## Contents

* `thinPart`, `repPart` : `(T₁, 0)` and `(0, T₂)` on `StrG`; `thinPart_add_repPart`.
* Regime objects: `ageVel` (`S_far + Y`), `gaugeN` (`|N_ν|`), `rhoRep` (`ρ = ε^{3/11}e^{m₀/ν}`),
  `oldN1` (`N = N₁(χ_oT₁)`, `IIIa.firstMoment`), `repSrcTen`, `repStressPhys`, `repX`, `repY`
  (the old repair source `χ_o(r_b⊗w + w⊗r_b)` and its Ward fields), `phaseL2Lr`, `phaseSupLr`
  (`L²_τL^r_y`, `L^∞_τL^r_y`), `vecLap`, `YmtFun`, `Bjet`, `clockJet` (the Newton jet clock).
* The numbered estimates at one regime (`…At`) and along the sequence (`SeqData.…`):
  `RepairSource` (5169-5176), `PhaseGradient` (5203-5223), `BodyError` (5196-5299),
  `AgeError` (5301-5372 with 5607-5627), `AgeVelocity` (5569-5605, 5618-5619), `ActualJet`
  (5400-5413), `JetClock` (5449-5458), `ThinComplete` (5484-5506), `AffineRemainder`
  (5507-5525); the inputs `ThinMoment` (5163-5167, 5527) and `NearBody` (5540-5547, 5621-5622);
  the gain-band forms `BodyRepairMargin`, `ThinBodyMargin`, `AffRemMargin` (5527-5531,
  5557-5567, 5614-5627).
* **`errorFamilyBounds_of`** (proved): `ErrorFamilyBounds S γ ω_b m₀` from `AgeError`,
  `AgeVelocity`, the three margin forms, `NearBody` and the invertibility of the near layer.

All bounds are for large `n` (`∀ᶠ n`) and every `z ∈ [-1,1]` (`μ = μ_n(z)`), with constants
`C ν^{-k}` (`P_ν`) uniform in `n` and `z` (source 5124-5131).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Thin and repair parts of a stress -/

section Parts

variable {c mZ ρb γ ν : ℝ}

/-- The thin part `(T₁, 0)` of `T = (T₁, T₂) ∈ Z = Z₁ ⊕ ρ_b^{-1/2}H_T` (source 5377-5379). -/
def thinPart : StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
      (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.inl ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
        (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).comp
      (ContinuousLinearMap.fst ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
        (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)))).comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
        (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).toContinuousLinearMap)

/-- The repair part `(0, T₂)` of `T = (T₁, T₂)` (source 5377-5379). -/
def repPart : StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
      (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.inr ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
        (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).comp
      (ContinuousLinearMap.snd ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
        (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)))).comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
        (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).toContinuousLinearMap)

theorem thinPart_add_repPart (T : StrG c mZ ρb γ ν) : thinPart T + repPart T = T := by
  apply (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).injective
  rw [map_add]
  simp only [thinPart, repPart, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Prod.mk_add_mk, add_zero, zero_add]

end Parts

/-! ## 2. Mixed phase norms -/

/-- `‖F‖_{L²_τ L^r_y}` over one period `P` with the normalized phase measure `dτ/P`, Frobenius
norm (source 5171: the repair source class `L²_τL^{22/19}`). -/
def phaseL2Lr (P r : ℝ) (F : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P,
    (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (F (t, y))) ^ r) ^ (2 / r)) ^
    (1 / 2 : ℝ)

/-- `‖f‖_{L^∞_τ L^r_y}` over one period `P` (source 5214-5217). -/
def phaseSupLr (P r : ℝ) (f : ℝ × Space → ℝ) : ℝ≥0∞ :=
  essSup (fun t => (∫⁻ y : Space, ENNReal.ofReal |f (t, y)| ^ r) ^ (1 / r))
    (volume.restrict (Ioc (0 : ℝ) P))

/-! ## 3. The objects of one regime -/

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `S_far T + Y[T] = (S_μ - S_N)T + Y[T]` (source 5303-5316, 5688-5689): the early-source and
late-output regions of the far mask and the two stream transitions. -/
def ageVel : LStr Pl K L →L[ℝ] LVel Pl L :=
  (Sop Pl K L μ - SNop Pl K L μ) + (wardOps Pl K L μ).1

/-- `|N_ν| = |e^{λ/ν}ν^{-κ}|` (source 5118). -/
def gaugeN : ℝ := ‖Nnu Pl.eigenvalue Pl.kappa L.ν‖

/-- `ρ = ε^{3/11}e^{m₀/ν}` (source 5138). -/
def rhoRep : ℝ := L.ε ^ (3 / 11 : ℝ) * Real.exp (K.m0 / L.ν)

/-- `N = N₁(χ_oT₁)`, the age-weighted first transverse moment of the old thin source
(source 5400, SP 2747-2752 `IIIa.firstMoment`), `χ_o(s) = χ̂_o(νs)`. -/
def oldN1 (T : LStr Pl K L) : ℝ≥0∞ :=
  UnforcedLeray.Short.IIIa.firstMoment (cOf L.ν) 0 (fun p => K.χo (L.ν * p.1) • thinRep T p)

/-- The old repair source `χ_oT₂` of `T = M_Uw` as a chart tensor (source 5153-5157: the old
source includes the repair). -/
def repSrcTen (w : LVel Pl L) : Chart → Ten3 :=
  ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (multOp Pl K L w)).snd :
    Chart → Ten3)

/-- The physical old repair stress `χ_o(r_b ⊗ w + w ⊗ r_b)` (source 5171), the lift `𝒩_T` of
`repSrcTen`. -/
def repStressPhys (w : LVel Pl L) : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ :=
  strPhys L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w)

/-- `X` for the old repair source (source 5155-5157, 5203-5210). -/
def repX (w : LVel Pl L) : ℝ → Space → Space :=
  wardX L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (repSrcTen Pl K L w)

/-- `Y = D_{μ+1}X` for the old repair source. -/
def repY (w : LVel Pl L) : ℝ → Space → Space :=
  wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (repSrcTen Pl K L w)

end Regime

/-- `Δ_y X = Σ_j ∂_j∂_jX` for fields on `Vec3`. -/
def vecLap (X : Vec3 → Vec3) (y : Vec3) : Vec3 :=
  ∑ j : Fin 3, fderiv ℝ (fun y' => fderiv ℝ X y' (Pi.single j 1)) y (Pi.single j 1)

/-- `Y^mt = D_{μ+1}X^mt = (-½y·∇ - νΔ + μ + ½)X^mt` for the phase-independent Newton field
(source 5380-5382, 5455). -/
def YmtFun (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (y : Vec3) : Vec3 :=
  -(1 / 2 : ℝ) • fderiv ℝ (Xmt c ν ε μ χo χy M) y y - ν • vecLap (Xmt c ν ε μ χo χy M) y +
    (μ + 1 / 2) • Xmt c ν ε μ χo χy M y

/-- `B_j(s) = s⁻¹D_yY^mt(R/√s, 0, 0)` (source 5446), `(D_yY)_{ij} = ∂_jY_i`. -/
def Bjet (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (s : ℝ) : Mat3 :=
  fun i j => s⁻¹ * fderiv ℝ (YmtFun c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i

/-- The clock term `(ν/s)D_yΔ_yX^mt(R/√s, 0, 0)` (source 5451). -/
def clockJet (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (s : ℝ) : Mat3 :=
  fun i j => (ν / s) * fderiv ℝ (vecLap (Xmt c ν ε μ χo χy M)) ![ε⁻¹ / Real.sqrt s, 0, 0]
    (Pi.single j 1) i

/-! ## 3a. The standing hypotheses of the repair section

The estimates concern the operators of `Concrete/ReturnInst.lean`, each defined as the operator with
its source pin (`Classical.epsilon`); `RegimePins` is the existence of the pinned operators at a
regime (the hypotheses of the `…_spec` lemmas of `ReturnInst.lean`), supplied by the
`ORG:return-concrete/instance-3/*` items.  `SeqData.RepairStanding` collects the standing
hypotheses of the module (source 5115-5146, 5150-5160, 5303-5306, 5835-5859, 5926-5950). -/

/-- The pinned operators of the regime exist (source 5777-5833): the split multiplier `M_U`
(2706, 3877-3878), the actual near operators (3866-3914), the stress inverse `S_μ = R_μℙdiv`
(4145, 1556-1572), the real form of the body inverse (1675-1677), the Ward fields (4161-4303), `𝓛`
(4792-4796), the affine fields `ĥ_A, F_A, E_A` (4969-4985), the residual `𝔯_A` (5001-5050) and the
real row `Λ_{μ,ν}` (4812-4815). -/
structure RegimePins (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) : Prop where
  split : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
    NearInst.IsSplitMult M (L.params Pl).R L.V L.rb
  near : ∃ o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K),
    NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o
  stress : ∃ S : LStr Pl K L →L[ℝ] LVel Pl L, IsWeakStressInverse S L.ε μ
  body : ∃ R : Hsp (cOf L.ν) →L[ℝ] Hsp (cOf L.ν), NearInst.IsBodyTransport R
    (UnforcedLeray.Short.PartIIa.Teps (P := (L.params Pl).period) (L.params Pl).ν_pos
      (L.params Pl).ε_pos (L.params Pl).c_pos rfl (μ : ℂ))
  ward : ∃ t : (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LVel Pl L) ×
      (LStr Pl K L →L[ℝ] LSrc L), IsWardTriple t.1 t.2.1 t.2.2 L.ε μ K.hχo K.χy L.U L.pres
  lj : ∃ Lj : LStr Pl K L →L[ℝ] AffSp K.as, ∀ T, affIota K.as (Lj T) =
    LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T
  hA : ∃ H : AffSp K.as →L[ℝ] LVel Pl L, ∀ A,
    (H A : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
      hAcoef L.ν L.ε K.χf (affIota K.as A)
  fA : ∃ F : AffSp K.as →L[ℝ] LSrc L, ∀ A,
    (F A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)] FAcoef L.ν μ K.χf (affIota K.as A)
  eA : ∃ E : AffSp K.as →L[ℝ] LSrc L, ∀ A,
    (E A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)] EAcoef L.ν μ K.χf (affIota K.as A)
  rA : ∃ r : AffSp K.as →L[ℝ] LSrc L, IsRAOp (multOp Pl K L) (hAOp Pl K L) (FAOp K L μ)
    (EAOp K L μ) r (affIota K.as) K.χf L.ε μ
  lam : ∃ l : AffSp K.as →L[ℝ] ℝ, ∀ A, l A =
    LamFun Pl.eigenvalue Pl.kappa Pl.strainCoupling (planarJ Pl) L.ε L.ν μ K.χf (affIota K.as A)

/-- `‖F‖_{Y_r}`: the phase-normalized `L^r` norm over `(0, P] × ℝ³` of a scalar density
(source 5134-5139, SP 1341-1344). -/
def phaseLr (P r : ℝ) (F : ℝ × Space → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r) ^
    (1 / r)

/-- The derivative bounds of the repair (source 5134-5139: `‖r_b‖_{W^{1,∞}} +
Σ_{j=1}^2 ‖D^jr_b‖_{Y_{11/4}} ≤ P_νρ`, `ρ = ε^{3/11}e^{m₀/ν}`; the `C_τL^{11/4}` and `L^∞` parts are
the field `energy` of `IIb.ExactSplitII`), at level `L` with constants `C ν^{-k}`. -/
def RepairDerivBound (K : ReturnConsts) (L : ReturnLevel) (C : ℝ) (k : ℕ) : Prop :=
  (∀ τ (y : Space), ‖fderiv ℝ (L.rb τ) y‖ ≤ C * L.ν⁻¹ ^ k * rhoRep K L) ∧
  phaseLr (2 * L.ε * cOf L.ν) (11 / 4) (fun x => ‖fderiv ℝ (L.rb x.1) x.2‖) ≤
    ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L) ∧
  phaseLr (2 * L.ε * cOf L.ν) (11 / 4)
      (fun x => ‖fderiv ℝ (fun y => fderiv ℝ (L.rb x.1) y) x.2‖) ≤
    ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L)

/-- **The standing hypotheses of the repair section for the concrete sequence** (source 5115-5146,
5150-5160, 5303-5306, 5835-5859, 5926-5950): the planar reference with `γ = Re λ > 0`, `ω ≠ 0`,
`σ₀ ∈ (0, 1/4)`; the fixed choices (`m_Z > 3/2`, `C₀ > 0`, output cut `0 < b < 1`, gap
`0 < δ < log(12/11)`, `0 < m₀ < 3d₋/11`, `2m₀ < 3d₋/11` (the contraction condition of
`short-bg:result`, 2510-2512, which the background construction meets with `m = m₀`: 4064-4068,
5851-5856), `m₀ < γ/1000` (5851-5854), `0 < a_s < γ/16` (4738-4740, 5878-5880), the stream and
source cutoff profiles); for large
`n` the level is actual (`IsActualLevel`: regime, exact split, exact profile), the inlet support
lies below the output cut `S = ε^{-b}`, the repair has the derivative bounds of 5134-5139, the pinned
operators exist on the window and the near layer is invertible there. -/
structure SeqData.RepairStanding (D : SeqData) (dm dp : ℝ) : Prop where
  planar : UnforcedLeray.Blueprint.Planar.IsPlanarReference D.Pl
  gamma_pos : 0 < gRate D.Pl
  omega_ne : D.Pl.eigenvalue.im ≠ 0
  sigma_pos : 0 < D.σ₀
  sigma_lt : D.σ₀ < 1 / 4
  dm_pos : 0 < dm
  mZ_gt : 3 / 2 < D.K.mZ
  C0_pos : 0 < D.K.C0
  b_pos : 0 < D.K.b
  b_lt : D.K.b < 1
  δ_pos : 0 < D.K.δ
  δ_lt : D.K.δ < Real.log (12 / 11)
  m0_pos : 0 < D.K.m0
  m0_lt : D.K.m0 < 3 * dm / 11
  /-- The contraction condition `2m < 3d₋/11` of `short-bg:result` (source 2510-2512: "This holds
  after decreasing `m` so `2m < 3d₋/11`") with `m = m₀`: the return's background is that
  construction realizing the prescribed `m₀` (source 4064-4068, 5851-5856: "The background
  construction realizes this `m₀`"; `ρ_b = P_ν ε^{3/11} e^{m₀/ν}`, 2701-2706). It is a fixed choice
  of the source: `m₀ < min{ϑd₀/16, γ/1000}` with `ϑ ≤ 3/22` (5851-5854). -/
  m0_ball : 2 * D.K.m0 < 3 * dm / 11
  m0_small : D.K.m0 < gRate D.Pl / 1000
  as_pos : 0 < D.K.as
  /-- The source choice of the exponential weight `a_s` of `𝒜` (source 4738-4740: "Choose
  `a_s<γ/16`"; restated in the closure, 5878-5880: `a_s<γ/16`). It is the budget of the Laplace
  integrand `t^{μ+3/2}e^{-(γ-a_s)t}` of the flat limit (4912); `SeqData.RepairStanding.as_lt_gamma`
  gives the form `a_s < γ = Re λ`. -/
  as_lt : D.K.as < gRate D.Pl / 16
  chiY : IsStreamCutoff D.K.χy
  chiF : IsSourceCutoffC D.K.χf
  actual : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n
  inlet : ∀ᶠ n : ℕ in atTop, D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b)
  repairDeriv : ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, RepairDerivBound D.K (D.level n) C k
  pins : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, RegimePins D.Pl D.K (D.level n) (D.mu n z)
  near : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z)
  /-- The flat near operator `D₀` is a unit on the window (source 3874-3887 `near:flat-bound`,
  3943-3951 `near:inverse-comparison`, 3560-3581 `D₀⁻¹ = I - M₀ S_lin`): needed so that the column
  pin about realizations with `IsUnit o.D0` speaks about `D.flat n` (flat limit, G5/G6). -/
  flatUnit : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    IsUnit (nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).D0

/-- `a_s < γ = Re λ`, from the source choice `a_s < γ/16` (source 4739, 5880) and `γ > 0`: the
Laplace integral `∫₀^∞ t^{μ+3/2}e^{-(γ-a_s)t} dt` of the flat limit converges (source 4912). -/
theorem SeqData.RepairStanding.as_lt_gamma {D : SeqData} {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.K.as < D.Pl.eigenvalue.re := by
  have h : D.K.as < gRate D.Pl := by linarith [hst.as_lt, hst.gamma_pos]
  exact h

/-! ## 4. The numbered estimates at one regime

`C ν^{-k}` is the source's `P_ν`; `γ = Re λ`; norms are those of `LVel` (`G`), `LStr` (`A`),
`LSrc` (`R⁻¹‖·‖_{Y_2}`), see `Concrete/ReturnOps.lean`. -/

section Estimates

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **`repair:source`** (source 5169-5176): `F_r = ‖χ_o(r_b⊗w + w⊗r_b)‖_{L²_τL^{22/19}} ≤
P_ν ρ R |N_ν| G(w)`, period `P = 2εc`. -/
def RepairSourceAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ w : LVel Pl L, phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) ≤
    ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖)

/-- **`repair:phase-gradient`** (source 5203-5223): for the old repair source,
`‖DX‖_{L^∞_τL^{22/3}} + ‖DY‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{46/11} F_r`. -/
def PhaseGradientAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ w : LVel Pl L,
    phaseSupLr (2 * L.ε * cOf L.ν) (22 / 3) (fun x => ‖fderiv ℝ (repX Pl K L μ w x.1) x.2‖) +
        phaseSupLr (2 * L.ε * cOf L.ν) (22 / 3) (fun x => ‖fderiv ℝ (repY Pl K L μ w x.1) x.2‖) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (46 / 11 : ℝ)) *
        phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w)

/-- **`repair:body-error`** (source 5196-5299; "the repair response", 5691-5692): the full
unprojected Ward residual of the old repair source on the exact background with its exact
pressure, `R⁻¹‖f_r‖_{Y_2} ≤ P_ν|N_ν|G(w)(ε^{85/22}e^{m₀/ν} + ε^{52/11}e^{2m₀/ν})`. -/
def BodyErrorAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ w : LVel Pl L, ‖(wardOps Pl K L μ).2.2 (repPart (multOp Pl K L w))‖ ≤
    C * L.ν⁻¹ ^ k * gaugeN Pl L *
      (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) +
        L.ε ^ (52 / 11 : ℝ) * Real.exp (2 * K.m0 / L.ν)) * ‖w‖

/-- **`repair:age-error`** (source 5301-5372), in the split form of the closure (5607-5627:
"their thin source bounds use `A`, whereas the repair source bounds use `G(w)`"):
`‖g⁻¹M_U(S_far + Y)(T₁,0)‖_Z ≤ P_ν e^{-(γ/15-ω_b-3m₀/2)/ν} A` and
`‖g⁻¹M_U(S_far + Y)(0,T₂)‖_Z ≤ P_ν e^{-(19γ/66-ω_b-3m₀/2)/ν} G(w)` for `T = M_Uw`,
`ω_b = kbd₀` (5607). -/
def AgeErrorAt (ωb C : ℝ) (k : ℕ) : Prop :=
  (∀ T : LStr Pl K L, ‖multOp Pl K L (ageVel Pl K L μ (thinPart T))‖ ≤
      C * L.ν⁻¹ ^ k * Real.exp (-(gRate Pl / 15 - ωb - 3 * K.m0 / 2) / L.ν) * ‖T‖) ∧
  (∀ w : LVel Pl L, ‖multOp Pl K L (ageVel Pl K L μ (repPart (multOp Pl K L w)))‖ ≤
      C * L.ν⁻¹ ^ k * Real.exp (-(19 * gRate Pl / 66 - ωb - 3 * K.m0 / 2) / L.ν) * ‖w‖)

/-- **The far velocities** (source 5569-5605, 5618-5619): the far thin-source velocity grows at most
like `e^{γ/(10ν)}` after gain weighting, the repair-source velocity has margin `31γ/165`:
`R⁻¹‖g⁻¹(S_far + Y)(T₁,0)‖_{Y_2} ≤ P_ν e^{(γ/10+ω_b+3m₀/2)/ν} A` and
`R⁻¹‖g⁻¹(S_far + Y)(0,T₂)‖_{Y_2} ≤ P_ν e^{-(31γ/165-ω_b-3m₀/2)/ν} G(w)`. -/
def AgeVelocityAt (ωb C : ℝ) (k : ℕ) : Prop :=
  (∀ T : LStr Pl K L, ‖ageVel Pl K L μ (thinPart T)‖ ≤
      C * L.ν⁻¹ ^ k * Real.exp ((gRate Pl / 10 + ωb + 3 * K.m0 / 2) / L.ν) * ‖T‖) ∧
  (∀ w : LVel Pl L, ‖ageVel Pl K L μ (repPart (multOp Pl K L w))‖ ≤
      C * L.ν⁻¹ ^ k * Real.exp (-(31 * gRate Pl / 165 - ωb - 3 * K.m0 / 2) / L.ν) * ‖w‖)

/-- **`repair:actual-jet`** (source 5400-5413): `A_T = 𝓛T₁` satisfies
`|(s∂_s)^jA_T(s)| ≤ C_j ε³ s^{5/2} N` for `0 ≤ j ≤ 6` and `A_T(s) = 0` for `s ≥ 1/ν`. -/
def ActualJetAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    (∀ j ≤ 6, ∀ s : ℝ, 0 < s →
      ENNReal.ofReal (frob (sDerivIter j
          (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) s)) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 3 * s ^ (5 / 2 : ℝ)) * oldN1 Pl K L T) ∧
    ∀ s : ℝ, 1 / L.ν ≤ s →
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T s = 0

/-- **`repair:exact-jet-clock`** (source 5449-5458): on the young range,
`B_T = B_j + (ν/s)D_yΔ_yX^mt(R/√s,0,0)` with `B_T = A_T' + μA_T/s` (`Bmat`, `χ_fA_T = A_T`,
5396-5398) and `|B_T - B_j| ≤ P_ν ν ε⁵ s^{5/2} N`. -/
def JetClockAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν),
    Bmat L.ν μ K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) s =
        Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s +
          clockJet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s ∧
      ENNReal.ofReal (frob
          (Bmat L.ν μ K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) s -
            Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s)) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ν * L.ε ^ 5 * s ^ (5 / 2 : ℝ)) * oldN1 Pl K L T

/-- **`repair:thin-complete`** (source 5484-5506; "its thin counterpart", 5692-5693): for the
thin old source, `R⁻¹‖E(U;X₁,Y₁) - E_{A_T}‖_{Y_2} ≤ P_ν N(ε⁴ + ε^{85/22}e^{m₀/ν} + ε³δ_base)`,
`δ_base = deltaBase C_Σ b_Σ ν` (5486-5490). -/
def ThinCompleteAt (C : ℝ) (k : ℕ) (Csig bsig : ℝ) : Prop :=
  ∀ T : LStr Pl K L,
    ENNReal.ofReal ‖(wardOps Pl K L μ).2.2 (thinPart T) - EAOp K L μ (LjOp Pl K L μ T)‖ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) +
        L.ε ^ 3 * deltaBase Csig bsig L.ν)) * oldN1 Pl K L T

/-- **`repair:actual-affine-remainder`** (source 5507-5525; "the final subtraction", 5694):
`R⁻¹‖𝔯_{A_T}‖_{Y_2} ≤ P_ν ε³ N (ε + ρ + δ_base)`. -/
def AffineRemainderAt (C : ℝ) (k : ℕ) (Csig bsig : ℝ) : Prop :=
  ∀ T : LStr Pl K L,
    ENNReal.ofReal ‖rAOp Pl K L μ (LjOp Pl K L μ T)‖ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 3 *
        (L.ε + rhoRep K L + deltaBase Csig bsig L.ν)) * oldN1 Pl K L T

/-- The thin moment of a gain stress (source 5163-5167, 5527: `N ≤ P_ν|N_ν|‖g⁻¹T‖_Z`; the
`|N_ν|` factor is `e^{γ/ν}` up to a power of `ν`): `N₁(χ_oT₁) ≤ P_ν e^{γ/ν} A`. -/
def ThinMomentAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, oldN1 Pl K L T ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * Real.exp (gRate Pl / L.ν) * ‖T‖)

/-- The body inverse on the generated range (source 5540-5547, 5621-5622):
`‖g⁻¹M_UR_μf‖_Z ≤ P_νR⁻¹‖f‖_{Y_2}` and `R⁻¹‖g⁻¹R_μf‖_{Y_2} ≤ P_νR⁻¹‖f‖_{Y_2}`. -/
def NearBodyAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ f : LSrc L, ‖multOp Pl K L (Rop Pl L μ f)‖ ≤ C * L.ν⁻¹ ^ k * ‖f‖ ∧
    ‖Rop Pl L μ f‖ ≤ C * L.ν⁻¹ ^ k * ‖f‖

/-- `repair:body-error` on the gain band (source 5557-5562): operator size
`P_ν e^{-(19γ/66 - m₀)/ν} + P_ν e^{-(19γ/33 - 2m₀)/ν}`, here in the weakened common form
`P_ν e^{-(19γ/66 - 3m₀/2)/ν}` of `δ_G` (5617). -/
def BodyRepairMarginAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ w : LVel Pl L, ‖(wardOps Pl K L μ).2.2 (repPart (multOp Pl K L w))‖ ≤
    C * L.ν⁻¹ ^ k * Real.exp (-(19 * gRate Pl / 66 - 3 * K.m0 / 2) / L.ν) * ‖w‖

/-- `repair:thin-complete` on the gain band (source 5527-5531: margins `γ/3`, `19γ/66 - m₀` and
the `δ_base` envelope, all at least the weakest age margin `γ/15`), in the form of `δ_A`. -/
def ThinBodyMarginAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ‖(wardOps Pl K L μ).2.2 (thinPart T) - EAOp K L μ (LjOp Pl K L μ T)‖ ≤
    C * L.ν⁻¹ ^ k * Real.exp (-(gRate Pl / 15 - 3 * K.m0 / 2) / L.ν) * ‖T‖

/-- `repair:actual-affine-remainder` on the gain band (source 5527-5531, 5563-5567: margins
`γ/3`, `γ/11 - m₀`; "included in `δ_A`", 5624-5625). -/
def AffRemMarginAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ‖rAOp Pl K L μ (LjOp Pl K L μ T)‖ ≤
    C * L.ν⁻¹ ^ k * Real.exp (-(gRate Pl / 15 - 3 * K.m0 / 2) / L.ν) * ‖T‖

end Estimates

/-! ## 5. The estimates along the concrete sequence (large `n`, all `z ∈ [-1,1]`) -/

namespace SeqData

variable (D : SeqData)

def RepairSource : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, RepairSourceAt D.Pl D.K (D.level n) C k

def PhaseGradient : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    PhaseGradientAt D.Pl D.K (D.level n) (D.mu n z) C k

def BodyError : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    BodyErrorAt D.Pl D.K (D.level n) (D.mu n z) C k

def AgeError (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    AgeErrorAt D.Pl D.K (D.level n) (D.mu n z) ωb C k

def AgeVelocity (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    AgeVelocityAt D.Pl D.K (D.level n) (D.mu n z) ωb C k

def ActualJet : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ActualJetAt D.Pl D.K (D.level n) (D.mu n z) C k

def JetClock : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    JetClockAt D.Pl D.K (D.level n) (D.mu n z) C k

def ThinComplete : Prop :=
  ∃ (C : ℝ) (k : ℕ) (Csig bsig : ℝ), 0 < bsig ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ThinCompleteAt D.Pl D.K (D.level n) (D.mu n z) C k Csig bsig

def AffineRemainder : Prop :=
  ∃ (C : ℝ) (k : ℕ) (Csig bsig : ℝ), 0 < bsig ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    AffineRemainderAt D.Pl D.K (D.level n) (D.mu n z) C k Csig bsig

def ThinMoment : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ThinMomentAt D.Pl D.K (D.level n) C k

def NearBody : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    NearBodyAt D.Pl D.K (D.level n) (D.mu n z) C k

def BodyRepairMargin : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    BodyRepairMarginAt D.Pl D.K (D.level n) (D.mu n z) C k

def ThinBodyMargin : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ThinBodyMarginAt D.Pl D.K (D.level n) (D.mu n z) C k

def AffRemMargin : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    AffRemMarginAt D.Pl D.K (D.level n) (D.mu n z) C k

end SeqData

/-- Enlarging the exponential factor and replacing the constant by its absolute value. -/
theorem ef_mono {c p e e' x : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e) (hee : e ≤ e') (hx : 0 ≤ x) :
    c * p * e * x ≤ |c| * p * e' * x := by
  have h1 : c * p ≤ |c| * p := mul_le_mul_of_nonneg_right (le_abs_self c) hp
  have h2 : c * p * e ≤ |c| * p * e' :=
    (mul_le_mul_of_nonneg_right h1 he).trans
      (mul_le_mul_of_nonneg_left hee (mul_nonneg (abs_nonneg c) hp))
  exact mul_le_mul_of_nonneg_right h2 hx

/-- `AgeError` is monotone in `ω_b`. -/
theorem SeqData.ageError_mono (D : SeqData) {ωb ωb' : ℝ} (h : ωb ≤ ωb') (hA : D.AgeError ωb) :
    D.AgeError ωb' := by
  obtain ⟨C, k, hC⟩ := hA
  refine ⟨|C|, k, hC.mono fun n hn z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hn z hz
  have hν := (D.level n).ν_pos
  have hp : 0 ≤ (D.level n).ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 hν.le) k
  refine ⟨fun T => (h1 T).trans (ef_mono hp (Real.exp_pos _).le ?_ (norm_nonneg _)),
    fun w => (h2 w).trans (ef_mono hp (Real.exp_pos _).le ?_ (norm_nonneg _))⟩
  · exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hν.le)
  · exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hν.le)

/-- `AgeVelocity` is monotone in `ω_b`. -/
theorem SeqData.ageVelocity_mono (D : SeqData) {ωb ωb' : ℝ} (h : ωb ≤ ωb')
    (hA : D.AgeVelocity ωb) : D.AgeVelocity ωb' := by
  obtain ⟨C, k, hC⟩ := hA
  refine ⟨|C|, k, hC.mono fun n hn z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hn z hz
  have hν := (D.level n).ν_pos
  have hp : 0 ≤ (D.level n).ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 hν.le) k
  refine ⟨fun T => (h1 T).trans (ef_mono hp (Real.exp_pos _).le ?_ (norm_nonneg _)),
    fun w => (h2 w).trans (ef_mono hp (Real.exp_pos _).le ?_ (norm_nonneg _))⟩
  · exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hν.le)
  · exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hν.le)

/-! ## 6. The error families from the estimates -/

/-- The error velocity of the concrete regime (source 5670-5671, 5807). -/
theorem concreteOps_vQ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (h : NearAt Pl K L μ) (T : LStr Pl K L) :
    (ConcreteReturnOps Pl K L μ h).vQ T = ageVel Pl K L μ T +
      Rop Pl L μ ((wardOps Pl K L μ).2.2 T - EAOp K L μ (LjOp Pl K L μ T) -
        rAOp Pl K L μ (LjOp Pl K L μ T)) := rfl

/-- One term: `c ν^{-j} e x ≤ |c| ν^{-K} e' x` for `0 < ν ≤ 1`, `j ≤ K`, `0 ≤ e ≤ e'`, `0 ≤ x`. -/
theorem ef_term {ν c e e' x : ℝ} {j K : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hjK : j ≤ K)
    (he : 0 ≤ e) (hee : e ≤ e') (hx : 0 ≤ x) :
    c * ν⁻¹ ^ j * e * x ≤ |c| * ν⁻¹ ^ K * e' * x := by
  have hp : 0 ≤ ν⁻¹ ^ j := pow_nonneg (inv_nonneg.2 hν.le) j
  have hpK : ν⁻¹ ^ j ≤ ν⁻¹ ^ K := pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) hjK
  have h1 : c * ν⁻¹ ^ j ≤ |c| * ν⁻¹ ^ K :=
    (mul_le_mul_of_nonneg_right (le_abs_self c) hp).trans
      (mul_le_mul_of_nonneg_left hpK (abs_nonneg c))
  have h0 : 0 ≤ |c| * ν⁻¹ ^ K := mul_nonneg (abs_nonneg c) (pow_nonneg (inv_nonneg.2 hν.le) K)
  have h2 : c * ν⁻¹ ^ j * e ≤ |c| * ν⁻¹ ^ K * e' := by
    calc c * ν⁻¹ ^ j * e ≤ |c| * ν⁻¹ ^ K * e := mul_le_mul_of_nonneg_right h1 he
      _ ≤ |c| * ν⁻¹ ^ K * e' := mul_le_mul_of_nonneg_left hee h0
  exact mul_le_mul_of_nonneg_right h2 hx

/-- A composed term: a body force bounded by `b ν^{-j} e x`, mapped back by an operator of size
`a ν^{-i}`. -/
theorem ef_term2 {ν a b e e' x f : ℝ} {i j K : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hijK : i + j ≤ K)
    (he : 0 ≤ e) (hee : e ≤ e') (hx : 0 ≤ x) (hf : f ≤ b * ν⁻¹ ^ j * e * x) {y : ℝ}
    (hy : y ≤ a * ν⁻¹ ^ i * f) (hf0 : 0 ≤ f) :
    y ≤ (|a| * |b|) * ν⁻¹ ^ K * e' * x := by
  have hpi : 0 ≤ ν⁻¹ ^ i := pow_nonneg (inv_nonneg.2 hν.le) i
  have hpj : 0 ≤ ν⁻¹ ^ j := pow_nonneg (inv_nonneg.2 hν.le) j
  have hf' : f ≤ |b| * ν⁻¹ ^ j * e * x :=
    hf.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self b) hpj) he) hx)
  have hy' : y ≤ |a| * ν⁻¹ ^ i * f :=
    hy.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self a) hpi) hf0)
  have h1 : |a| * ν⁻¹ ^ i * f ≤ |a| * ν⁻¹ ^ i * (|b| * ν⁻¹ ^ j * e * x) :=
    mul_le_mul_of_nonneg_left hf' (mul_nonneg (abs_nonneg a) hpi)
  have h2 : |a| * ν⁻¹ ^ i * (|b| * ν⁻¹ ^ j * e * x) = (|a| * |b|) * ν⁻¹ ^ (i + j) * e * x := by
    rw [pow_add]; ring
  have h3 := ef_term (c := |a| * |b|) (e := e) (e' := e') (x := x) hν hν1 hijK he hee hx
  rw [abs_of_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg b))] at h3
  linarith [h1, h2.le, h2.ge, h3]

set_option maxHeartbeats 1600000 in
/-- **The error families of the concrete sequence** (source 5607-5627, 5687-5697):
`ErrorFamilyBounds (concreteReturnSeq D G) γ ω_b m₀` from the age errors and far velocities, the
gain-band forms of `repair:body-error`, `repair:thin-complete` and
`repair:actual-affine-remainder`, the body inverse on the generated range, and the invertibility of
the near layer (`NearAt`) for large `n`. -/
theorem errorFamilyBounds_of (D : SeqData)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) {ωb : ℝ}
    (hγ : 0 ≤ gRate D.Pl) (hωb : 0 ≤ ωb) (hm0 : 0 ≤ D.K.m0) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hnear : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z))
    (h4 : D.AgeError ωb) (h4v : D.AgeVelocity ωb) (h5 : D.BodyRepairMargin)
    (h6 : D.ThinBodyMargin) (h7 : D.AffRemMargin) (hB : D.NearBody) :
    ErrorFamilyBounds (concreteReturnSeq D G) (gRate D.Pl) ωb D.K.m0 := by
  obtain ⟨C4, k4, e4⟩ := h4
  obtain ⟨C4v, k4v, e4v⟩ := h4v
  obtain ⟨C5, k5, e5⟩ := h5
  obtain ⟨C6, k6, e6⟩ := h6
  obtain ⟨C7, k7, e7⟩ := h7
  obtain ⟨CB, kB, eB⟩ := hB
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    ((retNu_tendsto D.σ₀ hω).eventually_lt_const one_pos).mono fun n h => h.le
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hnear.and (e4.and (e4v.and (e5.and (e6.and (e7.and (eB.and hν1)))))))
  refine ⟨|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|),
    k4 + k4v + kB + k5 + k6 + k7, N, fun n hn z hz V => ?_⟩
  obtain ⟨hnr, f4, f4v, f5, f6, f7, fB, hν1n⟩ := hN n hn
  have hnz := hnr z hz
  obtain ⟨f4a, f4b⟩ := f4 z hz
  obtain ⟨f4va, f4vb⟩ := f4v z hz
  have f5z := f5 z hz
  have f6z := f6 z hz
  have f7z := f7 z hz
  have fBz := fB z hz
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1' : (D.level n).ν ≤ 1 := hν1n
  have hops := concreteReturnSeq_ops_eq D G n z hnz
  have hMv : ∀ T',
      ((concreteReturnSeq D G).ops n z).M (((concreteReturnSeq D G).ops n z).vQ T') =
      multOp D.Pl D.K (D.level n) (ageVel D.Pl D.K (D.level n) (D.mu n z) T' +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T' -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T') -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T'))) := by
    intro T'; rw [hops]; rfl
  have hvQeq : ∀ T', ((concreteReturnSeq D G).ops n z).vQ T' =
      ageVel D.Pl D.K (D.level n) (D.mu n z) T' +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T' -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T') -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T')) := by
    intro T'; rw [hops]; exact concreteOps_vQ _ _ _ _ hnz T'
  have hgraph : ((concreteReturnSeq D G).ops n z).Tc V =
      multOp D.Pl D.K (D.level n) (((concreteReturnSeq D G).ops n z).wc V) := by
    rw [hops]; exact PairSp.graph V
  rw [hMv, hvQeq]
  generalize (((concreteReturnSeq D G).ops n z).Tc V : LStr D.Pl D.K (D.level n)) = T at hgraph ⊢
  generalize (((concreteReturnSeq D G).ops n z).wc V : LVel D.Pl (D.level n)) = w at hgraph ⊢
  have hTw : T = multOp D.Pl D.K (D.level n) w := hgraph
  -- the five pieces of `v_Q(T)` (source 5687-5697)
  have hsplitT := thinPart_add_repPart T
  have hage : ageVel D.Pl D.K (D.level n) (D.mu n z) (thinPart T) +
      ageVel D.Pl D.K (D.level n) (D.mu n z) (repPart T) =
      ageVel D.Pl D.K (D.level n) (D.mu n z) T := by
    rw [← map_add, hsplitT]
  have hE : (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (thinPart T) +
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (repPart T) =
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T := by
    rw [← map_add, hsplitT]
  obtain ⟨a1, ha1⟩ : ∃ a, a = ageVel D.Pl D.K (D.level n) (D.mu n z) (thinPart T) := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a, a = ageVel D.Pl D.K (D.level n) (D.mu n z) (repPart T) := ⟨_, rfl⟩
  obtain ⟨b1, hb1d⟩ : ∃ b, b = (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (thinPart T) -
      EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) := ⟨_, rfl⟩
  obtain ⟨b2, hb2d⟩ : ∃ b, b = (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (repPart T) :=
    ⟨_, rfl⟩
  obtain ⟨b3, hb3d⟩ : ∃ b, b = rAOp D.Pl D.K (D.level n) (D.mu n z)
      (LjOp D.Pl D.K (D.level n) (D.mu n z) T) := ⟨_, rfl⟩
  have hvQ : ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T)) =
      a1 + a2 + Rop D.Pl (D.level n) (D.mu n z) (b1 + b2 - b3) := by
    rw [← hage, ← hE, ha1, ha2, hb1d, hb2d, hb3d]
    simp only [map_add, map_sub]
    abel
  -- exponential factors
  obtain ⟨eA, heA⟩ : ∃ e, Real.exp (-(gRate D.Pl / 15 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) = e :=
    ⟨_, rfl⟩
  obtain ⟨eG, heG⟩ : ∃ e,
      Real.exp (-(19 * gRate D.Pl / 66 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) = e := ⟨_, rfl⟩
  obtain ⟨eχA, heχA⟩ : ∃ e,
      Real.exp ((gRate D.Pl / 10 + ωb + 3 * D.K.m0 / 2) / (D.level n).ν) = e := ⟨_, rfl⟩
  obtain ⟨eχG, heχG⟩ : ∃ e,
      Real.exp (-(31 * gRate D.Pl / 165 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) = e := ⟨_, rfl⟩
  obtain ⟨eA', heA'⟩ : ∃ e, Real.exp (-(gRate D.Pl / 15 - 3 * D.K.m0 / 2) / (D.level n).ν) = e :=
    ⟨_, rfl⟩
  obtain ⟨eG', heG'⟩ : ∃ e,
      Real.exp (-(19 * gRate D.Pl / 66 - 3 * D.K.m0 / 2) / (D.level n).ν) = e := ⟨_, rfl⟩
  have hdiv : ∀ {a b : ℝ}, a ≤ b → Real.exp (a / (D.level n).ν) ≤ Real.exp (b / (D.level n).ν) :=
    fun h => Real.exp_le_exp.2 (div_le_div_of_nonneg_right h hν.le)
  have hA'A : eA' ≤ eA := by rw [← heA', ← heA]; exact hdiv (by linarith)
  have hG'G : eG' ≤ eG := by rw [← heG', ← heG]; exact hdiv (by linarith)
  have hA'χ : eA' ≤ eχA := by rw [← heA', ← heχA]; exact hdiv (by linarith)
  have hG'χ : eG' ≤ eχG := by rw [← heG', ← heχG]; exact hdiv (by linarith)
  have hA'0 : 0 ≤ eA' := by rw [← heA']; exact (Real.exp_pos _).le
  have hG'0 : 0 ≤ eG' := by rw [← heG']; exact (Real.exp_pos _).le
  have hA0 : 0 ≤ eA := by rw [← heA]; exact (Real.exp_pos _).le
  have hG0 : 0 ≤ eG := by rw [← heG]; exact (Real.exp_pos _).le
  have hχA0 : 0 ≤ eχA := by rw [← heχA]; exact (Real.exp_pos _).le
  have hχG0 : 0 ≤ eχG := by rw [← heχG]; exact (Real.exp_pos _).le
  have hx : 0 ≤ ‖T‖ := norm_nonneg _
  have hy : 0 ≤ ‖w‖ := norm_nonneg _
  -- the pieces
  have g4a : ‖multOp D.Pl D.K (D.level n) a1‖ ≤ C4 * (D.level n).ν⁻¹ ^ k4 * eA * ‖T‖ := by
    rw [ha1, ← heA]; exact f4a T
  have g4b : ‖multOp D.Pl D.K (D.level n) a2‖ ≤ C4 * (D.level n).ν⁻¹ ^ k4 * eG * ‖w‖ := by
    rw [ha2, ← heG, hTw]; exact f4b w
  have g4va : ‖a1‖ ≤ C4v * (D.level n).ν⁻¹ ^ k4v * eχA * ‖T‖ := by
    rw [ha1, ← heχA]; exact f4va T
  have g4vb : ‖a2‖ ≤ C4v * (D.level n).ν⁻¹ ^ k4v * eχG * ‖w‖ := by
    rw [ha2, ← heχG, hTw]; exact f4vb w
  have hb1 : ‖b1‖ ≤ C6 * (D.level n).ν⁻¹ ^ k6 * eA' * ‖T‖ := by
    rw [hb1d, ← heA']; exact f6z T
  have hb2 : ‖b2‖ ≤ C5 * (D.level n).ν⁻¹ ^ k5 * eG' * ‖w‖ := by
    rw [hb2d, ← heG', hTw]; exact f5z w
  have hb3 : ‖b3‖ ≤ C7 * (D.level n).ν⁻¹ ^ k7 * eA' * ‖T‖ := by
    rw [hb3d, ← heA']; exact f7z T
  have hk1 : k4 ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  have hk2 : k4v ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  have hk3 : kB + k6 ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  have hk4 : kB + k5 ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  have hk5 : kB + k7 ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  -- stress bounds
  have sM1 := g4a.trans (ef_term (K := k4 + k4v + kB + k5 + k6 + k7) hν hν1' hk1 hA0 le_rfl hx)
  have sM2 := g4b.trans (ef_term (K := k4 + k4v + kB + k5 + k6 + k7) hν hν1' hk1 hG0 le_rfl hy)
  have sM3 := ef_term2 hν hν1' hk3 hA'0 hA'A hx hb1 (fBz b1).1 (norm_nonneg _)
  have sM4 := ef_term2 hν hν1' hk4 hG'0 hG'G hy hb2 (fBz b2).1 (norm_nonneg _)
  have sM5 := ef_term2 hν hν1' hk5 hA'0 hA'A hx hb3 (fBz b3).1 (norm_nonneg _)
  -- velocity bounds
  have sV1 := g4va.trans (ef_term (K := k4 + k4v + kB + k5 + k6 + k7) hν hν1' hk2 hχA0 le_rfl hx)
  have sV2 := g4vb.trans (ef_term (K := k4 + k4v + kB + k5 + k6 + k7) hν hν1' hk2 hχG0 le_rfl hy)
  have sV3 := ef_term2 hν hν1' hk3 hA'0 hA'χ hx hb1 (fBz b1).2 (norm_nonneg _)
  have sV4 := ef_term2 hν hν1' hk4 hG'0 hG'χ hy hb2 (fBz b2).2 (norm_nonneg _)
  have sV5 := ef_term2 hν hν1' hk5 hA'0 hA'χ hx hb3 (fBz b3).2 (norm_nonneg _)
  -- triangle inequalities
  have tM : ‖multOp D.Pl D.K (D.level n) (ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T)))‖ ≤
      ‖multOp D.Pl D.K (D.level n) a1‖ + ‖multOp D.Pl D.K (D.level n) a2‖ +
        (‖multOp D.Pl D.K (D.level n) (Rop D.Pl (D.level n) (D.mu n z) b1)‖ +
          ‖multOp D.Pl D.K (D.level n) (Rop D.Pl (D.level n) (D.mu n z) b2)‖ +
          ‖multOp D.Pl D.K (D.level n) (Rop D.Pl (D.level n) (D.mu n z) b3)‖) := by
    rw [hvQ]
    simp only [map_add, map_sub]
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have tV : ‖ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T))‖ ≤
      ‖a1‖ + ‖a2‖ + (‖Rop D.Pl (D.level n) (D.mu n z) b1‖ +
        ‖Rop D.Pl (D.level n) (D.mu n z) b2‖ + ‖Rop D.Pl (D.level n) (D.mu n z) b3‖) := by
    rw [hvQ]
    simp only [map_add, map_sub]
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  -- collect
  have hP : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) :=
    pow_nonneg (inv_nonneg.2 hν.le) _
  have hU : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eA * ‖T‖ :=
    mul_nonneg (mul_nonneg hP hA0) hx
  have hW : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eG * ‖w‖ :=
    mul_nonneg (mul_nonneg hP hG0) hy
  have hU' : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eχA * ‖T‖ :=
    mul_nonneg (mul_nonneg hP hχA0) hx
  have hW' : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eχG * ‖w‖ :=
    mul_nonneg (mul_nonneg hP hχG0) hy
  have c0 : 0 ≤ |C4| := abs_nonneg _
  have c1 : 0 ≤ |C4v| := abs_nonneg _
  have c2 : 0 ≤ |CB| * |C5| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have c3 : 0 ≤ |CB| * |C6| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have c4 : 0 ≤ |CB| * |C7| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have keyM : ‖multOp D.Pl D.K (D.level n) (ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T)))‖ ≤
      (|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|)) *
          (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eA * ‖T‖ +
        (|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|)) *
          (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eG * ‖w‖ := by
    linarith [tM, sM1, sM2, sM3, sM4, sM5, mul_nonneg c1 hU, mul_nonneg c2 hU,
      mul_nonneg c1 hW, mul_nonneg c3 hW, mul_nonneg c4 hW]
  have keyV : ‖ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T))‖ ≤
      (|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|)) *
          (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eχA * ‖T‖ +
        (|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|)) *
          (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eχG * ‖w‖ := by
    linarith [tV, sV1, sV2, sV3, sV4, sV5, mul_nonneg c0 hU', mul_nonneg c2 hU',
      mul_nonneg c0 hW', mul_nonneg c3 hW', mul_nonneg c4 hW']
  rw [← heA, ← heG] at keyM
  rw [← heχA, ← heχG] at keyV
  exact ⟨keyM, keyV⟩

end UnforcedLeray.Short.PartIIIb.Concrete
