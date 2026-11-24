import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_org

/-!
# `PartIII-b:C/rep/8/1/org`: the mean comparison of the thin residual (source 5374-5448)

Source of record: `the November 2 reference manuscript` (73 pages), lines
5374-5448 (`X₁,Y₁` against the phase-mean zero-width Newton response `X^mt, Y^mt`), with
5196-5299 (the full unprojected residual, the repair coefficients and the exact pressure) and
IIIa `sep:mean-comparison` (SP 3767-3780).

## What the source proves, and the corrected step (a)

The residual difference `E(U;X₁,Y₁) - E(U;X^mt,Y^mt)` (`actualE - meanE`) is a sum of products of a
background coefficient (`U`, `DU`, `D²U`, `U⊗U`, `∇p`) with a difference of the two responses
(`D(X₁-X^mt)`, `D(Y₁-Y^mt)`, `D²X₁ - D²X^mt`).  The source estimates these products in two
different ways:

* against the **raw-train coefficients** (`V = √s v`, the flat lifted pressure; transversally
  localized, "bounded in phase with all the finite transverse weights", 5434-5436, 5225-5242) the
  geometric comparison `‖D_yX₁ - D_yX^mt‖_{L²_τ} + ‖D_yY₁ - D_yY^mt‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N`
  (5415-5427) and the Hessian bound `‖D²_yX₁‖_{L²_τ} ≤ P_ν ε⁴ s³ N` (5438-5448) give `P_ν ε⁴ N`;
* against the **remainder coefficients** (the repair `r_b`, the entrance coefficients and the
  pressure correction `∇p - G_flat`, which are bounded only in `Y_{11/4}`, 5134-5139, 5276-5281)
  Hölder with the general thin-source estimate `‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22} N₁` gives
  `P_ν ε^{85/22} e^{m₀/ν} N` (5283-5289; "the 85/22 term retains the entire Cartesian pressure
  correction", 5506).  These remainder coefficients are not localized transversally, so they cannot
  be paired with the pointwise comparison bound.

Hence the source bound for step (a) is `P_ν N(ε⁴ + ε^{85/22}e^{m₀/ν})`, not `P_ν ε⁴ N`:
`MeanComparisonAt` of `PartIII-b_C_rep_8_org` (ε⁴ alone, with the exact background `U = V + r_b`
and the exact pressure in both residuals) is stronger than what lines 5272-5289 and 5415-5448 give:
the remainder coefficients multiply `D(X₁ - X^mt)`, for which the source has no `L^{22/3}` bound
better than the individual ones.  This is the same correction already made to `RingExpansionAt`
(organizer item `PartIII-b:C/rep/8/2/pres/org`); `ThinCompleteAt` carries `ε^{85/22}e^{m₀/ν}`, so
nothing downstream is lost.  `MeanComparisonAt` is step (a) with `ε⁴ + ε^{85/22}e^{m₀/ν}`;
the organizer item `PartIII-b:C/rep/8/1/pres/org` corrects `MeanComparisonAt` of
`PartIII-b_C_rep_8_org` to exactly this body, after which `SeqData.MeanComparison` is that body (done in `PartIII-b_C_rep_8_org`).

## The hypotheses of step (a)

* `GeomComparisonAt` (5415-5427): the normalized phase `L²` (`cellL2`) of
  `|D(X₁-X^mt)| + |D(Y₁-Y^mt)|` at every young receiver `y = (R/√s, 0, η/√s)`, `0 < s ≤ 1/ν`, is
  `≤ C ν^{-k} ε⁴ s^{5/2} N`;
* `HessianBoundAt` (5438-5448): the same for `|D²X₁| + |D²X^mt|` with `ε⁴ s³`;
* `YoungSupportAt` (5395-5398, 5296-5298): for `s > 1/ν` both quantities vanish (the stream cutoff);
* `MeanMeasurableAt`: `meanE` is a.e. strongly measurable (it is built from derivatives of the
  phase-free fields `X^mt, Y^mt` and the smooth background);
* `BackgroundSplitAt` (5134-5139, 5225-5242, 5272-5289, 5434-5436): the background coefficient size
  `coefSize` splits into a transversally localized part (bounded at young receivers, uniformly in
  phase, by `βl(s,η)` with `∫∫ s^{5/2} βl² ≤ C ν^{-k}`) and a remainder `Br ≥ 0` whose products with
  the individual response derivatives (`jetSize`) are `≤ C ν^{-k} ε^{85/22} e^{m₀/ν} N` in
  `L²(srcMeasure)`.

**`meanComparisonAt_of`** (proved): these give `MeanComparisonAziAt` (the body of
`MeanComparisonAt` for swirl-free thin stresses, `ThinAziZero`) at one regime;
**`SeqData.meanComparison_of`** (proved): the sequence form `MeanComparisonAzi`.

## The swirl-free hypothesis (organizer item `PartIII-b:C/rep/8/1/1/2/4/2/org`)

The source makes the comparison for `T = M_U w` (5376) with `U, w` swirl free (5141-5142), whose
thin component has zero azimuthal row and column (4772-4774).  The actual responses keep the hoop
entry of a general chart tensor (`NearInst.nsSym`), the phase-mean Newton fields drop it
(`phaseMean`), so `GeomComparisonAt` and its leaves carry `ThinAziZero T`, and step (a) is proved in
the form `MeanComparisonAziAt`.  The hypothesis holds on the pair space `T = M w` (`errorFamilyBounds_of`,
`hTw`); propagating it through `MeanComparisonAt`, `ThinCompleteAt`, `ThinBodyMarginAt` is organizer
item `PartIII-b:C/rep/8/swirl/org`.

The exact formula `Y^mt = 𝒞_{χ_y}W_μ + [D_{μ+1}, 𝒞_{χ_y}](W_μ - W_{μ+1})` (5427-5432) is
`MeanYFormula`; it follows from the shifted dilation identity of the uncut Newton fields outside the
old source disk (`MeanShiftIdentity`, 5383-5387) by `meanYFormula_of_shift` (proved).  It is the
tool for the `Y` part of `GeomComparisonAt` and is not a hypothesis of the assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Pointwise sizes -/

/-- `Σ_j |∂_jf|` of a spatial vector field. -/
def gradSize (f : Space → Space) (y : Space) : ℝ := ∑ j : Fin 3, ‖physPd f j y‖

/-- `Σ_{j,l} |∂_j∂_lf|` of a spatial vector field. -/
def hessSize (f : Space → Space) (y : Space) : ℝ := ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 f j l y‖

/-- `Σ_j |∂_jq|` of a scalar. -/
def presGradSize (q : Space → ℝ) (y : Space) : ℝ :=
  ∑ j : Fin 3, |fderiv ℝ q y (coordinateVector j)|

/-- The size of the background coefficients of the Ward residual (source 4276-4282):
`|U| + ν Σ|∂U| + ν Σ|∂²U| + |U|² + Σ|∂p|` (the coefficients of `2U·∇Y`, `2νC_diff`,
`(U⊗U):D²X`, `(DX+DXᵀ)∇p`). -/
def coefSize (ν : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (τ : ℝ) (y : Space) : ℝ :=
  ‖U τ y‖ + ν * gradSize (U τ) y + ν * hessSize (U τ) y + ‖U τ y‖ ^ 2 + presGradSize (p τ) y

/-- **The normalized phase `L²` at a young receiver** (source 5415-5427, `L²_τ`): at the chart point
`(s, η)` the receiver `y = chartY R (s, ·, η) = (R/√s, 0, η/√s)` is fixed and the phase
`τ = 2q/R + log s` runs over one period `P = 2c/R` as `q` runs over the cell `[-c/2, c/2)`, with
`dq/c = dτ/P`; so this is `‖F(·, y)‖_{L²_τ}` with the normalized phase measure. -/
def cellL2 (R c : ℝ) (F : ℝ → Space → ℝ) (s η : ℝ) : ℝ≥0∞ :=
  (∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ *
    ENNReal.ofReal (F (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))) ^ 2) ^
    (1 / 2 : ℝ)

/-! ## 2. The responses and their comparison data at one regime -/

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `X₁`: the Ward field of the old thin source `χ_oT₁` alone (source 5377-5379, 4171). -/
def actX (T : LStr Pl K L) : ℝ → Space → Space :=
  wardX L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (thinG Pl K L T)

/-- `Y₁ = D_{μ+1}X₁` (source 5377-5379, 4171). -/
def actY (T : LStr Pl K L) : ℝ → Space → Space :=
  wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (thinG Pl K L T)

/-- `X^mt` of the thin tensor of `T` (source 5380-5382), as a field on `Space`. -/
def mnX (T : LStr Pl K L) : ℝ → Space → Space :=
  Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)

/-- `Y^mt = D_{μ+1}X^mt` (source 5380-5382). -/
def mnY (T : LStr Pl K L) : ℝ → Space → Space :=
  Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)

/-- `|D_yX₁ - D_yX^mt| + |D_yY₁ - D_yY^mt|` (source 5419-5422), `(D_yX)_{ij} = ∂_jX_i`, operator
norms. -/
def cmpData (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (actX Pl K L μ T τ) y - fderiv ℝ (mnX Pl K L μ T τ) y‖ +
    ‖fderiv ℝ (actY Pl K L μ T τ) y - fderiv ℝ (mnY Pl K L μ T τ) y‖

/-- `|D²_yX₁| + |D²_yX^mt|` (source 5438-5448). -/
def hessData (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  hessSize (actX Pl K L μ T τ) y + hessSize (mnX Pl K L μ T τ) y

/-- The individual response derivatives `|DX₁| + |DX^mt| + |DY₁| + |DY^mt| + |D²X₁| + |D²X^mt|`
(the factors of the remainder-coefficient products, source 5283-5289). -/
def jetSize (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (actX Pl K L μ T τ) y‖ + ‖fderiv ℝ (mnX Pl K L μ T τ) y‖ +
    ‖fderiv ℝ (actY Pl K L μ T τ) y‖ + ‖fderiv ℝ (mnY Pl K L μ T τ) y‖ + hessData Pl K L μ T τ y

/-- The remainder-coefficient product `s^{-1/2} B_r |jet|` at a chart point (the chart coefficient
convention of `coefOf`, so that its `L²(srcMeasure)` norm is `R⁻¹‖·‖_{Y_2}`). -/
def remTerm (Br : ℝ → Space → ℝ) (T : LStr Pl K L) (p : Chart) : ℝ :=
  (Real.sqrt p.1)⁻¹ * Br (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) *
    jetSize Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)

/-! ## 3. The source facts of step (a) at one regime -/

/-- **The thin component is swirl free** (source 5376: the comparison is made for
`T = (T₁, T₂) = M_U w`, `T₁ = M_V w`; 5141-5142: `w` is an axisymmetric physical velocity without
swirl, and so is `U`, hence `T₁ = V ⊗ w + w ⊗ V` has zero azimuthal row and column, the `φφ`
entry included; 4772-4774: `Σ_M` of the phase-mean field retains them "as zero entries").  For
almost every chart point the `φ = 1` row and column of the thin representative `thinRep T`
vanish.  The actual responses (`oldPhys`, through `NearInst.nsSym`) keep the hoop entry `T(1,1)`
while the phase-mean Newton fields (`phaseMean`, `SourceL.lean`) drop it, so the comparisons
below hold only under this hypothesis. -/
def ThinAziZero (T : LStr Pl K L) : Prop :=
  ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), ∀ i j : Fin 3, (i = 1 ∨ j = 1) → thinRep T p i j = 0

/-- **Geometric comparison** (source 5415-5427; IIIa `sep:mean-comparison`, SP 3767-3780): for every
swirl-free thin stress (`ThinAziZero`, source 5376, 5141-5142) and every young chart point
`0 < s ≤ 1/ν`, `η ∈ ℝ`,
`‖D_yX₁ - D_yX^mt‖_{L²_τ} + ‖D_yY₁ - D_yY^mt‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N`, `N = N₁(χ_oT₁)`
(finite transverse width and heat-to-Newton error included; `Y` by `MeanYFormula`). -/
def GeomComparisonAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ThinAziZero Pl K L T → ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    cellL2 L.ε⁻¹ (cOf L.ν) (cmpData Pl K L μ T) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **Hessian bound** (source 5438-5448): `‖D²_yX₁‖_{L²_τ} ≤ P_ν ε⁴ s³ N` at young chart points, and
the same for the phase-mean zero-width field `X^mt` (the same separated kernel count, 5404-5413; the
mean transverse Taylor estimate 5441-5443 is its integrated form).  The phase function is
measurable along the cell (the fields are smooth). -/
def HessianBoundAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => hessData Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (hessData Pl K L μ T) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T

/-- **Young support** (source 5395-5398: `χ_y` is supported in `s ≤ 1/ν`; 5296-5298: every term of
the residual contains a derivative of `X` or `Y`): at chart points with `s > 1/ν` the comparison and
Hessian data vanish. -/
def YoungSupportAt : Prop :=
  ∀ (T : LStr Pl K L) (p : Chart), 1 / L.ν < p.1 →
    cmpData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) = 0 ∧
      hessData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) = 0

/-- **Measurability of the mean residual** (needed for the triangle inequality of 5484-5506):
`meanE` is built from `D_yX^mt, D²_yX^mt, D_yY^mt` (phase free) and the smooth exact background. -/
def MeanMeasurableAt : Prop :=
  ∀ T : LStr Pl K L, AEStronglyMeasurable (meanE Pl K L μ T) (srcMeasure (cOf L.ν))

/-- **The coefficient split** (source 5134-5139, 5225-5242, 5272-5289, 5434-5436): the background
coefficient size splits as `coefSize ≤ B_l + B_r` with
* `B_l` the transversally localized raw-train part (`V = √s v`, the flat lifted pressure `G_flat`):
  at young receivers it is bounded, uniformly in the phase, by `βl(s, η)` with
  `∫₀^{1/ν}∫ s^{5/2} βl² dη ds ≤ P_ν` ("the raw-train coefficients multiplying them are bounded in
  phase with all the finite transverse weights", 5434-5436; `‖sup_q|v(s,q,·)|‖₂`, 5225-5229);
* `B_r ≥ 0` the remainder (repair `r_b`, entrance coefficients, `∇p - G_flat`, all `≤ P_ν ρ` in
  `Y_{11/4}`), whose products with the individual response derivatives obey the Hölder bound
  `R⁻¹‖B_r·jet‖_{Y_2} ≤ P_ν ε^{85/22} e^{m₀/ν} N` (`‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22} N₁`,
  `1 + 3/11 + 57/22 = 85/22`, 5283-5289). -/
def BackgroundSplitAt (C : ℝ) (k : ℕ) : Prop :=
  ∃ (Bl Br : ℝ → Space → ℝ) (βl : ℝ → ℝ → ℝ),
    (∀ τ y, coefSize L.ν L.U L.pres τ y ≤ Bl τ y + Br τ y) ∧
    (∀ τ y, 0 ≤ Br τ y) ∧
    (∀ (τ : ℝ) (p : Chart), 0 < p.1 → p.1 ≤ 1 / L.ν →
      Bl τ (NearInst.chartY L.ε⁻¹ p) ≤ βl p.1 p.2.2) ∧
    ∫⁻ s in Ioc (0 : ℝ) (1 / L.ν), ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * βl s η ^ 2) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k) ∧
    ∀ T : LStr Pl K L, AEStronglyMeasurable (remTerm Pl K L μ Br T) (srcMeasure (cOf L.ν)) ∧
      eLpNorm (remTerm Pl K L μ Br T) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) *
          oldN1 Pl K L T

/-! ## 4. The corrected step (a) -/

/-- **Step (a) for swirl-free thin stresses** (source 5376, 5415-5448 with 5272-5289): the body of
`MeanComparisonAt` (`PartIII-b_C_rep_8_org`) for every `T` with `ThinAziZero T`.  This is what the
geometric comparison gives: for a thin stress with a hoop entry the actual response keeps it and
`meanE` does not, and the difference is of order `ε³N`.  `meanComparisonAt_of` proves this form;
the swirl-free hypothesis is discharged on the pair space `T = M w` (organizer item
`PartIII-b:C/rep/8/swirl/org`). -/
def MeanComparisonAziAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ThinAziZero Pl K L T →
    AEStronglyMeasurable (meanE Pl K L μ T) (srcMeasure (cOf L.ν)) ∧
    eLpNorm (actualE Pl K L μ T - meanE Pl K L μ T) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k *
        (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T

end Regime

/-! ## 5. The sequence forms -/

namespace SeqData

variable (D : SeqData)

def GeomComparison : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    GeomComparisonAt D.Pl D.K (D.level n) (D.mu n z) C k

def HessianBound : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    HessianBoundAt D.Pl D.K (D.level n) (D.mu n z) C k

def YoungSupport : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, YoungSupportAt D.Pl D.K (D.level n) (D.mu n z)

def MeanMeasurable : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, MeanMeasurableAt D.Pl D.K (D.level n) (D.mu n z)

def BackgroundSplit : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    BackgroundSplitAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `MeanComparisonAziAt` (step (a) for swirl-free thin stresses). -/
def MeanComparisonAzi : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanComparisonAziAt D.Pl D.K (D.level n) (D.mu n z) C k

end SeqData

/-! ## 6. The pointwise residual comparison -/

theorem abs_apply_le_norm (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  rwa [Real.norm_eq_abs] at this

theorem norm_coordinateVector (j : Fin 3) : ‖coordinateVector j‖ = 1 := by
  rw [coordinateVector, EuclideanSpace.norm_single, norm_one]

/-- A component of `∂_jX₁ - ∂_jX₂` is bounded by the operator norm of `DX₁ - DX₂`. -/
theorem physPd_sub_apply_le (X1 X2 : Space → Space) (y : Space) (j i : Fin 3) :
    |physPd X1 j y i - physPd X2 j y i| ≤ ‖fderiv ℝ X1 y - fderiv ℝ X2 y‖ := by
  have h : physPd X1 j y i - physPd X2 j y i =
      ((fderiv ℝ X1 y - fderiv ℝ X2 y) (coordinateVector j)) i := by
    simp [physPd]
  rw [h]
  refine (abs_apply_le_norm _ i).trans ?_
  refine ((fderiv ℝ X1 y - fderiv ℝ X2 y).le_opNorm _).trans ?_
  rw [norm_coordinateVector, mul_one]

/-- `|(!₂[v₀, v₂])| ≤ |v|`. -/
theorem norm_merid_le (v : Space) : ‖(!₂[v 0, v 2] : Merid)‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp
  nlinarith [sq_nonneg (v 1)]

/-- The chart coefficients of two fields differ by at most `s^{-1/2}` times the difference of the
fields at the receiver. -/
theorem coefOf_sub_norm_le (R : ℝ) (F G : ℝ → Space → Space) (p : Chart) :
    ‖coefOf R F p - coefOf R G p‖ ≤ (Real.sqrt p.1)⁻¹ *
      ‖F (NearInst.chartTau R p) (NearInst.chartY R p) -
        G (NearInst.chartTau R p) (NearInst.chartY R p)‖ := by
  unfold coefOf
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  gcongr
  set v := F (NearInst.chartTau R p) (NearInst.chartY R p) -
    G (NearInst.chartTau R p) (NearInst.chartY R p)
  have h : (!₂[F (NearInst.chartTau R p) (NearInst.chartY R p) 0,
        F (NearInst.chartTau R p) (NearInst.chartY R p) 2] : Merid) -
      !₂[G (NearInst.chartTau R p) (NearInst.chartY R p) 0,
        G (NearInst.chartTau R p) (NearInst.chartY R p) 2] = !₂[v 0, v 2] := by
    ext i; fin_cases i <;> simp [v]
  rw [h]
  exact norm_merid_le v


/-- The `C_diff` part of the residual difference. -/
theorem physCdiff_sub_norm_le (U X1 X2 : Space → Space) (y : Space) :
    ‖physCdiff U X1 y - physCdiff U X2 y‖ ≤
      gradSize U y * (hessSize X1 y + hessSize X2 y) +
        ‖fderiv ℝ X1 y - fderiv ℝ X2 y‖ * hessSize U y := by
  have hterm : ∀ j l : Fin 3,
      ‖((physPd U j y) l • physPd2 X1 j l y - (physPd X1 j y) l • physPd2 U j l y) -
          ((physPd U j y) l • physPd2 X2 j l y - (physPd X2 j y) l • physPd2 U j l y)‖ ≤
        gradSize U y * (‖physPd2 X1 j l y‖ + ‖physPd2 X2 j l y‖) +
          ‖fderiv ℝ X1 y - fderiv ℝ X2 y‖ * ‖physPd2 U j l y‖ := by
    intro j l
    have he : ((physPd U j y) l • physPd2 X1 j l y - (physPd X1 j y) l • physPd2 U j l y) -
          ((physPd U j y) l • physPd2 X2 j l y - (physPd X2 j y) l • physPd2 U j l y) =
        (physPd U j y) l • (physPd2 X1 j l y - physPd2 X2 j l y) -
          ((physPd X1 j y) l - (physPd X2 j y) l) • physPd2 U j l y := by
      rw [smul_sub, sub_smul]; abel
    have hg : |(physPd U j y) l| ≤ gradSize U y :=
      (abs_apply_le_norm _ l).trans (Finset.single_le_sum (f := fun j => ‖physPd U j y‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
    rw [he]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hg (norm_sub_le _ _) (norm_nonneg _)
        ((abs_nonneg _).trans hg)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (physPd_sub_apply_le X1 X2 y j l) (norm_nonneg _)
  have hdiff : physCdiff U X1 y - physCdiff U X2 y = ∑ j : Fin 3, ∑ l : Fin 3,
      (((physPd U j y) l • physPd2 X1 j l y - (physPd X1 j y) l • physPd2 U j l y) -
        ((physPd U j y) l • physPd2 X2 j l y - (physPd X2 j y) l • physPd2 U j l y)) := by
    simp only [physCdiff, ← Finset.sum_sub_distrib]
  rw [hdiff]
  calc _ ≤ ∑ j : Fin 3, ∑ l : Fin 3,
        ‖((physPd U j y) l • physPd2 X1 j l y - (physPd X1 j y) l • physPd2 U j l y) -
          ((physPd U j y) l • physPd2 X2 j l y - (physPd X2 j y) l • physPd2 U j l y)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, (gradSize U y * (‖physPd2 X1 j l y‖ + ‖physPd2 X2 j l y‖) +
          ‖fderiv ℝ X1 y - fderiv ℝ X2 y‖ * ‖physPd2 U j l y‖) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hterm j l
    _ = _ := by simp only [hessSize, mul_add, Finset.mul_sum, Finset.sum_add_distrib]

/-- The `(U⊗U):D²X` part of the residual difference. -/
theorem physUUD2_sub_norm_le (U X1 X2 : Space → Space) (y : Space) :
    ‖physUUD2 U X1 y - physUUD2 U X2 y‖ ≤ ‖U y‖ ^ 2 * (hessSize X1 y + hessSize X2 y) := by
  have hdiff : physUUD2 U X1 y - physUUD2 U X2 y = ∑ j : Fin 3, ∑ l : Fin 3,
      (U y j * U y l) • (physPd2 X1 j l y - physPd2 X2 j l y) := by
    simp only [physUUD2, ← Finset.sum_sub_distrib, smul_sub]
  rw [hdiff]
  calc _ ≤ ∑ j : Fin 3, ∑ l : Fin 3,
        ‖(U y j * U y l) • (physPd2 X1 j l y - physPd2 X2 j l y)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖U y‖ ^ 2 * (‖physPd2 X1 j l y‖ + ‖physPd2 X2 j l y‖) := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_mul, sq]
        exact mul_le_mul (mul_le_mul (abs_apply_le_norm _ j) (abs_apply_le_norm _ l)
          (abs_nonneg _) (norm_nonneg _)) (norm_sub_le _ _) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [hessSize, mul_add, Finset.mul_sum, Finset.sum_add_distrib]

/-- The `(DX + DXᵀ)∇p` part of the residual difference. -/
theorem physDXp_sub_norm_le (X1 X2 : Space → Space) (q : Space → ℝ) (y : Space) :
    ‖physDXp X1 q y - physDXp X2 q y‖ ≤
      6 * ‖fderiv ℝ X1 y - fderiv ℝ X2 y‖ * presGradSize q y := by
  set d := ‖fderiv ℝ X1 y - fderiv ℝ X2 y‖
  set M := 2 * d * presGradSize q y with hM
  have hd : 0 ≤ d := norm_nonneg _
  have hP : 0 ≤ presGradSize q y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM0 : 0 ≤ M := by positivity
  have hcomp : ∀ i : Fin 3, ‖(physDXp X1 q y - physDXp X2 q y) i‖ ≤ M := by
    intro i
    have he : (physDXp X1 q y - physDXp X2 q y) i = ∑ j : Fin 3,
        ((physPd X1 j y i - physPd X2 j y i) + (physPd X1 i y j - physPd X2 i y j)) *
          fderiv ℝ q y (coordinateVector j) := by
      simp only [physDXp, PiLp.sub_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [he, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hM, presGradSize, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    refine (abs_add_le _ _).trans ?_
    linarith [physPd_sub_apply_le X1 X2 y j i, physPd_sub_apply_le X1 X2 y i j]
  rw [EuclideanSpace.norm_eq]
  have hsq : ∑ i : Fin 3, ‖(physDXp X1 q y - physDXp X2 q y) i‖ ^ 2 ≤ (3 * M) ^ 2 := by
    have : ∀ i : Fin 3, ‖(physDXp X1 q y - physDXp X2 q y) i‖ ^ 2 ≤ M ^ 2 := fun i =>
      pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2
    calc _ ≤ ∑ _i : Fin 3, M ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = 3 * M ^ 2 := by simp
      _ ≤ (3 * M) ^ 2 := by nlinarith
  calc _ ≤ Real.sqrt ((3 * M) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 3 * M := Real.sqrt_sq (by positivity)
    _ = _ := by rw [hM]; ring

/-- **The pointwise residual comparison** (source 4276-4282): the difference of the unprojected Ward
residuals of two response pairs on the same background is bounded by `13 coefSize` times
`|DX₁ - DX₂| + |DY₁ - DY₂| + |D²X₁| + |D²X₂|`. -/
theorem wardEXY_sub_norm_le (ν μ R : ℝ) (hν : 0 ≤ ν) (U : ℝ → SpatialField)
    (p : ℝ → Space → ℝ) (X1 Y1 X2 Y2 : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    ‖wardEXY ν μ R U p X1 Y1 τ y - wardEXY ν μ R U p X2 Y2 τ y‖ ≤
      13 * coefSize ν U p τ y * (‖fderiv ℝ (X1 τ) y - fderiv ℝ (X2 τ) y‖ +
        ‖fderiv ℝ (Y1 τ) y - fderiv ℝ (Y2 τ) y‖ + (hessSize (X1 τ) y + hessSize (X2 τ) y)) := by
  set u := U τ y with hu
  set dX := ‖fderiv ℝ (X1 τ) y - fderiv ℝ (X2 τ) y‖
  set dY := ‖fderiv ℝ (Y1 τ) y - fderiv ℝ (Y2 τ) y‖
  set h := hessSize (X1 τ) y + hessSize (X2 τ) y
  have e : wardEXY ν μ R U p X1 Y1 τ y - wardEXY ν μ R U p X2 Y2 τ y =
      (2 : ℝ) • ((fderiv ℝ (Y1 τ) y - fderiv ℝ (Y2 τ) y) u) -
        (2 * ν) • (physCdiff (U τ) (X1 τ) y - physCdiff (U τ) (X2 τ) y) +
        (physUUD2 (U τ) (X1 τ) y - physUUD2 (U τ) (X2 τ) y) -
        (physDXp (X1 τ) (p τ) y - physDXp (X2 τ) (p τ) y) := by
    simp only [wardEXY, ContinuousLinearMap.sub_apply, smul_sub]
    abel
  rw [e]
  have t1 : ‖(2 : ℝ) • ((fderiv ℝ (Y1 τ) y - fderiv ℝ (Y2 τ) y) u)‖ ≤ 2 * (dY * ‖u‖) := by
    rw [norm_smul, Real.norm_two]
    gcongr
    exact ContinuousLinearMap.le_opNorm _ _
  have t2 : ‖(2 * ν) • (physCdiff (U τ) (X1 τ) y - physCdiff (U τ) (X2 τ) y)‖ ≤
      2 * ν * (gradSize (U τ) y * h + dX * hessSize (U τ) y) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact physCdiff_sub_norm_le _ _ _ _
  have t3 := physUUD2_sub_norm_le (U τ) (X1 τ) (X2 τ) y
  have t4 := physDXp_sub_norm_le (X1 τ) (X2 τ) (p τ) y
  set S := coefSize ν U p τ y with hS
  have hg0 : 0 ≤ gradSize (U τ) y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hh0 : 0 ≤ hessSize (U τ) y :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hp0 : 0 ≤ presGradSize (p τ) y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hhX : 0 ≤ h := add_nonneg
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hdX : 0 ≤ dX := norm_nonneg _
  have hdY : 0 ≤ dY := norm_nonneg _
  have hun : 0 ≤ ‖u‖ := norm_nonneg _
  have hνg : 0 ≤ ν * gradSize (U τ) y := mul_nonneg hν hg0
  have hνh : 0 ≤ ν * hessSize (U τ) y := mul_nonneg hν hh0
  have hS1 : ‖u‖ ≤ S := by rw [hS, coefSize]; nlinarith [sq_nonneg ‖u‖]
  have hS2 : ν * gradSize (U τ) y ≤ S := by rw [hS, coefSize]; nlinarith [sq_nonneg ‖u‖]
  have hS3 : ν * hessSize (U τ) y ≤ S := by rw [hS, coefSize]; nlinarith [sq_nonneg ‖u‖]
  have hS4 : ‖u‖ ^ 2 ≤ S := by rw [hS, coefSize]; nlinarith [sq_nonneg ‖u‖]
  have hS5 : presGradSize (p τ) y ≤ S := by rw [hS, coefSize]; nlinarith [sq_nonneg ‖u‖]
  set Dd := dX + dY + h with hDd
  have hD1 : dY ≤ Dd := by rw [hDd]; linarith
  have hD2 : h ≤ Dd := by rw [hDd]; linarith
  have hD3 : dX ≤ Dd := by rw [hDd]; linarith
  have p1 : dY * ‖u‖ ≤ Dd * S := mul_le_mul hD1 hS1 hun (by linarith)
  have p2 : ν * gradSize (U τ) y * h ≤ S * Dd := mul_le_mul hS2 hD2 hhX (by linarith)
  have p3 : dX * (ν * hessSize (U τ) y) ≤ Dd * S := mul_le_mul hD3 hS3 hνh (by linarith)
  have p4 : ‖u‖ ^ 2 * h ≤ S * Dd := mul_le_mul hS4 hD2 hhX (by linarith)
  have p5 : dX * presGradSize (p τ) y ≤ Dd * S := mul_le_mul hD3 hS5 hp0 (by linarith)
  calc _ ≤ ‖(2 : ℝ) • ((fderiv ℝ (Y1 τ) y - fderiv ℝ (Y2 τ) y) u)‖ +
        ‖(2 * ν) • (physCdiff (U τ) (X1 τ) y - physCdiff (U τ) (X2 τ) y)‖ +
        ‖physUUD2 (U τ) (X1 τ) y - physUUD2 (U τ) (X2 τ) y‖ +
        ‖physDXp (X1 τ) (p τ) y - physDXp (X2 τ) (p τ) y‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ ≤ 2 * (dY * ‖u‖) + 2 * ν * (gradSize (U τ) y * h + dX * hessSize (U τ) y) +
        ‖U τ y‖ ^ 2 * h + 6 * dX * presGradSize (p τ) y := by
        gcongr
    _ ≤ 13 * S * Dd := by nlinarith

/-! ## 7. Integration over the source measure -/

/-- Tonelli's inequality for `srcMeasure = π s^{-3/2} ds × dq/c dη` with the phase cell innermost
(no measurability needed). -/
theorem lintegral_srcMeasure_le (c : ℝ) (F : Chart → ℝ≥0∞) :
    ∫⁻ p, F p ∂srcMeasure c ≤ ENNReal.ofReal Real.pi * ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ∫⁻ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * F (s, (q, η)) := by
  rw [srcMeasure, lintegral_smul_measure, smul_eq_mul]
  gcongr
  rw [ageμ]
  refine (lintegral_prod_le _).trans ?_
  refine (lintegral_withDensity_le_lintegral_mul _ (measurable_ofReal_rpow _) _).trans ?_
  refine lintegral_mono fun s => ?_
  simp only [Pi.mul_apply]
  gcongr
  rw [Cyl.avgμ, lintegral_smul_measure, smul_eq_mul, Cyl.cellμ, Cyl.cell,
    Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    ← lintegral_prod_swap (fun z : ℝ × ℝ => F (s, z))]
  calc ENNReal.ofReal c⁻¹ * ∫⁻ z, F (s, z.swap) ∂(volume.prod (volume.restrict (Ico (-c / 2) (c / 2))))
      ≤ ENNReal.ofReal c⁻¹ * ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2), F (s, (q, η)) :=
        by gcongr; exact lintegral_prod_le _
    _ = _ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun η => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-! ## 8. Auxiliary inequalities -/

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at h
  have h2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rwa [h2] at h

theorem ennreal_rpow_half_sq (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem eLpNorm_two_eq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (f : α → E)
    (m : Measure α) : eLpNorm f 2 m = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂m) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- The phase-cell step: with `cellL2`-bounds `A`, `B` for `f`, `g ≥ 0` (and `g` measurable along
the cell), `∫ c⁻¹ |a(f+g)|² ≤ 2a²(A² + B²)`. -/
theorem cell_sum_le {c a : ℝ} (I : Set ℝ) {f g : ℝ → ℝ} (hf : ∀ q, 0 ≤ f q) (hg : ∀ q, 0 ≤ g q)
    (hgm : AEMeasurable g (volume.restrict I)) {A B : ℝ≥0∞}
    (hA : (∫⁻ q in I, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q) ^ 2) ^ (1 / 2 : ℝ) ≤ A)
    (hB : (∫⁻ q in I, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (g q) ^ 2) ^ (1 / 2 : ℝ) ≤ B)
    (ha : 0 ≤ a) :
    ∫⁻ q in I, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (a * (f q + g q)) ^ 2 ≤
      ENNReal.ofReal a ^ 2 * 2 * (A ^ 2 + B ^ 2) := by
  have hpt : ∀ q, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (a * (f q + g q)) ^ 2 ≤
      ENNReal.ofReal a ^ 2 * 2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q) ^ 2 +
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (g q) ^ 2) := by
    intro q
    rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_add (hf q) (hg q)]
    calc ENNReal.ofReal c⁻¹ * (ENNReal.ofReal a * (ENNReal.ofReal (f q) + ENNReal.ofReal (g q))) ^ 2
        = ENNReal.ofReal a ^ 2 * (ENNReal.ofReal c⁻¹ *
            (ENNReal.ofReal (f q) + ENNReal.ofReal (g q)) ^ 2) := by ring
      _ ≤ ENNReal.ofReal a ^ 2 * (ENNReal.ofReal c⁻¹ *
            (2 * (ENNReal.ofReal (f q) ^ 2 + ENNReal.ofReal (g q) ^ 2))) := by
          gcongr; exact ennreal_add_sq_le _ _
      _ = _ := by ring
  have hG : AEMeasurable (fun q => ENNReal.ofReal c⁻¹ * ENNReal.ofReal (g q) ^ 2)
      (volume.restrict I) := (hgm.ennreal_ofReal.pow_const 2).const_mul _
  have hfin : ENNReal.ofReal a ^ 2 * 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofNat_ne_top
  calc _ ≤ ∫⁻ q in I, ENNReal.ofReal a ^ 2 * 2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q) ^ 2 +
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (g q) ^ 2) := lintegral_mono hpt
    _ = ENNReal.ofReal a ^ 2 * 2 * ((∫⁻ q in I, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q) ^ 2) +
        ∫⁻ q in I, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (g q) ^ 2) := by
        rw [lintegral_const_mul' _ _ hfin, lintegral_add_right' _ hG]
    _ ≤ _ := by
        gcongr
        · rw [← ennreal_rpow_half_sq (∫⁻ q in I, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q) ^ 2)]
          exact ENNReal.pow_le_pow_left hA
        · rw [← ennreal_rpow_half_sq (∫⁻ q in I, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (g q) ^ 2)]
          exact ENNReal.pow_le_pow_left hB

/-- The age-power identity `s^{-3/2} s⁻¹ s⁵ = s^{5/2}` and the per-receiver real inequality. -/
theorem young_real_le {s b βv C P e4 νi : ℝ} (hs : 0 < s) (hsν : s ≤ νi) (hb : b ^ 2 ≤ βv ^ 2)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (he4 : 0 ≤ e4) (hb0 : 0 ≤ b) :
    s ^ (-3 / 2 : ℝ) * (13 * (Real.sqrt s)⁻¹ * b) ^ 2 * 2 *
        ((C * P * (e4 * s ^ (5 / 2 : ℝ))) ^ 2 + (C * P * (e4 * s ^ 3)) ^ 2) ≤
      338 * C ^ 2 * P ^ 2 * (1 + νi) * e4 ^ 2 * (s ^ (5 / 2 : ℝ) * βv ^ 2) := by
  set y := s ^ (-3 / 2 : ℝ) with hy
  set w := s ^ (5 / 2 : ℝ) with hw
  have hy0 : 0 ≤ y := Real.rpow_nonneg hs.le _
  have hw0 : 0 ≤ w := Real.rpow_nonneg hs.le _
  have hsq : (Real.sqrt s)⁻¹ ^ 2 = s⁻¹ := by rw [inv_pow, Real.sq_sqrt hs.le]
  have hw2 : w ^ 2 = s ^ 5 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  have hx : y * s⁻¹ * s ^ 5 = w := by
    rw [hy, hw, ← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_add hs,
      ← Real.rpow_add hs]
    norm_num
  have key : y * (13 * (Real.sqrt s)⁻¹ * b) ^ 2 * 2 *
        ((C * P * (e4 * w)) ^ 2 + (C * P * (e4 * s ^ 3)) ^ 2) =
      338 * b ^ 2 * C ^ 2 * P ^ 2 * e4 ^ 2 * (w * (1 + s)) := by
    rw [mul_pow (13 * (Real.sqrt s)⁻¹) b, mul_pow 13 (Real.sqrt s)⁻¹, hsq]
    linear_combination (338 * b ^ 2 * C ^ 2 * P ^ 2 * e4 ^ 2 * y * s⁻¹) * hw2 +
      (338 * b ^ 2 * C ^ 2 * P ^ 2 * e4 ^ 2 * (1 + s)) * hx
  rw [key]
  have h1 : 338 * b ^ 2 * C ^ 2 * P ^ 2 * e4 ^ 2 * (w * (1 + s)) ≤
      338 * βv ^ 2 * C ^ 2 * P ^ 2 * e4 ^ 2 * (w * (1 + νi)) := by
    gcongr
  calc _ ≤ 338 * βv ^ 2 * C ^ 2 * P ^ 2 * e4 ^ 2 * (w * (1 + νi)) := h1
    _ = _ := by ring

/-- The final real inequality of step (a). -/
theorem meanCmp_sqrt_le {C νi e4 E : ℝ} (k : ℕ) (hC : 0 ≤ C) (hνi : 1 ≤ νi) (he4 : 0 ≤ e4)
    (hE : 0 ≤ E) :
    Real.sqrt (2 * (Real.pi * (338 * C ^ 2 * (νi ^ k) ^ 2 * (1 + νi) * e4 ^ 2) * (C * νi ^ k) +
        (13 * (C * νi ^ k * E)) ^ 2)) ≤
      (1 + 1352 * Real.pi * C ^ 3 + 19 * C) * νi ^ (3 * k + 1) * (e4 + E) := by
  set P := νi ^ k with hP
  set V := νi ^ (3 * k + 1) with hV
  have hP1 : 1 ≤ P := one_le_pow₀ hνi
  have hV1 : 1 ≤ V := one_le_pow₀ hνi
  have hPV : P ≤ V := pow_le_pow_right₀ hνi (by omega)
  have hP3 : P ^ 3 * (1 + νi) ≤ 2 * V := by
    have : P ^ 3 * νi = V := by rw [hP, hV, ← pow_mul, ← pow_succ]; ring_nf
    nlinarith
  have hpi := Real.pi_pos
  set Pp := 676 * Real.pi * C ^ 3 * P ^ 3 * (1 + νi) with hPp
  have hPp0 : 0 ≤ Pp := by positivity
  have hX : 2 * (Real.pi * (338 * C ^ 2 * P ^ 2 * (1 + νi) * e4 ^ 2) * (C * P) +
      (13 * (C * P * E)) ^ 2) = Pp * e4 ^ 2 + 338 * (C * P * E) ^ 2 := by
    rw [hPp]; ring
  rw [hX]
  set T := (1 + Pp) * e4 + 19 * (C * P * E) with hT
  have hCPE : 0 ≤ C * P * E := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hXT : Pp * e4 ^ 2 + 338 * (C * P * E) ^ 2 ≤ T ^ 2 := by
    have : Pp ≤ (1 + Pp) ^ 2 := by nlinarith
    rw [hT]
    nlinarith [mul_nonneg (mul_nonneg hPp0 he4) hCPE, mul_nonneg he4 hCPE,
      mul_le_mul_of_nonneg_right this (sq_nonneg e4)]
  calc _ ≤ Real.sqrt (T ^ 2) := Real.sqrt_le_sqrt hXT
    _ = T := Real.sqrt_sq hT0
    _ ≤ (1 + 1352 * Real.pi * C ^ 3) * V * e4 + 19 * C * V * E := by
        rw [hT]
        have h1 : 1 + Pp ≤ (1 + 1352 * Real.pi * C ^ 3) * V := by
          rw [hPp]
          have hC3 : 0 ≤ C ^ 3 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hP3 (mul_nonneg hpi.le hC3)]
        have h2 : C * P * E ≤ C * V * E := by gcongr
        nlinarith
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC (zero_le_one.trans hV1)) he4,
          mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 1 + 1352 * Real.pi * C ^ 3)
            (zero_le_one.trans hV1)) hE]

theorem hessSize_nonneg (f : Space → Space) (y : Space) : 0 ≤ hessSize f y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem coefSize_nonneg {ν : ℝ} (hν : 0 ≤ ν) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (τ : ℝ) (y : Space) : 0 ≤ coefSize ν U p τ y := by
  have hg : 0 ≤ gradSize (U τ) y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hp : 0 ≤ presGradSize (p τ) y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hh := hessSize_nonneg (U τ) y
  unfold coefSize
  positivity

theorem max_zero_sq_le (x : ℝ) : max x 0 ^ 2 ≤ x ^ 2 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, zero_pow two_ne_zero]; positivity

/-! ## 9. Step (a) from the source facts -/

section Assembly

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

theorem actualE_eq_coef (T : LStr Pl K L) : actualE Pl K L μ T =
    coefOf L.ε⁻¹ (wardEXY L.ν μ L.ε⁻¹ L.U L.pres (actX Pl K L μ T) (actY Pl K L μ T)) := rfl

theorem meanE_eq_coef (T : LStr Pl K L) : meanE Pl K L μ T =
    coefOf L.ε⁻¹ (wardEXY L.ν μ L.ε⁻¹ L.U L.pres (mnX Pl K L μ T) (mnY Pl K L μ T)) := rfl

theorem cmpData_nonneg (T : LStr Pl K L) (τ : ℝ) (y : Space) : 0 ≤ cmpData Pl K L μ T τ y :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem hessData_nonneg (T : LStr Pl K L) (τ : ℝ) (y : Space) : 0 ≤ hessData Pl K L μ T τ y :=
  add_nonneg (hessSize_nonneg _ _) (hessSize_nonneg _ _)

theorem cmp_add_hess_le_jet (T : LStr Pl K L) (τ : ℝ) (y : Space) :
    cmpData Pl K L μ T τ y + hessData Pl K L μ T τ y ≤ jetSize Pl K L μ T τ y := by
  have h1 := norm_sub_le (fderiv ℝ (actX Pl K L μ T τ) y) (fderiv ℝ (mnX Pl K L μ T τ) y)
  have h2 := norm_sub_le (fderiv ℝ (actY Pl K L μ T τ) y) (fderiv ℝ (mnY Pl K L μ T τ) y)
  unfold cmpData jetSize
  linarith

theorem remTerm_nonneg {Br : ℝ → Space → ℝ} (hBr0 : ∀ τ y, 0 ≤ Br τ y) (T : LStr Pl K L)
    (p : Chart) : 0 ≤ remTerm Pl K L μ Br T p := by
  have hj : 0 ≤ jetSize Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) :=
    (add_nonneg (cmpData_nonneg Pl K L μ T _ _) (hessData_nonneg Pl K L μ T _ _)).trans
      (cmp_add_hess_le_jet Pl K L μ T _ _)
  have hb := hBr0 (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)
  unfold remTerm
  positivity

/-- The pointwise bound of `actualE - meanE` by the localized and the remainder parts. -/
theorem meanCmp_pointwise {Bl Br : ℝ → Space → ℝ} {βl : ℝ → ℝ → ℝ}
    (hsplit : ∀ τ y, coefSize L.ν L.U L.pres τ y ≤ Bl τ y + Br τ y)
    (hBr0 : ∀ τ y, 0 ≤ Br τ y)
    (hβ : ∀ (τ : ℝ) (p : Chart), 0 < p.1 → p.1 ≤ 1 / L.ν →
      Bl τ (NearInst.chartY L.ε⁻¹ p) ≤ βl p.1 p.2.2)
    (h3 : YoungSupportAt Pl K L μ) (T : LStr Pl K L) (p : Chart) :
    ‖actualE Pl K L μ T p - meanE Pl K L μ T p‖ ≤
      13 * (Real.sqrt p.1)⁻¹ * max (βl p.1 p.2.2) 0 *
          (cmpData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) +
            hessData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)) +
        13 * remTerm Pl K L μ Br T p := by
  have hrem : remTerm Pl K L μ Br T p = (Real.sqrt p.1)⁻¹ *
      Br (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) *
        jetSize Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) := rfl
  have hcm0 := cmpData_nonneg Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)
  have hhs0 := hessData_nonneg Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)
  have hcj := cmp_add_hess_le_jet Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)
  have hS0 := coefSize_nonneg L.ν_pos.le L.U L.pres (NearInst.chartTau L.ε⁻¹ p)
    (NearInst.chartY L.ε⁻¹ p)
  have hBr := hBr0 (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)
  have hr0 := remTerm_nonneg Pl K L μ hBr0 T p
  have hbase : ‖actualE Pl K L μ T p - meanE Pl K L μ T p‖ ≤ (Real.sqrt p.1)⁻¹ *
      (13 * coefSize L.ν L.U L.pres (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) *
        (cmpData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) +
          hessData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p))) := by
    rw [actualE_eq_coef, meanE_eq_coef]
    refine (coefOf_sub_norm_le _ _ _ p).trans ?_
    gcongr
    exact wardEXY_sub_norm_le L.ν μ L.ε⁻¹ L.ν_pos.le L.U L.pres _ _ _ _ _ _
  have hrhs0 : 0 ≤ 13 * (Real.sqrt p.1)⁻¹ * max (βl p.1 p.2.2) 0 *
          (cmpData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) +
            hessData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)) +
        13 * remTerm Pl K L μ Br T p := by positivity
  rcases le_or_gt p.1 0 with hp0 | hp0
  · have hz : (Real.sqrt p.1)⁻¹ = 0 := by rw [Real.sqrt_eq_zero'.2 hp0, inv_zero]
    rw [hz, zero_mul] at hbase
    exact hbase.trans hrhs0
  rcases le_or_gt p.1 (1 / L.ν) with hp1 | hp1
  · have hB := hβ (NearInst.chartTau L.ε⁻¹ p) p hp0 hp1
    have hS : coefSize L.ν L.U L.pres (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) ≤
        max (βl p.1 p.2.2) 0 + Br (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) :=
      (hsplit _ _).trans (by linarith [le_max_left (βl p.1 p.2.2) 0])
    refine hbase.trans ?_
    rw [hrem]
    have hsq : 0 ≤ (Real.sqrt p.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    set a := cmpData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) +
      hessData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)
    have ha : 0 ≤ a := add_nonneg hcm0 hhs0
    have key : coefSize L.ν L.U L.pres (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) * a ≤
        max (βl p.1 p.2.2) 0 * a + Br (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) *
          jetSize Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) := by
      calc _ ≤ (max (βl p.1 p.2.2) 0 + Br (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)) *
            a := mul_le_mul_of_nonneg_right hS ha
        _ = max (βl p.1 p.2.2) 0 * a +
            Br (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) * a := by ring
        _ ≤ _ := by gcongr
    calc (Real.sqrt p.1)⁻¹ * (13 * coefSize L.ν L.U L.pres (NearInst.chartTau L.ε⁻¹ p)
            (NearInst.chartY L.ε⁻¹ p) * a)
        = 13 * (Real.sqrt p.1)⁻¹ * (coefSize L.ν L.U L.pres (NearInst.chartTau L.ε⁻¹ p)
            (NearInst.chartY L.ε⁻¹ p) * a) := by ring
      _ ≤ 13 * (Real.sqrt p.1)⁻¹ * (max (βl p.1 p.2.2) 0 * a +
            Br (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) *
              jetSize Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)) := by
          gcongr
      _ = _ := by ring
  · obtain ⟨hc, hh⟩ := h3 T p hp1
    rw [hc, hh, add_zero, mul_zero, mul_zero] at hbase
    exact hbase.trans hrhs0

/-- **Step (a) at one regime** (source 5415-5448 with 5272-5289): the geometric comparison, the
Hessian bound, the young support, the measurability of `meanE` and the coefficient split give
step (a) for swirl-free thin stresses, `MeanComparisonAziAt` (source 5376: `T = M_U w`). -/
theorem meanComparisonAt_of {C : ℝ} {k : ℕ} (hC : 0 ≤ C) (hν1 : L.ν ≤ 1)
    (h1 : GeomComparisonAt Pl K L μ C k) (h2 : HessianBoundAt Pl K L μ C k)
    (h3 : YoungSupportAt Pl K L μ) (h4 : MeanMeasurableAt Pl K L μ)
    (h5 : BackgroundSplitAt Pl K L μ C k) :
    MeanComparisonAziAt Pl K L μ (1 + 1352 * Real.pi * C ^ 3 + 19 * C) (3 * k + 1) := by
  obtain ⟨Bl, Br, βl, hsplit, hBr0, hβ, hw, hrem⟩ := h5
  intro T hTz
  refine ⟨h4 T, ?_⟩
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hνi : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hpi := Real.pi_pos
  have hE0 : 0 ≤ L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) := by positivity
  have he40 : 0 ≤ L.ε ^ 4 := by positivity
  have hP0 : 0 ≤ L.ν⁻¹ ^ k := by positivity
  by_cases hNt : oldN1 Pl K L T = ⊤
  · rw [hNt]
    have hpos : 0 < (1 + 1352 * Real.pi * C ^ 3 + 19 * C) * L.ν⁻¹ ^ (3 * k + 1) *
        (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by positivity
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  set N := oldN1 Pl K L T with hN
  set E := L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) with hE
  set e4 := L.ε ^ 4 with he4
  set P := L.ν⁻¹ ^ k with hP
  set c := cOf L.ν with hc
  set Q := 338 * C ^ 2 * P ^ 2 * (1 + L.ν⁻¹) * e4 ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQN : ENNReal.ofReal Q * N ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hNt)
  set Dd : Chart → ℝ := fun p =>
    cmpData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) +
      hessData Pl K L μ T (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) with hDd
  set h1f : Chart → ℝ := fun p => 13 * (Real.sqrt p.1)⁻¹ * max (βl p.1 p.2.2) 0 * Dd p with hh1f
  set g := remTerm Pl K L μ Br T with hg
  -- pointwise
  have hpt : ∀ p, ‖(actualE Pl K L μ T - meanE Pl K L μ T) p‖ₑ ≤
      ENNReal.ofReal (h1f p) + ‖13 * g p‖ₑ := by
    intro p
    have hb := meanCmp_pointwise Pl K L μ hsplit hBr0 hβ h3 T p
    have hg0 : 0 ≤ 13 * g p := mul_nonneg (by norm_num) (remTerm_nonneg Pl K L μ hBr0 T p)
    rw [Pi.sub_apply, ← ofReal_norm_eq_enorm, Real.enorm_eq_ofReal hg0]
    exact (ENNReal.ofReal_le_ofReal hb).trans ENNReal.ofReal_add_le
  -- the remainder part
  have hBm : AEMeasurable (fun p => ‖13 * g p‖ₑ ^ 2) (srcMeasure c) :=
    (((hrem T).1.const_mul 13).enorm).pow_const 2
  have hB : ∫⁻ p, ‖13 * g p‖ₑ ^ 2 ∂srcMeasure c ≤
      ENNReal.ofReal ((13 * (C * P * E)) ^ 2) * N ^ 2 := by
    have he : eLpNorm (fun p => 13 * g p) 2 (srcMeasure c) ≤
        ENNReal.ofReal (13 * (C * P * E)) * N := by
      have hfun : (fun p => 13 * g p) = (13 : ℝ) • g := by funext p; simp [smul_eq_mul]
      rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num)]
      calc ENNReal.ofReal 13 * eLpNorm g 2 (srcMeasure c)
          ≤ ENNReal.ofReal 13 * (ENNReal.ofReal (C * P * E) * N) := by
            gcongr; exact (hrem T).2
        _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    rw [eLpNorm_two_eq] at he
    have := ENNReal.pow_le_pow_left he (n := 2)
    rwa [ennreal_rpow_half_sq, mul_pow, ← ENNReal.ofReal_pow (by positivity)] at this
  -- the localized part
  have hA : ∫⁻ p, ENNReal.ofReal (h1f p) ^ 2 ∂srcMeasure c ≤
      ENNReal.ofReal Real.pi * (ENNReal.ofReal Q * N ^ 2 * ENNReal.ofReal (C * P)) := by
    refine (lintegral_srcMeasure_le c _).trans ?_
    gcongr ENNReal.ofReal Real.pi * ?_
    have hstep : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ∫⁻ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
          ENNReal.ofReal c⁻¹ * ENNReal.ofReal (h1f (s, (q, η))) ^ 2 ≤
        (Ioc (0 : ℝ) (1 / L.ν)).indicator (fun s => ENNReal.ofReal Q * N ^ 2 *
          ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * βl s η ^ 2)) s := by
      intro s hs
      rcases le_or_gt s (1 / L.ν) with hs1 | hs1
      · rw [indicator_of_mem (show s ∈ Ioc (0 : ℝ) (1 / L.ν) from ⟨hs, hs1⟩)]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ hQN]
        refine lintegral_mono fun η => ?_
        have hcmpb := h1 T hTz s ⟨hs, hs1⟩ η
        obtain ⟨hhm, hhb⟩ := h2 T s ⟨hs, hs1⟩ η
        have hb0 : 0 ≤ max (βl s η) 0 := le_max_right _ _
        have ha0 : 0 ≤ 13 * (Real.sqrt s)⁻¹ * max (βl s η) 0 := by positivity
        have hα0 : 0 ≤ C * P * (e4 * s ^ (5 / 2 : ℝ)) := by
          have : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt hs) _
          positivity
        have hβ0 : 0 ≤ C * P * (e4 * s ^ 3) := by
          have : 0 ≤ s := le_of_lt hs
          positivity
        have hy0 : 0 ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt hs) _
        have hcell := cell_sum_le (c := c) (a := 13 * (Real.sqrt s)⁻¹ * max (βl s η) 0)
          (Ico (-c / 2) (c / 2))
          (f := fun q => cmpData Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
            (NearInst.chartY L.ε⁻¹ (s, (q, η))))
          (g := fun q => hessData Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
            (NearInst.chartY L.ε⁻¹ (s, (q, η))))
          (fun q => cmpData_nonneg Pl K L μ T _ _) (fun q => hessData_nonneg Pl K L μ T _ _)
          hhm hcmpb hhb ha0
        have hreal := young_real_le (s := s) (b := max (βl s η) 0) (βv := βl s η) (C := C)
          (P := P) (e4 := e4) (νi := L.ν⁻¹) hs (by rwa [one_div] at hs1) (max_zero_sq_le _)
          hC hP0 he40 hb0
        calc ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ∫⁻ q in Ico (-c / 2) (c / 2),
              ENNReal.ofReal c⁻¹ * ENNReal.ofReal (h1f (s, (q, η))) ^ 2
            ≤ ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
                (ENNReal.ofReal (13 * (Real.sqrt s)⁻¹ * max (βl s η) 0) ^ 2 * 2 *
                  ((ENNReal.ofReal (C * P * (e4 * s ^ (5 / 2 : ℝ))) * N) ^ 2 +
                    (ENNReal.ofReal (C * P * (e4 * s ^ 3)) * N) ^ 2)) := by
              gcongr
          _ = (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
                ENNReal.ofReal (13 * (Real.sqrt s)⁻¹ * max (βl s η) 0) ^ 2 * 2 *
                  (ENNReal.ofReal (C * P * (e4 * s ^ (5 / 2 : ℝ))) ^ 2 +
                    ENNReal.ofReal (C * P * (e4 * s ^ 3)) ^ 2)) * N ^ 2 := by ring
          _ ≤ (ENNReal.ofReal Q * ENNReal.ofReal (s ^ (5 / 2 : ℝ) * βl s η ^ 2)) * N ^ 2 := by
              gcongr ?_ * _
              rw [← ENNReal.ofReal_pow ha0, ← ENNReal.ofReal_pow hα0, ← ENNReal.ofReal_pow hβ0,
                ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul hy0,
                ← ENNReal.ofReal_ofNat 2,
                ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) *
                  (13 * (Real.sqrt s)⁻¹ * max (βl s η) 0) ^ 2),
                ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) *
                  (13 * (Real.sqrt s)⁻¹ * max (βl s η) 0) ^ 2 * 2),
                ← ENNReal.ofReal_mul hQ0]
              exact ENNReal.ofReal_le_ofReal hreal
          _ = _ := by ring
      · rw [indicator_of_notMem (fun h => absurd h.2 (not_le.2 hs1))]
        have hz : ∀ q η : ℝ, h1f (s, (q, η)) = 0 := by
          intro q η
          obtain ⟨hc', hh'⟩ := h3 T (s, (q, η)) hs1
          simp only [hh1f, hDd, hc', hh', add_zero, mul_zero]
        simp [hz]
    calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
          ∫⁻ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal (h1f (s, (q, η))) ^ 2
        ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioc (0 : ℝ) (1 / L.ν)).indicator (fun s => ENNReal.ofReal Q *
            N ^ 2 * ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * βl s η ^ 2)) s :=
          setLIntegral_mono' measurableSet_Ioi hstep
      _ ≤ ∫⁻ s, (Ioc (0 : ℝ) (1 / L.ν)).indicator (fun s => ENNReal.ofReal Q *
            N ^ 2 * ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * βl s η ^ 2)) s :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ s in Ioc (0 : ℝ) (1 / L.ν), ENNReal.ofReal Q * N ^ 2 *
            ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * βl s η ^ 2) :=
          lintegral_indicator measurableSet_Ioc _
      _ = ENNReal.ofReal Q * N ^ 2 * ∫⁻ s in Ioc (0 : ℝ) (1 / L.ν),
            ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * βl s η ^ 2) :=
          lintegral_const_mul' _ _ hQN
      _ ≤ ENNReal.ofReal Q * N ^ 2 * ENNReal.ofReal (C * P) := by gcongr
  -- assembly
  set X := 2 * (Real.pi * Q * (C * P) + (13 * (C * P * E)) ^ 2) with hX
  have hX0 : 0 ≤ X := by positivity
  have hI : ∫⁻ p, ‖(actualE Pl K L μ T - meanE Pl K L μ T) p‖ₑ ^ 2 ∂srcMeasure c ≤
      ENNReal.ofReal X * N ^ 2 := by
    calc _ ≤ ∫⁻ p, (ENNReal.ofReal (h1f p) + ‖13 * g p‖ₑ) ^ 2 ∂srcMeasure c :=
          lintegral_mono fun p => ENNReal.pow_le_pow_left (hpt p)
      _ ≤ ∫⁻ p, 2 * (ENNReal.ofReal (h1f p) ^ 2 + ‖13 * g p‖ₑ ^ 2) ∂srcMeasure c :=
          lintegral_mono fun p => ennreal_add_sq_le _ _
      _ = 2 * (∫⁻ p, ENNReal.ofReal (h1f p) ^ 2 ∂srcMeasure c +
            ∫⁻ p, ‖13 * g p‖ₑ ^ 2 ∂srcMeasure c) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_add_right' _ hBm]
      _ ≤ 2 * (ENNReal.ofReal Real.pi * (ENNReal.ofReal Q * N ^ 2 * ENNReal.ofReal (C * P)) +
            ENNReal.ofReal ((13 * (C * P * E)) ^ 2) * N ^ 2) := by gcongr
      _ = ENNReal.ofReal X * N ^ 2 := by
          have hXe : ENNReal.ofReal X = 2 * (ENNReal.ofReal Real.pi * ENNReal.ofReal Q *
              ENNReal.ofReal (C * P) + ENNReal.ofReal ((13 * (C * P * E)) ^ 2)) := by
            rw [hX, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
              ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ Real.pi * Q * (C * P))
                (by positivity : (0 : ℝ) ≤ (13 * (C * P * E)) ^ 2),
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.pi * Q),
              ENNReal.ofReal_mul hpi.le]
          rw [hXe]
          ring
  rw [eLpNorm_two_eq]
  calc (∫⁻ p, ‖(actualE Pl K L μ T - meanE Pl K L μ T) p‖ₑ ^ 2 ∂srcMeasure c) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal X * N ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hI (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt X) * N := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hX0 (by norm_num), ← Real.sqrt_eq_rpow,
          ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ _ := by
        gcongr
        exact meanCmp_sqrt_le k hC hνi he40 hE0

theorem pnu_mono {ν C C' : ℝ} {k k' : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') : C * ν⁻¹ ^ k ≤ C' * ν⁻¹ ^ k' := by
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hP : ν⁻¹ ^ k ≤ ν⁻¹ ^ k' := pow_le_pow_right₀ h1 hk
  have hP0 : 0 ≤ ν⁻¹ ^ k := by positivity
  calc C * ν⁻¹ ^ k ≤ C' * ν⁻¹ ^ k := mul_le_mul_of_nonneg_right hC hP0
    _ ≤ C' * ν⁻¹ ^ k' := mul_le_mul_of_nonneg_left hP hC'

theorem geomComparisonAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : GeomComparisonAt Pl K L μ C k) :
    GeomComparisonAt Pl K L μ C' k' := by
  intro T hTz s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact bound_mono L.ν_pos hν1 (mul_nonneg he hs0) hC hC' hk (h T hTz s hs η)

theorem hessianBoundAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : HessianBoundAt Pl K L μ C k) :
    HessianBoundAt Pl K L μ C' k' := by
  intro T s hs η
  have hs0 : 0 ≤ s ^ 3 := pow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h T s hs η).1, bound_mono L.ν_pos hν1 (mul_nonneg he hs0) hC hC' hk (h T s hs η).2⟩

theorem backgroundSplitAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : BackgroundSplitAt Pl K L μ C k) :
    BackgroundSplitAt Pl K L μ C' k' := by
  obtain ⟨Bl, Br, βl, hsplit, hBr0, hβ, hw, hrem⟩ := h
  refine ⟨Bl, Br, βl, hsplit, hBr0, hβ,
    hw.trans (ENNReal.ofReal_le_ofReal (pnu_mono L.ν_pos hν1 hC hC' hk)), fun T => ?_⟩
  have hE0 : 0 ≤ L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) := by
    have := L.ε_pos; positivity
  exact ⟨(hrem T).1, bound_mono L.ν_pos hν1 hE0 hC hC' hk (hrem T).2⟩

end Assembly

/-- **Step (a) along the sequence** (source 5415-5448 with 5272-5289), for swirl-free thin
stresses (source 5376). -/
theorem SeqData.meanComparison_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : D.GeomComparison) (h2 : D.HessianBound) (h3 : D.YoungSupport)
    (h4 : D.MeanMeasurable) (h5 : D.BackgroundSplit) : D.MeanComparisonAzi := by
  obtain ⟨C1, k1, e1⟩ := h1
  obtain ⟨C2, k2, e2⟩ := h2
  obtain ⟨C5, k5, e5⟩ := h5
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  set C : ℝ := |C1| + |C2| + |C5| with hCdef
  set k : ℕ := k1 + k2 + k5 with hkdef
  have hC0 : 0 ≤ C := by positivity
  have hC1 : C1 ≤ C := (le_abs_self C1).trans (by rw [hCdef]; linarith [abs_nonneg C2, abs_nonneg C5])
  have hC2 : C2 ≤ C := (le_abs_self C2).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C5])
  have hC5 : C5 ≤ C := (le_abs_self C5).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C2])
  refine ⟨1 + 1352 * Real.pi * C ^ 3 + 19 * C, 3 * k + 1, ?_⟩
  filter_upwards [e1, e2, h3, h4, e5, hle] with n a1 a2 a3 a4 a5 hν z hz
  have hν1 : (D.level n).ν ≤ 1 := hν.1
  exact meanComparisonAt_of D.Pl D.K (D.level n) (D.mu n z) hC0 hν1
    (geomComparisonAt_mono D.Pl D.K (D.level n) (D.mu n z) hν1 hC1 hC0 (by omega) (a1 z hz))
    (hessianBoundAt_mono D.Pl D.K (D.level n) (D.mu n z) hν1 hC2 hC0 (by omega) (a2 z hz))
    (a3 z hz) (a4 z hz)
    (backgroundSplitAt_mono D.Pl D.K (D.level n) (D.mu n z) hν1 hC5 hC0 (by omega) (a5 z hz))

/-! ## 10. The exact formula for `Y^mt` (source 5427-5432) -/

/-- The phase-free `D_{μ'}Z = -½ y·∇Z - νΔZ + (μ' - ½)Z` (source 4140-4141 without `∂_τ`). -/
def dmuFree (ν μ' : ℝ) (Z : Vec3 → Vec3) (y : Vec3) : Vec3 :=
  -(1 / 2 : ℝ) • fderiv ℝ Z y y - ν • vecLap Z y + (μ' - 1 / 2) • Z y

theorem YmtFun_eq_dmuFree (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) :
    YmtFun c ν ε μ χo χy M = dmuFree ν (μ + 1) (Xmt c ν ε μ χo χy M) := by
  funext y
  have h : (μ + 1 - 1 / 2 : ℝ) = μ + 1 / 2 := by ring
  simp only [YmtFun, dmuFree, h]

/-- **The shifted dilation identity of the uncut Newton fields** (source 5383-5387): the uncut
zero-width fields are harmonic outside the old source disk, and the `t`-integral of 4776-4782 gives
`(-½x·∇ + μ + ½)(V_μ - V_{μ+1}) = V_μ` there; hence at young receivers `|y'| ≥ R√ν`
(`R = ε⁻¹`), `D_{μ+1}(W^mt_μ - W^mt_{μ+1}) = W^mt_μ`. -/
def MeanShiftIdentity : Prop :=
  ∀ (c ν ε μ : ℝ) (χo χy : ℝ → ℝ), LHyp c ν ε μ χo χy → ∀ M : Chart → Mat3,
    OldThinFinite c ν M → ∀ y : Vec3, Real.sqrt ν / ε ≤ cylR y →
      dmuFree ν (μ + 1) (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) y =
        youngW c ν ε μ χo M y

/-- **The exact formula** (source 5427-5432):
`Y^mt = 𝒞_{χ_y}W_μ + [D_{μ+1}, 𝒞_{χ_y}](W_μ - W_{μ+1})` at the receiver `y`. -/
def MeanYFormula (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (y : Vec3) : Prop :=
  YmtFun c ν ε μ χo χy M y =
    streamCut ν ε χy (youngW c ν ε μ χo M) y +
      (dmuFree ν (μ + 1)
          (streamCut ν ε χy (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y -
        streamCut ν ε χy
          (dmuFree ν (μ + 1) (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y)

theorem cylR_rayPt_pos {y : Vec3} (hy : 0 < cylR y) {ρ : ℝ} (hρ : 0 < ρ) :
    cylR (rayPt y ρ) = ρ := by
  have hr2 : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have h : (ρ * (y 0 / cylR y)) ^ 2 + (ρ * (y 1 / cylR y)) ^ 2 = ρ ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, div_pow, ← mul_add, ← add_div, ← hr2,
      div_self (pow_ne_zero 2 hy.ne'), mul_one]
  show Real.sqrt ((rayPt y ρ) 0 ^ 2 + (rayPt y ρ) 1 ^ 2) = ρ
  simp only [rayPt, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h, Real.sqrt_sq hρ.le]

/-- The exact formula from the shifted dilation identity: along the outward ray from a young
receiver every point is young, so the stream cutoff of `D_{μ+1}(W_μ - W_{μ+1})` is that of `W_μ`. -/
theorem meanYFormula_of_shift (hS : MeanShiftIdentity) {c ν ε μ : ℝ} {χo χy : ℝ → ℝ}
    (hL : LHyp c ν ε μ χo χy) {M : Chart → Mat3} (hM : OldThinFinite c ν M) {y : Vec3}
    (hy : Real.sqrt ν / ε ≤ cylR y) : MeanYFormula c ν ε μ χo χy M y := by
  have hpos : 0 < cylR y :=
    lt_of_lt_of_le (div_pos (Real.sqrt_pos.2 hL.nu_pos) hL.eps_pos) hy
  have hZ : ∀ x : Vec3, Real.sqrt ν / ε ≤ cylR x →
      dmuFree ν (μ + 1) (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) x =
        youngW c ν ε μ χo M x := fun x hx => hS c ν ε μ χo χy hL M hM x hx
  have hpsi : streamPsi (dmuFree ν (μ + 1) (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y =
      streamPsi (youngW c ν ε μ χo M) y := by
    unfold streamPsi
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    have hρ' : cylR y < ρ := hρ
    rw [hZ (rayPt y ρ) (by rw [cylR_rayPt_pos hpos (hpos.trans hρ')]; exact hy.trans hρ'.le)]
  have hcut : streamCut ν ε χy
      (dmuFree ν (μ + 1) (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y =
      streamCut ν ε χy (youngW c ν ε μ χo M) y := by
    unfold streamCut
    rw [hZ y hy, hpsi]
  unfold MeanYFormula
  rw [YmtFun_eq_dmuFree, hcut]
  show dmuFree ν (μ + 1) (streamCut ν ε χy (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y =
    _
  abel

end UnforcedLeray.Short.PartIIIb.Concrete
