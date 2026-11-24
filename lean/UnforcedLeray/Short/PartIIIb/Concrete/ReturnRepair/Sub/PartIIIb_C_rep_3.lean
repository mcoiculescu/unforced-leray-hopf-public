import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.ChgPt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.HolderConv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# Design of `repair:body-error` (`PartIII-b:C/rep/3`, source 5196-5299)

Source of record: `the November 2 reference manuscript` (73 pages): 5196-5299
(`repair:body-error`), 5169-5176 (`repair:source`), 5131-5139 (the background bounds of the
section), 5691-5692 (the repair response of the error velocity).

The target `BodyErrorAt` (`Estimates.lean` §4) bounds `‖(wardOps ..).2.2 (repPart (M_Uw))‖`.  By
the Ward pin (`RegimePins.ward`, `IsWardTriple`; the thin representative of `(0, T₂)` is `0`) its
coefficient is `coefOf R (wardEXY ν μ R U p X Y)`: the full unprojected residual
`Ẽ(U;X,Y) = 2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX+DXᵀ)∇p` (5197-5203) on `U = V + r_b` with the exact
pressure `p`, `X = repX`, `Y = repY` the Ward fields of the old repair source, `R = ε⁻¹`.

## The split (source 5224-5268)

`Ẽ(U, p) = Ẽ(V, p_V) + [Ẽ(U, p) - Ẽ(V, p_V)]`, `p_V` the canonical pressure of `V`
(`∇p_V = -(I-ℙ)(V·∇V)`, 5245-5246).  `F_r = ‖χ_o(r_b⊗w+w⊗r_b)‖_{L²_τL^{22/19}}` is
`phaseL2Lr (2εc) (22/19) (repStressPhys w)`.

* **(A) `RepAgeSurfAt`** (5203-5210, 5236-5244): the age-surface bounds of the response.
* **(H) `RepVBgAt`** (5131-5139, 5225-5235, 5245-5247, 5255-5258): the background bounds of `V`
  and the canonical pressure `p_V` (existential in `RepVBg`).
* **(B) `VResidualOf`** (5224-5253): `R⁻¹‖Ẽ(V;X,Y)‖_{Y_2} ≤ P_ν ε^{101/22}F_r` from (A) and (H).
* **(C) `RepJetAt`** (5212-5223, 5259-5268): `DY, DX, D²X` in `Y_{22/3}`, `≤ P_ν ε^{46/11}F_r`.
  With `D.CoefChg` (`PartIII-b:C/rep/8/2/pres/4`: `‖|r_b| + |Dr_b| + |D²r_b|‖_{Y_{11/4}} ≤ P_νρ`,
  `|U| + |V| ≤ P_ν`, 5134-5139 through `RepairDerivBound`) and the pressure clause of (H),
  **`repCorrAt_of`** (proved here; `wardEXYChgPt`, `ringHolderConv`, `4/11 + 3/22 = 1/2`) gives the
  exact-pressure and `r_b` corrections `≤ P_ν R⁻¹ρε^{46/11}F_r` (5254-5268).
* **(D) `bodyErrorAt_of_parts`, `bodyError_of`** (proved here): the pin, the split, `repair:source`
  `F_r ≤ P_νρR|N_ν|G(w)` (5169-5176) and `101/22 + 3/11 - 1 = 85/22`, `46/11 + 2·3/11 = 52/11`
  (5250-5262, 5290-5294).

All chart-form norms read fields at azimuth `0` (`ringRead`, `ringPhysμ = πR²s^{-5/2}dς`,
`coefOf`, `srcMeasure`; `Sub/PartIII-b_C_rep_8_2/PresCoef.lean`), so every statement is true
irrespective of the symmetry of the fields; for axisymmetric fields they are the `Y_r` norms
(2681-2689).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Norms on age surfaces and of the background coefficient -/

/-- `sup_{age R y = s} f(y)`: the supremum over the age surface `|y'| = R/√s` (source 5206-5210:
"with the spatial supremum understood on that age surface"). -/
def ageSurfSup (R s : ℝ) (f : Space → ℝ) : ℝ≥0∞ :=
  ⨆ (y : Space) (_ : age R y = s), ENNReal.ofReal (f y)

/-- `‖f(s)‖_{L²_τL^∞_y}` on the age surface `s`, over one period `P` with `dτ/P`
(source 5205-5210). -/
def ageSurfL2 (P R s : ℝ) (f : ℝ → Space → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal P⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, ageSurfSup R s (f τ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- `‖sup_q |v(s,q,·)|‖_{L²_η}` (source 5227-5232; `V = √s v`) of the physical field `V`, read at
the chart points `(s, (q, η))` (`q` in one cell, essential supremum; SP 2717 `etaL2QSup` without
the weight `W ≥ 1`). -/
def vEtaSup (R c : ℝ) (V : ℝ → SpatialField) (s : ℝ) : ℝ≥0∞ :=
  (∫⁻ η : ℝ, (essSup (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
      ‖V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))
    (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- The thin-coefficient density `|V ⊗ V| + Σ_j|∂_jV| + Σ_{j,l}|∂_j∂_lV|` (source 5234-5235). -/
def vCoefDens (V : Space → Space) (y : Space) : ℝ :=
  ‖V y‖ ^ 2 + ∑ j : Fin 3, ‖physPd V j y‖ + ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 V j l y‖

/-! ## 2. The statements at one regime -/

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **(A) The age-surface bounds of the repair response** (source 5203-5210, 5236-5244).  The
pointwise gradient kernel of the separated resolvent has `L^{22/3}` norm `CD^{-101/22}` outside
distance `D` (`-5 + 3/(22/3) = -101/22`); at age `0 < s ≤ 1/ν` the distance from the old disk
`|z'| ≤ R√(5ν/6)` is `≥ cR/√s`, so
`‖DX(s)‖_{L²_τL^∞_y} + ‖DY(s)‖_{L²_τL^∞_y} ≤ P_ν ε^{101/22}s^{101/44}F_r` (spatial supremum on the
age surface).  The `q = ∞` endpoint of the phase-norm argument (dilation is an isometry of `L^∞`;
Young bounds `Z` and `BZ` in `L²_τL^∞_y`, 5238-5244) gives the ordinary bound
`‖DX‖_{L^∞_τL^∞_y} + ‖D²X‖_{L^∞_τL^∞_y} ≤ P_ν ε^{101/22}F_r` at every phase and point (`D²X` has an
additional curvature power, 5267).  `X = 0` off the young region `|y'| ≥ R√ν`. -/
def RepAgeSurfAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ w : LVel Pl L,
    (∀ s : ℝ, 0 < s → L.ν * s ≤ 1 →
      ageSurfL2 (2 * L.ε * cOf L.ν) L.ε⁻¹ s (fun τ y => ‖fderiv ℝ (repX Pl K L μ w τ) y‖) +
          ageSurfL2 (2 * L.ε * cOf L.ν) L.ε⁻¹ s (fun τ y => ‖fderiv ℝ (repY Pl K L μ w τ) y‖) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (101 / 22 : ℝ) * s ^ (101 / 44 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w)) ∧
    ∀ (τ : ℝ) (y : Space),
      ENNReal.ofReal (∑ j : Fin 3, ‖physPd (repX Pl K L μ w τ) j y‖ +
          ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 (repX Pl K L μ w τ) j l y‖) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (101 / 22 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w)

/-- **(B) The `V`-residual of the repair response** (source 5224-5253): for a pressure `p_V`,
`R⁻¹‖Ẽ(V, p_V; X, Y)‖_{Y_2} ≤ P_ν ε^{101/22}F_r` in chart form, with the measurability of the
coefficient. -/
def VResidualAt (pV : ℝ → Space → ℝ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ w : LVel Pl L,
    AEStronglyMeasurable
        (coefOf L.ε⁻¹ (wardEXY L.ν μ L.ε⁻¹ L.V pV (repX Pl K L μ w) (repY Pl K L μ w)))
        (srcMeasure (cOf L.ν)) ∧
      eLpNorm (coefOf L.ε⁻¹ (wardEXY L.ν μ L.ε⁻¹ L.V pV (repX Pl K L μ w) (repY Pl K L μ w)))
          2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (101 / 22 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w)

/-- **(C) The jet of the repair response in `Y_{22/3}`** (source 5212-5223 `repair:phase-gradient`,
5259-5268): `‖|DY| + Σ_j|∂_jX| + Σ_{j,l}|∂_j∂_lX|‖_{Y_{22/3}} ≤ P_ν ε^{46/11}F_r` in chart form
(`DX, DY` from `PhaseGradientAt`: the normalized-phase `Y_{22/3}` norm is at most the
`L^∞_τL^{22/3}` norm, `|∂_jX| ≤ |DX|` and `|DX|` is rotation invariant; `D²X` by the same kernel
argument with `j = 2`, one more power of `(R√ν)⁻¹`, "terms with `D²X` have an additional curvature
power", 5267), with the measurability of the density (as `MeanGradAt` for the thin mean field). -/
def RepJetAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ w : LVel Pl L,
    AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ =>
        meanJetDens (repX Pl K L μ w τ) (repY Pl K L μ w τ)) (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
    eLpNorm (ringRead L.ε⁻¹ fun τ => meanJetDens (repX Pl K L μ w τ) (repY Pl K L μ w τ))
        (22 / 3) (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (46 / 11 : ℝ)) *
        phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w)

/-- **The exact-pressure and `r_b` corrections** (source 5254-5268):
`R⁻¹‖Ẽ(U, p) - Ẽ(V, p_V)‖_{Y_2} ≤ P_ν R⁻¹ρε^{46/11}F_r` in chart form (proved below,
`repCorrAt_of`). -/
def RepCorrAt (pV : ℝ → Space → ℝ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ w : LVel Pl L,
    eLpNorm (coefOf L.ε⁻¹ (fun τ y =>
        wardEXY L.ν μ L.ε⁻¹ L.U L.pres (repX Pl K L μ w) (repY Pl K L μ w) τ y -
          wardEXY L.ν μ L.ε⁻¹ L.V pV (repX Pl K L μ w) (repY Pl K L μ w) τ y)) 2
        (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ))) *
        phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w)

end Regime

/-- **(H) The background bounds of `V` and its canonical pressure** at a level (source 5131-5139:
"`V = U_raw + Eα_bg`, with the unprojected raw residual and coefficient bounds of the background
construction"; 5225-5235; 5245-5247; 5255-5258), for a pressure `p_V`:
* `V` is `C²` off the axis and `p_V` is `C¹` (the background and its canonical pressure are smooth;
  these make the chart readings below and in `VResidualAt` measurable);
* `‖sup_q|v(s,q,·)|‖_{L²_η} ≤ P_ν` at every age (`IIIa.StressCoefficients`, fourth clause, with
  `W ≥ 1` and `|V| = √s|v|` for the swirl-free `V`; "the integral is finite at zero and polynomial
  in `ν⁻¹`", 5232);
* `R⁻¹(‖DV‖_{Y_2} + ‖D²V‖_{Y_2} + ‖V⊗V‖_{Y_2}) ≤ P_ν` (5234-5235), chart form, with measurability;
* `R⁻¹‖∇p_V‖_{Y_2} ≤ P_ν` (5245-5247: `‖∇p_V‖_2 ≤ C‖V‖_∞‖DV‖_2`), chart form;
* `‖∇p - ∇p_V‖_{Y_{11/4}} ≤ P_νρ` (5255-5258: `∇(p-p_V) = -(I-ℙ)(V·∇r_b + r_b·∇V + r_b·∇r_b)`),
  chart form, with measurability; `p = L.pres` the exact pressure. -/
def RepVBgAt (K : ReturnConsts) (L : ReturnLevel) (pV : ℝ → Space → ℝ) (C : ℝ) (k : ℕ) :
    Prop :=
  ContDiffOn ℝ 2 (fun x : ℝ × Space => L.V x.1 x.2) {x | 0 < ϱ x.2} ∧
  ContDiff ℝ 1 (fun x : ℝ × Space => pV x.1 x.2) ∧
  (∀ s : ℝ, 0 < s → vEtaSup L.ε⁻¹ (cOf L.ν) L.V s ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k)) ∧
  AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => vCoefDens (L.V τ)) (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
  ENNReal.ofReal L.ε * eLpNorm (ringRead L.ε⁻¹ fun τ => vCoefDens (L.V τ)) 2
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k) ∧
  ENNReal.ofReal L.ε * eLpNorm (ringRead L.ε⁻¹ fun τ y => ‖physGrad (pV τ) y‖) 2
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k) ∧
  AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (pV τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
  eLpNorm (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (pV τ)) (11 / 4)
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L)

/-! ## 3. The statements along the concrete sequence (large `n`, `z ∈ [-1,1]`) -/

/-- (A) along the sequence (task `PartIII-b:C/rep/3/1`). -/
def RepAgeSurf (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RepAgeSurfAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- (H) along the sequence: at each large level some pressure `p_V` has the bounds (task
`PartIII-b:C/rep/3/4`). -/
def RepVBg (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∃ pV : ℝ → Space → ℝ, RepVBgAt D.K (D.level n) pV C k

/-- (C) along the sequence (task `PartIII-b:C/rep/3/3`). -/
def RepJet (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RepJetAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- **(B) The `V`-residual from (A) and (H)** (source 5224-5253; task `PartIII-b:C/rep/3/2`): under
the standing hypotheses and the age-surface bounds, for every pair of background constants there
are `C, k` such that for large `n`, every `z ∈ [-1,1]` and every pressure `p_V` with the
background bounds (H) at level `n`, `R⁻¹‖Ẽ(V, p_V; X, Y)‖_{Y_2} ≤ Cν^{-k}ε^{101/22}F_r`.  Terms:
`2V·∇Y` by `V = √s v`, the chart Jacobian `πR²s^{-5/2}ds dη`, (A) on age surfaces and
`∫_0^{1/ν}s^{34/11}‖sup_q|v|‖_2² ds ≤ P_ν` (5225-5232, `-3/2 + 101/22 = 34/11`); `2νC_diff(V,X)`,
`(V⊗V):D²X` by the `Y_2` bounds of `DV, D²V, V⊗V` and the `L^∞_τL^∞_y` bounds of `DX, D²X`
(5233-5244); `(DX+DXᵀ)∇p_V` by `R⁻¹‖∇p_V‖_{Y_2} ≤ P_ν` and `‖DX‖_∞` (5245-5253). -/
def VResidualOf : Prop :=
  ∀ (D : SeqData) {dm dp : ℝ}, D.RepairStanding dm dp → RepAgeSurf D →
    ∀ (C₂ : ℝ) (k₂ : ℕ), ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ pV : ℝ → Space → ℝ, RepVBgAt D.K (D.level n) pV C₂ k₂ →
        VResidualAt D.Pl D.K (D.level n) (D.mu n z) pV C k

/-! ## 4. Helpers -/

private theorem be_chiO_repPart {c mZ ρb γ ν : ℝ} {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ)
    (T : StrG c mZ ρb γ ν) :
    chiOStr c mZ ρb γ ν hχ (repPart T) = repPart (chiOStr c mZ ρb γ ν hχ T) := by
  apply (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).injective
  simp [chiOStr, repPart]

private theorem be_repPart_fst {c mZ ρb γ ν : ℝ} (X : StrG c mZ ρb γ ν) :
    (repPart X).fst = 0 := by
  simp [repPart]

private theorem be_repPart_snd {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    (repPart T).snd = T.snd := by
  simp [repPart]

private theorem be_mono {ν C C' x : ℝ} {k k' : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hx : 0 ≤ x)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') (F : ℝ≥0∞) :
    ENNReal.ofReal (C * ν⁻¹ ^ k * x) * F ≤ ENNReal.ofReal (C' * ν⁻¹ ^ k' * x) * F :=
  mul_le_mul' (ENNReal.ofReal_le_ofReal (pnu_le_pnu hν hν1 hx hC hC' hk)) le_rfl

private theorem be_gauge_nonneg (Pl : PlanarData) (L : ReturnLevel) : 0 ≤ gaugeN Pl L :=
  norm_nonneg _

section Mono

variable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
  {pV : ℝ → Space → ℝ} {C C' : ℝ} {k k' : ℕ}

private theorem be_jet_mono (h : RepJetAt Pl K L μ C k) (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') : RepJetAt Pl K L μ C' k' := fun w =>
  ⟨(h w).1, (h w).2.trans (be_mono L.ν_pos hν1 (Real.rpow_nonneg L.ε_pos.le _) hC hC' hk _)⟩

private theorem be_vres_mono (h : VResidualAt Pl K L μ pV C k) (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') : VResidualAt Pl K L μ pV C' k' := fun w =>
  ⟨(h w).1, (h w).2.trans (be_mono L.ν_pos hν1 (Real.rpow_nonneg L.ε_pos.le _) hC hC' hk _)⟩

private theorem be_corr_mono (h : RepCorrAt Pl K L μ pV C k) (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') : RepCorrAt Pl K L μ pV C' k' := fun w =>
  (h w).trans (be_mono L.ν_pos hν1 (mul_nonneg (mul_nonneg L.ε_pos.le (rhoRep_nonneg K L))
    (Real.rpow_nonneg L.ε_pos.le _)) hC hC' hk _)

private theorem be_src_mono (h : RepairSourceAt Pl K L C k) (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') : RepairSourceAt Pl K L C' k' := by
  intro w
  refine (h w).trans (ENNReal.ofReal_le_ofReal ?_)
  have hx : 0 ≤ rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (rhoRep_nonneg K L) (inv_pos.2 L.ε_pos).le)
      (be_gauge_nonneg Pl L)) (norm_nonneg _)
  have := pnu_le_pnu L.ν_pos hν1 hx hC hC' hk
  calc C * L.ν⁻¹ ^ k * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖
      = C * L.ν⁻¹ ^ k * (rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := by ring
    _ ≤ C' * L.ν⁻¹ ^ k' * (rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := this
    _ = C' * L.ν⁻¹ ^ k' * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖ := by ring

end Mono

/-! ## 5. The corrections (C) and the assembly (D) -/

/-- **The exact-pressure and `r_b` corrections at one regime** (source 5254-5268): from the
coefficient change `D.CoefChg` (`U - V = r_b`), the pressure clause of (H) and the jet (C), by the
pointwise Ward-term change `wardEXYChgPt` and Hölder in the ring chart `ringHolderConv`
(`4/11 + 3/22 = 1/2`). -/
theorem repCorrAt_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    {pV : ℝ → Space → ℝ} (hν1 : L.ν ≤ 1) {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (h2 : CoefChgAt Pl K L C k)
    (hpm : AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (pV τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)))
    (hpn : eLpNorm (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (pV τ)) (11 / 4)
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L))
    (h3 : RepJetAt Pl K L μ C k) :
    RepCorrAt Pl K L μ pV (200 * C ^ 2 * (2 + C)) (3 * k) := by
  intro w
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hV1 : 1 ≤ L.ν⁻¹ ^ k := one_le_pow₀ ((one_le_inv₀ hν).2 hν1)
  obtain ⟨hmb, hnb⟩ := h3 w
  set X := repX Pl K L μ w with hX
  set Y := repY Pl K L μ w with hY
  set F := phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) with hF
  set P : ℝ := C * L.ν⁻¹ ^ k with hPdef
  have hP0 : 0 ≤ P := by positivity
  set A : ℝ := 100 * (1 + L.ν + P) with hAdef
  have hA0 : 0 ≤ A := by positivity
  set fc : Chart → ℝ := ringRead L.ε⁻¹ fun τ => coefChgDens (L.U τ) (L.V τ) with hfc
  set fp : Chart → ℝ := ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (pV τ) with hfp
  set a : ℝ → Space → ℝ := fun τ y =>
    A * (coefChgDens (L.U τ) (L.V τ) y + presChgDens (L.pres τ) (pV τ) y) with ha
  set b : ℝ → Space → ℝ := fun τ y => meanJetDens (X τ) (Y τ) y with hb
  set μp := ringPhysμ L.ε⁻¹ (cOf L.ν) with hμp
  set F1 : ℝ → Space → Space := fun τ y =>
    wardEXY L.ν μ L.ε⁻¹ L.U L.pres X Y τ y - wardEXY L.ν μ L.ε⁻¹ L.V pV X Y τ y with hF1
  have hra : ringRead L.ε⁻¹ a = A • (fc + fp) := by
    funext p
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rfl
  have hma : AEStronglyMeasurable (ringRead L.ε⁻¹ a) μp := by
    rw [hra]; exact (h2.1.add hpm).const_smul A
  have hpw : ∀ p : Chart, 0 < p.1 →
      ‖F1 (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ ≤
        ringRead L.ε⁻¹ a p * ringRead L.ε⁻¹ b p := by
    intro p hp
    set τ := NearInst.chartTau L.ε⁻¹ p
    set y := NearInst.chartY L.ε⁻¹ p
    have e := wardEXYChgPt L.ν μ L.ε⁻¹ L.U L.V L.pres pV X Y τ y
    have hU := h2.2.2 p hp
    have hS : 0 ≤ coefChgDens (L.U τ) (L.V τ) y + presChgDens (L.pres τ) (pV τ) y :=
      add_nonneg (coefChgDens_nonneg _ _ _) (presChgDens_nonneg _ _ _)
    have hJ : 0 ≤ meanJetDens (X τ) (Y τ) y := meanJetDens_nonneg _ _ _
    have hle : 100 * (1 + |L.ν| + ‖L.U τ y‖ + ‖L.V τ y‖) ≤ A := by
      rw [abs_of_pos hν, hAdef]
      linarith [hU, norm_nonneg (rawU Pl L τ y)]
    calc ‖F1 τ y‖ ≤ 100 * (1 + |L.ν| + ‖L.U τ y‖ + ‖L.V τ y‖) *
          (coefChgDens (L.U τ) (L.V τ) y + presChgDens (L.pres τ) (pV τ) y) *
            meanJetDens (X τ) (Y τ) y := e
      _ ≤ A * (coefChgDens (L.U τ) (L.V τ) y + presChgDens (L.pres τ) (pV τ) y) *
            meanJetDens (X τ) (Y τ) y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hS) hJ
      _ = ringRead L.ε⁻¹ a p * ringRead L.ε⁻¹ b p := rfl
  have hc' := ringHolderConv L.ε⁻¹ (cOf L.ν) hR hc F1 a b hma hmb hpw
  have h114 : (1 : ℝ≥0∞) ≤ 11 / 4 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hna : eLpNorm (ringRead L.ε⁻¹ a) (11 / 4) μp ≤
      ENNReal.ofReal A * (ENNReal.ofReal (P * rhoRep K L) + ENNReal.ofReal (P * rhoRep K L)) := by
    rw [hra, eLpNorm_const_smul, Real.enorm_eq_ofReal hA0]
    gcongr
    exact (eLpNorm_add_le h2.1 hpm h114).trans (add_le_add h2.2.1 hpn)
  have hρ0 := rhoRep_nonneg K L
  have hx : 0 ≤ P * rhoRep K L := mul_nonneg hP0 hρ0
  have hy : 0 ≤ P * L.ε ^ (46 / 11 : ℝ) := by positivity
  have h1νP : 1 + L.ν + P ≤ (2 + C) * L.ν⁻¹ ^ k := by
    rw [hPdef]; linarith
  have hE0 : 0 ≤ L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ) :=
    mul_nonneg (mul_nonneg hε.le hρ0) (Real.rpow_nonneg hε.le _)
  have hreal : L.ε * (A * (P * rhoRep K L + P * rhoRep K L)) * (P * L.ε ^ (46 / 11 : ℝ)) ≤
      200 * C ^ 2 * (2 + C) * L.ν⁻¹ ^ (3 * k) * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ)) := by
    calc L.ε * (A * (P * rhoRep K L + P * rhoRep K L)) * (P * L.ε ^ (46 / 11 : ℝ))
        = 200 * P ^ 2 * (1 + L.ν + P) * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ)) := by
          rw [hAdef]; ring
      _ ≤ 200 * P ^ 2 * ((2 + C) * L.ν⁻¹ ^ k) * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1νP (by positivity)) hE0
      _ = 200 * C ^ 2 * (2 + C) * L.ν⁻¹ ^ (3 * k) *
            (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ)) := by
          rw [pow_mul', hPdef]; ring
  calc eLpNorm (coefOf L.ε⁻¹ F1) 2 (srcMeasure (cOf L.ν))
      ≤ ENNReal.ofReal L.ε⁻¹⁻¹ * eLpNorm (ringRead L.ε⁻¹ a) (11 / 4) μp *
          eLpNorm (ringRead L.ε⁻¹ b) (22 / 3) μp := hc'
    _ ≤ ENNReal.ofReal L.ε *
          (ENNReal.ofReal A * (ENNReal.ofReal (P * rhoRep K L) +
            ENNReal.ofReal (P * rhoRep K L))) *
          (ENNReal.ofReal (P * L.ε ^ (46 / 11 : ℝ)) * F) := by
        rw [inv_inv]
        exact mul_le_mul' (mul_le_mul' le_rfl hna) hnb
    _ = ENNReal.ofReal (L.ε * (A * (P * rhoRep K L + P * rhoRep K L)) *
          (P * L.ε ^ (46 / 11 : ℝ))) * F := by
        rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul hε.le,
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

/-- **`BodyErrorAt` at one regime from the parts** (source 5196-5299, 5169-5176): the Ward pin
identifies the target with the chart coefficient of `Ẽ(U, p)`; split off `Ẽ(V, p_V)`; add (B) and
the corrections and insert `repair:source`. -/
theorem bodyErrorAt_of_parts {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    {pV : ℝ → Space → ℝ} {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (hW : IsWardTriple (wardOps Pl K L μ).1 (wardOps Pl K L μ).2.1 (wardOps Pl K L μ).2.2 L.ε μ
      K.hχo K.χy L.U L.pres)
    (hV : VResidualAt Pl K L μ pV C k) (hCo : RepCorrAt Pl K L μ pV C k)
    (hS : RepairSourceAt Pl K L C k) :
    BodyErrorAt Pl K L μ (C * C) (2 * k) := by
  intro w
  have hε := L.ε_pos
  set M := multOp Pl K L w with hM
  set X := repX Pl K L μ w with hX
  set Y := repY Pl K L μ w with hY
  set F := phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) with hF
  have h1 : ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart M)).fst :
      Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν] (0 : Chart → Ten3) := by
    rw [be_chiO_repPart, be_repPart_fst]
    exact Lp.coeFn_zero _ _ _
  have e2 : (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart M)).snd =
      (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo M).snd := by
    rw [be_chiO_repPart, be_repPart_snd]
  have h2 : ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart M)).snd :
      Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        repSrcTen Pl K L w := by
    rw [e2]
    exact Filter.EventuallyEq.rfl
  have hE := (hW (repPart M) 0 (repSrcTen Pl K L w) h1 h2).2.2
  have hg : (0 : Chart → Ten3) + repSrcTen Pl K L w = repSrcTen Pl K L w := zero_add _
  rw [hg] at hE
  set A := wardEXY L.ν μ L.ε⁻¹ L.U L.pres X Y with hA
  set B := wardEXY L.ν μ L.ε⁻¹ L.V pV X Y with hB
  have hEA : coefOf L.ε⁻¹
      (wardE L.ν μ L.ε⁻¹ (cOf L.ν) K.χy L.U L.pres (repSrcTen Pl K L w)) = coefOf L.ε⁻¹ A := rfl
  rw [hEA] at hE
  have hsplit : coefOf L.ε⁻¹ A = coefOf L.ε⁻¹ (fun τ y => A τ y - B τ y) + coefOf L.ε⁻¹ B := by
    rw [← coefOf_sub_eq L.ε⁻¹ A B]; abel
  obtain ⟨hBm, hBn⟩ := hV w
  have hAm : AEStronglyMeasurable (coefOf L.ε⁻¹ A) (srcMeasure (cOf L.ν)) :=
    (Lp.aestronglyMeasurable _).congr hE
  have hDm : AEStronglyMeasurable (coefOf L.ε⁻¹ (fun τ y => A τ y - B τ y))
      (srcMeasure (cOf L.ν)) := by
    rw [← coefOf_sub_eq L.ε⁻¹ A B]; exact hAm.sub hBm
  have hCn : eLpNorm (coefOf L.ε⁻¹ (fun τ y => A τ y - B τ y)) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ))) * F := hCo w
  have hSn : F ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) :=
    hS w
  have hρ0 := rhoRep_nonneg K L
  have hN0 := be_gauge_nonneg Pl L
  have hq0 : 0 ≤ C * L.ν⁻¹ ^ k := mul_nonneg hC (pow_nonneg (inv_nonneg.2 L.ν_pos.le) _)
  have hx1 : 0 ≤ C * L.ν⁻¹ ^ k * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ)) :=
    mul_nonneg hq0 (mul_nonneg (mul_nonneg hε.le hρ0) (Real.rpow_nonneg hε.le _))
  have hx2 : 0 ≤ C * L.ν⁻¹ ^ k * L.ε ^ (101 / 22 : ℝ) :=
    mul_nonneg hq0 (Real.rpow_nonneg hε.le _)
  have hreal : (C * L.ν⁻¹ ^ k * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ)) +
        C * L.ν⁻¹ ^ k * L.ε ^ (101 / 22 : ℝ)) *
        (C * L.ν⁻¹ ^ k * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) =
      C * C * L.ν⁻¹ ^ (2 * k) * gaugeN Pl L *
        (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) +
          L.ε ^ (52 / 11 : ℝ) * Real.exp (2 * K.m0 / L.ν)) * ‖w‖ := by
    have e1 : L.ε ^ (85 / 22 : ℝ) = L.ε ^ (101 / 22 : ℝ) * L.ε ^ (3 / 11 : ℝ) * L.ε⁻¹ := by
      rw [show (85 / 22 : ℝ) = 101 / 22 + 3 / 11 + (-1) by norm_num, Real.rpow_add hε,
        Real.rpow_add hε, Real.rpow_neg_one]
    have e2' : L.ε ^ (52 / 11 : ℝ) =
        L.ε ^ (3 / 11 : ℝ) * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (46 / 11 : ℝ) := by
      rw [show (52 / 11 : ℝ) = 3 / 11 + 3 / 11 + 46 / 11 by norm_num, Real.rpow_add hε,
        Real.rpow_add hε]
    have e3 : Real.exp (2 * K.m0 / L.ν) = Real.exp (K.m0 / L.ν) * Real.exp (K.m0 / L.ν) := by
      rw [← Real.exp_add]; ring_nf
    have e4 : L.ε * L.ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    rw [e1, e2', e3, rhoRep, two_mul, pow_add]
    linear_combination (C * L.ν⁻¹ ^ k * (C * L.ν⁻¹ ^ k) * gaugeN Pl L * ‖w‖ *
      (L.ε ^ (3 / 11 : ℝ) * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (46 / 11 : ℝ)) *
      (Real.exp (K.m0 / L.ν) * Real.exp (K.m0 / L.ν))) * e4
  have htot : eLpNorm (coefOf L.ε⁻¹ A) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * C * L.ν⁻¹ ^ (2 * k) * gaugeN Pl L *
        (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) +
          L.ε ^ (52 / 11 : ℝ) * Real.exp (2 * K.m0 / L.ν)) * ‖w‖) := by
    rw [hsplit, ← hreal]
    calc eLpNorm (coefOf L.ε⁻¹ (fun τ y => A τ y - B τ y) + coefOf L.ε⁻¹ B) 2
          (srcMeasure (cOf L.ν))
        ≤ eLpNorm (coefOf L.ε⁻¹ (fun τ y => A τ y - B τ y)) 2 (srcMeasure (cOf L.ν)) +
            eLpNorm (coefOf L.ε⁻¹ B) 2 (srcMeasure (cOf L.ν)) :=
          eLpNorm_add_le hDm hBm one_le_two
      _ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ))) * F +
            ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (101 / 22 : ℝ)) * F := add_le_add hCn hBn
      _ = ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ)) +
            C * L.ν⁻¹ ^ k * L.ε ^ (101 / 22 : ℝ)) * F := by
          rw [← add_mul, ← ENNReal.ofReal_add hx1 hx2]
      _ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε * rhoRep K L * L.ε ^ (46 / 11 : ℝ)) +
            C * L.ν⁻¹ ^ k * L.ε ^ (101 / 22 : ℝ)) *
            ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) :=
          mul_le_mul' le_rfl hSn
      _ = _ := (ENNReal.ofReal_mul (add_nonneg hx1 hx2)).symm
  have hfin : 0 ≤ C * C * L.ν⁻¹ ^ (2 * k) * gaugeN Pl L *
      (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) +
        L.ε ^ (52 / 11 : ℝ) * Real.exp (2 * K.m0 / L.ν)) * ‖w‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_self_nonneg C)
      (pow_nonneg (inv_nonneg.2 L.ν_pos.le) _)) hN0)
      (add_nonneg (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)
        (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le))) (norm_nonneg _)
  rw [Lp.norm_def, eLpNorm_congr_ae hE]
  exact ENNReal.toReal_le_of_le_ofReal hfin htot

/-- **`repair:body-error` along the concrete sequence from the parts** (source 5196-5299,
5691-5692): (B) `VResidualOf` with (A), (H); (C) `RepJet`; the coefficient change `D.CoefChg`
(`PartIII-b:C/rep/8/2/pres/4`); `repair:source` (`PartIII-b:C/rep/1`); the Ward pin of
`RegimePins.ward`.  Composed in `Concrete/ReturnRepair/BodyError.lean` (task `PartIII-b:C/rep/3`). -/
theorem bodyError_of (hB : VResidualOf) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) (hA : RepAgeSurf D) (hH : RepVBg D) (hJ : RepJet D)
    (hCC : D.CoefChg) (hS : D.RepairSource) : D.BodyError := by
  obtain ⟨C₂, k₂, hH'⟩ := hH
  obtain ⟨CV, kV, hV⟩ := hB D hst hA C₂ k₂
  obtain ⟨C₁, k₁, hC1⟩ := hCC
  obtain ⟨C₃, k₃, hJ'⟩ := hJ
  obtain ⟨CS, kS, hS'⟩ := hS
  set C : ℝ := |C₁| + |C₂| + |C₃| + |CV| + |CS| with hCdef
  set k : ℕ := k₁ + k₂ + k₃ + kV + kS with hkdef
  have a1 := abs_nonneg C₁
  have a2 := abs_nonneg C₂
  have a3 := abs_nonneg C₃
  have a4 := abs_nonneg CV
  have a5 := abs_nonneg CS
  have hC0 : 0 ≤ C := by positivity
  set C' : ℝ := 200 * C ^ 2 * (2 + C) + C with hC'def
  have h200 : 0 ≤ 200 * C ^ 2 * (2 + C) := by positivity
  have hCC' : C ≤ C' := by linarith
  have hC'0 : 0 ≤ C' := le_trans hC0 hCC'
  refine ⟨C' * C', 2 * (3 * k), ?_⟩
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hH', hV, hC1, hJ', hS', hst.pins, hev2] with n hHn hVn hCn hJn hSn hpn h2 z hz
  obtain ⟨pV, hpV⟩ := hHn
  have hν1 : (D.level n).ν ≤ 1 := h2.1
  have hν := (D.level n).ν_pos
  have hW : IsWardTriple (wardOps D.Pl D.K (D.level n) (D.mu n z)).1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.1 (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2
      (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U (D.level n).pres :=
    Classical.epsilon_spec (hpn z hz).ward
  have i1 : CoefChgAt D.Pl D.K (D.level n) C k :=
    hCn.mono hν1 (by linarith [le_abs_self C₁]) hC0 (by omega)
  have i2 : eLpNorm (ringRead (D.level n).ε⁻¹ fun τ =>
      presChgDens ((D.level n).pres τ) (pV τ)) (11 / 4)
      (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n)) :=
    hpV.2.2.2.2.2.2.2.trans (ENNReal.ofReal_le_ofReal (pnu_le_pnu hν hν1
      (rhoRep_nonneg D.K (D.level n)) (by linarith [le_abs_self C₂]) hC0 (by omega)))
  have i3 : RepJetAt D.Pl D.K (D.level n) (D.mu n z) C k :=
    be_jet_mono (hJn z hz) hν1 (by linarith [le_abs_self C₃]) hC0 (by omega)
  have hCo := repCorrAt_of hν1 hC0 i1 hpV.2.2.2.2.2.2.1 i2 i3
  have j1 : VResidualAt D.Pl D.K (D.level n) (D.mu n z) pV C' (3 * k) :=
    be_vres_mono (hVn z hz pV hpV) hν1 (by linarith [le_abs_self CV]) hC'0 (by omega)
  have j2 : RepCorrAt D.Pl D.K (D.level n) (D.mu n z) pV C' (3 * k) :=
    be_corr_mono hCo hν1 (by linarith) hC'0 le_rfl
  have j3 : RepairSourceAt D.Pl D.K (D.level n) C' (3 * k) :=
    be_src_mono hSn hν1 (by linarith [le_abs_self CS]) hC'0 (by omega)
  exact bodyErrorAt_of_parts hC'0 hW j1 j2 j3

end UnforcedLeray.Short.PartIIIb.Concrete

end
