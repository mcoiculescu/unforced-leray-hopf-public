import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.TableSupport

/-!
# `PartIII-b:C/rep/4/2/org/3/org`: the organisation of the thin transition table

Source `the November 2 reference manuscript` 5312-5355 (table and thin-to-thin
estimate), 5573-5592 (the mass `N_0(a)` and closure), 5527 (`N ≤ P_ν|N_ν|‖g⁻¹T‖_Z`), 5116, 5119.

`TransThinTable` (`YThinTrans.lean`) is the sequence-level statement
`‖g⁻¹M_U v‖_Z ≤ P_ν S^{k₁}|N_ν|(ε² + ε^{49/22}e^{m₀/(2ν)})e^{-4γ/(9ν)}‖g⁻¹T‖_Z` for the transition
field `v`.  The source proves it in four steps; here each is a concrete statement:

* (a) support `4/5 ≤ νs ≤ 1` of `transCut`, `transComm`: **proved** (`transField_zero_outside`).
* (b) late output `g⁻¹ ≤ e^{-4γ/(9ν)}`: **proved** (`ginv_le_late`).
* (c) `OldMassGauge` (`N_0 ≤ P_ν|N_ν|‖g⁻¹T‖`, 5527) with `MassZ1At` (`N_0(a) ≤ C(a^{-3/4} +
  a^{-1/2})‖T‖_{Z_1}`, 5573-5580), and `AnnulusFields` (the annulus bounds of `D^jW_μ` in terms of
  the old mass, 3669-3674, 3730, 5342-5355).
* (d) `TransMultiplierStep`: the multiplier step on the annulus field (5323-5340): thin receiver
  `ε²`, repair receiver `ε^{49/22}e^{m₀/(2ν)}` (`ρ = ε^{3/11}e^{m₀/ν}`), outward primitive and
  `∂_τW_μ` with the same norm powers, late output as the supremum `Λ` of `g⁻¹` on the support.

`transThinTable_of` assembles them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The old mass -/

/-- `N_0(a) = ∫_a^∞ t^{-3/2}∫‖T(t,·,η)‖_{L²_q}dη dt` (source 5573-5576), `L²_q` normalized on the
period cell `[-c/2, c/2)`. -/
def oldMassAt (c a : ℝ) (T : Chart → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi a, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
    ∫⁻ η : ℝ, (∫⁻ q in Ico (-(c / 2)) (c / 2),
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (T (s, (q, η))))) ^
        (1 / 2 : ℝ)

/-- The whole mass of the old thin source `χ_o(T₁, 0)` (source 5153-5157, 3669, 3730). -/
def oldMass (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) : ℝ≥0∞ :=
  oldMassAt (cOf L.ν) 0 (fun p => K.χo (L.ν * p.1) • thinRep T p)

/-- **Mass estimate** (source 5573-5580): `N_0(a) ≤ C(a^{-3/4} + a^{-1/2})‖T‖_{Z_1}`, for `m_Z > 3/2`. -/
def MassZ1At : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 < c → ∀ a : ℝ, 0 < a →
    ∀ T : Chart → Matrix (Fin 3) (Fin 3) ℝ, (∀ i j, Measurable fun p => T p i j) →
      oldMassAt c a T ≤ ENNReal.ofReal (C * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) *
        UnforcedLeray.Short.IIIa.z1NormSq c mZ T ^ (1 / 2 : ℝ)

/-- **Gain form of the old mass** (source 5527: `N ≤ P_ν|N_ν|‖g⁻¹T‖_Z`). -/
def MassGaugeAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, oldMass Pl K L T ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * gaugeN Pl L * ‖T‖)

/-! ## 2. The annulus fields in terms of the old mass -/

/-- **Annulus bounds of `D^jW_μ`** (source 3669-3674 `sep:thin-global`, 3730 "physical mass is
`R²N_0`", 5342-5355): for the old source `𝒩_T(χ_oT)` of chart representative `g`, supported in
`r ≤ R√(ν/1.2)` (4163-4168, `s ≥ 1.2/ν`) and read on the young region `r ≥ R√ν ⊇ {0.8/ν < s <
1/ν}`, `‖D^jW_μ‖_{L²_τL^q} ≤ C ν^{-k}R^{-2-j+3/q}N_0`, `j ≤ 2`, `q ∈ {2, 22/3}` (the exponents of
the table, 5329-5331), `N_0` the old mass.  This is `IIIa.SepThinGlobal` with `c₀ = 1 - √(5/6)`. -/
def AnnulusFieldBoundsAt (ν μ R c : ℝ) (g : Chart → Ten3) (N0 : ℝ≥0∞) (C : ℝ) (k : ℕ) : Prop :=
  ∀ P rOut : ℝ, 0 < P → rOut ≤ R * Real.sqrt ν * Real.sqrt (5 / 6) →
    UnforcedLeray.Short.IIIa.IsSepSource P rOut (oldPhys R c g) →
    ∀ (j : ℕ), j ≤ 2 → ∀ q : ℝ, q = 2 ∨ q = 22 / 3 →
      UnforcedLeray.Short.IIIa.ltauLq P q
          (UnforcedLeray.Short.IIIa.youngDerivNorm ν (μ : ℂ) (oldPhys R c g) j
            (R * Real.sqrt ν)) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * R ^ (-2 - (j : ℝ) + 3 / q)) * N0

/-! ## 3. The multiplier step -/

section Step

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **Multiplier step on the annulus field** (source 5323-5340): for an old thin source whose
annulus fields obey `AnnulusFieldBoundsAt` with the old mass `N_0`, every body velocity `v`
supported a.e. in `4/5 ≤ νs ≤ 1` (the transition field) and every `Λ ≥ g⁻¹` on that support, the
split multiplier satisfies
`‖g⁻¹M_Uv‖_Z ≤ C ν^{-k}S^{k₁}(ε² + ε^{49/22}e^{m₀/(2ν)})Λ N_0`: the thin receiver gets `ε²`
(separated pointwise velocity `P_νε²s²N_0`, then lift and thin multiplication, 5346-5352), the
repair receiver `ε^{49/22}e^{m₀/(2ν)}` (order-four kernel `L² → L^{22/3}`, off-diagonal norm
`D^{-23/11}`, then `√ρ`, `ρ = ε^{3/11}e^{m₀/ν}`, 5333-5340); the outward stream primitive and
`∂_τW_μ` have the same norm powers (5338-5340, 5588-5590). -/
def TransMultiplierStepAt (k₁ : ℕ) (C : ℝ) (k : ℕ) (Cf : ℝ) (kf : ℕ) : Prop :=
  ∀ (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldThin Pl K L T) g₁ g₂ →
    AnnulusFieldBoundsAt L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) (oldMass Pl K L T) Cf kf →
    oldMass Pl K L T ≠ ⊤ →
    ∀ Λ : ℝ, 0 ≤ Λ → (∀ p : Chart, 4 / 5 ≤ L.ν * p.1 → ginv (gRate Pl) L.ν p ≤ Λ) →
    ∀ v : LVel Pl L,
      (∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν),
          ¬(4 / 5 ≤ L.ν * p.1 ∧ L.ν * p.1 ≤ 1) → (v : Chart → Merid) p = 0) →
      (v : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
          coefOf L.ε⁻¹ (transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) →
        ‖multOp Pl K L v‖ ≤
          C * L.ν⁻¹ ^ k * L.Scut K ^ k₁ *
            (L.ε ^ (2 : ℝ) + L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) *
            Λ * (oldMass Pl K L T).toReal

end Step

/-! ## 4. The Props along the sequence -/

/-- (c1) the old mass in gain form, along the sequence (source 5527). -/
def OldMassGauge (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    MassGaugeAt D.Pl D.K (D.level n) C k

/-- (c2) the annulus field bounds along the sequence (source 3669-3674, 3730, 5342-5355). -/
def AnnulusFields (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    ∀ z ∈ Icc (-1 : ℝ) 1, ∀ (T : LStr D.Pl D.K (D.level n)) (g₁ g₂ : Chart → Ten3),
      IsRep D.Pl D.K (D.level n) (oldThin D.Pl D.K (D.level n) T) g₁ g₂ →
        AnnulusFieldBoundsAt (D.level n).ν (D.mu n z) (D.level n).ε⁻¹ (cOf (D.level n).ν)
          (g₁ + g₂) (oldMass D.Pl D.K (D.level n) T) C k

/-- (d) the multiplier step along the sequence, with `k₁` chosen before `b`. -/
def TransMultiplierStep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₁ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∀ (Cf : ℝ) (kf : ℕ), ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      TransMultiplierStepAt D.Pl D.K (D.level n) (D.mu n z) k₁ C k Cf kf

/-! ## 5. Assembly -/

/-- The transition field has a.e. support in the annulus (from (a)). -/
theorem transVel_support {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (g : Chart → Ten3) (v : LVel Pl L)
    (hv : (v : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
      coefOf L.ε⁻¹ (transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g)) :
    ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν),
      ¬(4 / 5 ≤ L.ν * p.1 ∧ L.ν * p.1 ≤ 1) → (v : Chart → Merid) p = 0 := by
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  filter_upwards [hv, bodyMeasure_ae_pos (cOf L.ν) (gRate Pl) L.ν] with p hvp hp hno
  have hy : 0 < ϱ (NearInst.chartY L.ε⁻¹ p) := by rw [ϱ_chartY hR hp]; positivity
  have hout : L.ν * age L.ε⁻¹ (NearInst.chartY L.ε⁻¹ p) < 4 / 5 ∨
      1 < L.ν * age L.ε⁻¹ (NearInst.chartY L.ε⁻¹ p) := by
    rw [age_chartY hR hp]
    by_contra hc
    push Not at hc
    exact hno ⟨hc.1, hc.2⟩
  obtain ⟨h1, h2⟩ := transField_zero_outside hχ L.ν μ L.ε⁻¹ (cOf L.ν) g
    (NearInst.chartTau L.ε⁻¹ p) hy hout
  rw [hvp]
  unfold coefOf
  have : transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g (NearInst.chartTau L.ε⁻¹ p)
      (NearInst.chartY L.ε⁻¹ p) = 0 := by
    unfold transField; rw [h1, h2]; simp
  rw [this]
  simp

/-- **The pointwise table from (b), (c), (d)**: `TransThinTableAt` at one regime. -/
theorem transThinTableAt_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (hγ : 0 ≤ gRate Pl) (hχ : IsStreamCutoff K.χy) {k₁ : ℕ} {Cm : ℝ} {km : ℕ} {Cf : ℝ} {kf : ℕ}
    {Cd : ℝ} {kd : ℕ} (hCm : 0 ≤ Cm) (hmass : MassGaugeAt Pl K L Cm km)
    (hfield : ∀ (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldThin Pl K L T) g₁ g₂ →
      AnnulusFieldBoundsAt L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) (oldMass Pl K L T) Cf kf)
    (hstep : TransMultiplierStepAt Pl K L μ k₁ Cd kd Cf kf) (hCd : 0 ≤ Cd) :
    TransThinTableAt Pl K L μ k₁ (Cd * Cm) (kd + km) := by
  intro T g₁ g₂ hg v hv
  have hmT := hmass T
  have hfin : oldMass Pl K L T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmT
  have hΛ := hstep T g₁ g₂ hg (hfield T g₁ g₂ hg) hfin
    (Real.exp (-(4 * gRate Pl / 9) / L.ν)) (Real.exp_nonneg _)
    (fun p hp => ginv_le_late hγ L.ν_pos p hp) v (transVel_support μ hχ _ v hv) hv
  have hX : 0 ≤ Cm * L.ν⁻¹ ^ km * gaugeN Pl L * ‖T‖ := by
    have : 0 ≤ gaugeN Pl L := norm_nonneg _
    have := L.ν_pos
    positivity
  have hN : (oldMass Pl K L T).toReal ≤ Cm * L.ν⁻¹ ^ km * gaugeN Pl L * ‖T‖ :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmT).trans (ENNReal.toReal_ofReal hX).le
  have hε := L.ε_pos
  have hν := L.ν_pos
  have hS : 0 ≤ L.Scut K := by unfold ReturnLevel.Scut; positivity
  calc ‖multOp Pl K L v‖ ≤ _ := hΛ
    _ ≤ (Cd * L.ν⁻¹ ^ kd * L.Scut K ^ k₁ *
          (L.ε ^ (2 : ℝ) + L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) *
          Real.exp (-(4 * gRate Pl / 9) / L.ν)) * (Cm * L.ν⁻¹ ^ km * gaugeN Pl L * ‖T‖) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- **Sequence level**: (b), (c), (d) give `TransThinTable` (the pointwise assembly
`transThinTableAt_of` with `k₁` chosen before `b`, as in the definition). -/
theorem transThinTable_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (hc1 : OldMassGauge dm dp)
    (hc2 : AnnulusFields dm dp) (hd : TransMultiplierStep Pl σ₀ mZ dm dp) :
    TransThinTable Pl σ₀ mZ dm dp := by
  obtain ⟨k₁, H⟩ := hd
  refine ⟨k₁, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨Cm, km, hCm, hm⟩ := hc1 D hst
  obtain ⟨Cf, kf, hf⟩ := hc2 D hst
  obtain ⟨Cd, kd, hCd, hs⟩ := H D hPl hσ hmZ hst Cf kf
  refine ⟨Cd * Cm, kd + km, ?_⟩
  filter_upwards [hm, hf, hs] with n hmn hfn hsn z hz
  exact transThinTableAt_of hst.gamma_pos.le hst.chiY hCm hmn
    (fun T g₁ g₂ hg => hfn z hz T g₁ g₂ hg) (hsn z hz) hCd

end UnforcedLeray.Short.PartIIIb.Concrete
