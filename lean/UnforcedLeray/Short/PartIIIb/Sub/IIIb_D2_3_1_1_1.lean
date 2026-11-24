import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

/-!
# Decomposition of `oldSourceReg_all` (`PartIII-b:IIIb-D2/3/1/1/1`)

Source of record: `the November 2 reference manuscript`
4155-4171 (the old source `χ_oT`, `T ∈ Y₂`, the cutoffs `χ_o = 0` for `s ≤ 1.2/ν`),
2666-2703 (the chart, the lifts `‖𝒩_TT‖²_{Y₂} = πR²‖T‖²_{H_T}`, the spaces `Z₁`, `H_T`, `Z`),
3611-3621 (`sep:resolvent`).

`OldSourceReg` (`Sub/IIIb-D2_3_1_1.lean`) is proved here (`oldSourceReg_of`) from five leaves.
Let `R = ε⁻¹`, `r₀ = R√(5ν/6)` and `G = strSum (χ_oT)`, the sum of the canonical (strongly
measurable) `Lp` representatives of the two components of `χ_oT`.  The separated source is
`T' = oldCutSrc R c r₀ G`, the lift `oldPhys R c G` cut off outside the old cylinder
`hRad z ≤ r₀`.

* a.e. on the chart (`ageμ c (-1/2)`; the gain measures have the same null sets for `ρ_b > 0`):
  `g₁ + g₂ = G`, and `G = 0` where `νs ≤ 6/5` (`χ̂_o(νs) = 0`, `IsOutwardCutoff.zero`);
* `ChartOfNullPullback`: chart-null sets pull back to null sets of `(τ, z)`; hence
  `oldPhys R c (g₁+g₂) = T'` a.e. (`hRad z > r₀` forces `νs < 6/5`, so the lift vanishes there);
* `SepWCongrAE`: `sepW` only sees the a.e. class of the source;
* `IsSepSource (2c/R) r₀ T'`: `OldCutMeasurable`, `oldPhysPeriodic` (`2c/R`-periodicity),
  support by definition;
* `SepMoment`: `OldCutMoment` (the lift identity) and `StrChartL2` (the gain norm controls
  `∫|G|² s^{-1/2}dς`: `g⁻¹ ≥ e^{-|γ|/ν}`, `W ≥ 1` for `m_Z ≥ 0`, `ρ_b > 0`).

`OldCutMoment` and `StrChartL2` are compositions of the smaller leaves `CartLiftFrobBound`,
`ChartPhaseLIntegral`, `AgeWeightShift` and `GainMeasureLower` (all stated here).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The old source `𝒩_T G` (`oldPhys`) cut off outside the old cylinder `|z'| ≤ r` (source
4161-4166: the old source disk `r ≤ R√(ν/1.2)`, `χ_o = 0` for `s ≤ 1.2/ν`). -/
def oldCutSrc (R c r : ℝ) (G : Chart → Ten3) : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ :=
  fun τ z => if NearInst.hRad z ≤ r then oldPhys R c G τ z else 0

/-! ## Leaves -/

/-- **Chart-null sets pull back to null sets** (source 2666-2668; `phaseAvg_ringChart`,
`NearInst.stressPairAE_null`): for `R, c > 0` and an `ageμ c (-1/2)`-null set `N` of chart
points, a.e. similarity point `(τ, z) ∈ ℝ × Space` (every phase: `chartOf R c z` is
`2c/R`-periodic in `τ`) has `chartOf R c z τ ∉ N`. -/
def ChartOfNullPullback : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ N : Set Chart, ageμ c (-1 / 2) N = 0 →
    ∀ᵐ x : ℝ × Space ∂volume, NearInst.chartOf R c x.2 x.1 ∉ N

/-- **`sepW` sees only the a.e. class of the source** (source 3611-3621): if two tensor fields
agree for a.e. `(τ, z)`, their separated responses agree at every `(y, τ)` (for fixed `τ`,
`l ↦ τ + 2 log l` is a diffeomorphism of `(0, 1)` onto `(-∞, τ)`, so null sets of phases pull
back to null sets of `l`). -/
def SepWCongrAE : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (T₁ T₂ : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    (∀ᵐ x : ℝ × Space ∂volume, T₁ x.1 x.2 = T₂ x.1 x.2) →
      ∀ (y : Space) (τ : ℝ), IIIa.sepW ν μ T₁ y τ = IIIa.sepW ν μ T₂ y τ

/-- **Measurability of the cut old source** (source 2666-2683): for a measurable chart tensor
`G`, every entry of `oldCutSrc R c r G` is jointly measurable in `(τ, z)` (`chartOf`, `cylFrame`,
`nsSym` and the cut are measurable). -/
def OldCutMeasurable : Prop :=
  ∀ (R c r : ℝ) (G : Chart → Ten3), Measurable G →
    ∀ i j : Fin 3, Measurable fun p : ℝ × Space => oldCutSrc R c r G p.1 p.2 i j

/-- **Pointwise Frobenius bound of the lift** (source 2683: `𝒩_TT = sT` in the orthonormal frame;
`nsSym` does not increase the Frobenius norm): `|cartLift R c G τ z| ≤ s|G(chartOf R c z τ)|`,
`s = (chartOf R c z τ).1` (on the axis both sides vanish: `s = R²/0 = 0`). -/
def CartLiftFrobBound : Prop :=
  ∀ (R c : ℝ) (G : Chart → Ten3) (τ : ℝ) (z : Space),
    IIIa.tensorNorm (oldPhys R c G τ z) ≤
      (NearInst.chartOf R c z τ).1 * ‖G (NearInst.chartOf R c z τ)‖

/-- **Change of variables to the chart over one period** (source 2666-2668, 2684-2687;
`phaseAvg_ringChart`, `NearInst.chartOf_eq_ring`): for `R, c > 0`, `P = 2c/R` and measurable
`F ≥ 0` on the chart, `∫_0^P ∫ F(chartOf R c z τ) dz dτ = P · πR² · ∫ F d(s^{-5/2}dς)`. -/
def ChartPhaseLIntegral : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ F : Chart → ℝ≥0∞, Measurable F →
    ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z, F (NearInst.chartOf R c z τ) =
      ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p, F p ∂(ageμ c (-5 / 2))

/-- **Age weights** (source 2666-2679): `s² · s^{-5/2} dς = s^{-1/2} dς`. -/
def AgeWeightShift : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Chart → ℝ≥0∞, Measurable f →
    ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * f p ∂(ageμ c (-5 / 2)) = ∫⁻ p, f p ∂(ageμ c (-1 / 2))

/-- **`Y₂` moment of the cut old source** (source 4155-4156, lift identity 2684-2687): for
`R, c > 0` and a measurable chart tensor `G` with `∫ |G|² s^{-1/2}dς < ∞`, the cut old source has
finite `L²_τL²_z` moment over the period `2c/R` (from `CartLiftFrobBound`,
`ChartPhaseLIntegral`, `AgeWeightShift`). -/
def OldCutMoment : Prop :=
  ∀ (R c r : ℝ) (G : Chart → Ten3), 0 < R → 0 < c → Measurable G →
    ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤ → SepMoment (2 * c / R) (oldCutSrc R c r G)

/-- **The gain measures dominate `s^{-1/2}dς`** (source 2694-2700, 3875): for `ρ_b > 0`,
`m_Z ≥ 0`, `ν > 0` there is `κ > 0` with `κ ∫ f d(s^{-1/2}dς) ≤ ∫ f dgainZ1Measure` and
`≤ ∫ f dgainHTMeasure` for measurable `f ≥ 0` (`g⁻² ≥ e^{-2|γ|/ν}` since `|γs/(1+νs)| ≤ |γ|/ν`
for `s ≥ 0`; `W² ≥ 1` for `m_Z ≥ 0`; the factor `ρ_b⁻¹`). -/
def GainMeasureLower : Prop :=
  ∀ (c mZ ρb γ ν : ℝ), 0 < ρb → 0 ≤ mZ → 0 < ν → ∃ κ : ℝ, 0 < κ ∧
    ∀ f : Chart → ℝ≥0∞, Measurable f →
      ENNReal.ofReal κ * ∫⁻ p, f p ∂(ageμ c (-1 / 2)) ≤ ∫⁻ p, f p ∂(gainZ1Measure c mZ γ ν) ∧
        ENNReal.ofReal κ * ∫⁻ p, f p ∂(ageμ c (-1 / 2)) ≤ ∫⁻ p, f p ∂(gainHTMeasure c ρb γ ν)

/-- **The gain norm controls the `H_T` norm of `T₁ + T₂`** (source 2694-2700, 5609; from
`GainMeasureLower` and the `L²` membership of both components). -/
def StrChartL2 : Prop :=
  ∀ (c mZ ρb γ ν : ℝ), 0 < ρb → 0 ≤ mZ → 0 < ν → ∀ T : StrG c mZ ρb γ ν,
    ∫⁻ p, ‖strSum T p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤

/-! ## Assembly -/

theorem osr_nsSym_zero : NearInst.nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ]

/-- **`OldSourceReg`** from the leaves (source 4155-4171, 2666-2703, 3611-3621). -/
theorem oldSourceReg_of (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hMeas : OldCutMeasurable)
    (hMom : OldCutMoment) (hL2 : StrChartL2) (c mZ ρb γ ν ε : ℝ) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) : OldSourceReg c mZ ρb γ ν ε hχo := by
  intro hc hρ hm hν hε T g₁ g₂ h1 h2
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  set G : Chart → Ten3 := strSum (chiOStr c mZ ρb γ ν hχo T) with hG
  have hGm : Measurable G := by
    have e₁ := (Lp.stronglyMeasurable (chiOStr c mZ ρb γ ν hχo T).fst).measurable
    have e₂ := (Lp.stronglyMeasurable (chiOStr c mZ ρb γ ν hχo T).snd).measurable
    exact e₁.add e₂
  -- the representatives and the cutoff, a.e. for `ageμ c (-1/2)`
  have hc1 : ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      cutFun χo ν • ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun χo ν) (cutFun_measurable hχo ν) 1 (cutFun_bound hχo ν) T.fst
  have hc2 : ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      cutFun χo ν • ((T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun χo ν) (cutFun_measurable hχo ν) 1 (cutFun_bound hχo ν) T.snd
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h1 hc1
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h2 hc2
  have hchart : ∀ᵐ p ∂(ageμ c (-1 / 2)), (g₁ + g₂) p = G p ∧ (ν * p.1 ≤ 6 / 5 → G p = 0) := by
    filter_upwards [h1, h2, hc1, hc2] with p e1 e2 e3 e4
    refine ⟨?_, fun hp => ?_⟩
    · simp only [Pi.add_apply, hG, strSum, e1, e2]
    · have h0 : cutFun χo ν p = 0 := hχo.zero _ hp
      simp only [hG, strSum, e3, e4, Pi.smul_apply', h0, zero_smul, add_zero]
  have hpull := hN ε⁻¹ c hR hc _ (ae_iff.1 hchart)
  -- the two sources agree a.e. in `(τ, z)`
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys ε⁻¹ c (g₁ + g₂) x.1 x.2 =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [not_not] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hphys : oldPhys ε⁻¹ c (g₁ + g₂) x.1 x.2 = oldPhys ε⁻¹ c G x.1 x.2 := by
      simp only [oldPhys, NearInst.cartLift, hx1]
    rw [hphys]
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 = ε⁻¹ ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf ε⁻¹ c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (ε⁻¹ ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx2 hs
      simp only [oldPhys, NearInst.cartLift, hG0, osr_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  -- the separated source
  have hper : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G (τ + 2 * c / ε⁻¹) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic ε⁻¹ c G τ z]
  have hsupp : ∀ τ z, ε⁻¹ * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  refine ⟨2 * c / ε⁻¹, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G, by positivity,
    ⟨hMeas ε⁻¹ c _ G hGm, hper, hsupp⟩,
    hMom ε⁻¹ c _ G hR hc hGm (hL2 c mZ ρb γ ν hρ hm hν _), (fun μ y τ => hS ν μ _ _ hagree y τ), hagree⟩

end UnforcedLeray.Short.PartIIIb.Concrete
