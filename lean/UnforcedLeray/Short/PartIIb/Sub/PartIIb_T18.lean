import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Lib.OperatorInputs.RieszThorin

/-!
# Part II-b, Task `PartII-b:T18`: Riesz-Thorin application (`LpInterpolationStep`, decomposition)

Source of record: `the November 2 reference manuscript` (SP), lines 1903-1908 and
1992-2005 (`bg:lp-free-comparison`).

With the weight isometry `(M P)(s, q, η) = s^{1/2} P(s, q, η)` between `H_q = L^q(s^{q/2 - 5/2} ds dq/c dη)`
and `L^q(dm)` (`dm = s^{-5/2} ds dq/c dη`), the conjugated operator `M B (T_ε - T_0) M⁻¹` is a
single bounded `ℂ`-linear operator across `q ∈ {2, 23/8, 11/4}` agreeing on indicator atoms.
Riesz-Thorin (`ExternalInputs.norm_le_of_rieszThorin_of_indicator`) with `p₀ = 2`, `p₁ = 23/8`,
`θ = 69/77`, `p = 11/4` (`ExternalInputs.rieszThorin_instance_exponents`) and rate bookkeeping
(`interp_rate`) yield the `H_{11/4}` rate `A^{8/77} M_r^{69/77} ε^{2/539}`.

## Proved here (zero `sorry`)
* `dmLp_rieszThorin_bound`: the Riesz-Thorin operator norm bound on `DmLp c` from
  `ExternalInputs.norm_le_of_rieszThorin_of_indicator`, `ExternalInputs.rieszThorin_instance_exponents`,
  `interp_weights`, and `interp_rate`;
* `existsConsistentDmRealizations_of`: assembly of `ExistsConsistentDmRealizations` from
  `HrComparisonOperatorFamily` (`PartII-b:T18/1`) and `DmLpRealizationOfHrOperator` (`PartII-b:T18/2`);
* `lpInterpolationStep_of_leaves`: conditional assembly of `LpInterpolationStep` (`PartII-b:T18`)
  from `HrComparisonOperatorFamily` and `DmLpRealizationOfHrOperator`.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.ExternalInputs UnforcedLeray.Cons.C03

/-- The unweighted reference measure `dm = s^{-5/2} ds dq/c dη` (SP 1900-1906). -/
def dm (c : ℝ) : Measure Coord :=
  Axi.ageμ c (-5 / 2)

/-- The unweighted `L^q(dm; CMerid)` space used for Riesz-Thorin interpolation (SP 1997-2005). -/
abbrev DmLp (c : ℝ) (q : ℝ≥0∞) : Type :=
  Lp CMerid q (dm c)

private theorem bgr_ennreal_eq : (23 / 8 : ℝ≥0∞) = ENNReal.ofReal (23 / 8) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

private theorem bgp_ennreal_eq : (11 / 4 : ℝ≥0∞) = ENNReal.ofReal (11 / 4) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

instance fact_one_le_two_ennreal : Fact (1 ≤ (2 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

instance fact_one_le_bgr_ennreal : Fact (1 ≤ (23 / 8 : ℝ≥0∞)) :=
  ⟨by rw [bgr_ennreal_eq, ENNReal.one_le_ofReal]; norm_num⟩

instance fact_one_le_bgp_ennreal : Fact (1 ≤ (11 / 4 : ℝ≥0∞)) :=
  ⟨by rw [bgp_ennreal_eq, ENNReal.one_le_ofReal]; norm_num⟩

/-- Cross-exponent agreement on finite-measure indicator atoms `1_S v` in `DmLp c`. -/
def DmOperatorConsistency (c : ℝ)
    (T₂ : DmLp c (2 : ℝ≥0∞) →L[ℂ] DmLp c (2 : ℝ≥0∞))
    (T_r : DmLp c (23 / 8 : ℝ≥0∞) →L[ℂ] DmLp c (23 / 8 : ℝ≥0∞))
    (T_p : DmLp c (11 / 4 : ℝ≥0∞) →L[ℂ] DmLp c (11 / 4 : ℝ≥0∞)) : Prop :=
  ∀ (S : Set Coord) (hS : MeasurableSet S) (hSμ : dm c S ≠ ∞) (v : CMerid),
    (T_p (indicatorConstLp (11 / 4 : ℝ≥0∞) hS hSμ v) : Coord → CMerid) =ᵐ[dm c]
      T₂ (indicatorConstLp (2 : ℝ≥0∞) hS hSμ v) ∧
    (T_r (indicatorConstLp (23 / 8 : ℝ≥0∞) hS hSμ v) : Coord → CMerid) =ᵐ[dm c]
      T₂ (indicatorConstLp (2 : ℝ≥0∞) hS hSμ v)

/-- **Riesz-Thorin interpolation bound on `DmLp c`** (`p₀ = 2`, `p₁ = 23/8`, `θ = 69/77`,
`p = 11/4`): if `‖T₂‖ ≤ A ε^{1/28}`, `‖T_r‖ ≤ M_r`, and `T_p, T_r, T₂` satisfy
`DmOperatorConsistency`, then `‖T_p‖ ≤ A^{8/77} M_r^{69/77} ε^{2/539}`. -/
theorem dmLp_rieszThorin_bound (c : ℝ)
    (T₂ : DmLp c (2 : ℝ≥0∞) →L[ℂ] DmLp c (2 : ℝ≥0∞))
    (T_r : DmLp c (23 / 8 : ℝ≥0∞) →L[ℂ] DmLp c (23 / 8 : ℝ≥0∞))
    (T_p : DmLp c (11 / 4 : ℝ≥0∞) →L[ℂ] DmLp c (11 / 4 : ℝ≥0∞))
    {A M_r ε : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (h2 : ‖T₂‖ ≤ A * ε ^ (1 / 28 : ℝ)) (hr : ‖T_r‖ ≤ M_r)
    (hcons : DmOperatorConsistency c T₂ T_r T_p) :
    ‖T_p‖ ≤ A ^ (8 / 77 : ℝ) * M_r ^ (69 / 77 : ℝ) * ε ^ (2 / 539 : ℝ) := by
  have hp₀ : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hp₁ : (23 / 8 : ℝ≥0∞) ≠ ∞ := by
    rw [bgr_ennreal_eq]
    exact ENNReal.ofReal_ne_top
  have hθ : (69 / 77 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hrt := norm_le_of_rieszThorin_of_indicator hp₀ hp₁ hθ
    rieszThorin_instance_exponents T₂ T_r T_p hcons
  have hrt' : ‖T_p‖ ≤ ‖T₂‖ ^ (8 / 77 : ℝ) * ‖T_r‖ ^ (1 - 8 / 77 : ℝ) := by
    convert hrt using 2 <;> norm_num
  have hrate := interp_rate (lam := (8 / 77 : ℝ)) (by norm_num) (by norm_num)
    hε hA (norm_nonneg T₂) (norm_nonneg T_r) h2 hr hrt'
  convert hrate using 2 <;> norm_num

/-- A bounded `ℂ`-linear operator `T` on `DmLp c q` realizes the conjugated comparison operator
`M B (T_ε - T_0) M⁻¹` at exponent `(r, q)` if its operator norm is controlled by any valid
`CompBoundAt` constant and conversely any upper bound on `‖T‖` yields `CompBoundAt`. -/
def IsDmRealization (ν c σ H₁ L₁ Γ : ℝ) (μ : ℂ) (B : ObsOp σ H₁ L₁ Γ) (ε r : ℝ) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (T : DmLp c q →L[ℂ] DmLp c q) : Prop :=
  (∀ M : ℝ, 0 ≤ M → CompBoundAt ν c σ H₁ L₁ Γ μ B ε r M → ‖T‖ ≤ M) ∧
    (∀ C : ℝ, 0 ≤ C → ‖T‖ ≤ C → CompBoundAt ν c σ H₁ L₁ Γ μ B ε r C)

/-- A profile-level operator `K_op : CProf → CProf` (representing `B(T_ε F - T_0 F)`) is a
consistent `ℂ`-linear family across `r ∈ {2, bgr, bgp}` if for each `r ∈ ({2, bgr, bgp} : Set ℝ)`:
1. `K_op F` is `hMeas c r`-a.e. strongly measurable whenever `InHr c r F`;
2. `K_op` respects `dm c`-a.e. equality on `InHr c r`;
3. `K_op` is `ℂ`-linear up to `dm c`-a.e. equality on `InHr c r`. -/
structure IsHrCompFamily (c : ℝ) (K_op : CProf → CProf) : Prop where
  meas : ∀ r ∈ ({2, bgr, bgp} : Set ℝ), ∀ F : CProf, InHr c r F →
    AEStronglyMeasurable (K_op F) (hMeas c r)
  congr_ae : ∀ r ∈ ({2, bgr, bgp} : Set ℝ), ∀ F₁ F₂ : CProf,
    InHr c r F₁ → InHr c r F₂ → F₁ =ᵐ[dm c] F₂ → K_op F₁ =ᵐ[dm c] K_op F₂
  map_add_ae : ∀ r ∈ ({2, bgr, bgp} : Set ℝ), ∀ F₁ F₂ : CProf,
    InHr c r F₁ → InHr c r F₂ → K_op (F₁ + F₂) =ᵐ[dm c] K_op F₁ + K_op F₂
  map_smul_ae : ∀ r ∈ ({2, bgr, bgp} : Set ℝ), ∀ (a : ℂ) (F : CProf),
    InHr c r F → K_op (a • F) =ᵐ[dm c] a • K_op F

/-- **Leaf 1 (`PartII-b:T18/1`, `HrComparisonOperatorFamily`, SP 1912-1938, 1992-2004)**:
For fixed parameters `(Γ, ν, c, σ, H₁, L₁, μ, B, ε)` in the free-comparison regime
(`1 ≤ Γ`, `Γ⁻¹ ≤ μ.re + 1/46`, `0 < ν, c, σ, ε`, `ε ≤ 1`, `2 * ε * c ≤ 1`), there exists a
profile-level assignment `K_op : CProf → CProf` (`F ↦ B(T_ε F - T_0 F)`) satisfying
`IsHrCompFamily c K_op` such that for each `r ∈ ({2, bgr, bgp} : Set ℝ)` and `M ≥ 0`,
`CompBoundAt ν c σ H₁ L₁ Γ μ B ε r M` holds if and only if
`∀ F : CProf, InHr c r F → hNorm c r (K_op F) ≤ ENNReal.ofReal M * hNorm c r F`. -/
def HrComparisonOperatorFamily : Prop :=
  ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
    H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 46 → 0 < ν → 0 < c → 0 < σ →
  ∀ B : ObsOp σ H₁ L₁ Γ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
    ∃ K_op : CProf → CProf,
      IsHrCompFamily c K_op ∧
      ∀ r ∈ ({2, bgr, bgp} : Set ℝ), ∀ M : ℝ, 0 ≤ M →
        (CompBoundAt ν c σ H₁ L₁ Γ μ B ε r M ↔
          ∀ F : CProf, InHr c r F → hNorm c r (K_op F) ≤ ENNReal.ofReal M * hNorm c r F)

/-- **Leaf 2 (`PartII-b:T18/2`, `DmLpRealizationOfHrOperator`, SP 1903-1908, 1994-2003)**:
For `0 < c` and any profile-level operator `K_op : CProf → CProf` satisfying `IsHrCompFamily c K_op`
that is bounded in `hNorm c r` at `r ∈ {2, bgr, bgp}`, conjugation by the weight isometry
`M : P ↦ √s P` between `(InHr c r, hNorm c r)` and `DmLp c q = Lp CMerid q (dm c)` yields bounded
`ℂ`-linear operators `T₂, T_r, T_p` on `DmLp c` satisfying `DmOperatorConsistency c T₂ T_r T_p` and
matching operator-norm bounds at each exponent. -/
def DmLpRealizationOfHrOperator : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (K_op : CProf → CProf), IsHrCompFamily c K_op →
    (∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ F : CProf, InHr c 2 F →
      hNorm c 2 (K_op F) ≤ ENNReal.ofReal M₂ * hNorm c 2 F) →
    (∃ M_r : ℝ, 0 ≤ M_r ∧ ∀ F : CProf, InHr c bgr F →
      hNorm c bgr (K_op F) ≤ ENNReal.ofReal M_r * hNorm c bgr F) →
    (∃ M_p : ℝ, 0 ≤ M_p ∧ ∀ F : CProf, InHr c bgp F →
      hNorm c bgp (K_op F) ≤ ENNReal.ofReal M_p * hNorm c bgp F) →
    ∃ (T₂ : DmLp c (2 : ℝ≥0∞) →L[ℂ] DmLp c (2 : ℝ≥0∞))
      (T_r : DmLp c (23 / 8 : ℝ≥0∞) →L[ℂ] DmLp c (23 / 8 : ℝ≥0∞))
      (T_p : DmLp c (11 / 4 : ℝ≥0∞) →L[ℂ] DmLp c (11 / 4 : ℝ≥0∞)),
      (∀ M : ℝ, 0 ≤ M →
        (‖T₂‖ ≤ M ↔ ∀ F : CProf, InHr c 2 F →
          hNorm c 2 (K_op F) ≤ ENNReal.ofReal M * hNorm c 2 F)) ∧
      (∀ M : ℝ, 0 ≤ M →
        (‖T_r‖ ≤ M ↔ ∀ F : CProf, InHr c bgr F →
          hNorm c bgr (K_op F) ≤ ENNReal.ofReal M * hNorm c bgr F)) ∧
      (∀ M : ℝ, 0 ≤ M →
        (‖T_p‖ ≤ M ↔ ∀ F : CProf, InHr c bgp F →
          hNorm c bgp (K_op F) ≤ ENNReal.ofReal M * hNorm c bgp F)) ∧
      DmOperatorConsistency c T₂ T_r T_p

/-- Existence of consistent `DmLp c` realizations of the conjugated comparison operator
`M B (T_ε - T_0) M⁻¹` at `q ∈ {2, 23/8, 11/4}` given qualitative `CompBoundAt` bounds at those
three exponents. -/
def ExistsConsistentDmRealizations : Prop :=
  ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
    H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 46 → 0 < ν → 0 < c → 0 < σ →
  ∀ B : ObsOp σ H₁ L₁ Γ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
    (∃ M₂ : ℝ, 0 ≤ M₂ ∧ CompBoundAt ν c σ H₁ L₁ Γ μ B ε 2 M₂) →
    (∃ M_r : ℝ, 0 ≤ M_r ∧ CompBoundAt ν c σ H₁ L₁ Γ μ B ε bgr M_r) →
    (∃ M_p : ℝ, 0 ≤ M_p ∧ CompBoundAt ν c σ H₁ L₁ Γ μ B ε bgp M_p) →
    ∃ (T₂ : DmLp c (2 : ℝ≥0∞) →L[ℂ] DmLp c (2 : ℝ≥0∞))
      (T_r : DmLp c (23 / 8 : ℝ≥0∞) →L[ℂ] DmLp c (23 / 8 : ℝ≥0∞))
      (T_p : DmLp c (11 / 4 : ℝ≥0∞) →L[ℂ] DmLp c (11 / 4 : ℝ≥0∞)),
      IsDmRealization ν c σ H₁ L₁ Γ μ B ε 2 (2 : ℝ≥0∞) T₂ ∧
      IsDmRealization ν c σ H₁ L₁ Γ μ B ε bgr (23 / 8 : ℝ≥0∞) T_r ∧
      IsDmRealization ν c σ H₁ L₁ Γ μ B ε bgp (11 / 4 : ℝ≥0∞) T_p ∧
      DmOperatorConsistency c T₂ T_r T_p

/-- **Assembly of `ExistsConsistentDmRealizations`** from `HrComparisonOperatorFamily` (`PartII-b:T18/1`)
and `DmLpRealizationOfHrOperator` (`PartII-b:T18/2`). -/
theorem existsConsistentDmRealizations_of
    (h1 : HrComparisonOperatorFamily)
    (h2 : DmLpRealizationOfHrOperator) :
    ExistsConsistentDmRealizations := by
  intro Γ ν c σ H₁ L₁ μ hΓ1 hν hνi hc hci hσi hH₁ hL₁ hμ hμre hν0 hc0 hσ0
    B ε hε0 hε1 hεc ⟨M₂, hM₂0, hM₂⟩ ⟨M_r, hMr0, hMr⟩ ⟨M_p, hMp0, hMp⟩
  obtain ⟨K_op, hfam, hiff⟩ :=
    h1 Γ ν c σ H₁ L₁ μ hΓ1 hν hνi hc hci hσi hH₁ hL₁ hμ hμre hν0 hc0 hσ0 B ε hε0 hε1 hεc
  have hm2 : (2 : ℝ) ∈ ({2, bgr, bgp} : Set ℝ) := by simp
  have hmr : bgr ∈ ({2, bgr, bgp} : Set ℝ) := by simp
  have hmp : bgp ∈ ({2, bgr, bgp} : Set ℝ) := by simp
  have hK₂ : ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ F : CProf, InHr c 2 F →
      hNorm c 2 (K_op F) ≤ ENNReal.ofReal M₂ * hNorm c 2 F :=
    ⟨M₂, hM₂0, (hiff 2 hm2 M₂ hM₂0).mp hM₂⟩
  have hKr : ∃ M_r : ℝ, 0 ≤ M_r ∧ ∀ F : CProf, InHr c bgr F →
      hNorm c bgr (K_op F) ≤ ENNReal.ofReal M_r * hNorm c bgr F :=
    ⟨M_r, hMr0, (hiff bgr hmr M_r hMr0).mp hMr⟩
  have hKp : ∃ M_p : ℝ, 0 ≤ M_p ∧ ∀ F : CProf, InHr c bgp F →
      hNorm c bgp (K_op F) ≤ ENNReal.ofReal M_p * hNorm c bgp F :=
    ⟨M_p, hMp0, (hiff bgp hmp M_p hMp0).mp hMp⟩
  obtain ⟨T₂, T_r, T_p, hT₂, hTr, hTp, hcons⟩ := h2 c hc0 K_op hfam hK₂ hKr hKp
  refine ⟨T₂, T_r, T_p, ?_, ?_, ?_, hcons⟩
  · exact ⟨fun M hM hcM => (hT₂ M hM).mpr ((hiff 2 hm2 M hM).mp hcM),
      fun C hC hnC => (hiff 2 hm2 C hC).mpr ((hT₂ C hC).mp hnC)⟩
  · exact ⟨fun M hM hcM => (hTr M hM).mpr ((hiff bgr hmr M hM).mp hcM),
      fun C hC hnC => (hiff bgr hmr C hC).mpr ((hTr C hC).mp hnC)⟩
  · exact ⟨fun M hM hcM => (hTp M hM).mpr ((hiff bgp hmp M hM).mp hcM),
      fun C hC hnC => (hiff bgp hmp C hC).mpr ((hTp C hC).mp hnC)⟩

/-- **Conditional assembly of `LpInterpolationStep` (`PartII-b:T18`)** from
`HrComparisonOperatorFamily` (`PartII-b:T18/1`) and `DmLpRealizationOfHrOperator` (`PartII-b:T18/2`). -/
theorem lpInterpolationStep_of_leaves
    (h1 : HrComparisonOperatorFamily)
    (h2 : DmLpRealizationOfHrOperator)
    (_h16 : UnforcedLeray.Short.IIb.HilbertBodyComparison) :
    UnforcedLeray.Short.IIb.LpInterpolationStep := by
  have hleaf := existsConsistentDmRealizations_of h1 h2
  intro Γ ν c σ H₁ L₁ μ hΓ1 hν hνi hc hci hσi hH₁ hL₁ hμ hμre hν0 hc0 hσ0
    B ε hε0 hε1 hεc A M_r hA0 hMr0 h2_bd hr hp
  have hM₂0 : 0 ≤ A * ε ^ (1 / 28 : ℝ) := by positivity
  obtain ⟨T₂, T_r, T_p, hT₂, hTr, hTp, hcons⟩ :=
    hleaf Γ ν c σ H₁ L₁ μ hΓ1 hν hνi hc hci hσi hH₁ hL₁ hμ hμre hν0 hc0 hσ0
      B ε hε0 hε1 hεc ⟨A * ε ^ (1 / 28 : ℝ), hM₂0, h2_bd⟩ ⟨M_r, hMr0, hr⟩ hp
  have hT₂_le : ‖T₂‖ ≤ A * ε ^ (1 / 28 : ℝ) := hT₂.1 _ hM₂0 h2_bd
  have hTr_le : ‖T_r‖ ≤ M_r := hTr.1 _ hMr0 hr
  have hTp_le : ‖T_p‖ ≤ A ^ (8 / 77 : ℝ) * M_r ^ (69 / 77 : ℝ) * ε ^ (2 / 539 : ℝ) :=
    dmLp_rieszThorin_bound c T₂ T_r T_p hε0.le hA0 hT₂_le hTr_le hcons
  have hC0 : 0 ≤ A ^ (8 / 77 : ℝ) * M_r ^ (69 / 77 : ℝ) * ε ^ (2 / 539 : ℝ) := by positivity
  exact hTp.2 _ hC0 hTp_le

end UnforcedLeray.Short.IIb

end
