import UnforcedLeray.Short.PartIIb.StatementsNonlinear
import UnforcedLeray.Short.PartIIb.Sub.G1
import UnforcedLeray.Short.PartIIb.Sub.G4
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16
import UnforcedLeray.Short.PartIIb.Compose
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSolenoidalCorr
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSymmetry

/-!
# Part II-b, `ORG:PartII-b/comparison-and-strong-design`: statement design and conditional assemblies

Source of record: `the November 2 reference manuscript` (SP), lines 1992-2023,
2430-2470, 2503-2562.

This file unserializes the two remaining `STATEMENT-FIRST:` chains in `PartII-b`:
* Chain (a): `T16 -> T18 -> T19 -> T20 -> G3 -> G5` (`G1 -> G2 -> G3 -> G5`);
* Chain (b): `G4 -> Q1 -> S1 -> S2 -> S3` (`Q1 -> Q2`).

## Statements defined here

1. `LpInterpolationStep` (`PartII-b:T18`, SP 1997-2005): Riesz-Thorin interpolation of the single
   consistent operator `M B(T_ε - T_0) M⁻¹` on `L^q(dm)` (`dm = s^{-5/2} ds dq/c dη`) between
   `r = 2` (rate `A ε^{1/28}`) and `r = bgr = 23/8` (bound `M_r`), with weight `λ = 8/77` at
   `p = bgp = 11/4` giving rate `A^{8/77} M_r^{69/77} ε^{2/539}`;
2. `YoungLateOperatorBounds` (`PartII-b:G2`, SP 2432-2445): existence of the physical interaction
   operator `K_ε` on `H_p` (`IsKop p Ke`) and the young/late age-indicator operator bounds
   `‖1_{s<σ} K_ε‖ + ‖1_{s<σ} K_0‖ ≤ 𝒫_ν √σ` (`0 < σ ≤ 1`),
   `‖1_{s>S} K_ε‖ ≤ 𝒫_ν (S^{-1/2} + ε)` and `‖1_{s>S} K_0‖ ≤ 𝒫_ν S^{-1/2}` (`1 ≤ S`);
3. `WindowComparison` (`PartII-b:G3`, SP 2438-2463): on the intermediate age window
   `σ = ε^a ≤ s ≤ S = ε^{-b}`, `‖1_{σ≤s≤S}(K_ε - K_0)‖ ≤ 𝒫_ν (ε^{2/539 - N(a+b)} + e^{-D/ν})`
   for a fixed `N : ℕ` independent of `Sig, q, D, a, b, d_±`;
4. `QuadBound` (`PartII-b:Q1`, SP 2503-2518): at fixed slow data `(Σ, λ, q)`, existence of a
   bilinear map `B : p.Z →ₗ[ℝ] p.Z →ₗ[ℝ] p.Y` representing `QuadRel` with
   `‖B z z'‖_Y ≤ 𝒫_ν ‖z‖_Z ‖z'‖_Z`;
5. `StrongFirstDerivative` (`PartII-b:S1`, SP 2525-2541): at fixed slow data `(Σ, λ, q)` and
   `2m < 3d₋/11`, for any solution `z` of `ProjectedEquation p z` in the contraction ball,
   `Dw ∈ D_p` (`HasPhaseOp (-∂_j)`) and display `short-bg:strong` holds (`w` in `C_per L^p` and
   `W^{1,∞}`, `E_εα` in `W^{1,∞}` bounded by `𝒫_ν e^{m/ν} ε^{3/11}`);
6. `StrongAllOrders` (`PartII-b:S2`, SP 2541-2562): at fixed slow data `(Σ, λ, q)` and
   `2m < 3d₋/11`, for any solution `z` of `ProjectedEquation p z` in the contraction ball,
   iterated spatial derivatives `D^α w` of all orders `k` lie in the maximal graph `D_p`,
   `U(τ) = bgField p z τ` is `C^k` in space with `D^k w` bounded and `D^k U` in `C_per L⁴`, and
   `U_raw`, `E_ε` are smooth bounded solenoidal pieces.

## Proved here (zero `sorry`)

* `lpFreeComparison_of_core` (`PartII-b:T19`): `HilbertBodyComparison → LpInterpolationStep → LpFreeComparison`;
* `globalOperatorComparison_of_core` (`PartII-b:G5`):
  `YoungLateOperatorBounds → WindowComparison → AffineInletFacts → GlobalOperatorComparison`;
* `quadraticFamily_of_core` (`PartII-b:Q2`): `QuadBound → QuadraticFamily`;
* `bgField_periodic_solenoidal_symmetric`: periodicity, solenoidality, and `𝒪`-invariance of
  `bgField p z` from the piece regularity of `U_raw`, `E_ε` and the graph trace of `w`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

/-! ## 1. Free `L^p` comparison (`T18`, `T19`, SP 1992-2005) -/

/-- Pointwise-in-parameters comparison bound at exponent `r` with factor `M`: for every `F ∈ H_r`
and responses `b_ε = T_ε F`, `b_0 = T_0 F`, the weak `(q, η)`-derivatives of `b_ε - b_0` exist and
`‖B(b_ε - b_0)‖_{H_r} ≤ M ‖F‖_{H_r}`. -/
def CompBoundAt (ν c σ H₁ L₁ Γ : ℝ) (μ : ℂ) (B : ObsOp σ H₁ L₁ Γ) (ε r M : ℝ) : Prop :=
  ∀ F bε b0 : CProf, InHr c r F → InHr c r bε → IsResponse ν c ε μ r F bε →
    IsFlatResponse ν μ F b0 → InFlatClass c r b0 →
    ∃ gq gη : CProf, HasWeakVec vQ0 dZero (bε - b0) gq ∧ HasWeakVec vEta dZero (bε - b0) gη ∧
      hNorm c r (B.apply (bε - b0) gq gη) ≤ ENNReal.ofReal M * hNorm c r F

/-- **`PartII-b:T18` (`LpInterpolationStep`)** (SP 1997-2005): Riesz-Thorin interpolation of the
single consistent operator `M B(T_ε - T_0) M⁻¹` on `L^q(dm)` (`dm = s^{-5/2} ds dq/c dη`,
SP 1900-1906) between the Hilbert endpoint `r = 2` (bound `A ε^{1/28}`) and `r = bgr = 23/8`
(bound `M_r`), given qualitative boundedness on `H_{11/4}`, yielding the `H_{11/4}` (`p = bgp`)
bound `A^{8/77} M_r^{69/77} ε^{2/539}` (`λ = 8/77`, `1 - λ = 69/77`, `λ/28 = 2/539`). -/
def LpInterpolationStep : Prop :=
  ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
    H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 46 → 0 < ν → 0 < c → 0 < σ →
  ∀ B : ObsOp σ H₁ L₁ Γ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
  ∀ A M_r : ℝ, 0 ≤ A → 0 ≤ M_r →
    CompBoundAt ν c σ H₁ L₁ Γ μ B ε 2 (A * ε ^ (1 / 28 : ℝ)) →
    CompBoundAt ν c σ H₁ L₁ Γ μ B ε bgr M_r →
    (∃ M_p : ℝ, 0 ≤ M_p ∧ CompBoundAt ν c σ H₁ L₁ Γ μ B ε bgp M_p) →
    CompBoundAt ν c σ H₁ L₁ Γ μ B ε bgp
      (A ^ (8 / 77 : ℝ) * M_r ^ (69 / 77 : ℝ) * ε ^ (2 / 539 : ℝ))

private theorem rpow_weighted_prod_le {C₂ C_r Γ : ℝ} {k₂ k_r : ℕ}
    (hC₂ : 0 < C₂) (hC_r : 0 < C_r) (hΓ1 : 1 ≤ Γ) :
    (C₂ * Γ ^ k₂) ^ (8 / 77 : ℝ) * (C_r * Γ ^ k_r) ^ (69 / 77 : ℝ) ≤
      (C₂ ^ (8 / 77 : ℝ) * C_r ^ (69 / 77 : ℝ)) * Γ ^ (k₂ + k_r) := by
  have hΓ0 : 0 ≤ Γ := by linarith
  have hk₂ : 0 ≤ (Γ ^ k₂ : ℝ) := by positivity
  have hk_r : 0 ≤ (Γ ^ k_r : ℝ) := by positivity
  rw [Real.mul_rpow hC₂.le hk₂, Real.mul_rpow hC_r.le hk_r]
  have hpow2 : (Γ ^ k₂) ^ (8 / 77 : ℝ) ≤ (Γ ^ (k₂ + k_r)) ^ (8 / 77 : ℝ) := by
    apply Real.rpow_le_rpow hk₂
    · exact pow_le_pow_right₀ hΓ1 (Nat.le_add_right k₂ k_r)
    · norm_num
  have hpowr : (Γ ^ k_r) ^ (69 / 77 : ℝ) ≤ (Γ ^ (k₂ + k_r)) ^ (69 / 77 : ℝ) := by
    apply Real.rpow_le_rpow hk_r
    · exact pow_le_pow_right₀ hΓ1 (Nat.le_add_left k_r k₂)
    · norm_num
  have hcomb : (Γ ^ (k₂ + k_r)) ^ (8 / 77 : ℝ) * (Γ ^ (k₂ + k_r)) ^ (69 / 77 : ℝ) =
      Γ ^ (k₂ + k_r) := by
    have hpos : 0 < Γ ^ (k₂ + k_r) := by positivity
    rw [← Real.rpow_add hpos]
    norm_num
  calc (C₂ ^ (8 / 77 : ℝ) * (Γ ^ k₂) ^ (8 / 77 : ℝ)) *
        (C_r ^ (69 / 77 : ℝ) * (Γ ^ k_r) ^ (69 / 77 : ℝ))
      = (C₂ ^ (8 / 77 : ℝ) * C_r ^ (69 / 77 : ℝ)) *
          ((Γ ^ k₂) ^ (8 / 77 : ℝ) * (Γ ^ k_r) ^ (69 / 77 : ℝ)) := by ring
    _ ≤ (C₂ ^ (8 / 77 : ℝ) * C_r ^ (69 / 77 : ℝ)) *
          ((Γ ^ (k₂ + k_r)) ^ (8 / 77 : ℝ) * (Γ ^ (k₂ + k_r)) ^ (69 / 77 : ℝ)) := by
        gcongr
    _ = (C₂ ^ (8 / 77 : ℝ) * C_r ^ (69 / 77 : ℝ)) * Γ ^ (k₂ + k_r) := by rw [hcomb]

/-- **Conditional assembly of `LpFreeComparison` (`PartII-b:T19`, SP 1940-2005)** from
`HilbertBodyComparison` (`T16`), `LpInterpolationStep` (`T18`), and the compiled `T17` endpoint
bounds (`lp_endpoint_bound`, `compRate_zero`). -/
theorem lpFreeComparison_of_core (h16 : HilbertBodyComparison) (h18 : LpInterpolationStep) :
    LpFreeComparison := by
  obtain ⟨k₂, C₂, hC₂, H2⟩ := h16
  obtain ⟨k_r, C_r, hC_r, Hr⟩ := lp_endpoint_bound
  have hbgp1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have hbgp3 : bgp < (3 : ℝ) := by norm_num [bgp]
  obtain ⟨k_p, C_p, hC_p, Hp⟩ := compRate_zero bgp hbgp1 hbgp3
  refine ⟨k₂ + k_r, C₂ ^ (8 / 77 : ℝ) * C_r ^ (69 / 77 : ℝ), by positivity, ?_⟩
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap hν hc hσ
    B ε hε0 hε1 hP
  have hgap2 : Γ⁻¹ ≤ μ.re + 1 / 4 := by linarith
  have hgap_p : Γ⁻¹ ≤ μ.re + (3 / bgp - 1) / 2 := by
    have : (1 / 46 : ℝ) ≤ (3 / bgp - 1) / 2 := by norm_num [bgp]
    linarith
  have h2_at : CompBoundAt ν c σ H₁ L₁ Γ μ B ε 2 ((C₂ * Γ ^ k₂) * ε ^ (1 / 28 : ℝ)) :=
    H2 Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap2 hν hc hσ B ε hε0 hε1 hP
  have hr_at : CompBoundAt ν c σ H₁ L₁ Γ μ B ε bgr (C_r * Γ ^ k_r) := by
    intro F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
    obtain ⟨gq, gη, hgq, hgη, hbd⟩ :=
      Hr Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap hν hc hσ B ε hε0 hε1 hP
        F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
    rw [Real.rpow_zero, mul_one] at hbd
    exact ⟨gq, gη, hgq, hgη, hbd⟩
  have hp_at : ∃ M_p : ℝ, 0 ≤ M_p ∧ CompBoundAt ν c σ H₁ L₁ Γ μ B ε bgp M_p := by
    refine ⟨C_p * Γ ^ k_p, by positivity, ?_⟩
    intro F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
    obtain ⟨gq, gη, hgq, hgη, hbd⟩ :=
      Hp Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap_p hν hc hσ B ε hε0 hε1 hP
        F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
    rw [Real.rpow_zero, mul_one] at hbd
    exact ⟨gq, gη, hgq, hgη, hbd⟩
  have hinterp := h18 Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap hν hc hσ
    B ε hε0 hε1 hP (C₂ * Γ ^ k₂) (C_r * Γ ^ k_r) (by positivity) (by positivity) h2_at hr_at hp_at
  intro F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
  obtain ⟨gq, gη, hgq, hgη, hbd⟩ := hinterp F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
  refine ⟨gq, gη, hgq, hgη, hbd.trans ?_⟩
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hprod := rpow_weighted_prod_le (k₂ := k₂) (k_r := k_r) hC₂ hC_r hΓ1
  exact mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hε0.le _)

/-! ## 2. Young/late tails, window comparison, and global comparison (`G2`, `G3`, `G5`, SP 2430-2470) -/

/-- Young age region `s < σ` in chart coordinates `x = (s, (q, η))`. -/
def youngAgeSet (σ : ℝ) : Set Coord := {x : Coord | x.1 < σ}

/-- Intermediate window age region `σ ≤ s ≤ S` in chart coordinates. -/
def windowAgeSet (σ S : ℝ) : Set Coord := {x : Coord | σ ≤ x.1 ∧ x.1 ≤ S}

/-- Late age region `S < s` in chart coordinates. -/
def lateAgeSet (S : ℝ) : Set Coord := {x : Coord | S < x.1}

/-- The `H_p` norm of an element `g : HpR c` restricted to an age region `A ⊆ Coord`:
`‖1_A g‖_{H_p}`. -/
def hpIndNorm (c : ℝ) (A : Set Coord) (g : HpR c) : ℝ :=
  (eLpNorm (A.indicator (g : Coord → Axi.Merid)) (ENNReal.ofReal bgp) (hMeas c bgp)).toReal

theorem measurableSet_youngAgeSet (σ : ℝ) : MeasurableSet (youngAgeSet σ) :=
  measurableSet_lt measurable_fst measurable_const

theorem measurableSet_windowAgeSet (σ S : ℝ) : MeasurableSet (windowAgeSet σ S) :=
  (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)

theorem measurableSet_lateAgeSet (S : ℝ) : MeasurableSet (lateAgeSet S) :=
  measurableSet_lt measurable_const measurable_fst

theorem hpIndNorm_nonneg (c : ℝ) (A : Set Coord) (g : HpR c) : 0 ≤ hpIndNorm c A g :=
  ENNReal.toReal_nonneg

private theorem eLpNorm_indicator_ne_top (c : ℝ) (A : Set Coord) (g : HpR c) :
    eLpNorm (A.indicator (g : Coord → Axi.Merid)) (ENNReal.ofReal bgp) (hMeas c bgp) ≠ ⊤ :=
  ((eLpNorm_indicator_le (s := A) (g : Coord → Axi.Merid)).trans_lt (Lp.eLpNorm_lt_top g)).ne

/-- Triangle splitting of `‖Ke f - K0 f‖_{H_p}` across the young (`s < σ`), window (`σ ≤ s ≤ S`),
and late (`s > S`) age regions. -/
theorem norm_sub_le_hpIndNorm_split (c σ S : ℝ) (Kef K0f : HpR c) :
    ‖Kef - K0f‖ ≤
      hpIndNorm c (youngAgeSet σ) Kef + hpIndNorm c (youngAgeSet σ) K0f +
        hpIndNorm c (windowAgeSet σ S) (Kef - K0f) +
        hpIndNorm c (lateAgeSet S) Kef + hpIndNorm c (lateAgeSet S) K0f := by
  set pE := ENNReal.ofReal bgp
  set μ := hMeas c bgp
  have hp1 : (1 : ℝ≥0∞) ≤ pE := Fact.out
  set f1 : Coord → Axi.Merid := (youngAgeSet σ).indicator (Kef : Coord → Axi.Merid)
  set f2 : Coord → Axi.Merid := (youngAgeSet σ).indicator (K0f : Coord → Axi.Merid)
  set f3 : Coord → Axi.Merid := (windowAgeSet σ S).indicator ((Kef - K0f : HpR c) : Coord → Axi.Merid)
  set f4 : Coord → Axi.Merid := (lateAgeSet S).indicator (Kef : Coord → Axi.Merid)
  set f5 : Coord → Axi.Merid := (lateAgeSet S).indicator (K0f : Coord → Axi.Merid)
  have mf1 : AEStronglyMeasurable f1 μ := (Lp.aestronglyMeasurable Kef).indicator (measurableSet_youngAgeSet σ)
  have mf2 : AEStronglyMeasurable f2 μ := (Lp.aestronglyMeasurable K0f).indicator (measurableSet_youngAgeSet σ)
  have mf3 : AEStronglyMeasurable f3 μ :=
    (Lp.aestronglyMeasurable (Kef - K0f)).indicator (measurableSet_windowAgeSet σ S)
  have mf4 : AEStronglyMeasurable f4 μ := (Lp.aestronglyMeasurable Kef).indicator (measurableSet_lateAgeSet S)
  have mf5 : AEStronglyMeasurable f5 μ := (Lp.aestronglyMeasurable K0f).indicator (measurableSet_lateAgeSet S)
  have hptw : ∀ᵐ x ∂μ, ‖((Kef - K0f : HpR c) : Coord → Axi.Merid) x‖ ≤
      (((((fun y => ‖f1 y‖) + fun y => ‖f2 y‖) + fun y => ‖f3 y‖) + fun y => ‖f4 y‖) + fun y => ‖f5 y‖) x := by
    filter_upwards [Lp.coeFn_sub Kef K0f] with x hx
    simp only [Pi.add_apply]
    by_cases h1 : x.1 < σ
    · have hm1 : x ∈ youngAgeSet σ := h1
      have : ‖((Kef - K0f : HpR c) : Coord → Axi.Merid) x‖ ≤ ‖f1 x‖ + ‖f2 x‖ := by
        rw [hx, Pi.sub_apply]
        dsimp [f1, f2]
        rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm1]
        exact norm_sub_le _ _
      linarith [norm_nonneg (f3 x), norm_nonneg (f4 x), norm_nonneg (f5 x)]
    · by_cases h2 : x.1 ≤ S
      · have hm2 : x ∈ windowAgeSet σ S := ⟨not_lt.mp h1, h2⟩
        have : ‖((Kef - K0f : HpR c) : Coord → Axi.Merid) x‖ = ‖f3 x‖ := by
          dsimp [f3]
          rw [Set.indicator_of_mem hm2]
        linarith [norm_nonneg (f1 x), norm_nonneg (f2 x), norm_nonneg (f4 x), norm_nonneg (f5 x)]
      · have hm3 : x ∈ lateAgeSet S := not_le.mp h2
        have : ‖((Kef - K0f : HpR c) : Coord → Axi.Merid) x‖ ≤ ‖f4 x‖ + ‖f5 x‖ := by
          rw [hx, Pi.sub_apply]
          dsimp [f4, f5]
          rw [Set.indicator_of_mem hm3, Set.indicator_of_mem hm3]
          exact norm_sub_le _ _
        linarith [norm_nonneg (f1 x), norm_nonneg (f2 x), norm_nonneg (f3 x)]
  have hmono : eLpNorm ((Kef - K0f : HpR c) : Coord → Axi.Merid) pE μ ≤
      eLpNorm (((((fun y => ‖f1 y‖) + fun y => ‖f2 y‖) + fun y => ‖f3 y‖) + fun y => ‖f4 y‖) + fun y => ‖f5 y‖) pE μ :=
    eLpNorm_mono_ae_real hptw
  have hsum :
      eLpNorm (((((fun y => ‖f1 y‖) + fun y => ‖f2 y‖) + fun y => ‖f3 y‖) + fun y => ‖f4 y‖) + fun y => ‖f5 y‖) pE μ ≤
      eLpNorm f1 pE μ + eLpNorm f2 pE μ + eLpNorm f3 pE μ + eLpNorm f4 pE μ + eLpNorm f5 pE μ := by
    have s12 := eLpNorm_add_le mf1.norm mf2.norm hp1
    have s123 := (eLpNorm_add_le (mf1.norm.add mf2.norm) mf3.norm hp1).trans (add_le_add s12 le_rfl)
    have s1234 := (eLpNorm_add_le ((mf1.norm.add mf2.norm).add mf3.norm) mf4.norm hp1).trans
      (add_le_add s123 le_rfl)
    have s12345 := (eLpNorm_add_le (((mf1.norm.add mf2.norm).add mf3.norm).add mf4.norm)
      mf5.norm hp1).trans (add_le_add s1234 le_rfl)
    simpa only [eLpNorm_norm] using s12345
  have htot := hmono.trans hsum
  have hne1 : eLpNorm f1 pE μ ≠ ⊤ := eLpNorm_indicator_ne_top c (youngAgeSet σ) Kef
  have hne2 : eLpNorm f2 pE μ ≠ ⊤ := eLpNorm_indicator_ne_top c (youngAgeSet σ) K0f
  have hne3 : eLpNorm f3 pE μ ≠ ⊤ := eLpNorm_indicator_ne_top c (windowAgeSet σ S) (Kef - K0f)
  have hne4 : eLpNorm f4 pE μ ≠ ⊤ := eLpNorm_indicator_ne_top c (lateAgeSet S) Kef
  have hne5 : eLpNorm f5 pE μ ≠ ⊤ := eLpNorm_indicator_ne_top c (lateAgeSet S) K0f
  have hne12 : eLpNorm f1 pE μ + eLpNorm f2 pE μ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hne1, hne2⟩
  have hne123 : eLpNorm f1 pE μ + eLpNorm f2 pE μ + eLpNorm f3 pE μ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hne12, hne3⟩
  have hne1234 : eLpNorm f1 pE μ + eLpNorm f2 pE μ + eLpNorm f3 pE μ + eLpNorm f4 pE μ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hne123, hne4⟩
  have hne_all :
      eLpNorm f1 pE μ + eLpNorm f2 pE μ + eLpNorm f3 pE μ + eLpNorm f4 pE μ + eLpNorm f5 pE μ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hne1234, hne5⟩
  have htoReal := ENNReal.toReal_mono hne_all htot
  rw [← Lp.norm_def, ENNReal.toReal_add hne1234 hne5, ENNReal.toReal_add hne123 hne4,
    ENNReal.toReal_add hne12 hne3, ENNReal.toReal_add hne1 hne2] at htoReal
  exact htoReal

/-- **`PartII-b:G2` (`YoungLateOperatorBounds`)** (SP 2432-2445): in the regime and for small `ν`,
the physical interaction operator `K_ε` exists as a bounded operator on `H_p` (`IsKop p Ke`), and
for any `Ke, K0 : HpR p.c →L[ℝ] HpR p.c` satisfying `IsKop p Ke` and `IsK0op p K0`:
* at the young end (`0 < σ ≤ 1`),
  `‖1_{s < σ} K_ε f‖_{H_p} + ‖1_{s < σ} K_0 f‖_{H_p} ≤ C ν^{-k} √σ ‖f‖_{H_p}`;
* at the late end (`1 ≤ S`), `‖1_{s > S} K_ε f‖_{H_p} ≤ C ν^{-k} (S^{-1/2} + ε) ‖f‖_{H_p}` and
  `‖1_{s > S} K_0 f‖_{H_p} ≤ C ν^{-k} S^{-1/2} ‖f‖_{H_p}`. -/
def YoungLateOperatorBounds : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      (∃ Ke : HpR p.c →L[ℝ] HpR p.c, IsKop p Ke) ∧
      ∀ (Ke K0 : HpR p.c →L[ℝ] HpR p.c), IsKop p Ke → IsK0op p K0 →
        (∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ f : HpR p.c,
          hpIndNorm p.c (youngAgeSet σ) (Ke f) + hpIndNorm p.c (youngAgeSet σ) (K0 f) ≤
            C * (p.ν ^ k)⁻¹ * Real.sqrt σ * ‖f‖) ∧
        (∀ S : ℝ, 1 ≤ S → ∀ f : HpR p.c,
          hpIndNorm p.c (lateAgeSet S) (Ke f) ≤
            C * (p.ν ^ k)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε) * ‖f‖ ∧
          hpIndNorm p.c (lateAgeSet S) (K0 f) ≤
            C * (p.ν ^ k)⁻¹ * S ^ (-(1 / 2 : ℝ)) * ‖f‖)

/-- **`PartII-b:G3` (`WindowComparison`)** (SP 2438-2463): there is a fixed integer `N`
(independent of `Sig, q, D, a, b, d_±`) such that for every `D > 0`, `a, b > 0` (the window
exponents `σ = ε^a`, `S = ε^{-b}`) and `d_±`, in the regime and for small `ν`, any operators
`Ke, K0` satisfying `IsKop p Ke` and `IsK0op p K0` obey
`‖1_{σ ≤ s ≤ S}(K_ε f - K_0 f)‖_{H_p} ≤ C ν^{-k} (ε^{2/539 - N(a+b)} + e^{-D/ν}) ‖f‖_{H_p}`. -/
def WindowComparison : Prop :=
  ∃ N : ℕ, ∀ D : ℝ, 0 < D → ∀ a b : ℝ, 0 < a → 0 < b → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ (Ke K0 : HpR p.c →L[ℝ] HpR p.c), IsKop p Ke → IsK0op p K0 → ∀ f : HpR p.c,
        hpIndNorm p.c (windowAgeSet (p.ε ^ a) (p.ε ^ (-b))) (Ke f - K0 f) ≤
          C * (p.ν ^ k)⁻¹ * (p.ε ^ ((2 / 539 : ℝ) - N * (a + b)) + Real.exp (-D / p.ν)) * ‖f‖

private theorem inv_pow_mono_of_le_one {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) {j k : ℕ}
    (hjk : j ≤ k) : (ν ^ j)⁻¹ ≤ (ν ^ k)⁻¹ := by
  rw [inv_le_inv₀ (pow_pos hν0 j) (pow_pos hν0 k)]
  exact pow_le_pow_of_le_one hν0.le hν1 hjk

/-- **Conditional assembly of `GlobalOperatorComparison` (`PartII-b:G5`, SP 2430-2470)** from
`YoungLateOperatorBounds` (`G2`), `WindowComparison` (`G3`), and `AffineInletFacts` (`G4`). -/
theorem globalOperatorComparison_of_core (h2 : YoungLateOperatorBounds) (h3 : WindowComparison)
    (h4 : AffineInletFacts) : GlobalOperatorComparison := by
  obtain ⟨N, hN⟩ := h3
  refine ⟨N, ?_⟩
  intro Sig lam q hSig hq D hD a b ha hb dm dp hdm
  obtain ⟨C₂, k₂, ν₂, hC₂, hν₂, H2⟩ := h2 dm dp hdm
  obtain ⟨C₃, k₃, ν₃, hC₃, hν₃, H3⟩ := hN D hD a b ha hb dm dp hdm
  obtain ⟨C₄, k₄, ν₄, hC₄, hν₄, H4⟩ := h4.1 Sig lam q hSig hq dm dp hdm
  set k : ℕ := max k₂ (max k₃ k₄)
  set C : ℝ := 2 * C₂ + C₃ + C₄
  set ν₀ : ℝ := min (min ν₂ ν₃) (min ν₄ 1)
  have hC : 0 < C := by positivity
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν₂ hν₃) (lt_min hν₄ zero_lt_one)
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hν hSg hmode
  have hν_pos : 0 < p.ν := p.ν_pos
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₄' : p.ν ≤ ν₄ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨⟨Ke₀, hKe₀⟩, H2_bd⟩ := H2 p d hreg hν₂'
  have H3_bd := H3 p d hreg hν₃'
  obtain ⟨⟨Ce₀, hCe₀⟩, H4_bd⟩ := H4 p d hreg hν₄' hSg hmode
  refine ⟨⟨Ke₀, Ce₀, hKe₀, hCe₀⟩, ?_⟩
  intro Ke K0 Ce C0 hKe hK0 hCe hC0
  obtain ⟨hyoung, hlate⟩ := H2_bd Ke K0 hKe hK0
  have hwin := H3_bd Ke K0 hKe hK0
  have hcol := H4_bd Ce C0 hCe hC0
  have hε0 : 0 < p.ε := p.ε_pos
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hν_pos.le
  set σ : ℝ := p.ε ^ a
  set S : ℝ := p.ε ^ (-b)
  have hσ0 : 0 < σ := Real.rpow_pos_of_pos hε0 a
  have hσ1 : σ ≤ 1 := Real.rpow_le_one hε0.le hε1 ha.le
  have hS1 : 1 ≤ S := by
    dsimp [S]
    rw [Real.rpow_neg hε0.le]
    exact one_le_inv₀ (Real.rpow_pos_of_pos hε0 b) |>.mpr (Real.rpow_le_one hε0.le hε1 hb.le)
  have hsqrt_σ : Real.sqrt σ = p.ε ^ (a / 2) := by
    dsimp [σ]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε0.le]
    ring_nf
  have hS_rpow : S ^ (-(1 / 2 : ℝ)) = p.ε ^ (b / 2) := by
    dsimp [S]
    rw [← Real.rpow_mul hε0.le]
    ring_nf
  have hk₂ : (p.ν ^ k₂)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_of_le_one hν_pos hν1 (le_max_left _ _)
  have hk₃ : (p.ν ^ k₃)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_of_le_one hν_pos hν1 ((le_max_left _ _).trans (le_max_right _ _))
  have hk₄ : (p.ν ^ k₄)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_of_le_one hν_pos hν1 ((le_max_right _ _).trans (le_max_right _ _))
  set B_terms : ℝ :=
    p.ε ^ (a / 2) + p.ε ^ (b / 2) + p.ε + p.ε ^ ((2 / 539 : ℝ) - N * (a + b)) +
      Real.exp (-D / p.ν)
  have hB_pos : 0 ≤ B_terms := by
    dsimp [B_terms]
    positivity
  have hKeK0 : ‖Ke - K0‖ ≤ (2 * C₂ + C₃) * (p.ν ^ k)⁻¹ * B_terms := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    have hsplit := norm_sub_le_hpIndNorm_split p.c σ S (Ke f) (K0 f)
    have hy := hyoung σ hσ0 hσ1 f
    obtain ⟨hl1, hl2⟩ := hlate S hS1 f
    have hw := hwin f
    rw [hsqrt_σ] at hy
    rw [hS_rpow] at hl1 hl2
    have hy' : hpIndNorm p.c (youngAgeSet σ) (Ke f) + hpIndNorm p.c (youngAgeSet σ) (K0 f) ≤
        C₂ * (p.ν ^ k)⁻¹ * p.ε ^ (a / 2) * ‖f‖ := by
      refine hy.trans ?_
      gcongr
    have hl1' : hpIndNorm p.c (lateAgeSet S) (Ke f) ≤
        C₂ * (p.ν ^ k)⁻¹ * (p.ε ^ (b / 2) + p.ε) * ‖f‖ := by
      refine hl1.trans ?_
      gcongr
    have hl2' : hpIndNorm p.c (lateAgeSet S) (K0 f) ≤
        C₂ * (p.ν ^ k)⁻¹ * p.ε ^ (b / 2) * ‖f‖ := by
      refine hl2.trans ?_
      gcongr
    have hw' : hpIndNorm p.c (windowAgeSet σ S) (Ke f - K0 f) ≤
        C₃ * (p.ν ^ k)⁻¹ * (p.ε ^ ((2 / 539 : ℝ) - N * (a + b)) + Real.exp (-D / p.ν)) * ‖f‖ := by
      refine hw.trans ?_
      gcongr
    have hsum_f : ‖(Ke - K0) f‖ ≤
        (C₂ * (p.ν ^ k)⁻¹ * p.ε ^ (a / 2) +
          C₃ * (p.ν ^ k)⁻¹ * (p.ε ^ ((2 / 539 : ℝ) - N * (a + b)) + Real.exp (-D / p.ν)) +
          C₂ * (p.ν ^ k)⁻¹ * (p.ε ^ (b / 2) + p.ε) +
          C₂ * (p.ν ^ k)⁻¹ * p.ε ^ (b / 2)) * ‖f‖ := by
      rw [sub_apply]
      linarith
    refine hsum_f.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
    dsimp [B_terms]
    have h1 : 0 ≤ C₂ * (p.ν ^ k)⁻¹ * p.ε ^ (a / 2) := by positivity
    have h2' : 0 ≤ C₂ * (p.ν ^ k)⁻¹ * p.ε := by positivity
    have h3' : 0 ≤ C₂ * (p.ν ^ k)⁻¹ * (p.ε ^ ((2 / 539 : ℝ) - N * (a + b)) + Real.exp (-D / p.ν)) := by
      positivity
    have h4' : 0 ≤ C₃ * (p.ν ^ k)⁻¹ * (p.ε ^ (a / 2) + p.ε ^ (b / 2) + p.ε) := by positivity
    linarith
  have hCeC0 : ‖Ce - C0‖ ≤ C₄ * (p.ν ^ k)⁻¹ * B_terms := by
    have hcol' : ‖Ce - C0‖ ≤ C₄ * (p.ν ^ k)⁻¹ * p.ε := by
      refine hcol.trans ?_
      gcongr
    refine hcol'.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    dsimp [B_terms]
    have : 0 ≤ p.ε ^ (a / 2) + p.ε ^ (b / 2) + p.ε ^ ((2 / 539 : ℝ) - N * (a + b)) +
        Real.exp (-D / p.ν) := by positivity
    linarith
  calc ‖Ke - K0‖ + ‖Ce - C0‖
      ≤ (2 * C₂ + C₃) * (p.ν ^ k)⁻¹ * B_terms + C₄ * (p.ν ^ k)⁻¹ * B_terms :=
        add_le_add hKeK0 hCeC0
    _ = C * (p.ν ^ k)⁻¹ * B_terms := by dsimp [C]; ring

/-! ## 3. Polarized quadratic estimate and family (`Q1`, `Q2`, SP 2503-2518) -/

/-- **`PartII-b:Q1` (`QuadBound`)** (SP 2503-2518): at a fixed slow age `Σ > 0` and growing
eigenpair `(λ, q)`, in the regime and for small `ν`, there is a bilinear map
`B : p.Z →ₗ[ℝ] p.Z →ₗ[ℝ] p.Y` representing the polarized quadratic source of `w + E_εα` (`QuadRel`)
with `‖B z z'‖_Y ≤ C ν^{-k} ‖z‖_Z ‖z'‖_Z`. -/
def QuadBound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∃ B : p.Z →ₗ[ℝ] p.Z →ₗ[ℝ] p.Y, (∀ z z', p.QuadRel z z' (B z z')) ∧
        ∀ z z', ‖B z z'‖ ≤ C * (p.ν ^ k)⁻¹ * ‖z‖ * ‖z'‖

/-- **Conditional assembly of `QuadraticFamily` (`PartII-b:Q2`, SP 2503-2518)** from
`QuadBound` (`Q1`) via `LinearMap.mkContinuous₂`. -/
theorem quadraticFamily_of_core (hQ1 : QuadBound) : QuadraticFamily := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, k, ν₀, hC, hν₀, H⟩ := hQ1 Sig lam q hSig hq dm dp hdm
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hν hSg hmode
  obtain ⟨B, hrel, hbd⟩ := H p d hreg hν hSg hmode
  have hpos : 0 ≤ C * (p.ν ^ k)⁻¹ := by
    have := p.ν_pos
    positivity
  refine ⟨B.mkContinuous₂ (C * (p.ν ^ k)⁻¹) hbd, ?_, ?_⟩
  · intro z z'
    simpa only [LinearMap.mkContinuous₂_apply] using hrel z z'
  · exact LinearMap.mkContinuous₂_norm_le B hpos hbd

/-! ## 4. Strong first derivative, all spatial orders, and strong regularity (`S1`, `S2`, `S3`, SP 2525-2562) -/

/-- `IsIteratedPhaseGrad P q k u g`: `g α` is the iterated distributional spatial derivative
`∂_{α(0)} ⋯ ∂_{α(k-1)} u` in `Y_q` for every multi-index `α : Fin k → Fin 3`. -/
def IsIteratedPhaseGrad (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∀ (k : ℕ), Yq P q → ((Fin k → Fin 3) → Yq P q) → Prop
  | 0, u, g => g Fin.elim0 = u
  | k + 1, u, g =>
      ∃ g₀ : (Fin k → Fin 3) → Yq P q, IsIteratedPhaseGrad P q k u g₀ ∧
        ∀ (α : Fin k → Fin 3) (j : Fin 3),
          HasPhaseOp (fun Φ => -dy j Φ) (g₀ α) (g (Fin.snoc α j))

/-- **`PartII-b:S1` (`StrongFirstDerivative`)** (SP 2525-2541, display `short-bg:strong` at 2538):
at fixed slow data `(Σ, λ, q)` and `0 < m` with `2m < 3d₋/11`, for any solution `z = (w, A)` of
`ProjectedEquation p z` in the contraction ball of radius `C₁ ν^{-k₁} e^{m/ν} ε^{3/11}`, the
distributional spatial derivatives `∂_j w` lie in the maximal graph `D_p = B0411.D p.period p.ν q0E`
at shift zero, and `sup_τ ‖w(τ)‖_p + ‖w‖_{W^{1,∞}} + ‖E_εα‖_{W^{1,∞}} ≤ C₂ ν^{-k₂} e^{m/ν} ε^{3/11}`. -/
def StrongFirstDerivative : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ (C₂ : ℝ) (k₂ : ℕ) (ν₀ : ℝ), 0 < C₂ ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∃ g : Fin 3 → B0411.D p.period p.ν q0E,
        ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g j : Yq p.period q0E)) ∧
      (∀ τ y, ‖p.corr z τ y‖ ≤ C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) ∧
        ‖fderiv ℝ (p.corr z τ) y‖ ≤ C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) ∧
      (∀ τ, eLpNorm (p.corr z τ) (ENNReal.ofReal bgp) volume ≤
        ENNReal.ofReal (C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ))) ∧
      (∀ τ y, ‖∑ i : Fin 2, p.coord z i • p.inlet i τ y‖ ≤ C₂ * (p.ν ^ k₂)⁻¹ *
          Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) ∧
        ‖fderiv ℝ (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ y') y‖ ≤ C₂ * (p.ν ^ k₂)⁻¹ *
          Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ))

/-- **`PartII-b:S2` (`StrongAllOrders`)** (SP 2541-2562): at fixed slow data `(Σ, λ, q)` and
`0 < m` with `2m < 3d₋/11`, for any solution `z` of `ProjectedEquation p z` in the contraction
ball, by induction on the spatial derivative order `k`:
* all order-`k` distributional spatial derivatives `D^α w` lie in the maximal graph
  `D_p = B0411.D p.period p.ν q0E`;
* every phase slice `bgField p z τ` is `C^k` on `ℝ³`, with `D^k(p.corr z τ)` uniformly bounded on
  `ℝ × ℝ³` and `D^k(bgField p z τ)` uniformly bounded in `L⁴(ℝ³)` (`U ∈ C_per W^{k,4} ∩ ...`);
* the raw lift `p.raw` and inlet columns `p.inlet i` are smooth bounded solenoidal fields. -/
def StrongAllOrders : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) ∧
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ, ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) ∧
      (IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) ∧
      (∀ i : Fin 2, IsBoundedBackground (p.inlet i) ∧ ∀ τ, IsSolenoidal (p.inlet i τ))

/-- Helper for `PartII-b:S3` (`StrongRegularity`): periodicity, solenoidality, and
axisymmetric-no-swirl symmetry of `bgField p z` at every phase, from `p.period ≤ 1` and the
piece regularity of `p.raw` and `p.inlet`. -/
theorem bgField_periodic_solenoidal_symmetric (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (hRaw : IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ))
    (hInlet : ∀ i : Fin 2, IsBoundedBackground (p.inlet i) ∧ ∀ τ, IsSolenoidal (p.inlet i τ)) :
    Function.Periodic (bgField p z) p.period ∧
      (∀ τ, IsSolenoidal (bgField p z τ)) ∧
      (∀ τ, IsAxisymmetricNoSwirl (bgField p z τ)) := by
  have hraw_piece : IsBackgroundPiece p.period p.raw :=
    isBackgroundPiece_raw p.ε_pos.ne' p.train (fun τ y hy => p.raw_eq_off_axis τ y hy) hRaw.1 hRaw.2
  have hinlet_piece : ∀ i : Fin 2, IsBackgroundPiece p.period (p.inlet i) := fun i =>
    isBackgroundPiece_of_lift p.R_pos.ne' p.period_eq
      (fun s _ ξ η => p.inletProfile_periodic i s ξ η) (fun _ _ _ => rfl) (hInlet i).1 (hInlet i).2
  have hsum_piece : IsBackgroundPiece p.period (∑ i : Fin 2, p.coord z i • p.inlet i) :=
    IsBackgroundPiece.lin2 hinlet_piece (p.coord z)
  have hraw_inlet : IsBackgroundPiece p.period (p.raw + ∑ i : Fin 2, p.coord z i • p.inlet i) :=
    hraw_piece.add hsum_piece
  have hbg_eq : bgField p z =
      (p.raw + ∑ i : Fin 2, p.coord z i • p.inlet i) + p.corr z := by
    ext τ y i
    simp [bgField]
  rw [hbg_eq]
  refine ⟨hraw_inlet.periodic.add (p.corr_periodic z), ?_, ?_⟩
  · intro τ
    exact isSolenoidal_add (hraw_inlet.solenoidal τ) (p.corr_isSolenoidal hP1 z τ)
  · intro τ
    exact isAxisymmetricNoSwirl_add' (hraw_inlet.symmetric τ) (p.corr_isAxisymmetricNoSwirl hP1 z τ)

end UnforcedLeray.Short.IIb

end
