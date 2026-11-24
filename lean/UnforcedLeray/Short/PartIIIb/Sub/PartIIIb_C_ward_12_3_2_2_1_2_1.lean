import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.RingLiftPtJet

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2/1` (decomposition): `RawResidualD2AxialTail`

Source of record:
`the November 2 reference manuscript`,
lines 1255-1304, 1310-1325, 2548-2551 at `k = 2`: in the near-axis cylinder `0 < ϱ(y) ≤ R₀`, the
similarity ring residual `F_R = rawResidualC p` is represented off the axis by the chart lift
`Axi.age p.R y • Axi.Nv p.R (resChartProfile p) τ y` (`ringResidual_eq_age_smul_Nv`), where the
meridional residual profile `r = (r_r, r_z) = resChartProfile p` expands at every positive age `s > 0`
as the exact polynomial in `ε = R⁻¹` (`B0188.train_residual_polynomial`):
`r_r = ε A₁ + ε² B₁`, `r_z = ε A₂ + ε² B₂ + ε³ B₃`.

This file proves:
1. **Exact polynomial expansion of `resChartProfile p` (`resChartProfile_eq_poly`)** and the
   weighted late bounds on `r_r, r_z` (`resChartProfile_late_radial_wtd`,
   `resChartProfile_late_axial_wtd`);
2. **Normalized weight identity (`trans_sq_div_age_eq_sq`, `inv_one_add_trans_sq_div_age_le`)**:
   off the axis, `(Axi.trans R y)² / Axi.age R y = y₃²` and
   `(1 + (Axi.trans R y)² / Axi.age R y)⁻¹ ≤ 2 (1 + |y₃|)^{-2}`;
3. **Off-axis second-derivative bridge (`norm_dy2_rawResidualC_le_iteratedFDeriv`)**: for every
   `y` with `ϱ(y) ≠ 0` and `j, l : Fin 3`,
   `‖∂_j ∂_l (rawResidualC p)(τ, y)‖ ≤ ‖iteratedFDeriv ℝ 2 (fun w => s(w) • N_v (resChartProfile p) τ w) y‖`;
4. **Pointwise Cartesian second-jet bound for `s • N_v b` at every off-axis point
   (`AxialTailSub.age_smul_nv_pt_jet2`)**: from `ringLiftPtJet` and `age_jet_le_two`, there is a
   universal exponent `K : ℕ` such that for any `R ≥ 2` and smooth chart profile `b`,
   `‖iteratedFDeriv ℝ 2 (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤ C (1 + s)^K (1 + |η|)^2 ∑_{l ≤ 2} ‖D^l b(chart y)‖`;
5. **Complete reduction (`resNearAxisJet2_of`, `rawResidualD2AxialTail_of_early_and_late`)**:
   combines the bounded-age (`0 < s ≤ 1`) weighted second-jet bound `ResProfileEarlyJet2` with the
   late-age (`s ≥ 1`) finite-order heat-expansion split `ResProfileLateHeatDecomp2` at order
   `N = K + 1` to prove `ResNearAxisJet2` and `RawResidualD2AxialTail`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Short.IIb (trainStream trainPressure rawResidualC)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FarDecaySub

/-- **Near-axis normalized-weight second-jet bound for the lifted residual**
(`the November 2 reference manuscript`, lines 1270-1304, 1310-1325, 2548-2551): on `0 < ϱ(y) ≤ R₀` with
`|y₃| > Z₀`, the second spatial jet of `F_R = s • N_v (resChartProfile p)` weighted by the
normalized similarity factor `1 + η² / s` is uniformly bounded. -/
def ResNearAxisJet2 : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ R0 : ℝ, 0 < R0 →
      ∃ C Z0 : ℝ, 0 ≤ Z0 ∧ ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
        Axi.ϱ y ≠ 0 → Axi.ϱ y ≤ R0 → Z0 < |y 2| →
        (1 + (Axi.trans p.R y) ^ 2 / Axi.age p.R y) *
          ‖iteratedFDeriv ℝ 2
            (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ ≤ C

/-- **(Leaf 1) Early-age (`0 < s ≤ 1`) weighted second-jet bound of the chart residual profile**
(`the November 2 reference manuscript`, lines 1294-1304, 2542-2551: at bounded age `0 < s ≤ 1`, the
residual coefficients `A₁, A₂, B₁, B₂, B₃` and their chart jets through order `2` have rapid
transverse decay in `η`, giving `(1 + |η|)⁴ ‖D^l (resChartProfile p)(m)‖ ≤ C` for `l ≤ 2`). -/
def ResProfileEarlyJet2 : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
      ∃ C : ℝ, ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ 1 → ∀ l ≤ 2,
        (1 + |m.2.2|) ^ 4 * ‖iteratedFDeriv ℝ l (resChartProfile p) m‖ ≤ C

/-- **(Leaf 2) Late-age (`s ≥ 1`) finite-order heat decomposition of the lifted residual**
(`the November 2 reference manuscript`, lines 1267-1285, 1310-1325, 2548-2551: on `ϱ ≤ R`, taking the
all-age heat expansion to a sufficiently high finite order `N`, the even radial powers of the heat
terms extend smoothly through the axis as `F_heat` with `(1 + y₃²) ‖D² F_heat(y)‖ ≤ C_heat` on
`ϱ(y) ≤ R`, while the remainder chart profile `r_rem` has normalized-weight second-jet age decay
`(1 + η² / s)² ‖D^l r_rem(m)‖ ≤ C_rem s^{-N}` for all `s ≥ 1` and `l ≤ 2`). -/
def ResProfileLateHeatDecomp2 : Prop :=
  ∀ N : ℕ, ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
      ∃ (F_heat : UnforcedLeray.Space → UnforcedLeray.Space)
        (r_rem : ℝ × (ℝ × ℝ) → Axi.Merid) (C_heat C_rem : ℝ),
        ContDiff ℝ ∞ F_heat ∧
        ContDiffOn ℝ ∞ r_rem {m : ℝ × (ℝ × ℝ) | 0 < m.1} ∧
        (∀ (τ : ℝ) (z : UnforcedLeray.Space), z ∉ Axi.axis →
          Axi.age p.R z • Axi.Nv p.R (resChartProfile p) τ z =
            F_heat z + Axi.age p.R z • Axi.Nv p.R r_rem τ z) ∧
        (∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ p.R →
          (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 F_heat y‖ ≤ C_heat) ∧
        (∀ m : ℝ × (ℝ × ℝ), 1 ≤ m.1 → ∀ l ≤ 2,
          (1 + m.2.2 ^ 2 / m.1) ^ 2 * ‖iteratedFDeriv ℝ l r_rem m‖ ≤
            C_rem * m.1 ^ (-(N : ℝ)))

/-- For any BUC train, the stream `p.train.ψ` satisfies `B0188.TrainStreamC3`. -/
theorem trainStreamC3_of_isBUCTrain (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train) :
    TrainStreamC3 p.train.ψ := by
  have hψ : ContDiffOn ℝ ∞ (trainStream p) ageDomain :=
    UnforcedLeray.Short.IIb.trainStreamSmoothBUC_of
      UnforcedLeray.Short.PartI.trainStreamSmooth p.ν p.c p.ν_pos p.c_pos p.train htr
  exact hψ.of_le (by norm_num)

/-- **Exact polynomial expansion of `resChartProfile p` at every positive age** (`B0188`,
`the November 2 reference manuscript`, lines 1255-1258): for `m = (s, (ξ, η))` with `0 < s`,
`r_r = ε A₁ + ε² B₁` and `r_z = ε A₂ + ε² B₂ + ε³ B₃` where `ε = ringEps p.R = p.R⁻¹`. -/
theorem resChartProfile_eq_poly (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    {m : ℝ × (ℝ × ℝ)} (hm : 0 < m.1) :
    resChartProfile p m 0 =
        ringEps p.R * coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m) +
          ringEps p.R ^ 2 * coeffB₁ p.ν (trainStream p) (chartSwap m) ∧
      resChartProfile p m 1 =
        ringEps p.R * coeffA₂ p.ν (trainStream p) (chartSwap m) +
          ringEps p.R ^ 2 * coeffB₂ p.ν (trainStream p) (chartSwap m) +
          ringEps p.R ^ 3 * coeffB₃ p.ν (trainStream p) (chartSwap m) := by
  have hψ3 : TrainStreamC3 p.train.ψ := trainStreamC3_of_isBUCTrain p htr
  have hx : 0 < (chartSwap m).2.2 := hm
  exact train_residual_polynomial p.R p.train.isTrain hψ3 hx

/-- For `2 ≤ R`, the inverse radius `ringEps R = R⁻¹` satisfies `0 ≤ ringEps R` and
`ringEps R ≤ 1`. -/
theorem ringEps_nonneg_and_le_one {R : ℝ} (hR : 2 ≤ R) :
    0 ≤ ringEps R ∧ ringEps R ≤ 1 := by
  unfold ringEps
  refine ⟨by positivity, ?_⟩
  exact inv_le_one_of_one_le₀ (by linarith)

/-- From the `A₁, B₁` late weighted bounds of `PartIIa.RingLateTable` (`StatementsRing.lean`,
line 148), the radial chart residual `resChartProfile p m 0` satisfies
`(1 + η² / s)^k |r_r(m)| ≤ 2 B s^{-2}` for all `s ≥ 1`. -/
theorem resChartProfile_late_radial_wtd (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train) (hR : 2 ≤ p.R)
    {k : ℕ} {B : ℝ}
    (hA1 : WtdBound k (coeffA₁ p.ν (trainStream p) (trainPressure p)) 2 B)
    (hB1 : WtdBound k (coeffB₁ p.ν (trainStream p)) 2 B)
    {m : ℝ × (ℝ × ℝ)} (hm : 1 ≤ m.1) :
    (1 + m.2.2 ^ 2 / m.1) ^ k * |resChartProfile p m 0| ≤ 2 * B * m.1 ^ (-2 : ℝ) := by
  have hm0 : 0 < m.1 := lt_of_lt_of_le one_pos hm
  rw [(resChartProfile_eq_poly p htr hm0).1]
  obtain ⟨hε0, hε1⟩ := ringEps_nonneg_and_le_one hR
  have hε2 : ringEps p.R ^ 2 ≤ 1 := by nlinarith
  have hW0 : 0 ≤ (1 + m.2.2 ^ 2 / m.1) ^ k := by positivity
  have hbA := hA1 (chartSwap m) hm
  have hbB := hB1 (chartSwap m) hm
  change (1 + m.2.2 ^ 2 / m.1) ^ k * |coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m)| ≤
    B * m.1 ^ (-2 : ℝ) at hbA
  change (1 + m.2.2 ^ 2 / m.1) ^ k * |coeffB₁ p.ν (trainStream p) (chartSwap m)| ≤
    B * m.1 ^ (-2 : ℝ) at hbB
  have htri : |ringEps p.R * coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m) +
      ringEps p.R ^ 2 * coeffB₁ p.ν (trainStream p) (chartSwap m)| ≤
      |coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m)| +
        |coeffB₁ p.ν (trainStream p) (chartSwap m)| := by
    calc |ringEps p.R * coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m) +
          ringEps p.R ^ 2 * coeffB₁ p.ν (trainStream p) (chartSwap m)|
        ≤ |ringEps p.R * coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m)| +
            |ringEps p.R ^ 2 * coeffB₁ p.ν (trainStream p) (chartSwap m)| := abs_add_le _ _
      _ = ringEps p.R * |coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m)| +
            ringEps p.R ^ 2 * |coeffB₁ p.ν (trainStream p) (chartSwap m)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hε0, abs_of_nonneg (sq_nonneg (ringEps p.R))]
      _ ≤ 1 * |coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m)| +
            1 * |coeffB₁ p.ν (trainStream p) (chartSwap m)| :=
          add_le_add (mul_le_mul_of_nonneg_right hε1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hε2 (abs_nonneg _))
      _ = |coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m)| +
            |coeffB₁ p.ν (trainStream p) (chartSwap m)| := by ring
  calc (1 + m.2.2 ^ 2 / m.1) ^ k *
        |ringEps p.R * coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m) +
          ringEps p.R ^ 2 * coeffB₁ p.ν (trainStream p) (chartSwap m)|
      ≤ (1 + m.2.2 ^ 2 / m.1) ^ k *
          (|coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m)| +
            |coeffB₁ p.ν (trainStream p) (chartSwap m)|) :=
        mul_le_mul_of_nonneg_left htri hW0
    _ = (1 + m.2.2 ^ 2 / m.1) ^ k *
          |coeffA₁ p.ν (trainStream p) (trainPressure p) (chartSwap m)| +
        (1 + m.2.2 ^ 2 / m.1) ^ k *
          |coeffB₁ p.ν (trainStream p) (chartSwap m)| := by ring
    _ ≤ B * m.1 ^ (-2 : ℝ) + B * m.1 ^ (-2 : ℝ) := add_le_add hbA hbB
    _ = 2 * B * m.1 ^ (-2 : ℝ) := by ring

/-- From the `A₂, B₂, B₃` late bounds of `PartIIa.RingLateTable` (`StatementsRing.lean`,
lines 154-162), the axial chart residual `resChartProfile p m 1` satisfies
`(1 + η² / s)^k |r_z(m)| ≤ B e^{-κ ν s / c²} + 2 B s^{-3/2}` for all `s ≥ 1`. -/
theorem resChartProfile_late_axial_wtd (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train) (hR : 2 ≤ p.R)
    {k : ℕ} {κ B : ℝ}
    (hA2 : ExpBound κ p.ν p.c k (coeffA₂ p.ν (trainStream p)) B)
    (hB2 : WtdBound k (coeffB₂ p.ν (trainStream p)) (3 / 2) B)
    (hB3 : WtdBound k (coeffB₃ p.ν (trainStream p)) (3 / 2) B)
    {m : ℝ × (ℝ × ℝ)} (hm : 1 ≤ m.1) :
    (1 + m.2.2 ^ 2 / m.1) ^ k * |resChartProfile p m 1| ≤
      B * Real.exp (-(κ * p.ν * m.1 / p.c ^ 2)) + 2 * B * m.1 ^ (-(3 / 2 : ℝ)) := by
  have hm0 : 0 < m.1 := lt_of_lt_of_le one_pos hm
  rw [(resChartProfile_eq_poly p htr hm0).2]
  obtain ⟨hε0, hε1⟩ := ringEps_nonneg_and_le_one hR
  have hε2 : ringEps p.R ^ 2 ≤ 1 := by nlinarith
  have hε3 : ringEps p.R ^ 3 ≤ 1 := by
    calc ringEps p.R ^ 3 = ringEps p.R ^ 2 * ringEps p.R := by ring
      _ ≤ 1 * 1 := mul_le_mul hε2 hε1 hε0 zero_le_one
      _ = 1 := mul_one 1
  have hW0 : 0 ≤ (1 + m.2.2 ^ 2 / m.1) ^ k := by positivity
  have hbA := hA2 (chartSwap m) hm
  have hbB2 := hB2 (chartSwap m) hm
  have hbB3 := hB3 (chartSwap m) hm
  change (1 + m.2.2 ^ 2 / m.1) ^ k * |coeffA₂ p.ν (trainStream p) (chartSwap m)| ≤
    B * Real.exp (-(κ * p.ν * m.1 / p.c ^ 2)) at hbA
  change (1 + m.2.2 ^ 2 / m.1) ^ k * |coeffB₂ p.ν (trainStream p) (chartSwap m)| ≤
    B * m.1 ^ (-(3 / 2 : ℝ)) at hbB2
  change (1 + m.2.2 ^ 2 / m.1) ^ k * |coeffB₃ p.ν (trainStream p) (chartSwap m)| ≤
    B * m.1 ^ (-(3 / 2 : ℝ)) at hbB3
  have htri : |ringEps p.R * coeffA₂ p.ν (trainStream p) (chartSwap m) +
      ringEps p.R ^ 2 * coeffB₂ p.ν (trainStream p) (chartSwap m) +
      ringEps p.R ^ 3 * coeffB₃ p.ν (trainStream p) (chartSwap m)| ≤
      |coeffA₂ p.ν (trainStream p) (chartSwap m)| +
        |coeffB₂ p.ν (trainStream p) (chartSwap m)| +
        |coeffB₃ p.ν (trainStream p) (chartSwap m)| := by
    calc |ringEps p.R * coeffA₂ p.ν (trainStream p) (chartSwap m) +
          ringEps p.R ^ 2 * coeffB₂ p.ν (trainStream p) (chartSwap m) +
          ringEps p.R ^ 3 * coeffB₃ p.ν (trainStream p) (chartSwap m)|
        ≤ |ringEps p.R * coeffA₂ p.ν (trainStream p) (chartSwap m) +
            ringEps p.R ^ 2 * coeffB₂ p.ν (trainStream p) (chartSwap m)| +
            |ringEps p.R ^ 3 * coeffB₃ p.ν (trainStream p) (chartSwap m)| := abs_add_le _ _
      _ ≤ |ringEps p.R * coeffA₂ p.ν (trainStream p) (chartSwap m)| +
            |ringEps p.R ^ 2 * coeffB₂ p.ν (trainStream p) (chartSwap m)| +
            |ringEps p.R ^ 3 * coeffB₃ p.ν (trainStream p) (chartSwap m)| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ = ringEps p.R * |coeffA₂ p.ν (trainStream p) (chartSwap m)| +
            ringEps p.R ^ 2 * |coeffB₂ p.ν (trainStream p) (chartSwap m)| +
            ringEps p.R ^ 3 * |coeffB₃ p.ν (trainStream p) (chartSwap m)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hε0, abs_of_nonneg (sq_nonneg (ringEps p.R)),
            abs_of_nonneg (pow_nonneg hε0 3)]
      _ ≤ 1 * |coeffA₂ p.ν (trainStream p) (chartSwap m)| +
            1 * |coeffB₂ p.ν (trainStream p) (chartSwap m)| +
            1 * |coeffB₃ p.ν (trainStream p) (chartSwap m)| :=
          add_le_add
            (add_le_add (mul_le_mul_of_nonneg_right hε1 (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hε2 (abs_nonneg _)))
            (mul_le_mul_of_nonneg_right hε3 (abs_nonneg _))
      _ = |coeffA₂ p.ν (trainStream p) (chartSwap m)| +
            |coeffB₂ p.ν (trainStream p) (chartSwap m)| +
            |coeffB₃ p.ν (trainStream p) (chartSwap m)| := by ring
  calc (1 + m.2.2 ^ 2 / m.1) ^ k *
        |ringEps p.R * coeffA₂ p.ν (trainStream p) (chartSwap m) +
          ringEps p.R ^ 2 * coeffB₂ p.ν (trainStream p) (chartSwap m) +
          ringEps p.R ^ 3 * coeffB₃ p.ν (trainStream p) (chartSwap m)|
      ≤ (1 + m.2.2 ^ 2 / m.1) ^ k *
          (|coeffA₂ p.ν (trainStream p) (chartSwap m)| +
            |coeffB₂ p.ν (trainStream p) (chartSwap m)| +
            |coeffB₃ p.ν (trainStream p) (chartSwap m)|) :=
        mul_le_mul_of_nonneg_left htri hW0
    _ = (1 + m.2.2 ^ 2 / m.1) ^ k * |coeffA₂ p.ν (trainStream p) (chartSwap m)| +
        (1 + m.2.2 ^ 2 / m.1) ^ k * |coeffB₂ p.ν (trainStream p) (chartSwap m)| +
        (1 + m.2.2 ^ 2 / m.1) ^ k * |coeffB₃ p.ν (trainStream p) (chartSwap m)| := by ring
    _ ≤ B * Real.exp (-(κ * p.ν * m.1 / p.c ^ 2)) +
          B * m.1 ^ (-(3 / 2 : ℝ)) + B * m.1 ^ (-(3 / 2 : ℝ)) :=
        add_le_add (add_le_add hbA hbB2) hbB3
    _ = B * Real.exp (-(κ * p.ν * m.1 / p.c ^ 2)) + 2 * B * m.1 ^ (-(3 / 2 : ℝ)) := by ring

/-- Off the axis, the normalized transverse ratio `η² / s = (Axi.trans R y)² / Axi.age R y`
equals `y₃²`. -/
theorem trans_sq_div_age_eq_sq {R : ℝ} (hR : R ≠ 0) {y : UnforcedLeray.Space}
    (hy : Axi.ϱ y ≠ 0) :
    (Axi.trans R y) ^ 2 / Axi.age R y = y 2 ^ 2 := by
  unfold Axi.trans Axi.age
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have hρ2 : Axi.ϱ y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  field_simp

/-- Elementary comparison `(1 + |t|)² ≤ 2 (1 + t²)` for all `t : ℝ`. -/
theorem sq_one_add_abs_le_two_mul_one_add_sq (t : ℝ) :
    (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
  have h1 : 0 ≤ (1 - |t|) ^ 2 := sq_nonneg (1 - |t|)
  have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith

/-- For all `t : ℝ`, `(1 + t²)⁻¹ ≤ 2 (1 + |t|)^{-2}`. -/
theorem one_add_sq_inv_le_two_rpow_neg_two (t : ℝ) :
    (1 + t ^ 2)⁻¹ ≤ 2 * (1 + |t|) ^ (-2 : ℝ) := by
  have h1_pos : 0 < 1 + |t| := by positivity
  have hsq_pos : 0 < (1 + |t|) ^ 2 := pow_pos h1_pos 2
  have h1t2_pos : 0 < 1 + t ^ 2 := by positivity
  have hrpow : (1 + |t|) ^ (-2 : ℝ) = ((1 + |t|) ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1_pos.le, Real.rpow_natCast]
  rw [hrpow]
  have hle := sq_one_add_abs_le_two_mul_one_add_sq t
  rw [inv_le_iff_one_le_mul₀' h1t2_pos]
  have hdiv : 1 ≤ 2 * (1 + t ^ 2) / (1 + |t|) ^ 2 := (one_le_div hsq_pos).2 hle
  linarith [div_eq_mul_inv (2 * (1 + t ^ 2)) ((1 + |t|) ^ 2)]

/-- Off the axis, `(1 + η² / s)⁻¹ ≤ 2 (1 + |y₃|)^{-2}`. -/
theorem inv_one_add_trans_sq_div_age_le {R : ℝ} (hR : R ≠ 0) {y : UnforcedLeray.Space}
    (hy : Axi.ϱ y ≠ 0) :
    (1 + (Axi.trans R y) ^ 2 / Axi.age R y)⁻¹ ≤ 2 * (1 + |y 2|) ^ (-2 : ℝ) := by
  rw [trans_sq_div_age_eq_sq hR hy]
  exact one_add_sq_inv_le_two_rpow_neg_two (y 2)

/-- Off the axis, every second partial `∂_j ∂_l (rawResidualC p)(τ, y)` is bounded in norm by the
second spatial Fréchet derivative of `w ↦ Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w`. -/
theorem norm_dy2_rawResidualC_le_iteratedFDeriv (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train) (hR : 2 ≤ p.R)
    (j l : Fin 3) (τ : ℝ) {y : UnforcedLeray.Space} (hy : Axi.ϱ y ≠ 0) :
    ‖dy j (dy l (rawResidualC p)) (τ, y)‖ ≤
      ‖iteratedFDeriv ℝ 2
        (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ := by
  have hyax : y ∉ Axi.axis := mt (Axi.mem_axis_iff y).mp hy
  have hsm := resChartProfile_contDiffOn p htr
  have hU : IsOpen {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    Axi.isOpen_compl_axis.preimage continuous_snd
  have hRpos : 0 < p.R := by linarith
  have hGsm : ContDiffOn ℝ ∞ (rawResidualC p)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    (age_smul_Nv_joint_contDiffOn p.R hRpos (resChartProfile p) hsm).congr
      (fun z hz => rawResidualC_eq_off_axis p htr hR z hz)
  have hsb := (sliceBridge CVec3 (rawResidualC p)
    {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} hU hGsm (τ, y) hyax j l j).2.1
  have hslice_eq : iteratedFDeriv ℝ 2 (fun w => rawResidualC p (τ, w)) y =
      iteratedFDeriv ℝ 2
        (fun w => efarRealCLI (Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w)) y := by
    have hev : (fun w => rawResidualC p (τ, w)) =ᶠ[𝓝 y]
        (fun w => efarRealCLI (Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w)) :=
      Filter.eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyax)
        (fun w hw => rawResidualC_eq_off_axis p htr hR (τ, w) hw)
    exact (hev.iteratedFDeriv ℝ 2).eq_of_nhds
  have hrealS : ContDiffOn ℝ ∞
      (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) Axi.axisᶜ := by
    have hAgeS : ContDiffOn ℝ ∞ (Axi.age p.R) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
        (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
    have hgS : ContDiffOn ℝ ∞ (fun z => resChartProfile p (Axi.chart p.R τ z)) Axi.axisᶜ :=
      hsm.comp (clf_chart_contDiffOn p.R τ hRpos) (clf_chart_mapsTo p.R τ hRpos)
    have hNvS : ContDiffOn ℝ ∞ (Axi.Nv p.R (resChartProfile p) τ) Axi.axisᶜ := by
      have hEq : Axi.Nv p.R (resChartProfile p) τ =
          fun z => liftFactor p.R z (resChartProfile p (Axi.chart p.R τ z)) :=
        funext fun z => Nv_eq_liftFactor p.R (resChartProfile p) τ z
      rw [hEq]
      exact (clf_lift_contDiffOn p.R hRpos).clm_apply hgS
    exact hAgeS.smul hNvS
  have hiso := efar_realC_norm
    (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) hrealS hyax 2
  calc ‖dy j (dy l (rawResidualC p)) (τ, y)‖
      ≤ ‖iteratedFDeriv ℝ 2 (fun w => rawResidualC p (τ, w)) y‖ := hsb
    _ = ‖iteratedFDeriv ℝ 2
          (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ := by
        rw [hslice_eq, hiso]

namespace AxialTailSub

/-- Off the axis, for `1 ≤ R`, `(Axi.ϱ y)⁻¹ ≤ 1 + Axi.age R y`. -/
theorem inv_ϱ_le_one_add_age {R : ℝ} (hR : 1 ≤ R) {y : UnforcedLeray.Space}
    (hy : y ∉ Axi.axis) :
    (Axi.ϱ y)⁻¹ ≤ 1 + Axi.age R y := by
  have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hρ2 : 0 < Axi.ϱ y ^ 2 := pow_pos hρ 2
  unfold Axi.age
  rw [inv_eq_one_div, div_le_iff₀ hρ]
  have h1 : (1 + R ^ 2 / Axi.ϱ y ^ 2) * Axi.ϱ y =
      (Axi.ϱ y ^ 2 + R ^ 2) / Axi.ϱ y := by
    field_simp
  rw [h1, le_div_iff₀ hρ]
  nlinarith [sq_nonneg (Axi.ϱ y - 1 / 2)]

/-- Off the axis, for `1 ≤ R` and `i ≤ 2`, `Axi.ϱ y ^ (-(2 + (i : ℝ))) ≤ (1 + Axi.age R y) ^ 4`. -/
theorem ϱ_rpow_neg_two_add_le_age {R : ℝ} (hR : 1 ≤ R) {y : UnforcedLeray.Space}
    (hy : y ∉ Axi.axis) {i : ℕ} (hi : i ≤ 2) :
    Axi.ϱ y ^ (-(2 + (i : ℝ))) ≤ (1 + Axi.age R y) ^ 4 := by
  have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hR0 : R ≠ 0 := by linarith
  have hs : 0 < Axi.age R y := Axi.age_pos hR0 hy
  have h1s : 1 ≤ 1 + Axi.age R y := by linarith
  have hinv0 : 0 ≤ (Axi.ϱ y)⁻¹ := inv_nonneg.2 hρ.le
  have hinv := inv_ϱ_le_one_add_age hR hy
  have hexp : -(2 + (i : ℝ)) = -(((2 + i : ℕ) : ℝ)) := by push_cast; ring
  rw [hexp, Real.rpow_neg hρ.le, Real.rpow_natCast, ← inv_pow]
  calc ((Axi.ϱ y)⁻¹) ^ (2 + i)
      ≤ (1 + Axi.age R y) ^ (2 + i) := pow_le_pow_left₀ hinv0 hinv _
    _ ≤ (1 + Axi.age R y) ^ 4 := pow_le_pow_right₀ h1s (by omega)

/-- The domains `{m : ℝ × (ℝ × ℝ) | 0 < m.1}` and `Ioi 0 ×ˢ univ` coincide. -/
theorem setOf_fst_pos_eq_prod :
    {m : ℝ × (ℝ × ℝ) | 0 < m.1} = Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
  ext ⟨s, q, η⟩
  simp

/-- Pointwise order-2 spatial jet bound for `w ↦ Axi.age R w • Axi.Nv R b τ w` at every off-axis
point `y ∉ Axi.axis`, with a universal exponent `K : ℕ`. -/
theorem age_smul_nv_pt_jet2 :
    ∃ K : ℕ, ∀ (R : ℝ), 2 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : ℝ × (ℝ × ℝ) → Axi.Merid), ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1} →
        ∀ (τ : ℝ) (y : UnforcedLeray.Space), y ∉ Axi.axis →
          ContDiffOn ℝ ∞ (fun w => Axi.age R w • Axi.Nv R b τ w) Axi.axisᶜ ∧
          ‖iteratedFDeriv ℝ 2 (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤
            C * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ 2 *
              ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
  obtain ⟨C0, k0, hC0, H0⟩ := ringLiftPtJet 0
  obtain ⟨C1, k1, hC1, H1⟩ := ringLiftPtJet 1
  obtain ⟨C2, k2, hC2, H2⟩ := ringLiftPtJet 2
  set K_nv : ℕ := k0 + k1 + k2
  set C_nv : ℝ := C0 + C1 + C2
  have hCnv0 : 0 ≤ C_nv := by positivity
  refine ⟨K_nv + 4, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  obtain ⟨Ca, hCa0, hCa⟩ := age_jet_le_two R hRpos
  refine ⟨6 * Ca * C_nv, by positivity, fun b hb τ y hyax => ?_⟩
  have hb' : ContDiffOn ℝ ∞ b (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    rwa [← setOf_fst_pos_eq_prod]
  have hAgeS : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
      (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
  have hNvS : ContDiffOn ℝ ∞ (Axi.Nv R b τ) Axi.axisᶜ := (H0 R τ b hR1 hb').1
  refine ⟨hAgeS.smul hNvS, ?_⟩
  have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
  have hs : 0 < Axi.age R y := Axi.age_pos hRpos.ne' hyax
  have h1s : 1 ≤ 1 + Axi.age R y := by linarith
  have h1t : 1 ≤ 1 + |Axi.trans R y| := by linarith [abs_nonneg (Axi.trans R y)]
  have hS0 : 0 ≤ ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hNv_le : ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤
        C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ 2 *
          ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
    intro j hj
    have hsub : ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤
        ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by omega)) (fun _ _ _ => norm_nonneg _)
    have hsumj0 : 0 ≤ ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have ht_le : (1 + |Axi.trans R y|) ^ j ≤ (1 + |Axi.trans R y|) ^ 2 :=
      pow_le_pow_right₀ h1t hj
    interval_cases j
    · have hj0 := (H0 R τ b hR1 hb').2 y hyax
      have hk : (1 + Axi.age R y) ^ k0 ≤ (1 + Axi.age R y) ^ K_nv :=
        pow_le_pow_right₀ h1s (by omega)
      have hC : C0 ≤ C_nv := by unfold C_nv; linarith
      have hfac : C0 * (1 + Axi.age R y) ^ k0 * (1 + |Axi.trans R y|) ^ 0 ≤
          C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ 2 :=
        mul_le_mul (mul_le_mul hC hk (by positivity) hCnv0) ht_le (by positivity) (by positivity)
      exact hj0.trans (mul_le_mul hfac hsub hsumj0 (by positivity))
    · have hj1 := (H1 R τ b hR1 hb').2 y hyax
      have hk : (1 + Axi.age R y) ^ k1 ≤ (1 + Axi.age R y) ^ K_nv :=
        pow_le_pow_right₀ h1s (by omega)
      have hC : C1 ≤ C_nv := by unfold C_nv; linarith
      have hfac : C1 * (1 + Axi.age R y) ^ k1 * (1 + |Axi.trans R y|) ^ 1 ≤
          C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ 2 :=
        mul_le_mul (mul_le_mul hC hk (by positivity) hCnv0) ht_le (by positivity) (by positivity)
      exact hj1.trans (mul_le_mul hfac hsub hsumj0 (by positivity))
    · have hj2 := (H2 R τ b hR1 hb').2 y hyax
      have hk : (1 + Axi.age R y) ^ k2 ≤ (1 + Axi.age R y) ^ K_nv :=
        pow_le_pow_right₀ h1s (by omega)
      have hC : C2 ≤ C_nv := by unfold C_nv; linarith
      have hfac : C2 * (1 + Axi.age R y) ^ k2 * (1 + |Axi.trans R y|) ^ 2 ≤
          C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ 2 :=
        mul_le_mul (mul_le_mul hC hk (by positivity) hCnv0) ht_le (by positivity) (by positivity)
      exact hj2.trans (mul_le_mul hfac hsub hsumj0 (by positivity))
  have hleib : ‖iteratedFDeriv ℝ 2 (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤
      ∑ i ∈ Finset.range 3, (Nat.choose 2 i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (2 - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ := by
    rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun w => Axi.age R w • Axi.Nv R b τ w) 2 Axi.isOpen_compl_axis hyS]
    exact norm_iteratedFDerivWithin_smul_le hAgeS hNvS
      Axi.isOpen_compl_axis.uniqueDiffOn hyS (n := 2) (hjLe 2)
  have hterm : ∀ i ∈ Finset.range 3,
      (Nat.choose 2 i : ℝ) * ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (2 - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ ≤
        2 * Ca * C_nv * (1 + Axi.age R y) ^ (K_nv + 4) * (1 + |Axi.trans R y|) ^ 2 *
          ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
    intro i hi
    have hi2 : i ≤ 2 := by have := Finset.mem_range.1 hi; omega
    rw [iteratedFDerivWithin_of_isOpen i Axi.isOpen_compl_axis hyS,
      iteratedFDerivWithin_of_isOpen (2 - i) Axi.isOpen_compl_axis hyS]
    have hA_i : ‖iteratedFDeriv ℝ i (Axi.age R) y‖ ≤ Ca * (1 + Axi.age R y) ^ 4 :=
      (hCa y hyax i hi2).trans
        (mul_le_mul_of_nonneg_left (ϱ_rpow_neg_two_add_le_age hR1 hyax hi2) hCa0)
    have hB_i := hNv_le (2 - i) (by omega)
    have hch : (Nat.choose 2 i : ℝ) ≤ 2 := by
      interval_cases i <;> norm_num [Nat.choose]
    have hr1 : 0 ≤ Ca * (1 + Axi.age R y) ^ 4 := by positivity
    calc (Nat.choose 2 i : ℝ) * ‖iteratedFDeriv ℝ i (Axi.age R) y‖ *
          ‖iteratedFDeriv ℝ (2 - i) (Axi.Nv R b τ) y‖
        ≤ 2 * (Ca * (1 + Axi.age R y) ^ 4) *
            (C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ 2 *
              ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖) :=
          mul_le_mul (mul_le_mul hch hA_i (norm_nonneg _) (by norm_num)) hB_i
            (norm_nonneg _) (mul_nonneg (by norm_num) hr1)
      _ = 2 * Ca * C_nv * ((1 + Axi.age R y) ^ K_nv * (1 + Axi.age R y) ^ 4) *
            (1 + |Axi.trans R y|) ^ 2 *
            ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by ring
      _ = 2 * Ca * C_nv * (1 + Axi.age R y) ^ (K_nv + 4) * (1 + |Axi.trans R y|) ^ 2 *
            ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
          rw [← pow_add (1 + Axi.age R y) K_nv 4]
  calc ‖iteratedFDeriv ℝ 2 (fun w => Axi.age R w • Axi.Nv R b τ w) y‖
      ≤ ∑ i ∈ Finset.range 3, (Nat.choose 2 i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (2 - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ := hleib
    _ ≤ ∑ _ ∈ Finset.range 3,
          2 * Ca * C_nv * (1 + Axi.age R y) ^ (K_nv + 4) * (1 + |Axi.trans R y|) ^ 2 *
            ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ :=
        Finset.sum_le_sum hterm
    _ = 6 * Ca * C_nv * (1 + Axi.age R y) ^ (K_nv + 4) * (1 + |Axi.trans R y|) ^ 2 *
          ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
        rw [Finset.sum_const, Finset.card_range]
        ring

/-- For `1 ≤ s` and any `η : ℝ`, `(1 + |η|)² ≤ 2 (1 + s) (1 + η² / s)`. -/
theorem sq_one_add_abs_le_two_one_add_age_mul {s : ℝ} (hs : 1 ≤ s) (η : ℝ) :
    (1 + |η|) ^ 2 ≤ 2 * (1 + s) * (1 + η ^ 2 / s) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have h1 := sq_one_add_abs_le_two_mul_one_add_sq η
  have h2 : s * (η ^ 2 / s) = η ^ 2 := mul_div_cancel₀ _ hs0.ne'
  have h3 : 0 ≤ η ^ 2 / s := div_nonneg (sq_nonneg η) hs0.le
  nlinarith

/-- On `Axi.ϱ y ≤ R0` with `1 ≤ R` and `Axi.ϱ y ≠ 0`,
`1 + (Axi.trans R y)² / Axi.age R y ≤ (1 + R0²) (1 + |Axi.trans R y|)²`. -/
theorem wtd_le_one_add_R0_sq_mul_trans {R R0 : ℝ} (hR : 1 ≤ R)
    {y : UnforcedLeray.Space} (hy0 : Axi.ϱ y ≠ 0) (hyR : Axi.ϱ y ≤ R0) :
    1 + (Axi.trans R y) ^ 2 / Axi.age R y ≤ (1 + R0 ^ 2) * (1 + |Axi.trans R y|) ^ 2 := by
  have hR_ne : R ≠ 0 := by linarith
  have hρ : 0 < Axi.ϱ y := lt_of_le_of_ne (Axi.ϱ_nonneg y) (Ne.symm hy0)
  rw [trans_sq_div_age_eq_sq hR_ne hy0]
  have hy2 : |y 2| ≤ R0 * |Axi.trans R y| := by
    unfold Axi.trans
    rw [abs_div, abs_mul, abs_of_pos (by linarith : 0 < R), abs_of_pos hρ]
    have h1 : |y 2| ≤ R * |y 2| := le_mul_of_one_le_left (abs_nonneg _) hR
    have h2 : |y 2| / Axi.ϱ y ≤ R * |y 2| / Axi.ϱ y :=
      div_le_div_of_nonneg_right h1 hρ.le
    have h3 : Axi.ϱ y * (|y 2| / Axi.ϱ y) = |y 2| := mul_div_cancel₀ _ hy0
    have h4 : Axi.ϱ y * (R * |y 2| / Axi.ϱ y) ≤ R0 * (R * |y 2| / Axi.ϱ y) :=
      mul_le_mul_of_nonneg_right hyR (by positivity)
    linarith [mul_le_mul_of_nonneg_left h2 hρ.le]
  have hy2_sq : y 2 ^ 2 ≤ R0 ^ 2 * (Axi.trans R y) ^ 2 := by
    have h0 : 0 ≤ R0 * |Axi.trans R y| :=
      mul_nonneg (hρ.le.trans hyR) (abs_nonneg _)
    have hsq := pow_le_pow_left₀ (abs_nonneg (y 2)) hy2 2
    rwa [sq_abs, mul_pow, sq_abs] at hsq
  have htr_sq : (Axi.trans R y) ^ 2 ≤ (1 + |Axi.trans R y|) ^ 2 := by
    have : |Axi.trans R y| ^ 2 = (Axi.trans R y) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (Axi.trans R y)]
  have htr_1 : 1 ≤ (1 + |Axi.trans R y|) ^ 2 := by
    nlinarith [abs_nonneg (Axi.trans R y)]
  have hy2_le : y 2 ^ 2 ≤ R0 ^ 2 * (1 + |Axi.trans R y|) ^ 2 :=
    hy2_sq.trans (mul_le_mul_of_nonneg_left htr_sq (sq_nonneg R0))
  linarith

/-- For `1 ≤ s` and any `M : ℕ`, `(1 + s)^M * s^{-(M : ℝ)} ≤ 2^M`. -/
theorem one_add_age_pow_mul_rpow_neg_le {s : ℝ} (hs : 1 ≤ s) (M : ℕ) :
    (1 + s) ^ M * s ^ (-(M : ℝ)) ≤ 2 ^ M := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have h1 : (1 + s) ^ M ≤ (2 * s) ^ M :=
    pow_le_pow_left₀ (by linarith) (by linarith) M
  have h2 : s ^ M * s ^ (-(M : ℝ)) = 1 := by
    rw [← Real.rpow_natCast s M, ← Real.rpow_add hs0, add_neg_cancel, Real.rpow_zero]
  calc (1 + s) ^ M * s ^ (-(M : ℝ))
      ≤ (2 * s) ^ M * s ^ (-(M : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs0.le _)
    _ = 2 ^ M * (s ^ M * s ^ (-(M : ℝ))) := by rw [mul_pow, mul_assoc]
    _ = 2 ^ M := by rw [h2, mul_one]

end AxialTailSub

/-- **`ResNearAxisJet2` from `ResProfileEarlyJet2` and `ResProfileLateHeatDecomp2`**
(`the November 2 reference manuscript`, lines 1270-1304, 1310-1325, 2548-2551). -/
theorem resNearAxisJet2_of (hEarly : ResProfileEarlyJet2) (hLate : ResProfileLateHeatDecomp2) :
    ResNearAxisJet2 := by
  obtain ⟨K, hJet⟩ := AxialTailSub.age_smul_nv_pt_jet2
  obtain ⟨ν₁, hν₁, HE⟩ := hEarly
  obtain ⟨ν₂, hν₂, HL⟩ := hLate (K + 1)
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p htr hν hc hR hP R0 hR0 => ?_⟩
  obtain ⟨C_lift, hClift0, Hlift⟩ := hJet p.R hR
  obtain ⟨C_early, Hearly⟩ := HE p htr (lt_of_lt_of_le hν (min_le_left _ _)) hc hR hP
  obtain ⟨F_heat, r_rem, C_heat, C_rem, hF_sm, hrem_sm, hdecomp, hF_bd, hrem_bd⟩ :=
    HL p htr (lt_of_lt_of_le hν (min_le_right _ _)) hc hR hP
  have hres_sm : ContDiffOn ℝ ∞ (resChartProfile p) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    resChartProfile_contDiffOn p htr
  set Ce : ℝ := C_lift * 2 ^ K * (1 + R0 ^ 2) * (3 * max C_early 0)
  set Cl : ℝ := max C_heat 0 + C_lift * 2 ^ (K + 2) * (3 * max C_rem 0)
  refine ⟨max Ce Cl, 0, le_rfl, fun τ _ y hy0 hyR _ => ?_⟩
  have hyax : y ∉ Axi.axis := mt (Axi.mem_axis_iff y).mp hy0
  have hR1 : 1 ≤ p.R := by linarith
  have hR_ne : p.R ≠ 0 := by linarith
  have hs0 : 0 < Axi.age p.R y := Axi.age_pos hR_ne hyax
  set W : ℝ := 1 + (Axi.trans p.R y) ^ 2 / Axi.age p.R y
  have hW0 : 0 ≤ W := by unfold W; positivity
  by_cases hs1 : Axi.age p.R y ≤ 1
  · -- Early / bounded age `0 < s ≤ 1`
    have h1 := (Hlift (resChartProfile p) hres_sm τ y hyax).2
    have hW_le := AxialTailSub.wtd_le_one_add_R0_sq_mul_trans hR1 hy0 hyR
    have hs_pow : (1 + Axi.age p.R y) ^ K ≤ 2 ^ K :=
      pow_le_pow_left₀ (by linarith) (by linarith) K
    have htr4_pos : 0 < (1 + |Axi.trans p.R y|) ^ 4 := by positivity
    have hterm_e : ∀ l ∈ Finset.range 3,
        (1 + |Axi.trans p.R y|) ^ 4 *
          ‖iteratedFDeriv ℝ l (resChartProfile p) (Axi.chart p.R τ y)‖ ≤ max C_early 0 := by
      intro l hl
      have hl2 : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
      exact (Hearly (Axi.chart p.R τ y) hs0 hs1 l hl2).trans (le_max_left _ _)
    have hsum_e : (1 + |Axi.trans p.R y|) ^ 4 *
        ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (resChartProfile p) (Axi.chart p.R τ y)‖ ≤
        3 * max C_early 0 := by
      rw [Finset.mul_sum]
      calc ∑ l ∈ Finset.range 3, (1 + |Axi.trans p.R y|) ^ 4 *
              ‖iteratedFDeriv ℝ l (resChartProfile p) (Axi.chart p.R τ y)‖
          ≤ ∑ _ ∈ Finset.range 3, max C_early 0 := Finset.sum_le_sum hterm_e
        _ = 3 * max C_early 0 := by rw [Finset.sum_const, Finset.card_range]; ring
    have hmain : W * ‖iteratedFDeriv ℝ 2
        (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ ≤ Ce := by
      calc W * ‖iteratedFDeriv ℝ 2
              (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖
          ≤ ((1 + R0 ^ 2) * (1 + |Axi.trans p.R y|) ^ 2) *
              (C_lift * (1 + Axi.age p.R y) ^ K * (1 + |Axi.trans p.R y|) ^ 2 *
                ∑ l ∈ Finset.range 3,
                  ‖iteratedFDeriv ℝ l (resChartProfile p) (Axi.chart p.R τ y)‖) :=
            mul_le_mul hW_le h1 (norm_nonneg _) (by positivity)
        _ = C_lift * (1 + Axi.age p.R y) ^ K * (1 + R0 ^ 2) *
              ((1 + |Axi.trans p.R y|) ^ 4 *
                ∑ l ∈ Finset.range 3,
                  ‖iteratedFDeriv ℝ l (resChartProfile p) (Axi.chart p.R τ y)‖) := by ring
        _ ≤ C_lift * 2 ^ K * (1 + R0 ^ 2) * (3 * max C_early 0) := by
            refine mul_le_mul ?_ hsum_e (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hs_pow hClift0) (by positivity)
    exact hmain.trans (le_max_left _ _)
  · -- Late age `1 < s`, hence `ϱ(y) ≤ p.R`
    have hs1' : 1 ≤ Axi.age p.R y := (not_le.mp hs1).le
    have hρR : Axi.ϱ y ≤ p.R := by
      have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hyax
      have h1 : 1 ≤ p.R ^ 2 / Axi.ϱ y ^ 2 := hs1'
      rw [le_div_iff₀ (pow_pos hρ 2), one_mul] at h1
      nlinarith [Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2)]
    have hev : (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) =ᶠ[𝓝 y]
        fun w => F_heat w + Axi.age p.R w • Axi.Nv p.R r_rem τ w :=
      Filter.eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyax)
        (fun z hz => hdecomp τ z hz)
    have hrem_lift := Hlift r_rem hrem_sm τ y hyax
    have hFc : ContDiffAt ℝ 2 F_heat y :=
      hF_sm.contDiffAt.of_le (by simp)
    have hRc : ContDiffAt ℝ 2 (fun w => Axi.age p.R w • Axi.Nv p.R r_rem τ w) y :=
      (hrem_lift.1.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hyax)).of_le
        (by simp)
    have hadd_fderiv :
        iteratedFDeriv ℝ 2 (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y =
          iteratedFDeriv ℝ 2 F_heat y +
            iteratedFDeriv ℝ 2 (fun w => Axi.age p.R w • Axi.Nv p.R r_rem τ w) y := by
      rw [(hev.iteratedFDeriv ℝ 2).eq_of_nhds]
      exact iteratedFDeriv_add_apply hFc hRc
    have htri : W * ‖iteratedFDeriv ℝ 2
        (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ ≤
        W * ‖iteratedFDeriv ℝ 2 F_heat y‖ +
          W * ‖iteratedFDeriv ℝ 2 (fun w => Axi.age p.R w • Axi.Nv p.R r_rem τ w) y‖ := by
      rw [hadd_fderiv, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hW0
    have hW_eq : W = 1 + y 2 ^ 2 := by
      unfold W
      rw [trans_sq_div_age_eq_sq hR_ne hy0]
    have hheat_part : W * ‖iteratedFDeriv ℝ 2 F_heat y‖ ≤ max C_heat 0 := by
      rw [hW_eq]
      exact (hF_bd y hρR).trans (le_max_left _ _)
    have htr_le := AxialTailSub.sq_one_add_abs_le_two_one_add_age_mul hs1' (Axi.trans p.R y)
    have hterm_r : ∀ l ∈ Finset.range 3,
        W ^ 2 * ‖iteratedFDeriv ℝ l r_rem (Axi.chart p.R τ y)‖ ≤
          max C_rem 0 * (Axi.age p.R y) ^ (-((K + 1 : ℕ) : ℝ)) := by
      intro l hl
      have hl2 : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
      have hb := hrem_bd (Axi.chart p.R τ y) hs1' l hl2
      exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs0.le _))
    have hsum_r : W ^ 2 * ∑ l ∈ Finset.range 3,
        ‖iteratedFDeriv ℝ l r_rem (Axi.chart p.R τ y)‖ ≤
        (3 * max C_rem 0) * (Axi.age p.R y) ^ (-((K + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      calc ∑ l ∈ Finset.range 3, W ^ 2 * ‖iteratedFDeriv ℝ l r_rem (Axi.chart p.R τ y)‖
          ≤ ∑ _ ∈ Finset.range 3, max C_rem 0 * (Axi.age p.R y) ^ (-((K + 1 : ℕ) : ℝ)) :=
            Finset.sum_le_sum hterm_r
        _ = (3 * max C_rem 0) * (Axi.age p.R y) ^ (-((K + 1 : ℕ) : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range]; ring
    have hpow_age := AxialTailSub.one_add_age_pow_mul_rpow_neg_le hs1' (K + 1)
    have hrem_part : W * ‖iteratedFDeriv ℝ 2
        (fun w => Axi.age p.R w • Axi.Nv p.R r_rem τ w) y‖ ≤
        C_lift * 2 ^ (K + 2) * (3 * max C_rem 0) := by
      have hS0 : 0 ≤ ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l r_rem (Axi.chart p.R τ y)‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hfac : W * (C_lift * (1 + Axi.age p.R y) ^ K * (1 + |Axi.trans p.R y|) ^ 2) ≤
          2 * C_lift * (1 + Axi.age p.R y) ^ (K + 1) * W ^ 2 := by
        have h1 : W * (C_lift * (1 + Axi.age p.R y) ^ K * (1 + |Axi.trans p.R y|) ^ 2) =
            (C_lift * (1 + Axi.age p.R y) ^ K * W) * (1 + |Axi.trans p.R y|) ^ 2 := by ring
        have h2 : (C_lift * (1 + Axi.age p.R y) ^ K * W) *
            (2 * (1 + Axi.age p.R y) * W) =
            2 * C_lift * (1 + Axi.age p.R y) ^ (K + 1) * W ^ 2 := by
          rw [pow_succ]; ring
        rw [h1, ← h2]
        exact mul_le_mul_of_nonneg_left htr_le (by positivity)
      calc W * ‖iteratedFDeriv ℝ 2 (fun w => Axi.age p.R w • Axi.Nv p.R r_rem τ w) y‖
          ≤ W * (C_lift * (1 + Axi.age p.R y) ^ K * (1 + |Axi.trans p.R y|) ^ 2 *
              ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l r_rem (Axi.chart p.R τ y)‖) :=
            mul_le_mul_of_nonneg_left hrem_lift.2 hW0
        _ = (W * (C_lift * (1 + Axi.age p.R y) ^ K * (1 + |Axi.trans p.R y|) ^ 2)) *
              ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l r_rem (Axi.chart p.R τ y)‖ := by ring
        _ ≤ (2 * C_lift * (1 + Axi.age p.R y) ^ (K + 1) * W ^ 2) *
              ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l r_rem (Axi.chart p.R τ y)‖ :=
            mul_le_mul_of_nonneg_right hfac hS0
        _ = (2 * C_lift * (1 + Axi.age p.R y) ^ (K + 1)) *
              (W ^ 2 * ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l r_rem (Axi.chart p.R τ y)‖) := by
            ring
        _ ≤ (2 * C_lift * (1 + Axi.age p.R y) ^ (K + 1)) *
              ((3 * max C_rem 0) * (Axi.age p.R y) ^ (-((K + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hsum_r (by positivity)
        _ = (2 * C_lift * (3 * max C_rem 0)) *
              ((1 + Axi.age p.R y) ^ (K + 1) * (Axi.age p.R y) ^ (-((K + 1 : ℕ) : ℝ))) := by ring
        _ ≤ (2 * C_lift * (3 * max C_rem 0)) * 2 ^ (K + 1) :=
            mul_le_mul_of_nonneg_left hpow_age (by positivity)
        _ = C_lift * 2 ^ (K + 2) * (3 * max C_rem 0) := by
            rw [pow_succ]; ring
    have hmain : W * ‖iteratedFDeriv ℝ 2
        (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ ≤ Cl :=
      htri.trans (add_le_add hheat_part hrem_part)
    exact hmain.trans (le_max_right _ _)

/-- **`RawResidualD2AxialTail` from `ResNearAxisJet2`** (`the November 2 reference manuscript`,
lines 1270-1304, 1310-1325, 2548-2551). -/
theorem rawResidualD2AxialTail_of (h : ResNearAxisJet2) : RawResidualD2AxialTail := by
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨ν₀, hν₀, fun p htr hν hc hR hP j l R0 hR0 => ?_⟩
  obtain ⟨C, Z0, hZ0, hjet⟩ := H p htr hν hc hR hP R0 hR0
  refine ⟨2 * max C 0, Z0, hZ0, fun τ hτ y hy0 hyR hyZ => ?_⟩
  have hR0_ne : p.R ≠ 0 := by linarith
  have hdy := norm_dy2_rawResidualC_le_iteratedFDeriv p htr hR j l τ hy0
  have hj := hjet τ hτ y hy0 hyR hyZ
  set W : ℝ := 1 + (Axi.trans p.R y) ^ 2 / Axi.age p.R y
  have hW_eq : W = 1 + y 2 ^ 2 := by
    unfold W
    rw [trans_sq_div_age_eq_sq hR0_ne hy0]
  have hW_pos : 0 < W := by
    rw [hW_eq]
    positivity
  have hjet_le :
      ‖iteratedFDeriv ℝ 2
          (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ ≤
        max C 0 * W⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀' hW_pos]
    exact hj.trans (le_max_left C 0)
  have hW_inv : W⁻¹ ≤ 2 * (1 + |y 2|) ^ (-2 : ℝ) :=
    inv_one_add_trans_sq_div_age_le hR0_ne hy0
  calc ‖dy j (dy l (rawResidualC p)) (τ, y)‖
      ≤ ‖iteratedFDeriv ℝ 2
          (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ := hdy
    _ ≤ max C 0 * W⁻¹ := hjet_le
    _ ≤ max C 0 * (2 * (1 + |y 2|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hW_inv (le_max_right C 0)
    _ = (2 * max C 0) * (1 + |y 2|) ^ (-2 : ℝ) := by ring

/-- **`RawResidualD2AxialTail` from `ResProfileEarlyJet2` and `ResProfileLateHeatDecomp2`**
(`the November 2 reference manuscript`, lines 1270-1304, 1310-1325, 2548-2551). -/
theorem rawResidualD2AxialTail_of_early_and_late
    (hEarly : ResProfileEarlyJet2) (hLate : ResProfileLateHeatDecomp2) :
    RawResidualD2AxialTail :=
  rawResidualD2AxialTail_of (resNearAxisJet2_of hEarly hLate)

/-- **`RawResidualD2NearBound` from `RingLiftSmoothExt` and `ResNearAxisJet2`**. -/
theorem rawResidualD2NearBound_of_smoothExt_and_jet2
    (hExt : UnforcedLeray.Short.IIb.RingLiftSmoothExt) (hJet : ResNearAxisJet2) :
    RawResidualD2NearBound :=
  rawResidualD2NearBound_of hExt (rawResidualD2AxialTail_of hJet)

end UnforcedLeray.Short.PartIIIb.Concrete
