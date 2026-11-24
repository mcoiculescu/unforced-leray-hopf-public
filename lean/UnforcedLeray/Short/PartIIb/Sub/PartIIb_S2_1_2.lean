import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2

/-!
# `PartII-b:S2/1/2`: `RawResidualIteratedEnvelope` (reduction to two leaves)

Source of record: `the November 2 reference manuscript`,
lines 2542-2551 (for any fixed derivative order the train complete source lies in `W^{k,Y_p}`:
large radius `C_{k,N} ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`; on `ϱ < R` the all-age heat expansion), 1206-1222
(ring lift, `F_R = s^{3/2} r`), 2563-2569.

## What is proved here

* **Far field, all orders** (`RawIterEnvSub.far_decay_of`): from the early-age chart jets of the
  residual profile (`ResProfileEarlyJetAll`), for `ϱ(y) > R` (so `s = R²/ϱ² < 1`),
  `‖iterDyRev β (rawResidualC p)(τ, y)‖ ≤ C ϱ^{-3}(1+|y₃|/ϱ)^{-2}`.  Slice bridge
  `norm_iterDyRev_le_slice`, `rawResidualC = realC (s • N_v r)` off the axis, and the all-order
  Leibniz/Faà di Bruno bound `age_smul_nv_far_jet_upto` (`RawResidualIteratedEnvelope/Calc.lean`).
* **Compact core, all orders** (`RawIterEnvSub.compact_core`): from `RingLiftSmoothExt`
  (`ringLiftSmoothExt_s2_proof`) and `ringResidualCartesianNS_proof`, `rawResidualC p` agrees off the
  axis with a globally `C^∞` field, so its iterated derivatives are bounded on
  `[0, P] × {ϱ ≤ R₀, |y₃| ≤ Z₀}`.
* **Assembly** (`rawResidualIteratedEnvelope_of`): with `R₀ = R` in `cylProfile`.

## The two leaves

* `ResProfileEarlyJetAll`: the all-order, all-weight analogue of `ResProfileEarlyJet2`
  (`PartIII-b_C_ward_12_3_2_2_1_2_1.lean:69`) **with one viscosity threshold for all orders and
  weights**.  The existing proof of `ResProfileEarlyJet2` (via `EarlyStreamProfile`,
  `EarlyPressureProfile`, `EarlyBdd`) gives, for each order and weight, a threshold depending on them
  (the Part I bounds `TrainInteriorStripJetBounds`, `TrainStreamVelocityPressureTransverseTail` are
  stated per order), so the uniform threshold demanded by `RawResidualIteratedEnvelope` (its `ν₀`
  precedes `m`) needs the fixed-parameter form, as for `TrainStreamWtdBdd`
  (`RingLiftOffAxis_Sub.lean:115`), together with its pressure analogue.
* `RawResidualIteratedLateTail`: the late-age (`ϱ ≤ R`, `s ≥ 1`) axial tail for `|y₃| > Z₀`, the
  all-order analogue of `RawResidualD2AxialTail` (whose order-2 proof is the finite heat expansion of
  `PartIII-b_C_ward_12_3_2_2_1_2_1_2.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **(Leaf 1) Early-age chart jets of the residual profile, all orders and weights, one threshold**
(SP 1294-1304, 2542-2548, 439-467 at fixed parameters): for `0 < s ≤ 1`, every jet of
`resChartProfile p` decays in `η` faster than any power, with constants depending on `p`, `L`, `N`
but the threshold `ν₀` independent of `L`, `N`. -/
def ResProfileEarlyJetAll : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ L N : ℕ,
      ∃ C : ℝ, ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ 1 → ∀ l ≤ L,
        (1 + |m.2.2|) ^ N * ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) m‖ ≤ C

/-- **(Leaf 2) Late-age axial tail of the iterated raw residual** (SP 1270-1304, 1305-1325,
2548-2551): on `0 < ϱ(y) ≤ R` (`s ≥ 1`) and `|y₃| > Z₀`, the all-age heat expansion to a finite
order gives `‖∂^β F_R(τ, y)‖ ≤ C (1 + |y₃|)^{-2}` (all-order analogue of
`RawResidualD2AxialTail`, restricted to `R₀ = R`). -/
def RawResidualIteratedLateTail : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ (m : ℕ) (β : Fin m → Fin 3),
      ∃ C Z0 : ℝ, 0 ≤ Z0 ∧ ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space,
        Axi.ϱ y ≠ 0 → Axi.ϱ y ≤ p.R → Z0 < |y 2| →
          ‖iterDyRev β (rawResidualC p) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)

namespace RawIterEnvSub

/-- **Far field of the iterated raw residual, all orders** (SP 2542-2548): on `ϱ(y) > R`,
`‖∂^β F_R(τ, y)‖ ≤ C ϱ^{-3} (1 + |y₃|/ϱ)^{-2}`. -/
theorem far_decay_of (hE : ResProfileEarlyJetAll) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ (m : ℕ) (β : Fin m → Fin 3),
        ∃ C : ℝ, ∀ (τ : ℝ) (y : Space), p.R < Axi.ϱ y →
          ‖iterDyRev β (rawResidualC p) (τ, y)‖ ≤
            C * (Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) := by
  obtain ⟨ν₀, hν₀, H⟩ := hE
  refine ⟨ν₀, hν₀, fun p htr hν hc hR hP m β => ?_⟩
  obtain ⟨Cb, hCb⟩ := H p htr hν hc hR hP m (m + 2)
  have hR1 : (1 : ℝ) ≤ p.R := by linarith
  have hRpos : 0 < p.R := by linarith
  obtain ⟨A, hA0, hA⟩ := age_smul_nv_far_jet_upto hR1 m
  have hsm := FarDecaySub.resChartProfile_contDiffOn p htr
  refine ⟨A * (((m : ℝ) + 1) * |Cb|), fun τ y hy => ?_⟩
  have hp : 0 < Axi.ϱ y := hRpos.trans hy
  have hyax : y ∉ Axi.axis := notMem_axis_of_le hRpos hy.le
  have hU : IsOpen {z : ℝ × Space | z.2 ∉ Axi.axis} :=
    Axi.isOpen_compl_axis.preimage continuous_snd
  have hGsm : ContDiffOn ℝ ∞ (rawResidualC p) {z : ℝ × Space | z.2 ∉ Axi.axis} :=
    (FarDecaySub.age_smul_Nv_joint_contDiffOn p.R hRpos (FarDecaySub.resChartProfile p) hsm).congr
      (fun z hz => FarDecaySub.rawResidualC_eq_off_axis p htr hR z hz)
  have h1 : ‖iterDyRev β (rawResidualC p) (τ, y)‖ ≤
      ‖iteratedFDeriv ℝ m (fun w => rawResidualC p (τ, w)) y‖ :=
    norm_iterDyRev_le_slice hU hGsm β (a := τ) (y := y) hyax
  have hev : (fun w => rawResidualC p (τ, w)) =ᶠ[𝓝 y]
      (fun w => efarRealCLI (Axi.age p.R w • Axi.Nv p.R (FarDecaySub.resChartProfile p) τ w)) :=
    Filter.eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyax)
      (fun w hw => FarDecaySub.rawResidualC_eq_off_axis p htr hR (τ, w) hw)
  have hrealS : ContDiffOn ℝ ∞
      (fun w => Axi.age p.R w • Axi.Nv p.R (FarDecaySub.resChartProfile p) τ w) Axi.axisᶜ := by
    have hAgeS : ContDiffOn ℝ ∞ (Axi.age p.R) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
        (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
    have hgS : ContDiffOn ℝ ∞
        (fun z => FarDecaySub.resChartProfile p (Axi.chart p.R τ z)) Axi.axisᶜ :=
      hsm.comp (clf_chart_contDiffOn p.R τ hRpos) (clf_chart_mapsTo p.R τ hRpos)
    have hNvS : ContDiffOn ℝ ∞ (Axi.Nv p.R (FarDecaySub.resChartProfile p) τ) Axi.axisᶜ := by
      have hEq : Axi.Nv p.R (FarDecaySub.resChartProfile p) τ =
          fun z => liftFactor p.R z (FarDecaySub.resChartProfile p (Axi.chart p.R τ z)) :=
        funext fun z => Nv_eq_liftFactor p.R (FarDecaySub.resChartProfile p) τ z
      rw [hEq]
      exact (clf_lift_contDiffOn p.R hRpos).clm_apply hgS
    exact hAgeS.smul hNvS
  have hiso := efar_realC_norm
    (fun w => Axi.age p.R w • Axi.Nv p.R (FarDecaySub.resChartProfile p) τ w) hrealS hyax m
  have h2 : ‖iteratedFDeriv ℝ m (fun w => rawResidualC p (τ, w)) y‖ =
      ‖iteratedFDeriv ℝ m
        (fun w => Axi.age p.R w • Axi.Nv p.R (FarDecaySub.resChartProfile p) τ w) y‖ := by
    rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds, hiso]
  have h3 := hA (FarDecaySub.resChartProfile p) hsm τ y hy.le
  -- the early-age chart jets at the chart point (`0 < s < 1`)
  have ht0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have ht1 : 0 < 1 + |y 2| / Axi.ϱ y := by linarith
  have hs0 : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos hRpos.ne' hyax
  have hs1 : (Axi.chart p.R τ y).1 ≤ 1 := by
    show Axi.age p.R y ≤ 1
    unfold Axi.age
    rw [div_le_one (by positivity)]
    nlinarith
  have hη : 1 + |y 2| / Axi.ϱ y ≤ 1 + |(Axi.chart p.R τ y).2.2| := by
    show 1 + |y 2| / Axi.ϱ y ≤ 1 + |Axi.trans p.R y|
    rw [Axi.trans, abs_div, abs_mul, abs_of_pos hRpos, abs_of_pos hp]
    have : |y 2| / Axi.ϱ y ≤ p.R * |y 2| / Axi.ϱ y :=
      div_le_div_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _) hR1) hp.le
    linarith
  have hl : ∀ l ∈ Finset.range (m + 1),
      ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) (Axi.chart p.R τ y)‖ ≤
        |Cb| * ((1 + |y 2| / Axi.ϱ y) ^ (m + 2))⁻¹ := by
    intro l hl
    have hlm : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hb := hCb (Axi.chart p.R τ y) hs0 hs1 l hlm
    have hpowle : (1 + |y 2| / Axi.ϱ y) ^ (m + 2) ≤ (1 + |(Axi.chart p.R τ y).2.2|) ^ (m + 2) :=
      pow_le_pow_left₀ ht1.le hη _
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos ht1 _)]
    calc ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) (Axi.chart p.R τ y)‖ *
          (1 + |y 2| / Axi.ϱ y) ^ (m + 2)
        ≤ ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) (Axi.chart p.R τ y)‖ *
          (1 + |(Axi.chart p.R τ y).2.2|) ^ (m + 2) :=
          mul_le_mul_of_nonneg_left hpowle (norm_nonneg _)
      _ = (1 + |(Axi.chart p.R τ y).2.2|) ^ (m + 2) *
          ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) (Axi.chart p.R τ y)‖ :=
          mul_comm _ _
      _ ≤ Cb := hb
      _ ≤ |Cb| := le_abs_self _
  have hS : ∑ l ∈ Finset.range (m + 1),
      ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) (Axi.chart p.R τ y)‖ ≤
        ((m : ℝ) + 1) * (|Cb| * ((1 + |y 2| / Axi.ϱ y) ^ (m + 2))⁻¹) := by
    refine (Finset.sum_le_sum hl).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hpow : (1 + |y 2| / Axi.ϱ y) ^ m * ((1 + |y 2| / Axi.ϱ y) ^ (m + 2))⁻¹ =
      ((1 + |y 2| / Axi.ϱ y) ^ 2)⁻¹ := by
    rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht1.ne'), one_mul]
  have e1 : Axi.ϱ y ^ (-3 : ℝ) = (Axi.ϱ y ^ 3)⁻¹ := by
    rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hp.le, Real.rpow_natCast]
  have e2 : (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) = ((1 + |y 2| / Axi.ϱ y) ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht1.le, Real.rpow_natCast]
  have hpre0 : 0 ≤ A * (Axi.ϱ y ^ 3)⁻¹ := mul_nonneg hA0 (inv_nonneg.2 (by positivity))
  calc ‖iterDyRev β (rawResidualC p) (τ, y)‖
      ≤ ‖iteratedFDeriv ℝ m (fun w => rawResidualC p (τ, w)) y‖ := h1
    _ = ‖iteratedFDeriv ℝ m
          (fun w => Axi.age p.R w • Axi.Nv p.R (FarDecaySub.resChartProfile p) τ w) y‖ := h2
    _ ≤ A * (Axi.ϱ y ^ 3)⁻¹ * ((1 + |y 2| / Axi.ϱ y) ^ m *
          ∑ l ∈ Finset.range (m + 1),
            ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) (Axi.chart p.R τ y)‖) := h3
    _ ≤ A * (Axi.ϱ y ^ 3)⁻¹ * ((1 + |y 2| / Axi.ϱ y) ^ m *
          (((m : ℝ) + 1) * (|Cb| * ((1 + |y 2| / Axi.ϱ y) ^ (m + 2))⁻¹))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (pow_nonneg ht1.le _)) hpre0
    _ = A * (((m : ℝ) + 1) * |Cb|) * ((Axi.ϱ y ^ 3)⁻¹ *
          ((1 + |y 2| / Axi.ϱ y) ^ m * ((1 + |y 2| / Axi.ϱ y) ^ (m + 2))⁻¹)) := by ring
    _ = A * (((m : ℝ) + 1) * |Cb|) *
          (Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) := by
        rw [hpow, e1, e2]

/-- **Compact core, all orders** (SP 1305-1322): on `{τ ∈ (0, P], 0 < ϱ(y) ≤ R₀, |y₃| ≤ Z₀}` the
iterated derivatives of `rawResidualC p` are bounded by `C (1 + |y₃|)^{-2}`. -/
theorem compact_core :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → ∀ (m : ℕ) (β : Fin m → Fin 3) (R0 Z0 : ℝ), 0 ≤ Z0 →
        ∃ C : ℝ, ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space,
          Axi.ϱ y ≠ 0 → Axi.ϱ y ≤ R0 → |y 2| ≤ Z0 →
          ‖iterDyRev β (rawResidualC p) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ) := by
  obtain ⟨ν₀, hν₀, H⟩ := IterDiffEqSub.ringLiftSmoothExt_s2_proof
  refine ⟨ν₀, hν₀, fun p htr hν hc hR m β R0 Z0 hZ0 => ?_⟩
  obtain ⟨U, Pw, hU, hPw, -, -, hext⟩ :=
    H p.ν ⟨p.ν_pos, hν⟩ (trainStream p) (trainPressure p)
      (isExactPlanarTrain_params_rpow p htr hc) p.R hR
  let Fc : ℝ × Space → CVec3 := fun x =>
    UnforcedLeray.B0411.L0 p.ν U x + UnforcedLeray.Cons.C03.Concrete.advT U U x +
      UnforcedLeray.PhaseSpace.gradT Pw x
  have hFc : ContDiff ℝ ∞ Fc := RawDeriv2EnvSub.contDiff_ns_rhs p.ν hU hPw
  have hoff : ∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 → rawResidualC p x = Fc x := fun x hx =>
    ringResidualCartesianNS_proof p.ν p.c p.R (trainStream p) (trainPressure p) p.ν_pos p.c_pos hR
      (isExactPlanarTrain_params p htr) U Pw hU hPw hext x.1 x.2 hx
  have hFn : ContDiff ℝ ∞ (iterDyRev β Fc) := IterDiffEqSub.contDiff_iterDyRev β hFc
  let K : Set (ℝ × Space) :=
    Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : Space) (R0 + Z0)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 (R0 + Z0))
  obtain ⟨M, hM⟩ := hK.bddAbove_image hFn.continuous.norm.continuousOn
  refine ⟨max M 0 * (1 + Z0) ^ (2 : ℝ), fun τ hτ y hy0 hyR hyZ => ?_⟩
  rw [IterDiffEqSub.iterDyRev_eq_off_axis hoff β (x := (τ, y)) hy0]
  have hmemK : (τ, y) ∈ K := by
    refine ⟨⟨hτ.1.le, hτ.2⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (RawNear2Sub.norm_space_le_ϱ_add_abs_two y).trans (add_le_add hyR hyZ)
  have hFn_le : ‖iterDyRev β Fc (τ, y)‖ ≤ max M 0 :=
    (hM (mem_image_of_mem (fun x => ‖iterDyRev β Fc x‖) hmemK)).trans (le_max_left _ _)
  have h1y_pos : 0 < 1 + |y 2| := by positivity
  have h1Z_pos : 0 < 1 + Z0 := by linarith
  have hrp : (1 + Z0) ^ (-2 : ℝ) ≤ (1 + |y 2|) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h1y_pos (by linarith) (by norm_num)
  have h1_le : 1 ≤ (1 + Z0) ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ) := by
    have hmul : (1 + Z0) ^ (2 : ℝ) * (1 + Z0) ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_add h1Z_pos]
      norm_num
    calc (1 : ℝ) = (1 + Z0) ^ (2 : ℝ) * (1 + Z0) ^ (-2 : ℝ) := hmul.symm
      _ ≤ (1 + Z0) ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left hrp (by positivity)
  calc ‖iterDyRev β Fc (τ, y)‖
      ≤ max M 0 * 1 := by linarith
    _ ≤ max M 0 * ((1 + Z0) ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1_le (le_max_right _ _)
    _ = (max M 0 * (1 + Z0) ^ (2 : ℝ)) * (1 + |y 2|) ^ (-2 : ℝ) := by ring

end RawIterEnvSub

open RawIterEnvSub

/-- **`RawResidualIteratedEnvelope` from the two leaves** (SP 2542-2551): far field by
`far_decay_of`, near-axis compact core by `compact_core`, near-axis axial tail by
`RawResidualIteratedLateTail`, with `R₀ = R` in `cylProfile`. -/
theorem rawResidualIteratedEnvelope_of (hE : ResProfileEarlyJetAll)
    (hT : RawResidualIteratedLateTail) : RawResidualIteratedEnvelope := by
  obtain ⟨ν₁, hν₁, H1⟩ := far_decay_of hE
  obtain ⟨ν₂, hν₂, H2⟩ := hT
  obtain ⟨ν₃, hν₃, H3⟩ := compact_core
  refine ⟨min ν₁ (min ν₂ ν₃), lt_min hν₁ (lt_min hν₂ hν₃),
    fun p htr hν hc hR hP m β => ?_⟩
  have e1 : p.ν < ν₁ := lt_of_lt_of_le hν (min_le_left _ _)
  have e2 : p.ν < ν₂ := lt_of_lt_of_le hν ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : p.ν < ν₃ := lt_of_lt_of_le hν ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Cf, hf⟩ := H1 p htr e1 hc hR hP m β
  obtain ⟨Ct, Z0, hZ0, ht⟩ := H2 p htr e2 hc hR hP m β
  obtain ⟨Cc, hcc⟩ := H3 p htr e3 hc hR m β p.R Z0 hZ0
  have hRpos : 0 < p.R := by linarith
  refine ⟨max (max Cf Ct) Cc, p.R, hRpos, fun τ hτ y hy0 => ?_⟩
  unfold cylProfile
  split_ifs with hy
  · have hyR : Axi.ϱ y ≤ p.R := hy
    have hpos : 0 ≤ (1 + |y 2|) ^ (-2 : ℝ) := by positivity
    by_cases hz : |y 2| ≤ Z0
    · exact (hcc τ hτ y hy0 hyR hz).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos)
    · exact (ht τ hτ y hy0 hyR (not_le.mp hz)).trans
        (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hpos)
  · have hy' : p.R < Axi.ϱ y := not_le.mp hy
    have hρ : 0 < Axi.ϱ y := hRpos.trans hy'
    have hpos : 0 ≤ Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) := by positivity
    exact (hf τ y hy').trans
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hpos)

end UnforcedLeray.Short.IIb
