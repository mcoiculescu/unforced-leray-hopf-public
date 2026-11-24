import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB1.HeatLiftHelp

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2/1/2/3`: `MeanBlockA1LateHeatSplit2`

Source of record: `the November 2 reference manuscript`, lines 1251, 1310-1325,
2548-2551 (late-age finite-order heat decomposition for the quadratic radial mean block
`ringEps p.R * meanA1` along `meridE0`).

## Results proved in this file

1. **`meanBlockA1LateHeatSplit2_at (N : ℕ)` (unconditional)**:
   For every expansion order `N : ℕ`, there is a viscosity threshold `ν₀ > 0` such that for all
   parameters `p` with `IsBUCTrain p.train`, `p.ν < ν₀`, `p.c = (p.ν ^ 2)⁻¹`, `2 ≤ p.R`,
   `p.period ≤ 1`, the lifted quadratic radial block
   `Axi.age p.R z • Axi.Nv p.R (fun m => (ringEps p.R * meanA1 p.ν p.c p.train (chartSwap m)) • meridE0) τ z`
   splits off the axis into:
   - the globally `C^∞` Cartesian heat field `heatA1Field p N` satisfying
     `(1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (heatA1Field p N) y‖ ≤ C_heat` on `Axi.ϱ y ≤ p.R`, and
   - the remainder profile `f_rem = fun x => ringEps p.R * remA1 N p.ν p.c p.train x` on
     `ageDomain` whose mixed directional partials `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f_rem))`
     (`ℓ, a, b ≤ 2`) satisfy the `(1 + η² / s)²`-weighted `B * s^{-N}` bound on `1 ≤ s`.
2. **`meanBlockA1LateHeatSplit2_of` (conditional on `JQUnif remA1`)**:
   Derives `MeanBlockA1LateHeatSplit2` once the viscosity threshold `ν₀ > 0` of
   `LateMeanRemainder` / `TrainMeanExpansion` is taken independent of `N` (or once `∀ N : ℕ` is
   placed outside `∃ ν₀ : ℝ` in `ScalarMeridLateHeatSplit2` / `ResProfileLateHeatDecomp2`, matching
   `LateMeanRemainder` and `resNearAxisJet2_of` which only instantiates `N = K + 1`).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal BigOperators
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FarDecaySub EarlyJet2Sub

namespace LateHeatDecomp2Sub

/-- Heat part of `v1bar = -∂_η S` at expansion order `M`. -/
def v1H (M : ℕ) : Jet.Fam := -Jet.famEta (heatSumFam M)

/-- Remainder part of `v1bar = -∂_η S` at expansion order `M`. -/
def v1R (M : ℕ) : Jet.Fam := -Jet.famEta (remFam M)

/-- Heat part of `hbar = (1 - K) S` at expansion order `M`. -/
def hH (M : ℕ) : Jet.Fam := heatSumFam M - Jet.famK (heatSumFam M)

/-- Remainder part of `hbar = (1 - K) S` at expansion order `M`. -/
def hR (M : ℕ) : Jet.Fam := remFam M - Jet.famK (remFam M)

/-- First quadratic heat summand for `(j, i)` (`hH * ∂_η v1H` contribution):
degree `(2j + 1) + (2i + 3) = 2(j + i) + 4`. -/
def heatA1Term₁ (j i : ℕ) : Jet.Fam :=
  fun ν _ tr x =>
    (-(meanCoeff tr j * meanCoeff tr i * (2 * (j : ℝ) + 2))) *
      (lhP ν (2 * j) x * lhP ν (2 * i + 2) x)

/-- Second quadratic heat summand for `(j, i)` (`-v1H * (K + 1) v1H` contribution):
degree `(2j + 2) + (2i + 2) = 2(j + i) + 4`. -/
def heatA1Term₂ (j i : ℕ) : Jet.Fam :=
  fun ν _ tr x =>
    (meanCoeff tr j * meanCoeff tr i * (2 * (i : ℝ) + 1)) *
      (lhP ν (2 * j + 1) x * lhP ν (2 * i + 1) x)

/-- Combined `(j, i)` quadratic heat profile for `meanA1`. -/
def heatA1Pair (j i : ℕ) : Jet.Fam :=
  heatA1Term₁ j i + heatA1Term₂ j i

/-- Explicit quadratic heat profile sum for `meanA1` at expansion order `M`. -/
def heatA1 (M : ℕ) : Jet.Fam :=
  fun ν c tr x =>
    ∑ q ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
      heatA1Pair q.1 q.2 ν c tr x

/-- Order-`M` remainder profile family for `meanA1`. -/
def remA1 (M : ℕ) : Jet.Fam :=
  meanA1 - heatA1 M

/-- Lifted 3D Cartesian field for `ringEps p.R • heatA1Term₁ j i` along `meridE0`. -/
def heatA1Field₁ (p : Params) (j i : ℕ) (z : Space) : Space :=
  (((ringEps p.R * (-(meanCoeff p.train j * meanCoeff p.train i * (2 * (j : ℝ) + 2)))) /
      p.R ^ (2 * (j + i) + 1)) *
    (z 0 ^ 2 + z 1 ^ 2) ^ (j + i) *
    (UnforcedLeray.B0191.profileDeriv p.ν (2 * j) (z 2) *
      UnforcedLeray.B0191.profileDeriv p.ν (2 * i + 2) (z 2))) • Axi.hor z

/-- Lifted 3D Cartesian field for `ringEps p.R • heatA1Term₂ j i` along `meridE0`. -/
def heatA1Field₂ (p : Params) (j i : ℕ) (z : Space) : Space :=
  (((ringEps p.R * (meanCoeff p.train j * meanCoeff p.train i * (2 * (i : ℝ) + 1))) /
      p.R ^ (2 * (j + i) + 1)) *
    (z 0 ^ 2 + z 1 ^ 2) ^ (j + i) *
    (UnforcedLeray.B0191.profileDeriv p.ν (2 * j + 1) (z 2) *
      UnforcedLeray.B0191.profileDeriv p.ν (2 * i + 1) (z 2))) • Axi.hor z

/-- Globally smooth 3D Cartesian heat field lifting `ringEps p.R • heatA1 M` along `meridE0`. -/
def heatA1Field (p : Params) (M : ℕ) (z : Space) : Space :=
  ∑ q ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
    (heatA1Field₁ p q.1 q.2 z + heatA1Field₂ p q.1 q.2 z)

theorem QConstFam.heatA1 (M : ℕ) : QConstFam (heatA1 M) :=
  fun ν _ _ =>
    QConst.sum (Finset.range (M + 1) ×ˢ Finset.range (M + 1)) fun q _ =>
      (((QConst.lhP ν (2 * q.1)).mul (QConst.lhP ν (2 * q.2 + 2))).const_mul _).add
        (((QConst.lhP ν (2 * q.1 + 1)).mul (QConst.lhP ν (2 * q.2 + 1))).const_mul _)

theorem QConstFam.remA1 (M : ℕ) : QConstFam (remA1 M) :=
  QConstFam.meanA1.sub (QConstFam.heatA1 M)

/-! ### Explicit evaluation of `v1H M`, `famShift 1 (v1H M)`, `hH M`, `famEta (v1H M)` on `ageDomain` -/

theorem v1H_late_sum (M : ℕ) :
    Jet.LateEq (v1H M)
      (fun ν _ tr x => ∑ j ∈ Finset.range (M + 1), (-meanCoeff tr j) * lhP ν (2 * j + 1) x) := by
  induction M with
  | zero =>
    intro ν c _ _ tr _ x hx
    have heq : heatSumFam 0 ν c tr = fun y => meanCoeff tr 0 * lhP ν 0 y := by
      funext y; simp [heatSumFam, heatTermFam]
    change -partialEta (heatSumFam 0 ν c tr) x = _
    rw [heq, partialEta_const_mul, lhPartialEta ν 0 hx]
    simp
  | succ M ih =>
    have hsplit : heatSumFam (M + 1) = heatSumFam M + heatTermFam (M + 1) := by
      funext ν c tr y; simp [heatSumFam, Finset.sum_range_succ]
    have hadd := v1_add_late (heatSumFam_smooth M) (heatTermFam_smooth (M + 1))
    intro ν c hν hc tr htr x hx
    have e1 : v1H (M + 1) ν c tr x =
        v1H M ν c tr x + (-partialEta (heatTermFam (M + 1) ν c tr) x) := by
      unfold v1H
      rw [hsplit]
      exact hadd ν c hν hc tr htr hx
    have e2 := ih ν c hν hc tr htr hx
    dsimp only at e2
    have e3 : -partialEta (heatTermFam (M + 1) ν c tr) x =
        (-meanCoeff tr (M + 1)) * lhP ν (2 * (M + 1) + 1) x := by
      unfold heatTermFam
      rw [partialEta_const_mul, lhPartialEta ν (2 * (M + 1)) hx]
      ring
    change v1H (M + 1) ν c tr x =
      ∑ j ∈ Finset.range (M + 1 + 1), (-meanCoeff tr j) * lhP ν (2 * j + 1) x
    rw [Finset.sum_range_succ _ (M + 1), e1, e2, e3]

theorem shift1_v1H_late_sum (M : ℕ) :
    Jet.LateEq (Jet.famShift 1 (v1H M))
      (fun ν _ tr x =>
        ∑ i ∈ Finset.range (M + 1),
          (meanCoeff tr i * (2 * (i : ℝ) + 1)) * lhP ν (2 * i + 1) x) := by
  have hT := Jet.jetToolkit
  induction M with
  | zero =>
    intro ν c _ _ tr _ x hx
    have hev : v1H 0 ν c tr =ᶠ[𝓝 x] fun y => (-meanCoeff tr 0) * lhP ν 1 y := by
      refine Filter.eventuallyEq_of_mem (lhMemNhds hx) fun y hy => ?_
      have heq : heatSumFam 0 ν c tr = fun z => meanCoeff tr 0 * lhP ν 0 z := by
        funext z; simp [heatSumFam, heatTermFam]
      change -partialEta (heatSumFam 0 ν c tr) y = _
      rw [heq, partialEta_const_mul, lhPartialEta ν 0 hy]
      ring
    change ageShift 1 (v1H 0 ν c tr) x = _
    rw [ageShift_congr_nhds 1 hev, ageShift_const_mul, lhP_ageShift ν 1 1 hx]
    simp
  | succ M ih =>
    have hsplit : heatSumFam (M + 1) = heatSumFam M + heatTermFam (M + 1) := by
      funext ν c tr y; simp [heatSumFam, Finset.sum_range_succ]
    have hv1 : Jet.LateEq (v1H (M + 1)) (v1H M + -Jet.famEta (heatTermFam (M + 1))) := by
      unfold v1H
      rw [hsplit]
      exact v1_add_late (heatSumFam_smooth M) (heatTermFam_smooth (M + 1))
    have hsh := (Jet.B2.shift_congr hT hv1 1).trans
      (Jet.B2.shift_add hT (v1_smooth (heatSumFam_smooth M))
        (v1_smooth (heatTermFam_smooth (M + 1))) 1)
    intro ν c hν hc tr htr x hx
    have e1 : Jet.famShift 1 (v1H (M + 1)) ν c tr x =
        Jet.famShift 1 (v1H M) ν c tr x +
          ageShift 1 (-partialEta (heatTermFam (M + 1) ν c tr)) x :=
      hsh ν c hν hc tr htr hx
    have e2 := ih ν c hν hc tr htr hx
    dsimp only at e2
    have hev : (-partialEta (heatTermFam (M + 1) ν c tr)) =ᶠ[𝓝 x]
        fun y => (-meanCoeff tr (M + 1)) * lhP ν (2 * (M + 1) + 1) y := by
      refine Filter.eventuallyEq_of_mem (lhMemNhds hx) fun y hy => ?_
      change -partialEta (heatTermFam (M + 1) ν c tr) y = _
      unfold heatTermFam
      rw [partialEta_const_mul, lhPartialEta ν (2 * (M + 1)) hy]
      ring
    have e3 : ageShift 1 (-partialEta (heatTermFam (M + 1) ν c tr)) x =
        (meanCoeff tr (M + 1) * (2 * ((M + 1 : ℕ) : ℝ) + 1)) *
          lhP ν (2 * (M + 1) + 1) x := by
      rw [ageShift_congr_nhds 1 hev, ageShift_const_mul,
        lhP_ageShift ν 1 (2 * (M + 1) + 1) hx]
      push_cast; ring
    change Jet.famShift 1 (v1H (M + 1)) ν c tr x =
      ∑ i ∈ Finset.range (M + 1 + 1),
        (meanCoeff tr i * (2 * (i : ℝ) + 1)) * lhP ν (2 * i + 1) x
    rw [Finset.sum_range_succ _ (M + 1), e1, e2, e3]

theorem hH_late_sum (M : ℕ) :
    Jet.LateEq (hH M)
      (fun ν _ tr x =>
        ∑ j ∈ Finset.range (M + 1),
          (meanCoeff tr j * (2 * (j : ℝ) + 2)) * lhP ν (2 * j) x) := by
  induction M with
  | zero =>
    intro ν c _ _ tr _ x hx
    have heq : heatSumFam 0 ν c tr = fun y => meanCoeff tr 0 * lhP ν 0 y := by
      funext y; simp [heatSumFam, heatTermFam]
    change ageDefect (heatSumFam 0 ν c tr) x = _
    rw [heq, ageDefect_const_mul, lhP_ageDefect ν 0 hx]
    simp; ring
  | succ M ih =>
    have hsplit : heatSumFam (M + 1) = heatSumFam M + heatTermFam (M + 1) := by
      funext ν c tr y; simp [heatSumFam, Finset.sum_range_succ]
    have hadd := defect_add_late (heatSumFam_smooth M) (heatTermFam_smooth (M + 1))
    intro ν c hν hc tr htr x hx
    have e1 : hH (M + 1) ν c tr x =
        hH M ν c tr x + ageDefect (heatTermFam (M + 1) ν c tr) x := by
      unfold hH
      rw [hsplit]
      exact hadd ν c hν hc tr htr hx
    have e2 := ih ν c hν hc tr htr hx
    dsimp only at e2
    have e3 : ageDefect (heatTermFam (M + 1) ν c tr) x =
        (meanCoeff tr (M + 1) * (2 * ((M + 1 : ℕ) : ℝ) + 2)) *
          lhP ν (2 * (M + 1)) x := by
      unfold heatTermFam
      rw [ageDefect_const_mul, lhP_ageDefect ν (2 * (M + 1)) hx]
      push_cast; ring
    change hH (M + 1) ν c tr x =
      ∑ j ∈ Finset.range (M + 1 + 1),
        (meanCoeff tr j * (2 * (j : ℝ) + 2)) * lhP ν (2 * j) x
    rw [Finset.sum_range_succ _ (M + 1), e1, e2, e3]

theorem eta_v1H_late_sum (M : ℕ) :
    Jet.LateEq (Jet.famEta (v1H M))
      (fun ν _ tr x =>
        ∑ i ∈ Finset.range (M + 1),
          (-meanCoeff tr i) * lhP ν (2 * i + 2) x) := by
  have hT := Jet.jetToolkit
  induction M with
  | zero =>
    intro ν c _ _ tr _ x hx
    have hev : v1H 0 ν c tr =ᶠ[𝓝 x] fun y => (-meanCoeff tr 0) * lhP ν 1 y := by
      refine Filter.eventuallyEq_of_mem (lhMemNhds hx) fun y hy => ?_
      have heq : heatSumFam 0 ν c tr = fun z => meanCoeff tr 0 * lhP ν 0 z := by
        funext z; simp [heatSumFam, heatTermFam]
      change -partialEta (heatSumFam 0 ν c tr) y = _
      rw [heq, partialEta_const_mul, lhPartialEta ν 0 hy]
      ring
    change partialEta (v1H 0 ν c tr) x = _
    rw [partialEta_congr_nhds hev, partialEta_const_mul, lhPartialEta ν 1 hx]
    simp
  | succ M ih =>
    have hsplit : heatSumFam (M + 1) = heatSumFam M + heatTermFam (M + 1) := by
      funext ν c tr y; simp [heatSumFam, Finset.sum_range_succ]
    have hv1 : Jet.LateEq (v1H (M + 1)) (v1H M + -Jet.famEta (heatTermFam (M + 1))) := by
      unfold v1H
      rw [hsplit]
      exact v1_add_late (heatSumFam_smooth M) (heatTermFam_smooth (M + 1))
    have heta := (hT.eqOps _ _ hv1).2.1.trans
      (hT.linOps _ _ (v1_smooth (heatSumFam_smooth M))
        (v1_smooth (heatTermFam_smooth (M + 1))) 0).2.1
    intro ν c hν hc tr htr x hx
    have e1 : Jet.famEta (v1H (M + 1)) ν c tr x =
        Jet.famEta (v1H M) ν c tr x +
          partialEta (-partialEta (heatTermFam (M + 1) ν c tr)) x :=
      heta ν c hν hc tr htr hx
    have e2 := ih ν c hν hc tr htr hx
    dsimp only at e2
    have hev : (-partialEta (heatTermFam (M + 1) ν c tr)) =ᶠ[𝓝 x]
        fun y => (-meanCoeff tr (M + 1)) * lhP ν (2 * (M + 1) + 1) y := by
      refine Filter.eventuallyEq_of_mem (lhMemNhds hx) fun y hy => ?_
      change -partialEta (heatTermFam (M + 1) ν c tr) y = _
      unfold heatTermFam
      rw [partialEta_const_mul, lhPartialEta ν (2 * (M + 1)) hy]
      ring
    have e3 : partialEta (-partialEta (heatTermFam (M + 1) ν c tr)) x =
        (-meanCoeff tr (M + 1)) * lhP ν (2 * (M + 1) + 2) x := by
      rw [partialEta_congr_nhds hev, partialEta_const_mul,
        lhPartialEta ν (2 * (M + 1) + 1) hx]
    change Jet.famEta (v1H (M + 1)) ν c tr x =
      ∑ i ∈ Finset.range (M + 1 + 1),
        (-meanCoeff tr i) * lhP ν (2 * i + 2) x
    rw [Finset.sum_range_succ _ (M + 1), e1, e2, e3]

/-- On `ageDomain`, `heatA1 M` equals `hH M * famEta (v1H M) - v1H M * famShift 1 (v1H M)`. -/
theorem heatA1_late_quad (M : ℕ) :
    Jet.LateEq (heatA1 M)
      (hH M * Jet.famEta (v1H M) - v1H M * Jet.famShift 1 (v1H M)) := by
  intro ν c hν hc tr htr x hx
  have e_v1 := v1H_late_sum M ν c hν hc tr htr hx
  have e_sh := shift1_v1H_late_sum M ν c hν hc tr htr hx
  have e_h := hH_late_sum M ν c hν hc tr htr hx
  have e_eta := eta_v1H_late_sum M ν c hν hc tr htr hx
  dsimp only at e_v1 e_sh e_h e_eta
  change (∑ q ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
      heatA1Pair q.1 q.2 ν c tr x) =
    hH M ν c tr x * Jet.famEta (v1H M) ν c tr x -
      v1H M ν c tr x * Jet.famShift 1 (v1H M) ν c tr x
  rw [Finset.sum_product, e_h, e_eta, e_v1, e_sh,
    Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp [heatA1Pair, heatA1Term₁, heatA1Term₂]
  ring

/-- Cross/remainder algebraic expression for `remA1 M` on `ageDomain`. -/
def remA1Expr (M : ℕ) : Jet.Fam :=
  (hH M * Jet.famEta (v1R M) + hR M * Jet.famEta (v1H M) + hR M * Jet.famEta (v1R M)) -
    (v1H M * Jet.famShift 1 (v1R M) + v1R M * Jet.famShift 1 (v1H M) +
      v1R M * Jet.famShift 1 (v1R M))

/-- On `ageDomain`, `remA1 M` agrees with `remA1Expr M`. -/
theorem remA1_late (M : ℕ) :
    Jet.LateEq (remA1 M) (remA1Expr M) := by
  have hT := Jet.jetToolkit
  have hS : Jet.meanFam = heatSumFam M + remFam M := meanFam_eq_heatSum_add_rem M
  have hv1 : Jet.LateEq Jet.B2.v1bar (v1H M + v1R M) := by
    unfold Jet.B2.v1bar v1H v1R
    rw [hS]
    exact v1_add_late (heatSumFam_smooth M) (remFam_smooth M)
  have hdef : Jet.LateEq Jet.B2.hbar (hH M + hR M) := by
    unfold Jet.B2.hbar hH hR
    rw [hS]
    exact defect_add_late (heatSumFam_smooth M) (remFam_smooth M)
  have hsh : Jet.LateEq (Jet.famShift 1 Jet.B2.v1bar)
      (Jet.famShift 1 (v1H M) + Jet.famShift 1 (v1R M)) :=
    (Jet.B2.shift_congr hT hv1 1).trans
      (Jet.B2.shift_add hT (v1_smooth (heatSumFam_smooth M)) (v1_smooth (remFam_smooth M)) 1)
  have heta : Jet.LateEq (Jet.famEta Jet.B2.v1bar)
      (Jet.famEta (v1H M) + Jet.famEta (v1R M)) :=
    (hT.eqOps _ _ hv1).2.1.trans
      (hT.linOps _ _ (v1_smooth (heatSumFam_smooth M)) (v1_smooth (remFam_smooth M)) 0).2.1
  have hheat := heatA1_late_quad M
  intro ν c hν hc tr htr x hx
  have e1 : Jet.B2.v1bar ν c tr x = v1H M ν c tr x + v1R M ν c tr x :=
    hv1 ν c hν hc tr htr hx
  have e2 : Jet.B2.hbar ν c tr x = hH M ν c tr x + hR M ν c tr x :=
    hdef ν c hν hc tr htr hx
  have e3 : Jet.famShift 1 Jet.B2.v1bar ν c tr x =
      Jet.famShift 1 (v1H M) ν c tr x + Jet.famShift 1 (v1R M) ν c tr x :=
    hsh ν c hν hc tr htr hx
  have e4 : Jet.famEta Jet.B2.v1bar ν c tr x =
      Jet.famEta (v1H M) ν c tr x + Jet.famEta (v1R M) ν c tr x :=
    heta ν c hν hc tr htr hx
  have e5 : heatA1 M ν c tr x =
      hH M ν c tr x * Jet.famEta (v1H M) ν c tr x -
        v1H M ν c tr x * Jet.famShift 1 (v1H M) ν c tr x :=
    hheat ν c hν hc tr htr hx
  have e0 : meanA1 ν c tr x =
      Jet.B2.hbar ν c tr x * Jet.famEta Jet.B2.v1bar ν c tr x -
        Jet.B2.v1bar ν c tr x * Jet.famShift 1 Jet.B2.v1bar ν c tr x := by
    change -(Jet.B2.v1bar ν c tr x * ageOperator (Jet.B2.v1bar ν c tr) x) +
        Jet.B2.hbar ν c tr x * partialEta (Jet.B2.v1bar ν c tr) x -
        Jet.B2.v1bar ν c tr x * Jet.B2.v1bar ν c tr x =
      Jet.B2.hbar ν c tr x * partialEta (Jet.B2.v1bar ν c tr) x -
        Jet.B2.v1bar ν c tr x * (ageOperator (Jet.B2.v1bar ν c tr) x + 1 * Jet.B2.v1bar ν c tr x)
    ring
  change meanA1 ν c tr x - heatA1 M ν c tr x =
    (hH M ν c tr x * Jet.famEta (v1R M) ν c tr x +
        hR M ν c tr x * Jet.famEta (v1H M) ν c tr x +
        hR M ν c tr x * Jet.famEta (v1R M) ν c tr x) -
      (v1H M ν c tr x * Jet.famShift 1 (v1R M) ν c tr x +
        v1R M ν c tr x * Jet.famShift 1 (v1H M) ν c tr x +
        v1R M ν c tr x * Jet.famShift 1 (v1R M) ν c tr x)
  rw [e0, e1, e2, e3, e4, e5]
  ring

/-- For every `M, n : ℕ`, `remA1 M` belongs to `Jet.JQ n (M : ℝ)`. -/
theorem remA1_jq (M n : ℕ) : Jet.JQ n (M : ℝ) (remA1 M) := by
  have hT := Jet.jetToolkit
  have hH_sum : ∀ m, Jet.JQ m (1 / 2) (heatSumFam M) := heatSumFam_jq M
  have hR_rem : ∀ m, Jet.JQ m ((M : ℝ) + 3 / 2) (remFam M) := remFam_jq M
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hv1H : ∀ m, Jet.JQ m 1 (v1H M) := fun m => by
    have he := (hH_sum (m + 1)).eta
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by ring] at he
    exact hT.jc.qneg he
  have hv1R : ∀ m, Jet.JQ m ((M : ℝ) + 2) (v1R M) := fun m => by
    have he := (hR_rem (m + 1)).eta
    rw [show (M : ℝ) + 3 / 2 + 1 / 2 = (M : ℝ) + 2 by ring] at he
    exact hT.jc.qneg he
  have hhH : ∀ m, Jet.JQ m (1 / 2) (hH M) := fun m =>
    hT.jc.qsub (hH_sum m) (hH_sum (m + 1)).k
  have hhR : ∀ m, Jet.JQ m ((M : ℝ) + 3 / 2) (hR M) := fun m =>
    hT.jc.qsub (hR_rem m) (hR_rem (m + 1)).k
  have heta_v1H : Jet.JQ n (3 / 2) (Jet.famEta (v1H M)) := by
    have he := (hv1H (n + 1)).eta
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by ring] at he
    exact he
  have heta_v1R : Jet.JQ n ((M : ℝ) + 5 / 2) (Jet.famEta (v1R M)) := by
    have he := (hv1R (n + 1)).eta
    rw [show (M : ℝ) + 2 + 1 / 2 = (M : ℝ) + 5 / 2 by ring] at he
    exact he
  have hsh_v1H : Jet.JQ n 1 (Jet.famShift 1 (v1H M)) :=
    hT.jc.qshift 1 (hv1H (n + 1))
  have hsh_v1R : Jet.JQ n ((M : ℝ) + 2) (Jet.famShift 1 (v1R M)) :=
    hT.jc.qshift 1 (hv1R (n + 1))
  have t1 : Jet.JQ n (M : ℝ) (hH M * Jet.famEta (v1R M)) :=
    hT.jc.qmono (by linarith)
      (hT.jc.qmul (by norm_num) (by linarith) (hhH n) heta_v1R)
  have t2 : Jet.JQ n (M : ℝ) (hR M * Jet.famEta (v1H M)) :=
    hT.jc.qmono (by linarith)
      (hT.jc.qmul (by linarith) (by norm_num) (hhR n) heta_v1H)
  have t3 : Jet.JQ n (M : ℝ) (hR M * Jet.famEta (v1R M)) :=
    hT.jc.qmono (by linarith)
      (hT.jc.qmul (by linarith) (by linarith) (hhR n) heta_v1R)
  have t4 : Jet.JQ n (M : ℝ) (v1H M * Jet.famShift 1 (v1R M)) :=
    hT.jc.qmono (by linarith)
      (hT.jc.qmul (by norm_num) (by linarith) (hv1H n) hsh_v1R)
  have t5 : Jet.JQ n (M : ℝ) (v1R M * Jet.famShift 1 (v1H M)) :=
    hT.jc.qmono (by linarith)
      (hT.jc.qmul (by linarith) (by norm_num) (hv1R n) hsh_v1H)
  have t6 : Jet.JQ n (M : ℝ) (v1R M * Jet.famShift 1 (v1R M)) :=
    hT.jc.qmono (by linarith)
      (hT.jc.qmul (by linarith) (by linarith) (hv1R n) hsh_v1R)
  have hexpr : Jet.JQ n (M : ℝ) (remA1Expr M) :=
    hT.jc.qsub (hT.jc.qadd (hT.jc.qadd t1 t2) t3) (hT.jc.qadd (hT.jc.qadd t4 t5) t6)
  exact hT.jc.qcongr (remA1_late M).symm hexpr

/-- Global `C^∞` regularity and `(1 + y 2 ^ 2)`-weighted second-jet bound on `Axi.ϱ y ≤ p.R` for
`heatA1Field p M`. -/
theorem heatA1Field_wtdJet2 (p : Params) (M : ℕ) :
    WtdHeatJet2Bdd p.R (heatA1Field p M) := by
  have hR0 : 0 ≤ p.R := p.R_pos.le
  unfold heatA1Field
  refine wtdHeatJet2Bdd_sum (Finset.range (M + 1) ×ˢ Finset.range (M + 1)) fun q _ => ?_
  have h1 : WtdHeatJet2Bdd p.R (heatA1Field₁ p q.1 q.2) :=
    wtdHeatJet2Bdd_hor hR0
      ((ringEps p.R * (-(meanCoeff p.train q.1 * meanCoeff p.train q.2 * (2 * (q.1 : ℝ) + 2)))) /
        p.R ^ (2 * (q.1 + q.2) + 1))
      (q.1 + q.2)
      (wtdLineJetBdd_mul
        (wtdLineJetBdd_profileDeriv p.ν_pos (2 * q.1))
        (wtdLineJetBdd_profileDeriv p.ν_pos (2 * q.2 + 2)))
  have h2 : WtdHeatJet2Bdd p.R (heatA1Field₂ p q.1 q.2) :=
    wtdHeatJet2Bdd_hor hR0
      ((ringEps p.R * (meanCoeff p.train q.1 * meanCoeff p.train q.2 * (2 * (q.2 : ℝ) + 1))) /
        p.R ^ (2 * (q.1 + q.2) + 1))
      (q.1 + q.2)
      (wtdLineJetBdd_mul
        (wtdLineJetBdd_profileDeriv p.ν_pos (2 * q.1 + 1))
        (wtdLineJetBdd_profileDeriv p.ν_pos (2 * q.2 + 1)))
  exact wtdHeatJet2Bdd_add h1 h2

/-- Off-axis lift decomposition of `ringEps p.R * meanA1` into `heatA1Field p M` and
`ringEps p.R * remA1 M`. -/
theorem heatA1_lift_decomp (p : Params) (M : ℕ) (τ : ℝ) {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age p.R z •
        Axi.Nv p.R (fun m =>
          (ringEps p.R * meanA1 p.ν p.c p.train (chartSwap m)) • meridE0) τ z =
      heatA1Field p M z +
        Axi.age p.R z •
          Axi.Nv p.R (fun m =>
            (ringEps p.R * remA1 M p.ν p.c p.train (chartSwap m)) • meridE0) τ z := by
  have hsplit :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R * meanA1 p.ν p.c p.train (chartSwap m)) • meridE0) =
      fun m =>
        ((fun x => ringEps p.R * heatA1 M p.ν p.c p.train x) (chartSwap m) +
          (fun x => ringEps p.R * remA1 M p.ν p.c p.train x) (chartSwap m)) • meridE0 := by
    funext m
    congr 1
    dsimp [remA1]
    ring
  rw [hsplit,
    Nv_add_merid p.R
      (fun x => ringEps p.R * heatA1 M p.ν p.c p.train x)
      (fun x => ringEps p.R * remA1 M p.ν p.c p.train x)
      meridE0 τ z,
    smul_add]
  congr 1
  set S := Finset.range (M + 1) ×ˢ Finset.range (M + 1)
  have hsum_eq :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R * heatA1 M p.ν p.c p.train (chartSwap m)) • meridE0) =
      fun m =>
        (∑ q ∈ S,
          (fun x => ringEps p.R * heatA1Pair q.1 q.2 p.ν p.c p.train x) (chartSwap m)) •
            meridE0 := by
    funext m
    congr 1
    unfold heatA1
    rw [Finset.mul_sum]
  rw [hsum_eq,
    Nv_sum_merid S p.R
      (fun q x => ringEps p.R * heatA1Pair q.1 q.2 p.ν p.c p.train x)
      meridE0 τ z,
    Finset.smul_sum]
  unfold heatA1Field
  refine Finset.sum_congr rfl fun q _ => ?_
  have hpair_eq :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R * heatA1Pair q.1 q.2 p.ν p.c p.train (chartSwap m)) • meridE0) =
      fun m =>
        ((fun x => ringEps p.R * heatA1Term₁ q.1 q.2 p.ν p.c p.train x) (chartSwap m) +
          (fun x => ringEps p.R * heatA1Term₂ q.1 q.2 p.ν p.c p.train x) (chartSwap m)) •
            meridE0 := by
    funext m
    congr 1
    dsimp [heatA1Pair]
    ring
  rw [hpair_eq,
    Nv_add_merid p.R
      (fun x => ringEps p.R * heatA1Term₁ q.1 q.2 p.ν p.c p.train x)
      (fun x => ringEps p.R * heatA1Term₂ q.1 q.2 p.ν p.c p.train x)
      meridE0 τ z,
    smul_add]
  have hm1 : (2 * q.1 + 1) + (2 * q.2 + 2 + 1) = 2 * (q.1 + q.2) + 4 := by omega
  have hm2 : (2 * q.1 + 1 + 1) + (2 * q.2 + 1 + 1) = 2 * (q.1 + q.2) + 4 := by omega
  have ht1 :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R * heatA1Term₁ q.1 q.2 p.ν p.c p.train (chartSwap m)) • meridE0) =
      fun m =>
        ((ringEps p.R * (-(meanCoeff p.train q.1 * meanCoeff p.train q.2 * (2 * (q.1 : ℝ) + 2)))) *
          (lhP p.ν (2 * q.1) (chartSwap m) * lhP p.ν (2 * q.2 + 2) (chartSwap m))) • meridE0 := by
    funext m
    congr 1
    dsimp [heatA1Term₁]
    ring
  have ht2 :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R * heatA1Term₂ q.1 q.2 p.ν p.c p.train (chartSwap m)) • meridE0) =
      fun m =>
        ((ringEps p.R * (meanCoeff p.train q.1 * meanCoeff p.train q.2 * (2 * (q.2 : ℝ) + 1))) *
          (lhP p.ν (2 * q.1 + 1) (chartSwap m) * lhP p.ν (2 * q.2 + 1) (chartSwap m))) • meridE0 := by
    funext m
    congr 1
    dsimp [heatA1Term₂]
    ring
  rw [ht1, ht2,
    lift_radial_lhP_mul p.R_pos p.ν
      (ringEps p.R * (-(meanCoeff p.train q.1 * meanCoeff p.train q.2 * (2 * (q.1 : ℝ) + 2))))
      hm1 τ hz,
    lift_radial_lhP_mul p.R_pos p.ν
      (ringEps p.R * (meanCoeff p.train q.1 * meanCoeff p.train q.2 * (2 * (q.2 : ℝ) + 1)))
      hm2 τ hz]
  rfl

end LateHeatDecomp2Sub

/-- **Unconditional fixed-order late heat decomposition for `BlockA1`** (`∀ N : ℕ` outside `∃ ν₀ : ℝ`). -/
theorem meanBlockA1LateHeatSplit2_at (N : ℕ) :
    LateHeatDecomp2Sub.ScalarMeridLateHeatSplit2At
      (fun p x => ringEps p.R * LateHeatDecomp2Sub.meanA1 p.ν p.c p.train x)
      LateHeatDecomp2Sub.meridE0 N := by
  obtain ⟨ν₀, hν₀, H⟩ :=
    LateHeatDecomp2Sub.jq_late_partials_bound
      (LateHeatDecomp2Sub.QConstFam.remA1 N)
      (LateHeatDecomp2Sub.remA1_jq N)
  refine ⟨ν₀, hν₀, fun p htr hν hc hR _ => ?_⟩
  obtain ⟨hrem_sm, B, hB0, hrem_bd⟩ := H p htr hν hc hR 1
  obtain ⟨hF_sm, C_heat, _, hF_bd⟩ := LateHeatDecomp2Sub.heatA1Field_wtdJet2 p N
  have hrem_sm' :
      ContDiffOn ℝ ∞ (fun x => ringEps p.R * LateHeatDecomp2Sub.remA1 N p.ν p.c p.train x)
        ageDomain := by
    simpa [pow_one] using hrem_sm
  have hrem_bd' :
      ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
        (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
          |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (fun y => ringEps p.R * LateHeatDecomp2Sub.remA1 N p.ν p.c p.train y)))) x| ≤
            B * x.2.2 ^ (-(N : ℝ)) := by
    simpa [pow_one] using hrem_bd
  exact ⟨LateHeatDecomp2Sub.heatA1Field p N,
    fun x => ringEps p.R * LateHeatDecomp2Sub.remA1 N p.ν p.c p.train x,
    C_heat, B, hB0, hF_sm, hrem_sm',
    fun τ z hz => LateHeatDecomp2Sub.heatA1_lift_decomp p N τ hz,
    hF_bd, hrem_bd'⟩

/-- **Target `MeanBlockA1LateHeatSplit2` (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/3`).** -/
theorem meanBlockA1LateHeatSplit2 : MeanBlockA1LateHeatSplit2 :=
  meanBlockA1LateHeatSplit2_at

end UnforcedLeray.Short.PartIIIb.Concrete
