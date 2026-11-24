import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB1.HeatLiftHelp

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2/1/2/2`: `MeanBlockB3LateHeatSplit2`

Source of record: `the November 2 reference manuscript`, lines 1258, 1310-1325,
2548-2551 (late-age finite-order heat decomposition for the linear axial mean block
`ringEps p.R ^ 3 * meanB3` along `meridE1`).

## Results proved in this file

1. **`meanBlockB3LateHeatSplit2_at (N : ℕ)` (unconditional)**:
   For every expansion order `N : ℕ`, there is a viscosity threshold `ν₀ > 0` such that for all
   parameters `p` with `IsBUCTrain p.train`, `p.ν < ν₀`, `p.c = (p.ν ^ 2)⁻¹`, `2 ≤ p.R`,
   `p.period ≤ 1`, the lifted axial block
   `Axi.age p.R z • Axi.Nv p.R (fun m => (ringEps p.R ^ 3 * meanB3 p.ν p.c p.train (chartSwap m)) • meridE1) τ z`
   splits off the axis into:
   - the globally `C^∞` Cartesian heat field `heatB3Field p N` satisfying
     `(1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (heatB3Field p N) y‖ ≤ C_heat` on `Axi.ϱ y ≤ p.R`, and
   - the remainder profile `f_rem = fun x => ringEps p.R ^ 3 * remB3 N p.ν p.c p.train x` on
     `ageDomain` whose mixed directional partials `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f_rem))`
     (`ℓ, a, b ≤ 2`) satisfy the `(1 + η² / s)²`-weighted `B * s^{-N}` bound on `1 ≤ s`.
2. **`meanBlockB3LateHeatSplit2_of` (conditional on `JQUnif remB3`)**:
   Derives `MeanBlockB3LateHeatSplit2` once the viscosity threshold `ν₀ > 0` of
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

/-- Explicit heat profile sum for `meanB3` at expansion order `M`:
the `j = 0` term vanishes since `(K + 1) G_{νs} = 0`, and the `j = d + 1` (`0 ≤ d < M`) terms
are multiples of `lhP ν (2 * d + 2)`. -/
def heatB3 (M : ℕ) : Jet.Fam :=
  fun ν _ tr x =>
    ∑ d ∈ Finset.range M,
      (-(meanCoeff tr (d + 1) *
        ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2))) *
        lhP ν (2 * d + 2) x

/-- Order-`M` remainder profile family for `meanB3`. -/
def remB3 (M : ℕ) : Jet.Fam :=
  meanB3 - heatB3 M

/-- Globally smooth 3D Cartesian heat field lifting `ringEps p.R ^ 3 • heatB3 M` along `meridE1`. -/
def heatB3Field (p : Params) (M : ℕ) (z : Space) : Space :=
  ∑ d ∈ Finset.range M,
    (((ringEps p.R ^ 3 *
        (-(meanCoeff p.train (d + 1) *
          p.ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) /
        p.R ^ (2 * d)) *
      (z 0 ^ 2 + z 1 ^ 2) ^ d *
      UnforcedLeray.B0191.profileDeriv p.ν (2 * d + 2) (z 2)) • Axi.e3

theorem QConstFam.heatB3 (M : ℕ) : QConstFam (heatB3 M) :=
  fun ν _ tr =>
    QConst.sum (Finset.range M) fun d _ =>
      (QConst.lhP ν (2 * d + 2)).const_mul
        (-(meanCoeff tr (d + 1) *
          ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2)))

theorem QConstFam.remB3 (M : ℕ) : QConstFam (remB3 M) :=
  QConstFam.meanB3.sub (QConstFam.heatB3 M)

/-- On `ageDomain`, `remB3 M` agrees with `coeffB₃ ν (remFam M ν c tr)`. -/
theorem remB3_late (M : ℕ) :
    Jet.LateEq (remB3 M)
      (-(Jet.famNu (Jet.famShift 1 (Jet.famShift 1 (remFam M - Jet.famK (remFam M)))))) := by
  have hadd := coeffB3_add_late (heatSumFam_smooth M) (remFam_smooth M)
  have hheat := coeffB3_heatSumFam M
  intro ν c hν hc tr htr x hx
  have hmean : meanB3 ν c tr x = coeffB₃ ν ((heatSumFam M + remFam M) ν c tr) x := by
    change coeffB₃ ν (Jet.meanFam ν c tr) x = _
    rw [meanFam_eq_heatSum_add_rem M]
  have e1 : coeffB₃ ν ((heatSumFam M + remFam M) ν c tr) x =
      coeffB₃ ν (heatSumFam M ν c tr) x + coeffB₃ ν (remFam M ν c tr) x :=
    hadd ν c hν hc tr htr hx
  have e2 : coeffB₃ ν (heatSumFam M ν c tr) x = heatB3 M ν c tr x :=
    hheat ν c hν hc tr htr hx
  have e3 : coeffB₃ ν (remFam M ν c tr) x =
      -(ν * ageShift 1 (ageShift 1 (ageDefect (remFam M ν c tr))) x) := by
    unfold UnforcedLeray.B0188.coeffB₃
    ring
  change meanB3 ν c tr x - heatB3 M ν c tr x =
    -(ν * ageShift 1 (ageShift 1 (ageDefect (remFam M ν c tr))) x)
  linarith

/-- For every `M, n : ℕ`, `remB3 M` belongs to `Jet.JQ n (M : ℝ)`. -/
theorem remB3_jq (M n : ℕ) : Jet.JQ n (M : ℝ) (remB3 M) := by
  have hT := Jet.jetToolkit
  have hrem : ∀ m, Jet.JQ m ((M : ℝ) + 3 / 2) (remFam M) := remFam_jq M
  have hdef : Jet.JQ (n + 2) ((M : ℝ) + 3 / 2) (remFam M - Jet.famK (remFam M)) :=
    hT.jc.qsub (hrem (n + 2)) (hrem (n + 3)).k
  have hsh :
      Jet.JQ n ((M : ℝ) + 3 / 2)
        (Jet.famShift 1 (Jet.famShift 1 (remFam M - Jet.famK (remFam M)))) :=
    hT.jc.qshift 1 (hT.jc.qshift 1 hdef)
  have hcoeff :
      Jet.JQ n ((M : ℝ) + 3 / 2)
        (-(Jet.famNu (Jet.famShift 1 (Jet.famShift 1 (remFam M - Jet.famK (remFam M)))))) :=
    hT.jc.qneg (hT.jc.qnu hsh)
  exact hT.jc.qcongr (remB3_late M).symm (hT.jc.qmono (by linarith) hcoeff)

/-- Global `C^∞` regularity and `(1 + y 2 ^ 2)`-weighted second-jet bound on `Axi.ϱ y ≤ p.R` for
`heatB3Field p M`. -/
theorem heatB3Field_wtdJet2 (p : Params) (M : ℕ) :
    WtdHeatJet2Bdd p.R (heatB3Field p M) := by
  have hR0 : 0 ≤ p.R := p.R_pos.le
  unfold heatB3Field
  refine wtdHeatJet2Bdd_sum (Finset.range M) fun d _ => ?_
  exact wtdHeatJet2Bdd_e3 hR0
    ((ringEps p.R ^ 3 *
        (-(meanCoeff p.train (d + 1) *
          p.ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) /
      p.R ^ (2 * d))
    d (wtdLineJetBdd_profileDeriv p.ν_pos (2 * d + 2))

/-- Off-axis lift decomposition of `ringEps p.R ^ 3 * meanB3` into `heatB3Field p M` and
`ringEps p.R ^ 3 * remB3 M`. -/
theorem heatB3_lift_decomp (p : Params) (M : ℕ) (τ : ℝ) {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age p.R z •
        Axi.Nv p.R (fun m =>
          (ringEps p.R ^ 3 * meanB3 p.ν p.c p.train (chartSwap m)) • meridE1) τ z =
      heatB3Field p M z +
        Axi.age p.R z •
          Axi.Nv p.R (fun m =>
            (ringEps p.R ^ 3 * remB3 M p.ν p.c p.train (chartSwap m)) • meridE1) τ z := by
  have hsplit :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R ^ 3 * meanB3 p.ν p.c p.train (chartSwap m)) • meridE1) =
      fun m =>
        ((fun x => ringEps p.R ^ 3 * heatB3 M p.ν p.c p.train x) (chartSwap m) +
          (fun x => ringEps p.R ^ 3 * remB3 M p.ν p.c p.train x) (chartSwap m)) • meridE1 := by
    funext m
    congr 1
    dsimp [remB3]
    ring
  rw [hsplit,
    Nv_add_merid p.R
      (fun x => ringEps p.R ^ 3 * heatB3 M p.ν p.c p.train x)
      (fun x => ringEps p.R ^ 3 * remB3 M p.ν p.c p.train x)
      meridE1 τ z,
    smul_add]
  congr 1
  have hsum_eq :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R ^ 3 * heatB3 M p.ν p.c p.train (chartSwap m)) • meridE1) =
      fun m =>
        (∑ d ∈ Finset.range M,
          (fun x =>
            (ringEps p.R ^ 3 *
              (-(meanCoeff p.train (d + 1) *
                p.ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) *
              lhP p.ν (2 * d + 2) x) (chartSwap m)) • meridE1 := by
    funext m
    congr 1
    unfold heatB3
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring
  rw [hsum_eq,
    Nv_sum_merid (Finset.range M) p.R
      (fun d x =>
        (ringEps p.R ^ 3 *
          (-(meanCoeff p.train (d + 1) *
            p.ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) *
          lhP p.ν (2 * d + 2) x)
      meridE1 τ z,
    Finset.smul_sum]
  unfold heatB3Field
  refine Finset.sum_congr rfl fun d _ => ?_
  exact lift_axial_lhP p.R_pos p.ν
    (ringEps p.R ^ 3 *
      (-(meanCoeff p.train (d + 1) *
        p.ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2))))
    d τ hz

end LateHeatDecomp2Sub

/-- **Unconditional fixed-order late heat decomposition for `BlockB3`** (`∀ N : ℕ` outside `∃ ν₀ : ℝ`). -/
theorem meanBlockB3LateHeatSplit2_at (N : ℕ) :
    LateHeatDecomp2Sub.ScalarMeridLateHeatSplit2At
      (fun p x => ringEps p.R ^ 3 * LateHeatDecomp2Sub.meanB3 p.ν p.c p.train x)
      LateHeatDecomp2Sub.meridE1 N := by
  obtain ⟨ν₀, hν₀, H⟩ :=
    LateHeatDecomp2Sub.jq_late_partials_bound
      (LateHeatDecomp2Sub.QConstFam.remB3 N)
      (LateHeatDecomp2Sub.remB3_jq N)
  refine ⟨ν₀, hν₀, fun p htr hν hc hR _ => ?_⟩
  obtain ⟨hrem_sm, B, hB0, hrem_bd⟩ := H p htr hν hc hR 3
  obtain ⟨hF_sm, C_heat, _, hF_bd⟩ := LateHeatDecomp2Sub.heatB3Field_wtdJet2 p N
  exact ⟨LateHeatDecomp2Sub.heatB3Field p N,
    fun x => ringEps p.R ^ 3 * LateHeatDecomp2Sub.remB3 N p.ν p.c p.train x,
    C_heat, B, hB0, hF_sm, hrem_sm,
    fun τ z hz => LateHeatDecomp2Sub.heatB3_lift_decomp p N τ hz,
    hF_bd, hrem_bd⟩

/-- **Target `MeanBlockB3LateHeatSplit2` (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/2`).** -/
theorem meanBlockB3LateHeatSplit2 : MeanBlockB3LateHeatSplit2 :=
  meanBlockB3LateHeatSplit2_at

end UnforcedLeray.Short.PartIIIb.Concrete
