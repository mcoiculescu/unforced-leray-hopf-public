import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB1.HeatLiftHelp

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2/1/2/1`: `MeanBlockB1LateHeatSplit2`

Source of record: `the November 2 reference manuscript`, lines 1255, 1310-1325,
2548-2551 (late-age finite-order heat decomposition for the linear radial mean block
`ringEps p.R ^ 2 * meanB1` along `meridE0`).

## Results proved in this file

1. **`meanBlockB1LateHeatSplit2_at (N : ℕ)` (unconditional)**:
   For every expansion order `N : ℕ`, there is a viscosity threshold `ν₀ > 0` such that for all
   parameters `p` with `IsBUCTrain p.train`, `p.ν < ν₀`, `p.c = (p.ν ^ 2)⁻¹`, `2 ≤ p.R`,
   `p.period ≤ 1`, the lifted radial block
   `Axi.age p.R z • Axi.Nv p.R (fun m => (ringEps p.R ^ 2 * meanB1 p.ν p.c p.train (chartSwap m)) • meridE0) τ z`
   splits off the axis into:
   - the globally `C^∞` Cartesian heat field `heatB1Field p N` satisfying
     `(1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (heatB1Field p N) y‖ ≤ C_heat` on `Axi.ϱ y ≤ p.R`, and
   - the remainder profile `f_rem = fun x => ringEps p.R ^ 2 * remB1 N p.ν p.c p.train x` on
     `ageDomain` whose mixed directional partials `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f_rem))`
     (`ℓ, a, b ≤ 2`) satisfy the `(1 + η² / s)²`-weighted `B * s^{-N}` bound on `1 ≤ s`.
2. **`meanBlockB1LateHeatSplit2_of` (conditional on `JQUnif remB1`)**:
   Derives `MeanBlockB1LateHeatSplit2` once the viscosity threshold `ν₀ > 0` of
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

/-- Explicit heat profile sum for `meanB1` at expansion order `M`:
the `j = 0` term vanishes since `(K + 2) ∂_η G_{νs} = 0`, and the `j = d + 1` (`0 ≤ d < M`) terms
are multiples of `lhP ν (2 * d + 3)`. -/
def heatB1 (M : ℕ) : Jet.Fam :=
  fun ν _ tr x =>
    ∑ d ∈ Finset.range M,
      (meanCoeff tr (d + 1) *
        (ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2))) *
        lhP ν (2 * d + 3) x

/-- Order-`M` remainder profile family for `meanB1`. -/
def remB1 (M : ℕ) : Jet.Fam :=
  meanB1 - heatB1 M

/-- Globally smooth 3D Cartesian heat field lifting `ringEps p.R ^ 2 • heatB1 M` along `meridE0`. -/
def heatB1Field (p : Params) (M : ℕ) (z : Space) : Space :=
  ∑ d ∈ Finset.range M,
    (((ringEps p.R ^ 2 *
        (meanCoeff p.train (d + 1) *
          (p.ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) /
        p.R ^ (2 * d + 1)) *
      (z 0 ^ 2 + z 1 ^ 2) ^ d *
      UnforcedLeray.B0191.profileDeriv p.ν (2 * d + 3) (z 2)) • Axi.hor z

theorem QConstFam.heatB1 (M : ℕ) : QConstFam (heatB1 M) :=
  fun ν _ tr =>
    QConst.sum (Finset.range M) fun d _ =>
      (QConst.lhP ν (2 * d + 3)).const_mul
        (meanCoeff tr (d + 1) * (ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2)))

theorem QConstFam.remB1 (M : ℕ) : QConstFam (remB1 M) :=
  QConstFam.meanB1.sub (QConstFam.heatB1 M)

/-- On `ageDomain`, `remB1 M` agrees with `coeffB₁ ν (remFam M ν c tr)`. -/
theorem remB1_late (M : ℕ) :
    Jet.LateEq (remB1 M) (-(Jet.famNu (Jet.famK (Jet.famShift 2 (-Jet.famEta (remFam M)))))) := by
  have hadd := coeffB1_add_late (heatSumFam_smooth M) (remFam_smooth M)
  have hheat := coeffB1_heatSumFam M
  intro ν c hν hc tr htr x hx
  have hmean : meanB1 ν c tr x = coeffB₁ ν ((heatSumFam M + remFam M) ν c tr) x := by
    change coeffB₁ ν (Jet.meanFam ν c tr) x = _
    rw [meanFam_eq_heatSum_add_rem M]
  have e1 : coeffB₁ ν ((heatSumFam M + remFam M) ν c tr) x =
      coeffB₁ ν (heatSumFam M ν c tr) x + coeffB₁ ν (remFam M ν c tr) x :=
    hadd ν c hν hc tr htr hx
  have e2 : coeffB₁ ν (heatSumFam M ν c tr) x = heatB1 M ν c tr x :=
    hheat ν c hν hc tr htr hx
  have e3 : coeffB₁ ν (remFam M ν c tr) x =
      -(ν * ageOperator (ageShift 2 (streamV1 (remFam M ν c tr))) x) := by
    unfold UnforcedLeray.B0188.coeffB₁
    ring
  change meanB1 ν c tr x - heatB1 M ν c tr x =
    -(ν * ageOperator (ageShift 2 (streamV1 (remFam M ν c tr))) x)
  linarith

/-- For every `M, n : ℕ`, `remB1 M` belongs to `Jet.JQ n (M : ℝ)`. -/
theorem remB1_jq (M n : ℕ) : Jet.JQ n (M : ℝ) (remB1 M) := by
  have hT := Jet.jetToolkit
  have hrem : ∀ m, Jet.JQ m ((M : ℝ) + 3 / 2) (remFam M) := remFam_jq M
  have hv1 : Jet.JQ (n + 2) ((M : ℝ) + 2) (-Jet.famEta (remFam M)) := by
    have he := (hrem (n + 3)).eta
    have hexp : (M : ℝ) + 3 / 2 + 1 / 2 = (M : ℝ) + 2 := by ring
    rw [hexp] at he
    exact hT.jc.qneg he
  have hsh : Jet.JQ (n + 1) ((M : ℝ) + 2) (Jet.famShift 2 (-Jet.famEta (remFam M))) :=
    hT.jc.qshift 2 hv1
  have hk : Jet.JQ n ((M : ℝ) + 2) (Jet.famK (Jet.famShift 2 (-Jet.famEta (remFam M)))) :=
    hsh.k
  have hcoeff :
      Jet.JQ n ((M : ℝ) + 2) (-(Jet.famNu (Jet.famK (Jet.famShift 2 (-Jet.famEta (remFam M)))))) :=
    hT.jc.qneg (hT.jc.qnu hk)
  exact hT.jc.qcongr (remB1_late M).symm (hT.jc.qmono (by linarith) hcoeff)

/-- Global `C^∞` regularity and `(1 + y 2 ^ 2)`-weighted second-jet bound on `Axi.ϱ y ≤ p.R` for
`heatB1Field p M`. -/
theorem heatB1Field_wtdJet2 (p : Params) (M : ℕ) :
    WtdHeatJet2Bdd p.R (heatB1Field p M) := by
  have hR0 : 0 ≤ p.R := p.R_pos.le
  unfold heatB1Field
  refine wtdHeatJet2Bdd_sum (Finset.range M) fun d _ => ?_
  exact wtdHeatJet2Bdd_hor hR0
    ((ringEps p.R ^ 2 *
        (meanCoeff p.train (d + 1) *
          (p.ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) /
      p.R ^ (2 * d + 1))
    d (wtdLineJetBdd_profileDeriv p.ν_pos (2 * d + 3))

/-- Off-axis lift decomposition of `ringEps p.R ^ 2 * meanB1` into `heatB1Field p M` and
`ringEps p.R ^ 2 * remB1 M`. -/
theorem heatB1_lift_decomp (p : Params) (M : ℕ) (τ : ℝ) {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age p.R z •
        Axi.Nv p.R (fun m =>
          (ringEps p.R ^ 2 * meanB1 p.ν p.c p.train (chartSwap m)) • meridE0) τ z =
      heatB1Field p M z +
        Axi.age p.R z •
          Axi.Nv p.R (fun m =>
            (ringEps p.R ^ 2 * remB1 M p.ν p.c p.train (chartSwap m)) • meridE0) τ z := by
  have hsplit :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R ^ 2 * meanB1 p.ν p.c p.train (chartSwap m)) • meridE0) =
      fun m =>
        ((fun x => ringEps p.R ^ 2 * heatB1 M p.ν p.c p.train x) (chartSwap m) +
          (fun x => ringEps p.R ^ 2 * remB1 M p.ν p.c p.train x) (chartSwap m)) • meridE0 := by
    funext m
    congr 1
    dsimp [remB1]
    ring
  rw [hsplit,
    Nv_add_merid p.R
      (fun x => ringEps p.R ^ 2 * heatB1 M p.ν p.c p.train x)
      (fun x => ringEps p.R ^ 2 * remB1 M p.ν p.c p.train x)
      meridE0 τ z,
    smul_add]
  congr 1
  have hsum_eq :
      (fun m : ℝ × (ℝ × ℝ) =>
        (ringEps p.R ^ 2 * heatB1 M p.ν p.c p.train (chartSwap m)) • meridE0) =
      fun m =>
        (∑ d ∈ Finset.range M,
          (fun x =>
            (ringEps p.R ^ 2 *
              (meanCoeff p.train (d + 1) *
                (p.ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) *
              lhP p.ν (2 * d + 3) x) (chartSwap m)) • meridE0 := by
    funext m
    congr 1
    unfold heatB1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring
  rw [hsum_eq,
    Nv_sum_merid (Finset.range M) p.R
      (fun d x =>
        (ringEps p.R ^ 2 *
          (meanCoeff p.train (d + 1) *
            (p.ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) *
          lhP p.ν (2 * d + 3) x)
      meridE0 τ z,
    Finset.smul_sum]
  unfold heatB1Field
  refine Finset.sum_congr rfl fun d _ => ?_
  exact lift_radial_lhP p.R_pos p.ν
    (ringEps p.R ^ 2 *
      (meanCoeff p.train (d + 1) *
        (p.ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2))))
    d τ hz

end LateHeatDecomp2Sub

/-- **Unconditional fixed-order late heat decomposition for `BlockB1`** (`∀ N : ℕ` outside `∃ ν₀ : ℝ`). -/
theorem meanBlockB1LateHeatSplit2_at (N : ℕ) :
    LateHeatDecomp2Sub.ScalarMeridLateHeatSplit2At
      (fun p x => ringEps p.R ^ 2 * LateHeatDecomp2Sub.meanB1 p.ν p.c p.train x)
      LateHeatDecomp2Sub.meridE0 N := by
  obtain ⟨ν₀, hν₀, H⟩ :=
    LateHeatDecomp2Sub.jq_late_partials_bound
      (LateHeatDecomp2Sub.QConstFam.remB1 N)
      (LateHeatDecomp2Sub.remB1_jq N)
  refine ⟨ν₀, hν₀, fun p htr hν hc hR _ => ?_⟩
  obtain ⟨hrem_sm, B, hB0, hrem_bd⟩ := H p htr hν hc hR 2
  obtain ⟨hF_sm, C_heat, _, hF_bd⟩ := LateHeatDecomp2Sub.heatB1Field_wtdJet2 p N
  exact ⟨LateHeatDecomp2Sub.heatB1Field p N,
    fun x => ringEps p.R ^ 2 * LateHeatDecomp2Sub.remB1 N p.ν p.c p.train x,
    C_heat, B, hB0, hF_sm, hrem_sm,
    fun τ z hz => LateHeatDecomp2Sub.heatB1_lift_decomp p N τ hz,
    hF_bd, hrem_bd⟩

/-- **Target `MeanBlockB1LateHeatSplit2` (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/1`).** -/
theorem meanBlockB1LateHeatSplit2 : MeanBlockB1LateHeatSplit2 :=
  meanBlockB1LateHeatSplit2_at

end UnforcedLeray.Short.PartIIIb.Concrete
