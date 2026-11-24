import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs

/-!
# `BgUL4` from the `L⁴` bounds of `V` and of `r_b` (task `PartIII-b:C/ward/13/7`)

Source of record: `the November 2 reference manuscript` (73 pages).

Source 2607-2612: "The inverse-distance bounds and the all-age expansion give `D^jV ∈ C_per L⁴`.
For `w`, interpolation between its `C_per L^p` derivatives and their uniform supremum bounds gives
`D^jw ∈ C_per L⁴`.  Therefore `D^jU ∈ C_per L⁴`."  The ball split is `V = U_raw + Σ αᵢEᵢ`
(2664-2672), `r_b = w = corr z` (2505-2524, `short-bg:strong` 2525-2562).  `BgVL4` is the first
sentence, `BgRbL4` the second; `bgUL4_of` is the third (Minkowski, `fderiv` additive, `V + r_b`
smooth by `IsExactProfile.smoothU`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`D^jV ∈ C_per L⁴`, `j ≤ 1`, for the raw-plus-inlet part** (source 2563-2601, 2607-2608: the
inverse-distance bounds `|D^jF| ≲ |y|^{-1-j}` at large `|y|` of `U_raw` and of the inlet columns
`Eᵢ`, with boundedness, and the all-age expansion; `V = U_raw + Σ αᵢEᵢ`, `|αᵢ|` bounded on the
ball, 2664-2672): at the ball levels `V(τ)` is differentiable and `V(τ)`, `DV(τ)` are bounded in
`L⁴(ℝ³)` uniformly in the phase. -/
def BgVL4 : Prop :=
  AtBallLevels fun _ V _ _ => ∃ C : ℝ, ∀ τ : ℝ, Differentiable ℝ (V τ) ∧
    eLpNorm (V τ) 4 volume ≤ ENNReal.ofReal C ∧
      eLpNorm (fun y => fderiv ℝ (V τ) y) 4 volume ≤ ENNReal.ofReal C

/-- **`D^jw ∈ C_per L⁴`, `j ≤ 1`, for the correction `r_b = w`** (source 2608-2610: "interpolation
between its `C_per L^p` derivatives and their uniform supremum bounds"; `short-bg:strong`
2525-2562, `IIb.StrongRegularity`: on the ball `w ∈ L^{11/4} ∩ W^{1,∞}`; the `L^{11/4}` bound of
`Dw` is from 2538-2562): `r_b(τ)` and `Dr_b(τ)` are bounded in `L⁴(ℝ³)` uniformly in the
phase. -/
def BgRbL4 : Prop :=
  AtBallLevels fun _ _ rb _ => ∃ C : ℝ, ∀ τ : ℝ,
    eLpNorm (rb τ) 4 volume ≤ ENNReal.ofReal C ∧
      eLpNorm (fun y => fderiv ℝ (rb τ) y) 4 volume ≤ ENNReal.ofReal C

theorem bgUL4_of (hV : BgVL4) (hR : BgRbL4) : BgUL4 := by
  refine AtBallLevels.mono' (AtBallLevels.and hV hR) ?_
  intro p V rb pres hU ⟨⟨CV, hCV⟩, ⟨CR, hCR⟩⟩
  refine ⟨|CV| + |CR|, fun τ => ?_⟩
  obtain ⟨hVd, hV0, hV1⟩ := hCV τ
  obtain ⟨hR0, hR1⟩ := hCR τ
  have hUd : Differentiable ℝ (fun y => V τ y + rb τ y) := by
    have h1 : Differentiable ℝ (fun x : ℝ × Space => (fun τ y => V τ y + rb τ y) x.1 x.2) :=
      hU.smoothU.differentiable (by simp)
    exact h1.comp ((differentiable_const τ).prodMk differentiable_id)
  have hRd : Differentiable ℝ (rb τ) := by
    have : rb τ = fun y => (V τ y + rb τ y) - V τ y := by funext y; simp
    rw [this]; exact hUd.sub hVd
  have hCsum : ENNReal.ofReal (|CV| + |CR|) = ENNReal.ofReal |CV| + ENNReal.ofReal |CR| :=
    ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  have hle1 : ENNReal.ofReal CV ≤ ENNReal.ofReal |CV| := ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hle2 : ENNReal.ofReal CR ≤ ENNReal.ofReal |CR| := ENNReal.ofReal_le_ofReal (le_abs_self _)
  constructor
  · calc eLpNorm (fun y => V τ y + rb τ y) 4 volume
        ≤ eLpNorm (V τ) 4 volume + eLpNorm (rb τ) 4 volume :=
          eLpNorm_add_le hVd.continuous.aestronglyMeasurable hRd.continuous.aestronglyMeasurable
            (by norm_num)
      _ ≤ _ := by rw [hCsum]; exact add_le_add (hV0.trans hle1) (hR0.trans hle2)
  · have hfd : (fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y) =
        fun y => fderiv ℝ (V τ) y + fderiv ℝ (rb τ) y := by
      funext y; exact fderiv_add (hVd y) (hRd y)
    rw [hfd]
    have m1 : AEStronglyMeasurable (fun y => fderiv ℝ (V τ) y) volume :=
      (measurable_fderiv ℝ (V τ)).aestronglyMeasurable
    have m2 : AEStronglyMeasurable (fun y => fderiv ℝ (rb τ) y) volume :=
      (measurable_fderiv ℝ (rb τ)).aestronglyMeasurable
    have hadd := eLpNorm_add_le (p := (4 : ℝ≥0∞)) m1 m2 (by norm_num)
    refine hadd.trans ?_
    rw [hCsum]
    exact add_le_add (hV1.trans hle1) (hR1.trans hle2)

end UnforcedLeray.Short.PartIIIb.Concrete
