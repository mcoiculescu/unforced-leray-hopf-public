import UnforcedLeray.Short.PartI.Sub.T02_1_3

/-!
# Part I, task `PartI:T02/1/3`: density of smooth periodic fields at level `k + 3`

Source of record: `the November 2 reference manuscript`, lines 261-288
(approximation by smooth periodic fields).

The target is `CylSmoothDensity` (`Short/PartI/Sub/T02_1_3.lean`, line 99).  It is the level
`k + 3` analogue of `UnforcedLeray.TrainB.exists_smoothVecH3_sequence`
(`Lib/TrainB/P0RoughH3.lean:19`), proved by the same argument with the sequential density lemma
`Sob.W.exists_seq_cylSmooth` (`Lib/SobolevC/CylDensity.lean:760`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartI

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Density of smooth periodic fields at level `k + 3`, with exact `W.ofCylSmooth`
representatives. -/
theorem cylSmoothDensity : CylSmoothDensity := by
  unfold CylSmoothDensity
  intro c hc k x
  obtain ⟨y, hrep, hlim⟩ := Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
    (k := k + 3) (p := 2) hc (by norm_num) x
  choose u hu hae using hrep
  refine ⟨u, hu, ?_⟩
  have hy : ∀ n, y n = Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 3) (p := 2) hc (u n) (hu n) := by
    intro n
    apply Sob.W.value_injective
    apply Lp.ext
    have haeW := (Sob.ae_eq_wμ_iff (Sob.cylinder c).μ
      (Cyl.ρwW c ^ (0 : ℝ))).mpr (hae n)
    filter_upwards [haeW,
      Sob.W.value_ofCylSmooth (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 3) (p := 2) hc (u n) (hu n)] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  exact hlim.congr (fun n => hy n)

end UnforcedLeray.Short.PartI
