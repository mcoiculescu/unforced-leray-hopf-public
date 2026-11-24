import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1

/-!
# Part I, task `PartI:T02/1/4/4/1/7`: the generator of the `H^3` heat semigroup on `H^5`

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1; the datum is smooth, solenoidal and lies in every `H^k`).

Target: `HeatGeneratorH5` (leaf G of `Short/PartI/Sub/T02_1_4_4_1.lean`): for `y ∈ H^5`,
`(S(νh) y - y)/h → ν Δ y` in `H^3` as `h → 0+`, where `S = heatVecH3Semigroup`.



This file does not prove the target. It reduces `HeatGeneratorH5` to three analytic leaves, each
a `Prop` below, by the three-epsilon argument (`heatGeneratorH5_of`, compiled):

* `HeatSmoothGen5`: the generator limit on smooth fields `W.ofCylSmooth` at level `5`
  (open, not proved here);
* `HeatDiffUniform5`: the uniform bound `‖h⁻¹ (S(νh) - 1) y‖_{H^3} ≤ C ‖y‖_{H^5}` for `0 < h ≤ 1`
  (open, not proved here).

The third leaf, `CylSmoothDense5` (density of smooth cylinder fields in `H^5` with exact
`W.ofCylSmooth` values), is proved in this file as `cylSmoothDense5`. The file therefore proves
`heatGeneratorH5_of_two : HeatSmoothGen5 → HeatDiffUniform5 → HeatGeneratorH5`. The target theorem
`heatGeneratorH5 : HeatGeneratorH5` is not established until the two open leaves are proved.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-! ### The smooth fields and the difference quotient -/

/-- The smooth `H^5` field attached to a cylinder-smooth profile `T` (`W.ofCylSmooth`). -/
def smoothH5Field {c : ℝ} (hc : 0 < c) (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T) :
    Cyl.H ℝ Cyl.Vec2 c 0 5 :=
  Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 5) (p := 2)
    hc T hT

/-- The difference quotient `h⁻¹ (S(νh) - 1)` applied to the `H^3` restriction of `w ∈ H^5`,
with `S = heatVecH3Semigroup`. The target `HeatGeneratorH5` is exactly the statement that this
tends to `ν • hLap c 3 y` as `h → 0+`. -/
def heatQuot (ν c : ℝ) (hc : 0 < c) (h : ℝ) (w : Cyl.H ℝ Cyl.Vec2 c 0 5) :
    Cyl.H ℝ Cyl.Vec2 c 0 3 :=
  h⁻¹ • (HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * h) hc
      (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) -
    (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3))

/-- The difference quotient is additive in its `H^5` argument. -/
theorem heatQuot_sub (ν c : ℝ) (hc : 0 < c) (h : ℝ) (w z : Cyl.H ℝ Cyl.Vec2 c 0 5) :
    heatQuot ν c hc h (w - z) = heatQuot ν c hc h w - heatQuot ν c hc h z := by
  unfold heatQuot
  simp only [map_sub]
  rw [← smul_sub]
  congr 1
  abel

/-! ### The three leaves -/

/-- **Leaf G1** (generator on smooth fields; source lines 261-288). For a cylinder-smooth profile
`T`, the difference quotient of the `H^3` heat semigroup at the smooth `H^5` field
`z = W.ofCylSmooth T` converges in `H^3` to `ν Δ z`. Proof idea: `S(νh) z - z = ν ∫_0^h S(νσ) Δz dσ`
in `H^3` (age derivative of the Gaussian kernel, `heatKernel2AgeDerivative_eq_spatialLaplacian`,
`Lib/HeatCylinder/HeatKernelAgeLaplacian.lean:145`; `hasDerivAt_heatVecConvolution_age`,
`Lib/HeatCylinder/HeatVecAgeDerivative.lean:30`), then strong continuity at zero
(`tendsto_heatVecH3Semigroup_apply_zero_ofCylSmooth`, `Lib/HeatCylinder/HeatVecH3ZeroAgeSmoothContinuity.lean:27`,
which is at level 3 only). -/
def HeatSmoothGen5 : Prop :=
  ∀ (ν c : ℝ), 0 < ν → ∀ hc : 0 < c, ∀ (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T),
    Tendsto (fun h : ℝ => heatQuot ν c hc h (smoothH5Field hc T hT))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν • hLap c 3 (smoothH5Field hc T hT)))

/-- **Leaf G2** (uniform bound; source lines 261-288). There is a constant `C` with
`‖h⁻¹ (S(νh) - 1) y‖_{H^3} ≤ C ‖y‖_{H^5}` for all `y ∈ H^5` and `0 < h ≤ 1`. Proof idea: on smooth
`y` the integral formula of `HeatSmoothGen5` gives `‖S(νh) y - y‖_{H^3} ≤ ν h ‖Δ y‖_{H^3}`
(contraction `norm_heatVecH3Semigroup_le_one`, `Lib/HeatCylinder/HeatVecH3SemigroupContraction.lean:20`),
and `‖Δ y‖_{H^3} ≤ ‖hLap c 3‖ ‖y‖_{H^5}`; the bound extends to all of `H^5` by density (`CylSmoothDense5`)
and continuity of the linear map `y ↦ heatQuot ν c hc h y`. -/
def HeatDiffUniform5 : Prop :=
  ∀ (ν c : ℝ), 0 < ν → ∀ hc : 0 < c, ∃ C : ℝ, ∀ (y : Cyl.H ℝ Cyl.Vec2 c 0 5) (h : ℝ),
    0 < h → h ≤ 1 → ‖heatQuot ν c hc h y‖ ≤ C * ‖y‖

/-- **Leaf G3** (density; source lines 261-288). Smooth cylinder fields are dense in `H^5`, with
exact `W.ofCylSmooth` representatives. Proved below as `cylSmoothDense5` from
`Sob.W.exists_seq_cylSmooth` (`Lib/SobolevC/CylDensity.lean:760`) at level `k = 5`. -/
def CylSmoothDense5 : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (y : Cyl.H ℝ Cyl.Vec2 c 0 5) (δ : ℝ), 0 < δ →
    ∃ (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T), dist y (smoothH5Field hc T hT) < δ

/-! ### The reduction: the three leaves give the generator property -/

/-- **Reduction** (three-epsilon argument). The leaves `HeatSmoothGen5`, `HeatDiffUniform5` and
`CylSmoothDense5` imply `HeatGeneratorH5`. The quotient is controlled on `y` by its value on a
nearby smooth field `z` (leaf G2 for `y - z`), the smooth field converges (leaf G1), and the
limit `ν • hLap c 3` is Lipschitz. -/
theorem heatGeneratorH5_of (hSmooth : HeatSmoothGen5) (hBound : HeatDiffUniform5)
    (hDense : CylSmoothDense5) : HeatGeneratorH5 := by
  intro ν c hν hc y
  show Tendsto (fun h : ℝ => heatQuot ν c hc h y) (𝓝[>] (0 : ℝ)) (𝓝 (ν • hLap c 3 y))
  obtain ⟨C, hC⟩ := hBound ν c hν hc
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |C| + ν * ‖hLap c 3‖ + 1 := ⟨_, rfl⟩
  have hLnn : 0 ≤ ν * ‖hLap c 3‖ := mul_nonneg hν.le (norm_nonneg (hLap c 3))
  have habs := abs_nonneg C
  have hKpos : 0 < K := by linarith
  have hKC : |C| ≤ K := by linarith
  have hKL : ν * ‖hLap c 3‖ ≤ K := by linarith
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨T, hT, hdist⟩ :=
    hDense c hc y (ε / (3 * K)) (div_pos hε (mul_pos (by norm_num) hKpos))
  have hsm := Metric.tendsto_nhds.mp (hSmooth ν c hν hc T hT) (ε / 3)
    (div_pos hε (by norm_num))
  generalize hz : smoothH5Field hc T hT = z at hdist hsm
  filter_upwards [hsm, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with h hhz hh
  obtain ⟨hpos, hlt⟩ := hh
  have hA : dist (heatQuot ν c hc h y) (heatQuot ν c hc h z) ≤ K * dist y z := by
    rw [dist_eq_norm, ← heatQuot_sub ν c hc h y z]
    calc ‖heatQuot ν c hc h (y - z)‖ ≤ C * ‖y - z‖ := hC (y - z) h hpos hlt.le
      _ ≤ |C| * ‖y - z‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ ≤ K * ‖y - z‖ := mul_le_mul_of_nonneg_right hKC (norm_nonneg _)
      _ = K * dist y z := by rw [dist_eq_norm]
  have hB : dist (ν • hLap c 3 z) (ν • hLap c 3 y) ≤ K * dist y z := by
    rw [dist_eq_norm, ← smul_sub, ← map_sub (hLap c 3), norm_smul,
      Real.norm_of_nonneg hν.le]
    have hzy : ‖z - y‖ = dist y z := by rw [dist_eq_norm, norm_sub_rev]
    calc ν * ‖hLap c 3 (z - y)‖ ≤ ν * (‖hLap c 3‖ * ‖z - y‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm (hLap c 3) (z - y)) hν.le
      _ = (ν * ‖hLap c 3‖) * dist y z := by rw [hzy]; ring
      _ ≤ K * dist y z := mul_le_mul_of_nonneg_right hKL dist_nonneg
  have hK' : K * dist y z < ε / 3 := by
    have hd := mul_lt_mul_of_pos_left hdist hKpos
    have he : K * (ε / (3 * K)) = ε / 3 := by
      field_simp
    linarith
  have t1 := dist_triangle (heatQuot ν c hc h y) (heatQuot ν c hc h z) (ν • hLap c 3 y)
  have t2 := dist_triangle (heatQuot ν c hc h z) (ν • hLap c 3 z) (ν • hLap c 3 y)
  linarith

/-! ### Leaf G3 is proved: smooth fields are dense in `H^5` -/

theorem cylSmoothDense5 : CylSmoothDense5 := by
  intro c hc y δ hδ
  obtain ⟨x, hrep, hlim⟩ := Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 5) (p := 2) hc
    (by norm_num) y
  choose u hu hae using hrep
  have hx : ∀ n, x n = Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Cyl.Vec2) (k := 5) (p := 2) hc (u n) (hu n) := by
    intro n
    apply Sob.W.value_injective
    apply Lp.ext
    have haeW := (Sob.ae_eq_wμ_iff (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))).mpr (hae n)
    filter_upwards [haeW,
      Sob.W.value_ofCylSmooth (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
        (k := 5) (p := 2) hc (u n) (hu n)] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.mp hlim) δ hδ).exists
  refine ⟨u n, hu n, ?_⟩
  unfold smoothH5Field
  rw [dist_comm, ← hx n]
  exact hn

/-- The generator property from the two remaining leaves `HeatSmoothGen5` and `HeatDiffUniform5`
(density is proved above). -/
theorem heatGeneratorH5_of_two (hSmooth : HeatSmoothGen5) (hBound : HeatDiffUniform5) :
    HeatGeneratorH5 :=
  heatGeneratorH5_of hSmooth hBound cylSmoothDense5

end UnforcedLeray.Short.PartI
