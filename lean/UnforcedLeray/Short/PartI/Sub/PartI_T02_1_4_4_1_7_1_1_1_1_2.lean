import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/2`: `HeatL2GeneratorSmooth` from an `L^2(cell)` Taylor bound

Source `the November 2 reference manuscript`, lines 261-288.

The pointwise bound `heatTaylorUniform` does not give an `L^2(cell)` bound, since `cellMeasure c`
has infinite mass (the cell is `Ioc 0 c ×ˢ univ`).  One needs transversal decay: for cylinder-smooth
`f` the transversal support is compact, so the quotient is Gaussian-small outside `|η| ≤ R + 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Leaf (`L^2(cell)` Taylor bound; source lines 261-288).** For cylinder-smooth `T` with
cylinder-smooth Laplacian, and every direction list `vs`,
`‖h⁻¹ (heatVecConvolution h (∂^vs T) - ∂^vs T) - ∂^vs (ΔT)‖_{L²(cellMeasure c)} ≤ C √h`
for `0 < h ≤ 1`.  Proof idea: `∂^vs T` and `∂^vs ΔT = Δ ∂^vs T` are cylinder-smooth with
transversal support in `|η| ≤ R`; inside `|η| ≤ R+1` use `heatTaylorUniform` (finite cell mass
`c⁻¹ · c · 2(R+1)`); outside, the quotient is bounded by `h⁻¹ e^{-a/(4h)} ≤ C √h` times a Gaussian
tail in `η`, which is square integrable. -/
def HeatCellL2Bound : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (T : Plane → Cyl.Vec2) (_hT : Sob.IsCylSmooth c T)
    (_hΔ : Sob.IsCylSmooth c (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
      + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x)) (vs : List Plane),
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 →
      eLpNorm (fun z => h⁻¹ • (HeatCylinder.heatVecConvolution h (Sob.iterD vs T) z
          - Sob.iterD vs T z)
        - Sob.iterD vs (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
            + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x) z) 2 (B0284.cellMeasure c)
        ≤ ENNReal.ofReal (C * Real.sqrt h)

theorem heatL2GeneratorSmooth_of (hB : HeatCellL2Bound) : HeatL2GeneratorSmooth := by
  intro c hc T hT hΔ vs
  obtain ⟨C, hC⟩ := hB c hc T hT hΔ vs
  set x := (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT vs).toLp (Sob.iterD vs T)
  set y := (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hΔ vs).toLp
    (Sob.iterD vs (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
      + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x))
  have hbound : ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖h⁻¹ • (HeatCylinder.heatVecL2CLM hc h x - x) - y‖ ≤ |C| * Real.sqrt h := by
    intro h h0 h1
    have hae : ((h⁻¹ • (HeatCylinder.heatVecL2CLM hc h x - x) - y : Lp Cyl.Vec2 2
        (B0284.cellMeasure c)) : Plane → Cyl.Vec2) =ᵐ[B0284.cellMeasure c]
        fun z => h⁻¹ • (HeatCylinder.heatVecConvolution h (Sob.iterD vs T) z
          - Sob.iterD vs T z)
        - Sob.iterD vs (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
            + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x) z := by
      have h1' := HeatCylinder.heatVecL2CLM_value_ae_iterD_cylSmooth hc h0 hT vs
      have hx := (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT vs).coeFn_toLp
      have hy := (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hΔ vs).coeFn_toLp
      filter_upwards [Lp.coeFn_sub (h⁻¹ • (HeatCylinder.heatVecL2CLM hc h x - x)) y,
        Lp.coeFn_smul h⁻¹ (HeatCylinder.heatVecL2CLM hc h x - x),
        Lp.coeFn_sub (HeatCylinder.heatVecL2CLM hc h x) x, h1', hx, hy] with z a b c' d e f
      simp only [a, b, c', Pi.sub_apply, Pi.smul_apply] at *
      rw [d, e, f]
    have hn : ‖h⁻¹ • (HeatCylinder.heatVecL2CLM hc h x - x) - y‖
        = (eLpNorm (fun z => h⁻¹ • (HeatCylinder.heatVecConvolution h (Sob.iterD vs T) z
          - Sob.iterD vs T z)
        - Sob.iterD vs (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
            + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x) z) 2
          (B0284.cellMeasure c)).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae hae]
    rw [hn]
    have hle := hC h h0 h1
    have hfin : ENNReal.ofReal (C * Real.sqrt h) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc _ ≤ (ENNReal.ofReal (C * Real.sqrt h)).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = max (C * Real.sqrt h) 0 := ENNReal.toReal_ofReal' 
      _ ≤ |C| * Real.sqrt h := by
          apply max_le
          · exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
          · positivity
  have hlim : Tendsto (fun h : ℝ => |C| * Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun h : ℝ => |C| * Real.sqrt h) (𝓝 0) (𝓝 (|C| * Real.sqrt 0)) :=
      (Real.continuous_sqrt.const_smul |C|).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  have : Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT one_pos
  filter_upwards [this] with h hh using hbound h hh.1 hh.2.le

end UnforcedLeray.Short.PartI
