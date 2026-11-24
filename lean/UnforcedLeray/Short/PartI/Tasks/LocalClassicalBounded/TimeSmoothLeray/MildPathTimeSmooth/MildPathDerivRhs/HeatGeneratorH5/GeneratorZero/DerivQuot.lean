import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.L2Generator
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.LapIdentify
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeNorm

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/3`: `HeatH3DerivQuot`

Source `the November 2 reference manuscript`, lines 261-288.

For `h > 0` the `α`-derivative of the difference quotient `h⁻¹ (S(h) z - z) - Δz` agrees almost
everywhere on the centered cell with the centered transport of `h⁻¹ (S(h) x - x) - y`, where
`x = ∂^{word α} T` and `y = ∂^{word α} ΔT` are the normalized-cell classes. Its norm is bounded by
`√c` times the normalized `L²` quotient, which tends to zero by `HeatL2GeneratorSmooth`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The `H^3` restriction of the smooth `H^5` field is the smooth `H^3` field. -/
theorem smoothH5_restrict_eq {c : ℝ} (hc : 0 < c) (T : Plane → Cyl.Vec2)
    (hT : Sob.IsCylSmooth c T) :
    (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
      Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3) (p := 2)
        hc T hT := by
  apply cylH_ext
  intro α
  have e5 := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
    (k := 5) (p := 2) hc T hT (Sob.Idx.castLE (by norm_num : 3 ≤ 5) α)
  have e3 := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
    (k := 3) (p := 2) hc T hT α
  rw [Sob.W.deriv_restrict]
  unfold smoothH5Field
  apply Lp.ext
  filter_upwards [e5, e3] with x h5 h3
  rw [h5, h3, Sob.TestDomain.word_castLE]

/-- The weighted cylinder measure of the `H^k` scale is the centered cell measure. -/
theorem wMu_eq_cellμ (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW]
  simp [Cyl.wμ]

/-- Almost everywhere equality on the weighted measure gives it on the centered cell. -/
theorem ae_cell_of_ae_w {c : ℝ} {f g : Plane → Cyl.Vec2}
    (h : f =ᵐ[Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))] g) :
    f =ᵐ[Cyl.cellμ c] g := by
  rw [wMu_eq_cellμ c] at h
  exact h

/-- A scalar combination of differences of `L²` classes, a.e. pointwise. -/
theorem coeFn_comb {μ : Measure Plane} (r : ℝ) (f g k : Lp Cyl.Vec2 2 μ) :
    (⇑(r • (f - g) - k) : Plane → Cyl.Vec2) =ᵐ[μ]
      fun z => r • ((⇑f z) - (⇑g z)) - (⇑k z) := by
  filter_upwards [Lp.coeFn_sub (r • (f - g)) k, Lp.coeFn_smul r (f - g), Lp.coeFn_sub f g]
    with z h1 h2 h3
  simp only [h1, h2, h3, Pi.sub_apply, Pi.smul_apply]

/-- The norm of an `H^k`-weighted derivative class equals the norm of its centered-cell class,
when they agree a.e. on the centered cell. -/
theorem norm_eq_of_ae_cell {c : ℝ}
    {f : Lp Cyl.Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))}
    {g : Lp Cyl.Vec2 2 (Cyl.cellμ c)}
    (h : (f : Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c] (g : Plane → Cyl.Vec2)) : ‖f‖ = ‖g‖ := by
  have h1 : eLpNorm (f : Plane → Cyl.Vec2) 2 (Cyl.cellμ c) =
      eLpNorm (g : Plane → Cyl.Vec2) 2 (Cyl.cellμ c) := eLpNorm_congr_ae h
  have h2 : eLpNorm (f : Plane → Cyl.Vec2) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) =
      eLpNorm (f : Plane → Cyl.Vec2) 2 (Cyl.cellμ c) :=
    congrArg (fun m => eLpNorm (f : Plane → Cyl.Vec2) 2 m) (wMu_eq_cellμ c)
  rw [Lp.norm_def, Lp.norm_def, h2, h1]

/-- The period-normalized class of a smooth derivative is its centered-cell representative. -/
theorem centered_normalized_ae_iterD {c : ℝ} (hc : 0 < c) {U : Plane → Cyl.Vec2}
    (hU : Sob.IsCylSmooth c U) (vs : List Plane) :
    (HeatCylinder.normalizedVecToCenteredLinear hc
        ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hU vs).toLp
          (Sob.iterD vs U)) : Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c] Sob.iterD vs U := by
  let Tα := Sob.iterD vs U
  let hm := HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hU vs
  let x := hm.toLp Tα
  have hper : UnforcedLeray.B0284.IsQPeriodic c Tα := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact (hU.iterD vs).periodic z
  have hcell : HeatCylinder.normalizedVecPeriodicRep hc x =ᵐ[UnforcedLeray.B0284.cellMeasure c] Tα :=
    (HeatCylinder.normalizedVecPeriodicRep_cell_ae hc x).trans hm.coeFn_toLp
  have hglobal : HeatCylinder.normalizedVecPeriodicRep hc x =ᵐ[volume] Tα := by
    have hlift := HeatCylinder.perLift_congr_ae hc hcell
    have hleft := HeatCylinder.perLift_eq_self_of_periodic hc
      (HeatCylinder.normalizedVecPeriodicRep_periodic hc x)
    have hright := HeatCylinder.perLift_eq_self_of_periodic hc hper
    filter_upwards [hlift] with z hz
    rw [congrFun hleft z, congrFun hright z] at hz
    exact hz
  have hcenter : HeatCylinder.normalizedVecPeriodicRep hc x =ᵐ[Cyl.cellμ c] Tα :=
    ae_restrict_of_ae (s := Cyl.cell c) hglobal
  filter_upwards [HeatCylinder.centeredVecOfNormalizedVec_coe_ae hc x, hcenter] with z hC hR
  exact hC.trans hR

/-- The centered image of the normalized heat of a smooth derivative is the actual Gaussian
heat field, almost everywhere on the centered cell. -/
theorem centered_heat_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Cyl.Vec2} (hT : Sob.IsCylSmooth c T) (α : Sob.Idx 2 3) :
    (HeatCylinder.normalizedVecToCenteredLinear hc
        (HeatCylinder.heatVecL2CLM hc θ
          ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
              ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T))) :
        Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c] HeatCylinder.heatVecH3Field (c := c) (θ := θ) T α := by
  have hout := HeatCylinder.centeredVecOfNormalizedVec_heatVecL2CLM_iterD hc hθ hT α
  show (HeatCylinder.centeredVecOfNormalizedVec hc _ : Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c] _
  rw [hout]
  exact MemLp.coeFn_toLp _

/-- The `α`-derivative of the normalized-cell difference quotient, as an a.e. identity on the
centered cell. -/
theorem deriv_quot_ae {c h : ℝ} (hc : 0 < c) (hh : 0 < h) {T V : Plane → Cyl.Vec2}
    (hT : Sob.IsCylSmooth c T) (hV : Sob.IsCylSmooth c V) (α : Sob.Idx 2 3) :
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
        (h⁻¹ • (HeatCylinder.heatVecH3 hc hh hT -
            Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
              (p := 2) hc T hT) -
          Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
            (p := 2) hc V hV) : Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c]
      (HeatCylinder.normalizedVecToCenteredLinear hc
        (h⁻¹ • (HeatCylinder.heatVecL2CLM hc h
              ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T)) -
            (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T)) -
          (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hV
              ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) V)) :
        Plane → Cyl.Vec2) := by
  -- Linear splitting of the derivative, on the weighted measure.
  have hLpD : Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
      (h⁻¹ • (HeatCylinder.heatVecH3 hc hh hT -
            Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
              (p := 2) hc T hT) -
          Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
            (p := 2) hc V hV) =
      h⁻¹ • (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
          (HeatCylinder.heatVecH3 hc hh hT) -
        Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
          (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
            (p := 2) hc T hT)) -
      Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
          (p := 2) hc V hV) := by
    simp only [map_sub, map_smul]
  have hD : (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
        (h⁻¹ • (HeatCylinder.heatVecH3 hc hh hT -
            Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
              (p := 2) hc T hT) -
          Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
            (p := 2) hc V hV) : Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c]
      fun z => h⁻¹ • ((⇑(Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
          (HeatCylinder.heatVecH3 hc hh hT)) z) -
        (⇑(Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
          (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
            (p := 2) hc T hT)) z)) -
      (⇑(Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3)
          (p := 2) hc V hV)) z) := by
    apply ae_cell_of_ae_w
    rw [hLpD]
    exact coeFn_comb _ _ _ _
  -- The right-hand side, split linearly on the centered cell.
  have hR : (HeatCylinder.normalizedVecToCenteredLinear hc
        (h⁻¹ • (HeatCylinder.heatVecL2CLM hc h
              ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T)) -
            (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T)) -
          (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hV
              ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) V)) :
        Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c]
      fun z => h⁻¹ • ((⇑(HeatCylinder.normalizedVecToCenteredLinear hc
            (HeatCylinder.heatVecL2CLM hc h
              ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T)))) z) -
        (⇑(HeatCylinder.normalizedVecToCenteredLinear hc
            ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T))) z)) -
      (⇑(HeatCylinder.normalizedVecToCenteredLinear hc
        ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hV
            ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) V))) z) := by
    have hsplit : HeatCylinder.normalizedVecToCenteredLinear hc
        (h⁻¹ • (HeatCylinder.heatVecL2CLM hc h
              ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T)) -
            (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T)) -
          (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hV
              ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) V)) =
        h⁻¹ • (HeatCylinder.normalizedVecToCenteredLinear hc
            (HeatCylinder.heatVecL2CLM hc h
              ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T))) -
          HeatCylinder.normalizedVecToCenteredLinear hc
            ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT
                ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) T))) -
        HeatCylinder.normalizedVecToCenteredLinear hc
          ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hV
              ((Sob.cylinder c).word α)).toLp (Sob.iterD ((Sob.cylinder c).word α) V)) := by
      simp only [map_sub, map_smul]
    rw [hsplit]
    exact coeFn_comb _ _ _ _
  -- Pointwise identification of the four ingredients.
  filter_upwards [hD, hR, HeatCylinder.deriv_heatVecH3_ae_cell hc hh hT α,
    HeatCylinder.deriv_ofCylSmooth_ae_cell hc hT α,
    HeatCylinder.deriv_ofCylSmooth_ae_cell hc hV α,
    centered_heat_ae hc hh hT α,
    centered_normalized_ae_iterD hc hT ((Sob.cylinder c).word α),
    centered_normalized_ae_iterD hc hV ((Sob.cylinder c).word α)] with z d r e1 e2 e3 a1 a2 a3
  rw [d, r, e1, e2, e3, a1, a2, a3]

/-- **Part I, `HeatH3DerivQuot` (lines 261-288).** The `H^3`-derivative form of the generator
limit, from the `L²(cell)` generator limit `HeatL2GeneratorSmooth`. -/
theorem heatH3DerivQuot : HeatH3DerivQuot := by
  intro c hc T hT α
  obtain ⟨hΔ, hEq⟩ := heatLapSmoothIdentify5 c hc T hT
  have hL := heatL2GeneratorSmooth c hc T hT hΔ ((Sob.cylinder c).word α)
  have hbound : ∀ w : Lp Cyl.Vec2 2 (UnforcedLeray.B0284.cellMeasure c),
      ‖HeatCylinder.normalizedVecToCenteredLinear hc w‖ ≤ Real.sqrt c * ‖w‖ := by
    intro w
    calc ‖HeatCylinder.normalizedVecToCenteredLinear hc w‖
        = ‖HeatCylinder.normalizedVecToCenteredCLM hc w‖ := rfl
      _ ≤ ‖HeatCylinder.normalizedVecToCenteredCLM hc‖ * ‖w‖ :=
          (HeatCylinder.normalizedVecToCenteredCLM hc).le_opNorm w
      _ ≤ Real.sqrt c * ‖w‖ :=
          mul_le_mul_of_nonneg_right (HeatCylinder.norm_normalizedVecToCenteredCLM_le hc)
            (norm_nonneg w)
  have ha := hL.const_mul (Real.sqrt c)
  rw [mul_zero] at ha
  refine squeeze_zero_norm' ?_ ha
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpos : 0 < h := hh
  rw [norm_norm, smoothH5_restrict_eq hc T hT,
    HeatCylinder.heatVecH3Semigroup_apply_of_pos hc hpos,
    HeatCylinder.actualHeatVecH3CLM_apply_ofCylSmooth hc hpos hT, hEq]
  refine le_trans (le_of_eq (norm_eq_of_ae_cell (deriv_quot_ae hc hpos hT hΔ α))) ?_
  exact hbound _

end UnforcedLeray.Short.PartI
