import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.CellBridge

/-!
# Part I, task `PartI:T07/Agmon`: the scale-invariant Agmon step on the cylinder

Source of record: `the November 2 reference manuscript`, lines 366-374.
Target `cylAgmonL2_proof : CylAgmonL2`: for smooth `c`-periodic `f` with `f, Df, D²f ∈ L²(cell)`,
`‖f z‖ₑ² ≤ 2 (c⁻¹ ‖f‖₂ ‖Df‖₂ + ‖Df‖₂² + ‖f‖₂ ‖D²f‖₂)`.

Proof (B0151.enorm_le_H2 on the cell `(0, c]`, with the line bound for `2 f ∂_q f`):
circle bound in `q` (`B0151.sq_le_circle`), the `η`-line bound for `f²` (`B0151.circle_sq_le`),
and the `η`-line bound for `u = 2 f ∂_q f` (`agmon_line`). Transfer between `(0, c]` and the centred
cell by `CylCellBridge` (`memLp_cellMeasure_iff`, `eLpNorm_cellMeasure_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.GaussianVortex (partialX partialY)

/-- The norm of the `j`-th Fréchet derivative of a `c`-periodic function is `c`-periodic. -/
theorem agmon_jet_periodic {c : ℝ} {f : Cyl.Plane → ℝ} (hper : Cyl.IsPeriodic c f) (j : ℕ) :
    Cyl.IsPeriodic c (fun z => ‖Train.jet j f z‖) := by
  have hshift : (fun w : Cyl.Plane => f (w + ((c, 0) : Cyl.Plane))) = f := by
    funext w
    rw [show w + ((c, 0) : Cyl.Plane) = (w.1 + c, w.2) from by ext <;> simp]
    exact hper w
  intro z
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) j ((c, 0) : Cyl.Plane) z
  rw [hshift] at h
  have hz : z + ((c, 0) : Cyl.Plane) = (z.1 + c, z.2) := by ext <;> simp
  show ‖iteratedFDeriv ℝ j f (z.1 + c, z.2)‖ = ‖iteratedFDeriv ℝ j f z‖
  rw [← hz, ← h]

/-- The norm of the `j`-th Fréchet derivative of a smooth function is continuous. -/
theorem agmon_jet_continuous {f : Cyl.Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    Continuous (fun z => ‖Train.jet j f z‖) := by
  have hc : Continuous (fun z => iteratedFDeriv ℝ j f z) :=
    hf.continuous_iteratedFDeriv (by simp)
  exact hc.norm

/-- Transfer of the `L²` norm of a jet from the library cell to the centred cell. -/
theorem agmon_eLpNorm_jet {c : ℝ} (hc : 0 < c) {f : Cyl.Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Cyl.IsPeriodic c f) (j : ℕ) :
    eLpNorm (Train.jet j f) 2 (B0151.cellMeasure c) = eLpNorm (Train.jet j f) 2 (Cyl.cellμ c) := by
  have h := eLpNorm_cellMeasure_eq hc (g := fun z => ‖Train.jet j f z‖)
    (agmon_jet_continuous hf j).measurable (agmon_jet_periodic hper j) 2
  simpa only [eLpNorm_norm] using h

/-- The product rule for the `η`-derivative of `2 f ∂_q f`. -/
theorem agmon_partialY_mul {f : Cyl.Plane → ℝ} (hf : ContDiff ℝ ∞ f) (q t : ℝ) :
    partialY (fun w => 2 * f w * partialX f w) (q, t) =
      2 * partialY f (q, t) * partialX f (q, t) + 2 * f (q, t) * partialY (partialX f) (q, t) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hX : ContDiff ℝ ∞ (partialX f) := B0151.contDiff_partialX_infty hf
  have hdX : Differentiable ℝ (partialX f) := hX.differentiable (by simp)
  have hdu : Differentiable ℝ (fun w => 2 * f w * partialX f w) :=
    (hd.const_mul 2).mul hdX
  have h1 : HasDerivAt (fun y => f (q, y)) (partialY f (q, t)) t :=
    B0151.hasDerivAt_sliceY hd q t
  have h2 : HasDerivAt (fun y => partialX f (q, y)) (partialY (partialX f) (q, t)) t :=
    B0151.hasDerivAt_sliceY hdX q t
  have hs : HasDerivAt (fun y => 2 * f (q, y) * partialX f (q, y))
      (2 * partialY f (q, t) * partialX f (q, t) + 2 * f (q, t) * partialY (partialX f) (q, t)) t := by
    have h3 := (h1.mul h2).const_mul 2
    have hfun : (fun y => 2 * f (q, y) * partialX f (q, y)) =
        fun y => 2 * (f (q, y) * partialX f (q, y)) := by
      funext y
      ring
    rw [hfun]
    refine h3.congr_deriv ?_
    ring
  exact (B0151.hasDerivAt_sliceY hdu q t).unique hs

/-- The `η`-line bound on the library cell: `|u(q₀, η)|` is bounded by the cell integral of
`|∂_η u|`, integrated over `q ∈ (0, c]`. -/
theorem agmon_line {c : ℝ} (u : Cyl.Plane → ℝ) (hu : ContDiff ℝ 1 u)
    (hi : Integrable u (B0151.cellMeasure c)) (hiy : Integrable (partialY u) (B0151.cellMeasure c))
    (η : ℝ) :
    ∫⁻ s in Ioc 0 c, ‖u (s, η)‖ₑ ≤ ∫⁻ z, ‖partialY u z‖ₑ ∂(B0151.cellMeasure c) := by
  have hd : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hcy : Continuous (partialY u) := B0151.continuous_partialY hu
  have hm : Measurable fun z => ‖partialY u z‖ₑ := hcy.measurable.enorm
  rw [B0151.lintegral_cell c hm]
  apply lintegral_mono_ae
  filter_upwards [B0151.ae_integrable_slice hi, B0151.ae_integrable_slice hiy] with q hq1 hq2
  have key := B0151.ofReal_abs_le_lintegral_deriv (φ := fun t => u (q, t))
    (φ' := fun t => partialY u (q, t)) (fun t => B0151.hasDerivAt_sliceY hd q t) hq2 hq1 η
  rw [Real.enorm_eq_ofReal_abs]
  exact key

/-- **Target** `cylAgmonL2_proof` (source lines 366-374): the scale-invariant Agmon step. -/
theorem cylAgmonL2_proof : UnforcedLeray.Short.PartI.CylAgmonL2 := by
  unfold UnforcedLeray.Short.PartI.CylAgmonL2
  intro c hc f hf hper h0 h1 h2 z
  obtain ⟨q0, η0⟩ := z
  -- smoothness and continuity
  have hF1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hX : ContDiff ℝ ∞ (partialX f) := B0151.contDiff_partialX_infty hf
  have hX1 : ContDiff ℝ 1 (partialX f) := hX.of_le (by simp)
  have hcf : Continuous f := hf.continuous
  have hcX : Continuous (partialX f) := B0151.continuous_partialX hF1
  have hcY : Continuous (partialY f) := B0151.continuous_partialY hF1
  have hcXY : Continuous (partialY (partialX f)) := B0151.continuous_partialY hX1
  have hmX : Measurable (partialX f) := hcX.measurable
  have hmY : Measurable (partialY f) := hcY.measurable
  have hmXY : Measurable (partialY (partialX f)) := hcXY.measurable
  -- periodicity of the derivatives
  have hperX : Cyl.IsPeriodic c (partialX f) := hper.partialQ
  have hperY : Cyl.IsPeriodic c (partialY f) := hper.partialEta
  have hperXY : Cyl.IsPeriodic c (partialY (partialX f)) := hperX.partialEta
  -- pointwise bounds of the derivatives by the jets (CylJetWord)
  have hJ : ∀ (j : ℕ) (w : List Bool), w.length = j → ∀ z : Cyl.Plane,
      |B0151.derivWord w f z| ≤ ‖Train.jet j f z‖ :=
    fun j w hw z => (cylJetWord_proof f hf j z).1 w hw
  have hXb : ∀ z : Cyl.Plane, ‖partialX f z‖ ≤ ‖Train.jet 1 f z‖ := fun z => by
    rw [Real.norm_eq_abs]
    exact hJ 1 [true] rfl z
  have hYb : ∀ z : Cyl.Plane, ‖partialY f z‖ ≤ ‖Train.jet 1 f z‖ := fun z => by
    rw [Real.norm_eq_abs]
    exact hJ 1 [false] rfl z
  have hXYb : ∀ z : Cyl.Plane, ‖partialY (partialX f) z‖ ≤ ‖Train.jet 2 f z‖ := fun z => by
    rw [Real.norm_eq_abs]
    exact hJ 2 [false, true] rfl z
  -- memberships on the centred cell
  have hX1c : MemLp (partialX f) 2 (Cyl.cellμ c) :=
    h1.norm.of_le hmX.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [norm_norm] using hXb z)
  have hY1c : MemLp (partialY f) 2 (Cyl.cellμ c) :=
    h1.norm.of_le hmY.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [norm_norm] using hYb z)
  have hXY2c : MemLp (partialY (partialX f)) 2 (Cyl.cellμ c) :=
    h2.norm.of_le hmXY.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [norm_norm] using hXYb z)
  -- memberships on the library cell (0, c]
  have hF0 : MemLp f 2 (B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc hcf.measurable hper 2).2 h0
  have hX0 : MemLp (partialX f) 2 (B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc hmX hperX 2).2 hX1c
  have hY0 : MemLp (partialY f) 2 (B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc hmY hperY 2).2 hY1c
  have hXY0 : MemLp (partialY (partialX f)) 2 (B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc hmXY hperXY 2).2 hXY2c
  -- norm transfers
  have eF : eLpNorm f 2 (B0151.cellMeasure c) = Train.cellL2 c f :=
    eLpNorm_cellMeasure_eq hc hcf.measurable hper 2
  have eD1 : eLpNorm (Train.jet 1 f) 2 (B0151.cellMeasure c) = Train.cellL2 c (Train.jet 1 f) :=
    agmon_eLpNorm_jet hc hf hper 1
  have eD2 : eLpNorm (Train.jet 2 f) 2 (B0151.cellMeasure c) = Train.cellL2 c (Train.jet 2 f) :=
    agmon_eLpNorm_jet hc hf hper 2
  have hX0le : eLpNorm (partialX f) 2 (B0151.cellMeasure c) ≤
      eLpNorm (Train.jet 1 f) 2 (B0151.cellMeasure c) := eLpNorm_mono hXb
  have hY0le : eLpNorm (partialY f) 2 (B0151.cellMeasure c) ≤
      eLpNorm (Train.jet 1 f) 2 (B0151.cellMeasure c) := eLpNorm_mono hYb
  have hXY0le : eLpNorm (partialY (partialX f)) 2 (B0151.cellMeasure c) ≤
      eLpNorm (Train.jet 2 f) 2 (B0151.cellMeasure c) := eLpNorm_mono hXYb
  -- the circle bound in q and the line bound in η for f²
  have hpL : B0151.IsPeriodicQ c f := fun q η => hper (q, η)
  have hcirc := B0151.sq_le_circle hc hF1 hpL q0 η0
  have hI1 : ∫⁻ s in Ioc 0 c, ‖f (s, η0)‖ₑ ^ 2 ≤
      2 * (eLpNorm f 2 (B0151.cellMeasure c) * eLpNorm (partialY f) 2 (B0151.cellMeasure c)) :=
    (B0151.circle_sq_le hF1 hF0 hY0 η0).trans (B0151.lintegral_two_mul_le hF0.1 hY0.1)
  -- the line bound for u = 2 f ∂_q f
  have hu1 : ContDiff ℝ 1 (fun w => 2 * f w * partialX f w) :=
    (contDiff_const.mul hF1).mul hX1
  have hiu : Integrable (fun w => 2 * f w * partialX f w) (B0151.cellMeasure c) := by
    refine ((hF0.integrable_mul hX0).const_mul 2).congr (ae_of_all _ fun w => ?_)
    show 2 * (f w * partialX f w) = 2 * f w * partialX f w
    ring
  have hformula : partialY (fun w => 2 * f w * partialX f w) =
      fun z => 2 * partialY f z * partialX f z + 2 * f z * partialY (partialX f) z := by
    funext z
    obtain ⟨q, t⟩ := z
    exact agmon_partialY_mul hf q t
  have hiyu : Integrable (partialY (fun w => 2 * f w * partialX f w)) (B0151.cellMeasure c) := by
    rw [hformula]
    have a1 : Integrable (fun z => 2 * partialY f z * partialX f z) (B0151.cellMeasure c) := by
      refine ((hY0.integrable_mul hX0).const_mul 2).congr (ae_of_all _ fun z => ?_)
      show 2 * (partialY f z * partialX f z) = 2 * partialY f z * partialX f z
      ring
    have a2 : Integrable (fun z => 2 * f z * partialY (partialX f) z) (B0151.cellMeasure c) := by
      refine ((hF0.integrable_mul hXY0).const_mul 2).congr (ae_of_all _ fun z => ?_)
      show 2 * (f z * partialY (partialX f) z) = 2 * f z * partialY (partialX f) z
      ring
    exact a1.add a2
  have hline : ∫⁻ s in Ioc 0 c, ‖2 * f (s, η0) * partialX f (s, η0)‖ₑ ≤
      ∫⁻ z, ‖partialY (fun w => 2 * f w * partialX f w) z‖ₑ ∂(B0151.cellMeasure c) :=
    agmon_line (c := c) (fun w => 2 * f w * partialX f w) hu1 hiu hiyu η0
  -- pointwise bound of the η-derivative of u
  have hpt : ∀ z : Cyl.Plane, ‖partialY (fun w => 2 * f w * partialX f w) z‖ₑ ≤
      ‖2 * partialY f z * partialX f z‖ₑ + ‖2 * f z * partialY (partialX f) z‖ₑ := by
    intro z
    obtain ⟨q, t⟩ := z
    rw [agmon_partialY_mul hf q t]
    exact enorm_add_le _ _
  have hmA : Measurable (fun z : Cyl.Plane => ‖2 * partialY f z * partialX f z‖ₑ) :=
    (((continuous_const.mul hcY).mul hcX).enorm).measurable
  have hmB : Measurable (fun z : Cyl.Plane => ‖2 * f z * partialY (partialX f) z‖ₑ) :=
    (((continuous_const.mul hcf).mul hcXY).enorm).measurable
  have hI2 : ∫⁻ z, ‖partialY (fun w => 2 * f w * partialX f w) z‖ₑ ∂(B0151.cellMeasure c) ≤
      2 * (eLpNorm (partialY f) 2 (B0151.cellMeasure c) * eLpNorm (partialX f) 2 (B0151.cellMeasure c)) +
        2 * (eLpNorm f 2 (B0151.cellMeasure c) *
          eLpNorm (partialY (partialX f)) 2 (B0151.cellMeasure c)) := by
    calc ∫⁻ z, ‖partialY (fun w => 2 * f w * partialX f w) z‖ₑ ∂(B0151.cellMeasure c)
        ≤ ∫⁻ z, (‖2 * partialY f z * partialX f z‖ₑ + ‖2 * f z * partialY (partialX f) z‖ₑ)
            ∂(B0151.cellMeasure c) := lintegral_mono hpt
      _ = ∫⁻ z, ‖2 * partialY f z * partialX f z‖ₑ ∂(B0151.cellMeasure c) +
            ∫⁻ z, ‖2 * f z * partialY (partialX f) z‖ₑ ∂(B0151.cellMeasure c) :=
          lintegral_add_left hmA _
      _ ≤ _ := add_le_add (B0151.lintegral_two_mul_le hY0.1 hX0.1)
          (B0151.lintegral_two_mul_le hF0.1 hXY0.1)
  -- assembly on the library cell
  have hfin : ‖f (q0, η0)‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * (2 * (eLpNorm f 2 (B0151.cellMeasure c) *
          eLpNorm (partialY f) 2 (B0151.cellMeasure c))) +
        (2 * (eLpNorm (partialY f) 2 (B0151.cellMeasure c) *
            eLpNorm (partialX f) 2 (B0151.cellMeasure c)) +
          2 * (eLpNorm f 2 (B0151.cellMeasure c) *
            eLpNorm (partialY (partialX f)) 2 (B0151.cellMeasure c))) := by
    calc ‖f (q0, η0)‖ₑ ^ 2 ≤ ENNReal.ofReal c⁻¹ * (∫⁻ s in Ioc 0 c, ‖f (s, η0)‖ₑ ^ 2) +
          ∫⁻ s in Ioc 0 c, ‖2 * f (s, η0) * partialX f (s, η0)‖ₑ := hcirc
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hI1 bot_le) (hline.trans hI2)
  calc ‖f (q0, η0)‖ₑ ^ 2 ≤ _ := hfin
    _ ≤ ENNReal.ofReal c⁻¹ * (2 * (eLpNorm f 2 (B0151.cellMeasure c) *
            eLpNorm (Train.jet 1 f) 2 (B0151.cellMeasure c))) +
          (2 * (eLpNorm (Train.jet 1 f) 2 (B0151.cellMeasure c) *
              eLpNorm (Train.jet 1 f) 2 (B0151.cellMeasure c)) +
            2 * (eLpNorm f 2 (B0151.cellMeasure c) *
              eLpNorm (Train.jet 2 f) 2 (B0151.cellMeasure c))) := by
          gcongr
    _ = 2 * (ENNReal.ofReal c⁻¹ * (eLpNorm f 2 (B0151.cellMeasure c) *
            eLpNorm (Train.jet 1 f) 2 (B0151.cellMeasure c)) +
          eLpNorm (Train.jet 1 f) 2 (B0151.cellMeasure c) ^ 2 +
          eLpNorm f 2 (B0151.cellMeasure c) *
            eLpNorm (Train.jet 2 f) 2 (B0151.cellMeasure c)) := by
          ring
    _ = 2 * (ENNReal.ofReal c⁻¹ * (Train.cellL2 c f * Train.cellL2 c (Train.jet 1 f)) +
          Train.cellL2 c (Train.jet 1 f) ^ 2 + Train.cellL2 c f * Train.cellL2 c (Train.jet 2 f)) := by
          rw [eF, eD1, eD2]

end UnforcedLeray.Short.PartI
