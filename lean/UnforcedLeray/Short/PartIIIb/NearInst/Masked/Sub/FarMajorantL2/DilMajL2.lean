import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Minkowski over the dilation parameter (source 4002)

`dilMajL2_of`: the `L²([0,P) × ℝ³)` norm of `dilMaj` is the `L²` norm of the `l`-integral of the
fixed-`l` terms `dmlF l (τ, y)`; Minkowski's integral inequality (`PhaseMinkowski`) bounds it by the
integral over `l ∈ (0,1)` of the fixed-`l` norms, and `DilMajFixedL` bounds each of those by
`l^{2μ+1/2} A ‖g‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The fixed-dilation term of `dilMaj` at `(τ, y) = a`: `dilMaj μ d g τ y = ∫_{(0,1)} dmlF l (τ,y) dl`. -/
private def dmlF (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞) (l : ℝ)
    (a : ℝ × UnforcedLeray.Space) : ℝ≥0∞ :=
  ENNReal.ofReal (l ^ (2 * μ + 2)) * ∫⁻ z : UnforcedLeray.Space,
    farKern d (a.2 - l • z) * g (a.1 + 2 * Real.log l) z

/-- Joint measurability of the fixed-`l` terms in `(l, τ, y)`. -/
private lemma dml_meas_F (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : ℝ × (ℝ × UnforcedLeray.Space) => dmlF μ d g p.1 p.2) := by
  have hfar : Measurable (farKern d) := by
    unfold farKern
    exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) measurable_const
  have h1 : Measurable (fun q : (ℝ × (ℝ × UnforcedLeray.Space)) × UnforcedLeray.Space =>
      q.1.2.2 - q.1.1 • q.2) :=
    (measurable_snd.comp (measurable_snd.comp measurable_fst)).sub
      ((measurable_fst.comp measurable_fst).smul measurable_snd)
  have h2 : Measurable (fun q : (ℝ × (ℝ × UnforcedLeray.Space)) × UnforcedLeray.Space =>
      (q.1.2.1 + 2 * Real.log q.1.1, q.2)) :=
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).add
      (measurable_const.mul (Real.measurable_log.comp (measurable_fst.comp measurable_fst)))).prodMk
      measurable_snd
  have hI : Measurable (fun q : (ℝ × (ℝ × UnforcedLeray.Space)) × UnforcedLeray.Space =>
      farKern d (q.1.2.2 - q.1.1 • q.2) * Function.uncurry g (q.1.2.1 + 2 * Real.log q.1.1, q.2)) :=
    Measurable.mul (hfar.comp h1) (hg.comp h2)
  have hGint : Measurable (fun p : ℝ × (ℝ × UnforcedLeray.Space) =>
      ∫⁻ z : UnforcedLeray.Space, farKern d (p.2.2 - p.1 • z) *
        Function.uncurry g (p.2.1 + 2 * Real.log p.1, z)) :=
    hI.lintegral_prod_right'
  exact (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hGint

theorem dilMajL2_of (hF : DilMajFixedL) (hMk : PhaseMinkowski) (hM : DilMajMeasurable) :
    DilMajL2 := by
  intro μ d g hg P hP0 hper A hA
  have hFm : Measurable (fun p : ℝ × (ℝ × UnforcedLeray.Space) => dmlF μ d g p.1 p.2) :=
    dml_meas_F μ d g hg
  have hsf : SFinite ((volume.restrict (Ico (0 : ℝ) P)).prod
      (volume : Measure UnforcedLeray.Space)) := by
    infer_instance
  -- measurability of the `l`-integral in `a = (τ, y)`
  have hsw : Measurable (fun q : (ℝ × UnforcedLeray.Space) × ℝ => dmlF μ d g q.2 q.1) :=
    hFm.comp (measurable_snd.prodMk measurable_fst)
  have hPhi : Measurable (fun a : ℝ × UnforcedLeray.Space =>
      ∫⁻ l in Ioo (0 : ℝ) 1, dmlF μ d g l a) := hsw.lintegral_prod_right'
  have hdil : ∀ τ y, dilMaj μ d g τ y = ∫⁻ l in Ioo (0 : ℝ) 1, dmlF μ d g l (τ, y) :=
    fun τ y => rfl
  -- the left-hand side is the `(τ, y)`-integral of the squared `l`-integral
  have hLHS : (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space, dilMaj μ d g τ y ^ (2 : ℝ)) =
      ∫⁻ a, (∫⁻ l in Ioo (0 : ℝ) 1, dmlF μ d g l a) ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space)) := by
    rw [lintegral_prod (fun a => (∫⁻ l in Ioo (0 : ℝ) 1, dmlF μ d g l a) ^ (2 : ℝ))
      (hPhi.pow_const (2 : ℝ)).aemeasurable]
    refine lintegral_congr fun τ => lintegral_congr fun y => ?_
    exact congrArg (· ^ (2 : ℝ)) (hdil τ y)
  -- fixed `l`: Young (`DilMajFixedL`) after the change to the `(τ, y)`-integral
  have hfix : ∀ l ∈ Ioo (0 : ℝ) 1,
      (∫⁻ a, dmlF μ d g l a ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * A *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have hm : Measurable (fun a : ℝ × UnforcedLeray.Space => dmlF μ d g l a ^ (2 : ℝ)) :=
      (hFm.comp (measurable_const.prodMk measurable_id)).pow_const _
    rw [lintegral_prod (fun a => dmlF μ d g l a ^ (2 : ℝ)) hm.aemeasurable]
    exact hF μ d g hg P hP0 hper A hA l hl0
  have hRHS : (∫⁻ l in Ioo (0 : ℝ) 1, (∫⁻ a, dmlF μ d g l a ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
          (1 / 2 : ℝ)) ≤
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * A *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    setLIntegral_mono' (μ := volume) measurableSet_Ioo hfix
  have hmf : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * A) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul_const A
  have hm1 : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (2 * μ + 1 / 2))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  rw [hLHS]
  calc (∫⁻ a, (∫⁻ l in Ioo (0 : ℝ) 1, dmlF μ d g l a) ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, (∫⁻ a, dmlF μ d g l a ^ (2 : ℝ)
          ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
            (1 / 2 : ℝ) :=
        hMk _ _ (dmlF μ d g) hFm (Ioo (0 : ℝ) 1) measurableSet_Ioo
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * A *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        hRHS
    _ = (∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2))) * A *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [lintegral_mul_const _ hmf, lintegral_mul_const _ hm1]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
