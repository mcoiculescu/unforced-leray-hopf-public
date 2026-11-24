import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Joint measurability of `dilMaj` (source 4001-4002)

The integrand `(τ, y, l, z) ↦ farKern d (y - l z) g(τ + 2 log l, z)` is measurable, and two
applications of `Measurable.lintegral_prod_right'` (in `z`, then in `l` over `(0,1)`) give the
measurability of `(τ, y) ↦ dilMaj μ d g τ y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem dilMajMeasurable_holds : DilMajMeasurable := by
  intro μ d g hg
  have hfar : Measurable (farKern d) := by
    unfold farKern
    exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) measurable_const
  have h1 : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      q.1.1.2 - q.1.2 • q.2) :=
    (measurable_snd.comp (measurable_fst.comp measurable_fst)).sub
      ((measurable_snd.comp measurable_fst).smul measurable_snd)
  have hl : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      q.1.1.1 + 2 * Real.log q.1.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      (measurable_const.mul (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))
  have h2 : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      (q.1.1.1 + 2 * Real.log q.1.2, q.2)) :=
    hl.prodMk measurable_snd
  have hI : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      farKern d (q.1.1.2 - q.1.2 • q.2) *
        Function.uncurry g (q.1.1.1 + 2 * Real.log q.1.2, q.2)) :=
    Measurable.mul (hfar.comp h1) (hg.comp h2)
  have hGint : Measurable (fun p : (ℝ × UnforcedLeray.Space) × ℝ =>
      ∫⁻ z : UnforcedLeray.Space, farKern d (p.1.2 - p.2 • z) *
        Function.uncurry g (p.1.1 + 2 * Real.log p.2, z)) :=
    hI.lintegral_prod_right'
  have hOut : Measurable (fun q : (ℝ × UnforcedLeray.Space) × ℝ =>
      ENNReal.ofReal (q.2 ^ (2 * μ + 2)) * ∫⁻ z : UnforcedLeray.Space,
        farKern d (q.1.2 - q.2 • z) * Function.uncurry g (q.1.1 + 2 * Real.log q.2, z)) :=
    (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)).mul hGint
  exact hOut.lintegral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
