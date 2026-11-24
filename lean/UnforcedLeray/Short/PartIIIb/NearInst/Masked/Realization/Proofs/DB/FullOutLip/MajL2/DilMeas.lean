import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.KerMeas

/-!
# Joint measurability of `dilMajG` (source 3996-4011, 2683)

The integrand `((τ, y), l, z) ↦ fmKer ν l (y - l z) * g(τ + 2 log l, z)` is jointly measurable,
since `fmKer ν` is jointly measurable in `(l, w)` (`fmKerMeasurable`). Two applications of
`Measurable.lintegral_prod_right'` (in `z`, then in `l` over `(0,1)`) give the measurability of
`(τ, y) ↦ dilMajG ν μ g τ y`. This is the radial-kernel version of `dilMajMeasurable_holds`
(`NearInst/Masked/Sub/FarMajorantL2/DilMajMeasurable.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem fmDilMeasurable :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmDilMeasurable := by
  intro ν μ g hg
  have hK : Measurable (fun p : ℝ × UnforcedLeray.Space => fmKer ν p.1 p.2) :=
    fmKerMeasurable ν
  have h1 : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      q.1.1.2 - q.1.2 • q.2) :=
    (measurable_snd.comp (measurable_fst.comp measurable_fst)).sub
      ((measurable_snd.comp measurable_fst).smul measurable_snd)
  have h1' : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      (q.1.2, q.1.1.2 - q.1.2 • q.2)) :=
    (measurable_snd.comp measurable_fst).prodMk h1
  have hKq : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      fmKer ν q.1.2 (q.1.1.2 - q.1.2 • q.2)) :=
    hK.comp h1'
  have hl : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      q.1.1.1 + 2 * Real.log q.1.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      (measurable_const.mul (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))
  have h2 : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      (q.1.1.1 + 2 * Real.log q.1.2, q.2)) :=
    hl.prodMk measurable_snd
  have hI : Measurable (fun q : ((ℝ × UnforcedLeray.Space) × ℝ) × UnforcedLeray.Space =>
      fmKer ν q.1.2 (q.1.1.2 - q.1.2 • q.2) *
        Function.uncurry g (q.1.1.1 + 2 * Real.log q.1.2, q.2)) :=
    Measurable.mul hKq (hg.comp h2)
  have hGint : Measurable (fun p : (ℝ × UnforcedLeray.Space) × ℝ =>
      ∫⁻ z : UnforcedLeray.Space, fmKer ν p.2 (p.1.2 - p.2 • z) *
        Function.uncurry g (p.1.1 + 2 * Real.log p.2, z)) :=
    hI.lintegral_prod_right'
  have hOut : Measurable (fun q : (ℝ × UnforcedLeray.Space) × ℝ =>
      ENNReal.ofReal (q.2 ^ (2 * μ + 2)) * ∫⁻ z : UnforcedLeray.Space,
        fmKer ν q.2 (q.1.2 - q.2 • z) * Function.uncurry g (q.1.1 + 2 * Real.log q.2, z)) :=
    (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)).mul hGint
  exact hOut.lintegral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
