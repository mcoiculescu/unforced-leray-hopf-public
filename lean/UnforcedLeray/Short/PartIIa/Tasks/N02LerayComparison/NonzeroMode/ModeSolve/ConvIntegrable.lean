import UnforcedLeray.Short.PartIIa.Sub.N02_4_5

/-!
# Part II-a, task `PartII-a:N02/4/5/6` (`NzConvIntegrable`)

Source of record: `the November 2 reference manuscript` (nonzero `q`-mode system,
Green kernel `G_k(t) = -e^{-|k||t|}/(2|k|)`).

Route. The exponential weight `t ↦ e^{-|k||t|}` is integrable on `ℝ`: it is integrable on `(0, ∞)`
(`exp_neg_integrableOn_Ioi`) and, by reflection (`IntegrableOn.comp_neg`), on `(-∞, 0)`; the two
pieces together with `{0}` cover `ℝ` (`Iio_union_Ici`). Hence the Green kernel is integrable.
The data `h` is continuous with compact support, so `t ↦ h(x.1, x.2 - t)` is continuous and bounded
by `sup ‖h‖`, and `Integrable.mul_bdd` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The weight `t ↦ e^{-|k||t|}` is integrable on `ℝ` for `k ≠ 0`. -/
theorem nzci_exp_abs_integrable (k : ℝ) (hk : k ≠ 0) :
    Integrable (fun t : ℝ => Real.exp (-|k| * |t|)) := by
  have hb : 0 < |k| := abs_pos.mpr hk
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-|k| * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hb
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-|k| * |t|)) (Ioi 0) := by
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : 0 < t := ht
    simp [abs_of_pos ht']
  have h2' : IntegrableOn (fun t : ℝ => Real.exp (-|k| * |t|)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h2
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-|k| * |t|)) (Iio 0) := by
    have h4 := h2.comp_neg
    rw [neg_Ioi, neg_zero] at h4
    refine h4.congr_fun (fun t _ => ?_) measurableSet_Iio
    simp [abs_neg]
  have h5 := h3.union h2'
  rw [Iio_union_Ici] at h5
  exact integrableOn_univ.mp h5

/-- The one-dimensional Green kernel `t ↦ G_k(t)` is integrable on `ℝ` for `k ≠ 0`. -/
theorem nzci_green_integrable (k : ℝ) (hk : k ≠ 0) :
    Integrable (fun t : ℝ => nzGreen k t) := by
  have hI := nzci_exp_abs_integrable k hk
  refine ((hI.div_const (2 * |k|)).neg).congr (ae_of_all _ fun t => ?_)
  show -(Real.exp (-|k| * |t|) / (2 * |k|)) = -Real.exp (-|k| * |t|) / (2 * |k|)
  ring

/-- The complex-valued Green kernel `t ↦ (G_k(t) : ℂ)` is integrable on `ℝ` for `k ≠ 0`. -/
theorem nzci_green_complex_integrable (k : ℝ) (hk : k ≠ 0) :
    Integrable (fun t : ℝ => (nzGreen k t : ℂ)) :=
  (nzci_green_integrable k hk).ofReal

/-- **Leaf `NzConvIntegrable`: the convolution integrand is integrable.** -/
theorem nzConvIntegrable_proof : NzConvIntegrable := by
  unfold NzConvIntegrable
  intro k hk h hh hcs x
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hcs
  have hG := nzci_green_complex_integrable k hk
  have hcont : Continuous (fun t : ℝ => h (x.1, x.2 - t)) :=
    hh.comp (f := fun t : ℝ => (x.1, x.2 - t)) (by fun_prop)
  exact hG.mul_bdd hcont.aestronglyMeasurable (ae_of_all _ fun t => hC _)

end UnforcedLeray.Short.PartIIa
