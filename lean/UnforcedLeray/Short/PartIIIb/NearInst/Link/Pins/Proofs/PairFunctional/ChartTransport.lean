import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3_1
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtH

/-!
# `ChartTransport` (task `PartIII-b:C/near/pins/3/3/1/1`)

Source `the November 2 reference manuscript` 2666-2668, 2683-2689, 1640-1641.
The real part of an `H`-class: `T g := merReL ∘ g ∘ cellPtInv` is the bounded real-linear map
`Body.reV c` (`Body.reV_ae` gives its chart form).  For a class with real chart form `f`
(`ChartRep`), `T g = f` a.e. and `T (-i g) = 0` (the real part of `-i · merC v` vanishes).
The a.e. transfer from `measureH c` to `ageμ c (-3/2)` uses `Masked.cellPtInvH_eq`,
`Masked.cellPtH_eq`, and `cellPt ∘ cellPtInv = id` a.e. on the chart measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

theorem ct_merReL_merC (b : Merid) : Body.merReL (merC b) = b := by
  ext i
  simp [Body.merReL, Body.merReLin, merC]

/-- The inverse recentring carries `ageμ c (-3/2)` to `c⁻¹ · measureH c`; derived from the forward
identity `Masked.cellPtH_eq` (the two proof files cannot be imported together). -/
theorem ct_cellPtInvH (c : ℝ) (hc : 0 < c) : Masked.CellPtInvH c := by
  show Measure.map (Masked.cellPtInv c) (ageμ c (-3 / 2)) = ENNReal.ofReal c⁻¹ • measureH c
  have hH : Measure.map (cellPt c) (measureH c) = ENNReal.ofReal c • ageμ c (-3 / 2) :=
    Masked.cellPtH_eq c hc
  have hae : (Masked.cellPtInv c ∘ cellPt c) =ᵐ[measureH c] id := by
    filter_upwards [Body.ae_mem_cell c] with q hq
    obtain ⟨-, ⟨h0, hcq⟩, -⟩ := hq
    exact Masked.cellPtInv_cellPt h0 hcq
  have h1 : Measure.map (Masked.cellPtInv c) (Measure.map (cellPt c) (measureH c)) =
      measureH c := by
    rw [Measure.map_map (Masked.measurable_cellPtInv c) (Body.measurable_cellPt' c),
      Measure.map_congr hae, Measure.map_id]
  have h2 : ENNReal.ofReal c • Measure.map (Masked.cellPtInv c) (ageμ c (-3 / 2)) =
      measureH c := by
    rw [← Measure.map_smul, ← hH, h1]
  rw [← h2, smul_smul, ENNReal.ofReal_inv_of_pos hc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top, one_smul]

/-- A property of the profile holding `measureH`-a.e. pulls back to an `ageμ`-a.e. property of
the recentred chart point. -/
theorem ct_ae_transfer {c : ℝ} (hc : 0 < c) (Q : Profile → Prop)
    (hQ : ∀ᵐ q ∂measureH c, Q q) : ∀ᵐ x ∂ageμ c (-3 / 2), Q (Masked.cellPtInv c x) := by
  have hmap : Measure.map (Masked.cellPtInv c) (ageμ c (-3 / 2)) =
      ENNReal.ofReal c⁻¹ • measureH c :=
    ct_cellPtInvH c hc
  apply ae_of_ae_map (Masked.measurable_cellPtInv c).aemeasurable
  rw [hmap]
  exact (Measure.smul_absolutelyContinuous).ae_le hQ

/-- `cellPt ∘ cellPtInv = id` almost everywhere for the chart measure `ageμ c (-3/2)`. -/
theorem ct_cellPt_cellPtInv (c : ℝ) (hc : 0 < c) :
    ∀ᵐ x ∂ageμ c (-3 / 2), cellPt c (Masked.cellPtInv c x) = x := by
  have hA : ∀ᵐ q ∂measureH c, cellPt c (Masked.cellPtInv c (cellPt c q)) = cellPt c q := by
    filter_upwards [Body.ae_mem_cell c] with q hq
    obtain ⟨-, ⟨h0, hcq⟩, -⟩ := hq
    rw [Masked.cellPtInv_cellPt h0 hcq]
  have hmeas : Measurable (fun y : Chart => cellPt c (Masked.cellPtInv c y)) :=
    (Body.measurable_cellPt' c).comp (Masked.measurable_cellPtInv c)
  have hset : MeasurableSet {y : Chart | cellPt c (Masked.cellPtInv c y) = y} :=
    measurableSet_eq_fun hmeas measurable_id
  have hB : ∀ᵐ y ∂(Measure.map (cellPt c) (measureH c)),
      cellPt c (Masked.cellPtInv c y) = y :=
    (ae_map_iff (Body.measurable_cellPt' c).aemeasurable hset).2 hA
  rw [Masked.cellPtH_eq c hc] at hB
  exact (Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 hc).ne').ae_le hB

theorem chartTransport : ChartTransport := by
  intro c hc
  have hI : Masked.CellPtInvH c := ct_cellPtInvH c hc
  refine ⟨Body.reV c hI, fun g f hg => ⟨?_, ?_⟩⟩
  · have hK := ct_ae_transfer hc (fun q => (g : Profile → MeridC) q = merC (f (cellPt c q))) hg
    filter_upwards [Body.reV_ae c hI g, hK, ct_cellPt_cellPtInv c hc] with x h1 h2 h3
    rw [h1, h2, h3, ct_merReL_merC]
  · apply Lp.ext
    have hsm : ∀ᵐ q ∂measureH c, ((-Complex.I) • g : HSpace c MeridC) q =
        (-Complex.I) • merC (f (cellPt c q)) := by
      filter_upwards [Lp.coeFn_smul (-Complex.I) g, hg] with q h1 h2
      rw [h1, Pi.smul_apply, h2]
    have hK' := ct_ae_transfer hc
      (fun q => ((-Complex.I) • g : HSpace c MeridC) q = (-Complex.I) • merC (f (cellPt c q))) hsm
    filter_upwards [Body.reV_ae c hI ((-Complex.I) • g), hK', ct_cellPt_cellPtInv c hc,
      Lp.coeFn_zero Merid 2 (ageμ c (-3 / 2))]
      with x h1 h2 h3 h4
    rw [h1, h2, h3, h4, Pi.zero_apply]
    ext i
    simp [Body.merReL, Body.merReLin, merC, Complex.mul_re]

end UnforcedLeray.Short.PartIIIb.NearInst
