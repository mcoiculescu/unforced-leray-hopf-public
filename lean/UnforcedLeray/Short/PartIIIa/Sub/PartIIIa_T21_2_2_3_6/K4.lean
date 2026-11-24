import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Unique
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# `PartIII-a:T21/2/2/3/6/1/4`: `WeakDerivC1` (leaf K4)

Source: `the November 2 reference manuscript` (adjoint localized interaction,
SP 3052-3058). A `C^1`, `d`-periodic complex field has its classical cylinder derivative
`pdCx` as weak derivative on the cell. Proof: integration by parts on the cell
(`Cyl.integral_cell_partialQ_mul`, `Cyl.integral_cell_partialEta_mul`), with the seam terms
cancelled by periodicity; integrability from the compact band support of the real tests.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace K4Aux

theorem cell_eq_cyl (c : ℝ) : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

theorem pdCx_zero_eq {χ : ℝ × ℝ → ℂ} (hd : Differentiable ℝ χ) (z : ℝ × ℝ) :
    UnforcedLeray.Short.IIIa.pdCx 0 χ z = UnforcedLeray.Cyl.partialQ χ z := by
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hd]
  rfl

theorem pdCx_one_eq {χ : ℝ × ℝ → ℂ} (hd : Differentiable ℝ χ) (z : ℝ × ℝ) :
    UnforcedLeray.Short.IIIa.pdCx 1 χ z = UnforcedLeray.Cyl.partialEta χ z := by
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hd]
  rfl

theorem ofReal_diff {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) :
    Differentiable ℝ (fun x => (ψ x : ℂ)) :=
  Complex.ofRealCLM.differentiable.comp hψ

theorem partialQ_ofReal {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialQ (fun x => (ψ x : ℂ)) z =
      ((UnforcedLeray.B0579.pd 0 ψ z : ℝ) : ℂ) := by
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv (ofReal_diff hψ)]
  have h : HasFDerivAt (fun x => (ψ x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ ψ z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z (hψ z).hasFDerivAt
  rw [h.fderiv]
  simp [UnforcedLeray.B0579.pd, UnforcedLeray.B0579.dir]

theorem partialEta_ofReal {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialEta (fun x => (ψ x : ℂ)) z =
      ((UnforcedLeray.B0579.pd 1 ψ z : ℝ) : ℂ) := by
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv (ofReal_diff hψ)]
  have h : HasFDerivAt (fun x => (ψ x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ ψ z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z (hψ z).hasFDerivAt
  rw [h.fderiv]
  simp [UnforcedLeray.B0579.pd, UnforcedLeray.B0579.dir]

theorem isPeriodic_ofReal {d : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest d ψ) :
    UnforcedLeray.Cyl.IsPeriodic d (fun x => (ψ x : ℂ)) :=
  fun z => by
    show ((ψ (z.1 + d, z.2) : ℝ) : ℂ) = (ψ z : ℂ)
    rw [hψ.periodic z]

/-- A product of a continuous complex field with a real profile that vanishes for large `|η|`
is integrable on the cell. -/
theorem integrable_vanish {d : ℝ} {χ : ℝ × ℝ → ℂ} (hχ : Continuous χ) {φ : ℝ × ℝ → ℝ}
    (hφ : Continuous φ) {R : ℝ} (hR : ∀ x : ℝ × ℝ, R < |x.2| → φ x = 0) :
    IntegrableOn (fun x => χ x * (φ x : ℂ)) (UnforcedLeray.Cyl.cell d) := by
  have hv : UnforcedLeray.Cyl.VanishesOutside R (fun x => χ x * (φ x : ℂ)) := fun z hz => by
    show χ z * (φ z : ℂ) = 0
    rw [hR z hz]
    simp
  exact hv.integrableOn_cell (hχ.mul (Complex.continuous_ofReal.comp hφ)) d

theorem hw_zero (d : ℝ) (χ : ℝ × ℝ → ℂ) (hd : 0 < d) (hχ1 : ContDiff ℝ 1 χ)
    (hper : ∀ y : ℝ × ℝ, χ (y.1 + d, y.2) = χ y) :
    UnforcedLeray.Short.IIIa.HasWeakCellDerivC d 0 χ (UnforcedLeray.Short.IIIa.pdCx 0 χ) := by
  have hχd : Differentiable ℝ χ := hχ1.differentiable (by simp)
  have hχc : Continuous χ := hχ1.continuous
  have hPQc : Continuous (UnforcedLeray.Cyl.partialQ χ) :=
    (UnforcedLeray.Cyl.C1_partial_of_contDiff hχ1).1
  have hpdC : ∀ x, UnforcedLeray.Short.IIIa.pdCx 0 χ x = UnforcedLeray.Cyl.partialQ χ x :=
    fun x => pdCx_zero_eq hχd x
  unfold UnforcedLeray.Short.IIIa.HasWeakCellDerivC
  rw [cell_eq_cyl]
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · obtain ⟨R, hR⟩ := (hψ.pd 0).band
    exact integrable_vanish hχc (hψ.pd 0).continuous hR
  · obtain ⟨R, hR⟩ := hψ.band
    simp only [hpdC]
    exact integrable_vanish hPQc hψ.continuous hR
  · obtain ⟨R, hR⟩ := hψ.band
    obtain ⟨R', hR'⟩ := (hψ.pd 0).band
    have h1 : IntegrableOn (fun z => UnforcedLeray.Cyl.partialQ χ z * (ψ z : ℂ))
        (UnforcedLeray.Cyl.cell d) := integrable_vanish hPQc hψ.continuous hR
    have h2 : IntegrableOn (fun z => χ z * UnforcedLeray.Cyl.partialQ (fun x => (ψ x : ℂ)) z)
        (UnforcedLeray.Cyl.cell d) := by
      simp only [partialQ_ofReal hψ.differentiable]
      exact integrable_vanish hχc (hψ.pd 0).continuous hR'
    have key := UnforcedLeray.Cyl.integral_cell_partialQ_mul hd (f := χ)
      (g := fun x => (ψ x : ℂ)) hχd (ofReal_diff hψ.differentiable) hper
      (isPeriodic_ofReal hψ) h1 h2
    simp only [partialQ_ofReal hψ.differentiable] at key
    simp only [hpdC]
    linear_combination key

theorem hw_one (d : ℝ) (χ : ℝ × ℝ → ℂ) (hd : 0 < d) (hχ1 : ContDiff ℝ 1 χ)
    (hper : ∀ y : ℝ × ℝ, χ (y.1 + d, y.2) = χ y) :
    UnforcedLeray.Short.IIIa.HasWeakCellDerivC d 1 χ (UnforcedLeray.Short.IIIa.pdCx 1 χ) := by
  have hχd : Differentiable ℝ χ := hχ1.differentiable (by simp)
  have hχc : Continuous χ := hχ1.continuous
  have hPEc : Continuous (UnforcedLeray.Cyl.partialEta χ) :=
    (UnforcedLeray.Cyl.C1_partial_of_contDiff hχ1).2
  have hpdC : ∀ x, UnforcedLeray.Short.IIIa.pdCx 1 χ x = UnforcedLeray.Cyl.partialEta χ x :=
    fun x => pdCx_one_eq hχd x
  unfold UnforcedLeray.Short.IIIa.HasWeakCellDerivC
  rw [cell_eq_cyl]
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · obtain ⟨R, hR⟩ := (hψ.pd 1).band
    exact integrable_vanish hχc (hψ.pd 1).continuous hR
  · obtain ⟨R, hR⟩ := hψ.band
    simp only [hpdC]
    exact integrable_vanish hPEc hψ.continuous hR
  · obtain ⟨R, hR⟩ := hψ.band
    obtain ⟨R', hR'⟩ := (hψ.pd 1).band
    have h0 : IntegrableOn (fun z => χ z * (ψ z : ℂ)) (UnforcedLeray.Cyl.cell d) :=
      integrable_vanish hχc hψ.continuous hR
    have h1 : IntegrableOn (fun z => UnforcedLeray.Cyl.partialEta χ z * (ψ z : ℂ))
        (UnforcedLeray.Cyl.cell d) := integrable_vanish hPEc hψ.continuous hR
    have h2 : IntegrableOn (fun z => χ z * UnforcedLeray.Cyl.partialEta (fun x => (ψ x : ℂ)) z)
        (UnforcedLeray.Cyl.cell d) := by
      simp only [partialEta_ofReal hψ.differentiable]
      exact integrable_vanish hχc (hψ.pd 1).continuous hR'
    have key := UnforcedLeray.Cyl.integral_cell_partialEta_mul (f := χ)
      (g := fun x => (ψ x : ℂ)) hχd (ofReal_diff hψ.differentiable) h0 h1 h2
    simp only [partialEta_ofReal hψ.differentiable] at key
    simp only [hpdC]
    linear_combination key

end K4Aux

open K4Aux in
theorem weakDerivC1 : UnforcedLeray.Short.IIIa.AdjE1.WeakDerivC1 := by
  intro d χ hd hχ1 hper j
  fin_cases j
  · exact hw_zero d χ hd hχ1 hper
  · exact hw_one d χ hd hχ1 hper

#print axioms weakDerivC1
