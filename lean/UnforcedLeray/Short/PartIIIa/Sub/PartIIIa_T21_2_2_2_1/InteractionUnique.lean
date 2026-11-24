import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K5

/-!
# Part III-a, `PartIII-a:T21/2/2/2/1/4`: `InteractionUnique` from the three leaves

Source `the November 2 reference manuscript` (SP), lines 3052-3058.

Leaves (compiled and auto-accepted): `kernelBSExists` (kernel Biot-Savart velocities exist,
`PartIII-a:T21/2/2/3/6/1/1`), `cellUnique` (du Bois-Reymond on the cylinder,
`PartIII-a:T21/2/2/3/6/1/3`), `bandMulTest` (band-integrable fields pair with cylinder tests,
`PartIII-a:T21/2/2/3/6/1/5`).  The only extra input is that `MemLp χ 2 (cellMeasure d (-m))`
gives integrability on every band `cell d ∩ {|η| ≤ R}`, which is proved here from
`integrableOn_band_X` applied to the real and imaginary parts.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- A complex `L²(cellMeasure d (-m))` function is integrable on every band of the cell. -/
theorem interactionUnique_bandInt_real (m d : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : MemLp f 2 (UnforcedLeray.B0579.cellMeasure d (-m))) (R : ℝ) :
    IntegrableOn f (UnforcedLeray.B0579.band R ∩ UnforcedLeray.B0579.cell d) := by
  have h := UnforcedLeray.B0579.integrableOn_band_X (c := d) (m := -m) (hf.toLp f) R
  refine h.congr_fun_ae ?_
  have h1 : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell d)), (hf.toLp f) x = f x :=
    (UnforcedLeray.B0579.ac_cellMeasure d (-m)).ae_le hf.coeFn_toLp
  exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right h1

theorem interactionUnique_bandInt (m d : ℝ) (χ : ℝ × ℝ → ℂ)
    (hχ : MemLp χ 2 (UnforcedLeray.B0579.cellMeasure d (-m))) (R : ℝ) :
    IntegrableOn χ (UnforcedLeray.B0579.cell d ∩ {x : ℝ × ℝ | |x.2| ≤ R}) := by
  have hre : IntegrableOn (fun x => (χ x).re)
      (UnforcedLeray.B0579.band R ∩ UnforcedLeray.B0579.cell d) :=
    interactionUnique_bandInt_real m d (fun x => (χ x).re) hχ.re R
  have him : IntegrableOn (fun x => (χ x).im)
      (UnforcedLeray.B0579.band R ∩ UnforcedLeray.B0579.cell d) :=
    interactionUnique_bandInt_real m d (fun x => (χ x).im) hχ.im R
  have hm1 : AEStronglyMeasurable χ
      ((volume.restrict (UnforcedLeray.B0579.cell d)).restrict (UnforcedLeray.B0579.band R)) :=
    (hχ.aestronglyMeasurable.mono_ac (UnforcedLeray.B0579.ac_cellMeasure d (-m))).restrict
  rw [Measure.restrict_restrict (UnforcedLeray.B0579.measurableSet_band R)] at hm1
  have hg : Integrable (fun x => |(χ x).re| + |(χ x).im|)
      (volume.restrict (UnforcedLeray.B0579.band R ∩ UnforcedLeray.B0579.cell d)) :=
    (hre.abs).add (him.abs)
  have hbd : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.band R ∩ UnforcedLeray.B0579.cell d)),
      ‖χ x‖ ≤ |(χ x).re| + |(χ x).im| :=
    Filter.Eventually.of_forall fun x => Complex.norm_le_abs_re_add_abs_im (χ x)
  rw [Set.inter_comm (UnforcedLeray.B0579.cell d) {x : ℝ × ℝ | |x.2| ≤ R}]
  exact Integrable.mono' hg hm1 hbd

theorem interactionUnique : UnforcedLeray.Short.IIIa.E0.InteractionUnique := by
  intro m d hd E Φ χ χ' hχ hχ' hI hI'
  have hb : ∀ R : ℝ, IntegrableOn χ
      (UnforcedLeray.B0579.cell d ∩ {x : ℝ × ℝ | |x.2| ≤ R}) :=
    fun R => interactionUnique_bandInt m d χ hχ R
  have hb' : ∀ R : ℝ, IntegrableOn χ'
      (UnforcedLeray.B0579.cell d ∩ {x : ℝ × ℝ | |x.2| ≤ R}) :=
    fun R => interactionUnique_bandInt m d χ' hχ' R
  have hae : (χ - χ') =ᵐ[volume.restrict (UnforcedLeray.B0579.cell d)] 0 := by
    refine cellUnique d (χ - χ') hd (fun R => (hb R).sub (hb' R)) ?_
    intro ψ hψ
    obtain ⟨u, hu⟩ := kernelBSExists d ψ hd hψ
    have i1 := bandMulTest d χ ψ hd hb hψ
    have i2 := bandMulTest d χ' ψ hd hb' hψ
    have e1 := hI ψ u hψ hu
    have e2 := hI' ψ u hψ hu
    have hsub : ∫ x in UnforcedLeray.B0579.cell d, (χ - χ') x * (ψ x : ℂ) =
        (∫ x in UnforcedLeray.B0579.cell d, χ x * (ψ x : ℂ)) -
          ∫ x in UnforcedLeray.B0579.cell d, χ' x * (ψ x : ℂ) := by
      rw [← integral_sub i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [sub_mul]
    rw [hsub, e1, e2, sub_self]
  filter_upwards [hae] with x hx
  exact sub_eq_zero.1 hx

#print axioms interactionUnique
