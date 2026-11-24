import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Box.Minkowski
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.ThinMass
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

/-!
# `PartIII-b:C/rep/4/1/org/2/1` (b): the disk integral of the source weight is `πR²·N₀`

Source `the November 2 reference manuscript` 2666-2684 (chart `s = R²/ϱ²`,
`η = Rz₃/ϱ`, `dy = πR² s^{-5/2} ds dη`, `𝒩_T T = sT`, normalized phase `dq/c`), 5573-5576
(`N₀(a) = ∫_a^∞ t^{-3/2}∫‖T(t,·,η)‖_{L²_q}dη dt`).

`slice_avg`: the phase average of a function of the chart point at fixed `z` is the cell average in
`q`.  `disk_mass`: `∫_D (P⁻¹∫_τ srcW²)^{1/2} dz = πR²·N₀(a)` on the disk `D` of source ages `> a`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FTT

open UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- **Phase average = cell average** (source 2666-2668): at a fixed source point `z`, the average
over one phase period `P = 2c/R` of a function of the chart point `chartOf R c z τ` is the average
over the cell in `q`. -/
theorem slice_avg {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (H : Chart → ℝ≥0∞) (z : Space) :
    ENNReal.ofReal (2 * c / R)⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), H (NearInst.chartOf R c z τ) =
      ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * H (age R z, (q, trans R z)) := by
  have hk : 0 < R / 2 := by positivity
  have hPk : 2 * c / R = c / (R / 2) := by field_simp
  set h : ℝ → ℝ≥0∞ := fun q => H (age R z, (cellRep c q, trans R z)) with hh
  have hper : Function.Periodic h c := fun q => by
    simp only [hh, cellRep_add hc.ne']
  have hL : ∀ τ : ℝ, H (NearInst.chartOf R c z τ) = h ((R / 2) * τ + (-(R / 2) * Real.log (age R z))) := by
    intro τ
    rw [NearInst.chartOf_eq_ring R c hR hc z τ]
    simp only [hh, phase_eq]
  simp only [hL]
  rw [hPk, lintegral_periodic_affine hc hk h hper]
  have hcell : ∫⁻ q in Ico (-c / 2) (c / 2), h q =
      ∫⁻ q in Ico (-c / 2) (c / 2), H (age R z, (q, trans R z)) := by
    refine setLIntegral_congr_fun measurableSet_Ico fun q hq => ?_
    simp only [hh, cellRep_of_mem hc hq]
  rw [hcell, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 2
  field_simp

/-- **The `L²_τ` norm of the source weight at `z` is the slice norm** (source 2683, 5573-5576):
`(P⁻¹∫_τ srcW²)^{1/2} = s · ‖g(s, ·, η)‖_{L²_q}`, `s = age z`, `η = trans z`. -/
theorem srcW_slice {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (g : Chart → Ten3) (z : Space) :
    ENNReal.ofReal (2 * c / R)⁻¹ ^ (1 / 2 : ℝ) *
        (∫⁻ τ in Ioc 0 (2 * c / R), srcW R c (fun q => ‖g q‖ₑ) τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (age R z) * sliceL2q c g (age R z) (trans R z) := by
  have h1 : ∀ τ : ℝ, srcW R c (fun q => ‖g q‖ₑ) τ z ^ (2 : ℝ) =
      ENNReal.ofReal (age R z) ^ (2 : ℝ) * (‖g (NearInst.chartOf R c z τ)‖ₑ ^ (2 : ℝ)) := by
    intro τ
    unfold srcW
    exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  simp only [h1]
  have hne : ENNReal.ofReal (age R z) ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  rw [lintegral_const_mul' _ _ hne, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
    ← mul_assoc, mul_comm (ENNReal.ofReal (2 * c / R)⁻¹ ^ (1 / 2 : ℝ)),
    mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [slice_avg hR hc (fun q => ‖g q‖ₑ ^ (2 : ℝ)) z]
  rfl

/-- **The disk integral of the slice norms is `πR²·N₀(a)`** (source 2679-2684 for `dy = πR²
s^{-5/2}ds dη`, 5573-5576): for a measurable disk `D` which is, off the axis, the set of source
ages `> a`, `∫_D s·‖g(s,·,η)‖_{L²_q} dz = πR² N₀(a)`. -/
theorem disk_mass {R c a : ℝ} (hR : 0 < R) (ha : 0 < a) (g : Chart → Ten3) (hg : Measurable g)
    (Dk : Set Space) (hDm : MeasurableSet Dk)
    (hD : ∀ z : Space, ϱ z ≠ 0 → (z ∈ Dk ↔ a < age R z)) (hc : 0 < c) :
    ∫⁻ z in Dk, ENNReal.ofReal (age R z) * sliceL2q c g (age R z) (trans R z) =
      ENNReal.ofReal (Real.pi * R ^ 2) * thinMass c g a := by
  set Fp : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if a < p.1 then ENNReal.ofReal p.1 * sliceL2q c g p.1 p.2 else 0 with hFp
  have hFm : Measurable Fp := by
    refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
    exact (ENNReal.measurable_ofReal.comp measurable_fst).mul (measurable_sliceL2q c hg)
  have hax : ∀ᵐ z : Space ∂volume, ϱ z ≠ 0 := by
    have hN : volume {z : Space | ϱ z = 0} = 0 := NearInst.Masked.axisNull_holds
    rw [ae_iff]
    simpa using hN
  rw [← lintegral_indicator hDm]
  have hae : (Dk.indicator fun z => ENNReal.ofReal (age R z) * sliceL2q c g (age R z) (trans R z))
      =ᵐ[volume] fun z => Fp (age R z, trans R z) := by
    filter_upwards [hax] with z hz
    by_cases hzD : z ∈ Dk
    · rw [indicator_of_mem hzD]
      have := (hD z hz).1 hzD
      simp [hFp, this]
    · rw [indicator_of_notMem hzD]
      have : ¬ a < age R z := fun h => hzD ((hD z hz).2 h)
      simp [hFp, this]
  rw [lintegral_congr_ae hae, lintegral_ringChart hR Fp hFm]
  congr 1
  have hFm2 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) * Fp p :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hFm
  rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod_univ _ hFm2]
  have h2 : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ η, ENNReal.ofReal (t ^ (-(5 / 2 : ℝ))) * Fp (t, η) =
      (Ioi a).indicator (fun t => ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
        ∫⁻ η, sliceL2q c g t η) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    by_cases hat : a < t
    · rw [indicator_of_mem (show t ∈ Ioi a from hat)]
      have e : ∀ η : ℝ, ENNReal.ofReal (t ^ (-(5 / 2 : ℝ))) * Fp (t, η) =
          ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * sliceL2q c g t η := by
        intro η
        simp only [hFp, hat, if_true]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _),
          ← Real.rpow_add_one ht0.ne']
        norm_num
      simp only [e]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    · rw [indicator_of_notMem (show t ∉ Ioi a from hat)]
      simp [hFp, hat]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.2 (Ioi_subset_Ioi ha.le)]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.FTT

end
