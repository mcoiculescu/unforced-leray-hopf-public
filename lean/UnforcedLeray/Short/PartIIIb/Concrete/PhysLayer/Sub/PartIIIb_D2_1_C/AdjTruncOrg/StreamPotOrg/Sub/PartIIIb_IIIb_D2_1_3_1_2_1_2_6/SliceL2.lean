import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6

/-!
# A.e. phase slices of a phase-`L²` field are `L²` (phaseSliceL2)

Source `the November 2 reference manuscript` lines 1334-1337 (`Y_r`) and
1351-1362. Periodicity of `Ψ` on the whole line is propagated from one period by integer shifts.
The proof is the one for `bsSliceL2` in `Fubini/BsSliceL2.lean`, restated for `PhaseSliceL2`
(same proposition, shown here without importing the Fubini layer).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- An a.e. period-shift invariant function of `t` is a.e. invariant under all integer shifts. -/
theorem phaseSliceL2_aeShift {P : ℝ} {H : ℝ → ℝ≥0∞} (hper : ∀ᵐ t : ℝ, H (t + P) = H t) :
    ∀ n : ℤ, ∀ᵐ t : ℝ, H (t + (n : ℝ) * P) = H t := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
      filter_upwards [(measurePreserving_add_right volume ((i : ℝ) * P)).quasiMeasurePreserving.ae
        hper, ih] with t h1 h2
      rw [show t + ((((i : ℤ) + 1 : ℤ)) : ℝ) * P = t + (i : ℝ) * P + P by push_cast; ring, h1]
      exact h2
  | pred i ih =>
      have h1 := (measurePreserving_add_right volume ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * P)).quasiMeasurePreserving.ae
        hper
      filter_upwards [h1, ih] with t h1 h2
      rw [show t + ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * P) + P = t + (((-(i : ℤ)) : ℤ) : ℝ) * P by
        push_cast; ring] at h1
      rw [← h1]
      exact h2

/-- Finiteness a.e. on the line from finiteness a.e. on one period, given integer shift
invariance. -/
theorem phaseSliceL2_aeFin {P : ℝ} (hP : 0 < P) {H : ℝ → ℝ≥0∞}
    (hper : ∀ n : ℤ, ∀ᵐ t : ℝ, H (t + (n : ℝ) * P) = H t)
    (h : ∀ᵐ t ∂(volume.restrict (Ioc 0 P)), H t < ⊤) : ∀ᵐ t : ℝ, H t < ⊤ := by
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  have hall : ∀ᵐ t : ℝ, ∀ n : ℤ, (t + (n : ℝ) * P ∈ Ioc 0 P → H t < ⊤) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [(measurePreserving_add_right volume ((n : ℝ) * P)).quasiMeasurePreserving.ae h,
      hper n] with t h1 h2
    intro hmem
    rw [← h2]
    exact h1 hmem
  filter_upwards [hall] with t ht
  have hm : t + (((-(toIocDiv hP 0 t) : ℤ)) : ℝ) * P ∈ Ioc 0 P := by
    have h0 := sub_toIocDiv_zsmul_mem_Ioc hP 0 t
    rw [zero_add] at h0
    convert h0 using 1
    rw [zsmul_eq_mul]
    push_cast
    ring
  exact ht _ hm

/-- A.e. phase slices of `Ψ ∈ Y_2` are in `L²(ℝ³)` (source 1334-1337). -/
theorem phaseSliceL2 : PhaseSliceL2 := by
  intro P hP Ψ hΨ
  have hfm : AEMeasurable (fun p : ℝ × Space => ‖Ψ p‖ₑ ^ (2 : ℝ)) volume :=
    ((hΨ.meas.aemeasurable).enorm).pow_const (2 : ℝ)
  have hHm : AEMeasurable (fun t : ℝ => ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ)) volume :=
    hfm.lintegral_prod_right'
  have hI : ∫⁻ t in Ioc 0 P, ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
    intro htop
    apply hΨ.finite.ne
    unfold UnforcedLeray.Short.IIb.phaseLpNorm
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne',
      ENNReal.top_rpow_of_pos (by norm_num)]
  have hH_ae : ∀ᵐ t ∂(volume.restrict (Ioc 0 P)),
      ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ) < ⊤ :=
    ae_lt_top' hHm.restrict hI
  have hpp : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      Ψ (z.1 + P, z.2) = Ψ z := hΨ.periodic
  have hper : ∀ᵐ t : ℝ, (∫⁻ y : Space, ‖Ψ (t + P, y)‖ₑ ^ (2 : ℝ))
      = ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hpp] with t ht
    exact lintegral_congr_ae (ht.mono fun y hy => by dsimp only; rw [hy])
  have hfin := phaseSliceL2_aeFin hP (phaseSliceL2_aeShift hper) hH_ae
  have hmeas : ∀ᵐ t : ℝ, AEStronglyMeasurable (fun y : Space => Ψ (t, y)) volume :=
    hΨ.meas.prodMk_left
  filter_upwards [hfin, hmeas] with t ht hmt
  refine ⟨hmt, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ht.ne

end UnforcedLeray.Short.PartIIIb.Concrete
