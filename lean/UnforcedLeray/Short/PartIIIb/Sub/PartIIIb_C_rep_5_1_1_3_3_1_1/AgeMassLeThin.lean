import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.Tail

/-!
# `PartIII-b:C/rep/5/1/1/3/3/1/1/2`: the `L¹_q` mass is at most the `L²_q` mass

Source `the November 2 reference manuscript` 5569-5575.

On the cell `q ∈ [-c/2, c/2)` with the normalized measure `c⁻¹ dq` (total mass `1`), the
Cauchy-Schwarz inequality gives `∫ c⁻¹ ‖g‖ dq ≤ (∫ c⁻¹ ‖g‖² dq)^{1/2}`. Integrating in `η` and
against `t^{-3/2} dt` over `t > a` gives `ageMass c a g ≤ thinMass c g a`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Cauchy-Schwarz on the cell `[-c/2, c/2)` with the normalized measure `c⁻¹ dq`. -/
lemma ageMassLeThin_cell_cs {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * F q
      ≤ (∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * F q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hvol : (volume.restrict (Ico (-c / 2) (c / 2))) univ = ENNReal.ofReal c := by
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    congr 1
    ring
  have hu : ENNReal.ofReal c⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have huv : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ico (-c / 2) (c / 2)))
    Real.HolderConjugate.two_two (f := fun _ : ℝ => (1 : ℝ≥0∞)) (g := F)
    aemeasurable_const hF.aemeasurable
  have hH' : ∫⁻ q in Ico (-c / 2) (c / 2), F q
      ≤ (ENNReal.ofReal c) ^ (1 / 2 : ℝ) * (∫⁻ q in Ico (-c / 2) (c / 2), F q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    simpa [ENNReal.one_rpow, lintegral_one, hvol] using hH
  have h1 : ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal c ^ (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), huv, ENNReal.one_rpow]
  have h2 : ENNReal.ofReal c⁻¹ = ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have key2 : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c ^ (1 / 2 : ℝ)
      = ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) := by
    calc ENNReal.ofReal c⁻¹ * ENNReal.ofReal c ^ (1 / 2 : ℝ)
        = (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ))
            * ENNReal.ofReal c ^ (1 / 2 : ℝ) := by rw [← h2]
      _ = ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal c ^ (1 / 2 : ℝ)) := by ring
      _ = ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) := by rw [h1, mul_one]
  have key1 : ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), F q
      ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c ^ (1 / 2 : ℝ)
          * (∫⁻ q in Ico (-c / 2) (c / 2), F q ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
    gcongr
  have key3 := ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal c⁻¹)
    (∫⁻ q in Ico (-c / 2) (c / 2), F q ^ (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [lintegral_const_mul' _ _ hu, lintegral_const_mul' _ _ hu, key3]
  calc ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), F q
      ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c ^ (1 / 2 : ℝ)
          * (∫⁻ q in Ico (-c / 2) (c / 2), F q ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := key1
    _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c ^ (1 / 2 : ℝ))
          * (∫⁻ q in Ico (-c / 2) (c / 2), F q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by ring
    _ = ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ)
          * (∫⁻ q in Ico (-c / 2) (c / 2), F q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [key2]

/-- The age-restricted indicator of `‖g‖ₑ` on `{a < t}`. -/
def ageMassLeThin_ind (a : ℝ) (g : Chart → Ten3) : Chart → ℝ≥0∞ :=
  {p : Chart | a < p.1}.indicator (fun p => ‖g p‖ₑ)

lemma ageMassLeThin_ind_meas {a : ℝ} {g : Chart → Ten3} (hg : Measurable g) :
    Measurable (ageMassLeThin_ind a g) := by
  have hS : MeasurableSet {p : Chart | a < p.1} := measurableSet_Ioi.preimage measurable_fst
  exact hg.enorm.indicator hS

theorem ageMassLeThin : AgeMassLeThin := by
  unfold AgeMassLeThin
  intro c hc a g hg
  have hS : MeasurableSet {p : Chart | a < p.1} := measurableSet_Ioi.preimage measurable_fst
  have hfm : Measurable (ageMassLeThin_ind a g) := ageMassLeThin_ind_meas hg
  have hw : Measurable fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  have hHm : Measurable fun p : Chart =>
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) * ageMassLeThin_ind a g p := hw.mul hfm
  have h1 : ageMass c a g = ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) * ageMassLeThin_ind a g p := by
    calc ageMass c a g = ∫⁻ p, ageMassLeThin_ind a g p ∂(ageμ c (-3 / 2)) := by
          unfold ageMass ageMassLeThin_ind
          rw [lintegral_indicator hS]
      _ = _ := lintegral_ageμ hc (-3 / 2 : ℝ) hfm
  -- the inner bound on each source age
  have key : ∀ t : ℝ, ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2),
      ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ)) * ageMassLeThin_ind a g (t, (q, η))
        ≤ (Ioi a).indicator
            (fun t : ℝ => ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c g t η) t := by
    intro t
    by_cases ht : a < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi a from ht)]
      have hI : ∀ q η, ageMassLeThin_ind a g (t, (q, η)) = ‖g (t, (q, η))‖ₑ := fun q η =>
        Set.indicator_of_mem (show (t, (q, η)) ∈ {p : Chart | a < p.1} from ht) _
      have hmeas : ∀ η, Measurable fun q : ℝ => ‖g (t, (q, η))‖ₑ := fun η =>
        (hg.comp (by fun_prop : Measurable fun q : ℝ => ((t, (q, η)) : Chart))).enorm
      have hpt : ∀ η, ∫⁻ q in Ico (-c / 2) (c / 2),
          ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ)) * ageMassLeThin_ind a g (t, (q, η))
            ≤ ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * sliceL2q c g t η := by
        intro η
        have e1 : ∀ q : ℝ, ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ))
            * ageMassLeThin_ind a g (t, (q, η))
            = ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * (ENNReal.ofReal c⁻¹ * ‖g (t, (q, η))‖ₑ) := by
          intro q
          rw [hI q η, ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
          ring
        rw [lintegral_congr (μ := volume.restrict (Ico (-c / 2) (c / 2))) e1,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact ageMassLeThin_cell_cs hc _ (hmeas η)
      calc ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2),
            ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ)) * ageMassLeThin_ind a g (t, (q, η))
          ≤ ∫⁻ η, ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * sliceL2q c g t η :=
            lintegral_mono (fun η => hpt η)
        _ = ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c g t η :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem (show t ∉ Ioi a from ht)]
      have hz : ∀ q η, ageMassLeThin_ind a g (t, (q, η)) = 0 := fun q η =>
        Set.indicator_of_notMem (show (t, (q, η)) ∉ {p : Chart | a < p.1} from ht) _
      simp [hz]
  calc ageMass c a g
      = ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) * ageMassLeThin_ind a g p := h1
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2),
          ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ)) * ageMassLeThin_ind a g (t, (q, η)) :=
        lintegral_ioi_qCell _ hHm
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (Ioi a).indicator
          (fun t : ℝ => ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c g t η) t :=
        lintegral_mono (fun t => key t)
    _ = ∫⁻ t in Ioi a ∩ Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c g t η :=
        setLIntegral_indicator measurableSet_Ioi _
    _ ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c g t η :=
        lintegral_mono_set inter_subset_left
    _ = thinMass c g a := rfl

end UnforcedLeray.Short.PartIIIb.Concrete
