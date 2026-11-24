import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4

/-!
# `selSubseq`: a.e.-slice `L²` convergence along a subsequence on one period

Source `the November 2 reference manuscript` lines 1334-1337, 1341-1344, 1351-1362.
A period `L²` norm tends to zero, so the period integral of the slice `L²` norms tends to zero;
a fast subsequence has summable slice norms, hence slice norms tend to zero a.e. on the period.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Squared `L²` norm of the slice of `f` at time `t`. -/
private def sliceE (f : ℝ × Space → CVec3) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ y : Space, ‖f (t, y)‖ₑ ^ (2 : ℝ)

private lemma slice_aemeas (f : ℝ × Space → CVec3) (hf : AEStronglyMeasurable f volume) :
    AEMeasurable (sliceE f) volume := by
  unfold sliceE
  have hf2 : AEMeasurable (fun z : ℝ × Space => ‖f z‖ₑ ^ (2 : ℝ)) volume :=
    (hf.aemeasurable.enorm).pow_const (2 : ℝ)
  exact hf2.lintegral_prod_right'

/-- The period `L²` norm tending to zero gives the period integral of slice norms tending to zero. -/
private lemma lint_tendsto_of_phase (P : ℝ) (hP : 0 < P) (f : ℕ → ℝ × Space → CVec3)
    (h : Tendsto (fun n => UnforcedLeray.Short.IIb.phaseLpNorm P 2 (f n)) atTop (nhds 0)) :
    Tendsto (fun n => ∫⁻ t in Ioc (0 : ℝ) P, sliceE (f n) t) atTop (nhds 0) := by
  have hc0 : ENNReal.ofReal P⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne'
  have hct : ENNReal.ofReal P⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : ∀ x : ENNReal, (x ^ (1 / (2 : ℝ))) ^ (2 : ℝ) = x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have hpow : Tendsto (fun n => (UnforcedLeray.Short.IIb.phaseLpNorm P 2 (f n)) ^ (2 : ℝ))
      atTop (nhds 0) := by
    have := ((ENNReal.continuous_rpow_const (y := 2)).tendsto 0).comp h
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this
  have hcI : Tendsto (fun n => ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, sliceE (f n) t)
      atTop (nhds 0) := by
    refine hpow.congr (fun n => ?_)
    unfold UnforcedLeray.Short.IIb.phaseLpNorm
    rw [key]
    rfl
  have hI := ENNReal.Tendsto.const_mul hcI (Or.inr (ENNReal.inv_ne_top.2 hc0))
  rw [mul_zero] at hI
  refine hI.congr (fun n => ?_)
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- (1) Subsequence with a.e.-slice `L²` convergence on one period (source 1341-1344). -/
theorem selSubseq : SelSubseq := by
  intro P hP Φ F Ψ D hΦ hF hΨ hD hΨΦ hDF
  have hS : Tendsto (fun n => ∫⁻ t in Ioc (0 : ℝ) P, sliceE (fun x => Ψ n x - Φ x) t)
      atTop (nhds 0) :=
    lint_tendsto_of_phase P hP (fun n x => Ψ n x - Φ x) hΨΦ
  have hT : Tendsto (fun n => ∫⁻ t in Ioc (0 : ℝ) P, sliceE (fun x => D n x - F x) t)
      atTop (nhds 0) :=
    lint_tendsto_of_phase P hP (fun n x => D n x - F x) hDF
  have hST := hS.add hT
  rw [add_zero] at hST
  have hε : ∀ k : ℕ, 0 < (2 : ENNReal)⁻¹ ^ k :=
    fun k => ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) k
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop,
      (∫⁻ t in Ioc (0 : ℝ) P, sliceE (fun x => Ψ n x - Φ x) t)
        + (∫⁻ t in Ioc (0 : ℝ) P, sliceE (fun x => D n x - F x) t) < (2 : ENNReal)⁻¹ ^ k :=
    fun k => (tendsto_order.1 hST).2 _ (hε k)
  obtain ⟨φ, hmono, hφ⟩ := Filter.extraction_forall_of_eventually hev
  have mΨ : ∀ k, AEMeasurable (sliceE (fun x => Ψ (φ k) x - Φ x)) volume :=
    fun k => slice_aemeas _ ((hΨ (φ k)).meas.sub hΦ.meas)
  have mD : ∀ k, AEMeasurable (sliceE (fun x => D (φ k) x - F x)) volume :=
    fun k => slice_aemeas _ ((hD (φ k)).meas.sub hF.meas)
  have hint : ∀ k, ∫⁻ t in Ioc (0 : ℝ) P,
      (sliceE (fun x => Ψ (φ k) x - Φ x) t + sliceE (fun x => D (φ k) x - F x) t)
        = (∫⁻ t in Ioc (0 : ℝ) P, sliceE (fun x => Ψ (φ k) x - Φ x) t)
          + ∫⁻ t in Ioc (0 : ℝ) P, sliceE (fun x => D (φ k) x - F x) t :=
    fun k => lintegral_add_left' ((mΨ k).mono_measure Measure.restrict_le_self) _
  have hmeasG : ∀ k, AEMeasurable (fun t => sliceE (fun x => Ψ (φ k) x - Φ x) t
      + sliceE (fun x => D (φ k) x - F x) t) (volume.restrict (Ioc (0 : ℝ) P)) :=
    fun k => ((mΨ k).add (mD k)).mono_measure Measure.restrict_le_self
  have hgeo : ∑' k : ℕ, (2 : ENNReal)⁻¹ ^ k < ⊤ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    norm_num
  have hfin : ∫⁻ t in Ioc (0 : ℝ) P, ∑' k, (sliceE (fun x => Ψ (φ k) x - Φ x) t
      + sliceE (fun x => D (φ k) x - F x) t) ≠ ⊤ := by
    rw [lintegral_tsum hmeasG]
    refine ne_top_of_le_ne_top hgeo.ne ?_
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    rw [hint k]
    exact (hφ k).le
  have hae1 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ∑' k, (sliceE (fun x => Ψ (φ k) x - Φ x) t + sliceE (fun x => D (φ k) x - F x) t) < ⊤ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum hmeasG) hfin
  have hae : ∀ᵐ t : ℝ, t ∈ Ioc (0 : ℝ) P →
      ∑' k, (sliceE (fun x => Ψ (φ k) x - Φ x) t + sliceE (fun x => D (φ k) x - F x) t) < ⊤ :=
    (ae_restrict_iff' measurableSet_Ioc).1 hae1
  refine ⟨φ, hmono, ?_, ?_⟩
  · filter_upwards [hae] with τ hτ hmem
    have htend := ENNReal.tendsto_atTop_zero_of_tsum_ne_top (hτ hmem).ne
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
      (fun k => zero_le) (fun k => le_self_add)
  · filter_upwards [hae] with τ hτ hmem
    have htend := ENNReal.tendsto_atTop_zero_of_tsum_ne_top (hτ hmem).ne
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
      (fun k => zero_le) (fun k => le_add_self)

end UnforcedLeray.Short.PartIIIb.Concrete
