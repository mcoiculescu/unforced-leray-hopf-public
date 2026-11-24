import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4

/-!
# `selAeSliceL2`: slice `L²` finiteness and measurability transfer to all `τ`

Source `the November 2 reference manuscript` lines 1334-1337, 1341-1344, 1351-1362.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- A.e. statements in `τ` are invariant under translation by a fixed constant. -/
private lemma ae_shift_of_ae (c : ℝ) {p : ℝ → Prop} (h : ∀ᵐ τ : ℝ, p τ) :
    ∀ᵐ τ : ℝ, p (τ + c) :=
  (measurePreserving_add_right volume c).quasiMeasurePreserving.ae h

/-- One-period periodicity of a.e.-periodic fields, slice by slice (Fubini on the product). -/
private lemma slice_periodic_ae (P : ℝ) (g : ℝ × Space → CVec3)
    (hg : ∀ᵐ x : ℝ × Space, g (x.1 + P, x.2) = g x) :
    ∀ᵐ τ : ℝ, ∀ᵐ y : Space, g (τ + P, y) = g (τ, y) := by
  have h := Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume) hg
  filter_upwards [h] with τ hτ
  filter_upwards [hτ] with y hy
  simpa using hy

/-- Slice `L²` integrals are a.e. invariant under one period shift. -/
private lemma slice_lint_periodic (P : ℝ) (g : ℝ × Space → CVec3)
    (hg : ∀ᵐ x : ℝ × Space, g (x.1 + P, x.2) = g x) :
    ∀ᵐ τ : ℝ, (∫⁻ y : Space, ‖g (τ + P, y)‖ₑ ^ (2 : ℝ))
      = ∫⁻ y : Space, ‖g (τ, y)‖ₑ ^ (2 : ℝ) := by
  filter_upwards [slice_periodic_ae P g hg] with τ hτ
  exact lintegral_congr_ae (by filter_upwards [hτ] with y hy; simp [hy])

/-- Integer translates of slice integrals agree a.e. -/
private lemma slice_lint_shift (P : ℝ) (g : ℝ × Space → CVec3)
    (hg : ∀ᵐ x : ℝ × Space, g (x.1 + P, x.2) = g x) (m : ℤ) :
    ∀ᵐ τ : ℝ, (∫⁻ y : Space, ‖g (τ + (m : ℝ) * P, y)‖ₑ ^ (2 : ℝ))
      = ∫⁻ y : Space, ‖g (τ, y)‖ₑ ^ (2 : ℝ) := by
  have hP := slice_lint_periodic P g hg
  refine Int.induction_on m ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun τ => by simp)
  · intro i ih
    filter_upwards [ih, ae_shift_of_ae (((i : ℤ) : ℝ) * P) hP] with τ h1 h2
    have e : τ + (((i : ℤ) + 1 : ℤ) : ℝ) * P = (τ + ((i : ℤ) : ℝ) * P) + P := by
      push_cast; ring
    rw [e, h2]
    exact h1
  · intro i ih
    have hc := ae_shift_of_ae ((((-(i : ℤ)) - 1 : ℤ) : ℝ) * P) hP
    filter_upwards [ih, hc] with τ h1 h2
    have e2 : τ + ((((-(i : ℤ)) - 1 : ℤ) : ℝ) * P) + P = τ + (((-(i : ℤ) : ℤ)) : ℝ) * P := by
      push_cast; ring
    rw [e2] at h2
    rw [← h2]
    exact h1

/-- Periodic transfer for a whole sequence of fields, a.e. in `τ`. -/
private lemma slice_lint_all (P : ℝ) (g : ℕ → ℝ × Space → CVec3)
    (hg : ∀ k, ∀ᵐ x : ℝ × Space, g k (x.1 + P, x.2) = g k x) :
    ∀ᵐ τ : ℝ, ∀ k, ∀ m : ℤ, (∫⁻ y : Space, ‖g k (τ + (m : ℝ) * P, y)‖ₑ ^ (2 : ℝ))
      = ∫⁻ y : Space, ‖g k (τ, y)‖ₑ ^ (2 : ℝ) :=
  ae_all_iff.2 (fun k => ae_all_iff.2 (fun m => slice_lint_shift P (g k) (hg k) m))

theorem selAeSliceL2 : SelAeSliceL2 := by
  intro P hP0 g hg
  have hmeas : ∀ᵐ τ : ℝ, AEStronglyMeasurable (fun y : Space => g (τ, y)) volume :=
    hg.meas.prodMk_left
  -- finiteness on one period
  have hfin0 : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖g (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    have h := hg.finite
    unfold UnforcedLeray.Short.IIb.phaseLpNorm at h
    have hc : ENNReal.ofReal P⁻¹ ≠ 0 := by
      simpa using hP0
    have hx : ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖g (t, y)‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
      intro hbad
      have : (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖g (t, y)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ⊤ := by
        rw [hbad]
        exact ENNReal.top_rpow_of_pos (by norm_num)
      exact absurd h (by rw [this]; exact lt_irrefl _)
    exact ENNReal.lt_top_of_mul_ne_top_left (by rwa [mul_comm]) hc
  have hmS : AEMeasurable (fun t : ℝ => ∫⁻ y : Space, ‖g (t, y)‖ₑ ^ (2 : ℝ)) volume := by
    have hf2 : AEMeasurable (fun z : ℝ × Space => ‖g z‖ₑ ^ (2 : ℝ)) volume :=
      (hg.meas.aemeasurable.enorm).pow_const (2 : ℝ)
    exact hf2.lintegral_prod_right'
  have hae1 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ∫⁻ y : Space, ‖g (t, y)‖ₑ ^ (2 : ℝ) < ⊤ :=
    ae_lt_top' (hmS.mono_measure Measure.restrict_le_self) hfin0.ne
  have hae : ∀ᵐ t : ℝ, t ∈ Ioc (0 : ℝ) P → ∫⁻ y : Space, ‖g (t, y)‖ₑ ^ (2 : ℝ) < ⊤ :=
    (ae_restrict_iff' measurableSet_Ioc).1 hae1
  -- transfer by periodicity
  have hper : ∀ᵐ τ : ℝ, ∀ m : ℤ, (∫⁻ y : Space, ‖g (τ + (m : ℝ) * P, y)‖ₑ ^ (2 : ℝ))
      = ∫⁻ y : Space, ‖g (τ, y)‖ₑ ^ (2 : ℝ) :=
    ae_all_iff.2 (fun m => slice_lint_shift P g hg.periodic m)
  have hshift : ∀ m : ℤ, ∀ᵐ τ : ℝ, (τ + (m : ℝ) * P ∈ Ioc (0 : ℝ) P →
      ∫⁻ y : Space, ‖g (τ + (m : ℝ) * P, y)‖ₑ ^ (2 : ℝ) < ⊤) :=
    fun m => ae_shift_of_ae ((m : ℝ) * P) hae
  have hall := ae_all_iff.2 hshift
  filter_upwards [hmeas, hper, hall] with τ hm hp hf
  refine ⟨hm, ?_⟩
  have h1 := toIocMod_add_toIocDiv_zsmul hP0 (0 : ℝ) τ
  have h2 := toIocMod_mem_Ioc hP0 (0 : ℝ) τ
  have hkey : τ + (((-(toIocDiv hP0 (0 : ℝ) τ)) : ℤ) : ℝ) * P = toIocMod hP0 (0 : ℝ) τ := by
    rw [zsmul_eq_mul] at h1
    push_cast
    linarith
  have hmem : τ + (((-(toIocDiv hP0 (0 : ℝ) τ)) : ℤ) : ℝ) * P ∈ Ioc (0 : ℝ) P := by
    rw [hkey]
    simpa using h2
  have hT := hf (-(toIocDiv hP0 (0 : ℝ) τ)) hmem
  rw [← hp (-(toIocDiv hP0 (0 : ℝ) τ))]
  exact hT

end UnforcedLeray.Short.PartIIIb.Concrete
