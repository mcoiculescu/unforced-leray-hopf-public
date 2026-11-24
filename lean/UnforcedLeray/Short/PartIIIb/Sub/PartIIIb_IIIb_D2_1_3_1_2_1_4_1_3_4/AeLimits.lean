import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4

/-!
# `selAeSliceLimits`: a.e. slice limits transfer to all `τ` by periodicity

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

theorem selAeSliceLimits : SelAeSliceLimits := by
  intro P hP0 g hg hlim
  have hper := slice_lint_all P g hg
  have hshift : ∀ m : ℤ, ∀ᵐ τ : ℝ,
      (τ + (m : ℝ) * P ∈ Ioc (0 : ℝ) P →
        Tendsto (fun k => ∫⁻ y : Space, ‖g k (τ + (m : ℝ) * P, y)‖ₑ ^ (2 : ℝ)) atTop (nhds 0)) :=
    fun m => ae_shift_of_ae ((m : ℝ) * P) hlim
  have hall := ae_all_iff.2 hshift
  filter_upwards [hper, hall] with τ hτ1 hτ2
  have h1 := toIocMod_add_toIocDiv_zsmul hP0 (0 : ℝ) τ
  have h2 := toIocMod_mem_Ioc hP0 (0 : ℝ) τ
  have hkey : τ + (((-(toIocDiv hP0 (0 : ℝ) τ)) : ℤ) : ℝ) * P = toIocMod hP0 (0 : ℝ) τ := by
    rw [zsmul_eq_mul] at h1
    push_cast
    linarith
  have hmem : τ + (((-(toIocDiv hP0 (0 : ℝ) τ)) : ℤ) : ℝ) * P ∈ Ioc (0 : ℝ) P := by
    rw [hkey]
    simpa using h2
  have hT := hτ2 (-(toIocDiv hP0 (0 : ℝ) τ)) hmem
  exact Tendsto.congr (fun k => hτ1 k (-(toIocDiv hP0 (0 : ℝ) τ))) hT

end UnforcedLeray.Short.PartIIIb.Concrete
