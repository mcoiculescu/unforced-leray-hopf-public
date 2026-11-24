import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Units.B0425

/-!
# Part II-a, task `PartII-a:F06/1/2`: a.e.-periodic centre averaging (`PeriodAverageAE`)

Periodise an a.e.-`P`-periodic density `h` by `g τ = h' (τ - P ⌊τ/P⌋)` (with `h'` a measurable
representative of `h`), then apply `B0425.lintegral_center_average` to `g`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa

theorem periodAverageAE : PeriodAverageAE := by
  intro P hP h hh hper I _hI
  set h' := hh.mk h with hh'def
  have hh'm : Measurable h' := hh.measurable_mk
  have hae1 : ∀ᵐ x : ℝ, h' x = h x := hh.ae_eq_mk.symm
  -- shifts by nonnegative multiples of `P`
  have hshift : ∀ n : ℕ, ∀ᵐ τ : ℝ, h (τ + (n : ℝ) * P) = h τ := by
    intro n
    induction n with
    | zero => exact Filter.Eventually.of_forall fun τ => by simp
    | succ n ih =>
      filter_upwards [(measurePreserving_add_right volume P).quasiMeasurePreserving.ae ih,
        hper] with τ h1 h2
      have e : τ + ((((n + 1 : ℕ)) : ℝ)) * P = τ + P + (n : ℝ) * P := by push_cast; ring
      rw [e, h1, h2]
  -- all integer shifts
  have hshiftZ : ∀ k : ℤ, ∀ᵐ τ : ℝ, h (τ + (k : ℝ) * P) = h τ := by
    intro k
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · simpa using hshift n
    · filter_upwards [(measurePreserving_add_right volume (-((n : ℝ) * P))).quasiMeasurePreserving.ae
        (hshift n)] with τ h1
      have e1 : τ + (((-(n : ℤ)) : ℤ) : ℝ) * P = τ + -((n : ℝ) * P) := by push_cast; ring
      have e2 : τ + -((n : ℝ) * P) + (n : ℝ) * P = τ := by ring
      rw [e1]
      rw [e2] at h1
      exact h1.symm
  -- a.e. identity of `h'` with `h` along all integer shifts
  have hC : ∀ᵐ τ : ℝ, ∀ k : ℤ, h' (τ + (k : ℝ) * P) = h (τ + (k : ℝ) * P) := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_add_right volume ((k : ℝ) * P)).quasiMeasurePreserving.ae hae1
  have hgh : ∀ᵐ τ : ℝ, h' (τ + ((-⌊τ / P⌋ : ℤ) : ℝ) * P) = h τ := by
    filter_upwards [hC, ae_all_iff.2 hshiftZ] with τ h1 h2
    rw [h1 _, h2 _]
  -- the periodisation
  set g : ℝ → ℝ≥0∞ := fun τ => h' (τ + ((-⌊τ / P⌋ : ℤ) : ℝ) * P) with hg
  have hfl : Measurable fun τ : ℝ => ((-⌊τ / P⌋ : ℤ) : ℝ) :=
    (measurable_of_countable (fun n : ℤ => ((-n : ℤ) : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.div_const P))
  have hgm : Measurable g := by
    rw [hg]
    exact hh'm.comp (measurable_id.add (hfl.mul_const P))
  have hgper : Function.Periodic g P := by
    intro τ
    have hfl' : ⌊(τ + P) / P⌋ = ⌊τ / P⌋ + 1 := by
      rw [add_div, div_self hP.ne']
      exact Int.floor_add_one _
    simp only [hg, hfl']
    congr 1
    push_cast
    ring
  have hgh' : ∀ᵐ τ : ℝ, h τ = g τ := by
    filter_upwards [hgh] with τ hτ
    rw [hg]
    exact hτ.symm
  have hkey : ∀ τ₀ : ℝ, ∫⁻ t in I, h (τ₀ + t) = ∫⁻ t in I, g (τ₀ + t) := by
    intro τ₀
    apply lintegral_congr_ae
    apply ae_restrict_of_ae
    filter_upwards [(measurePreserving_add_left volume τ₀).quasiMeasurePreserving.ae hgh'] with t ht
    exact ht
  have hstep : ∫⁻ τ₀ in Ioc 0 P, ∫⁻ t in I, h (τ₀ + t) =
      ∫⁻ τ₀ in Ioc 0 P, ∫⁻ t in I, g (τ₀ + t) :=
    lintegral_congr fun τ₀ => hkey τ₀
  rw [hstep, UnforcedLeray.B0425.lintegral_center_average hgm hgper I]
  congr 1
  apply lintegral_congr_ae
  exact ae_restrict_of_ae (hgh'.mono fun τ hτ => hτ.symm)

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.periodAverageAE
