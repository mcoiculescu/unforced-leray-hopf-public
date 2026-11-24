import UnforcedLeray.Analysis.Rayleigh.Compactness
import UnforcedLeray.Analysis.Rayleigh.ZeroExtension
import UnforcedLeray.Analysis.Rayleigh.MassLocalization
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact mass convergence and preservation of a nonzero annular limit

Uniform convergence on a fixed compact set and the actual common supremum
bound give convergence of the squared mass by dominated convergence. The
Gaussian potential estimate supplies a fixed compact interval containing at
least 3/8 of each normalized annular mode's mass. Thus an extracted local
uniform limit is nonzero even as an almost-everywhere equivalence class.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.Rayleigh

/-- Local mass of the zero extension is exactly mass on the intersected annulus. -/
theorem setIntegral_norm_sq_zeroExtension (l r : ℝ) (F : ℝ → ℂ) (S : Set ℝ) :
    (∫ t in S, ‖zeroExtension l r F t‖ ^ 2) =
      ∫ t in S ∩ Ioc l r, ‖F t‖ ^ 2 := by
  have he : (fun t => ‖zeroExtension l r F t‖ ^ 2) =
      (Ioc l r).indicator (fun t => ‖F t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ Ioc l r <;> simp [zeroExtension, ht]
  rw [he, setIntegral_indicator measurableSet_Ioc]

/-- The same fixed compact interval captures mass of every actual zero extension. -/
theorem exists_uniform_zeroExtension_local_mass :
    ∃ R : ℝ, 0 < R ∧ ∀ (q : ℝ → ℝ) (z : ℂ) (F : ℝ → ℂ) (l r : ℝ),
      ShiftedAnnularMode q z F l r →
      (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1 →
      (3 / 8 : ℝ) ≤ ∫ t in Icc (-R) R, ‖zeroExtension l r F t‖ ^ 2 := by
  obtain ⟨R, hR, hm⟩ := exists_uniform_local_mass
  refine ⟨R, hR, ?_⟩
  intro q z F l r h hn
  rw [setIntegral_norm_sq_zeroExtension]
  exact hm q z F l r h hn

/-- Genuine compact-set mass convergence; the constant majorant is integrable
because compact real intervals and compact real subsets have finite volume. -/
theorem tendsto_compact_mass_of_uniform_bound
    (F : ℕ → ℝ → ℂ) {f : ℝ → ℂ} (hF : ∀ n, Continuous (F n))
    (M : ℝ) (hsup : ∀ n x, ‖F n x‖ ≤ M)
    {S : Set ℝ} (hS : IsCompact S) (hu : TendstoUniformlyOn F f atTop S) :
    Tendsto (fun n => ∫ t in S, ‖F n t‖ ^ 2) atTop
      (𝓝 (∫ t in S, ‖f t‖ ^ 2)) := by
  have hM : 0 ≤ M := (norm_nonneg (F 0 0)).trans (hsup 0 0)
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_ne_top
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => M ^ 2)
  · intro n
    exact ((hF n).norm.pow 2).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (hsup n t)
  · filter_upwards [ae_restrict_mem hS.measurableSet] with t ht
    exact (hu.tendsto_at ht).norm.pow 2

/-- A positive compact mass lower bound survives local uniform convergence and
rules out the zero almost-everywhere class. -/
theorem nonzero_of_compact_mass_limit
    (F : ℕ → ℝ → ℂ) {f : ℝ → ℂ} (hF : ∀ n, Continuous (F n))
    (M : ℝ) (hsup : ∀ n x, ‖F n x‖ ≤ M)
    {S : Set ℝ} (hS : IsCompact S) (hu : TendstoUniformlyOn F f atTop S)
    {a : ℝ} (ha : 0 < a) (hmass : ∀ n, a ≤ ∫ t in S, ‖F n t‖ ^ 2) :
    a ≤ (∫ t in S, ‖f t‖ ^ 2) ∧ ¬ f =ᵐ[volume] (0 : ℝ → ℂ) := by
  have hlim := tendsto_compact_mass_of_uniform_bound F hF M hsup hS hu
  have hl := ge_of_tendsto hlim (Eventually.of_forall hmass)
  refine ⟨hl, ?_⟩
  intro hz
  have hi : (∫ t in S, ‖f t‖ ^ 2) = 0 := by
    calc
      _ = ∫ t in S, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hz] with t ht
        simp [ht]
      _ = 0 := by simp
  rw [hi] at hl
  exact (not_le_of_gt ha) hl

/-- Actual annular ODEs and their normalization supply the local mass premise;
only the independently derived common extension modulus and bound are needed
for this application of the compactness theorem. -/
theorem exists_nonzero_annular_limit
    (q : ℕ → ℝ → ℝ) (z : ℕ → ℂ) (F : ℕ → ℝ → ℂ) (l r : ℕ → ℝ)
    (hmode : ∀ n, ShiftedAnnularMode (q n) (z n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1)
    (hext : ∀ n, Continuous (zeroExtension (l n) (r n) (F n)))
    (M K : ℝ)
    (hsup : ∀ n x, ‖zeroExtension (l n) (r n) (F n) x‖ ≤ M)
    (hmod : ∀ n x y,
      ‖zeroExtension (l n) (r n) (F n) x - zeroExtension (l n) (r n) (F n) y‖ ≤
        K * Real.sqrt |x - y|) :
    ∃ (f : ℝ → ℂ) (φ : ℕ → ℕ), Continuous f ∧ StrictMono φ ∧
      TendstoLocallyUniformly
        (fun n => zeroExtension (l (φ n)) (r (φ n)) (F (φ n))) f atTop ∧
      ¬ f =ᵐ[volume] (0 : ℝ → ℂ) := by
  let E : ℕ → ℝ → ℂ := fun n => zeroExtension (l n) (r n) (F n)
  obtain ⟨f, φ, hf, hφ, hu, _, _⟩ :=
    exists_uniformOnCompacts_subsequence_of_sup_sqrt_bound E hext M K hsup hmod
  obtain ⟨R, _, hR⟩ := exists_uniform_zeroExtension_local_mass
  have hlocal := fun n => hR (q (φ n)) (z (φ n)) (F (φ n)) (l (φ n)) (r (φ n))
    (hmode (φ n)) (hmass (φ n))
  have hn := (nonzero_of_compact_mass_limit (fun n => E (φ n)) (fun n => hext (φ n))
    M (fun n => hsup (φ n)) isCompact_Icc (hu _ isCompact_Icc)
    (show (0 : ℝ) < 3 / 8 by norm_num) hlocal).2
  exact ⟨f, φ, hf, hφ, tendstoLocallyUniformly_iff_forall_isCompact.mpr hu, hn⟩

end UnforcedLeray.Rayleigh
