import UnforcedLeray.Analysis.Rayleigh.JointCompactness
import UnforcedLeray.Analysis.Rayleigh.LocalUniformPairing
import UnforcedLeray.Analysis.Rayleigh.WeakSecondLimit

/-!
# A genuine nonzero H² limit of expanding Gaussian annular modes

The local-uniform nonzero limit and the weak L²/H² limit are identified by
actual complex test integrals. The resulting continuous representative is
itself H². All compactness and norm bounds are derived from the normalized
annular differential problem; no finite zero extension is called H².
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.Rayleigh
open Sturm NonUniqueEuler.Sob

/-- Actual nonzero continuous H² compactness, with a common speed and weak
field/derivative/residual subsequence and explicit quotient representatives. -/
theorem exists_nonzero_H2_gaussian_annular_limit
    (c : ℕ → ℂ) (F : ℕ → ℝ → ℂ) (l r : ℕ → ℝ)
    (hmode : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1)
    (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop) :
    ∃ (cLimit : ℂ) (f : ℝ → ℂ) (u g k : ComplexL2) (φ : ℕ → ℕ),
      StrictMono φ ∧ Continuous f ∧ MemLp f 2 volume ∧
      (∫ t, ‖f t‖ ^ 2) ≤ 1 ∧ ¬ f =ᵐ[volume] (0 : ℝ → ℂ) ∧
      f =ᵐ[volume] (u : ℝ → ℂ) ∧ u ≠ 0 ∧
      MemH1On 2 univ f ∧ MemH1On 2 univ (u : ℝ → ℂ) ∧
      HasWeakDerivOn univ [1] (u : ℝ → ℂ) (g : ℝ → ℂ) ∧
      HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ)
        ((k + (4 : ℂ) • u : ComplexL2) : ℝ → ℂ) ∧
      ‖u‖ ≤ 1 ∧ ‖g‖ ≤ 2 ∧ ‖k‖ ≤ 8 ∧
      Tendsto (fun n => c (φ n)) atTop (𝓝 cLimit) ∧
      0 ≤ cLimit.im ∧ ‖cLimit‖ ≤ 2 ∧
      TendstoLocallyUniformly
        (fun n => zeroExtension (l (φ n)) (r (φ n)) (F (φ n))) f atTop ∧
      WeakL2.WeakTendsto (fun n => (hmode (φ n)).toShifted.fieldL2) atTop u ∧
      WeakL2.WeakTendsto (fun n => (hmode (φ n)).toShifted.derivativeL2) atTop g ∧
      WeakL2.WeakTendsto (fun n => (hmode (φ n)).toShifted.residualL2) atTop k := by
  obtain ⟨cLimit, f, φ, hφ, hfcont, hfmem, hfmass, hfne, hc, hcim, hcnorm, hlocal⟩ :=
    exists_joint_gaussian_annular_limit c F l r hmode hmass
  obtain ⟨ψ, hψ, u, g, k, hun, hgn, hkn, huH2, hdu, hddu, hwu, hwg, hwk⟩ :=
    exists_common_H2_weak_subsequence (fun n => (hmode (φ n)).toShifted)
      (fun n => hmass (φ n)) (hl.comp hφ.tendsto_atTop) (hr.comp hφ.tendsto_atTop)
  have hlocal' := locallyUniform_subseq hlocal hψ
  have hcont : ∀ n, Continuous
      (zeroExtension (l (φ (ψ n))) (r (φ (ψ n))) (F (φ (ψ n)))) := by
    intro n
    exact zeroExtension_continuous (hmode (φ (ψ n))).regularity.continuous
      (hmode (φ (ψ n))).ordered (hmode (φ (ψ n))).left_endpoint
      (hmode (φ (ψ n))).right_endpoint
  have hbound : ∀ n t,
      ‖zeroExtension (l (φ (ψ n))) (r (φ (ψ n))) (F (φ (ψ n))) t‖ ≤ 4 := by
    intro n t
    exact (hmode (φ (ψ n))).toShifted.normalized_zeroExtension_bound
      (hmass (φ (ψ n))) t
  have hpair : ∀ ξ : ℝ → ℂ, MemLp ξ 2 volume →
      Tendsto (fun n => ∫ t,
        zeroExtension (l (φ (ψ n))) (r (φ (ψ n))) (F (φ (ψ n))) t * ξ t)
        atTop (𝓝 (∫ t, u t * ξ t)) := by
    intro ξ hξ
    simpa only [ShiftedAnnularMode.integral_fieldL2_mul] using
      weakTendsto_integral_mul hwu ξ hξ
  have hae : f =ᵐ[volume] (u : ℝ → ℂ) :=
    ae_eq_of_locallyUniform_and_pairing_limit _ hcont 4 hbound
      hfmem (Lp.memLp u) hlocal' hpair
  have hune : u ≠ 0 := by
    intro hu0
    apply hfne
    rw [hu0] at hae
    exact hae.trans (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ))
  have hfH2 : MemH1On 2 univ f := by
    refine ⟨by simpa using hfmem, ?_⟩
    intro j hj
    obtain ⟨v, hv, hder⟩ := huH2.deriv j hj
    refine ⟨v, hv, hder.congr_ae ?_ ?_⟩
    · filter_upwards [hae] with t ht
      intro _
      exact ht.symm
    · exact Eventually.of_forall fun _ _ => rfl
  exact ⟨cLimit, f, u, g, k, φ ∘ ψ, hφ.comp hψ, hfcont, hfmem, hfmass, hfne,
    hae, hune, hfH2, huH2, hdu, hddu, hun, hgn, hkn, hc.comp hψ.tendsto_atTop,
    hcim, hcnorm, hlocal', hwu, hwg, hwk⟩

end UnforcedLeray.Rayleigh
