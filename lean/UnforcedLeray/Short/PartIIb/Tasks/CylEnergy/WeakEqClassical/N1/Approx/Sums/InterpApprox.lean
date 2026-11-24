import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.Interp1D
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.InterpCommute
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.CutModuliPlanar
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.AgeDerivModulus

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
Choose `K` with `2h` below the moduli of `cutTest` (`CutModuliPlanar`), of the age derivative
(`AgeDerivModulus`), and apply the scalar estimates (`Interp1D`) together with the commutation
of planar derivatives with the age interpolation (`InterpCommute`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

theorem interpApprox : UnforcedLeray.Short.IIb.TdSums.InterpApprox := by
  intro c t₀ t₁ R φ hc hR ht hφ ε hε
  obtain ⟨A, hA0, hAI⟩ := (interp1D : UnforcedLeray.Short.IIb.TdSums.Interp1D)
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = ε / (4 * (A + 1)) := ⟨_, rfl⟩
  have hwpos : 0 < w := by
    rw [hwdef]
    exact div_pos hε (by linarith)
  have hwε : w * (4 * (A + 1)) = ε := by
    rw [hwdef]
    exact div_mul_cancel₀ ε (by linarith : (0 : ℝ) < 4 * (A + 1)).ne'
  have hAw : 4 * (A * w) ≤ ε := by nlinarith
  have hAw' : A * w ≤ ε := by nlinarith [mul_nonneg hA0 hwpos.le]
  obtain ⟨δ₁, hδ₁, hCM⟩ := cutModuliPlanar c t₀ t₁ R φ hc hR hφ w hwpos
  obtain ⟨δ₂, hδ₂, hAD⟩ := ageDerivModulus c t₀ t₁ R φ hc hR hφ w hwpos
  obtain ⟨δ, hδ, hδ₁', hδ₂'⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ :=
    ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * (t₁ - t₀) / δ)
  have h0 : 0 ≤ 2 * (t₁ - t₀) / δ := div_nonneg (by linarith) hδ.le
  have hKpos : (0 : ℝ) < K := lt_of_le_of_lt h0 hK
  have hKN : 0 < K := by exact_mod_cast hKpos
  have hgrid : 2 * gridH t₀ t₁ K ≤ δ := by
    have h1 : 2 * (t₁ - t₀) < K * δ := by
      have := (div_lt_iff₀ hδ).mp hK
      linarith
    unfold gridH
    rw [← mul_div_assoc, div_le_iff₀ hKpos]
    linarith [mul_comm δ (K : ℝ)]
  have hgrid₁ : 2 * gridH t₀ t₁ K ≤ δ₁ := le_trans hgrid hδ₁'
  have hgrid₂ : 2 * gridH t₀ t₁ K ≤ δ₂ := le_trans hgrid hδ₂'
  refine ⟨K, fun r hr x => ?_, fun r hr x => ?_⟩
  · -- planar part: value and planar derivatives of the interpolant
    have hcom := interpCommute c t₀ t₁ R K φ hR ht hφ r x
    have e0 : |sepApprox t₀ t₁ K R φ r x - cutTest R φ r x| ≤ A * w :=
      (hAI t₀ t₁ K ht hKN).1 (fun s => cutTest R φ s x) w
        (fun r hr r' hr' hd => (hCM r hr r' hr' (le_trans hd hgrid₁) x).1) r hr
    have e1 : |B0579.pd 0 (sepApprox t₀ t₁ K R φ r) x - B0579.pd 0 (cutTest R φ r) x| ≤ A * w := by
      rw [hcom.1 0]
      exact (hAI t₀ t₁ K ht hKN).1 (fun s => B0579.pd 0 (cutTest R φ s) x) w
        (fun r hr r' hr' hd => (hCM r hr r' hr' (le_trans hd hgrid₁) x).2.1) r hr
    have e2 : |B0579.pd 1 (sepApprox t₀ t₁ K R φ r) x - B0579.pd 1 (cutTest R φ r) x| ≤ A * w := by
      rw [hcom.1 1]
      exact (hAI t₀ t₁ K ht hKN).1 (fun s => B0579.pd 1 (cutTest R φ s) x) w
        (fun r hr r' hr' hd => (hCM r hr r' hr' (le_trans hd hgrid₁) x).2.2.1) r hr
    have e3 : |lapP (sepApprox t₀ t₁ K R φ r) x - lapP (cutTest R φ r) x| ≤ A * w := by
      rw [hcom.2]
      exact (hAI t₀ t₁ K ht hKN).1 (fun s => lapP (cutTest R φ s) x) w
        (fun r hr r' hr' hd => (hCM r hr r' hr' (le_trans hd hgrid₁) x).2.2.2) r hr
    unfold planarErr
    linarith
  · -- age derivative part
    have hcut : ∀ r ∈ Ioo t₀ t₁, HasDerivAt (fun s => cutTest R φ s x)
        (etaCut R x * deriv (fun s => φ s x) r) r := by
      intro r hr
      have hnhds : Icc t₀ t₁ ×ˢ (univ : Set B0579.Plane) ∈ 𝓝 (r, x) :=
        prod_mem_nhds (Icc_mem_nhds hr.1 hr.2) univ_mem
      have hdiff : DifferentiableAt ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x) :=
        (hφ.smooth.contDiffAt hnhds).differentiableAt (by simp)
      have hγ : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : B0579.Plane)) r :=
        (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
      have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt r hγ
      have hd : DifferentiableAt ℝ (fun s => φ s x) r := hcomp.differentiableAt
      exact hd.hasDerivAt.const_mul (etaCut R x)
    have hcontG : ContinuousOn (fun s => cutTest R φ s x) (Icc t₀ t₁) := by
      have h2 : ContinuousOn (fun s : ℝ => ((s, x) : ℝ × B0579.Plane)) (Icc t₀ t₁) :=
        (by fun_prop : Continuous (fun s : ℝ => ((s, x) : ℝ × B0579.Plane))).continuousOn
      have h3 : ContinuousOn (fun s : ℝ => φ s x) (Icc t₀ t₁) :=
        hφ.smooth.continuousOn.comp h2 (fun s hs => ⟨hs, mem_univ _⟩)
      have h4 : ContinuousOn (fun s : ℝ => etaCut R x * φ s x) (Icc t₀ t₁) :=
        continuousOn_const.mul h3
      exact h4
    have hosc : ∀ r ∈ Ioo t₀ t₁, ∀ r' ∈ Ioo t₀ t₁, |r - r'| ≤ 2 * gridH t₀ t₁ K →
        |etaCut R x * deriv (fun s => φ s x) r - etaCut R x * deriv (fun s => φ s x) r'| ≤ w :=
      fun r hr r' hr' hd => hAD r hr r' hr' (le_trans hd hgrid₂) x
    have hfin : |deriv (interp1 t₀ t₁ K (fun s => cutTest R φ s x)) r
        - etaCut R x * deriv (fun s => φ s x) r| ≤ A * w :=
      (hAI t₀ t₁ K ht hKN).2 (fun s => cutTest R φ s x)
        (fun s => etaCut R x * deriv (fun s' => φ s' x) s) w hcontG hcut hosc r hr
    exact le_trans hfin hAw'

end TdSums

end UnforcedLeray.Short.IIb
