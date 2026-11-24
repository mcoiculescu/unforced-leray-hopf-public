import UnforcedLeray.Short.PartI.Sub.C09
import UnforcedLeray.Short.PartI.Sub.C09.RemOrigEst

/-!


Source of record: `the November 2 reference manuscript`, lines 1139-1143
(gluing across the origin).  Statement: `RemovableOrigin` of `Short/PartI/Sub/C09.lean`.

Proof: for a test function `φ` on `ℝ²`, the test function `ψ_ε = φ - φ·χ_ε` vanishes near `0`
(`χ_ε(z) = Gfun(z/ε)`, `χ_ε = 1` on the square of half-side `ε`, `0` off the square of half-side
`2ε`), so the hypothesis applies to `ψ_ε`.  Expanding `Δψ_ε` by Leibniz gives, for every `ε > 0`,
`∫ uΔφ - ∫ Fφ = D(ε) + R(ε)` with `D(ε) → 0` (dominated convergence) and `R(ε) = O(ε)` (the
`O(|z|)` bound of `u` on the square of half-side `2ε`, against `ε⁻²` derivatives of `χ_ε`).
Uniqueness of limits gives `∫ uΔφ = ∫ Fφ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob

theorem removableOrigin : RemovableOrigin := by
  intro u F hu hF hO hWL φ hφ
  obtain ⟨C, δ, hδ, hC⟩ := hO
  have hu' : LocallyIntegrableOn u univ := hu.locallyIntegrableOn univ
  have hF' : LocallyIntegrableOn F univ := hF.locallyIntegrableOn univ
  have hL : IsTestFn univ (RemOrig.lapf φ) := RemOrig.lapf_testFn hφ
  have hI1 : Integrable (fun z => u z * RemOrig.lapf φ z) := integrable_mul_testFn hu' hL
  have hI4 : Integrable (fun z => F z * φ z) := integrable_mul_testFn hF' hφ
  -- Identity for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε →
      (∫ z, u z * RemOrig.lapf φ z) - (∫ z, F z * φ z)
        = ((∫ z, u z * (RemOrig.cutG ε z * RemOrig.lapf φ z))
            - ∫ z, F z * (RemOrig.cutG ε z * φ z))
          + ∫ z, u z * RemOrig.Tfun φ ε z := by
    intro ε hε
    have hψ := RemOrig.isTestFn_psi hφ hε
    have h : ∫ z, u z * RemOrig.lapf (fun y => φ y - φ y * RemOrig.cutG ε y) z
        = ∫ z, F z * (φ z - φ z * RemOrig.cutG ε z) := hWL _ hψ
    have hI2 : Integrable (fun z => u z * (RemOrig.cutG ε z * RemOrig.lapf φ z)) :=
      integrable_mul_testFn hu' (RemOrig.isTestFn_mul_smooth (RemOrig.cutG_contDiff ε) hL)
    have hI3 : Integrable (fun z => u z * RemOrig.Tfun φ ε z) :=
      integrable_mul_testFn hu' (RemOrig.Tfun_testFn hφ ε)
    have hI5 : Integrable (fun z => F z * (RemOrig.cutG ε z * φ z)) :=
      integrable_mul_testFn hF' (RemOrig.isTestFn_mul_smooth (RemOrig.cutG_contDiff ε) hφ)
    have hpt1 : (fun z => u z * RemOrig.lapf (fun y => φ y - φ y * RemOrig.cutG ε y) z)
        = fun z => (u z * RemOrig.lapf φ z - u z * (RemOrig.cutG ε z * RemOrig.lapf φ z))
            - u z * RemOrig.Tfun φ ε z := by
      funext z
      rw [RemOrig.lapf_psi φ hφ.smooth ε z]
      unfold RemOrig.Tfun
      ring
    have hpt2 : (fun z => F z * (φ z - φ z * RemOrig.cutG ε z))
        = fun z => F z * φ z - F z * (RemOrig.cutG ε z * φ z) := by
      funext z
      ring
    have hAB : Integrable (fun z => u z * RemOrig.lapf φ z
        - u z * (RemOrig.cutG ε z * RemOrig.lapf φ z)) := hI1.sub hI2
    have eU : ∫ z, u z * RemOrig.lapf (fun y => φ y - φ y * RemOrig.cutG ε y) z
        = (∫ z, u z * RemOrig.lapf φ z) - (∫ z, u z * (RemOrig.cutG ε z * RemOrig.lapf φ z))
          - ∫ z, u z * RemOrig.Tfun φ ε z := by
      rw [hpt1, integral_sub hAB hI3, integral_sub hI1 hI2]
    have eF : ∫ z, F z * (φ z - φ z * RemOrig.cutG ε z)
        = (∫ z, F z * φ z) - ∫ z, F z * (RemOrig.cutG ε z * φ z) := by
      rw [hpt2, integral_sub hI4 hI5]
    linear_combination h - eU + eF
  -- The two limits as `ε → 0⁺`.
  have hD1 : Tendsto (fun ε : ℝ => ∫ z, u z * (RemOrig.cutG ε z * RemOrig.lapf φ z))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine (RemOrig.tendsto_cut_integral hI1).congr (fun ε => ?_)
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  have hD2 : Tendsto (fun ε : ℝ => ∫ z, F z * (RemOrig.cutG ε z * φ z))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine (RemOrig.tendsto_cut_integral hI4).congr (fun ε => ?_)
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  have hD : Tendsto (fun ε : ℝ => (∫ z, u z * (RemOrig.cutG ε z * RemOrig.lapf φ z))
      - ∫ z, F z * (RemOrig.cutG ε z * φ z)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hD1.sub hD2
    rwa [sub_zero] at this
  -- The cross term is `O(ε)`.
  have hR : Tendsto (fun ε : ℝ => ∫ z, u z * RemOrig.Tfun φ ε z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    obtain ⟨K, hK⟩ := RemOrig.R_bound hδ hC hφ
    refine squeeze_zero_norm' (a := fun ε : ℝ => K * ε) ?_ ?_
    · have hm : (0 : ℝ) < min (δ / 2) 1 := lt_min (half_pos hδ) one_pos
      filter_upwards [Ioo_mem_nhdsGT hm] with ε hε
      have h2 : 2 * ε < δ := by
        have := min_le_left (δ / 2) 1
        linarith [hε.2]
      have h1 : ε ≤ 1 := by
        have := min_le_right (δ / 2) 1
        linarith [hε.2]
      exact hK ε hε.1 h2 h1
    · have hlin : Tendsto (fun ε : ℝ => K * ε) (𝓝 0) (𝓝 0) := by
        have h : Tendsto (fun ε : ℝ => K * ε) (𝓝 0) (𝓝 (K * 0)) := tendsto_id.const_mul K
        rwa [mul_zero] at h
      exact hlin.mono_left nhdsWithin_le_nhds
  -- Pass to the limit in the identity.
  have hsum := hD.add hR
  rw [add_zero] at hsum
  have heq : (fun _ : ℝ => (∫ z, u z * RemOrig.lapf φ z) - ∫ z, F z * φ z)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ((∫ z, u z * (RemOrig.cutG ε z * RemOrig.lapf φ z))
            - ∫ z, F z * (RemOrig.cutG ε z * φ z))
          + ∫ z, u z * RemOrig.Tfun φ ε z) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact key ε hε
  have hlim := tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds hsum heq
  exact sub_eq_zero.1 hlim

end UnforcedLeray.Short.PartI
