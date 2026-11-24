import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.Symm

/-!
# `Y_p` bound of a bilinear convection field (`PartII-b:Q1` helper)

Source of record: `the November 2 reference manuscript`, lines 2503-2518.

`phaseLpNorm_eq_eLpNorm'` identifies `‖·‖_{Y_r}` with a multiple of the `L^r` norm on one phase
cell; `phaseLpNorm_add_le'` is Minkowski in `Y_p`, and `phaseLpNorm_bilin_le` bounds a field
pointwise dominated by `∑ₖ (|Dₖ| |v| + |u| |D'ₖ|)` with `|u| ≤ M`, `|v| ≤ N` a.e.:
`‖W‖_{Y_p} ≤ ∑ₖ (N ‖Dₖ‖_{Y_p} + M ‖D'ₖ‖_{Y_p})`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.QuadLeaf

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0412

theorem phaseLpNorm_eq_eLpNorm' (P r : ℝ) (hr : 0 < r) {f : ℝ × Space → CVec3}
    (hf : AEStronglyMeasurable f volume) :
    phaseLpNorm P r f =
      (ENNReal.ofReal P⁻¹) ^ (1 / r) * eLpNorm f (ENNReal.ofReal r) (cellμ P) := by
  have hae : AEMeasurable (fun z => ‖f z‖ₑ ^ r) (cellμ P) :=
    AEMeasurable.pow_const (AEStronglyMeasurable.enorm (hf.mono_ac (cellμ_ac P))) r
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  unfold phaseLpNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le, lintegral_prod _ hae,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hr.le)]

theorem bgp_pos' : (0 : ℝ) < bgp := by norm_num [bgp]

theorem one_le_ofReal_bgp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp :=
  ENNReal.one_le_ofReal.2 (by norm_num [bgp])

/-- Minkowski in `Y_p`. -/
theorem phaseLpNorm_add_le' (P : ℝ) {f g : ℝ × Space → CVec3}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    phaseLpNorm P bgp (fun x => f x + g x) ≤ phaseLpNorm P bgp f + phaseLpNorm P bgp g := by
  show phaseLpNorm P bgp (f + g) ≤ _
  rw [phaseLpNorm_eq_eLpNorm' P bgp bgp_pos' (hf.add hg), phaseLpNorm_eq_eLpNorm' P bgp bgp_pos' hf,
    phaseLpNorm_eq_eLpNorm' P bgp bgp_pos' hg, ← mul_add]
  gcongr
  exact eLpNorm_add_le (hf.mono_ac (cellμ_ac P)) (hg.mono_ac (cellμ_ac P)) one_le_ofReal_bgp

/-- `Y_p` bound of a field dominated by `∑ₖ (|Dₖ| |v| + |u| |D'ₖ|)` with bounded `u, v`. -/
theorem phaseLpNorm_bilin_le (P : ℝ) {W u v : ℝ × Space → CVec3}
    {D D' : Fin 3 → ℝ × Space → CVec3} (hW : AEStronglyMeasurable W volume)
    (hD : ∀ k, AEStronglyMeasurable (D k) volume) (hD' : ∀ k, AEStronglyMeasurable (D' k) volume)
    {M N : ℝ} (hM0 : 0 ≤ M) (hN0 : 0 ≤ N)
    (hM : ∀ᵐ x ∂(cellμ P), ‖u x‖ ≤ M) (hN : ∀ᵐ x ∂(cellμ P), ‖v x‖ ≤ N)
    (hpt : ∀ x, ‖W x‖ ≤ ∑ k : Fin 3, (‖D k x‖ * ‖v x‖ + ‖u x‖ * ‖D' k x‖)) :
    phaseLpNorm P bgp W ≤ ∑ k : Fin 3, (ENNReal.ofReal N * phaseLpNorm P bgp (D k) +
      ENNReal.ofReal M * phaseLpNorm P bgp (D' k)) := by
  have hDμ : ∀ k, AEStronglyMeasurable (fun x => ‖D k x‖) (cellμ P) := fun k =>
    ((hD k).mono_ac (cellμ_ac P)).norm
  have hD'μ : ∀ k, AEStronglyMeasurable (fun x => ‖D' k x‖) (cellμ P) := fun k =>
    ((hD' k).mono_ac (cellμ_ac P)).norm
  let G : Fin 3 → ℝ × Space → ℝ := fun k x => N * ‖D k x‖ + M * ‖D' k x‖
  have hGm : ∀ k, AEStronglyMeasurable (G k) (cellμ P) := fun k =>
    ((hDμ k).const_mul N).add ((hD'μ k).const_mul M)
  have h1 : eLpNorm W (ENNReal.ofReal bgp) (cellμ P) ≤
      eLpNorm (∑ k : Fin 3, G k) (ENNReal.ofReal bgp) (cellμ P) := by
    refine eLpNorm_mono_ae_real ?_
    filter_upwards [hM, hN] with x hMx hNx
    calc ‖W x‖ ≤ ∑ k : Fin 3, (‖D k x‖ * ‖v x‖ + ‖u x‖ * ‖D' k x‖) := hpt x
      _ ≤ ∑ k : Fin 3, G k x := Finset.sum_le_sum fun k _ => by
          have e1 : ‖D k x‖ * ‖v x‖ ≤ N * ‖D k x‖ := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_right hNx (norm_nonneg _)
          have e2 : ‖u x‖ * ‖D' k x‖ ≤ M * ‖D' k x‖ :=
            mul_le_mul_of_nonneg_right hMx (norm_nonneg _)
          simp only [G]
          linarith
      _ = (∑ k : Fin 3, G k) x := by rw [Finset.sum_apply]
  have h2 : eLpNorm (∑ k : Fin 3, G k) (ENNReal.ofReal bgp) (cellμ P) ≤
      ∑ k : Fin 3, eLpNorm (G k) (ENNReal.ofReal bgp) (cellμ P) :=
    eLpNorm_sum_le (fun k _ => hGm k) one_le_ofReal_bgp
  have h3 : ∀ k, eLpNorm (G k) (ENNReal.ofReal bgp) (cellμ P) ≤
      ENNReal.ofReal N * eLpNorm (D k) (ENNReal.ofReal bgp) (cellμ P) +
        ENNReal.ofReal M * eLpNorm (D' k) (ENNReal.ofReal bgp) (cellμ P) := by
    intro k
    have hsplit : G k = N • (fun x => ‖D k x‖) + M • (fun x => ‖D' k x‖) := by
      funext x
      simp [G, smul_eq_mul]
    rw [hsplit]
    refine (eLpNorm_add_le ((hDμ k).const_smul N) ((hD'μ k).const_smul M)
      one_le_ofReal_bgp).trans (le_of_eq ?_)
    rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_norm, eLpNorm_norm,
      Real.enorm_of_nonneg hN0, Real.enorm_of_nonneg hM0]
  rw [phaseLpNorm_eq_eLpNorm' P bgp bgp_pos' hW]
  calc (ENNReal.ofReal P⁻¹) ^ (1 / bgp) * eLpNorm W (ENNReal.ofReal bgp) (cellμ P)
      ≤ (ENNReal.ofReal P⁻¹) ^ (1 / bgp) *
          ∑ k : Fin 3, (ENNReal.ofReal N * eLpNorm (D k) (ENNReal.ofReal bgp) (cellμ P) +
            ENNReal.ofReal M * eLpNorm (D' k) (ENNReal.ofReal bgp) (cellμ P)) := by
        gcongr
        exact h1.trans (h2.trans (Finset.sum_le_sum fun k _ => h3 k))
    _ = ∑ k : Fin 3, (ENNReal.ofReal N * phaseLpNorm P bgp (D k) +
          ENNReal.ofReal M * phaseLpNorm P bgp (D' k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [phaseLpNorm_eq_eLpNorm' P bgp bgp_pos' (hD k),
          phaseLpNorm_eq_eLpNorm' P bgp bgp_pos' (hD' k)]
        ring

end UnforcedLeray.Short.IIb.QuadLeaf
