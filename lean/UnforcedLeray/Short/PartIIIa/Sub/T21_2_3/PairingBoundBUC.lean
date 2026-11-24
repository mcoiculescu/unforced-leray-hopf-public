import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Part III-a, `PartIII-a:T21/2/3`: the duality pairing bound for the BUC train

Source of record: `the November 2 reference manuscript` (SP), lines 3036-3040
(`<J_a⁻¹ f, φ> = a<f, φ(·/√a)>`), 3044 (equivalence of `p_d` and `⟨y⟩^{2m}`), 3074-3075
("By duality, the moving weak-to-strong norm is at most ..."), with the train of SP 270-288 and
the weight `m > 8` of SP 2824.

`AdjointPairingBound m` (`Clock/WeakSmoothing/Adjoint.lean`) is stated for `ν ≤ ν₀` and the BUC
trains `PartI.IsBUCTrain`. `adjointPairingBoundBUC_of` assembles it from the BUC weak duality
`LinAdjDualityBUC` (`Sub/T21_2_3/LinAdjDualitySub.lean`) and the train-free leaves `PairingCoV`,
`MovingPhiH1`, `H1BySeminorm`, `NegNormPairing` (`Sub/PartIIIa_T21_2_3.lean`): the chain
`∫_{C_{d_s}} W(z_s)G = ∫_{C_c} w(s) g = ∫_{C_c} f φ(t) = ∫_{C_{d_t}} J_{a_t}⁻¹f Φ(z_t)`, then
`|∫ F Φ| ≤ ‖F‖_{(H¹_{-m})*} ‖Φ‖_{H¹_{-m}}` and `‖Φ‖_{H¹_{-m}} ≤ C (E_0 + E_1)^{1/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Assembly** of `AdjointPairingBound` for the BUC train (SP 3036-3040, 3044, 3074-3075):
the `ν₀` is that of `LinAdjDualityBUC`. -/
theorem adjointPairingBoundBUC_of (m : ℝ) (hm : 8 < m) (h1 : LinAdjDualityBUC m)
    (h2 : PairingCoV) (h3 : MovingPhiH1 m) (h4 : H1BySeminorm m) (h5 : NegNormPairing) :
    AdjointPairingBound m := by
  obtain ⟨ν₀, hν₀, h1⟩ := h1
  obtain ⟨C, hC0, hC⟩ := h4 (by linarith)
  refine ⟨C, ν₀, hC0, hν₀, ?_⟩
  intro ν hν' tr htr t s ht hts G hG φ hφ f hf hf0 w u hw
  have hν : 0 < ν := hν'.1
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have has : 0 < clockA ν s := by unfold clockA; have : 0 ≤ s := ht.trans hts.le; positivity
  have hat : 0 < clockA ν t := by unfold clockA; positivity
  have hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν t) := by
    unfold cellLen; exact div_pos hc (Real.sqrt_pos.mpr hat)
  have e1 := h2 _ _ hc has (w s) G
  have e2 := h1 ν hν' tr htr t s ht hts _ φ hφ f hf hf0 w u hw
  have e3 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f x * φ t x =
      ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)),
        JscaleInv (clockA ν t) f y * movingPhi ν φ t y := by
    rw [h2 _ _ hc hat f (movingPhi ν φ t)]
    simp only [physAdj_movingPhi hν ht]
  obtain ⟨hd, hmem, hmem'⟩ := h3 ν hν tr t s ht hts _ φ hφ
  have hbound := hC _ hdt (movingPhi ν φ t) hmem hmem'
  have hfin : h1Norm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (movingPhi ν φ t)
      (fun j => pdCx j (movingPhi ν φ t)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hp := h5 _ m (JscaleInv (clockA ν t) f) (movingPhi ν φ t) _ hd hfin
  have hrev : revE0 ν (ν ^ (-2 : ℝ)) m φ s (deltaZ ν t s) +
      revE1 ν (ν ^ (-2 : ℝ)) m φ s (deltaZ ν t s) =
      adjE0 (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (movingPhi ν φ t) +
        adjE1 (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (movingPhi ν φ t) := by
    unfold revE0 revE1
    rw [revAge_deltaZ hν ht]
  rw [e1, e2, e3, hrev]
  exact hp.trans (by gcongr)

end UnforcedLeray.Short.IIIa
