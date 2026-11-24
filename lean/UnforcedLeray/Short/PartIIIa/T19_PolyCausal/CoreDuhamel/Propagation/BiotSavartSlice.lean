import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.WeakCellAeUnique

/-!
# Part III-a, leaf `PartIII-a:T19/2/3/1`: the Biot-Savart slice bound

Source of record: `the November 2 reference manuscript` (SP), lines 3497-3515
(zero-circulation Biot-Savart reconstruction `‖K_c ω‖_{H¹} ≤ C ‖ω‖_{X_m}` and the identification
of the velocity with the Biot-Savart velocity of its curl: the discrepancy is divergence free and
curl free, hence vanishes).

`coreBiotSavartSliceBound : CoreBiotSavartSliceBound`. A divergence-free `L²(cell c)` velocity
`u` with weak gradient `G` is a Biot-Savart velocity of its weak curl `ω = G 1 0 - G 0 1`
(`isBiotSavart_of_weakGrad`). By `CTE.isBiotSavart_unique` (Liouville on the cylinder) it agrees
a.e. on the cell with the reconstruction `(u', G')` of `ω` supplied by the hypothesis, and by
`weakCellAeUnique` (uniqueness of weak cell derivatives) `G = G'` a.e. on the cell. The bounds of
the reconstruction therefore transfer to `(u, G)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- A divergence-free `L²(cell c)` velocity `u` with weak cell gradient `G` (`G x i j = ∂_j u_i`)
is a Biot-Savart velocity of its weak curl `G 1 0 - G 0 1` (SP 3497-3515). -/
theorem isBiotSavart_of_weakGrad {c : ℝ} {u : ℝ × ℝ → Fin 2 → ℂ}
    {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hu2 : ∀ i, MemLp (fun x => u x i) 2 (volume.restrict (B0579.cell c)))
    (hdiv : ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) = 0)
    (hgrad : ∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => u x i) (fun x => G x i j)) :
    IsBiotSavart c (fun x => G x 1 0 - G x 0 1) u := by
  refine ⟨hu2, hdiv, fun ψ hψ => ?_⟩
  obtain ⟨hint01, heq01⟩ := hgrad 0 1
  obtain ⟨hint10, heq10⟩ := hgrad 1 0
  have hA : IntegrableOn (fun x => u x 0 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
    (hint01 ψ hψ).1
  have hB : IntegrableOn (fun x => u x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
    (hint10 ψ hψ).1
  have hC : IntegrableOn (fun x => G x 0 1 * (ψ x : ℂ)) (B0579.cell c) := (hint01 ψ hψ).2
  have hD : IntegrableOn (fun x => G x 1 0 * (ψ x : ℂ)) (B0579.cell c) := (hint10 ψ hψ).2
  have e1 : ∫ x in B0579.cell c, u x 0 * (B0579.pd 1 ψ x : ℂ) =
      -∫ x in B0579.cell c, G x 0 1 * (ψ x : ℂ) := heq01 ψ hψ
  have e2 : ∫ x in B0579.cell c, u x 1 * (B0579.pd 0 ψ x : ℂ) =
      -∫ x in B0579.cell c, G x 1 0 * (ψ x : ℂ) := heq10 ψ hψ
  have e3 : ∫ x in B0579.cell c, (G x 1 0 - G x 0 1) * (ψ x : ℂ) =
      (∫ x in B0579.cell c, G x 1 0 * (ψ x : ℂ)) - ∫ x in B0579.cell c, G x 0 1 * (ψ x : ℂ) := by
    rw [← integral_sub hD hC]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have e4 : ∫ x in B0579.cell c, (u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ)) =
      (∫ x in B0579.cell c, u x 0 * (B0579.pd 1 ψ x : ℂ)) -
        ∫ x in B0579.cell c, u x 1 * (B0579.pd 0 ψ x : ℂ) :=
    integral_sub hA hB
  rw [e3, e4, e1, e2]
  ring

/-- **Leaf `PartIII-a:T19/2/3/1` (`CoreBiotSavartSliceBound`, SP 3497-3515).** -/
theorem coreBiotSavartSliceBound : CoreBiotSavartSliceBound := by
  intro C_BS _hC_BS hBS c hc1 u G _hu _hG hu2 _hG2 hdiv hgrad hω2 hωcirc
  obtain ⟨u', G', _hu', _hG', hBS', hgrad', hbu, hbG⟩ := hBS c hc1 _ hω2 hωcirc
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hBSu : IsBiotSavart c (fun x => G x 1 0 - G x 0 1) u :=
    isBiotSavart_of_weakGrad hu2 hdiv hgrad
  have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), u x = u' x :=
    CTE.isBiotSavart_unique c hc0 _ u u' hBSu hBS'
  have hGae : ∀ i j : Fin 2,
      (fun x => G x i j) =ᵐ[volume.restrict (B0579.cell c)] (fun x => G' x i j) := by
    intro i j
    refine weakCellAeUnique c j (fun x => u x i) _ _ (hgrad i j) ?_
    refine HasWeakCellDerivC.congr_ae ?_ (Eventually.of_forall fun _ => rfl) (hgrad' i j)
    filter_upwards [hae] with x hx
    rw [hx]
  have hGae' : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), G x = G' x := by
    have h : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i j : Fin 2, G x i j = G' x i j :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => hGae i j
    filter_upwards [h] with x hx
    funext i j
    exact hx i j
  refine ⟨?_, ?_⟩
  · calc (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2))
        = ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u' x) ^ 2) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [hx]
      _ ≤ _ := hbu
  · calc (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2))
        = ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G' x) ^ 2) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hGae'] with x hx
          rw [hx]
      _ ≤ _ := hbG

end UnforcedLeray.Short.IIIa
