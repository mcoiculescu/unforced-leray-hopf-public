import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.CutBounds
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.CrossDriftCalc
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.CrossPhaseTest
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.DriftPsi

/-!
# `CrossDriftPair`: the `∇χₙ × ψ` part of the drift pairing (source 1351-1362, 1470-1480)

Target: `crossDriftPair : CrossDriftPair`, i.e. for a phase test `Θ`,
`⟪driftT Θ, ∇χₙ × ψ⟫ = ⟪Θ, crossB n ν μ D⟫`.

Mathematics. Write `g = ∇χₙ`, `rg = ∇(radS χₙ) - ∇χₙ`, `Θ₂ = g × Θ`, `V = (μ+½)ψ - w + ν curlΦ`.
* `a·(g×b) = -b·(g×a)` (`wlp_dotL_cross'`), so `⟪driftTΘ, g×ψ⟫ = -⟪g×driftTΘ, ψ⟫`.
* `g × driftTΘ = driftT Θ₂ - ½ rg×Θ` (`crossDriftCalc`).
* `⟪driftT Θ₂, ψ⟫ = ⟪Θ₂, V⟫ = -⟪Θ, g×V⟫` (`driftPsi`, triple product).
* `⟪rg×Θ, ψ⟫ = -⟪Θ, rg×ψ⟫`.
Altogether `⟪driftTΘ, g×ψ⟫ = ⟪Θ, g×V - ½ rg×ψ⟫ = ⟪Θ, crossB⟫`.

Integrability: `g×ψ`, `g×w`, `rg×ψ` are `Y_2` by the Hardy bounds `|g|, |rg| ≲ 1/|y|`
(`isInYr_cross_hardy`); `g×curlΦ` is `Y_2` by boundedness of `g` (`isInYr_cross_bdd`).
The bounds come from `cutBounds`, as in `DriftBMem.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ### Pairing helpers -/

/-- Pairings agree when the integrands agree pointwise. -/
theorem cdp_pairF_congr {P : ℝ} {X Y u v : ℝ × Space → CVec3}
    (h : ∀ z, dotL (X z) (u z) = dotL (Y z) (v z)) : pairF P X u = pairF P Y v := by
  simp only [pairF, phaseInt, h]

/-- Negation in the second slot of a pairing. -/
theorem cdp_pairF_neg_right {P : ℝ} (X Y : ℝ × Space → CVec3) :
    pairF P X (fun x => -Y x) = -pairF P X Y := by
  simp [pairF, phaseInt, integral_neg, smul_neg]

/-- Splitting the second slot of a pairing, given integrability of both summands. -/
theorem cdp_pairF_sub_right {P : ℝ} {X Y Z : ℝ × Space → CVec3}
    (hY : Integrable (fun z => dotL (X z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (X z) (Z z)) (muP P)) :
    pairF P X (fun x => Y x - Z x) = pairF P X Y - pairF P X Z := by
  have hint : Integrable (fun z => dotL (X z) (Y z - Z z)) (muP P) :=
    (hY.sub hZ).congr (ae_of_all _ fun z => by simp [map_sub])
  rw [pair_eq_integral P X _ hint, pair_eq_integral P X Y hY, pair_eq_integral P X Z hZ]
  simp only [map_sub]
  rw [integral_sub hY hZ, smul_sub]

/-! ### The cross-product part of the drift pairing -/

/-- **Cross-product drift pairing**: `⟪driftT Θ, ∇χₙ × ψ⟫ = ⟪Θ, crossB⟫` (source 1351-1362, 1470-1480). -/
theorem crossDriftPair : CrossDriftPair := by
  intro P ν μ hP hP1 hν hμ D hD n Θ hΘ
  have hc : ContDiff ℝ ∞ (cutχ n) := contDiff_cutχ n
  have hradC : ContDiff ℝ ∞ (radS (cutχ n)) := contDiff_radS' hc
  have hψ : LocL2 P D.ψ := Or.inr hD.spΦ.hardy
  -- phase tests
  have hΘ2 : IsPhaseTest P (fun q => crossC (gradC (cutχ n) q.2) (Θ q)) :=
    (crossPhaseTest P (cutχ n) hc Θ hΘ).1
  have hΘR : IsPhaseTest P (fun q => crossC (gradC (radS (cutχ n)) q.2) (Θ q)) :=
    (crossPhaseTest P (radS (cutχ n)) hradC Θ hΘ).1
  have hΘrg : IsPhaseTest P
      (fun q => crossC (gradC (radS (cutχ n)) q.2 - gradC (cutχ n) q.2) (Θ q)) := by
    have e : (fun q : ℝ × Space => crossC (gradC (radS (cutχ n)) q.2 - gradC (cutχ n) q.2) (Θ q))
        = fun q => crossC (gradC (radS (cutχ n)) q.2) (Θ q)
          - crossC (gradC (cutχ n) q.2) (Θ q) := by
      funext q
      exact cdc_crossC_sub _ _ _
    rw [e]
    exact hΘR.sub hΘ2
  have hD2 : IsPhaseTest P (driftT (fun q => crossC (gradC (cutχ n) q.2) (Θ q))) :=
    hΘ2.driftT
  -- product rule, pointwise
  have hdrift : ∀ x : ℝ × Space,
      crossC (gradC (cutχ n) x.2) (driftT Θ x)
        = driftT (fun q => crossC (gradC (cutχ n) q.2) (Θ q)) x
          - (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (Θ x) := by
    intro x
    rw [crossDriftCalc (cutχ n) hc Θ hΘ.smooth x]
    abel
  -- cut-off bounds
  have hCB : CutBounds := cutBounds
  unfold CutBounds at hCB
  obtain ⟨C, hC0, hb⟩ := hCB
  have hG1 : ∀ y : Space, ‖gradC (cutχ n) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).1) (hb n y).2.1
  have hG2 : ∀ y : Space, ‖gradC (radS (cutχ n)) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).2.1) (hb n y).2.2.1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hGbdd : ∀ y : Space, ‖gradC (cutχ n) y‖ ≤ C := fun y =>
    (hb n y).2.1.trans (div_le_self hC0 hn1)
  have hcont_gC : Continuous (gradC (cutχ n)) :=
    continuous_gradC' fun j => (contDiff_sd hc j).continuous
  have hcont_gR : Continuous (gradC (radS (cutχ n))) :=
    continuous_gradC' fun j => (contDiff_sd hradC j).continuous
  have hcont_G6 : Continuous (fun y : Space => gradC (radS (cutχ n)) y - gradC (cutχ n) y) :=
    hcont_gR.sub hcont_gC
  have hG6 : ∀ y : Space,
      ‖gradC (radS (cutχ n)) y - gradC (cutχ n) y‖ ≤ 4 * C * ‖y‖⁻¹ := fun y => by
    have h := norm_sub_le (gradC (radS (cutχ n)) y) (gradC (cutχ n) y)
    have h1 := hG2 y
    have h2 := hG1 y
    linarith
  -- Y_2 inputs
  have hψH := hD.spΦ.hardy
  have hwH := hD.spg.hardy
  have hDΦ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (D.DΦ k) := fun k => (hD.dΦ k).1
  have hcurl : UnforcedLeray.Short.IIb.IsInYr P 2 (curlD D) := by
    have hk : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2
        (fun x : ℝ × Space => crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x)) := fun k =>
      isInYr_cross_bdd hP (A := fun _ : Space => EuclideanSpace.single k (1 : ℂ)) (M := 1)
        (by norm_num) (fun y => by simp) continuous_const (hDΦ k)
    have e : curlD D = fun x => (crossC (EuclideanSpace.single 0 (1 : ℂ)) (D.DΦ 0 x)
        + crossC (EuclideanSpace.single 1 (1 : ℂ)) (D.DΦ 1 x))
        + crossC (EuclideanSpace.single 2 (1 : ℂ)) (D.DΦ 2 x) := by
      funext x
      simp only [curlD, Fin.sum_univ_three]
    rw [e]
    exact isInYr_add2 hP (fun x => rfl)
      (isInYr_add2 hP (fun x => rfl) (hk 0) (hk 1)) (hk 2)
  have hYψ : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.ψ x)) :=
    isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC hD.spΦ.periodic hD.spΦ.meas hψH
  have hYw : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.w x)) :=
    isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC hD.spg.periodic hD.spg.meas hwH
  have hYcurl : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (curlD D x)) :=
    isInYr_cross_bdd hP (A := fun y : Space => gradC (cutχ n) y) (M := C) hC0 hGbdd hcont_gC hcurl
  have hYrg : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x)) :=
    isInYr_cross_hardy hP (A := fun y : Space => gradC (radS (cutχ n)) y - gradC (cutχ n) y)
      (M := 4 * C) (by linarith) hG6 hcont_G6 hD.spΦ.periodic hD.spΦ.meas hψH
  -- the Y_2 membership of `g × V`, `V = (μ+½)ψ - w + ν curlΦ`
  have hp1 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (μ + 1 / 2 : ℝ) • crossC (gradC (cutχ n) x.2) (D.ψ x)) :=
    isInYr_smul_of_bdd hP (M := |μ + 1 / 2|) (a := fun _ : ℝ × Space => μ + 1 / 2)
      aestronglyMeasurable_const (fun _ => le_rfl) (Filter.Eventually.of_forall fun x => rfl) hYψ
  have hp2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (-1 : ℝ) • crossC (gradC (cutχ n) x.2) (D.w x)) :=
    isInYr_smul_of_bdd hP (M := 1) (a := fun _ : ℝ × Space => (-1 : ℝ))
      aestronglyMeasurable_const (fun _ => by norm_num) (Filter.Eventually.of_forall fun x => rfl) hYw
  have hp3 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => ν • crossC (gradC (cutχ n) x.2) (curlD D x)) :=
    isInYr_smul_of_bdd hP (M := |ν|) (a := fun _ : ℝ × Space => ν)
      aestronglyMeasurable_const (fun _ => le_rfl) (Filter.Eventually.of_forall fun x => rfl) hYcurl
  have hYV : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2)
        ((μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)) := by
    have e : (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2)
        ((μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x))
        = fun x => ((μ + 1 / 2 : ℝ) • crossC (gradC (cutχ n) x.2) (D.ψ x)
            + (-1 : ℝ) • crossC (gradC (cutχ n) x.2) (D.w x))
          + ν • crossC (gradC (cutχ n) x.2) (curlD D x) := by
      funext x
      ext i
      fin_cases i <;> simp [crossC, Complex.real_smul] <;> ring
    rw [e]
    exact isInYr_add2 hP (fun x => rfl) (isInYr_add2 hP (fun x => rfl) hp1 hp2) hp3
  -- integrability against the phase test `Θ`
  have hIX : Integrable (fun z => dotL (Θ z) (crossC (gradC (cutχ n) z.2)
      ((μ + 1 / 2 : ℝ) • D.ψ z - D.w z + ν • curlD D z))) (muP P) :=
    wlp_integrable hP hΘ (Or.inl hYV)
  have hIZ : Integrable (fun z => dotL (Θ z)
      ((1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) z.2 - gradC (cutχ n) z.2) (D.ψ z))) (muP P) := by
    refine ((wlp_integrable hP hΘ (Or.inl hYrg)).const_mul ((1 / 2 : ℝ) : ℂ)).congr
      (ae_of_all _ fun z => ?_)
    simp only [wlp_dotL_smul_right, smul_eq_mul]
  -- Step 1: move the cross product onto the first slot
  have h1 : pairF P (driftT Θ) (fun x => crossC (gradC (cutχ n) x.2) (D.ψ x))
      = pairF P (fun x => (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (Θ x)
          - driftT (fun q => crossC (gradC (cutχ n) q.2) (Θ q)) x) D.ψ := by
    apply cdp_pairF_congr
    intro z
    rw [wlp_dotL_cross' (gradC (cutχ n) z.2) (driftT Θ z) (D.ψ z), hdrift z]
    simp only [map_sub, sub_apply, wlp_dotL_smul_left, smul_eq_mul]
    ring
  -- Step 2: linearity in the first slot
  have h2 : pairF P (fun x => (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (Θ x)
          - driftT (fun q => crossC (gradC (cutχ n) q.2) (Θ q)) x) D.ψ
      = pairF P (fun x => (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (Θ x)) D.ψ
        - pairF P (driftT (fun q => crossC (gradC (cutχ n) q.2) (Θ q))) D.ψ :=
    wlp_pairF_sub hP (hΘrg.const_smul (1 / 2 : ℝ)) hD2 hψ
  have h3 : pairF P (fun x => (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (Θ x)) D.ψ
      = ((1 / 2 : ℝ) : ℂ) * pairF P (fun x => crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (Θ x)) D.ψ :=
    wlp_pairF_const_smul P (1 / 2 : ℝ) _ D.ψ
  -- Step 3: the triple product for `rg × Θ`
  have h4a : pairF P (fun x => crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (Θ x)) D.ψ
      = pairF P Θ (fun x => -crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x)) :=
    cdp_pairF_congr (fun z => by simp only [wlp_dotL_cross, map_neg])
  have h4 : pairF P (fun x => crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (Θ x)) D.ψ
      = -pairF P Θ (fun x => crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x)) := by
    rw [h4a, cdp_pairF_neg_right]
  -- Step 4: the stream-potential identity for `Θ₂ = g × Θ`
  have h5a : pairF P (driftT (fun q => crossC (gradC (cutχ n) q.2) (Θ q))) D.ψ
      = pairF P (fun q => crossC (gradC (cutχ n) q.2) (Θ q))
          (fun x => (μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x) :=
    driftPsi P ν μ hP hP1 hν hμ D hD _ hΘ2
  -- Step 5: triple product for `g × V`
  have h6a : pairF P (fun q => crossC (gradC (cutχ n) q.2) (Θ q))
      (fun x => (μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)
      = pairF P Θ (fun x => -crossC (gradC (cutχ n) x.2)
          ((μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)) :=
    cdp_pairF_congr (fun z => by simp only [wlp_dotL_cross, map_neg])
  have h6 : pairF P (fun q => crossC (gradC (cutχ n) q.2) (Θ q))
      (fun x => (μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)
      = -pairF P Θ (fun x => crossC (gradC (cutχ n) x.2)
          ((μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)) := by
    rw [h6a, cdp_pairF_neg_right]
  -- Step 6: identify `crossB` with `g × V - ½ rg × ψ`
  have hcb : crossB n ν μ D = fun x => crossC (gradC (cutχ n) x.2)
      ((μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)
      - (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x) := by
    funext x
    ext i
    fin_cases i <;> simp [crossB, crossC, Complex.real_smul] <;> ring
  -- Step 7: split the second slot
  have h8 : pairF P Θ (fun x => crossC (gradC (cutχ n) x.2)
        ((μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)
      - (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x))
      = pairF P Θ (fun x => crossC (gradC (cutχ n) x.2)
          ((μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x))
        - ((1 / 2 : ℝ) : ℂ) * pairF P Θ (fun x => crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x)) := by
    rw [cdp_pairF_sub_right hIX hIZ, wlp_pairF_const_smul_right]
  -- Assemble
  rw [h1, h2, h3, h4, h5a, h6, hcb, h8]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
