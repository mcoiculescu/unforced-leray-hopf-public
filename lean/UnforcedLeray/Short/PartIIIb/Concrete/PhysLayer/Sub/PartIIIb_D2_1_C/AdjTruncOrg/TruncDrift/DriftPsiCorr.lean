import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.DriftPsi.Identity
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.LapPsi

/-!
# `DriftPsiCorr`: corrected weak drift of the stream potential

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
Proof: the pointwise identity `driftT Θ = (μ + ½) Θ - ν lapT Θ - wOpT ν μ Θ`
(`driftT_eq_wOpT_pointwise`) splits the pairing with `ψ` into three pieces. The `lapT` piece is
`LapPsi` (`lapPsi`), the `wOpT` piece is the intertwining `inter` of `TruncHyp`, and the constant
piece is the scalar `(μ + ½)`. The right-hand side is split in the second slot. Linearity uses
integrability of each `dotL (Θ z) (·)` against a phase test: `ψ`, `w` are locally `L²` by Hardy, and
`curlD D` is a finite sum of `Y_2` fields against constants. Helpers are local (prefix `dpc_`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ### Linearity of `pairF` in the second slot -/

theorem dpc_pairF_add_right {P : ℝ} {X Y Z : ℝ × Space → CVec3}
    (hY : Integrable (fun z => dotL (X z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (X z) (Z z)) (muP P)) :
    pairF P X (fun x => Y x + Z x) = pairF P X Y + pairF P X Z := by
  have hint : Integrable (fun z => dotL (X z) (Y z + Z z)) (muP P) :=
    (hY.add hZ).congr (ae_of_all _ fun z => by simp [map_add])
  rw [pair_eq_integral P X _ hint, pair_eq_integral P X Y hY, pair_eq_integral P X Z hZ]
  simp only [map_add]
  rw [integral_add hY hZ, smul_add]

theorem dpc_pairF_sub_right {P : ℝ} {X Y Z : ℝ × Space → CVec3}
    (hY : Integrable (fun z => dotL (X z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (X z) (Z z)) (muP P)) :
    pairF P X (fun x => Y x - Z x) = pairF P X Y - pairF P X Z := by
  have hint : Integrable (fun z => dotL (X z) (Y z - Z z)) (muP P) :=
    (hY.sub hZ).congr (ae_of_all _ fun z => by simp [map_sub])
  rw [pair_eq_integral P X _ hint, pair_eq_integral P X Y hY, pair_eq_integral P X Z hZ]
  simp only [map_sub]
  rw [integral_sub hY hZ, smul_sub]

/-! ### The corrected drift pairing -/

/-- **Corrected weak drift of the stream potential** (source 1351-1362, 1470-1480):
`⟪driftT Θ, ψ⟫ = ⟪Θ, (μ + ½)ψ - w + ν curl Φ⟫` for every phase test `Θ`. -/
theorem driftPsiCorr : DriftPsiCorr := by
  intro P ν μ hP hP1 hν hμ D hD Θ hΘ
  -- locally `L²` data
  have hψ : LocL2 P D.ψ := Or.inr hD.spΦ.hardy
  have hw : LocL2 P D.w := Or.inr hD.spg.hardy
  have hDk : ∀ k : Fin 3, LocL2 P (D.DΦ k) := fun k => Or.inl (hD.dΦ k).1
  -- the pointwise identity, and the phase-test property of its pieces
  have hdrift : driftT Θ = fun x => ((μ + 1 / 2 : ℝ) • Θ x - ν • lapT Θ x) - wOpT ν μ Θ x := by
    funext x
    exact driftT_eq_wOpT_pointwise ν μ Θ x
  have hE : IsPhaseTest P (fun x => (μ + 1 / 2 : ℝ) • Θ x - ν • lapT Θ x) :=
    (hΘ.const_smul (μ + 1 / 2 : ℝ)).sub (hΘ.lapT.const_smul ν)
  have hE1 : IsPhaseTest P (fun x => (μ + 1 / 2 : ℝ) • Θ x) := hΘ.const_smul (μ + 1 / 2 : ℝ)
  have hE2 : IsPhaseTest P (fun x => ν • lapT Θ x) := hΘ.lapT.const_smul ν
  have hWeq : wOpT ν μ Θ = fun x => ((μ + 1 / 2 : ℝ) • Θ x - ν • lapT Θ x) - driftT Θ x := by
    funext x
    have h := driftT_eq_wOpT_pointwise ν μ Θ x
    rw [h]
    abel
  have hWOp : IsPhaseTest P (wOpT ν μ Θ) := by
    rw [hWeq]
    exact hE.sub hΘ.driftT
  -- the three named identities
  have hI : pairF P (wOpT ν μ Θ) D.ψ = pairF P Θ D.w := hD.inter Θ hΘ
  have hL : pairF P (lapT Θ) D.ψ = -pairF P Θ (curlD D) := lapPsi P ν μ hP hP1 hν hμ D hD Θ hΘ
  -- integrability of the pieces against the phase test `Θ`
  have iA : Integrable (fun z => dotL (Θ z) ((μ + 1 / 2 : ℝ) • D.ψ z)) (muP P) := by
    refine ((wlp_integrable hP hΘ hψ).const_mul ((μ + 1 / 2 : ℝ) : ℂ)).congr
      (ae_of_all _ fun z => ?_)
    simp only [wlp_dotL_smul_right, smul_eq_mul]
  have iW : Integrable (fun z => dotL (Θ z) (D.w z)) (muP P) := wlp_integrable hP hΘ hw
  have hcurl : Integrable (fun z => dotL (Θ z) (curlD D z)) (muP P) := by
    have hs : Integrable (fun z => ∑ k : Fin 3,
        dotL (Θ z) (crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k z))) (muP P) :=
      integrable_finsetSum _ (fun k _ => wlp_integrable_cross hP hΘ (hDk k) (EuclideanSpace.single k (1 : ℂ)))
    refine hs.congr (ae_of_all _ fun z => ?_)
    simp only [curlD, map_sum]
  have iC : Integrable (fun z => dotL (Θ z) ((ν : ℝ) • curlD D z)) (muP P) := by
    refine (hcurl.const_mul (ν : ℂ)).congr (ae_of_all _ fun z => ?_)
    simp only [wlp_dotL_smul_right, smul_eq_mul]
  have iAW : Integrable (fun z => dotL (Θ z) ((μ + 1 / 2 : ℝ) • D.ψ z - D.w z)) (muP P) := by
    refine (iA.sub iW).congr (ae_of_all _ fun z => ?_)
    simp [map_sub]
  -- decomposition of the right-hand side in the second slot
  have hR : pairF P Θ (fun x => (μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x) =
      pairF P Θ (fun x => (μ + 1 / 2 : ℝ) • D.ψ x - D.w x) + pairF P Θ (fun x => ν • curlD D x) :=
    dpc_pairF_add_right iAW iC
  have hRsub : pairF P Θ (fun x => (μ + 1 / 2 : ℝ) • D.ψ x - D.w x) =
      pairF P Θ (fun x => (μ + 1 / 2 : ℝ) • D.ψ x) - pairF P Θ D.w :=
    dpc_pairF_sub_right iA iW
  have hRsmul : pairF P Θ (fun x => (μ + 1 / 2 : ℝ) • D.ψ x) =
      ((μ + 1 / 2 : ℝ) : ℂ) * pairF P Θ D.ψ :=
    wlp_pairF_const_smul_right P (μ + 1 / 2 : ℝ) Θ D.ψ
  have hRnu : pairF P Θ (fun x => ν • curlD D x) = (ν : ℂ) * pairF P Θ (curlD D) :=
    wlp_pairF_const_smul_right P ν Θ (curlD D)
  -- left-hand side
  rw [hdrift, wlp_pairF_sub hP hE hWOp hψ, hI, wlp_pairF_sub hP hE1 hE2 hψ,
    wlp_pairF_const_smul P (μ + 1 / 2 : ℝ) Θ D.ψ, wlp_pairF_const_smul P ν (lapT Θ) D.ψ, hL]
  rw [hR, hRsub, hRsmul, hRnu]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
