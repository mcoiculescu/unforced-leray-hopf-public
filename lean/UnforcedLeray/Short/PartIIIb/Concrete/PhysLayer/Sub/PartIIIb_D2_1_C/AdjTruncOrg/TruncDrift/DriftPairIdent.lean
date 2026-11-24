import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.CutBounds
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.PhiDriftPair
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.CrossDriftPair

/-!
# `DriftPairIdent`: the pairing identity `⟪driftT Θ, Φₙ⟫ = ⟪Θ, driftB⟫` (source 1351-1362, 1470-1480)

Target: `driftPairIdent : DriftPairIdent`.

Mathematics. `truncPhi n D = χₙ Φ + ∇χₙ × ψ`, so the left pairing splits into the `χₙ Φ` part and the
`∇χₙ × ψ` part, which are `phiDriftPair` and `crossDriftPair`. The right side `driftB` is
`A + crossB` with `A = χₙ bΦ - ½ (y·∇χₙ) Φ`, and `phiDriftPair` has right side `A`, `crossDriftPair`
has right side `crossB`. Splitting is legitimate by integrability on the phase measure:
`truncPhi ∈ Y_2` (`truncMemY`), `crossB ∈ Y_2` (Hardy bounds, inline), `driftT Θ` and `Θ` are `Y_2`
(`isInYr_of_phaseTest`), and `A ∈ Y_2` (bounded cutoff times `bΦ`, and `½ radS χₙ` bounded times `Φ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- **Pairing identity**: `⟪driftT Θ, Φₙ⟫ = ⟪Θ, driftB⟫` for phase tests (source 1351-1362, 1470-1480). -/
theorem driftPairIdent : DriftPairIdent := by
  intro P ν μ hP hP1 hν hμ D hD n bΦ hbΦ hbd Θ hΘ
  have hCut : CutBounds := cutBounds
  -- the two pairing identities
  have hPhi := phiDriftPair P ν μ hP hP1 hν hμ D hD n bΦ hbΦ hbd Θ hΘ
  have hCr := crossDriftPair P ν μ hP hP1 hν hμ D hD n Θ hΘ
  -- phase-test and Y_2 inputs
  have hDΘ : IsPhaseTest P (driftT Θ) := hΘ.driftT
  have hDΘY : UnforcedLeray.Short.IIb.IsInYr P 2 (driftT Θ) := isInYr_of_phaseTest hP hDΘ
  have hΦY : UnforcedLeray.Short.IIb.IsInYr P 2 D.Φ := hD.dom.mem
  obtain ⟨Cc, hCc⟩ := pdp_cut_bound n
  obtain ⟨L, hL⟩ := goodMult_radS_cutχ.bound
  have hcc : Continuous (cutχ n) := (contDiff_cutχ n).continuous
  have hrc : Continuous (fun y : Space => (1 / 2 : ℝ) * radS (cutχ n) y) :=
    goodMult_radS_cutχ.cont n
  have hcont_rad : Continuous (radS (cutχ n)) := (contDiff_radS' (contDiff_cutχ n)).continuous
  -- the `χₙ Φ` part lies in Y_2
  have hUY : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => cutχ n x.2 • D.Φ x) :=
    isInYr_smul_of_bdd hP (a := fun x : ℝ × Space => cutχ n x.2) (M := Cc)
      (hcc.comp continuous_snd).aestronglyMeasurable (fun x => hCc x.2)
      (ae_of_all _ fun x => rfl) hΦY
  -- `truncPhi ∈ Y_2`
  have hTP : UnforcedLeray.Short.IIb.IsInYr P 2 (truncPhi n D) :=
    (truncMemY hCut P ν μ hP hP1 hν hμ D hD n).1
  -- `A = χₙ bΦ - ½ radS χₙ Φ` lies in Y_2
  have hu : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => cutχ n x.2 • bΦ x) :=
    isInYr_smul_of_bdd hP (a := fun x : ℝ × Space => cutχ n x.2) (M := Cc)
      (hcc.comp continuous_snd).aestronglyMeasurable (fun x => hCc x.2)
      (ae_of_all _ fun x => rfl) hbΦ
  have hv : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (-(1 / 2 : ℝ) * radS (cutχ n) x.2) • D.Φ x) :=
    isInYr_smul_of_bdd hP (a := fun x : ℝ × Space => (-(1 / 2 : ℝ) * radS (cutχ n) x.2)) (M := L)
      (continuous_const.mul (hcont_rad.comp continuous_snd)).aestronglyMeasurable
      (fun x => by
        show |(-(1 / 2 : ℝ) * radS (cutχ n) x.2)| ≤ L
        rw [neg_mul, abs_neg]
        exact hL n x.2)
      (ae_of_all _ fun x => rfl) hΦY
  have hAY : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => cutχ n x.2 • bΦ x - ((1 / 2 : ℝ) * radS (cutχ n) x.2) • D.Φ x) :=
    isInYr_add2 hP (fun x => by simp only [neg_mul, neg_smul, sub_eq_add_neg]) hu hv
  have hAint := wlp_integrable hP hΘ (Or.inl hAY)
  -- `crossB ∈ Y_2` (Hardy bounds on `∇χₙ`, `∇(radS χₙ) - ∇χₙ`; as in `CrossDriftPair`)
  have hcS : ContDiff ℝ ∞ (cutχ n) := contDiff_cutχ n
  have hradC : ContDiff ℝ ∞ (radS (cutχ n)) := contDiff_radS' hcS
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
    continuous_gradC' fun j => (contDiff_sd hcS j).continuous
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
  have hYw : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.w x)) :=
    isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC hD.spg.periodic hD.spg.meas hwH
  have hYψ : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.ψ x)) :=
    isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC hD.spΦ.periodic hD.spΦ.meas hψH
  have hYcurl : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (curlD D x)) :=
    isInYr_cross_bdd hP (A := fun y : Space => gradC (cutχ n) y) (M := C) hC0 hGbdd hcont_gC hcurl
  have hYrg : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x)) :=
    isInYr_cross_hardy hP (A := fun y : Space => gradC (radS (cutχ n)) y - gradC (cutχ n) y)
      (M := 4 * C) (by linarith) hG6 hcont_G6 hD.spΦ.periodic hD.spΦ.meas hψH
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
  have hYcross : UnforcedLeray.Short.IIb.IsInYr P 2 (crossB n ν μ D) := by
    have e : crossB n ν μ D = fun x => crossC (gradC (cutχ n) x.2)
        ((μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)
        + (-(1 / 2 : ℝ)) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x) := by
      funext x
      ext i
      fin_cases i <;> simp [crossB, crossC, Complex.real_smul] <;> ring
    rw [e]
    exact isInYr_add2 hP (fun x => rfl) hYV
      (isInYr_smul_of_bdd hP (a := fun _ : ℝ × Space => (-(1 / 2 : ℝ))) (M := 1)
        aestronglyMeasurable_const (fun _ => by norm_num) (Filter.Eventually.of_forall fun x => rfl)
        hYrg)
  have hCi : Integrable (fun z => dotL (Θ z) (crossB n ν μ D z)) (muP P) :=
    wlp_integrable hP hΘ (Or.inl hYcross)
  -- integrability of the pieces of `Φₙ` against `driftT Θ`
  have hUi : Integrable (fun z => dotL (driftT Θ z) (cutχ n z.2 • D.Φ z)) (muP P) :=
    dot_integrable hP hDΘY hUY
  have hVi : Integrable
      (fun z => dotL (driftT Θ z) (crossC (gradC (cutχ n) z.2) (D.ψ z))) (muP P) := by
    refine (((dot_integrable hP hDΘY hTP).sub hUi).congr (ae_of_all _ fun z => ?_))
    simp only [Pi.sub_apply, truncPhi, map_add]
    ring
  -- split the left pairing
  have hLHS : pairF P (driftT Θ) (truncPhi n D)
      = pairF P (driftT Θ) (fun x => cutχ n x.2 • D.Φ x)
        + pairF P (driftT Θ) (fun x => crossC (gradC (cutχ n) x.2) (D.ψ x)) :=
    wlm_pairF_add_right hUi hVi
  -- split the right pairing
  have hRHS : pairF P Θ (driftB n ν μ D bΦ)
      = pairF P Θ (fun x => cutχ n x.2 • bΦ x - ((1 / 2 : ℝ) * radS (cutχ n) x.2) • D.Φ x)
        + pairF P Θ (crossB n ν μ D) :=
    wlm_pairF_add_right hAint hCi
  rw [hLHS, hPhi, hCr, hRHS]

end UnforcedLeray.Short.PartIIIb.Concrete
