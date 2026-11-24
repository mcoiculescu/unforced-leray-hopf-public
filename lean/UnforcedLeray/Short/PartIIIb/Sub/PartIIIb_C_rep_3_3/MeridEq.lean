import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Source

/-!
# `PartIII-b:C/rep/3/3/3`: meridional trace invariance of the separated jets and primitives

Proves `sepJetMeridEq : SepJetMeridEq`: by horizontal rotation equivariance of `sepX0` and `sepWre`
off the source disk (`wgx_sepX0_equivariant`, `wgyw_equivariant`) and the linear isometry
invariance of `‖iteratedFDeriv ℝ j · ·‖`, the jet norms `wgxJet j`, `wgyWJet j` and the outward
primitive densities `wgxPsi`, `wgyWPsi` at `!₂[ϱ y, 0, y 2] = meridPt y` equal those at `y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private lemma norm_iteratedFDeriv_meridPt_eq {U : Set Space} (hU : IsOpen U)
    {y : Space} (hy : 0 < ϱ y) (hm : meridPt y ∈ U)
    {f : Space → Space}
    (hf : ∀ z ∈ U,
      f (actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) z) =
        actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) (f z))
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j f (meridPt y)‖ₑ = ‖iteratedFDeriv ℝ j f y‖ₑ := by
  obtain ⟨hco, hmer⟩ := wgx_rot_meridPt hy
  let g : Space ≃ₗᵢ[ℝ] Space := lieOf (rotM_orth hco)
  have hg_apply : ∀ z : Space, g z = actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) z := fun _ => rfl
  have hev : f ∘ g =ᶠ[nhds (meridPt y)] g ∘ f := by
    filter_upwards [hU.mem_nhds hm] with z hz
    simp only [Function.comp_apply, hg_apply]
    exact hf z hz
  have h1 : iteratedFDeriv ℝ j (f ∘ g) (meridPt y) = iteratedFDeriv ℝ j (g ∘ f) (meridPt y) :=
    (hev.iteratedFDeriv ℝ j).eq_of_nhds
  have h2 : ‖iteratedFDeriv ℝ j f (meridPt y)‖ = ‖iteratedFDeriv ℝ j f y‖ := by
    calc ‖iteratedFDeriv ℝ j f (meridPt y)‖
        = ‖iteratedFDeriv ℝ j (g ∘ f) (meridPt y)‖ :=
          (g.norm_iteratedFDeriv_comp_left f (meridPt y) j).symm
      _ = ‖iteratedFDeriv ℝ j (f ∘ g) (meridPt y)‖ := by rw [h1]
      _ = ‖iteratedFDeriv ℝ j f (g (meridPt y))‖ :=
          g.norm_iteratedFDeriv_comp_right f (meridPt y) j
      _ = ‖iteratedFDeriv ℝ j f y‖ := by rw [hg_apply, hmer]
  simp only [← ofReal_norm, h2]

/-- **Leaf 3 of `PartIII-b:C/rep/3/3`.** Meridional trace invariance of `wgxJet`, `wgyWJet`,
`wgxPsi`, and `wgyWPsi`. -/
theorem sepJetMeridEq : SepJetMeridEq := by
  intro ν μ R P hν hR hP hμ T hS hM hAx τ y hy
  set rOut : ℝ := R * Real.sqrt (5 * ν / 6) with hrOut
  set rIn : ℝ := R * Real.sqrt ν with hrIn
  have hr0 : 0 ≤ rOut := by rw [hrOut]; positivity
  have hrOut_lt_rIn : rOut < rIn := by
    rw [hrOut, hrIn]
    exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  let U : Set Space := {z : Space | rOut < ϱ z}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  obtain ⟨hco, _⟩ := wgx_rot_meridPt hy
  have hT_rot : ∀ τ' z,
      T τ' (actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) z) =
        rotM (y 0 / ϱ y) (y 1 / ϱ y) * T τ' z * (rotM (y 0 / ϱ y) (y 1 / ϱ y)).transpose :=
    hAx.1 _ _ hco
  have hρm : ϱ !₂[ϱ y, 0, y 2] = ϱ y := varrho_meridPt y
  have hm_eq : (!₂[ϱ y, 0, y 2] : Space) = meridPt y := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    unfold wgxJet
    rw [hρm]
    split_ifs with hle
    · have hmU : meridPt y ∈ U := by
        show rOut < ϱ (meridPt y)
        rw [varrho_meridPt]
        exact lt_of_lt_of_le hrOut_lt_rIn hle
      rw [hm_eq]
      refine norm_iteratedFDeriv_meridPt_eq hU hy hmU (fun z hz => ?_) j
      have hI1 := sepIntegrableOfSource_all ν (μ : ℂ) rOut P T hν (by simpa using hμ) hr0 hP hS hM
        τ z hz
      have hI2 := sepIntegrableOfSource_all ν ((μ : ℂ) + 1) rOut P T hν (by simp; linarith) hr0 hP
        hS hM τ z hz
      exact wgx_sepX0_equivariant _ (rotM_orth hco) ν μ T hT_rot z τ hI1 hI2
    · rfl
  · intro j
    unfold wgyWJet
    rw [hρm]
    split_ifs with hle
    · have hmU : meridPt y ∈ U := by
        show rOut < ϱ (meridPt y)
        rw [varrho_meridPt]
        exact lt_of_lt_of_le hrOut_lt_rIn hle
      rw [hm_eq]
      refine norm_iteratedFDeriv_meridPt_eq hU hy hmU (fun z hz => ?_) j
      have hI1 := sepIntegrableOfSource_all ν (μ : ℂ) rOut P T hν (by simpa using hμ) hr0 hP hS hM
        τ z hz
      exact wgyw_equivariant _ (rotM_orth hco) ν μ T hT_rot z τ hI1
    · rfl
  · unfold wgxPsi streamAnn
    simp [Set.indicator_apply, hρm]
  · unfold wgyWPsi streamAnn
    simp [Set.indicator_apply, hρm]

end UnforcedLeray.Short.PartIIIb.Concrete

end
