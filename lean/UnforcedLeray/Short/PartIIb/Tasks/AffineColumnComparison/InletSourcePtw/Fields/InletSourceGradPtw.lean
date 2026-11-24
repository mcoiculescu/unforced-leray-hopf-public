import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.AbsPhaseIBP
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# Part II-b, task `PartII-b:G4/4/1/1/6` (`InletSourceGradPtw`)

Source of record: `the November 2 reference manuscript`, lines 2355-2383.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Axi

private theorem isgp_space_sum_single (v : Space) :
    v = ∑ k : Fin 3, v k • EuclideanSpace.single k (1 : ℝ) := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three]

theorem isgp_advT_Efun_Ufun {p : Params}
    (hRaw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)) (i : Fin 2) (x : ℝ × Space) :
    advT (p.Efun i) p.Ufun x =
      realC (fderiv ℝ (p.raw x.1) x.2 (p.inlet i x.1 x.2)) := by
  have hv : fderiv ℝ (p.raw x.1) x.2 (p.inlet i x.1 x.2) =
      ∑ k : Fin 3, (p.inlet i x.1 x.2 k) •
        fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) := by
    conv_lhs => rw [isgp_space_sum_single (p.inlet i x.1 x.2)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
  ext m
  unfold Params.Ufun
  simp only [advT, Params.Efun, dy_realC_comp hRaw, hv, realC_apply,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul]

theorem contDiff_advT {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (advT A B) := by
  unfold advT
  exact ContDiff.sum fun k _ =>
    (srwf_coord_contDiff hA k).smul (UnforcedLeray.PhaseSpace.contDiff_dy hB k)

set_option maxHeartbeats 400000 in
theorem contDiff_inletSourceF {p : Params} {i : Fin 2}
    (hInl : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2))
    (hRaw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)) :
    ContDiff ℝ ∞ (inletSourceF p i) := by
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_field hInl
  have hU : ContDiff ℝ ∞ p.Ufun := contDiff_realC_field hRaw
  have h1 : ContDiff ℝ ∞ (dτ (p.Efun i)) := UnforcedLeray.PhaseSpace.contDiff_dτ hE
  have h2 : ContDiff ℝ ∞ (fun x => (1 / 2 : ℝ) • radialT (p.Efun i) x) :=
    (UnforcedLeray.PhaseSpace.contDiff_radialT hE).const_smul (1 / 2 : ℝ)
  have h3 : ContDiff ℝ ∞ (fun x => p.ν • lapT (p.Efun i) x) :=
    (UnforcedLeray.PhaseSpace.contDiff_lapT hE).const_smul p.ν
  have h4 : ContDiff ℝ ∞ (fun x => (1 / 2 : ℝ) • p.Efun i x) :=
    hE.const_smul (1 / 2 : ℝ)
  have h5 : ContDiff ℝ ∞ (advT p.Ufun (p.Efun i)) := contDiff_advT hU hE
  have h6 : ContDiff ℝ ∞ (advT (p.Efun i) p.Ufun) := contDiff_advT hE hU
  have heq : inletSourceF p i = fun x =>
      dτ (p.Efun i) x - (1 / 2 : ℝ) • radialT (p.Efun i) x - p.ν • lapT (p.Efun i) x
        - (1 / 2 : ℝ) • p.Efun i x
        + advT p.Ufun (p.Efun i) x
        + advT (p.Efun i) p.Ufun x := by
    funext x
    simp only [inletSourceF, isgp_advT_Efun_Ufun hRaw i x]
  rw [heq]
  exact ((((h1.sub h2).sub h3).sub h4).add h5).add h6

theorem hasPtwOp_neg_dy_of_contDiff {P : ℝ} {F : ℝ × Space → CVec3} (hF : ContDiff ℝ ∞ F)
    (j : Fin 3) : HasPtwOp P (fun Φ x => -(dy j Φ x)) F (dy j F) := by
  intro Φ hΦ
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦ.smooth
  have hF_dy : ContDiff ℝ ∞ (dy j F) := UnforcedLeray.PhaseSpace.contDiff_dy hF j
  have hΦ_dy : ContDiff ℝ ∞ (dy j Φ) := UnforcedLeray.PhaseSpace.contDiff_dy hΦc j
  have hD : ContDiff ℝ ∞ (dotFn Φ F) := srwf_dotFn_contDiff hΦc hF
  obtain ⟨hK_int, hK_zero⟩ :=
    srwf_slab_dy (P := P) (R := R) hD (fun τ y hy => by simp [dotFn, hR τ y hy]) j
  have h1_int : Integrable (fun z => dotL (-(dy j Φ z)) (F z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hΦ_dy.neg.continuous).clm_apply hF.continuous) (R := R)
      (fun t y hy => by simp [srwf_dy_bdd hR j t y hy])
  have h2_int : Integrable (fun z => dotL (Φ z) (dy j F z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hΦc.continuous).clm_apply hF_dy.continuous) (R := R)
      (fun t y hy => by simp [hR t y hy])
  have hpt : (fun z => dotL (-(dy j Φ z)) (F z)) =
      fun z => dotL (Φ z) (dy j F z) - dy j (dotFn Φ F) z := by
    funext z
    have hleib := dy_dotFn (hΦc.differentiable (by simp)) (hF.differentiable (by simp)) j z
    simp only [map_neg, neg_apply, hleib]
    ring
  unfold pairF
  rw [srwf_phaseInt_eq h1_int, srwf_phaseInt_eq h2_int, hpt,
    integral_sub h2_int hK_int, hK_zero, sub_zero]

/-- **The spatial derivative is the weak gradient** of the inlet source (SP 2355-2383). -/
theorem inletSourceGradPtw_of (hRaw : UnforcedLeray.Short.IIb.RawJointSmooth) :
    UnforcedLeray.Short.IIb.InletSourceGradPtw := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, h1, H1⟩ := inletJointSmooth Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, h2, H2⟩ := hRaw Sig lam q hSig hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min h1 h2, ?_⟩
  intro p d hreg hν hSig' hmode i j
  have e1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hInl : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    H1 p d hreg e1 hSig' hmode i
  have hRaw' : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) :=
    H2 p d hreg e2 hSig' hmode i
  exact hasPtwOp_neg_dy_of_contDiff (contDiff_inletSourceF hInl hRaw') j

end UnforcedLeray.Short.IIb
