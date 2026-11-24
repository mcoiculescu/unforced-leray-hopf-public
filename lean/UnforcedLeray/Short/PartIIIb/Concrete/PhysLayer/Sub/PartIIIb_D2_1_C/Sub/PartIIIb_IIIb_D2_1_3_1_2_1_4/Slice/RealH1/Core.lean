import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_2_1
import UnforcedLeray.Loc.Hyp.ModeIdentification.Regularity
import UnforcedLeray.Loc.L10Nonlinear.Pairing

/-!
# Real elliptic `H¹` core (`RealH1Core`)

Source `the November 2 reference manuscript` lines 1351-1362.
Elliptic regularity `laplacianH1Regularity` gives `F ∈ H¹` with weak Laplacian `g`; its
derivatives `G j = ∂ⱼF` are the required `L²` fields, the vector-test identity is
`H1_inner_testPartial`, and the energy identity `⟨∇F,∇F⟩ = -⟨g,f⟩` with Cauchy-Schwarz gives the bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem rc_memLp_test {φ : Space → Space} (hφ : UnforcedLeray.Blueprint.IsVectorTest φ) :
    MemLp φ 2 volume :=
  hφ.smooth.continuous.memLp_of_hasCompactSupport hφ.compact

theorem rc_inner_L2_toL2 (H : UnforcedLeray.L2Space) {w : Space → Space}
    (hw : MemLp w 2 volume) :
    inner ℝ H (UnforcedLeray.toL2 w) = ∫ x, inner ℝ (H x) (w x) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [UnforcedLeray.coeFn_toL2 hw] with x hx
  rw [hx]

theorem rc_inner_toL2 (u w : Space → Space) (hu : MemLp u 2 volume) (hw : MemLp w 2 volume) :
    inner ℝ (UnforcedLeray.toL2 u) (UnforcedLeray.toL2 w) = ∫ x, inner ℝ (u x) (w x) := by
  rw [rc_inner_L2_toL2 _ hw]
  refine integral_congr_ae ?_
  filter_upwards [UnforcedLeray.coeFn_toL2 hu] with x hx
  rw [hx]

theorem rc_norm_sq (H : UnforcedLeray.L2Space) : ‖H‖ ^ 2 = ∫ y, ‖H y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x => real_inner_self_eq_norm_sq _)

theorem rc_integral_norm_sq (u : Space → Space) (hu : MemLp u 2 volume) :
    ∫ y, ‖u y‖ ^ 2 = ‖UnforcedLeray.toL2 u‖ ^ 2 := by
  rw [rc_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [UnforcedLeray.coeFn_toL2 hu] with x hx
  rw [hx]

theorem realH1Core : RealH1Core := by
  intro u v hu hv hyp
  have hyp' : ∀ φ : Space → Space, UnforcedLeray.Blueprint.IsVectorTest φ →
      inner ℝ (UnforcedLeray.toL2 u)
          (UnforcedLeray.toL2 (UnforcedLeray.Blueprint.ModeId.testLap φ))
        = inner ℝ (UnforcedLeray.toL2 v) (UnforcedLeray.toL2 φ) := by
    intro φ hφ
    rw [rc_inner_toL2 u _ hu
        (rc_memLp_test (UnforcedLeray.Blueprint.ModeId.isVectorTest_testLap hφ)),
      rc_inner_toL2 v φ hv (rc_memLp_test hφ)]
    exact hyp φ hφ
  obtain ⟨F, hFv, hFL⟩ :=
    UnforcedLeray.Blueprint.ModeId.laplacianH1Regularity (UnforcedLeray.toL2 u)
      (UnforcedLeray.toL2 v) hyp'
  have hweak : ∀ (j : Fin 3) (φ : Space → Space), UnforcedLeray.Blueprint.IsVectorTest φ →
      -(∫ y : Space, inner ℝ (u y) (UnforcedLeray.Blueprint.testPartial φ j y))
        = ∫ y : Space, inner ℝ ((F.derivative j : Space → Space) y) (φ y) := by
    intro j φ hφ
    have h1 := UnforcedLeray.Blueprint.L10.H1_inner_testPartial F hφ j
    rw [hFv, rc_inner_toL2 u _ hu
        (rc_memLp_test (UnforcedLeray.Blueprint.ModeId.isVectorTest_testPartial hφ j)),
      rc_inner_L2_toL2 _ (rc_memLp_test hφ)] at h1
    linarith
  have hF2 : ∑ j : Fin 3, ‖F.derivative j‖ ^ 2
      = -inner ℝ (UnforcedLeray.toL2 v) (UnforcedLeray.toL2 u) := by
    have h := hFL F
    rw [hFv] at h
    simp only [real_inner_self_eq_norm_sq] at h
    linarith
  have hbound : -inner ℝ (UnforcedLeray.toL2 v) (UnforcedLeray.toL2 u)
      ≤ ‖UnforcedLeray.toL2 u‖ * ‖UnforcedLeray.toL2 v‖ := by
    have h1 := abs_real_inner_le_norm (UnforcedLeray.toL2 v) (UnforcedLeray.toL2 u)
    linarith [neg_le_abs (inner ℝ (UnforcedLeray.toL2 v) (UnforcedLeray.toL2 u))]
  refine ⟨fun j => ⇑(F.derivative j), fun j => Lp.memLp (F.derivative j),
    fun j φ hφ => hweak j φ hφ, ?_⟩
  dsimp only
  have hL : ∑ j : Fin 3, ∫ y : Space, ‖(F.derivative j : Space → Space) y‖ ^ 2
      = ∑ j : Fin 3, ‖F.derivative j‖ ^ 2 :=
    Finset.sum_congr rfl (fun j _ => (rc_norm_sq (F.derivative j)).symm)
  have hR : (∫ y : Space, ‖u y‖ ^ 2) ^ (1 / 2 : ℝ) * (∫ y : Space, ‖v y‖ ^ 2) ^ (1 / 2 : ℝ)
      = ‖UnforcedLeray.toL2 u‖ * ‖UnforcedLeray.toL2 v‖ := by
    rw [rc_integral_norm_sq u hu, rc_integral_norm_sq v hv, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hR, hL, hF2]
  exact hbound

end UnforcedLeray.Short.PartIIIb.Concrete
