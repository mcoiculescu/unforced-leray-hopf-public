import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.PotLocIntCell
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.YrLocIntCell
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.CellIntegrable
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.PairFProd
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.ProdTestPhase

/-!
# FubiniUnfold

Source `the November 2 reference manuscript` lines 1351-1362 (weak `y`-gradient of
the stream potential) and 1334-1337 (`Y_r`).

Integrability over one period comes from `cellIntegrable` with the two cell-integrable fields
`bsPot Φ` and `Dψ j`. Orthogonality to smooth periodic `s` comes from `HasPtwOp` tested against the
product phase test `prodTest s g i`, with the pairings computed by `pairFProd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt)
open UnforcedLeray.Short.IIb (IsInYr HasPtwOp)

theorem fubiniUnfold : FubiniUnfold := by
  intro P Φ Dψ hW g hg j i
  unfold WGHyp at hW
  obtain ⟨hP, hΦ, hD⟩ := hW
  obtain ⟨hgC, hgS⟩ : ContDiff ℝ ∞ g ∧ HasCompactSupport g := hg
  have hg' : SmoothCS g := ⟨hgC, hgS⟩
  have hDj : IsInYr P 2 (Dψ j) := (hD j).1
  have hPtw : HasPtwOp P (fun Θ => -dy j Θ) (bsPot Φ) (Dψ j) := (hD j).2
  -- the `i`-th coordinate of an integrable vector field is integrable
  have hcoord : ∀ (F : ℝ × Space → CVec3) (S : Set (ℝ × Space)), IntegrableOn F S volume →
      IntegrableOn (fun x => F x i) S volume := fun F S hF =>
    ContinuousLinearMap.integrableOn_comp
      ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ) hF
  have hPL : ∀ R : ℝ, IntegrableOn (bsPot Φ) (Ioc 0 P ×ˢ closedBall (0 : Space) R) volume :=
    fun R => potLocIntCell P hP Φ hΦ R
  have hYL : ∀ R : ℝ, IntegrableOn (Dψ j) (Ioc 0 P ×ˢ closedBall (0 : Space) R) volume :=
    fun R => yrLocIntCell P hP (Dψ j) hDj R
  -- the test function `y ↦ ∂ⱼ g(y)` is continuous with compact support
  have hc1 : Continuous (fun y : Space => fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) :=
    (hgC.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc1c : HasCompactSupport (fun y : Space => fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) :=
    (hgS.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] ℂ => L (EuclideanSpace.single j (1 : ℝ)))
      (by simp)
  obtain ⟨R1, hR1⟩ := hc1c.isCompact.isBounded.subset_closedBall (0 : Space)
  have hz1 : ∀ y : Space, R1 < ‖y‖ → fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    intro y hy
    have hyt : y ∉ tsupport (fun y : Space => fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) := by
      intro h
      have h1 := hR1 h
      rw [mem_closedBall_zero_iff] at h1
      linarith
    exact image_eq_zero_of_notMem_tsupport (f := fun y : Space =>
      fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) hyt
  obtain ⟨R2, hR2⟩ := hgS.isCompact.isBounded.subset_closedBall (0 : Space)
  have hz2 : ∀ y : Space, R2 < ‖y‖ → g y = 0 := by
    intro y hy
    have hyt : y ∉ tsupport g := by
      intro h
      have h1 := hR2 h
      rw [mem_closedBall_zero_iff] at h1
      linarith
    exact image_eq_zero_of_notMem_tsupport hyt
  -- integrability of the two pieces of `wgFun` over one period
  have hA_int : IntegrableOn
      (fun t : ℝ => ∫ y : Space, fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) * bsPot Φ (t, y) i)
      (Ioc 0 P) volume :=
    cellIntegrable P hP (fun x => bsPot Φ x i) R1 (hcoord (bsPot Φ) _ (hPL R1))
      (fun y => fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) hc1 hz1
  have hB_int : IntegrableOn
      (fun t : ℝ => ∫ y : Space, g y * Dψ j (t, y) i) (Ioc 0 P) volume :=
    cellIntegrable P hP (fun x => Dψ j x i) R2 (hcoord (Dψ j) _ (hYL R2))
      g hgC.continuous hz2
  refine ⟨?_, ?_⟩
  · exact hA_int.add hB_int
  · intro s hs hper
    -- the product test is a phase test
    have hΘ : IsPhaseTest P (prodTest s g i) := prodTestPhase P s g i hs hper hg'
    have hΘ' : pairF P (-dy j (prodTest s g i)) (bsPot Φ) = pairF P (prodTest s g i) (Dψ j) :=
      hPtw _ hΘ
    obtain ⟨hPF1, -⟩ := pairFProd P s g j i hs hg' (bsPot Φ)
    obtain ⟨-, hPF4⟩ := pairFProd P s g j i hs hg' (Dψ j)
    rw [hPF1, hPF4] at hΘ'
    simp only [Complex.real_smul] at hΘ'
    have hinv : ((P⁻¹ : ℝ) : ℂ) * (P : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hP.ne', Complex.ofReal_one]
    have alg : ∀ (c p a b : ℂ), c * p = 1 → -(c * a) = c * b → a + b = 0 := by
      intro c p a b hc h
      linear_combination (-p) * h - (a + b) * hc
    have key := alg _ _ _ _ hinv hΘ'
    -- integrability of the weighted pieces on one period
    have hsA : IntegrableOn
        (fun t : ℝ => s t * ∫ y : Space,
          fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) * bsPot Φ (t, y) i) (Ioc 0 P) volume :=
      IntegrableOn.continuousOn_mul_of_subset hs.continuous.continuousOn hA_int isCompact_Icc
        measurableSet_Ioc Ioc_subset_Icc_self
    have hsB : IntegrableOn
        (fun t : ℝ => s t * ∫ y : Space, g y * Dψ j (t, y) i) (Ioc 0 P) volume :=
      IntegrableOn.continuousOn_mul_of_subset hs.continuous.continuousOn hB_int isCompact_Icc
        measurableSet_Ioc Ioc_subset_Icc_self
    simp only [wgFun, mul_add]
    exact (integral_add hsA hsB).trans key
