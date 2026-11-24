import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Lib.Sobolev.Cylinder
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `PartIII-a:T21/2/7/2/1/1/7/8`: uniqueness of the cell weak derivative

Source: `the November 2 reference manuscript` lines 3060-3061.
If `g` and `g'` are both weak `∂_j`-derivatives of `φ` on the cylinder, then `g = g'` a.e. on the
cell.  Subtracting the two identities gives `∫_cell (g - g') ψ = 0` for every cylinder test `ψ`;
the periodization `Sob.exists_isCylTest_eq` provides cylinder tests equal to any bump in the open
cell, and the fundamental lemma on the open cell (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`)
together with the null boundary of the cell finishes the proof.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem cellWeakUnique : UnforcedLeray.Short.IIIa.CellWeakUnique := by
  intro c j φ g g' hc hg hg'
  have hUo : IsOpen (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hUcell : Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) ⊆ B0579.cell c :=
    fun y hy => ⟨⟨hy.1.1.le, hy.1.2⟩, mem_univ _⟩
  -- the boundary line `x₁ = -c/2` is Lebesgue null
  have hnull : volume {x : ℝ × ℝ | x.1 = -(c / 2)} = 0 := by
    have e : {x : ℝ × ℝ | x.1 = -(c / 2)} = ({-(c / 2)} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      ext x
      simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hae1 : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x.1 ≠ -(c / 2) := by
    rw [ae_iff]
    simpa using hnull
  have hae2 : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), x.1 ≠ -(c / 2) :=
    ae_restrict_of_ae hae1
  -- the integral identity against cylinder tests supported in the open cell
  have hint : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) →
      ∫ x, ψ x • (g x - g' x) ∂(volume.restrict (B0579.cell c)) = 0 := by
    intro ψ hψ hψc hψU
    obtain ⟨Φ, hΦ, hΦeq⟩ := UnforcedLeray.Sob.exists_isCylTest_eq hc hψ hψc hψU
    have hΦc : B0579.IsCylTest c Φ :=
      { smooth := hΦ.smooth
        periodic := fun x => by
          have h := hΦ.periodic x
          rw [show x + ((c : ℝ), (0 : ℝ)) = (x.1 + c, x.2) by ext <;> simp] at h
          exact h
        band := hΦ.bounded }
    have hgI : IntegrableOn (fun x => g x * (Φ x : ℂ)) (B0579.cell c) := (hg.1 Φ hΦc).2
    have hg'I : IntegrableOn (fun x => g' x * (Φ x : ℂ)) (B0579.cell c) := (hg'.1 Φ hΦc).2
    have hE1 := hg.2 Φ hΦc
    have hE2 := hg'.2 Φ hΦc
    have hEq : ∫ x in B0579.cell c, g x * (Φ x : ℂ) = ∫ x in B0579.cell c, g' x * (Φ x : ℂ) :=
      neg_injective (hE1.symm.trans hE2)
    have hsplit : ∫ x in B0579.cell c, (g x - g' x) * (Φ x : ℂ) = 0 := by
      simp only [sub_mul]
      rw [integral_sub hgI hg'I, hEq, sub_self]
    have hcongr : ∫ x, ψ x • (g x - g' x) ∂(volume.restrict (B0579.cell c)) =
        ∫ x in B0579.cell c, (g x - g' x) * (Φ x : ℂ) :=
      setIntegral_congr_fun (B0579.measurableSet_cell c) (fun x hx => by
        show ψ x • (g x - g' x) = (g x - g' x) * (Φ x : ℂ)
        rw [Complex.real_smul, hΦeq x hx]
        ring)
    rw [hcongr, hsplit]
  -- restriction to a measurable subset of the cell
  have hrestr : ∀ (f : ℝ × ℝ → ℂ) (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ B0579.cell c →
      IntegrableOn f s volume → IntegrableOn f s (volume.restrict (B0579.cell c)) := by
    intro f s hs hsc hf
    have e : (volume.restrict (B0579.cell c)).restrict s = volume.restrict s := by
      rw [Measure.restrict_restrict hs, Set.inter_eq_left.2 hsc]
    unfold IntegrableOn at hf ⊢
    rw [e]
    exact hf
  -- local integrability of `g - g'` on the open cell
  have hloc : LocallyIntegrableOn (fun x => g x - g' x) (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ))
      (volume.restrict (B0579.cell c)) := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo x hx
    let f : ContDiffBump x :=
      { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
    have hf1 : ∀ y ∈ Metric.ball x (r / 4), f y = 1 := fun y hy =>
      f.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    have hts : tsupport f ⊆ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := by
      rw [ContDiffBump.tsupport_eq]
      exact (Metric.closedBall_subset_ball (show f.rOut < r by
        show r / 2 < r
        linarith)).trans hball
    obtain ⟨Φ, hΦ, hΦeq⟩ := UnforcedLeray.Sob.exists_isCylTest_eq hc f.contDiff
      f.hasCompactSupport hts
    have hΦc : B0579.IsCylTest c Φ :=
      { smooth := hΦ.smooth
        periodic := fun y => by
          have h := hΦ.periodic y
          rw [show y + ((c : ℝ), (0 : ℝ)) = (y.1 + c, y.2) by ext <;> simp] at h
          exact h
        band := hΦ.bounded }
    have hsubset : Metric.ball x (r / 4) ⊆ B0579.cell c :=
      (Metric.ball_subset_ball (by linarith)).trans (hball.trans hUcell)
    have hΦball : ∀ y ∈ Metric.ball x (r / 4), Φ y = 1 := fun y hy => by
      rw [hΦeq y (hsubset hy)]
      exact hf1 y hy
    have hgI' : IntegrableOn g (Metric.ball x (r / 4)) (volume.restrict (B0579.cell c)) := by
      refine (hrestr _ _ Metric.isOpen_ball.measurableSet hsubset
        ((hg.1 Φ hΦc).2.mono_set hsubset)).congr_fun (fun y hy => ?_)
        Metric.isOpen_ball.measurableSet
      show g y * (Φ y : ℂ) = g y
      rw [hΦball y hy]
      simp
    have hg'I' : IntegrableOn g' (Metric.ball x (r / 4)) (volume.restrict (B0579.cell c)) := by
      refine (hrestr _ _ Metric.isOpen_ball.measurableSet hsubset
        ((hg'.1 Φ hΦc).2.mono_set hsubset)).congr_fun (fun y hy => ?_)
        Metric.isOpen_ball.measurableSet
      show g' y * (Φ y : ℂ) = g' y
      rw [hΦball y hy]
      simp
    exact ⟨Metric.ball x (r / 4),
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (by positivity)),
      hgI'.sub hg'I'⟩
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume.restrict (B0579.cell c))
    hUo hloc hint
  filter_upwards [hae, ae_restrict_mem (B0579.measurableSet_cell c), ae_restrict_of_ae hae1]
    with x hx1 hx2 hx3
  have hxU : x ∈ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) :=
    ⟨⟨lt_of_le_of_ne hx2.1.1 (Ne.symm hx3), hx2.1.2⟩, mem_univ _⟩
  have h0 : g x - g' x = 0 := hx1 hxU
  exact sub_eq_zero.1 h0

end UnforcedLeray.Short.IIIa
