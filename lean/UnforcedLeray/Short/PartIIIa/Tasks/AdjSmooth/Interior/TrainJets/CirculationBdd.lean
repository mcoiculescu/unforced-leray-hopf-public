import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Units.B0238
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/2/17`: the circulation of the train on strips

Proof of `TjCirculationBdd` (`Sub/AdjInterior/Train/Defs.lean`, SP 270-288).

With `u = v(ρ)`, `E = ∂_q u₂ - ∂_η u₁`:

* the `∂_q u₂` part vanishes on each horizontal line by `c`-periodicity of `u`;
* the `∂_η u₁` part, after Fubini (`intervalIntegral_intervalIntegral_swap`), has inner
  `η`-integral `u₁(q, b) - u₁(q, a)`, bounded by `2M` on the `q`-interval of length `c`.

The continuity of the partial derivatives of the `C^1` field is proved separately.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The partial derivative `∂_η` of a `C¹` function on the plane is jointly continuous. -/
theorem tj_partialEta_continuous {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    Continuous (fun z : ℝ × ℝ => UnforcedLeray.Cyl.partialEta G z) := by
  have h1 : ∀ z : ℝ × ℝ, HasDerivAt (fun η : ℝ => G (z.1, η)) (fderiv ℝ G z (0, 1)) z.2 := by
    intro z
    have hd : HasFDerivAt G (fderiv ℝ G z) z :=
      ((hG.differentiable one_ne_zero) z).hasFDerivAt
    have hl : HasDerivAt (fun η : ℝ => ((z.1, η) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    exact hd.comp_hasDerivAt z.2 hl
  have hc : Continuous (fun z : ℝ × ℝ => fderiv ℝ G z (0, 1)) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact hc.congr (fun z => (h1 z).deriv.symm)

theorem tjCirculationBdd : TjCirculationBdd := by
  intro ν c tr hc ρ hρ M hM a b
  -- the velocity at age `ρ` is `C^1` and `c`-periodic
  have hu1 : ContDiff ℝ 1 (tr.v ρ) :=
    (UnforcedLeray.B0238.contDiff_Vc tr hρ).of_le (by exact_mod_cast le_top)
  have hper : ∀ z : ℝ × ℝ, tr.v ρ (z.1 + c, z.2) = tr.v ρ z :=
    tr.isTrain.periodic_v ρ hρ
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ × ℝ → ℝ, F = fun z => tr.v ρ z 1 := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℝ, G = fun z => tr.v ρ z 0 := ⟨_, rfl⟩
  have hF : ContDiff ℝ 1 F := by
    rw [hFdef]; exact (EuclideanSpace.proj (1 : Fin 2)).contDiff.comp hu1
  have hG : ContDiff ℝ 1 G := by
    rw [hGdef]; exact (EuclideanSpace.proj (0 : Fin 2)).contDiff.comp hu1
  -- the vorticity is `∂_q F - ∂_η G`
  have hEq : ∀ η q : ℝ, UnforcedLeray.B0238.Ec tr ρ (q, η) =
      UnforcedLeray.Cyl.partialQ F (q, η) - UnforcedLeray.Cyl.partialEta G (q, η) := by
    intro η q
    rw [hFdef, hGdef]
    rfl
  -- the bound on the second component
  have hbound : ∀ z : ℝ × ℝ, |G z| ≤ M := by
    intro z
    rw [hGdef, ← Real.norm_eq_abs]
    exact le_trans (PiLp.norm_apply_le _ 0) (hM z)
  -- continuity of the partial derivatives in each variable
  have hJ : Continuous (fun z : ℝ × ℝ => UnforcedLeray.Cyl.partialEta G z) :=
    tj_partialEta_continuous hG
  have hcQ : ∀ η : ℝ, Continuous (fun q : ℝ => UnforcedLeray.Cyl.partialQ F (q, η)) := by
    intro η
    have hcd : ContDiff ℝ 1 (fun q : ℝ => F (q, η)) :=
      hF.comp (contDiff_id.prodMk contDiff_const)
    exact hcd.continuous_deriv le_rfl
  have hcE : ∀ η : ℝ, Continuous (fun q : ℝ => UnforcedLeray.Cyl.partialEta G (q, η)) :=
    fun η => hJ.comp (continuous_id.prodMk continuous_const)
  -- the `q`-integral of `∂_q F` on each line vanishes by periodicity
  have hA : ∀ η : ℝ, ∫ q in (-(c / 2))..(c / 2), UnforcedLeray.Cyl.partialQ F (q, η) = 0 := by
    intro η
    have hderiv : ∀ q ∈ uIcc (-(c / 2)) (c / 2),
        HasDerivAt (fun q' : ℝ => F (q', η)) (UnforcedLeray.Cyl.partialQ F (q, η)) q := by
      intro q _
      have hcd : ContDiff ℝ 1 (fun q' : ℝ => F (q', η)) :=
        hF.comp (contDiff_id.prodMk contDiff_const)
      exact (hcd.differentiable one_ne_zero q).hasDerivAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ((hcQ η).intervalIntegrable _ _)]
    have hp := hper (-(c / 2), η)
    rw [show -(c / 2) + c = c / 2 by ring] at hp
    simp only [hFdef]
    rw [hp, sub_self]
  -- the inner `q`-integral of the vorticity, pointwise in `η`
  have hstep1 : (∫ η in a..b, ∫ q in (-(c / 2))..(c / 2),
      UnforcedLeray.B0238.Ec tr ρ (q, η)) =
      -∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), UnforcedLeray.Cyl.partialEta G (q, η) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro η _
    simp only [hEq]
    rw [intervalIntegral.integral_sub ((hcQ η).intervalIntegrable _ _)
      ((hcE η).intervalIntegrable _ _), hA η]
    ring
  -- Fubini on the rectangle
  have hcont2 : Continuous (Function.uncurry fun η q : ℝ =>
      UnforcedLeray.Cyl.partialEta G (q, η)) :=
    hJ.comp (continuous_snd.prodMk continuous_fst)
  have hint : IntegrableOn (Function.uncurry fun η q : ℝ =>
      UnforcedLeray.Cyl.partialEta G (q, η))
      (uIoc a b ×ˢ uIoc (-(c / 2)) (c / 2)) :=
    ((hcont2.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc))
  have hswap : (∫ η in a..b, ∫ q in (-(c / 2))..(c / 2),
      UnforcedLeray.Cyl.partialEta G (q, η)) =
      ∫ q in (-(c / 2))..(c / 2), ∫ η in a..b, UnforcedLeray.Cyl.partialEta G (q, η) :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hint
  -- the inner `η`-integral is `G(q, b) - G(q, a)`
  have hcη : ∀ q : ℝ, Continuous (fun η : ℝ => UnforcedLeray.Cyl.partialEta G (q, η)) :=
    fun q => hJ.comp (continuous_const.prodMk continuous_id)
  have hq : ∀ q : ℝ, ∫ η in a..b, UnforcedLeray.Cyl.partialEta G (q, η) =
      G (q, b) - G (q, a) := by
    intro q
    have hcd : ContDiff ℝ 1 (fun η' : ℝ => G (q, η')) :=
      hG.comp (contDiff_const.prodMk contDiff_id)
    have hderiv : ∀ η ∈ uIcc a b,
        HasDerivAt (fun η' : ℝ => G (q, η')) (UnforcedLeray.Cyl.partialEta G (q, η)) η := by
      intro η _
      exact (hcd.differentiable one_ne_zero η).hasDerivAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ((hcη q).intervalIntegrable _ _)]
  -- the bound on each inner integral and the conclusion
  have hbd : ∀ q : ℝ, ‖G (q, b) - G (q, a)‖ ≤ 2 * M := by
    intro q
    have h1 := abs_le.mp (hbound (q, b))
    have h2 := abs_le.mp (hbound (q, a))
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [hstep1, abs_neg, hswap]
  simp only [hq]
  rw [← Real.norm_eq_abs]
  calc ‖∫ q in (-(c / 2))..(c / 2), (G (q, b) - G (q, a))‖
      ≤ (2 * M) * |c / 2 - -(c / 2)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun q _ => hbd q)
    _ = 2 * c * M := by
        rw [show c / 2 - -(c / 2) = c by ring, abs_of_pos hc]; ring

end UnforcedLeray.Short.IIIa
