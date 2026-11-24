import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_B1_reg
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily.PhysUniqueCross
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily.Linearity
import UnforcedLeray.Short.PartIIb.Tasks.RowOrdRel
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairLinR.Integrable

/-!
# `PartII-b:G2/1/org/B1`: `PhysKOutLinCombSmooth`

Source of record: `the November 2 reference manuscript`, lines 1214, 2007–2010.

Under joint smoothness `ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)` and `IsPhaseTest p.period Φ`,
`convT p.raw Φ` is continuous on `ℝ × Space` with bounded spatial support, hence bounded on the
compact cylinder `Icc 0 p.period ×ˢ closedBall 0 R` and zero outside it on `phaseCell p.period`.
Combining `nvCInYr_proof` + `memLp_phaseCell_of_phaseLpNorm` for `b₁, b₂ ∈ InHr p.c bgp` yields
Bochner integrability of `dotL (convT p.raw Φ ·) (NvC p.R b_i ·)` on `phaseCell p.period`, whence
linearity of `pairF` on the `b`-side, `hMeas`-a.e. congruence via `CongrHelp.ae_volume_of_ageμ` +
`HrOpHelp.nvC_ae_eq_of_ae_pos`, and `g`-side linearity via `pairF_nvC_toProf_add` /
`pairF_nvC_toProf_smul`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private theorem integrable_dotL_compact_Yr {P r R : ℝ} (hP : 0 < P) (hr1 : 1 ≤ r)
    {F u : ℝ × Space → CVec3} (hFc : Continuous F)
    (hF0 : ∀ τ y, R < ‖y‖ → F (τ, y) = 0) (hu : IsInYr P r u) :
    Integrable (fun x => dotL (F x) (u x)) (volume.restrict (phaseCell P)) := by
  let μ : Measure (ℝ × Space) := volume.restrict (phaseCell P)
  let K : Set (ℝ × Space) := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) (max R 0)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hK.measurableSet
  have hKfin : μ K ≠ ⊤ := by
    have hlt : μ K < ⊤ := by
      rw [Measure.restrict_apply hKm]
      exact lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top
    exact ne_of_lt hlt
  have hum : MemLp u (ENNReal.ofReal r) μ :=
    memLp_phaseCell_of_phaseLpNorm hP (by linarith) hu.meas hu.finite
  have hu_cut : MemLp (K.indicator u) 1 μ :=
    (hum.indicator hKm).mono_exponent_of_measure_support_ne_top
      (fun x hx => Set.indicator_of_notMem hx u) hKfin (ENNReal.one_le_ofReal.2 hr1)
  have hu_int : Integrable (K.indicator u) μ := memLp_one_iff_integrable.mp hu_cut
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hFc.continuousOn
  have hmeas : AEStronglyMeasurable (fun x => dotL (F x) (u x)) μ :=
    dotL.aestronglyMeasurable_comp₂ hFc.aestronglyMeasurable hum.1
  refine (hu_int.norm.const_mul (‖dotL‖ * max M 0)).mono' hmeas ?_
  have hcell_m : MeasurableSet (phaseCell P) := measurableSet_Ioc.prod MeasurableSet.univ
  refine ae_restrict_of_forall_mem hcell_m fun x hx => ?_
  by_cases hy : ‖x.2‖ ≤ max R 0
  · have hxK : x ∈ K := ⟨Ioc_subset_Icc_self hx.1, by simpa [Metric.mem_closedBall] using hy⟩
    have hFM : ‖F x‖ ≤ max M 0 := (hM x hxK).trans (le_max_left M 0)
    calc ‖dotL (F x) (u x)‖
        ≤ ‖dotL‖ * ‖F x‖ * ‖u x‖ := dotL.le_opNorm₂ (F x) (u x)
      _ ≤ ‖dotL‖ * max M 0 * ‖u x‖ := by gcongr
      _ = (‖dotL‖ * max M 0) * ‖K.indicator u x‖ := by rw [Set.indicator_of_mem hxK]
  · have hRlt : R < ‖x.2‖ := (le_max_left R 0).trans_lt (lt_of_not_ge hy)
    have hFx : F (x.1, x.2) = 0 := hF0 x.1 x.2 hRlt
    rw [Prod.mk.eta] at hFx
    rw [hFx, map_zero, zero_apply, norm_zero]
    positivity

private theorem pairF_lincomb_right {P : ℝ} [Fact (0 < P)] (a : ℂ)
    {F u₁ u₂ : ℝ × Space → CVec3}
    (h₁ : Integrable (fun x => dotL (F x) (u₁ x)) (volume.restrict (phaseCell P)))
    (h₂ : Integrable (fun x => dotL (F x) (u₂ x)) (volume.restrict (phaseCell P))) :
    pairF P F (a • u₁ + u₂) = a * pairF P F u₁ + pairF P F u₂ := by
  have hpt : (fun x => dotL (F x) ((a • u₁ + u₂) x)) =
      fun x => a * dotL (F x) (u₁ x) + dotL (F x) (u₂ x) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, smul_eq_mul]
  have hcomb : Integrable (fun x => dotL (F x) ((a • u₁ + u₂) x))
      (volume.restrict (phaseCell P)) := by
    rw [hpt]
    exact (h₁.const_mul a).add h₂
  rw [pairF_eq_restrictedProductIntegral hcomb,
    pairF_eq_restrictedProductIntegral h₁,
    pairF_eq_restrictedProductIntegral h₂]
  simp_rw [hpt]
  rw [integral_add (h₁.const_mul a) h₂, integral_const_mul]
  simp only [Complex.real_smul]
  ring

theorem physKOutLinCombSmooth_proof : UnforcedLeray.Short.IIb.PhysKOutLinCombSmooth := by
  intro p _hν hc hε hraw a b₁ b₂ b g₁ g₂ hb₁ hb₂ hb hk₁ hk₂ hbe Φ hΦ
  have hr1 : (1 : ℝ) ≤ bgp := by norm_num [bgp]
  have hr0 : (0 : ℝ) < bgp := by norm_num [bgp]
  let bs : CProf := (a : ℂ) • b₁ + b₂
  have hbs : InHr p.c bgp bs := HrOpHelp.inHr_add (HrOpHelp.inHr_smul (a : ℂ) hb₁) hb₂
  have hbv : ∀ᵐ x : Coord, 0 < x.1 → b x = bs x :=
    CongrHelp.ae_volume_of_ageμ hc hb.periodic hbs.periodic hbe
  have hNv_ae : NvC p.R b =ᵐ[volume] NvC p.R bs :=
    HrOpHelp.nvC_ae_eq_of_ae_pos hc hε hb hbs hbv
  have hNv_lin : NvC p.R bs = (a : ℂ) • NvC p.R b₁ + NvC p.R b₂ := by
    dsimp only [bs]
    rw [HrOpHelp.nvC_add, HrOpHelp.nvC_smul]
  have hu₁ : IsInYr p.period bgp (NvC p.R b₁) :=
    nvCInYr_proof p.c p.ε bgp b₁ hc hε hr0 hb₁
  have hu₂ : IsInYr p.period bgp (NvC p.R b₂) :=
    nvCInYr_proof p.c p.ε bgp b₂ hc hε hr0 hb₂
  have hFc : Continuous (convT p.raw Φ) := continuous_convT hraw hΦ.smooth
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hF0 : ∀ τ y, R < ‖y‖ → convT p.raw Φ (τ, y) = 0 := convT_eq_zero_of_norm_gt hR
  have hint₁ : Integrable (fun x => dotL (convT p.raw Φ x) (NvC p.R b₁ x))
      (volume.restrict (phaseCell p.period)) :=
    integrable_dotL_compact_Yr p.period_pos hr1 hFc hF0 hu₁
  have hint₂ : Integrable (fun x => dotL (convT p.raw Φ x) (NvC p.R b₂ x))
      (volume.restrict (phaseCell p.period)) :=
    integrable_dotL_compact_Yr p.period_pos hr1 hFc hF0 hu₂
  rw [FreeRespCongrHelp.pairF_congr_ae' p.period (convT p.raw Φ) _ _ hNv_ae,
    hNv_lin, pairF_lincomb_right (a : ℂ) hint₁ hint₂,
    hk₁ Φ hΦ, hk₂ Φ hΦ,
    pairF_nvC_toProf_add p (a • g₁) g₂ hΦ,
    pairF_nvC_toProf_smul p a g₁ hΦ]

end UnforcedLeray.Short.IIb

end
