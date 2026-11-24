import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# `PartII-b:T10/2` (`ProfileRegularize`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1902-1906, 1633-1637.

The profile `b` of the hypothesis is arbitrary, in particular on `s ≤ 0` (where the chart never
lands), so the true inverse-chart facts concern `s > 0` only:

* `ProfileMeasOfLift`: if `N_v b ∈ Y_r` then `b` is `hMeas`-a.e. strongly measurable (the chart
  `(τ, y) ↦ (s, ξ, η)` is a submersion with a measurable section family; `b ∘ chart` is a.e.
  measurable on `ℝ × ℝ³`, hence `b` is a.e. measurable on the chart space);
* `ProfilePosPeriodic`: if `N_v b ∈ Y_r` then `b (s, ξ + c, η) = b (s, ξ, η)` for a.e. `s > 0`
  (`chart R (τ + P) y = qShift c (chart R τ y)` by `Axi.chart_add_period`, and the converse chart
  null-set statement `phaseAvg_ringChart` with `G = 1_B`).

`profileRegularize_of` derives `ProfileRegularize` from these two by cutting `b` off to `0` on `s ≤ 0`,
taking the periodic representative (`periodicRepresentative`) and `chart_null_all`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

/-- **`T10/2/1`** (SP 1902-1906): measurability of a profile from the measurability of its lift.
If the lift `N_v b` of an arbitrary profile `b` lies in `Y_r`, then `b` is a.e. strongly measurable
for `hMeas c r = s^{r/2-5/2} ds dξ/c dη` (carried by `s > 0`). -/
def ProfileMeasOfLift : Prop :=
  ∀ (c ε r : ℝ) (b : CProf), 0 < c → 0 < ε → 0 < r → IsInYr (2 * ε * c) r (NvC ε⁻¹ b) →
    AEStronglyMeasurable b (hMeas c r)

/-- **`T10/2/2`** (SP 1902-1906): `P`-periodicity of the lift in the phase is `c`-periodicity of the
profile in `q`, almost everywhere on `s > 0` (values on `s ≤ 0` are irrelevant). -/
def ProfilePosPeriodic : Prop :=
  ∀ (c ε r : ℝ) (b : CProf), 0 < c → 0 < ε → 0 < r → IsInYr (2 * ε * c) r (NvC ε⁻¹ b) →
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))), b (qShift c x) = b x

theorem ageμ_ae_pos (c a : ℝ) : ∀ᵐ x ∂(Axi.ageμ c a), 0 < x.1 := by
  rw [ae_iff]
  have h : {x : Coord | ¬ 0 < x.1} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext x; simp
  haveI : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ; infer_instance
  have hI : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and,
      not_lt]; exact id
  rw [h, Axi.ageμ, Measure.prod_prod, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hI]
  simp

theorem ageμ_ac_volume (c a : ℝ) : Axi.ageμ c a ≪ (volume : Measure Coord) := by
  rw [Axi.ageμ, Measure.volume_eq_prod]
  refine Measure.AbsolutelyContinuous.prod ?_ ?_
  · exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · unfold Cyl.avgμ
    exact (Measure.smul_absolutelyContinuous).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem phaseLpNorm_congr_ae {P r : ℝ} {f f' : ℝ × Space → CVec3} (h : f =ᵐ[volume] f') :
    phaseLpNorm P r f = phaseLpNorm P r f' := by
  unfold phaseLpNorm
  congr 2
  have h2 : ∀ᵐ t : ℝ, ∀ᵐ y : Space, f (t, y) = f' (t, y) := by
    rw [Measure.volume_eq_prod] at h
    exact Measure.ae_ae_of_ae_prod h
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h2] with t ht
  refine lintegral_congr_ae ?_
  filter_upwards [ht] with y hy
  rw [hy]

open NvCInYrHelp in
/-- **`ProfileRegularize` from the two inverse-chart facts.** -/
theorem profileRegularize_of (h1 : ProfileMeasOfLift) (h2 : ProfilePosPeriodic) :
    ProfileRegularize := by
  intro c ε r b hc hε hr hY
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hR0 : ε⁻¹ ≠ 0 := hR.ne'
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hmeas := h1 c ε r b hc hε hr hY
  have hper := h2 c ε r b hc hε hr hY
  -- the cut-off profile
  set b₁ : CProf := fun x => if 0 < x.1 then b x else 0 with hb₁
  have hb₁pos : ∀ x : Coord, 0 < x.1 → b₁ x = b x := fun x hx => by simp [hb₁, hx]
  have hper1 : QPeriodic c b₁ := by
    have := (ae_restrict_iff' hS).1 hper
    refine QPerHalf.of_ae ?_
    filter_upwards [this] with x hx
    by_cases hpos : 0 < x.1
    · have hx' := hx ⟨hpos, mem_univ _⟩
      have hq : 0 < (qShift c x).1 := hpos
      rw [hb₁pos _ hq, hb₁pos _ hpos]
      exact hx'
    · have hq : ¬ 0 < (qShift c x).1 := hpos
      simp [hb₁, hpos, hq]
  have hae1 : b₁ =ᵐ[hMeas c r] b := by
    filter_upwards [ageμ_ae_pos c (r / 2 - 5 / 2)] with x hx
    exact hb₁pos x hx
  have hmeas1 : AEStronglyMeasurable b₁ (hMeas c r) := hmeas.congr hae1.symm
  obtain ⟨b', M, hb'm, hb'per, hMm, hM0, hMper, hkey⟩ :=
    periodicRepresentative c r hc b₁ hper1 hmeas1
  have hMae : ∀ᵐ x : Coord, x ∉ M := measure_eq_zero_iff_ae_notMem.1 hM0
  have hNull := chart_null_all (P := 2 * ε * c) hR hc hP M hMm hM0 hMper
  have hax : ∀ᵐ x : ℝ × Space, x.2 ∉ Axi.axis :=
    (Measure.quasiMeasurePreserving_snd).ae Axi.ae_not_mem_axis
  have hNN : NvC ε⁻¹ b' =ᵐ[volume] NvC ε⁻¹ b := by
    filter_upwards [hNull, hax] with x hxM hxax
    have hpos : 0 < Axi.age ε⁻¹ x.2 := Axi.age_pos hR0 hxax
    have k1 := hkey _ (show 0 < (Axi.chart ε⁻¹ x.1 x.2).1 from hpos) hxM
    have k2 := hb₁pos (Axi.chart ε⁻¹ x.1 x.2) hpos
    have key : b (Axi.chart ε⁻¹ x.1 x.2) = b' (Axi.chart ε⁻¹ x.1 x.2) := k2.symm.trans k1
    simp only [NvC, Axi.Nv, key]
  have hper' : QPeriodic c b' := Filter.Eventually.of_forall fun x => hb'per x.1 x.2.1 x.2.2
  have hmeas' : AEStronglyMeasurable b' (hMeas c r) := hb'm.aestronglyMeasurable
  refine ⟨b', ?_, ?_, ⟨hper', hmeas', ?_⟩, hNN⟩
  · refine (ae_restrict_iff' hS).2 ?_
    filter_upwards [hMae] with x hxM hxS
    exact ((hkey x hxS.1 hxM).symm.trans (hb₁pos x hxS.1)) |>.symm.symm
  · filter_upwards [ageμ_ae_pos c (r / 2 - 5 / 2), (ageμ_ac_volume c (r / 2 - 5 / 2)).ae_le hMae]
      with x hx hxM
    exact ((hkey x hx hxM).symm.trans (hb₁pos x hx))
  · have e := phaseLpNorm_NvC hc hr hε b' hper' hmeas'
    rw [phaseLpNorm_congr_ae hNN] at e
    have hfin := hY.finite
    rw [e] at hfin
    have hκ0 : ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    by_contra hcon
    have htop : hNorm c r b' = ⊤ := not_lt_top_iff.1 hcon
    rw [htop, ENNReal.mul_top hκ0] at hfin
    exact lt_irrefl _ hfin

end UnforcedLeray.Short.IIb
