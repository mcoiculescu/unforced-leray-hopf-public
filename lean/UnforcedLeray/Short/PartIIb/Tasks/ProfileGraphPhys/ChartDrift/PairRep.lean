import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.PeriodicRepresentative
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.ChartNull
import UnforcedLeray.Short.PartIIb.Sub.T07

/-!
# `PartII-b:T10/6/3/1/2d`: a.e. invariance of the pairing under the periodic representative

Given `b ∈ H_r`, take the measurable everywhere `c`-periodic representative `b'` and its
periodic null set `M` from `periodicRepresentative` (`Sub/T07`, `b = b'` off `M` on `s > 0`).

* `NvC` at a chart point with `s > 0` only reads `b` there; on the axis (`age = 0`) both lifts
  vanish. Off `M` (`chartNullPullback`) the lifts agree for a.e. `(τ, y)` in `(0, P] × ℝ³`, so the
  pairings agree.
* `b x i * φ x = b' x i * φ x` off `M` (`φ` vanishes for `s ≤ 0`), and `M` is null, so the
  integrals agree.
* `b' ∈ H_r` since `b' = b` `hMeas`-a.e. (the null set `M` and `{s ≤ 0}` are `ageμ`-null).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- The age measure gives no mass to `{s ≤ 0}` (its first factor lives on `(0, ∞)`). -/
theorem prep_ageμ_nonpos (c a : ℝ) : Axi.ageμ c a {p : ℝ × (ℝ × ℝ) | p.1 ≤ 0} = 0 := by
  have hset : {p : ℝ × (ℝ × ℝ) | p.1 ≤ 0} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext p
    simp
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  unfold Axi.ageμ
  rw [hset, Measure.prod_prod]
  have hI : ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a))
      (Iic 0) = 0 := by
    rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.Iic_inter_Ioi, Set.Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
  rw [hI, zero_mul]

theorem prep_realC_zero : B0412.realC (0 : Space) = 0 := by
  ext i
  simp [B0412.realC_apply]

/-- Off the null set `M`, on `s > 0`, the ring lifts of `b` and `b'` agree at `(τ, y)` whenever the
chart point avoids `M`. -/
theorem prep_NvC_eq (b b' : CProf) (M : Set Coord)
    (hkey : ∀ x : Coord, 0 < x.1 → x ∉ M → b x = b' x) (R τ : ℝ) (y : Space)
    (hy : Axi.chart R τ y ∉ M) : NvC R b (τ, y) = NvC R b' (τ, y) := by
  by_cases h0 : Axi.age R y = 0
  · simp [NvC, Axi.Nv, h0, prep_realC_zero]
  · have hpos : 0 < (Axi.chart R τ y).1 :=
      lt_of_le_of_ne (Axi.age_nonneg R y) (Ne.symm h0)
    have hx : b (Axi.chart R τ y) = b' (Axi.chart R τ y) := hkey _ hpos hy
    simp only [NvC, Axi.Nv, hx]

theorem pairRep_proof : UnforcedLeray.Short.IIb.ChartLift.PairRep := by
  intro c ε r φ i b hc hε hr hφ hb
  obtain ⟨b', M, hb'm, hb'per, hMm, hM0, hMper, hkey⟩ :=
    periodicRepresentative c r hc b hb.periodic hb.meas
  -- `b' = b` `hMeas`-a.e.
  have hae : b' =ᵐ[hMeas c r] b := by
    have hsub : {x : Coord | ¬ (b' x = b x)} ⊆ M ∪ {p : ℝ × (ℝ × ℝ) | p.1 ≤ 0} := by
      intro x hx
      by_cases h1 : x.1 ≤ 0
      · exact Or.inr h1
      · left
        by_contra hM
        exact hx (hkey x (not_le.1 h1) hM).symm
    have hnull : hMeas c r {x : Coord | ¬ (b' x = b x)} = 0 :=
      measure_mono_null hsub
        (measure_union_null (ageμ_null_of_volume_null hc hMm hM0) (prep_ageμ_nonpos c _))
    exact ae_iff.2 hnull
  have hIn : InHr c r b' := by
    refine ⟨Filter.Eventually.of_forall (fun x => hb'per x.1 x.2.1 x.2.2),
      hb'm.aestronglyMeasurable, ?_⟩
    have hN : hNorm c r b' = hNorm c r b := by
      unfold hNorm
      exact eLpNorm_congr_ae hae
    rw [hN]
    exact hb.finite
  -- the pairing
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]
    ring
  have hcnp := chartNullPullback ε⁻¹ c (2 * ε * c) (inv_pos.2 hε) hc hP M hMm hM0 hMper
  have hpt : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      ∀ᵐ y : Space, NvC ε⁻¹ b (τ, y) = NvC ε⁻¹ b' (τ, y) := by
    filter_upwards [hcnp] with τ hτ
    filter_upwards [hτ] with y hy
    exact prep_NvC_eq b b' M hkey ε⁻¹ τ y hy
  have hpair : pairF (2 * ε * c) (ChartLift.liftTest c ε φ i) (NvC ε⁻¹ b) =
      pairF (2 * ε * c) (ChartLift.liftTest c ε φ i) (NvC ε⁻¹ b') := by
    unfold pairF phaseInt
    congr 1
    apply integral_congr_ae
    filter_upwards [hpt] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ] with y hy
    simp only [hy]
  -- the integral identity: `φ` vanishes for `s ≤ 0`, and `M` is null
  have hφ0 : ∀ x : Coord, x.1 ≤ 0 → φ x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ hne
    have h1 := hφ.supp hmem
    have h2 : (0 : ℝ) < x.1 := (Set.mem_prod.1 h1).1
    linarith
  have hMae : ∀ᵐ x ∂(volume : Measure Coord), x ∉ M :=
    measure_eq_zero_iff_ae_notMem.1 hM0
  have hint : ∫ x, b x i * (φ x : ℂ) = ∫ x, b' x i * (φ x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [hMae] with x hx
    by_cases h : 0 < x.1
    · rw [hkey x h hx]
    · rw [hφ0 x (not_lt.1 h)]
      simp
  exact ⟨b', hIn, hb'm, fun s ξ η => hb'per s ξ η, hpair, hint⟩

end UnforcedLeray.Short.IIb
