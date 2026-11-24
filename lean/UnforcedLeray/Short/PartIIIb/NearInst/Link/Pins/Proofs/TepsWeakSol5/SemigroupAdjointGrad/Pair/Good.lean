import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4_4

/-!
# Leaf G: `repX F` is the pull-back of an `L²(PSpace P)` class (`RepXGood`)

Source `the November 2 reference manuscript`
1339-1362, 3346-3352.

`repX P F x = F (x.2, (x.1 : AddCircle P))`.  The map
`qmap P x = (x.2, (x.1 : AddCircle P))` is measure preserving from
`volume.restrict (Ioc t (t+P) ×ˢ univ)` onto `volume` on `PSpace P`, for every `t`
(`AddCircle.measurePreserving_mk`), hence quasi-measure preserving from `ℝ × Space`
(a null set pulls back to a countable union of null pieces `Ioc (nP) (nP+P) × Space`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0223 (SpaceC X PSpace outerS)

/-- The map `(τ, y) ↦ (y, τ mod P)` from spacetime to `PSpace P`. -/
def rgQmap (P : ℝ) (x : ℝ × Space) : PSpace P := (x.2, (x.1 : AddCircle P))

/-- Measure preservation on one period `Ioc t (t+P)`, for every base point `t`. -/
theorem rgQmap_mp (P : ℝ) [Fact (0 < P)] (t : ℝ) :
    MeasurePreserving (rgQmap P)
      (volume.restrict (Ioc t (t + P) ×ˢ (univ : Set Space))) volume := by
  have hmk : MeasurePreserving (fun s : ℝ => (s : AddCircle P))
      (volume.restrict (Ioc t (t + P))) volume :=
    AddCircle.measurePreserving_mk (T := P) t
  have hres : (volume : Measure (ℝ × Space)).restrict (Ioc t (t + P) ×ˢ (univ : Set Space)) =
      ((volume : Measure ℝ).restrict (Ioc t (t + P))).prod (volume : Measure Space) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hres]
  have h1 : MeasurePreserving (Prod.swap : ℝ × Space → Space × ℝ)
      (((volume : Measure ℝ).restrict (Ioc t (t + P))).prod (volume : Measure Space))
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioc t (t + P)))) :=
    Measure.measurePreserving_swap
  have h2 : MeasurePreserving (Prod.map (id : Space → Space) (fun s : ℝ => (s : AddCircle P)))
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioc t (t + P))))
      ((volume : Measure Space).prod (volume : Measure (AddCircle P))) :=
    (MeasurePreserving.id volume).prod hmk
  have h3 := h2.comp h1
  rw [← Measure.volume_eq_prod] at h3
  exact h3

/-- The null-set property of `rgQmap` on the whole of `ℝ × Space`. -/
theorem rgQmap_null (P : ℝ) [hP : Fact (0 < P)] (N : Set (PSpace P)) (hN : MeasurableSet N)
    (hN0 : volume N = 0) : volume (rgQmap P ⁻¹' N : Set (ℝ × Space)) = 0 := by
  have hmeas : Measurable (rgQmap P) := by
    refine Measurable.prodMk measurable_snd ?_
    exact (AddCircle.measurable_mk' (a := P)).comp measurable_fst
  have hcov : ∀ τ : ℝ, ∃ n : ℤ, τ ∈ Ioc ((n : ℝ) * P) ((n : ℝ) * P + P) := by
    intro τ
    have hτ : τ ∈ ⋃ n : ℤ, Ioc (n • P) ((n + 1) • P) := by
      rw [iUnion_Ioc_zsmul hP.out]
      trivial
    obtain ⟨n, hn⟩ := mem_iUnion.mp hτ
    refine ⟨n, ?_⟩
    simpa [zsmul_eq_mul, add_mul] using hn
  have hsub : (rgQmap P ⁻¹' N : Set (ℝ × Space)) ⊆
      ⋃ n : ℤ, ((rgQmap P ⁻¹' N : Set (ℝ × Space)) ∩
        (Ioc ((n : ℝ) * P) ((n : ℝ) * P + P) ×ˢ (univ : Set Space))) := by
    intro x hx
    obtain ⟨n, hn⟩ := hcov x.1
    exact mem_iUnion.mpr ⟨n, hx, mem_prod.mpr ⟨hn, mem_univ _⟩⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
  have hS : MeasurableSet (Ioc ((n : ℝ) * P) ((n : ℝ) * P + P) ×ˢ (univ : Set Space)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  rw [← Measure.restrict_apply' hS]
  rw [(rgQmap_mp P ((n : ℝ) * P)).measure_preimage hN.nullMeasurableSet, hN0]

/-- `rgQmap` is quasi-measure preserving from `ℝ × Space` to `PSpace P`. -/
theorem rgQmap_qmp (P : ℝ) [Fact (0 < P)] :
    Measure.QuasiMeasurePreserving (rgQmap P) (volume : Measure (ℝ × Space))
      (volume : Measure (PSpace P)) := by
  have hmeas : Measurable (rgQmap P) := by
    refine Measurable.prodMk measurable_snd ?_
    exact (AddCircle.measurable_mk' (a := P)).comp measurable_fst
  refine ⟨hmeas, fun s hs => ?_⟩
  -- `map (rgQmap P) volume s = 0` when `volume s = 0`
  have hpre : ∀ N : Set (PSpace P), MeasurableSet N → volume N = 0 →
      Measure.map (rgQmap P) (volume : Measure (ℝ × Space)) N = 0 := by
    intro N hN hN0
    rw [Measure.map_apply hmeas hN]
    exact rgQmap_null P N hN hN0
  have hle : Measure.map (rgQmap P) (volume : Measure (ℝ × Space)) s ≤
      Measure.map (rgQmap P) (volume : Measure (ℝ × Space)) (toMeasurable volume s) :=
    measure_mono (subset_toMeasurable _ _)
  have h0 : Measure.map (rgQmap P) (volume : Measure (ℝ × Space)) (toMeasurable volume s) = 0 :=
    hpre _ (measurableSet_toMeasurable _ _) (by rw [measure_toMeasurable]; exact hs)
  exact le_antisymm (hle.trans_eq h0) zero_le

/-- **Leaf G** (source 1339-1362, 3346-3352). -/
theorem repXGood : RepXGood := by
  intro P _ F
  have hF : AEStronglyMeasurable (fun z : PSpace P => (F : PSpace P → SpaceC) z) volume :=
    Lp.aestronglyMeasurable F
  refine ⟨?_, ?_, ?_⟩
  · -- a.e. measurability
    exact hF.comp_quasiMeasurePreserving (rgQmap_qmp P)
  · intro τ y
    show (F : PSpace P → SpaceC) (y, ((τ + P : ℝ) : AddCircle P)) =
      (F : PSpace P → SpaceC) (y, (τ : AddCircle P))
    rw [AddCircle.coe_add_period]
  · -- integrability of `‖F‖²` on one period
    have hmp := rgQmap_mp P 0
    rw [zero_add] at hmp
    have hint : Integrable (fun z : PSpace P => ‖(F : PSpace P → SpaceC) z‖ ^ 2) volume := by
      have h2 := (Lp.memLp F).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
      simpa [Real.rpow_two] using h2
    have hg : AEStronglyMeasurable (fun z : PSpace P => ‖(F : PSpace P → SpaceC) z‖ ^ 2) volume :=
      (hF.norm).pow 2
    exact (hmp.integrable_comp hg).mpr hint

end UnforcedLeray.Short.PartIIIb.NearInst
