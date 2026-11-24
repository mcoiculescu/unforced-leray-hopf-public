import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.ChartSectionEq
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.ChartCompAesm
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.PsiQMP
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm

/-!
# Part II-b, task `PartII-b:T10/2/2` (`ProfilePosPeriodic`)

Source: `the November 2 reference manuscript`, lines 1902-1906.

No measurable representative of `b` is needed.  `NvC b` periodic gives, a.e. in `(τ, y)`,
`b(chart(τ+P,y)) = b(chart(τ,y))` (`sum_nvC`).  Translating in `τ` by `jP` (`chart = qShift (jc)`)
the bad sets `N_j` are null.  The section `Ψ` (`PsiQMP`, `ChartSectionEq`) pulls them back: the set
`W_j` of half-cell points `w` with `b(qShift((j+1)c) w) ≠ b(qShift(jc) w)` is `hMeas`-null, hence
Lebesgue-null; the bad set of the target lies in `⋃_j qShift(-jc)⁻¹ W_j`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

lemma ppp_chart_shift_int {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R) (k : ℤ) (τ : ℝ)
    (y : Space) :
    Axi.chart R (τ + (k : ℝ) * P) y = qShift ((k : ℝ) * c) (Axi.chart R τ y) := by
  have : R * ((k : ℝ) * P) / 2 = (k : ℝ) * c := by rw [hP]; field_simp
  simp only [Axi.chart, Axi.phase, qShift]
  congr 2
  linarith [this, show R * (τ + (k : ℝ) * P) / 2 = R * τ / 2 + R * ((k : ℝ) * P) / 2 by ring]

theorem profilePosPeriodic_proof : UnforcedLeray.Short.IIb.ProfilePosPeriodic := by
  intro c ε r b hc hε hr hY
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hR0 : ε⁻¹ ≠ 0 := hR.ne'
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  have hax : ∀ᵐ x : ℝ × Space, x.2 ∉ Axi.axis :=
    (Measure.quasiMeasurePreserving_snd).ae Axi.ae_not_mem_axis
  -- (1) a.e. periodicity of `b ∘ chart` in the phase time
  have hHper : ∀ᵐ x : ℝ × Space,
      b (Axi.chart ε⁻¹ (x.1 + 2 * ε * c) x.2) = b (Axi.chart ε⁻¹ x.1 x.2) := by
    filter_upwards [hY.periodic, hax] with x hx hxax
    have hpos : 0 < Axi.age ε⁻¹ x.2 := Axi.age_pos hR0 hxax
    have hne : (Real.sqrt (Axi.age ε⁻¹ x.2) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne'
    ext i
    have h1 := sum_nvC ε⁻¹ hR b (x.1 + 2 * ε * c, x.2) hxax i
    have h2 := sum_nvC ε⁻¹ hR b x hxax i
    simp only at h1
    rw [hx] at h1
    exact mul_left_cancel₀ hne (h1.symm.trans h2)
  -- (2) null sets `N_j` of failures along the shifted phase
  have hN : ∀ j : ℤ, volume {x : ℝ × Space | ¬ (b (Axi.chart ε⁻¹
      (x.1 + ((j + 1 : ℤ) : ℝ) * (2 * ε * c)) x.2) =
        b (Axi.chart ε⁻¹ (x.1 + (j : ℝ) * (2 * ε * c)) x.2))} = 0 := by
    intro j
    have hmp : MeasurePreserving (fun x : ℝ × Space => (x.1 + (j : ℝ) * (2 * ε * c), x.2))
        ((volume : Measure ℝ).prod (volume : Measure Space))
        ((volume : Measure ℝ).prod (volume : Measure Space)) :=
      (measurePreserving_add_right (volume : Measure ℝ) ((j : ℝ) * (2 * ε * c))).prod
        (MeasurePreserving.id (volume : Measure Space))
    have h := hmp.quasiMeasurePreserving.ae hHper
    refine ae_iff.1 ?_
    filter_upwards [h] with x hx
    have hx' : b (Axi.chart ε⁻¹ (x.1 + (j : ℝ) * (2 * ε * c) + 2 * ε * c) x.2) =
        b (Axi.chart ε⁻¹ (x.1 + (j : ℝ) * (2 * ε * c)) x.2) := hx
    have e : x.1 + ((j + 1 : ℤ) : ℝ) * (2 * ε * c) = x.1 + (j : ℝ) * (2 * ε * c) + 2 * ε * c := by
      push_cast; ring
    rw [e]
    exact hx'
  -- (3) the bad sets on the half cell
  set ν : Measure ℝ := volume.restrict (Ioo 0 (2 * Real.pi)) with hν
  have hQ := psiQMP_proof c r ε⁻¹ hR hc
  have hW : ∀ j : ℤ, volume ({w : Coord | w ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c ∧
      ¬ (b (qShift (((j + 1 : ℤ) : ℝ) * c) w) = b (qShift ((j : ℝ) * c) w))} ∩
        (Ioi (0 : ℝ) ×ˢ Axi.qCell c)) = 0 := by
    intro j
    set W : Set Coord := {w : Coord | w ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c ∧
      ¬ (b (qShift (((j + 1 : ℤ) : ℝ) * c) w) = b (qShift ((j : ℝ) * c) w))} with hWdef
    have hpre := hQ.preimage_null (hN j)
    have hsub : W ×ˢ Ioo (0 : ℝ) (2 * Real.pi) ⊆
        (fun p : Coord × ℝ => (psiTau ε⁻¹ p.1, psiSpace ε⁻¹ p.1 p.2)) ⁻¹'
          {x : ℝ × Space | ¬ (b (Axi.chart ε⁻¹
            (x.1 + ((j + 1 : ℤ) : ℝ) * (2 * ε * c)) x.2) =
              b (Axi.chart ε⁻¹ (x.1 + (j : ℝ) * (2 * ε * c)) x.2))} := by
      rintro ⟨w, θ⟩ ⟨⟨hw1, hw2⟩, _⟩
      have hpos : 0 < w.1 := hw1.1
      have hsec := chartSectionEq_proof ε⁻¹ w θ hR hpos
      simp only [mem_preimage, mem_setOf_eq]
      rw [hP, ppp_chart_shift_int hR0 rfl, ppp_chart_shift_int hR0 rfl, hsec]
      exact hw2
    have h0 : ((hMeas c r).prod ν) (W ×ˢ Ioo (0 : ℝ) (2 * Real.pi)) = 0 :=
      measure_mono_null hsub hpre
    haveI hs : SFinite (hMeas c r) := by
      unfold hMeas Axi.ageμ
      haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by unfold UnforcedLeray.Cyl.avgμ; infer_instance
      infer_instance
    have hfin : IsFiniteMeasure ν := ⟨by
      rw [hν, Measure.restrict_apply_univ]
      simp [ENNReal.mul_lt_top]⟩
    rw [Measure.prod_prod] at h0
    have hν0 : ν (Ioo (0 : ℝ) (2 * Real.pi)) ≠ 0 := by
      rw [hν, Measure.restrict_apply measurableSet_Ioo, inter_self, Real.volume_Ioo]
      simp [Real.pi_pos]
    have hWn : hMeas c r W = 0 := (mul_eq_zero.1 h0).resolve_right hν0
    have := NvCNorm.volume_null_of_ageμ_null hc (a := r / 2 - 5 / 2) (N := W) hWn
    exact this
  -- (4) assemble
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  rw [ae_iff, Measure.restrict_apply' hS]
  refine measure_mono_null ?_ (measure_iUnion_null fun j : ℤ => ?_ :
    volume (⋃ j : ℤ, qShift (-(j : ℝ) * c) ⁻¹' {w : Coord | w ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c ∧
      ¬ (b (qShift (((j + 1 : ℤ) : ℝ) * c) w) = b (qShift ((j : ℝ) * c) w))}) = 0)
  · rintro z ⟨hz, hzS⟩
    obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, Axi.cellRep c z.2.1 = z.2.1 + (k₀ : ℝ) * c :=
      ⟨-⌊(z.2.1 + c / 2) / c⌋, by unfold Axi.cellRep; push_cast; ring⟩
    rw [mem_iUnion]
    refine ⟨-k₀, ?_⟩
    have hw : qShift (-((-k₀ : ℤ) : ℝ) * c) z = (z.1, (Axi.cellRep c z.2.1, z.2.2)) := by
      simp only [qShift, hk₀]
      push_cast
      ext <;> simp
    have hz' : z = qShift (((-k₀ : ℤ) : ℝ) * c) (qShift (-((-k₀ : ℤ) : ℝ) * c) z) := by
      rw [qShift_qShift]; simp [qShift_zero]
    refine ⟨?_, ?_⟩
    · rw [hw]
      exact Set.mk_mem_prod hzS.1 (periodicRep_mem_qCell hc z.2.1 z.2.2)
    · show ¬ _
      intro hcon
      apply hz
      have e1 : qShift (((-k₀ + 1 : ℤ) : ℝ) * c) (qShift (-((-k₀ : ℤ) : ℝ) * c) z) =
          qShift c z := by
        rw [qShift_qShift]
        congr 1
        push_cast; ring_nf
      rw [e1, ← hz'] at hcon
      exact hcon
  · have h0 := hW j
    rw [inter_eq_left.2 (fun w hw => hw.1)] at h0
    exact (measurePreserving_qShift (-(j : ℝ) * c)).quasiMeasurePreserving.preimage_null h0

end UnforcedLeray.Short.IIb
