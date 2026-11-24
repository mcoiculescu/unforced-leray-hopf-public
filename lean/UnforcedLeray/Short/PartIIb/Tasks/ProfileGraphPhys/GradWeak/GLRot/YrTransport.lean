import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2

/-!
# `PartII-b:T10/7/1/1/2/5`: `gl_yrTransport` (`Y_r` is stable under the transport `trF T`)

Source of record: `the November 2 reference manuscript` lines 1912-1921 (chart 1639-1668).
Mathematics: `x ↦ (x.1, T x.2)` is measure preserving, so the periodicity and measurability of
`f` transfer almost everywhere; `cApp S` is continuous and norm preserving on `ℂ³`, so the
phase-normalized `L^r` norm of `trF T f` is that of `f` slice by slice (the slices are moved by
the measure-preserving `T`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- `cApp S` is continuous. -/
theorem cApp_continuous' (S : Space ≃ₗᵢ[ℝ] Space) : Continuous (cApp S) := by
  unfold cApp
  have hre : Continuous (fun v : CVec3 => reS v) := by
    unfold reS
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => Complex.continuous_re.comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_id))
  have him : Continuous (fun v : CVec3 => imS v) := by
    unfold imS
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => Complex.continuous_im.comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_id))
  have hr : Continuous (fun x : Space => B0412.realC x) := by
    unfold B0412.realC
    fun_prop
  have h1 : Continuous fun v : CVec3 => B0412.realC (S (reS v)) := hr.comp (S.continuous.comp hre)
  have h2 : Continuous fun v : CVec3 => B0412.realC (S (imS v)) := hr.comp (S.continuous.comp him)
  exact h1.add (h2.const_smul Complex.I)

/-- `cApp S` preserves the Euclidean norm of `ℂ³`. -/
theorem cApp_norm' (S : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : ‖cApp S v‖ = ‖v‖ := by
  have hsq : ∀ w : CVec3, ‖w‖ ^ 2 = ‖reS w‖ ^ 2 + ‖imS w‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [reS, imS, Real.norm_eq_abs, sq_abs]
    ring
  have hre : reS (cApp S v) = S (reS v) := by
    ext i
    simp [reS, cApp, B0412.realC_apply]
  have him : imS (cApp S v) = S (imS v) := by
    ext i
    simp [imS, cApp, B0412.realC_apply]
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
  rw [hsq (cApp S v), hre, him, S.norm_map, S.norm_map, ← hsq v]

/-- The map `x ↦ (x.1, T x.2)` is measure preserving on `ℝ × ℝ³`. -/
theorem slice_measurePreserving (T : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (fun x : ℝ × Space => (x.1, T x.2)) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod (T.measurePreserving)
  rw [← Measure.volume_eq_prod] at h
  exact h

theorem gl_yrTransport : UnforcedLeray.Short.IIb.GLYrTransport := by
  intro P r T f hf
  have hqmp := (slice_measurePreserving T).quasiMeasurePreserving
  have hnorm : ∀ v : CVec3, ‖cApp T.symm v‖ₑ = ‖v‖ₑ := by
    intro v
    rw [← ofReal_norm, ← ofReal_norm, cApp_norm']
  have hemb : MeasurableEmbedding (T : Space → Space) := T.toHomeomorph.measurableEmbedding
  have hint : ∀ t : ℝ, ∫⁻ y, ‖trF T f (t, y)‖ₑ ^ r = ∫⁻ y, ‖f (t, y)‖ₑ ^ r := by
    intro t
    calc ∫⁻ y, ‖trF T f (t, y)‖ₑ ^ r = ∫⁻ y, ‖f (t, T y)‖ₑ ^ r := by
          refine lintegral_congr fun y => ?_
          show ‖cApp T.symm (f (t, T y))‖ₑ ^ r = _
          rw [hnorm]
      _ = ∫⁻ y, ‖f (t, y)‖ₑ ^ r :=
          (T.measurePreserving).lintegral_comp_emb hemb (fun y => ‖f (t, y)‖ₑ ^ r)
  have hn : phaseLpNorm P r (trF T f) = phaseLpNorm P r f := by
    unfold phaseLpNorm
    simp only [hint]
  refine ⟨?_, ?_, ?_⟩
  · have h := hqmp.ae hf.periodic
    filter_upwards [h] with x hx
    show cApp T.symm (f (x.1 + P, T x.2)) = cApp T.symm (f (x.1, T x.2))
    rw [hx]
  · have hm : AEStronglyMeasurable (fun x : ℝ × Space => f (x.1, T x.2)) volume :=
      hf.meas.comp_quasiMeasurePreserving hqmp
    exact (cApp_continuous' T.symm).comp_aestronglyMeasurable hm
  · rw [hn]
    exact hf.finite

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_yrTransport
