import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.Cont
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvGInt

/-!
# Proof of `FcvTriMeas` (source 4610)

On the triangle `T = {0 < t < ρ ≤ s}` the map `(t,ρ) ↦ t^μ ℓ_ρ(𝒰(ρ,t) g_B(t))` is continuous, hence
a.e.-strongly measurable.  Two inputs:
* `(t,ρ) ↦ 𝒰(ρ,t) g_B(t)` is continuous on `T` into `X_{m,c}` (`jointCont` for the datum fixed,
  `locBdd` for the operator norms, continuity of `g_B` on `(0,∞)`);
* `ρ ↦ ℓ_ρ(ω)` is continuous for fixed `ω` (`fcvEllFixed`) and `|ℓ_ρ ω| ≤ C ‖ω‖` locally uniformly
  in `ρ` (`fcvEllUnif`), so `ℓ_ρ(V p)` is continuous at `p₀` in `T` (split off `ℓ_ρ(V p₀)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem fcvTriMeas : FcvTriMeas := by
  intro κ ν c m _ _ tr D μ as χf A hν hμ hχ hA φ hφ s hs
  have hBc : ContinuousOn (Bmat ν μ χf A) (Ioi 0) := bmat_continuousOn hχ hA
  have hG : ContinuousOn (fun t => gBD D (Bmat ν μ χf A) t) (Ioi 0) :=
    gBD_continuousOn D hBc
  have hpc : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ))) (Ioi 0) := by
    refine ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn ?_
    intro t ht
    exact Or.inl (by simpa using ht)
  obtain ⟨C, hC⟩ := D.ev.locBdd s
  obtain ⟨CE, hCE⟩ := (fcvEllUnif : FcvEllUnif) ν c m tr φ hφ s
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ s} with hT
  have hTm : MeasurableSet T := by
    have a1 : MeasurableSet {p : ℝ × ℝ | 0 < p.1} :=
      measurableSet_lt measurable_const measurable_fst
    have a2 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
      measurableSet_lt measurable_fst measurable_snd
    have a3 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ s} :=
      measurableSet_le measurable_snd measurable_const
    exact a1.inter (a2.inter a3)
  have hcontT : ∀ p0 ∈ T, ContinuousWithinAt
      (fun p : ℝ × ℝ => ((p.1 : ℂ) ^ (μ : ℂ)) *
        ellFn tr φ p.2 (D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p.1))) T p0 := by
    intro p0 hp0
    obtain ⟨h1, h2, h3⟩ := hp0
    have hρ0 : 0 < p0.2 := by linarith
    -- continuity of the datum-dependent operator family on `T`
    have hg0 : ContinuousWithinAt (fun p : ℝ × ℝ => gBD D (Bmat ν μ χf A) p.1) T p0 :=
      (hG p0.1 h1).comp continuous_fst.continuousWithinAt (fun p hp => hp.1)
    have hjc : ContinuousWithinAt
        (fun q : ℝ × ℝ => D.ev.U q.1 q.2 (gBD D (Bmat ν μ χf A) p0.1))
        {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1} (p0.2, p0.1) :=
      D.ev.jointCont (gBD D (Bmat ν μ χf A) p0.1) (p0.2, p0.1) ⟨h1.le, h2.le⟩
    have hq' : Tendsto (fun p : ℝ × ℝ => ((p.2, p.1) : ℝ × ℝ)) (𝓝[T] p0)
        (𝓝[{q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1}] (p0.2, p0.1)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_snd.prodMk continuous_fst).tendsto p0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with p hp
        exact ⟨hp.1.le, hp.2.1.le⟩
    have hx : ContinuousWithinAt
        (fun p : ℝ × ℝ => D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p0.1)) T p0 :=
      Tendsto.comp hjc hq'
    have hVt : ContinuousWithinAt
        (fun p : ℝ × ℝ => D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p.1)) T p0 := by
      rw [ContinuousWithinAt]
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have h1' : Tendsto (fun p : ℝ × ℝ =>
          C * ‖gBD D (Bmat ν μ χf A) p.1 - gBD D (Bmat ν μ χf A) p0.1‖) (𝓝[T] p0) (𝓝 0) := by
        have := (tendsto_iff_norm_sub_tendsto_zero.1 hg0.tendsto).const_mul C
        rw [mul_zero] at this
        exact this
      have h2' : Tendsto (fun p : ℝ × ℝ =>
          ‖D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p0.1) -
            D.ev.U p0.2 p0.1 (gBD D (Bmat ν μ χf A) p0.1)‖) (𝓝[T] p0) (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 hx
      have h3' := h1'.add h2'
      rw [add_zero] at h3'
      refine squeeze_zero' (Eventually.of_forall fun p => norm_nonneg _) ?_ h3'
      filter_upwards [self_mem_nhdsWithin] with p hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      have hUt : ‖D.ev.U p.2 p.1‖ ≤ C := hC p.2 p.1 hp1.le hp2.le hp3
      have e : D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p.1) -
          D.ev.U p0.2 p0.1 (gBD D (Bmat ν μ χf A) p0.1) =
          D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p.1 - gBD D (Bmat ν μ χf A) p0.1) +
            (D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p0.1) -
              D.ev.U p0.2 p0.1 (gBD D (Bmat ν μ χf A) p0.1)) := by
        rw [map_sub]; abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine ((D.ev.U p.2 p.1).le_opNorm _).trans ?_
      exact mul_le_mul_of_nonneg_right hUt (norm_nonneg _)
    -- the flow term: `ℓ_ρ(V p) = ℓ_ρ(V p - V p₀) + ℓ_ρ(V p₀)`
    have hVn := tendsto_iff_norm_sub_tendsto_zero.1 hVt
    have hBlim : Tendsto (fun p : ℝ × ℝ =>
        ellFn tr φ p.2 (D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p.1) -
          D.ev.U p0.2 p0.1 (gBD D (Bmat ν μ χf A) p0.1))) (𝓝[T] p0) (𝓝 0) := by
      have h5 := hVn.const_mul CE
      rw [mul_zero] at h5
      refine squeeze_zero_norm' ?_ h5
      filter_upwards [self_mem_nhdsWithin] with p hp
      obtain ⟨hp1, hp2', hp3⟩ := hp
      have hpos : 0 < p.2 := by linarith
      exact hCE p.2 hpos hp3 _
    have hA : ContinuousWithinAt (fun p : ℝ × ℝ =>
        ellFn tr φ p.2 (D.ev.U p0.2 p0.1 (gBD D (Bmat ν μ χf A) p0.1))) T p0 :=
      ((fcvEllFixed : FcvEllFixed) ν c m tr φ hφ
          (D.ev.U p0.2 p0.1 (gBD D (Bmat ν μ χf A) p0.1)) p0.2 hρ0).comp
        continuous_snd.continuousWithinAt
        (fun p hp => (show (0 : ℝ) < p.2 by linarith [hp.1, hp.2.1]))
    have hsum := hBlim.add hA.tendsto
    rw [zero_add] at hsum
    have hE : ContinuousWithinAt (fun p : ℝ × ℝ =>
        ellFn tr φ p.2 (D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p.1))) T p0 := by
      rw [ContinuousWithinAt]
      refine Tendsto.congr' ?_ hsum
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hpos : 0 < p.2 := by linarith [hp.1, hp.2.1]
      rw [fcvc_sub tr φ hφ p.2 hpos _ _]
      ring
    have hP : ContinuousWithinAt (fun p : ℝ × ℝ => ((p.1 : ℂ)) ^ (μ : ℂ)) T p0 :=
      (hpc p0.1 h1).comp continuous_fst.continuousWithinAt (fun p hp => hp.1)
    exact hP.mul hE
  exact ContinuousOn.aestronglyMeasurable (fun p hp => hcontT p hp) hTm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.fcvTriMeas
