import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared

/-!
# `MollConvJet` (task `PartIII-a:T21/2/7/2/1/1/5/18/1/3`)

Convolution with a smooth compactly supported kernel of an `X_{-m,c}`-continuous family is
in `C((a, b); H^∞_{-m,c})`. Source: SP lines 3060-3071.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The iterated partials `pdWordR w K` of a smooth compactly supported kernel that vanishes
outside the closed unit ball are smooth, compactly supported, and vanish outside the unit ball. -/
theorem pdWordR_props (K : ℝ × ℝ → ℝ) (hK : ContDiff ℝ ∞ K) (hKs : HasCompactSupport K)
    (hK1 : ∀ y : ℝ × ℝ, 1 < ‖y‖ → K y = 0) (w : List (Fin 2)) :
    ContDiff ℝ ∞ (pdWordR w K) ∧ HasCompactSupport (pdWordR w K) ∧
      ∀ y : ℝ × ℝ, 1 < ‖y‖ → pdWordR w K y = 0 := by
  induction w with
  | nil => exact ⟨hK, hKs, hK1⟩
  | cons j w ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · exact B0579.contDiff_pd h1 j
    · have hpd : B0579.pd j (pdWordR w K) =
          fun x => fderiv ℝ (pdWordR w K) x (B0579.dir j) := rfl
      show HasCompactSupport (B0579.pd j (pdWordR w K))
      rw [hpd]
      exact h2.fderiv_apply ℝ (B0579.dir j)
    · intro y hy
      show B0579.pd j (pdWordR w K) y = 0
      have hopen : IsOpen {z : ℝ × ℝ | 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
      have hev : pdWordR w K =ᶠ[𝓝 y] (fun _ : ℝ × ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hy) (fun z hz => h3 z hz)
      unfold B0579.pd
      rw [hev.fderiv_eq]
      simp

/-- Convolution integrand is integrable: a continuous compactly supported kernel against a
locally integrable field. -/
theorem cellConv_integrable (K : ℝ × ℝ → ℝ) (hK : Continuous K) (hKs : HasCompactSupport K)
    (g : ℝ × ℝ → ℂ) (hg : LocallyIntegrable g volume) (x : ℝ × ℝ) :
    Integrable (fun y => K y • g (x - y)) volume := by
  have h := (hKs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hK hg) x
  have h2 := h.integrable
  simpa [ContinuousLinearMap.lsmul_apply] using h2

/-- Linearity of `cellConv` in the field, pointwise. -/
theorem cellConv_sub_apply (K : ℝ × ℝ → ℝ) (hK : Continuous K) (hKs : HasCompactSupport K)
    (g h : ℝ × ℝ → ℂ) (hg : LocallyIntegrable g volume) (hh : LocallyIntegrable h volume)
    (x : ℝ × ℝ) : cellConv K (g - h) x = cellConv K g x - cellConv K h x := by
  unfold cellConv
  simp only [Pi.sub_apply, smul_sub]
  exact integral_sub (cellConv_integrable K hK hKs g hg x) (cellConv_integrable K hK hKs h hh x)

theorem mollConvJet (hS : UnforcedLeray.Short.IIIa.SmoothCellJet)
    (hD : UnforcedLeray.Short.IIIa.CellConvDeriv) (hB : UnforcedLeray.Short.IIIa.CellConvBound)
    (hL : UnforcedLeray.Short.IIIa.CellPeriodicLocInt) :
    UnforcedLeray.Short.IIIa.MollConvJet := by
  intro c m K f a b hc hK hKs hK1 hX
  obtain ⟨C, hC0, hBC⟩ := hB c m hc
  refine ⟨fun r hr k => ?_, fun w r hr => ?_⟩
  · -- every slice is a cell jet of every order
    obtain ⟨hperr, hmemr⟩ := hX.1 r hr
    obtain ⟨hF, hper', hadj⟩ := hD c m K (f r) hc hK hKs hperr hmemr
    have hmemw : ∀ w : List (Fin 2),
        MemLp (adjSpatial w (cellConv K (f r))) 2 (B0579.cellMeasure c (-m)) := by
      intro w
      obtain ⟨hK1c', hK1s', hK1z'⟩ := pdWordR_props K hK hKs hK1 w
      rw [hadj w]
      exact (hBC (pdWordR w K) (f r) hK1c'.continuous hK1z' hperr hmemr).1
    exact hS c m (cellConv K (f r)) hc hF hper' hmemw k
  · -- the derivative fields are continuous in X_{-m,c} on (a, b)
    obtain ⟨hK1c, hK1s, hK1z⟩ := pdWordR_props K hK hKs hK1 w
    have hlim : Tendsto (fun r' => ENNReal.ofReal (C * ∫ y, |pdWordR w K y|) *
        xNorm c (-m) (f r' - f r)) (𝓝[Ioo a b] r)
        (𝓝 (ENNReal.ofReal (C * ∫ y, |pdWordR w K y|) * 0)) :=
      ENNReal.Tendsto.const_mul (hX.2 r hr) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hlim
    have hbound : ∀ᶠ r' in 𝓝[Ioo a b] r,
        xNorm c (-m) (adjSpatial w (cellConv K (f r')) - adjSpatial w (cellConv K (f r))) ≤
          ENNReal.ofReal (C * ∫ y, |pdWordR w K y|) * xNorm c (-m) (f r' - f r) := by
      filter_upwards [eventually_mem_nhdsWithin] with r' hr'
      obtain ⟨hperr', hmemr'⟩ := hX.1 r' hr'
      obtain ⟨hperr, hmemr⟩ := hX.1 r hr
      have hL' := hL c m (f r') hc hperr' hmemr'
      have hL'' := hL c m (f r) hc hperr hmemr
      have hdiff : adjSpatial w (cellConv K (f r')) - adjSpatial w (cellConv K (f r)) =
          cellConv (pdWordR w K) (f r' - f r) := by
        rw [(hD c m K (f r') hc hK hKs hperr' hmemr').2.2 w,
          (hD c m K (f r) hc hK hKs hperr hmemr).2.2 w]
        funext x
        exact (cellConv_sub_apply (pdWordR w K) hK1c.continuous hK1s (f r') (f r)
          hL'.2 hL''.2 x).symm
      have hperdiff : ∀ x : ℝ × ℝ, (f r' - f r) (x.1 + c, x.2) = (f r' - f r) x := by
        intro x
        simp only [Pi.sub_apply, hperr' x, hperr x]
      have hmemdiff : MemLp (f r' - f r) 2 (B0579.cellMeasure c (-m)) :=
        hmemr'.sub hmemr
      rw [hdiff]
      exact (hBC (pdWordR w K) (f r' - f r) hK1c.continuous hK1z hperdiff hmemdiff).2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun _ => zero_le) hbound

end UnforcedLeray.Short.IIIa
