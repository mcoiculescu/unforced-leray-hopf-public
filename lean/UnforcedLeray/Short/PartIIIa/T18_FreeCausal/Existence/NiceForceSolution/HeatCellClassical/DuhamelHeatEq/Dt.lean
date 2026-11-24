import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3_1

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3/1` (leaf A): `w_s = ∫_{r>0} A(r) dr`

Target: `duhEqDt : DuhEqDt`. Source: `the November 2 reference manuscript`,
lines 3427-3440. Proof: `duhamelHeat ν h = duhFd ν h` (Fubini), `duhFd` is differentiable with
directional derivative `duhFd ν (∂_t h)` (`Sub/PartIII-a_T18_2_4_1_3_1.lean`), and the slice
integrals of `∂_t h` are `duhDt`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem duhEqDt_deriv {h : ℝ × (ℝ × ℝ) → ℂ} (hh : ContDiff ℝ ∞ h) (t : ℝ) (y : ℝ × ℝ) :
    deriv (fun t' : ℝ => h (t', y)) t = duhDir ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) h (t, y) := by
  have h1 : HasDerivAt (fun t' : ℝ => ((t', y) : ℝ × (ℝ × ℝ))) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have h2 := ((hh.differentiable (by simp)) (t, y)).hasFDerivAt.comp_hasDerivAt t h1
  exact h2.deriv

theorem duhEqDt_slice (ν : ℝ) {h : ℝ × (ℝ × ℝ) → ℂ} (hh : ContDiff ℝ ∞ h) (s : ℝ) (x : ℝ × ℝ)
    (r : ℝ) : duhDt ν h s x r = ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        duhDir ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) h (s - r, (x.1 - z.1, x.2 - z.2)) := by
  unfold duhDt
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [duhEqDt_deriv hh]

theorem duhEqDt : UnforcedLeray.Short.IIIa.DuhEqDt := by
  intro c ν h hc hν hn s x
  have hD := duhDir_nice hn ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
  have hfun : (fun r => duhDt ν h s x r) = fun r => ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        duhDir ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) h (s - r, (x.1 - z.1, x.2 - z.2)) :=
    funext fun r => duhEqDt_slice ν hn.1 s x r
  rw [hfun]
  refine ⟨duhFd_slice_integrable hc hν hD s x, ?_⟩
  have hint : ∫ r in Ioi (0 : ℝ), ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        duhDir ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) h (s - r, (x.1 - z.1, x.2 - z.2))
      = duhamelHeat ν (duhDir ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) h) s x := rfl
  rw [hint, duhFd_eq hc hν hD (s, x)]
  have hW : ∀ s' : ℝ, duhamelHeat ν h s' x = duhFd ν h (s', x) := fun s' => duhFd_eq hc hν hn (s', x)
  have hfun2 : (fun s' => duhamelHeat ν h s' x) = fun s' => duhFd ν h (s', x) := funext hW
  rw [hfun2]
  have h1 : HasDerivAt (fun t' : ℝ => ((t', x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h2 := (duhFd_differentiable hc hν hn (s, x)).hasFDerivAt.comp_hasDerivAt s h1
  rw [duhFd_fderiv_apply hc hν hn (s, x) _] at h2
  exact h2

end UnforcedLeray.Short.IIIa
