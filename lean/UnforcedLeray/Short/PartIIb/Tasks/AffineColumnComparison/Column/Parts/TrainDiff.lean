import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_8

/-!
# Part II-b, task `PartII-b:G4/3/8/1` (`TrainDiff`)

Source of record: `the November 2 reference manuscript` (SP), lines 397, 2049,
2347-2349. The train velocity `v = p.train.v` is jointly smooth on `[0, ∞) × ℝ²`
(`IsTrain.smooth_v`), and the stream `ψ` is jointly smooth on `(0, ∞) × ℝ²`
(`BgRegime.train_stream_smooth`). Hence `trainProf p` (the velocity) and `raisedMerid p`
(the raised stream times `e_z`) are differentiable at every point with `0 < s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- Partial derivative in `η` of a function on the chart space is a directional fderiv. -/
theorem deriv_eta_eq_fderiv {Φ : ℝ × (ℝ × ℝ) → ℝ} (y : ℝ × (ℝ × ℝ))
    (hΦ : DifferentiableAt ℝ Φ y) :
    deriv (fun t : ℝ => Φ (y.1, (y.2.1, t))) y.2.2 = fderiv ℝ Φ y (0, (0, 1)) := by
  have hγ : HasDerivAt (fun t : ℝ => ((y.1, (y.2.1, t)) : ℝ × (ℝ × ℝ))) (0, (0, 1)) y.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  exact (hΦ.hasFDerivAt.comp_hasDerivAt y.2.2 hγ).deriv

/-- Partial derivative in `s` of a function on the chart space is a directional fderiv. -/
theorem deriv_s_eq_fderiv {Φ : ℝ × (ℝ × ℝ) → ℝ} (y : ℝ × (ℝ × ℝ))
    (hΦ : DifferentiableAt ℝ Φ y) :
    deriv (fun t : ℝ => Φ (t, (y.2.1, y.2.2))) y.1 = fderiv ℝ Φ y (1, (0, 0)) := by
  have hγ : HasDerivAt (fun t : ℝ => ((t, (y.2.1, y.2.2)) : ℝ × (ℝ × ℝ))) (1, (0, 0)) y.1 :=
    (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
  exact (hΦ.hasFDerivAt.comp_hasDerivAt y.1 hγ).deriv

/-- **Joint differentiability of the train and the raised stream on `s > 0`** (SP 397, 2049). -/
theorem trainDiff : TrainDiff := by
  intro p d dm dp hreg x hx
  -- the train velocity is jointly smooth on `[0, ∞) × ℝ²`, hence near `x` (where `0 < s`)
  have hvC : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => p.train.v y.1 y.2) (Ici 0 ×ˢ univ) :=
    p.train.isTrain.smooth_v
  have hUv : Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 x :=
    prod_mem_nhds (Ioi_mem_nhds hx) univ_mem
  have hv : ContDiffAt ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => p.train.v y.1 y.2) x :=
    hvC.contDiffAt (Filter.mem_of_superset hUv (prod_mono Ioi_subset_Ici_self subset_rfl))
  have hT : DifferentiableAt ℝ (trainProf p) x := hv.differentiableAt (by simp)
  -- the stream is jointly smooth on the open set `(0, ∞) × ℝ²`
  have hΦ : ∀ y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)),
      ContDiffAt ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) y := fun y hy =>
    hreg.train_stream_smooth.contDiffAt (prod_mem_nhds (Ioi_mem_nhds hy.1) univ_mem)
  have hψ : ContDiffAt ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) x :=
    hΦ x ⟨hx, mem_univ _⟩
  have hU : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 x :=
    prod_mem_nhds (Ioi_mem_nhds hx) univ_mem
  -- the two partial derivatives of `ψ` are directional fderivs, hence differentiable at `x`
  have hDs : DifferentiableAt ℝ
      (fun y : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) y (1, (0, 0)))
      x :=
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hDe : DifferentiableAt ℝ
      (fun y : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) y (0, (0, 1)))
      x :=
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
  have eS : (fun y : ℝ × (ℝ × ℝ) => deriv (fun t : ℝ => p.train.ψ t (y.2.1, y.2.2)) y.1) =ᶠ[𝓝 x]
      (fun y : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) y (1, (0, 0))) := by
    filter_upwards [hU] with y hy
    exact deriv_s_eq_fderiv (Φ := fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) y
      ((hΦ y hy).differentiableAt (by simp))
  have eE : (fun y : ℝ × (ℝ × ℝ) => deriv (fun t : ℝ => p.train.ψ y.1 (y.2.1, t)) y.2.2) =ᶠ[𝓝 x]
      (fun y : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) y (0, (0, 1))) := by
    filter_upwards [hU] with y hy
    exact deriv_eta_eq_fderiv (Φ := fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) y
      ((hΦ y hy).differentiableAt (by simp))
  have hDs' := hDs.congr_of_eventuallyEq eS
  have hDe' := hDe.congr_of_eventuallyEq eE
  have hR : DifferentiableAt ℝ (raisedProf p) x := by
    have hψx : DifferentiableAt ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) x :=
      hψ.differentiableAt (by simp)
    have h1 : DifferentiableAt ℝ (fun y : ℝ × (ℝ × ℝ) => y.2.2) x := by fun_prop
    have h2 : DifferentiableAt ℝ (fun y : ℝ × (ℝ × ℝ) => 2 * y.1) x := by fun_prop
    have hfun : DifferentiableAt ℝ (fun y : ℝ × (ℝ × ℝ) =>
        p.train.ψ y.1 y.2 -
          (y.2.2 * deriv (fun t : ℝ => p.train.ψ y.1 (y.2.1, t)) y.2.2 +
            2 * y.1 * deriv (fun t : ℝ => p.train.ψ t (y.2.1, y.2.2)) y.1)) x :=
      hψx.sub ((h1.mul hDe').add (h2.mul hDs'))
    exact hfun
  -- `raisedMerid p = raisedProf p • e_z`
  have hM : DifferentiableAt ℝ (raisedMerid p) x := hR.smul_const Axi.m1
  exact ⟨hT, hM⟩

end UnforcedLeray.Short.IIb

end
