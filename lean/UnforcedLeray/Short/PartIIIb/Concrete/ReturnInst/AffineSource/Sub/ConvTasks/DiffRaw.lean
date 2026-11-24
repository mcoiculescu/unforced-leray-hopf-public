import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Cons.C03Background.RawLift

/-!
# `rawProfile` is differentiable on `s > 0` (`PartIII-b:C/asrc/ra/9/2/2/4`, source 2075-2077)

`rawProfile ε v ψ (s, x) = v(s, x) + (ε · raisedStream ψ s x) e_1`, with
`raisedStream ψ s x = ψ - (η ∂_η ψ + 2 s ∂_s ψ)`.  The velocity `v` is jointly smooth on `s ≥ 0`
(`IsTrain.smooth_v`), and the stream `ψ` is jointly smooth on `s > 0` (`BgRegime.train_stream_smooth`).
The one-variable partial derivatives of a jointly `C²` function are jointly differentiable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `s`-derivative along the chart line `t ↦ (t, x)` is jointly differentiable. -/
theorem raw_diff_s {G : Chart → ℝ} {p0 : Chart} (hG : ContDiffAt ℝ 2 G p0) :
    DifferentiableAt ℝ (fun p : Chart => deriv (fun t => G (t, p.2)) p.1) p0 := by
  have hev : ∀ᶠ p in 𝓝 p0, ContDiffAt ℝ 2 G p := hG.eventually (by simp)
  have hfd : ContDiffAt ℝ 1 (fun p => fderiv ℝ G p) p0 := hG.fderiv_right (m := 1) (by norm_num)
  have hH : DifferentiableAt ℝ (fun p : Chart => fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ))) p0 :=
    (hfd.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  refine hH.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  have hd1 : HasDerivAt (fun t : ℝ => (t, p.2)) ((1 : ℝ), (0 : ℝ × ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hG' : HasFDerivAt G (fderiv ℝ G p) p := (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hc := hG'.comp_hasDerivAt p.1 hd1
  have hd : deriv (fun t => G (t, p.2)) p.1 = fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ)) := hc.deriv
  first | exact hd.symm | exact hd

/-- The `η`-derivative along the chart line `t ↦ (s, (ξ, t))` is jointly differentiable. -/
theorem raw_diff_eta {G : Chart → ℝ} {p0 : Chart} (hG : ContDiffAt ℝ 2 G p0) :
    DifferentiableAt ℝ (fun p : Chart => deriv (fun t => G (p.1, (p.2.1, t))) p.2.2) p0 := by
  have hev : ∀ᶠ p in 𝓝 p0, ContDiffAt ℝ 2 G p := hG.eventually (by simp)
  have hfd : ContDiffAt ℝ 1 (fun p => fderiv ℝ G p) p0 := hG.fderiv_right (m := 1) (by norm_num)
  have hH : DifferentiableAt ℝ
      (fun p : Chart => fderiv ℝ G p ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) p0 :=
    (hfd.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  refine hH.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  have hd1 : HasDerivAt (fun t : ℝ => (p.1, (p.2.1, t)))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) p.2.2 :=
    (hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id' p.2.2))
  have hG' : HasFDerivAt G (fderiv ℝ G p) p := (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hc := hG'.comp_hasDerivAt p.2.2 hd1
  have hd : deriv (fun t => G (p.1, (p.2.1, t))) p.2.2 =
      fderiv ℝ G p ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := hc.deriv
  first | exact hd.symm | exact hd

/-- **Differentiability of the raw profile on `s > 0`** (source 2075-2077, 270-288). -/
theorem convDiffRaw : ConvDiffRaw := by
  intro dm dp hdm p d hreg s hs x
  have hopen : (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∈ 𝓝 (s, x) :=
    IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ) ⟨hs, mem_univ _⟩
  have hψ : ContDiffAt ℝ 2 (fun q : Chart => p.train.ψ q.1 q.2) (s, x) :=
    ((hreg.train_stream_smooth).contDiffAt hopen).of_le (by norm_num)
  have hvs : ContDiffOn ℝ ∞ (fun q : Chart => p.train.v q.1 q.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    p.train.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hv : ContDiffAt ℝ 2 (fun q : Chart => p.train.v q.1 q.2) (s, x) :=
    (hvs.contDiffAt hopen).of_le (by norm_num)
  have hEta := raw_diff_eta hψ
  have hS := raw_diff_s hψ
  have hGd : DifferentiableAt ℝ (fun q : Chart => p.train.ψ q.1 q.2) (s, x) :=
    hψ.differentiableAt (by norm_num)
  have hHd : DifferentiableAt ℝ (fun q : Chart =>
      p.train.ψ q.1 q.2 - (q.2.2 * deriv (fun t => p.train.ψ q.1 (q.2.1, t)) q.2.2 +
        2 * q.1 * deriv (fun t => p.train.ψ t q.2) q.1)) (s, x) := by
    have hη : DifferentiableAt ℝ (fun q : Chart => q.2.2) (s, x) := by fun_prop
    have h1 : DifferentiableAt ℝ (fun q : Chart => q.1) (s, x) := by fun_prop
    exact hGd.sub ((hη.mul hEta).add ((h1.const_mul 2).mul hS))
  have hvd : DifferentiableAt ℝ (fun q : Chart => p.train.v q.1 q.2) (s, x) :=
    hv.differentiableAt (by norm_num)
  have hf := hvd.add ((hHd.const_mul p.ε).smul (differentiableAt_const
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))))
  exact hf

end UnforcedLeray.Short.PartIIIb.Concrete
