import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2

/-!
# `RawProfileSmooth`: the raw profile is smooth for positive age (`PartIII-b:C/rep/8/2/1/2/1`)

Source `the November 2 reference manuscript`,
lines 1206-1222 (`v = ∇^⊥ψ`, `H = (1-K)ψ`, `K = η∂_η + 2s∂_s`), 270-288, 397, 2040, 2049, 2073-2077.

`b_raw = (v₁, v₂ + εH) = v + ε H e_z` with `H = ψ - η∂_ηψ - 2s∂_sψ`.  On the open set `{s > 0}`
the train velocity is `C^∞` (`IsTrain.smooth_v`, on `s ≥ 0`), and the stream
`Ψ(s, (q, η)) = ψ(s, (q, η))` is jointly `C^∞` there (the field `ReturnLevel.train_stream_smooth`,
source 397, 2049).  The one-variable derivatives in `H` are `DΨ(x)(0, (0, 1))` and `DΨ(x)(1, (0, 0))`.
Argument: as `bgRawProfileSmooth` (`Concrete/ReturnInst/Ward/Bg/YoungW2/RawProfileSmooth.lean`),
with `L.train_stream_smooth` in place of `BgRegime.train_stream_smooth`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`RawProfileSmooth`** (source 1206-1222, 397, 2049): the raw profile of every return level is
`C^∞` on `{s > 0}`. -/
theorem rawProfileSmooth : RawProfileSmooth := by
  intro L x hx
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    L.train_stream_smooth
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => L.train.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    L.train.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hdΨ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) x)
      (Ioi 0 ×ˢ univ) :=
    hΨ.fderiv_of_isOpen hU (by simp)
  have hdη : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) x (0, (0, 1)))
      (Ioi 0 ×ˢ univ) :=
    hdΨ.clm_apply contDiffOn_const
  have hds : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) x (1, (0, 0)))
      (Ioi 0 ×ˢ univ) :=
    hdΨ.clm_apply contDiffOn_const
  have hG : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => L.train.v x.1 x.2 +
      (L.ε * (L.train.ψ x.1 x.2 -
        (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) x (1, (0, 0))))) •
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (Ioi 0 ×ˢ univ) := by
    refine hv.add (ContDiffOn.smul_const ?_ _)
    exact contDiffOn_const.mul (hΨ.sub ((contDiffOn_snd.snd.mul hdη).add
      ((contDiffOn_const.mul contDiffOn_fst).mul hds)))
  have hcongr : ∀ y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))),
      (fun x : ℝ × (ℝ × ℝ) => L.train.v x.1 x.2 +
      (L.ε * (L.train.ψ x.1 x.2 -
        (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) x (1, (0, 0))))) •
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) y = bRaw L y := by
    intro y hy
    have hxU : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 y := hU.mem_nhds hy
    have hΨd : HasFDerivAt (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2)
        (fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) y) y :=
      ((hΨ.contDiffAt hxU).differentiableAt (by simp)).hasFDerivAt
    have e1 : deriv (fun t => L.train.ψ y.1 (y.2.1, t)) y.2.2 =
        fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) y (0, (0, 1)) := by
      have hl : HasDerivAt (fun t : ℝ => ((y.1, (y.2.1, t)) : ℝ × (ℝ × ℝ))) (0, (0, 1)) y.2.2 :=
        (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
      exact (HasFDerivAt.comp_hasDerivAt (x := y.2.2) hΨd hl).deriv
    have e2 : deriv (fun t => L.train.ψ t (y.2.1, y.2.2)) y.1 =
        fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => L.train.ψ x.1 x.2) y (1, (0, 0)) := by
      have hl : HasDerivAt (fun t : ℝ => ((t, (y.2.1, y.2.2)) : ℝ × (ℝ × ℝ))) (1, (0, 0)) y.1 :=
        (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
      exact (HasFDerivAt.comp_hasDerivAt (x := y.1) hΨd hl).deriv
    simp only [UnforcedLeray.Cons.C03.rawProfile, UnforcedLeray.Cons.C03.raisedStream, bRaw]
    rw [e1, e2]
  have hcontOn : ContDiffOn ℝ ∞ (bRaw L) (Ioi 0 ×ˢ univ) :=
    hG.congr (fun y hy => (hcongr y hy).symm)
  have hx' : x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hx, mem_univ _⟩
  exact hcontOn.contDiffAt (hU.mem_nhds hx')

end UnforcedLeray.Short.PartIIIb.Concrete
