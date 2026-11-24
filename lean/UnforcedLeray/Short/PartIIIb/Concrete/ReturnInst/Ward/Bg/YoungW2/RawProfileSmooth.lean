import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Defs

/-!
# The raw profile is smooth for positive age (source 1206-1222, 397, 2049)

Source of record: `the November 2 reference manuscript` (73 pages).

Leaf of `PartIII-b:C/ward/12` (`BgRawProfileSmooth`, `Ward/Bg/YoungW2/Defs.lean`).
`b_raw = v + ε H e_z`, `H = ψ - η∂_ηψ - 2s∂_sψ` (`Cons.C03.rawProfile`, `raisedStream`): on the open
set `{s > 0}` the train velocity is `C^∞` (`IsTrain.smooth_v`, on `s ≥ 0`), the stream
`Ψ(s, (q, η)) = ψ(s, (q, η))` is `C^∞` (`BgRegime.train_stream_smooth`), and the one-variable
derivatives in `raisedStream` are `DΨ(x)(0, (0, 1))` and `DΨ(x)(1, (0, 0))`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **The raw profile on `{s > 0}` in terms of the stream** (source 1206-1222: `v = ∇^⊥ψ`,
`H = (1-K)ψ`, `K = η∂_η + 2s∂_s`): with `Ψ(s, (q, η)) = ψ(s, (q, η))`,
`b_raw = (-∂_ηΨ, ∂_qΨ) + ε(Ψ - η∂_ηΨ - 2s∂_sΨ) e_z`, the partials being `DΨ(x)` applied to the
coordinate directions (`IsTrain.stream` for `v`). -/
theorem bgRawProfile_eq_on {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) {x : ℝ × (ℝ × ℝ)}
    (hx : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :
    UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ x =
      UnforcedLeray.Train.toVec
          (-(fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (0, (0, 1))),
            fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (0, (1, 0))) +
        (p.ε * (p.train.ψ x.1 x.2 -
          (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (0, (0, 1)) +
            2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (1, (0, 0))))) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hreg.train_stream_smooth
  have hxU : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 x := hU.mem_nhds hx
  have hΨd : HasFDerivAt (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2)
      (fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x) x :=
    ((hΨ.contDiffAt hxU).differentiableAt (by simp)).hasFDerivAt
  have e1 : deriv (fun t => p.train.ψ x.1 (x.2.1, t)) x.2.2 =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (0, (0, 1)) := by
    have hl : HasDerivAt (fun t : ℝ => ((x.1, (x.2.1, t)) : ℝ × (ℝ × ℝ))) (0, (0, 1)) x.2.2 :=
      (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
    exact (HasFDerivAt.comp_hasDerivAt (x := x.2.2) hΨd hl).deriv
  have e2 : deriv (fun t => p.train.ψ t (x.2.1, x.2.2)) x.1 =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (1, (0, 0)) := by
    have hl : HasDerivAt (fun t : ℝ => ((t, (x.2.1, x.2.2)) : ℝ × (ℝ × ℝ))) (1, (0, 0)) x.1 :=
      (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
    exact (HasFDerivAt.comp_hasDerivAt (x := x.1) hΨd hl).deriv
  have e3 : deriv (fun t => p.train.ψ x.1 (t, x.2.2)) x.2.1 =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (0, (1, 0)) := by
    have hl : HasDerivAt (fun t : ℝ => ((x.1, (t, x.2.2)) : ℝ × (ℝ × ℝ))) (0, (1, 0)) x.2.1 :=
      (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
    exact (HasFDerivAt.comp_hasDerivAt (x := x.2.1) hΨd hl).deriv
  have hv : p.train.v x.1 x.2 = UnforcedLeray.Train.toVec
      (UnforcedLeray.GaussianVortex.perpendicularGradient (p.train.ψ x.1) x.2) :=
    p.train.isTrain.stream x.1 (le_of_lt hx.1) x.2
  simp only [UnforcedLeray.Cons.C03.rawProfile, UnforcedLeray.Cons.C03.raisedStream, hv,
    UnforcedLeray.GaussianVortex.perpendicularGradient, UnforcedLeray.GaussianVortex.partialX,
    UnforcedLeray.GaussianVortex.partialY]
  rw [e1, e2, e3]

/-- **`BgRawProfileSmooth`** (source 1206-1222 `sct:lift`, 397, 2049). -/
theorem bgRawProfileSmooth : BgRawProfileSmooth := by
  intro p d dm dp hreg
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hreg.train_stream_smooth
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => p.train.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    p.train.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hdΨ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x)
      (Ioi 0 ×ˢ univ) :=
    hΨ.fderiv_of_isOpen hU (by simp)
  have hdη : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (0, (0, 1)))
      (Ioi 0 ×ˢ univ) :=
    hdΨ.clm_apply contDiffOn_const
  have hds : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (1, (0, 0)))
      (Ioi 0 ×ˢ univ) :=
    hdΨ.clm_apply contDiffOn_const
  have hG : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => p.train.v x.1 x.2 +
      (p.ε * (p.train.ψ x.1 x.2 -
        (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (1, (0, 0))))) •
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (Ioi 0 ×ˢ univ) := by
    refine hv.add (ContDiffOn.smul_const ?_ _)
    exact contDiffOn_const.mul (hΨ.sub ((contDiffOn_snd.snd.mul hdη).add
      ((contDiffOn_const.mul contDiffOn_fst).mul hds)))
  refine hG.congr fun x hx => ?_
  have hxU : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 x := hU.mem_nhds hx
  have hΨd : HasFDerivAt (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2)
      (fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x) x :=
    ((hΨ.contDiffAt hxU).differentiableAt (by simp)).hasFDerivAt
  have e1 : deriv (fun t => p.train.ψ x.1 (x.2.1, t)) x.2.2 =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (0, (0, 1)) := by
    have hl : HasDerivAt (fun t : ℝ => ((x.1, (x.2.1, t)) : ℝ × (ℝ × ℝ))) (0, (0, 1)) x.2.2 :=
      (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
    exact (HasFDerivAt.comp_hasDerivAt (x := x.2.2) hΨd hl).deriv
  have e2 : deriv (fun t => p.train.ψ t (x.2.1, x.2.2)) x.1 =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x (1, (0, 0)) := by
    have hl : HasDerivAt (fun t : ℝ => ((t, (x.2.1, x.2.2)) : ℝ × (ℝ × ℝ))) (1, (0, 0)) x.1 :=
      (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
    exact (HasFDerivAt.comp_hasDerivAt (x := x.1) hΨd hl).deriv
  simp only [UnforcedLeray.Cons.C03.rawProfile, UnforcedLeray.Cons.C03.raisedStream]
  rw [e1, e2]

#print axioms bgRawProfileSmooth

end UnforcedLeray.Short.PartIIIb.Concrete
