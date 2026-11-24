import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1

/-!
# Smoothness of the raw lift profile (task `PartIII-b:C/rep/8/2/pres/4/1/2`)

Source `the November 2 reference manuscript`
2076-2077 (the lift `U_raw = √s[v₁ e_r + (v₂ + εH) e_z]`, `H = (1 − K_age) ψ`) and 5200.
In the library notation this is `rawProfile ε v ψ p = v p.1 p.2 + (ε * raisedStream ψ p.1 p.2.1
p.2.2) • e_1` (`Cons/C03Background/RawLift.lean`, lines 47-56).

On the open set `Ioi 0 ×ˢ univ`: the train velocity `v` is `C^∞` (`IsTrain.smooth_v` on
`Ici 0 ×ˢ univ`), and `raisedStream` is built from `ψ` and its one-variable partials
`∂_η ψ`, `∂_s ψ`. Since `ψ` is `C³` jointly there, these partials are `C²` (as joint
`fderiv`s of `ψ`, evaluated on fixed vectors), so `H` is `C²`.
-/

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03
open UnforcedLeray.Cyl

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The one-variable `η`-derivative of a slice is a joint partial derivative. -/
theorem rp_deriv_eta {ψ : ℝ → ℝ × ℝ → ℝ} {s ξ η : ℝ}
    (hd : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (ξ, η))) :
    deriv (fun t => ψ s (ξ, t)) η =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (ξ, η)) (0, (0, 1)) := by
  have hγ : HasDerivAt (fun t : ℝ => ((s, (ξ, t)) : ℝ × (ℝ × ℝ)))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) η :=
    (hasDerivAt_const η s).prodMk ((hasDerivAt_const η ξ).prodMk (hasDerivAt_id η))
  exact (HasFDerivAt.comp_hasDerivAt η hd.hasFDerivAt hγ).deriv

/-- The one-variable `s`-derivative of a slice is a joint partial derivative. -/
theorem rp_deriv_s {ψ : ℝ → ℝ × ℝ → ℝ} {s ξ η : ℝ}
    (hd : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (ξ, η))) :
    deriv (fun t => ψ t (ξ, η)) s =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (ξ, η)) (1, (0, 0)) := by
  have hγ : HasDerivAt (fun t : ℝ => ((t, (ξ, η)) : ℝ × (ℝ × ℝ)))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk ((hasDerivAt_const s ξ).prodMk (hasDerivAt_const s η))
  exact (HasFDerivAt.comp_hasDerivAt s hd.hasFDerivAt hγ).deriv

/-- Pointwise formula for `raisedStream` through joint partial derivatives of `ψ`. -/
theorem rp_raised_eq {ψ : ℝ → ℝ × ℝ → ℝ} {O : Set (ℝ × (ℝ × ℝ))} (hO : IsOpen O)
    (hG : ContDiffOn ℝ 3 (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) O) {p : ℝ × (ℝ × ℝ)} (hp : p ∈ O) :
    raisedStream ψ p.1 p.2.1 p.2.2 =
      ψ p.1 p.2 - (p.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) p (0, (0, 1)) +
        2 * p.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) p (1, (0, 0))) := by
  have hd : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (p.1, (p.2.1, p.2.2)) :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hp)
  unfold raisedStream
  rw [rp_deriv_eta hd, rp_deriv_s hd]

/-- `raisedStream` is `C²` on an open set where `ψ` is `C³` jointly. -/
theorem rp_raised_contDiffOn {ψ : ℝ → ℝ × ℝ → ℝ} {O : Set (ℝ × (ℝ × ℝ))} (hO : IsOpen O)
    (hG : ContDiffOn ℝ 3 (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) O) :
    ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => raisedStream ψ p.1 p.2.1 p.2.2) O := by
  have hG2 : ContDiffOn ℝ 2 (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) O := hG.of_le (by norm_num)
  have hFd : ContDiffOn ℝ 2
      (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => ψ y.1 y.2) x) O :=
    hG.fderiv_of_isOpen hO (by norm_num)
  have hD1 : ContDiffOn ℝ 2
      (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => ψ y.1 y.2) x (0, (0, 1))) O :=
    hFd.clm_apply (contDiffOn_const (c := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
  have hD2 : ContDiffOn ℝ 2
      (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => ψ y.1 y.2) x (1, (0, 0))) O :=
    hFd.clm_apply (contDiffOn_const (c := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))))
  have hη : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => p.2.2) O :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hp1 : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => p.1) O := contDiffOn_fst
  have hH : ContDiffOn ℝ 2
      (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2 - (p.2.2 *
        fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) p (0, (0, 1)) +
          2 * p.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) p (1, (0, 0)))) O :=
    hG2.sub ((hη.mul hD1).add (((contDiffOn_const (c := (2 : ℝ))).mul hp1).mul hD2))
  exact hH.congr fun p hp => rp_raised_eq hO hG hp

/-- **Task `PartIII-b:C/rep/8/2/pres/4/1/2`.** The raw lift profile of a train is `C²` on
`Ioi 0 ×ˢ univ`. -/
theorem rawProfile_contDiffOn {ν c ε : ℝ} {v : ℝ → Plane → UnforcedLeray.Train.Vec} {p ψ : ℝ → Plane → ℝ} (h : UnforcedLeray.B0140.IsTrain ν c v p ψ) (hψ : ContDiffOn ℝ 3 (fun x : ℝ × Plane => ψ x.1 x.2) (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ 2 (UnforcedLeray.Cons.C03.rawProfile ε v ψ) (Ioi 0 ×ˢ univ) := by
  have hO : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hv : ContDiffOn ℝ 2 (fun x : ℝ × Plane => v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    (h.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Set.Subset.rfl)).of_le (by norm_num)
  have hH := rp_raised_contDiffOn hO hψ
  have hstep : ContDiffOn ℝ 2
      (fun p : ℝ × (ℝ × ℝ) => (ε * raisedStream ψ p.1 p.2.1 p.2.2) •
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (Ioi 0 ×ˢ univ) :=
    ((contDiffOn_const (c := ε)).mul hH).smul contDiffOn_const
  unfold UnforcedLeray.Cons.C03.rawProfile
  exact hv.add hstep

end UnforcedLeray.Short.PartIIIb.Concrete
