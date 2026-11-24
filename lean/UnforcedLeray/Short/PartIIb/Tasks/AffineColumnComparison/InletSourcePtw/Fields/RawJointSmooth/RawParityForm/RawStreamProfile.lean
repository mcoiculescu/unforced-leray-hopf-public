import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_org

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- **The raw profile is the ring stream profile of the train stream** (`RawStreamProfile`;
SP 1207-1212). The components of `rawProfile R⁻¹ v ψ` at `y = (s, (q, η))` are the Cartesian
velocity `v(s,(q,η))`, `(−∂_η ψ, ∂_q ψ)` (`IsTrain.stream`, `perpendicularGradient`), plus the
`R⁻¹`-weighted raised stream `H = ψ − η∂_ηψ − 2s∂_sψ`; these are the chart partials of
`ringStreamProfile R Ψ` (`ringStreamProfile_apply_zero/_one`). -/
theorem rawStreamProfile : UnforcedLeray.Short.IIb.RawStreamProfile := by
  intro ν c R tr hR hψ y hy
  have hs : 0 < y.1 := hy
  have hmem : y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := Set.mk_mem_prod hy (Set.mem_univ _)
  have hd : DifferentiableAt ℝ (fun y : ℝ × (ℝ × ℝ) => tr.ψ y.1 y.2) y :=
    UnforcedLeray.Short.IIb.differentiableAt_of_contDiffOn_pos hψ hmem
  -- the three chart partials of the stream, as one-variable derivatives along coordinate lines
  have hdS : UnforcedLeray.Axi.dS (fun y : ℝ × (ℝ × ℝ) => tr.ψ y.1 y.2) y =
      deriv (fun t => tr.ψ t (y.2.1, y.2.2)) y.1 := by
    have hline : HasDerivAt (fun t : ℝ => ((t, (y.2.1, y.2.2)) : ℝ × (ℝ × ℝ)))
        ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) y.1 :=
      (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
    exact (hd.hasFDerivAt.comp_hasDerivAt y.1 hline).deriv.symm
  have hdQ : UnforcedLeray.Axi.dQ (fun y : ℝ × (ℝ × ℝ) => tr.ψ y.1 y.2) y =
      deriv (fun t => tr.ψ y.1 (t, y.2.2)) y.2.1 := by
    have hline : HasDerivAt (fun t : ℝ => ((y.1, (t, y.2.2)) : ℝ × (ℝ × ℝ)))
        ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) y.2.1 :=
      (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
    exact (hd.hasFDerivAt.comp_hasDerivAt y.2.1 hline).deriv.symm
  have hdEta : UnforcedLeray.Axi.dEta (fun y : ℝ × (ℝ × ℝ) => tr.ψ y.1 y.2) y =
      deriv (fun t => tr.ψ y.1 (y.2.1, t)) y.2.2 := by
    have hline : HasDerivAt (fun t : ℝ => ((y.1, (y.2.1, t)) : ℝ × (ℝ × ℝ)))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) y.2.2 :=
      (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
    exact (hd.hasFDerivAt.comp_hasDerivAt y.2.2 hline).deriv.symm
  -- the two Cartesian components of the velocity at the stream's own point
  have hv0 : tr.v y.1 y.2 0 = -(deriv (fun t => tr.ψ y.1 (y.2.1, t)) y.2.2) := by
    rw [tr.isTrain.stream y.1 hs.le y.2]
    rfl
  have hv1 : tr.v y.1 y.2 1 = deriv (fun t => tr.ψ y.1 (t, y.2.2)) y.2.1 := by
    rw [tr.isTrain.stream y.1 hs.le y.2]
    rfl
  have h0 : UnforcedLeray.Cons.C03.rawProfile R⁻¹ tr.v tr.ψ y 0 =
      UnforcedLeray.Axi.ringStreamProfile R (fun y : ℝ × (ℝ × ℝ) => tr.ψ y.1 y.2) y 0 := by
    rw [UnforcedLeray.Cons.C03.rawProfile_zero, UnforcedLeray.Short.IIb.ringStreamProfile_apply_zero,
      hv0, hdEta]
  have h1 : UnforcedLeray.Cons.C03.rawProfile R⁻¹ tr.v tr.ψ y 1 =
      UnforcedLeray.Axi.ringStreamProfile R (fun y : ℝ × (ℝ × ℝ) => tr.ψ y.1 y.2) y 1 := by
    rw [UnforcedLeray.Cons.C03.rawProfile_one, UnforcedLeray.Short.IIb.ringStreamProfile_apply_one,
      hv1, hdQ, hdS, hdEta]
    unfold UnforcedLeray.Cons.C03.raisedStream
    simp only [Prod.mk.eta]
    ring
  ext i
  fin_cases i
  · exact h0
  · exact h1

end UnforcedLeray.Short.IIb
