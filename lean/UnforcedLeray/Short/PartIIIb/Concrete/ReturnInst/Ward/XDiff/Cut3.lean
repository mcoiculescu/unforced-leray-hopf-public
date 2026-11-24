import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff.Psid

/-!
# The stream cutoff preserves `C³` on the young region (source 4180-4186)

Source of record: `the November 2 reference manuscript` (73 pages).

`C³` version of `t9_outPrim_c2` and `t9_wsc_contDiffOn`: the outward primitive of a `C³` field on
the young region is `C³` there (its gradient `(r Z_z, -r Z_r)` is `C³`), and
`𝒞_y Z = χ_y Z + (χ_y'/r)Ψ_Z e_z` is `C³` (`χ_y` is `C^∞`; `ϱ ≠ 0` on the young region).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem xc_outPrim_c3 {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {Z : ℝ → Space → Space} {τ : ℝ}
    (hZ : ContDiffOn ℝ 3 (Z τ) (youngOpen ν R))
    (hdr : ∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim Z τ r' z) (r * Z τ !₂[r, 0, z] 2) r ∧
        HasDerivAt (fun z' => outPrim Z τ r z') (-(r * Z τ !₂[r, 0, z] 0)) z) :
    ContDiffOn ℝ 3 (fun y : Space => outPrim Z τ (ϱ y) (y 2)) (youngOpen ν R) := by
  have hS : IsOpen {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have hm : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
    have hv : ContDiff ℝ 3 (fun p : ℝ × ℝ => (![p.1, 0, p.2] : Fin 3 → ℝ)) :=
      contDiff_pi.2 (fun i => by fin_cases i <;> simp <;> fun_prop)
    have : ContDiff ℝ 3 (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) :=
      PiLp.contDiff_toLp.comp hv
    exact this.contDiffOn
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} (youngOpen ν R) := by
    intro p hp
    have hp' : R * Real.sqrt (5 * ν / 6) < p.1 := hp
    show R * Real.sqrt (5 * ν / 6) < ϱ (!₂[p.1, 0, p.2] : Space)
    have hϱ : ϱ (!₂[p.1, 0, p.2] : Space) = |p.1| := by simp [ϱ, Real.sqrt_sq_eq_abs]
    rw [hϱ]
    exact lt_of_lt_of_le hp' (le_abs_self _)
  have hPc : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    contDiffOn_fst.mul ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (hZ.comp hm hmaps))
  have hQc : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    (contDiffOn_fst.mul ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (hZ.comp hm hmaps))).neg
  have hD := fun p (hp : p ∈ {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1}) =>
    t9_hasFDerivAt_of_partials _ hS (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
      (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      hPc.continuousOn hQc.continuousOn
      (fun p hp => (hdr p.1 p.2 hp).1) (fun p hp => (hdr p.1 p.2 hp).2) p hp
  have hPc1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := hPc.of_le (by norm_num)
  have hQc1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := hQc.of_le (by norm_num)
  have hS1 : ContDiffOn ℝ 2 (fderiv ℝ (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
    refine ContDiffOn.congr (f := fun p : ℝ × ℝ =>
      (p.1 * Z τ !₂[p.1, 0, p.2] 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(p.1 * Z τ !₂[p.1, 0, p.2] 0)) • ContinuousLinearMap.snd ℝ ℝ ℝ) ?_ ?_
    · exact (hPc1.smul contDiffOn_const).add (hQc1.smul contDiffOn_const)
    · intro p hp
      exact (hD p hp).fderiv
  have hF : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
    have h' : ContDiffOn ℝ (2 + 1) (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
        {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hS]
      refine ⟨fun p hp => (hD p hp).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), hS1⟩
    exact h'
  have hϱ2 : ContDiffOn ℝ 3 (fun y : Space => ϱ y) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun y hy => t9_not_axis hν hR hy)
  have hz2 : ContDiffOn ℝ 3 (fun y : Space => y 2) (youngOpen ν R) :=
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff).contDiffOn
  have hG : ContDiffOn ℝ 3 (fun y : Space => ((ϱ y, y 2) : ℝ × ℝ)) (youngOpen ν R) :=
    hϱ2.prodMk hz2
  have hmapG : Set.MapsTo (fun y : Space => ((ϱ y, y 2) : ℝ × ℝ)) (youngOpen ν R)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := fun y hy => by
    show R * Real.sqrt (5 * ν / 6) < ϱ y
    exact hy
  exact hF.comp hG hmapG

theorem xc_wsc_c3 {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) (hν : 0 < ν)
    (hR : 0 < R) {Z : ℝ → Space → Space} {τ : ℝ}
    (hZ : ContDiffOn ℝ 3 (Z τ) (youngOpen ν R))
    (hO : ContDiffOn ℝ 3 (fun y : Space => outPrim Z τ (ϱ y) (y 2)) (youngOpen ν R)) :
    ContDiffOn ℝ 3 (wardStreamCut ν R χy Z τ) (youngOpen ν R) := by
  have hne : ∀ y ∈ youngOpen ν R, ϱ y ≠ 0 := fun y hy => by
    have hp := t9_thr_pos hν hR
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
    intro h0
    linarith
  have hϱ : ContDiffOn ℝ 3 (fun y : Space => ϱ y) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun y hy => t9_not_axis hν hR hy)
  have hage : ContDiffOn ℝ 3 (fun y : Space => age R y) (youngOpen ν R) :=
    ContDiffOn.div contDiffOn_const (hϱ.pow 2) (fun y hy => pow_ne_zero 2 (hne y hy))
  have hνage : ContDiffOn ℝ 3 (fun y : Space => ν * age R y) (youngOpen ν R) :=
    contDiffOn_const.mul hage
  have hχ3 : ContDiff ℝ 3 χy := hχy.smooth.of_le (xd_le_top 3)
  have hdχ3 : ContDiff ℝ 3 (deriv χy) :=
    ((show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχy.smooth).deriv').of_le
      (xd_le_top 3)
  have hχA : ContDiffOn ℝ 3 (fun y : Space => χy (ν * age R y)) (youngOpen ν R) :=
    hχ3.comp_contDiffOn hνage
  have hdA : ContDiffOn ℝ 3 (fun y : Space => deriv χy (ν * age R y)) (youngOpen ν R) :=
    hdχ3.comp_contDiffOn hνage
  have hK : ContDiffOn ℝ 3 (fun y : Space => -2 * ν * R ^ 2 / ϱ y ^ 3) (youngOpen ν R) :=
    ContDiffOn.div contDiffOn_const (hϱ.pow 3) (fun y hy => pow_ne_zero 3 (hne y hy))
  have hterm1 := hχA.smul hZ
  have hterm2 := (((hdA.mul hK).div hϱ hne).mul hO).smul
    (contDiffOn_const (c := (coordinateVector 2 : Space)))
  exact hterm1.add hterm2

end UnforcedLeray.Short.PartIIIb.Concrete
