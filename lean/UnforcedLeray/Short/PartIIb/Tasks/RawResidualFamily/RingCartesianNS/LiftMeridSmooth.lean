import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7`, leaf `LiftMeridSmooth`: the lifted profiles are `C²`

Proves `UnforcedLeray.Short.IIb.LiftMeridSmooth` (defined in `Sub/R1_7.lean`, lines 209-212).
Source of record: `the November 2 reference manuscript`, lines 1203-1250
(the lift `u_r = (R/r) v_1`, `u_z = (R/r)(v_2 + εH)`, `p_raw = (R/r)^2 p`; chart
`q = R log(r/R)`, `η = R z/r`, `s = R² t/r²`).

Proof idea. The chart `(r, z, t) ↦ (q, η, s)` is `C²` on `{r > 0}` and maps `{r > 0, t > 0}` into the
open age domain `{s > 0}` (`liftMS_chart`, `liftMS_mapsTo`). The profile `streamV1 ψ = -∂_η ψ` and
`axialProfile R ψ = ∂_q ψ + R⁻¹ (ψ - K ψ)` are `C²` on the age domain when `ψ` is `C³` there
(`liftMS_streamV1`, `liftMS_axialProfile`, via `fderiv` of a `C³` function). Composing with the chart and
multiplying by the weight `(R/r)^k` gives the `C²` claim for `scaledLift R k g`, `k = 1, 1, 2`
(`liftMS_scaled`). No hypothesis is added to the statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

theorem liftMS_mem {q : ℝ × ℝ × ℝ} (hq : q ∈ meridDomain) : 0 < q.1 ∧ 0 < q.2.2 := hq

/-- The chart `(r, z, t) ↦ (R log(r/R), (R/r) z, (R/r)² t)` is `C²` on `{r > 0, t > 0}`. -/
theorem liftMS_chart (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => profileChart R q.1 q.2.1 q.2.2) meridDomain := by
  have hq1 : ∀ q ∈ meridDomain, q.1 ≠ 0 := fun q hq => ne_of_gt (liftMS_mem hq).1
  have hinv : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => q.1⁻¹) meridDomain :=
    contDiffOn_fst.inv hq1
  have hlog : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => R * Real.log (q.1 / R)) meridDomain :=
    contDiffOn_const.mul ((contDiffOn_fst.div_const R).log fun q hq =>
      div_ne_zero (hq1 q hq) hR.ne')
  have ha : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => R / q.1) meridDomain :=
    ((contDiffOn_const (c := R)).mul hinv).congr fun q _ => by simp [div_eq_mul_inv]
  have hη1 : ContDiff ℝ 2 (fun q : ℝ × ℝ × ℝ => q.2.1) := contDiff_snd.fst
  have hσ1 : ContDiff ℝ 2 (fun q : ℝ × ℝ × ℝ => q.2.2) := contDiff_snd.snd
  have hη : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => R / q.1 * q.2.1) meridDomain :=
    ha.mul hη1.contDiffOn
  have hs : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => (R / q.1) ^ 2 * q.2.2) meridDomain :=
    (ha.pow 2).mul hσ1.contDiffOn
  have hmain : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ =>
      (R * Real.log (q.1 / R), (R / q.1 * q.2.1, (R / q.1) ^ 2 * q.2.2))) meridDomain :=
    hlog.prodMk (hη.prodMk hs)
  exact hmain

/-- The chart maps `{r > 0, t > 0}` into the open age domain `{s > 0}`. -/
theorem liftMS_mapsTo (R : ℝ) (hR : 0 < R) :
    MapsTo (fun q : ℝ × ℝ × ℝ => profileChart R q.1 q.2.1 q.2.2) meridDomain ageDomain := by
  intro q hq
  obtain ⟨h1, h2⟩ := liftMS_mem hq
  show 0 < (R / q.1) ^ 2 * q.2.2
  exact mul_pos (pow_pos (div_pos hR h1) 2) h2

/-- A profile `g` that is `C²` on the age domain gives the `C²` lift `a_r^k g(q, η, s)` on
`{r > 0, t > 0}`, with `a_r = R/r`. -/
theorem liftMS_scaled (R : ℝ) (hR : 0 < R) (k : ℕ) {g : ProfilePoint → ℝ}
    (hg : ContDiffOn ℝ 2 g ageDomain) :
    ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => scaledLift R k g q.1 q.2.1 q.2.2) meridDomain := by
  have hcomp : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => g (profileChart R q.1 q.2.1 q.2.2))
      meridDomain :=
    hg.comp (liftMS_chart R hR) (liftMS_mapsTo R hR)
  have hinv : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => q.1⁻¹) meridDomain :=
    contDiffOn_fst.inv fun q hq => ne_of_gt (liftMS_mem hq).1
  have hw : ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => (R / q.1) ^ k) meridDomain :=
    (((contDiffOn_const (c := R)).mul hinv).pow k).congr fun q _ => by
      simp [div_eq_mul_inv]
  exact hw.mul hcomp

/-- The stream profile `streamV1 ψ = -∂_η ψ` is `C²` on the age domain. -/
theorem liftMS_streamV1 {psi : ProfilePoint → ℝ} (hpsi : ContDiffOn ℝ 3 psi ageDomain) :
    ContDiffOn ℝ 2 (streamV1 psi) ageDomain := by
  have hD : ContDiffOn ℝ 2 (fderiv ℝ psi) ageDomain :=
    hpsi.fderiv_of_isOpen isOpen_ageDomain (by norm_num)
  have he : ContDiffOn ℝ 2 (fun y => fderiv ℝ psi y eηDir) ageDomain :=
    hD.clm_apply (contDiffOn_const (c := eηDir))
  exact he.neg

/-- The axial profile `axialProfile R ψ = ∂_q ψ + R⁻¹ (ψ - Kψ)` is `C²` on the age domain. -/
theorem liftMS_axialProfile (R : ℝ) {psi : ProfilePoint → ℝ}
    (hpsi : ContDiffOn ℝ 3 psi ageDomain) :
    ContDiffOn ℝ 2 (axialProfile R psi) ageDomain := by
  have hD : ContDiffOn ℝ 2 (fderiv ℝ psi) ageDomain :=
    hpsi.fderiv_of_isOpen isOpen_ageDomain (by norm_num)
  have hq : ContDiffOn ℝ 2 (fun y => fderiv ℝ psi y eqDir) ageDomain :=
    hD.clm_apply (contDiffOn_const (c := eqDir))
  have he : ContDiffOn ℝ 2 (fun y => fderiv ℝ psi y eηDir) ageDomain :=
    hD.clm_apply (contDiffOn_const (c := eηDir))
  have hs : ContDiffOn ℝ 2 (fun y => fderiv ℝ psi y esDir) ageDomain :=
    hD.clm_apply (contDiffOn_const (c := esDir))
  have hψ2 : ContDiffOn ℝ 2 psi ageDomain := hpsi.of_le (by norm_num)
  have hη1 : ContDiff ℝ 2 (fun y : ProfilePoint => y.2.1) := contDiff_snd.fst
  have hσ1 : ContDiff ℝ 2 (fun y : ProfilePoint => y.2.2) := contDiff_snd.snd
  have hK : ContDiffOn ℝ 2 (ageOperator psi) ageDomain :=
    (hη1.contDiffOn.mul he).add (((contDiffOn_const (c := (2 : ℝ))).mul hσ1.contDiffOn).mul hs)
  exact hq.add ((contDiffOn_const (c := ringEps R)).mul (hψ2.sub hK))

/-- **Unit `LiftMeridSmooth`**: for `R ≥ 2`, `ψ` and `pr` of class `C³` and `C²` on the age
domain, the lifts `u_r`, `u_z` (with `k = 1`) and the raw pressure (`k = 2`) are `C²` jointly in
`(r, z, t)` on `{r > 0, t > 0}`. -/
theorem liftMeridSmooth : UnforcedLeray.Short.IIb.LiftMeridSmooth := by
  unfold LiftMeridSmooth
  intro R psi pr hR hpsi hpr
  have hR0 : 0 < R := by linarith
  exact ⟨liftMS_scaled R hR0 1 (liftMS_streamV1 hpsi),
    liftMS_scaled R hR0 1 (liftMS_axialProfile R hpsi),
    liftMS_scaled R hR0 2 hpr⟩

end UnforcedLeray.Short.IIb

end
