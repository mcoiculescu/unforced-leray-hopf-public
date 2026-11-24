import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part II-b, task `PartII-b:R1/5`: `U_raw` is the ring lift of the actual train (conditional)

Source of record: `the November 2 reference manuscript`, lines 1203-1250
(Proposition `sct:lift`: the physical stream `rψ(q,η,s)` gives `u_r = (R/r)v₁`,
`u_z = (R/r)(v₂ + εH)`, `H = (1-K)ψ`, `K = η∂_η + 2s∂_s`; "smooth through the axis for positive
time"), and lines 2040-2046 (`V₀ = U_raw` is the solenoidal lift of the train).

## What is proved, and what it rests on

Target: `RawIsRingLift` (`Sub/R1.lean`): off the axis, `p.raw τ y = simProfile 1 (liftVelocity R ψ̃) τ y`
with `ψ̃ = trainProfile p.train.ψ`.



* `p.raw` is built from `rawProfile ε v ψ = (v₁, v₂ + ε raisedStream ψ)`, where `raisedStream` uses the
  one-variable `deriv`s of `ψ`;
* `liftVelocity` is built from `merProfile R ψ̃ = (streamV1 ψ̃, axialProfile R ψ̃)`, where `streamV1`,
  `streamV2`, `ageOperator` use `partialQ, partialEta, partialAge = fderiv ψ̃ ·` of the *profile*
  `ψ̃(q,η,s) = ψ(s,(q,η))`.

The two agree exactly when `ψ̃` is (jointly) differentiable at the chart point, `s > 0` (otherwise
`fderiv ψ̃ = 0` is a junk value). `B0140.IsTrain` only gives `ψ(s, ·)` differentiable at each fixed
`s` (`stream_differentiable`), not the joint/time regularity of `ψ`. That joint regularity is the
named Prop `PartI.TrainStreamSmooth` (`Short/PartI/Sub/T01.lean`), a true source fact (source lines
261-288, 1203-1250: the train is smooth for positive time and `ψ` is its decaying stream) that is NOT a

author: the fix is a field `stream_smooth` of `IsTrain`).

Proved here (no sorry, no new hypothesis beyond `PartI.TrainStreamSmooth`):
`rawIsRingLift_of (h : PartI.TrainStreamSmooth) : RawIsRingLift`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0184 UnforcedLeray.B0185
  UnforcedLeray.B0190

/-- Joint differentiability of the train profile at every point of positive age, from
`PartI.TrainStreamSmooth` (profile point `(q, η, s) ↦ ψ(s, (q, η))`). -/
theorem trainProfile_differentiableAt_of_smooth (h : UnforcedLeray.Short.PartI.TrainStreamSmooth)
    {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) (T : UnforcedLeray.B0140.TrainSol ν c)
    (hT : UnforcedLeray.Short.PartI.IsBUCTrain T) {x : ProfilePoint} (hx : 0 < x.2.2) :
    DifferentiableAt ℝ (trainProfile T.ψ) x := by
  have hψ := h ν c hν hc T hT
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (x.2.2, (x.1, x.2.1)) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    Set.mk_mem_prod hx (Set.mem_univ _)
  have hat : ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => T.ψ z.1 z.2) (x.2.2, (x.1, x.2.1)) :=
    hψ.contDiffAt (hopen.mem_nhds hmem)
  have hg : DifferentiableAt ℝ (fun x : ProfilePoint => (x.2.2, (x.1, x.2.1))) x := by
    fun_prop
  exact (hat.differentiableAt (by simp)).comp x hg

/-- At a point of differentiability, `∂_η` of the profile is the one-variable `deriv` in `η`. -/
theorem partialEta_trainProfile {ν c : ℝ} (T : UnforcedLeray.B0140.TrainSol ν c)
    {x : ProfilePoint} (hd : DifferentiableAt ℝ (trainProfile T.ψ) x) :
    partialEta (trainProfile T.ψ) x = deriv (fun t => T.ψ x.2.2 (x.1, t)) x.2.1 := by
  have hline : HasDerivAt (fun e : ℝ => ((x.1, (e, x.2.2)) : ProfilePoint)) eηDir x.2.1 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  have h1 := hd.hasFDerivAt.comp_hasDerivAt x.2.1 hline
  exact h1.deriv.symm

/-- At a point of differentiability, `∂_s` of the profile is the one-variable `deriv` in `s`. -/
theorem partialAge_trainProfile {ν c : ℝ} (T : UnforcedLeray.B0140.TrainSol ν c)
    {x : ProfilePoint} (hd : DifferentiableAt ℝ (trainProfile T.ψ) x) :
    partialAge (trainProfile T.ψ) x = deriv (fun t => T.ψ t (x.1, x.2.1)) x.2.2 := by
  have hline : HasDerivAt (fun e : ℝ => ((x.1, (x.2.1, e)) : ProfilePoint)) esDir x.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  have h1 := hd.hasFDerivAt.comp_hasDerivAt x.2.2 hline
  exact h1.deriv.symm

/-- **The profile identity** (`eq:m3-ring-lift`, SP 1212-1240): for `s > 0`, the raw profile
`(v₁, v₂ + εH)` of the actual train (one-variable derivatives) is the profile `merProfile R ψ̃` of the
B0185 lift (profile `fderiv`s), `ε = R⁻¹`. -/
theorem rawProfile_eq_merProfile_of_smooth (h : UnforcedLeray.Short.PartI.TrainStreamSmooth)
    {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) (T : UnforcedLeray.B0140.TrainSol ν c)
    (hT : UnforcedLeray.Short.PartI.IsBUCTrain T) {R ε : ℝ} (hε : ε = R⁻¹) {x : ℝ × (ℝ × ℝ)} (hx : 0 < x.1) :
    UnforcedLeray.Cons.C03.rawProfile ε T.v T.ψ x = merProfile R (trainProfile T.ψ) x := by
  set x' : ProfilePoint := (x.2.1, (x.2.2, x.1)) with hx'
  have hd : DifferentiableAt ℝ (trainProfile T.ψ) x' :=
    trainProfile_differentiableAt_of_smooth h hν hc T hT (show 0 < x'.2.2 from hx)
  have hV1 := streamV1_trainProfile T (show 0 ≤ x'.2.2 from hx.le) hd
  have hV2 := streamV2_trainProfile T (show 0 ≤ x'.2.2 from hx.le) hd
  have hE := partialEta_trainProfile T hd
  have hA := partialAge_trainProfile T hd
  have hH : UnforcedLeray.Cons.C03.raisedStream T.ψ x.1 x.2.1 x.2.2 = ageDefect (trainProfile T.ψ) x' := by
    unfold UnforcedLeray.Cons.C03.raisedStream ageDefect ageOperator
    rw [hE, hA]
    rfl
  have hε' : ε = ringEps R := hε
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, UnforcedLeray.Cons.C03.rawProfile_zero, merProfile, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Axi.m0_zero, Axi.m1_zero, mul_one, mul_zero, add_zero]
    exact hV1.symm
  · simp only [Fin.mk_one, UnforcedLeray.Cons.C03.rawProfile_one, merProfile, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Axi.m0_one, Axi.m1_one, mul_one, mul_zero, zero_add, axialProfile]
    rw [hV2, hH, hε']

/-- **`PartII-b:R1/5`, conditional form**: `U_raw` is the ring lift of the actual train, assuming
the joint smoothness `PartI.TrainStreamSmooth` of the decaying stream for positive age. -/
theorem rawIsRingLift_of (h : UnforcedLeray.Short.PartI.TrainStreamSmooth) : RawIsRingLift := by
  intro p hb τ y hy
  have hyax : y ∉ Axi.axis := fun h' => hy ((Axi.mem_axis_iff y).1 h')
  have hR : 0 < p.R := p.R_pos
  have hRε : p.ε = p.R⁻¹ := by
    show p.ε = (p.ε⁻¹)⁻¹
    exact (inv_inv _).symm
  rw [p.raw_eq_off_axis τ y hyax, simProfile_liftVelocity_eq_Nv hR _ τ hyax]
  have hs : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos hR.ne' hyax
  have hprof := rawProfile_eq_merProfile_of_smooth h p.ν_pos p.c_pos p.train hb hRε hs
  change Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ y =
    Axi.Nv p.R (merProfile p.R (trainStream p)) τ y
  unfold Axi.Nv
  rw [hprof]
  rfl

end UnforcedLeray.Short.IIb
