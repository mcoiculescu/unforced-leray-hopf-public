import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_4
import UnforcedLeray.Short.PartIIb.Sub.R1_5

/-!
# Part II-b, task `PartII-b:G4/3/4/2` (`RawProfDiffAt`)

Source of record: `the November 2 reference manuscript`, SP 1206-1216, 2419.
On `s > 0` the raw profile `rawProf p = (v₁, v₂ + εH)` is the profile `merProfile R ψ̃` of the
B0185 lift (the identity of `rawProfile_eq_merProfile_of_smooth`, with the joint smoothness
supplied by `BgRegime.train_stream_smooth` instead of `PartI.TrainStreamSmooth`), and
`merProfile` is differentiable wherever the train stream is `C²` there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0184 UnforcedLeray.B0185
  UnforcedLeray.B0190

/-- The train profile is `C^∞` at a point of positive age (from `BgRegime`). -/
theorem rawDiff_trainProfile_contDiffAt {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp)
    {x : ProfilePoint} (hx : 0 < x.2.2) :
    ContDiffAt ℝ ∞ (trainProfile p.train.ψ) x := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (x.2.2, (x.1, x.2.1)) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    Set.mk_mem_prod hx (Set.mem_univ _)
  have hat : ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => p.train.ψ z.1 z.2) (x.2.2, (x.1, x.2.1)) :=
    hb.train_stream_smooth.contDiffAt (hopen.mem_nhds hmem)
  have hg : ContDiff ℝ ∞ (fun y : ProfilePoint => (y.2.2, (y.1, y.2.1))) := by fun_prop
  exact hat.comp x hg.contDiffAt

/-- Partial derivatives of a `C^∞` profile at a point are differentiable there. -/
theorem rawDiff_fderiv_apply {f : ProfilePoint → ℝ} {z : ProfilePoint} (hf : ContDiffAt ℝ ∞ f z)
    (v : ProfilePoint) : DifferentiableAt ℝ (fun w => fderiv ℝ f w v) z :=
  ((hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).clm_apply
    (differentiableAt_const _)

theorem rawDiff_ageOp_diffAt {f : ProfilePoint → ℝ} {z : ProfilePoint} (hf : ContDiffAt ℝ ∞ f z) :
    DifferentiableAt ℝ (fun w => ageOperator f w) z := by
  unfold ageOperator partialEta partialAge
  exact ((by fun_prop : DifferentiableAt ℝ (fun w : ProfilePoint => w.2.1) z).mul
      (rawDiff_fderiv_apply hf eηDir)).add
    ((by fun_prop : DifferentiableAt ℝ (fun w : ProfilePoint => 2 * w.2.2) z).mul
      (rawDiff_fderiv_apply hf esDir))

theorem rawDiff_ageDef_diffAt {f : ProfilePoint → ℝ} {z : ProfilePoint}
    (hf : ContDiffAt ℝ ∞ f z) :
    DifferentiableAt ℝ (fun w => ageDefect f w) z := by
  unfold ageDefect
  exact (hf.differentiableAt (by simp)).sub (rawDiff_ageOp_diffAt hf)

/-- The raw profile equals the lift profile on `s > 0` (SP 1206-1216; the proof of
`rawProfile_eq_merProfile_of_smooth` with the smoothness from `BgRegime`). -/
theorem rawProf_eq_merProfile_of_contDiff {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp)
    {x : ℝ × (ℝ × ℝ)} (hx : 0 < x.1) :
    UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ x =
      merProfile p.R (trainProfile p.train.ψ) x := by
  have hRε : p.ε = p.R⁻¹ := by
    show p.ε = (p.ε⁻¹)⁻¹
    exact (inv_inv _).symm
  set x' : ProfilePoint := (x.2.1, (x.2.2, x.1)) with hx'
  have hd : DifferentiableAt ℝ (trainProfile p.train.ψ) x' :=
    (rawDiff_trainProfile_contDiffAt hb (show 0 < x'.2.2 from hx)).differentiableAt (by simp)
  have hV1 := streamV1_trainProfile p.train (show 0 ≤ x'.2.2 from hx.le) hd
  have hV2 := streamV2_trainProfile p.train (show 0 ≤ x'.2.2 from hx.le) hd
  have hE := partialEta_trainProfile p.train hd
  have hA := partialAge_trainProfile p.train hd
  have hH : UnforcedLeray.Cons.C03.raisedStream p.train.ψ x.1 x.2.1 x.2.2 =
      ageDefect (trainProfile p.train.ψ) x' := by
    unfold UnforcedLeray.Cons.C03.raisedStream ageDefect ageOperator
    rw [hE, hA]
    rfl
  have hε' : p.ε = ringEps p.R := hRε
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, UnforcedLeray.Cons.C03.rawProfile_zero, merProfile, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Axi.m0_zero, Axi.m1_zero, mul_one, mul_zero, add_zero]
    exact hV1.symm
  · simp only [Fin.mk_one, UnforcedLeray.Cons.C03.rawProfile_one, merProfile, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Axi.m0_one, Axi.m1_one, mul_one, mul_zero, zero_add,
      axialProfile]
    rw [hV2, hH, hε']

/-- The lift profile is differentiable at every chart point of positive age. -/
theorem rawDiff_merProfile_diffAt {R : ℝ} {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp)
    {x : ℝ × (ℝ × ℝ)} (hx : 0 < x.1) :
    DifferentiableAt ℝ (merProfile R (trainProfile p.train.ψ)) x := by
  have hC : ContDiffAt ℝ ∞ (trainProfile p.train.ψ) (x.2.1, (x.2.2, x.1)) :=
    rawDiff_trainProfile_contDiffAt hb (show 0 < (x.2.1, (x.2.2, x.1)).2.2 from hx)
  have h1 : DifferentiableAt ℝ (fun w => streamV1 (trainProfile p.train.ψ) w)
      (x.2.1, (x.2.2, x.1)) := by
    unfold streamV1 partialEta
    exact (rawDiff_fderiv_apply hC eηDir).neg
  have h2 : DifferentiableAt ℝ (fun w => axialProfile R (trainProfile p.train.ψ) w)
      (x.2.1, (x.2.2, x.1)) := by
    unfold axialProfile streamV2 partialQ
    exact (rawDiff_fderiv_apply hC eqDir).add
      ((differentiableAt_const (ringEps R)).mul (rawDiff_ageDef_diffAt hC))
  have hF : DifferentiableAt ℝ (fun w : ProfilePoint =>
      streamV1 (trainProfile p.train.ψ) w • Axi.m0 +
        axialProfile R (trainProfile p.train.ψ) w • Axi.m1) (x.2.1, (x.2.2, x.1)) :=
    (h1.smul_const Axi.m0).add (h2.smul_const Axi.m1)
  have hg : DifferentiableAt ℝ (fun y : ℝ × (ℝ × ℝ) => (y.2.1, (y.2.2, y.1))) x := by
    fun_prop
  show DifferentiableAt ℝ ((fun w : ProfilePoint =>
      streamV1 (trainProfile p.train.ψ) w • Axi.m0 +
        axialProfile R (trainProfile p.train.ψ) w • Axi.m1) ∘
      (fun y : ℝ × (ℝ × ℝ) => (y.2.1, (y.2.2, y.1)))) x
  exact DifferentiableAt.comp x hF hg

/-- **Differentiability of the raw profile** `b_raw = (v₁, v₂ + εH)` on `s > 0`
(`BgRegime.train_stream_smooth`, SP 1206-1216, 2419). -/
theorem rawProfDiffAt : UnforcedLeray.Short.IIb.RawProfDiffAt := by
  intro dm dp p d hb m hm
  have hopen : {x : Coord | 0 < x.1} ∈ 𝓝 m :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (show 0 < m.1 from hm)
  have hL : rawProf p =ᶠ[𝓝 m] merProfile p.R (trainProfile p.train.ψ) := by
    filter_upwards [hopen] with x hx
    exact rawProf_eq_merProfile_of_contDiff hb hx
  exact (rawDiff_merProfile_diffAt hb hm).congr_of_eventuallyEq hL

end UnforcedLeray.Short.IIb
