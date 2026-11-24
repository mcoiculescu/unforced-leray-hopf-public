import UnforcedLeray.Short.PartIIb.Sub.P1
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm

/-!
# Part II-b, task `PartII-b:P1/2`: the norm factor of the body lift

Source of record: `the November 2 reference manuscript`, lines 1902-1906.
If `rep f =ᵃᵉ N_v (toProf g)` then `‖f‖_Y = (πR²)^{1/p} ‖g‖_{H_p}`.

Uses `PartII-b:T07` (`phaseLpNorm_NvC`, `Tasks/NvCNorm.lean`). Helper facts proved here:
the complex lift `liftM` of a real meridional vector is isometric and continuous;
`toProf c g` is `c`-periodic everywhere and agrees with the lift of `g` almost everywhere on the
`H_p` measure; the `Y_q` norm is the phase-normalised `L^q` norm of `rep f`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- The complex lift of a real meridional vector (coordinatewise inclusion). -/
def liftM (v : Axi.Merid) : CMerid := WithLp.toLp 2 fun i => ((v i : ℝ) : ℂ)

theorem liftM_norm (v : Axi.Merid) : ‖liftM v‖ = ‖v‖ := by
  unfold liftM
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two]

theorem continuous_liftM : Continuous liftM := by
  unfold liftM
  fun_prop

/-- `q`-cell wrapping is the identity on the centred cell. -/
theorem qwrap_of_mem {c q : ℝ} (hc : 0 < c) (hq : q ∈ Ico (-c / 2) (c / 2)) :
    qwrap c q = q := by
  unfold qwrap
  have h0 : 0 ≤ (q + c / 2) / c := div_nonneg (by linarith [hq.1]) hc.le
  have h1 : (q + c / 2) / c < 1 := (div_lt_one hc).2 (by linarith [hq.2])
  rw [Int.floor_eq_zero_iff.2 ⟨h0, h1⟩]
  simp

/-- `qwrap` is `c`-periodic. -/
theorem qwrap_add_c {c q : ℝ} (hc : 0 < c) : qwrap c (q + c) = qwrap c q := by
  unfold qwrap
  have h : (q + c + c / 2) / c = (q + c / 2) / c + 1 := by
    rw [div_add_one hc.ne']
    congr 1
    ring
  rw [h, Int.floor_add_one]
  push_cast
  ring

/-- `toProf c g` is `c`-periodic in `q` (everywhere). -/
theorem toProf_periodic {c : ℝ} (hc : 0 < c) (g : HpR c) : QPeriodic c (toProf c g) := by
  unfold QPeriodic
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [toProf, qShift, qwrap_add_c hc]

/-- `toProf c g` is the complex lift of `g` almost everywhere on `H_p`. -/
theorem toProf_ae_eq {c : ℝ} (hc : 0 < c) (g : HpR c) :
    toProf c g =ᵐ[hMeas c bgp] fun x => liftM ((g : Coord → Axi.Merid) x) := by
  filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with p hp
  have hm : p.2.1 ∈ Ico (-c / 2) (c / 2) := (Set.mem_prod.1 hp.2).1
  have hq : qwrap c p.2.1 = p.2.1 := qwrap_of_mem hc hm
  simp only [toProf, liftM, hq, Prod.mk.eta]

theorem toProf_aestronglyMeasurable {c : ℝ} (hc : 0 < c) (g : HpR c) :
    AEStronglyMeasurable (toProf c g) (hMeas c bgp) := by
  have h1 : AEStronglyMeasurable (fun x : Coord => liftM ((g : Coord → Axi.Merid) x))
      (hMeas c bgp) :=
    continuous_liftM.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g)
  exact h1.congr (toProf_ae_eq hc g).symm

theorem hNorm_toProf {c : ℝ} (hc : 0 < c) (g : HpR c) :
    hNorm c bgp (toProf c g) = ‖g‖ₑ := by
  rw [Lp.enorm_def]
  unfold hNorm
  rw [eLpNorm_congr_ae (toProf_ae_eq hc g)]
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => liftM_norm _)

/-- The phase-normalised norm only depends on the a.e. class of the field. -/
theorem phaseLpNorm_congr_ae' {P r : ℝ} {F G : ℝ × Space → CVec3}
    (h : ∀ᵐ x : ℝ × Space, F x = G x) : phaseLpNorm P r F = phaseLpNorm P r G := by
  unfold phaseLpNorm
  have h' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), F x = G x := by
    rw [← Measure.volume_eq_prod]
    exact h
  have h2 := Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => F z = G z) h'
  have hI : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖F (t, y)‖ₑ ^ r =
      ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖G (t, y)‖ₑ ^ r := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae h2] with t ht
    refine lintegral_congr_ae ?_
    filter_upwards [ht] with y hy
    rw [hy]
  rw [hI]

/-- The `Y_q` norm is the phase-normalised `L^q` norm of its joint representative. -/
theorem enorm_eq_phaseLpNorm_rep {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (f : Yq P q) :
    ‖f‖ₑ = phaseLpNorm P q.toReal (fun x => rep f x.1 x.2) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le one_pos hq1)) hq
  have hslice : ∀ t : ℝ, ∫⁻ y : Space, ‖rep f t y‖ₑ ^ q.toReal =
      ‖(f (t : AddCircle P) : Lp CVec3 q (volume : Measure Space))‖ₑ ^ q.toReal := by
    intro t
    rw [← lintegral_enorm_rpow_Lp (f (t : AddCircle P)) hq]
    refine lintegral_congr_ae ?_
    filter_upwards [rep_slice f t] with y hy
    rw [hy]
  have key : ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖rep f t y‖ₑ ^ q.toReal =
      ‖f‖ₑ ^ q.toReal := by
    simp only [hslice]
    rw [enorm_rpow_Yq f hq]
  unfold phaseLpNorm
  rw [key, one_div, ← ENNReal.rpow_mul, mul_inv_cancel₀ hq0.ne', ENNReal.rpow_one]

theorem q0E_toReal : q0E.toReal = bgp := by
  unfold q0E
  rw [ENNReal.toReal_ofReal (by norm_num [B0281.q0])]
  norm_num [B0281.q0, bgp]

theorem q0E_ne_top' : q0E ≠ ⊤ := by
  unfold q0E
  exact ENNReal.ofReal_ne_top

/-- **`PartII-b:P1/2`** (SP 1902-1906): if `rep f = N_v (toProf g)` a.e., then
`‖f‖_Y = (πR²)^{1/p} ‖g‖_{H_p}`. -/
theorem bodyLiftNorm_proof : BodyLiftNorm := by
  intro dm dp hdm p d hreg f g hrep
  have hc : 0 < p.c := p.c_pos
  have hε : 0 < p.ε := p.ε_pos
  have hr : 0 < bgp := by norm_num [bgp]
  have h1 : ‖(f : Yq p.period q0E)‖ₑ =
      phaseLpNorm p.period bgp (fun x => rep (f : Yq p.period q0E) x.1 x.2) := by
    rw [enorm_eq_phaseLpNorm_rep q0E_ne_top' (f : Yq p.period q0E), q0E_toReal]
  have h2 : phaseLpNorm p.period bgp (fun x => rep (f : Yq p.period q0E) x.1 x.2) =
      phaseLpNorm p.period bgp (NvC p.R (toProf p.c g)) :=
    phaseLpNorm_congr_ae' hrep
  have h3 : phaseLpNorm p.period bgp (NvC p.R (toProf p.c g)) =
      ENNReal.ofReal ((Real.pi * p.R ^ 2) ^ (1 / bgp)) * hNorm p.c bgp (toProf p.c g) :=
    phaseLpNorm_NvC hc hr hε (toProf p.c g) (toProf_periodic hc g)
      (toProf_aestronglyMeasurable hc g)
  have h4 : ‖(f : Yq p.period q0E)‖ₑ =
      ENNReal.ofReal ((Real.pi * p.R ^ 2) ^ (1 / bgp)) * ‖g‖ₑ := by
    rw [h1, h2, h3, hNorm_toProf hc g]
  have hK : 0 ≤ (Real.pi * p.R ^ 2) ^ (1 / bgp) := by
    have : 0 < p.R := p.R_pos
    positivity
  calc ‖f‖ = ‖(f : Yq p.period q0E)‖ₑ.toReal := (toReal_enorm _).symm
    _ = (ENNReal.ofReal ((Real.pi * p.R ^ 2) ^ (1 / bgp)) * ‖g‖ₑ).toReal :=
        congrArg ENNReal.toReal h4
    _ = (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖g‖ₑ.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK]
    _ = (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖g‖ := congrArg _ (toReal_enorm g)

end UnforcedLeray.Short.IIb
