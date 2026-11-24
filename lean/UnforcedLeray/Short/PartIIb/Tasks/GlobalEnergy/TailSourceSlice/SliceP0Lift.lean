import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2_2
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvWeakLeibniz
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvSliceGoodAe.JointWeak
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.PeriodizeTest
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.P0Rep
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0DivFreeC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0OrthC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0CommWeakC

/-!
# `SliceP0Lift`: Jointly measurable `q`-periodic lift of `-P_0` on `H¹(C_c)` slices

Source of record: `the November 2 reference manuscript` (SP), lines 2213–2239
and 2269–2282 (`g = -P_0(v_c · ∇b_0 + b_0 · ∇v_c)`).

Given `U = flatBv tr b0' b0q b0η` and its formal Leibniz derivatives `Uq`, `Uη` with joint weak
derivatives `HasWeakVec vQ0 dZero U Uq`, `HasWeakVec vEta dZero U Uη`, and local-in-`s`
integrability `∀ a b, 0 < a → ∫⁻ s in Icc a b, sliceH1Norm c U Uq Uη s < ⊤`, we construct
jointly strongly measurable `c`-periodic profiles `g, gq, gη : CProf` representing `-P_0 U(s, ·)`
and its spatial derivatives on every good slice `s > 0`, satisfying:
* `QPeriodic c g`, `HasWeakVec vQ0 dZero g gq`, `HasWeakVec vEta dZero g gη`,
* `IsBodySource tr b0' b0q b0η g`,
* `∀ s > 0, sliceH1Norm c g gq gη s ≤ ENNReal.ofReal 2 * sliceH1Norm c U Uq Uη s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.TailSliceP0LiftAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIb.CylProjectionSub

/-! ### 1. Periodic cell retraction `toCell c : Plane → Plane` -/

private def toCell (c : ℝ) (z : B0579.Plane) : B0579.Plane :=
  (z.1 - c * (⌊(z.1 + c / 2) / c⌋ : ℝ), z.2)

private theorem measurable_toCell (c : ℝ) : Measurable (toCell c) := by
  unfold toCell
  have hfl : Measurable (fun z : B0579.Plane => (⌊(z.1 + c / 2) / c⌋ : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (((measurable_fst.add measurable_const).div_const c).floor)
  exact (measurable_fst.sub (measurable_const.mul hfl)).prodMk measurable_snd

private theorem toCell_periodic {c : ℝ} (hc : 0 < c) (z : B0579.Plane) :
    toCell c (z.1 + c, z.2) = toCell c z := by
  unfold toCell
  ext
  · dsimp only
    have hdiv : (z.1 + c + c / 2) / c = (z.1 + c / 2) / c + 1 := by
      field_simp [hc.ne']
      ring
    rw [hdiv, Int.floor_add_one]
    push_cast
    ring
  · rfl

private theorem toCell_eq_self_of_mem_cell {c : ℝ} (hc : 0 < c) {z : B0579.Plane}
    (hz : z ∈ B0579.cell c) : toCell c z = z := by
  have hlo : 0 ≤ (z.1 + c / 2) / c := div_nonneg (by linarith [hz.1.1]) hc.le
  have hhi : (z.1 + c / 2) / c < 1 := (div_lt_one hc).2 (by linarith [hz.1.2])
  have hfl : ⌊(z.1 + c / 2) / c⌋ = 0 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using hlo, by simpa using hhi⟩
  ext
  · simp [toCell, hfl]
  · rfl

/-! ### 2. Truncation to `0 < x.1` and measurability / periodicity of `flatBv`, `flatBvQ`, `flatBvEta` -/

private def posSet : Set Coord := {x : Coord | 0 < x.1}

private theorem measurableSet_posSet : MeasurableSet posSet :=
  (isOpen_lt continuous_const continuous_fst).measurableSet

private def posInd (w : CProf) : CProf := posSet.indicator w

private theorem stronglyMeasurable_posInd {w : CProf} (hw : StronglyMeasurable w) :
    StronglyMeasurable (posInd w) :=
  hw.indicator measurableSet_posSet

private theorem posInd_eq_of_pos (w : CProf) {x : Coord} (hx : 0 < x.1) :
    posInd w x = w x :=
  Set.indicator_of_mem (s := posSet) hx w

private theorem posInd_eq_zero_of_nonpos (w : CProf) {x : Coord} (hx : ¬ 0 < x.1) :
    posInd w x = 0 :=
  Set.indicator_of_notMem (s := posSet) hx w

private theorem measurable_posInd_real {f : Coord → ℝ} (hf : ContinuousOn f posSet) :
    Measurable (posSet.indicator f) := by
  classical
  have hpw : posSet.indicator f = posSet.piecewise f 0 := by
    funext x
    by_cases hx : x ∈ posSet <;> simp [hx, Set.piecewise]
  rw [hpw]
  exact hf.measurable_piecewise continuousOn_const measurableSet_posSet

private theorem continuousOn_tr_v {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) :
    ContinuousOn (fun x : Coord => tr.v x.1 x.2 k) posSet := by
  have h := (FlatBvWL.gC_contDiffOn tr k).continuousOn
  have heq : FlatBvWL.U0 = posSet := by
    ext x; simp [FlatBvWL.U0, posSet]
  rwa [heq] at h

private theorem continuousOn_trD1 {ν c : ℝ} (tr : B0140.TrainSol ν c) (d : ℝ × ℝ) (k : Fin 2) :
    ContinuousOn (fun x : Coord => trD1 tr d x.1 x.2 k) posSet := by
  have h := (FlatBvWL.gD_contDiffOn tr k d).continuousOn
  have heq : FlatBvWL.U0 = posSet := by
    ext x; simp [FlatBvWL.U0, posSet]
  rw [heq] at h
  exact h.congr fun x hx => (FlatBvWL.gD_eq tr k d hx).symm

private theorem continuousOn_trD2 {ν c : ℝ} (tr : B0140.TrainSol ν c) (d e : ℝ × ℝ) (k : Fin 2) :
    ContinuousOn (fun x : Coord => trD2 tr d e x.1 x.2 k) posSet := by
  have h := (((FlatBvWL.gD_contDiffOn tr k d).fderiv_of_isOpen FlatBvWL.isOpen_U0
    (m := ∞) (by simp)).clm_apply (contDiffOn_const (c := ((0 : ℝ), e)))).continuousOn
  have heq : FlatBvWL.U0 = posSet := by
    ext x; simp [FlatBvWL.U0, posSet]
  rw [heq] at h
  exact h.congr fun x hx => FlatBvWL.trD2_eq tr d e k hx

private theorem stronglyMeasurable_of_coords {W : CProf}
    (h : ∀ i : Fin 2, Measurable (fun x : Coord => W x i)) : StronglyMeasurable W := by
  have hm : Measurable W := by
    have heq : W = fun x => WithLp.toLp 2 (fun i : Fin 2 => W x i) := funext fun x => rfl
    rw [heq]
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ h)
  exact hm.stronglyMeasurable

private theorem meas_mul_term {A : Coord → ℝ} (hA : ContinuousOn A posSet)
    {w : CProf} (hw : StronglyMeasurable w) (i : Fin 2) :
    Measurable (fun x : Coord => posSet.indicator (fun y => (A y : ℂ) * w y i) x) := by
  have heq : (fun x : Coord => posSet.indicator (fun y => (A y : ℂ) * w y i) x) =
      fun x => ((posSet.indicator A x : ℝ) : ℂ) *
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ) (posInd w x)) := by
    funext x
    by_cases hx : x ∈ posSet
    · simp [posInd, hx]
    · simp [posInd, hx]
  rw [heq]
  exact (Complex.measurable_ofReal.comp (measurable_posInd_real hA)).mul
    (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_posInd hw)).measurable)

private theorem meas_mul_term_rev {A : Coord → ℝ} (hA : ContinuousOn A posSet)
    {w : CProf} (hw : StronglyMeasurable w) (i : Fin 2) :
    Measurable (fun x : Coord => posSet.indicator (fun y => w y i * (A y : ℂ)) x) := by
  have heq : (fun x : Coord => posSet.indicator (fun y => w y i * (A y : ℂ)) x) =
      fun x => posSet.indicator (fun y => (A y : ℂ) * w y i) x := by
    funext x; by_cases hx : x ∈ posSet <;> simp [hx, mul_comm]
  rw [heq]
  exact meas_mul_term hA hw i

private theorem stronglyMeasurable_posInd_flatBv {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {b0' b0q b0η : CProf} (h0 : StronglyMeasurable b0')
    (hq : StronglyMeasurable b0q) (hη : StronglyMeasurable b0η) :
    StronglyMeasurable (posInd (flatBv tr b0' b0q b0η)) := by
  refine stronglyMeasurable_of_coords fun i => ?_
  have heq : (fun x : Coord => posInd (flatBv tr b0' b0q b0η) x i) = fun x =>
      posSet.indicator (fun y => ((tr.v y.1 y.2 0 : ℝ) : ℂ) * b0q y i) x +
      posSet.indicator (fun y => ((tr.v y.1 y.2 1 : ℝ) : ℂ) * b0η y i) x +
      posSet.indicator (fun y => b0' y 0 * ((trD1 tr (1, 0) y.1 y.2 i : ℝ) : ℂ)) x +
      posSet.indicator (fun y => b0' y 1 * ((trD1 tr (0, 1) y.1 y.2 i : ℝ) : ℂ)) x := by
    funext x
    by_cases hx : x ∈ posSet
    · simp [posInd, hx, FlatBvWL.flatBv_apply]
    · simp [posInd, hx]
  rw [heq]
  exact (((meas_mul_term (continuousOn_tr_v tr 0) hq i).add
    (meas_mul_term (continuousOn_tr_v tr 1) hη i)).add
    (meas_mul_term_rev (continuousOn_trD1 tr (1, 0) i) h0 0)).add
    (meas_mul_term_rev (continuousOn_trD1 tr (0, 1) i) h0 1)

private theorem stronglyMeasurable_posInd_flatBvQ {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {b0' b0q b0η d00 d10 : CProf} (h0 : StronglyMeasurable b0')
    (hq : StronglyMeasurable b0q) (hη : StronglyMeasurable b0η)
    (hd00 : StronglyMeasurable d00) (hd10 : StronglyMeasurable d10) :
    StronglyMeasurable (posInd (flatBvQ tr b0' b0q b0η d00 d10)) := by
  refine stronglyMeasurable_of_coords fun i => ?_
  have heq : (fun x : Coord => posInd (flatBvQ tr b0' b0q b0η d00 d10) x i) = fun x =>
      posSet.indicator (fun y => ((trD1 tr (1, 0) y.1 y.2 0 : ℝ) : ℂ) * b0q y i) x +
      posSet.indicator (fun y => ((tr.v y.1 y.2 0 : ℝ) : ℂ) * d00 y i) x +
      posSet.indicator (fun y => ((trD1 tr (1, 0) y.1 y.2 1 : ℝ) : ℂ) * b0η y i) x +
      posSet.indicator (fun y => ((tr.v y.1 y.2 1 : ℝ) : ℂ) * d10 y i) x +
      posSet.indicator (fun y => b0q y 0 * ((trD1 tr (1, 0) y.1 y.2 i : ℝ) : ℂ)) x +
      posSet.indicator (fun y => b0' y 0 * ((trD2 tr (1, 0) (1, 0) y.1 y.2 i : ℝ) : ℂ)) x +
      posSet.indicator (fun y => b0q y 1 * ((trD1 tr (0, 1) y.1 y.2 i : ℝ) : ℂ)) x +
      posSet.indicator (fun y => b0' y 1 * ((trD2 tr (0, 1) (1, 0) y.1 y.2 i : ℝ) : ℂ)) x := by
    funext x
    by_cases hx : x ∈ posSet
    · simp [posInd, hx, FlatBvWL.flatBvQ_apply]
    · simp [posInd, hx]
  rw [heq]
  exact (((((((meas_mul_term (continuousOn_trD1 tr (1, 0) 0) hq i).add
    (meas_mul_term (continuousOn_tr_v tr 0) hd00 i)).add
    (meas_mul_term (continuousOn_trD1 tr (1, 0) 1) hη i)).add
    (meas_mul_term (continuousOn_tr_v tr 1) hd10 i)).add
    (meas_mul_term_rev (continuousOn_trD1 tr (1, 0) i) hq 0)).add
    (meas_mul_term_rev (continuousOn_trD2 tr (1, 0) (1, 0) i) h0 0)).add
    (meas_mul_term_rev (continuousOn_trD1 tr (0, 1) i) hq 1)).add
    (meas_mul_term_rev (continuousOn_trD2 tr (0, 1) (1, 0) i) h0 1)

private theorem stronglyMeasurable_posInd_flatBvEta {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {b0' b0q b0η d01 d11 : CProf} (h0 : StronglyMeasurable b0')
    (hq : StronglyMeasurable b0q) (hη : StronglyMeasurable b0η)
    (hd01 : StronglyMeasurable d01) (hd11 : StronglyMeasurable d11) :
    StronglyMeasurable (posInd (flatBvEta tr b0' b0q b0η d01 d11)) := by
  refine stronglyMeasurable_of_coords fun i => ?_
  have heq : (fun x : Coord => posInd (flatBvEta tr b0' b0q b0η d01 d11) x i) = fun x =>
      posSet.indicator (fun y => ((trD1 tr (0, 1) y.1 y.2 0 : ℝ) : ℂ) * b0q y i) x +
      posSet.indicator (fun y => ((tr.v y.1 y.2 0 : ℝ) : ℂ) * d01 y i) x +
      posSet.indicator (fun y => ((trD1 tr (0, 1) y.1 y.2 1 : ℝ) : ℂ) * b0η y i) x +
      posSet.indicator (fun y => ((tr.v y.1 y.2 1 : ℝ) : ℂ) * d11 y i) x +
      posSet.indicator (fun y => b0η y 0 * ((trD1 tr (1, 0) y.1 y.2 i : ℝ) : ℂ)) x +
      posSet.indicator (fun y => b0' y 0 * ((trD2 tr (1, 0) (0, 1) y.1 y.2 i : ℝ) : ℂ)) x +
      posSet.indicator (fun y => b0η y 1 * ((trD1 tr (0, 1) y.1 y.2 i : ℝ) : ℂ)) x +
      posSet.indicator (fun y => b0' y 1 * ((trD2 tr (0, 1) (0, 1) y.1 y.2 i : ℝ) : ℂ)) x := by
    funext x
    by_cases hx : x ∈ posSet
    · simp [posInd, hx, FlatBvWL.flatBvEta_apply]
    · simp [posInd, hx]
  rw [heq]
  exact (((((((meas_mul_term (continuousOn_trD1 tr (0, 1) 0) hq i).add
    (meas_mul_term (continuousOn_tr_v tr 0) hd01 i)).add
    (meas_mul_term (continuousOn_trD1 tr (0, 1) 1) hη i)).add
    (meas_mul_term (continuousOn_tr_v tr 1) hd11 i)).add
    (meas_mul_term_rev (continuousOn_trD1 tr (1, 0) i) hη 0)).add
    (meas_mul_term_rev (continuousOn_trD2 tr (1, 0) (0, 1) i) h0 0)).add
    (meas_mul_term_rev (continuousOn_trD1 tr (0, 1) i) hη 1)).add
    (meas_mul_term_rev (continuousOn_trD2 tr (0, 1) (0, 1) i) h0 1)

private theorem qPeriodic_of_sqrtS {c : ℝ} {w : CProf} (hw : QPeriodic c (sqrtS w)) :
    QPeriodic c w := by
  filter_upwards [hw, ae_restrict_mem measurableSet_posSet] with x hx hpos
  have hc0 : (Real.sqrt x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne'
  have h1 : (Real.sqrt x.1 : ℂ) • w (qShift c x) = (Real.sqrt x.1 : ℂ) • w x := by
    simpa [sqrtS, qShift] using hx
  exact smul_right_injective _ hc0 h1

private theorem qPeriodic_of_mulS {c : ℝ} {w : CProf} (hw : QPeriodic c (mulS w)) :
    QPeriodic c w := by
  filter_upwards [hw, ae_restrict_mem measurableSet_posSet] with x hx hpos
  have hc0 : (x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  have h1 : (x.1 : ℂ) • w (qShift c x) = (x.1 : ℂ) • w x := by
    simpa [mulS, qShift] using hx
  exact smul_right_injective _ hc0 h1

private theorem qPeriodic_posInd {c : ℝ} {w : CProf} (hw : QPeriodic c w) :
    QPeriodic c (posInd w) := by
  filter_upwards [hw, ae_restrict_mem measurableSet_posSet] with x hx hpos
  have hpos' : 0 < (qShift c x).1 := hpos
  rw [posInd_eq_of_pos w hpos', posInd_eq_of_pos w hpos]
  exact hx

private theorem fderiv_periodic_plane {c : ℝ} {f : B0579.Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : ∀ z : B0579.Plane, f (z.1 + c, z.2) = f z)
    (d : ℝ × ℝ) (z : B0579.Plane) :
    fderiv ℝ f (z.1 + c, z.2) d = fderiv ℝ f z d := by
  have hshift : HasFDerivAt (fun w : B0579.Plane => w + (c, (0 : ℝ)))
      (ContinuousLinearMap.id ℝ B0579.Plane) z := by
    simpa using (hasFDerivAt_id z).add_const (c, (0 : ℝ))
  have hdiff : DifferentiableAt ℝ f (z + (c, (0 : ℝ))) :=
    (hf.differentiable (by simp)).differentiableAt
  have hcomp := hdiff.hasFDerivAt.comp z hshift
  have hfun : (f ∘ fun w : B0579.Plane => w + (c, (0 : ℝ))) = f := by
    funext w
    change f (w.1 + c, w.2 + 0) = f w
    rw [add_zero, hper w]
  rw [hfun] at hcomp
  have heq : fderiv ℝ f z = fderiv ℝ f (z + (c, (0 : ℝ))) := by
    simpa using hcomp.fderiv
  have hz : (z.1 + c, z.2) = z + (c, (0 : ℝ)) := by ext <;> simp
  rw [hz, ← heq]

private theorem trD1_periodic {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (d : ℝ × ℝ) (z : B0579.Plane) (i : Fin 2) :
    trD1 tr d s (z.1 + c, z.2) i = trD1 tr d s z i :=
  fderiv_periodic_plane (contDiff_train_v_coord tr hs i)
    (fun w => congrArg (fun v => v i) (tr.isTrain.periodic_v s hs w)) d z

private theorem trD2_periodic {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (d e : ℝ × ℝ) (z : B0579.Plane) (i : Fin 2) :
    trD2 tr d e s (z.1 + c, z.2) i = trD2 tr d e s z i :=
  fderiv_periodic_plane (contDiff_trD1 tr d hs i)
    (fun w => trD1_periodic tr hs d w i) e z

private theorem qPeriodic_flatBv {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {b0' b0q b0η : CProf}
    (hp0 : QPeriodic c b0') (hpq : QPeriodic c b0q) (hpη : QPeriodic c b0η) :
    QPeriodic c (flatBv tr b0' b0q b0η) := by
  filter_upwards [hp0, hpq, hpη, ae_restrict_mem measurableSet_posSet] with x hx0 hxq hxη hpos
  have hs : 0 ≤ x.1 := le_of_lt hpos
  ext i
  simp only [FlatBvWL.flatBv_apply, qShift]
  change ((tr.v x.1 (x.2.1 + c, x.2.2) 0 : ℝ) : ℂ) * b0q (qShift c x) i +
      ((tr.v x.1 (x.2.1 + c, x.2.2) 1 : ℝ) : ℂ) * b0η (qShift c x) i +
      b0' (qShift c x) 0 * ((trD1 tr (1, 0) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) +
      b0' (qShift c x) 1 * ((trD1 tr (0, 1) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) = _
  rw [tr.isTrain.periodic_v x.1 hs x.2, trD1_periodic tr hs (1, 0) x.2 i,
    trD1_periodic tr hs (0, 1) x.2 i, hx0, hxq, hxη]

private theorem qPeriodic_flatBvQ {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {b0' b0q b0η d00 d10 : CProf}
    (hp0 : QPeriodic c b0') (hpq : QPeriodic c b0q) (hpη : QPeriodic c b0η)
    (hp00 : QPeriodic c d00) (hp10 : QPeriodic c d10) :
    QPeriodic c (flatBvQ tr b0' b0q b0η d00 d10) := by
  filter_upwards [hp0, hpq, hpη, hp00, hp10, ae_restrict_mem measurableSet_posSet]
    with x hx0 hxq hxη hx00 hx10 hpos
  have hs : 0 ≤ x.1 := le_of_lt hpos
  ext i
  simp only [FlatBvWL.flatBvQ_apply, qShift]
  change ((trD1 tr (1, 0) x.1 (x.2.1 + c, x.2.2) 0 : ℝ) : ℂ) * b0q (qShift c x) i +
      ((tr.v x.1 (x.2.1 + c, x.2.2) 0 : ℝ) : ℂ) * d00 (qShift c x) i +
      ((trD1 tr (1, 0) x.1 (x.2.1 + c, x.2.2) 1 : ℝ) : ℂ) * b0η (qShift c x) i +
      ((tr.v x.1 (x.2.1 + c, x.2.2) 1 : ℝ) : ℂ) * d10 (qShift c x) i +
      b0q (qShift c x) 0 * ((trD1 tr (1, 0) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) +
      b0' (qShift c x) 0 * ((trD2 tr (1, 0) (1, 0) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) +
      b0q (qShift c x) 1 * ((trD1 tr (0, 1) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) +
      b0' (qShift c x) 1 * ((trD2 tr (0, 1) (1, 0) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) = _
  rw [tr.isTrain.periodic_v x.1 hs x.2,
    trD1_periodic tr hs (1, 0) x.2 0, trD1_periodic tr hs (1, 0) x.2 1,
    trD1_periodic tr hs (1, 0) x.2 i, trD1_periodic tr hs (0, 1) x.2 i,
    trD2_periodic tr hs (1, 0) (1, 0) x.2 i, trD2_periodic tr hs (0, 1) (1, 0) x.2 i,
    hx0, hxq, hxη, hx00, hx10]

private theorem qPeriodic_flatBvEta {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {b0' b0q b0η d01 d11 : CProf}
    (hp0 : QPeriodic c b0') (hpq : QPeriodic c b0q) (hpη : QPeriodic c b0η)
    (hp01 : QPeriodic c d01) (hp11 : QPeriodic c d11) :
    QPeriodic c (flatBvEta tr b0' b0q b0η d01 d11) := by
  filter_upwards [hp0, hpq, hpη, hp01, hp11, ae_restrict_mem measurableSet_posSet]
    with x hx0 hxq hxη hx01 hx11 hpos
  have hs : 0 ≤ x.1 := le_of_lt hpos
  ext i
  simp only [FlatBvWL.flatBvEta_apply, qShift]
  change ((trD1 tr (0, 1) x.1 (x.2.1 + c, x.2.2) 0 : ℝ) : ℂ) * b0q (qShift c x) i +
      ((tr.v x.1 (x.2.1 + c, x.2.2) 0 : ℝ) : ℂ) * d01 (qShift c x) i +
      ((trD1 tr (0, 1) x.1 (x.2.1 + c, x.2.2) 1 : ℝ) : ℂ) * b0η (qShift c x) i +
      ((tr.v x.1 (x.2.1 + c, x.2.2) 1 : ℝ) : ℂ) * d11 (qShift c x) i +
      b0η (qShift c x) 0 * ((trD1 tr (1, 0) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) +
      b0' (qShift c x) 0 * ((trD2 tr (1, 0) (0, 1) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) +
      b0η (qShift c x) 1 * ((trD1 tr (0, 1) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) +
      b0' (qShift c x) 1 * ((trD2 tr (0, 1) (0, 1) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) = _
  rw [tr.isTrain.periodic_v x.1 hs x.2,
    trD1_periodic tr hs (0, 1) x.2 0, trD1_periodic tr hs (0, 1) x.2 1,
    trD1_periodic tr hs (1, 0) x.2 i, trD1_periodic tr hs (0, 1) x.2 i,
    trD2_periodic tr hs (1, 0) (0, 1) x.2 i, trD2_periodic tr hs (0, 1) (0, 1) x.2 i,
    hx0, hxq, hxη, hx01, hx11]

/-! ### 3. Jointly measurable `q`-periodic lift of `-P_0` for a single profile -/

private theorem exists_negP0_periodic_rep {c : ℝ} (hc : 0 < c)
    {S : Set ℝ} (hS : MeasurableSet S) {W : CProf} (hW : StronglyMeasurable W) :
    ∃ G : CProf, StronglyMeasurable G ∧ QPeriodic c G ∧
      (∀ s ∉ S, ∀ z : B0579.Plane, G (s, z) = 0) ∧
      (∀ s ∈ S, ∀ᵐ z ∂(volume.restrict (B0579.cell c)),
        G (s, z) = p0Merid c (fun y => -W (s, y)) z) := by
  classical
  have hYm : ∀ i : Fin 2, Measurable (fun p : Coord => -W p i) := fun i =>
    (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hW).neg).measurable
  obtain ⟨Yt, hYt_m, hYt_ae⟩ := UnforcedLeray.Short.IIIa.lmP0Rep c hc (fun p i => -W p i) hYm
  let G0 : CProf := fun x => WithLp.toLp 2 (Yt (x.1, toCell c x.2))
  have hG0_sm : StronglyMeasurable G0 := by
    refine stronglyMeasurable_of_coords fun i => ?_
    exact (hYt_m i).comp (measurable_fst.prodMk ((measurable_toCell c).comp measurable_snd))
  let G : CProf := fun x => if x.1 ∈ S then G0 x else 0
  have hG_sm : StronglyMeasurable G :=
    StronglyMeasurable.ite (measurable_fst hS) hG0_sm stronglyMeasurable_const
  have hG_per : QPeriodic c G := by
    refine Eventually.of_forall fun x => ?_
    dsimp [G, G0, qShift]
    rw [toCell_periodic hc x.2]
  refine ⟨G, hG_sm, hG_per, ?_, ?_⟩
  · intro s hs z
    simp [G, hs]
  · intro s hs
    filter_upwards [hYt_ae s, ae_restrict_mem (B0579.measurableSet_cell c)] with z hz hz_cell
    ext i
    simp only [G, G0, hs, ite_true, toCell_eq_self_of_mem_cell hc hz_cell]
    exact hz i

/-! ### 4. Slice helpers: `MemLp` of `reVec`/`imVec`, negation of `HasWeakCellDerivC`, and `hLoc` a.e. finiteness -/

private theorem memLp_reVec_imVec_of_lt_top {c : ℝ} {W : CProf} (hW : StronglyMeasurable W)
    {s : ℝ} (hfin : eLpNorm (fun z => W (s, z)) 2 (volume.restrict (B0579.cell c)) < ⊤) :
    MemLp (IIIa.reVec (fun z i => (-W (s, z)) i)) 2 (UnforcedLeray.Cyl.cellμ c) ∧
      MemLp (IIIa.imVec (fun z i => (-W (s, z)) i)) 2 (UnforcedLeray.Cyl.cellμ c) := by
  have hWs_m : Measurable (fun z : B0579.Plane => -W (s, z)) :=
    (hW.neg.measurable).comp (measurable_const.prodMk measurable_id)
  have hm_i : ∀ i : Fin 2, Measurable (fun z : B0579.Plane => (-W (s, z)) i) := fun i =>
    (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).measurable.comp hWs_m
  have hm_re : Measurable (IIIa.reVec (fun z i => (-W (s, z)) i)) := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
    fin_cases i
    · exact Complex.measurable_re.comp (hm_i 0)
    · exact Complex.measurable_re.comp (hm_i 1)
  have hm_im : Measurable (IIIa.imVec (fun z i => (-W (s, z)) i)) := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
    fin_cases i
    · exact Complex.measurable_im.comp (hm_i 0)
    · exact Complex.measurable_im.comp (hm_i 1)
  have hfin_neg : eLpNorm (fun z => -W (s, z)) 2 (UnforcedLeray.Cyl.cellμ c) < ⊤ := by
    rw [IIIa.cellμ_eq c]
    have heq : (fun z => -W (s, z)) = -(fun z => W (s, z)) := rfl
    rwa [heq, eLpNorm_neg]
  refine ⟨⟨hm_re.aestronglyMeasurable, ?_⟩, ⟨hm_im.aestronglyMeasurable, ?_⟩⟩
  ·exact ((eLpNorm_mono_real (norm_reVec_le (fun z => -W (s, z)))).trans_eq
      (eLpNorm_norm _)).trans_lt hfin_neg
  · exact ((eLpNorm_mono_real (norm_imVec_le (fun z => -W (s, z)))).trans_eq
      (eLpNorm_norm _)).trans_lt hfin_neg

private theorem hasWeakCellDerivC_neg {c : ℝ} {j : Fin 2} {φ g : B0579.Plane → ℂ}
    (h : IIIa.HasWeakCellDerivC c j φ g) :
    IIIa.HasWeakCellDerivC c j (fun z => -φ z) (fun z => -g z) := by
  obtain ⟨hint, heq⟩ := h
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have h1 : (fun z => -φ z * (B0579.pd j ψ z : ℂ)) =
        fun z => -(φ z * (B0579.pd j ψ z : ℂ)) := funext fun _ => neg_mul _ _
    have h2 : (fun z => -g z * (ψ z : ℂ)) =
        fun z => -(g z * (ψ z : ℂ)) := funext fun _ => neg_mul _ _
    rw [h1, h2]
    exact ⟨(hint ψ hψ).1.neg, (hint ψ hψ).2.neg⟩
  · have h1 : (fun z => -φ z * (B0579.pd j ψ z : ℂ)) =
        fun z => -(φ z * (B0579.pd j ψ z : ℂ)) := funext fun _ => neg_mul _ _
    have h2 : (fun z => -g z * (ψ z : ℂ)) =
        fun z => -(g z * (ψ z : ℂ)) := funext fun _ => neg_mul _ _
    rw [h1, h2, integral_neg, integral_neg, heq ψ hψ]

private theorem ae_lt_top_of_loc_lintegral {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hLoc : ∀ a b : ℝ, 0 < a → ∫⁻ s in Icc a b, f s < ⊤) :
    ∀ᵐ s ∂volume, 0 < s → f s < ⊤ := by
  have hn : ∀ n : ℕ, ∀ᵐ s ∂volume, s ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) → f s < ⊤ := by
    intro n
    have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hlt := hLoc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ha
    exact (ae_restrict_iff' measurableSet_Icc).1 (ae_lt_top hf hlt.ne)
  filter_upwards [ae_all_iff.2 hn] with s hs hpos
  obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt hpos
  obtain ⟨n2, hn2⟩ := exists_nat_gt s
  let n : ℕ := max n1 n2
  apply hs n
  refine ⟨?_, ?_⟩
  · have hle : (n1 : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (le_max_left n1 n2) 1
    exact (one_div_le_one_div_of_le (by positivity) hle).trans hn1.le
  · have hle : (n2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_right n1 n2
    linarith

/-! ### 5. Main lift theorem `p0SliceLiftH1_of_loc` -/

theorem p0SliceLiftH1_of_loc {ν c : ℝ} (tr : B0140.TrainSol ν c) (hc : 0 < c)
    (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf)
    (hb0'_hr : InHr c bgp b0') (hbq_hr : InHr c bgp (sqrtS b0q))
    (hbη_hr : InHr c bgp (sqrtS b0η)) (hD2_hr : ∀ i j, InHr c bgp (mulS (D2 i j)))
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    (hwU_q : HasWeakVec vQ0 dZero (flatBv tr b0' b0q b0η)
      (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)))
    (hwU_η : HasWeakVec vEta dZero (flatBv tr b0' b0q b0η)
      (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)))
    (hLoc : ∀ a b : ℝ, 0 < a →
      ∫⁻ s in Icc a b,
        sliceH1Norm c (flatBv tr b0' b0q b0η)
          (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
          (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s < ⊤) :
    ∃ g gq gη : CProf,
      StronglyMeasurable g ∧ StronglyMeasurable gq ∧ StronglyMeasurable gη ∧
      QPeriodic c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
      IsBodySource tr b0' b0q b0η g ∧
      (∀ s : ℝ, 0 < s →
        sliceH1Norm c g gq gη s ≤
          ENNReal.ofReal 2 *
            sliceH1Norm c (flatBv tr b0' b0q b0η)
              (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
              (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s) := by
  let U := flatBv tr b0' b0q b0η
  let Uq := flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)
  let Uη := flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)
  let Up := posInd U
  let Uqp := posInd Uq
  let Uηp := posInd Uη
  have hU_sm : StronglyMeasurable Up := stronglyMeasurable_posInd_flatBv tr hsm0 hsmq hsmη
  have hUq_sm : StronglyMeasurable Uqp :=
    stronglyMeasurable_posInd_flatBvQ tr hsm0 hsmq hsmη (hsmD2 0 0) (hsmD2 1 0)
  have hUη_sm : StronglyMeasurable Uηp :=
    stronglyMeasurable_posInd_flatBvEta tr hsm0 hsmq hsmη (hsmD2 0 1) (hsmD2 1 1)
  have hp0 : QPeriodic c b0' := hb0'_hr.periodic
  have hpq : QPeriodic c b0q := qPeriodic_of_sqrtS hbq_hr.periodic
  have hpη : QPeriodic c b0η := qPeriodic_of_sqrtS hbη_hr.periodic
  have hpD2 : ∀ i j, QPeriodic c (D2 i j) := fun i j => qPeriodic_of_mulS (hD2_hr i j).periodic
  have hU_per : QPeriodic c U := qPeriodic_flatBv tr hp0 hpq hpη
  have hUp_per : QPeriodic c Up := qPeriodic_posInd hU_per
  have hUqp_per : QPeriodic c Uqp :=
    qPeriodic_posInd (qPeriodic_flatBvQ tr hp0 hpq hpη (hpD2 0 0) (hpD2 1 0))
  have hUηp_per : QPeriodic c Uηp :=
    qPeriodic_posInd (qPeriodic_flatBvEta tr hp0 hpq hpη (hpD2 0 1) (hpD2 1 1))
  have hwUp_q : HasWeakVec vQ0 dZero Up Uqp := fun i =>
    FlatBvWL.hasWeakFO_congr_ae (hwU_q i)
      (Eventually.of_forall fun x hx => congrArg (fun v => v i) (posInd_eq_of_pos U hx))
      (Eventually.of_forall fun x hx => congrArg (fun v => v i) (posInd_eq_of_pos Uq hx))
  have hwUp_η : HasWeakVec vEta dZero Up Uηp := fun i =>
    FlatBvWL.hasWeakFO_congr_ae (hwU_η i)
      (Eventually.of_forall fun x hx => congrArg (fun v => v i) (posInd_eq_of_pos U hx))
      (Eventually.of_forall fun x hx => congrArg (fun v => v i) (posInd_eq_of_pos Uη hx))
  have hslice_eq : ∀ {s : ℝ}, 0 < s → sliceH1Norm c Up Uqp Uηp s = sliceH1Norm c U Uq Uη s := by
    intro s hs
    have e1 : (fun z => Up (s, z)) = fun z => U (s, z) := funext fun z => posInd_eq_of_pos U hs
    have e2 : (fun z => Uqp (s, z)) = fun z => Uq (s, z) := funext fun z => posInd_eq_of_pos Uq hs
    have e3 : (fun z => Uηp (s, z)) = fun z => Uη (s, z) := funext fun z => posInd_eq_of_pos Uη hs
    unfold sliceH1Norm
    rw [e1, e2, e3]
  have hLocp : ∀ a b : ℝ, 0 < a → ∫⁻ s in Icc a b, sliceH1Norm c Up Uqp Uηp s < ⊤ := by
    intro a b ha
    have heq : ∫⁻ s in Icc a b, sliceH1Norm c Up Uqp Uηp s =
        ∫⁻ s in Icc a b, sliceH1Norm c U Uq Uη s := by
      refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      exact hslice_eq (lt_of_lt_of_le ha hs.1)
    rw [heq]
    exact hLoc a b ha
  have hm_H1 : Measurable (sliceH1Norm c Up Uqp Uηp) :=
    measurable_sliceH1Norm_cp c hU_sm hUq_sm hUη_sm
  let S : Set ℝ := {s : ℝ | 0 < s ∧ sliceH1Norm c Up Uqp Uηp s < ⊤}
  have hS_meas : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt hm_H1 measurable_const)
  obtain ⟨g, hg_sm, hg_per, hg_zero, hg_ae⟩ := exists_negP0_periodic_rep hc hS_meas hU_sm
  obtain ⟨gq, hgq_sm, hgq_per, hgq_zero, hgq_ae⟩ := exists_negP0_periodic_rep hc hS_meas hUq_sm
  obtain ⟨gη, hgη_sm, hgη_per, hgη_zero, hgη_ae⟩ := exists_negP0_periodic_rep hc hS_meas hUη_sm
  -- Pointwise slice H¹ bound for every s > 0
  have hH1_le : ∀ s : ℝ, 0 < s →
      sliceH1Norm c g gq gη s ≤ ENNReal.ofReal 2 * sliceH1Norm c U Uq Uη s := by
    intro s hs
    rw [← hslice_eq hs]
    by_cases hsS : s ∈ S
    · have hb_W : ∀ {G W : CProf},
          (∀ᵐ z ∂(volume.restrict (B0579.cell c)), G (s, z) = p0Merid c (fun y => -W (s, y)) z) →
          eLpNorm (fun z => G (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
            ENNReal.ofReal 2 * eLpNorm (fun z => W (s, z)) 2 (volume.restrict (B0579.cell c)) := by
        intro G W hae
        rw [eLpNorm_congr_ae hae]
        refine (eLpNorm_p0Merid_le c (fun y => -W (s, y))).trans ?_
        have hneg : (fun y => -W (s, y)) = -(fun y => W (s, y)) := rfl
        rw [hneg, eLpNorm_neg]
      have b1 := hb_W (hg_ae s hsS)
      have b2 := hb_W (hgq_ae s hsS)
      have b3 := hb_W (hgη_ae s hsS)
      unfold sliceH1Norm
      rw [mul_add, mul_add]
      exact add_le_add (add_le_add b1 b2) b3
    · rw [sliceH1Norm_zero_of_eq_zero c (hg_zero s hsS) (hgq_zero s hsS) (hgη_zero s hsS)]
      exact zero_le
  -- Almost every s > 0 lies in S and has cylinder weak derivatives
  have hae_fin : ∀ᵐ s ∂volume, 0 < s → sliceH1Norm c Up Uqp Uηp s < ⊤ :=
    ae_lt_top_of_loc_lintegral hm_H1 hLocp
  have hae_jq := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 0 Up Uqp
    hU_sm hUq_sm hUp_per hUqp_per hwUp_q
  have hae_jη := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 1 Up Uηp
    hU_sm hUη_sm hUp_per hUηp_per hwUp_η
  have hae_good : ∀ᵐ s ∂volume, 0 < s →
      s ∈ S ∧
      (∀ i : Fin 2,
        IIIa.HasWeakCellDerivC c 0 (fun z => g (s, z) i) (fun z => gq (s, z) i) ∧
        IIIa.HasWeakCellDerivC c 1 (fun z => g (s, z) i) (fun z => gη (s, z) i)) ∧
      (∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ →
        ∫ z in B0579.cell c,
          (g (s, z) 0 * (B0579.pd 0 ψ z : ℂ) + g (s, z) 1 * (B0579.pd 1 ψ z : ℂ)) = 0) ∧
      (∀ Ψ : B0579.Plane → Fin 2 → ℝ, IIIa.IsDivFreeTestField c Ψ →
        ∫ z in B0579.cell c,
          ∑ i : Fin 2, (g (s, z) i + Up (s, z) i) * (Ψ z i : ℂ) = 0) := by
    filter_upwards [hae_fin, hae_jq, hae_jη] with s hfin hjq hjη hpos
    have hH1_s : sliceH1Norm c Up Uqp Uηp s < ⊤ := hfin hpos
    have hsS : s ∈ S := ⟨hpos, hH1_s⟩
    have hU_fin : eLpNorm (fun z => Up (s, z)) 2 (volume.restrict (B0579.cell c)) < ⊤ :=
      (le_self_add.trans le_self_add).trans_lt hH1_s
    have hUq_fin : eLpNorm (fun z => Uqp (s, z)) 2 (volume.restrict (B0579.cell c)) < ⊤ :=
      (le_add_self.trans le_self_add).trans_lt hH1_s
    have hUη_fin : eLpNorm (fun z => Uηp (s, z)) 2 (volume.restrict (B0579.cell c)) < ⊤ :=
      le_add_self.trans_lt hH1_s
    have hU_mem : MemLp (fun z => Up (s, z)) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(hU_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable, hU_fin⟩
    have hUq_mem : MemLp (fun z => Uqp (s, z)) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(hUq_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable, hUq_fin⟩
    have hUη_mem : MemLp (fun z => Uηp (s, z)) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(hUη_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable, hUη_fin⟩
    obtain ⟨hmU_re, hmU_im⟩ := memLp_reVec_imVec_of_lt_top hU_sm hU_fin
    obtain ⟨hmUq_re, hmUq_im⟩ := memLp_reVec_imVec_of_lt_top hUq_sm hUq_fin
    obtain ⟨hmUη_re, hmUη_im⟩ := memLp_reVec_imVec_of_lt_top hUη_sm hUη_fin
    let fU : B0579.Plane → Fin 2 → ℂ := fun z i => (-Up (s, z)) i
    let fD : Fin 2 → B0579.Plane → Fin 2 → ℂ :=
      ![fun z i => (-Uqp (s, z)) i, fun z i => (-Uηp (s, z)) i]
    have hD_re : ∀ j : Fin 2, MemLp (IIIa.reVec (fD j)) 2 (UnforcedLeray.Cyl.cellμ c) := by
      intro j; fin_cases j
      · exact hmUq_re
      · exact hmUη_re
    have hD_im : ∀ j : Fin 2, MemLp (IIIa.imVec (fD j)) 2 (UnforcedLeray.Cyl.cellμ c) := by
      intro j; fin_cases j
      · exact hmUq_im
      · exact hmUη_im
    have hw_neg : ∀ i j : Fin 2,
        IIIa.HasWeakCellDerivC c j (fun z => fU z i) (fun z => fD j z i) := by
      intro i j; fin_cases j
      · exact hasWeakCellDerivC_neg (hjq hpos hU_mem hUq_mem i)
      · exact hasWeakCellDerivC_neg (hjη hpos hU_mem hUη_mem i)
    have hp0_comm := IIIa.p0CommWeakC c hc fU fD hmU_re hmU_im hD_re hD_im hw_neg
    have hga := hg_ae s hsS
    have hgqa := hgq_ae s hsS
    have hgηa := hgη_ae s hsS
    refine ⟨hsS, ?_, ?_, ?_⟩
    · intro i
      have hga_i : (fun z => g (s, z) i) =ᵐ[volume.restrict (B0579.cell c)]
          fun z => IIIa.P0C c fU z i :=
        hga.mono fun z hz => congrArg (fun v : CMerid => v i) hz
      have hgqa_i : (fun z => gq (s, z) i) =ᵐ[volume.restrict (B0579.cell c)]
          fun z => IIIa.P0C c (fD 0) z i :=
        hgqa.mono fun z hz => congrArg (fun v : CMerid => v i) hz
      have hgηa_i : (fun z => gη (s, z) i) =ᵐ[volume.restrict (B0579.cell c)]
          fun z => IIIa.P0C c (fD 1) z i :=
        hgηa.mono fun z hz => congrArg (fun v : CMerid => v i) hz
      exact ⟨IIIa.HasWeakCellDerivC.congr_ae hga_i hgqa_i (hp0_comm i 0),
        IIIa.HasWeakCellDerivC.congr_ae hga_i hgηa_i (hp0_comm i 1)⟩
    · intro ψ hψ
      have hdiv := IIIa.p0DivFreeC c hc fU ψ hψ
      refine (integral_congr_ae ?_).trans hdiv
      filter_upwards [hga] with z hz
      have hz0 : g (s, z) 0 = IIIa.P0C c fU z 0 := congrArg (fun v : CMerid => v 0) hz
      have hz1 : g (s, z) 1 = IIIa.P0C c fU z 1 := congrArg (fun v : CMerid => v 1) hz
      rw [hz0, hz1]
    · intro Ψ hΨ
      have horth := IIIa.p0OrthC c hc fU hmU_re hmU_im Ψ hΨ
      refine (integral_congr_ae ?_).trans horth
      filter_upwards [hga] with z hz
      refine Finset.sum_congr rfl fun i _ => ?_
      have hzi : g (s, z) i = IIIa.P0C c fU z i := congrArg (fun v : CMerid => v i) hz
      have hfU_i : fU z i = -(Up (s, z) i) := rfl
      rw [hzi, hfU_i, sub_neg_eq_add]
  -- Local L² bounds in s for PeriodizeTest
  have hLoc_g_gq : ∀ a b : ℝ, 0 < a →
      (∫⁻ s in Icc a b,
        (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => gq (s, z)) 2 (volume.restrict (B0579.cell c)))) < ⊤ := by
    intro a b ha
    have hle : ∫⁻ s in Icc a b,
          (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun z => gq (s, z)) 2 (volume.restrict (B0579.cell c))) ≤
        ENNReal.ofReal 2 * ∫⁻ s in Icc a b, sliceH1Norm c U Uq Uη s := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      exact le_self_add.trans (hH1_le s (lt_of_lt_of_le ha hs.1))
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hLoc a b ha))
  have hLoc_g_gη : ∀ a b : ℝ, 0 < a →
      (∫⁻ s in Icc a b,
        (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => gη (s, z)) 2 (volume.restrict (B0579.cell c)))) < ⊤ := by
    intro a b ha
    have hle : ∫⁻ s in Icc a b,
          (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun z => gη (s, z)) 2 (volume.restrict (B0579.cell c))) ≤
        ENNReal.ofReal 2 * ∫⁻ s in Icc a b, sliceH1Norm c U Uq Uη s := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      have h1 : eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun z => gη (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
          sliceH1Norm c g gq gη s := by
        unfold sliceH1Norm
        exact add_le_add le_self_add le_rfl
      exact h1.trans (hH1_le s (lt_of_lt_of_le ha hs.1))
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hLoc a b ha))
  -- Apply PeriodizeTest.sliceWeakToJoint (j = 0, 1)
  have hgwq : HasWeakVec vQ0 dZero g gq :=
    TailPeriodizeAux.sliceWeakToJoint hc 0 g gq hg_sm hgq_sm hg_per hgq_per hLoc_g_gq
      (hae_good.mono fun s hs hpos i => (hs hpos).2.1 i |>.1)
  have hgwη : HasWeakVec vEta dZero g gη :=
    TailPeriodizeAux.sliceWeakToJoint hc 1 g gη hg_sm hgη_sm hg_per hgη_per hLoc_g_gη
      (hae_good.mono fun s hs hpos i => (hs hpos).2.1 i |>.2)
  -- Apply PeriodizeTest.sliceBodySourceToJoint with posInd profiles, then transfer to (b0', b0q, b0η)
  have hU_eq_pos : Up = flatBv tr (posInd b0') (posInd b0q) (posInd b0η) := by
    funext x
    dsimp only [Up]
    by_cases hx : 0 < x.1
    · rw [posInd_eq_of_pos U hx]
      ext i
      simp [U, FlatBvWL.flatBv_apply, posInd_eq_of_pos _ hx]
    · rw [posInd_eq_zero_of_nonpos U hx]
      ext i
      simp [FlatBvWL.flatBv_apply, posInd_eq_zero_of_nonpos _ hx]
  have hLoc_g_U : ∀ a b : ℝ, 0 < a →
      (∫⁻ s in Icc a b,
        (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => flatBv tr (posInd b0') (posInd b0q) (posInd b0η) (s, z)) 2
            (volume.restrict (B0579.cell c)))) < ⊤ := by
    intro a b ha
    rw [← hU_eq_pos]
    have hle : ∫⁻ s in Icc a b,
          (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun z => Up (s, z)) 2 (volume.restrict (B0579.cell c))) ≤
        ENNReal.ofReal 3 * ∫⁻ s in Icc a b, sliceH1Norm c U Uq Uη s := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      have hpos : 0 < s := lt_of_lt_of_le ha hs.1
      have hg_le : eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
          ENNReal.ofReal 2 * sliceH1Norm c U Uq Uη s :=
        (le_self_add.trans le_self_add).trans (hH1_le s hpos)
      have hU_le : eLpNorm (fun z => Up (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
          1 * sliceH1Norm c U Uq Uη s := by
        rw [one_mul, ← hslice_eq hpos]
        exact le_self_add.trans le_self_add
      have h3 : ENNReal.ofReal 2 + 1 = ENNReal.ofReal 3 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) zero_le_one]
        norm_num
      calc eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
              eLpNorm (fun z => Up (s, z)) 2 (volume.restrict (B0579.cell c))
          ≤ ENNReal.ofReal 2 * sliceH1Norm c U Uq Uη s +
              1 * sliceH1Norm c U Uq Uη s := add_le_add hg_le hU_le
        _ = (ENNReal.ofReal 2 + 1) * sliceH1Norm c U Uq Uη s := (add_mul _ _ _).symm
        _ = ENNReal.ofReal 3 * sliceH1Norm c U Uq Uη s := by rw [h3]
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hLoc a b ha))
  have hg_src_pos : IsBodySource tr (posInd b0') (posInd b0q) (posInd b0η) g :=
    TailPeriodizeAux.sliceBodySourceToJoint hc tr (posInd b0') (posInd b0q) (posInd b0η) g
      hg_sm (hU_eq_pos ▸ hU_sm.aestronglyMeasurable) hg_per (hU_eq_pos ▸ hUp_per) hLoc_g_U
      (hae_good.mono fun s hs hpos => (hs hpos).2.2.1)
      (hU_eq_pos ▸ hae_good.mono fun s hs hpos => (hs hpos).2.2.2)
  have hg_src : IsBodySource tr b0' b0q b0η g := by
    refine ⟨hg_src_pos.solenoidal, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, heq⟩ := hg_src_pos.equation Ψ hΨ
    have hcdot_eq : cdot (flatBv tr b0' b0q b0η) Ψ =
        cdot (flatBv tr (posInd b0') (posInd b0q) (posInd b0η)) Ψ := by
      funext x
      by_cases hx : 0 < x.1
      · rw [← hU_eq_pos]
        unfold cdot
        dsimp only [Up]
        rw [posInd_eq_of_pos U hx]
      · have hΨ0 : ∀ i : Fin 2, Ψ x i = 0 := fun i =>
          Function.notMem_support.mp fun h =>
            hx ((hΨ.smooth i).supp (subset_tsupport _ h)).1
        unfold cdot
        simp [hΨ0]
    rw [hcdot_eq]
    exact ⟨hi1, hi2, heq⟩
  exact ⟨g, gq, gη, hg_sm, hgq_sm, hgη_sm, hg_per, hgwq, hgwη, hg_src, hH1_le⟩

end UnforcedLeray.Short.IIb.TailSliceP0LiftAux

end
