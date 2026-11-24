import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvSliceGoodAe.CellLemmas
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvSliceGoodAe.JointWeak
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvWeakLeibniz
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.FlatGraphD2Slice

/-!
# `PartII-b:F5/2/2/2` (`FlatBvSliceGoodAe`): Fubini slice disintegration and zero cell circulation for `flatBv`

Source of record: `the November 2 reference manuscript` (SP), lines 2213–2239
(slice `H¹(C_c)` / `X_m` finiteness via Hölder `1/2 = 3/22 + 4/11`, slice cylinder weak derivatives,
and zero cell circulation of `curl(flatBv)`).

Proves `flatBvSliceGoodAe_proof : UnforcedLeray.Short.IIb.FlatBvSliceGoodAe` via
`flatBvSliceGoodAe_of` and `FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof`:
1. a.e. finiteness of `sliceD2Sum`, hence of `sliceH1Norm` and `sliceXmNorm` via
   `sliceH1Norm_flatBv_le` and `sliceXmNorm_flatBv_curl_le`;
2. slice cylinder weak derivatives via `JointWeakToSlice` applied to the `{s > 0}`-truncated
   profiles;
3. cell `L¹` integrability of `profCurl Uq Uη (s, ·)` from `integrableOnCellOfXm_proof`;
4. zero cell circulation from `zeroCirculationOfWeak_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ### 1. Truncation to `{s > 0}`, joint measurability, and `q`-periodicity of `flatBv` jets -/

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
    have heq : W = fun x => WithLp.toLp 2 (fun i : Fin 2 => W x i) := funext fun _ => rfl
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
    by_cases hx : x ∈ posSet <;> simp [posInd, hx]
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

/-! ### 2. Private clause lemmas for `FlatBvSliceGoodAe` -/

/-- Clause (1): `sliceD2Sum` is finite a.e. on `(0, ∞)`, so `sliceH1Norm` and `sliceXmNorm` are
finite for a.e. `s > 0`. -/
private theorem ae_sliceNorms_lt_top {ν c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    (tr : B0140.TrainSol ν c)
    (hTr : ∀ᵐ s ∂volume, 0 < s → trainSliceNorm22_3 c m tr s < ⊤)
    {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hb0'_hr : InHr c bgp b0') (hbq_hr : InHr c bgp (sqrtS b0q))
    (hbη_hr : InHr c bgp (sqrtS b0η)) (hD2_hr : ∀ i j, InHr c bgp (mulS (D2 i j)))
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j)) :
    ∀ᵐ s ∂volume, 0 < s →
      sliceH1Norm c (flatBv tr b0' b0q b0η)
          (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
          (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s < ⊤ ∧
        sliceXmNorm c m
          (profCurl (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
            (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1))) s < ⊤ := by
  have hm0 := measurable_sliceLpNorm c hsm0
  have hmq := measurable_sliceLpNorm c hsmq
  have hmη := measurable_sliceLpNorm c hsmη
  have hmD2 : ∀ i j, Measurable (sliceLpNorm c (D2 i j)) :=
    fun i j => measurable_sliceLpNorm c (hsmD2 i j)
  have hmSum := measurable_sliceD2Sum c hm0 hmq hmη hmD2
  have hae_band : ∀ n : ℕ, ∀ᵐ s ∂volume,
      s ∈ Ioc (0 : ℝ) ((n : ℝ) + 1) → sliceD2Sum c b0' b0q b0η D2 s < ⊤ := by
    intro n
    let T : ℝ := (n : ℝ) + 1
    have hT : 0 < T := by positivity
    have hs0_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0') < ⊤ :=
      (sLpNorm_D0_le T _ hm0).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sliceLpNorm_le_hNorm c T hsm0).trans_lt hb0'_hr.finite))
    have hsq_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0q) < ⊤ :=
      (sLpNorm_D1_le T _ hmq).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sqrtS_sliceLpNorm_le c T hsmq).trans_lt hbq_hr.finite))
    have hsη_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0η) < ⊤ :=
      (sLpNorm_D1_le T _ hmη).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sqrtS_sliceLpNorm_le c T hsmη).trans_lt hbη_hr.finite))
    have hsD2_lt : ∀ i j, sLpNorm (13 / 8) T (sliceLpNorm c (D2 i j)) < ⊤ := fun i j => by
      rw [sLpNorm_D2_eq T _ (hmD2 i j)]
      exact (sLpNorm_mulS_sliceLpNorm_le c T (hsmD2 i j)).trans_lt (hD2_hr i j).finite
    have hsSum_lt : sLpNorm (13 / 8) T (sliceD2Sum c b0' b0q b0η D2) < ⊤ := by
      refine (sLpNorm_sliceD2Sum_le (13 / 8) T c hm0 hmq hmη hmD2).trans_lt ?_
      refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
        ⟨hs0_lt, hsq_lt⟩, hsη_lt⟩, ?_⟩
      exact ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr fun j _ => hsD2_lt i j
    have hHardy := hardyL1_proof T hT (sliceD2Sum c b0' b0q b0η D2) hmSum
    change ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s ≤
      ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * T ^ (1 / 22 : ℝ)) *
        sLpNorm (13 / 8) T (sliceD2Sum c b0' b0q b0η D2) at hHardy
    have hIoc_lt : ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s < ⊤ :=
      hHardy.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsSum_lt)
    exact (ae_restrict_iff' measurableSet_Ioc).1 (ae_lt_top hmSum hIoc_lt.ne)
  filter_upwards [hTr, ae_all_iff.2 hae_band] with s hTr_s hSum_n hs
  have hSum_s : sliceD2Sum c b0' b0q b0η D2 s < ⊤ :=
    hSum_n ⌊s⌋₊ ⟨hs, (Nat.lt_floor_add_one s).le⟩
  have hTr_fin : trainSliceNorm22_3 c m tr s < ⊤ := hTr_s hs
  have hfac_fin : trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) < ⊤ :=
    ENNReal.mul_lt_top hTr_fin ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · exact (sliceH1Norm_flatBv_le hc hm tr hsm0 hsmq hsmη hsmD2 hs.le).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfac_fin) hSum_s)
  · exact (sliceXmNorm_flatBv_curl_le hc tr hsm0 hsmq hsmη hsmD2 hs.le).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfac_fin) hSum_s)

/-- Clause (2): cylinder weak derivatives on a.e. slice `s > 0` where `sliceH1Norm < ⊤`. -/
private theorem ae_sliceWeakDeriv (hJ : FlatBvSliceGoodAeNeeded.JointWeakToSlice)
    {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hb0'_hr : InHr c bgp b0') (hbq_hr : InHr c bgp (sqrtS b0q))
    (hbη_hr : InHr c bgp (sqrtS b0η)) (hD2_hr : ∀ i j, InHr c bgp (mulS (D2 i j)))
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    (hwU_q : HasWeakVec vQ0 dZero (flatBv tr b0' b0q b0η)
      (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)))
    (hwU_η : HasWeakVec vEta dZero (flatBv tr b0' b0q b0η)
      (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1))) :
    let U := flatBv tr b0' b0q b0η
    let Uq := flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)
    let Uη := flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)
    ∀ᵐ s ∂volume, 0 < s → sliceH1Norm c U Uq Uη s < ⊤ →
      ∀ i : Fin 2,
        IIIa.HasWeakCellDerivC c 0 (fun z => U (s, z) i) (fun z => Uq (s, z) i) ∧
        IIIa.HasWeakCellDerivC c 1 (fun z => U (s, z) i) (fun z => Uη (s, z) i) := by
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
  have hUp_per : QPeriodic c Up := qPeriodic_posInd (qPeriodic_flatBv tr hp0 hpq hpη)
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
  have hae_q := hJ c hc 0 Up Uqp hU_sm hUq_sm hUp_per hUqp_per hwUp_q
  have hae_η := hJ c hc 1 Up Uηp hU_sm hUη_sm hUp_per hUηp_per hwUp_η
  filter_upwards [hae_q, hae_η] with s hjq hjη hs hH1 i
  have eU : (fun z => Up (s, z)) = fun z => U (s, z) := funext fun z => posInd_eq_of_pos U hs
  have eUq : (fun z => Uqp (s, z)) = fun z => Uq (s, z) := funext fun z => posInd_eq_of_pos Uq hs
  have eUη : (fun z => Uηp (s, z)) = fun z => Uη (s, z) := funext fun z => posInd_eq_of_pos Uη hs
  have hU_fin : eLpNorm (fun z => Up (s, z)) 2 (volume.restrict (B0579.cell c)) < ⊤ := by
    rw [eU]; exact (le_self_add.trans le_self_add).trans_lt hH1
  have hUq_fin : eLpNorm (fun z => Uqp (s, z)) 2 (volume.restrict (B0579.cell c)) < ⊤ := by
    rw [eUq]; exact (le_add_self.trans le_self_add).trans_lt hH1
  have hUη_fin : eLpNorm (fun z => Uηp (s, z)) 2 (volume.restrict (B0579.cell c)) < ⊤ := by
    rw [eUη]; exact le_add_self.trans_lt hH1
  have hU_mem : MemLp (fun z => Up (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    ⟨(hU_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable, hU_fin⟩
  have hUq_mem : MemLp (fun z => Uqp (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    ⟨(hUq_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable, hUq_fin⟩
  have hUη_mem : MemLp (fun z => Uηp (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    ⟨(hUη_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable, hUη_fin⟩
  have h0 := hjq hs hU_mem hUq_mem i
  have h1 := hjη hs hU_mem hUη_mem i
  have eUi : (fun z => Up (s, z) i) = fun z => U (s, z) i := funext fun z =>
    congrArg (fun v => v i) (posInd_eq_of_pos U hs)
  have eUqi : (fun z => Uqp (s, z) i) = fun z => Uq (s, z) i := funext fun z =>
    congrArg (fun v => v i) (posInd_eq_of_pos Uq hs)
  have eUηi : (fun z => Uηp (s, z) i) = fun z => Uη (s, z) i := funext fun z =>
    congrArg (fun v => v i) (posInd_eq_of_pos Uη hs)
  rw [eUi, eUqi] at h0
  rw [eUi, eUηi] at h1
  exact ⟨h0, h1⟩

/-- Clause (3): `IntegrableOn` of `profCurl Uq Uη (s, ·)` on `B0579.cell c` for `s > 0` with
`sliceXmNorm < ⊤`. -/
private theorem sliceCurl_integrableOn {ν c m : ℝ} (hm : 8 < m) (tr : B0140.TrainSol ν c)
    {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    {s : ℝ} (hs : 0 < s)
    (hXm : sliceXmNorm c m
      (profCurl (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
        (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1))) s < ⊤) :
    IntegrableOn
      (fun z => profCurl (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
        (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) (s, z))
      (B0579.cell c) volume := by
  let Uq := flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)
  let Uη := flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)
  have hUq_sm := stronglyMeasurable_posInd_flatBvQ tr hsm0 hsmq hsmη (hsmD2 0 0) (hsmD2 1 0)
  have hUη_sm := stronglyMeasurable_posInd_flatBvEta tr hsm0 hsmq hsmη (hsmD2 0 1) (hsmD2 1 1)
  have hm_q1 : Measurable (fun z : B0579.Plane => Uq (s, z) 1) := by
    have heq : (fun z : B0579.Plane => Uq (s, z) 1) =
        fun z => (EuclideanSpace.proj (1 : Fin 2) : CMerid →L[ℂ] ℂ) (posInd Uq (s, z)) :=
      funext fun z => congrArg (fun v => v 1) (posInd_eq_of_pos Uq hs).symm
    rw [heq]
    exact ((EuclideanSpace.proj (1 : Fin 2) : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      (hUq_sm.comp_measurable (measurable_const.prodMk measurable_id))).measurable
  have hm_η0 : Measurable (fun z : B0579.Plane => Uη (s, z) 0) := by
    have heq : (fun z : B0579.Plane => Uη (s, z) 0) =
        fun z => (EuclideanSpace.proj (0 : Fin 2) : CMerid →L[ℂ] ℂ) (posInd Uη (s, z)) :=
      funext fun z => congrArg (fun v => v 0) (posInd_eq_of_pos Uη hs).symm
    rw [heq]
    exact ((EuclideanSpace.proj (0 : Fin 2) : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      (hUη_sm.comp_measurable (measurable_const.prodMk measurable_id))).measurable
  have hw_aesm : AEStronglyMeasurable (fun z => profCurl Uq Uη (s, z))
      (volume.restrict (B0579.cell c)) :=
    (hm_q1.sub hm_η0).aestronglyMeasurable
  exact FlatBvSliceGoodAeNeeded.integrableOnCellOfXm_proof c m (by linarith) _ hw_aesm hXm

/-- Clause (4): zero cell circulation of `profCurl Uq Uη (s, ·)` for `s > 0`. -/
private theorem sliceCurl_integral_zero {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η)
    {s : ℝ} (hs : 0 < s)
    (hH1 : sliceH1Norm c (flatBv tr b0' b0q b0η)
      (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
      (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s < ⊤)
    (hweak : ∀ i : Fin 2,
      IIIa.HasWeakCellDerivC c 0
        (fun z => flatBv tr b0' b0q b0η (s, z) i)
        (fun z => flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) (s, z) i) ∧
      IIIa.HasWeakCellDerivC c 1
        (fun z => flatBv tr b0' b0q b0η (s, z) i)
        (fun z => flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) (s, z) i))
    (hint : IntegrableOn
      (fun z => profCurl (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
        (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) (s, z))
      (B0579.cell c) volume) :
    ∫ z in B0579.cell c,
      profCurl (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
        (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) (s, z) = 0 := by
  let U := flatBv tr b0' b0q b0η
  have hU_sm := stronglyMeasurable_posInd_flatBv tr hsm0 hsmq hsmη
  have eU : (fun z : B0579.Plane => posInd U (s, z)) = fun z => U (s, z) :=
    funext fun z => posInd_eq_of_pos U hs
  have hU_aesm : AEStronglyMeasurable (fun z => U (s, z)) (volume.restrict (B0579.cell c)) := by
    rw [← eU]
    exact (hU_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hU_mem : MemLp (fun z => U (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    ⟨hU_aesm, (le_self_add.trans le_self_add).trans_lt hH1⟩
  have hU0_mem : MemLp (fun z => U (s, z) 0) 2 (volume.restrict (B0579.cell c)) :=
    (EuclideanSpace.proj (0 : Fin 2) : CMerid →L[ℂ] ℂ).comp_memLp' hU_mem
  exact FlatBvSliceGoodAeNeeded.zeroCirculationOfWeak_proof c hc
    (fun z => U (s, z) 0) (fun z => U (s, z) 1)
    (fun z => flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) (s, z) 1)
    (fun z => flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) (s, z) 0)
    hU0_mem (hweak 1).1 (hweak 0).2 hint

/-! ### 3. Main theorems: `flatBvSliceGoodAe_of` and `flatBvSliceGoodAe_proof` -/

/-- Conditional proof of `FlatBvSliceGoodAe` from `FlatBvSliceGoodAeNeeded.JointWeakToSlice`. -/
theorem flatBvSliceGoodAe_of (hJ : FlatBvSliceGoodAeNeeded.JointWeakToSlice) :
    UnforcedLeray.Short.IIb.FlatBvSliceGoodAe := by
  intro m hm ν c tr hc hTr b0 b0' b0q b0η D2 _hb0 _hae0 hb0'_hr hbq_hr hbη_hr hD2_hr
    hsm0 hsmq hsmη hsmD2 _hwq _hwη _hw00 _hw01 _hw10 _hw11 hwU_q hwU_η
  have hae_norms := ae_sliceNorms_lt_top hc (by linarith : 0 ≤ m) tr hTr
    hb0'_hr hbq_hr hbη_hr hD2_hr hsm0 hsmq hsmη hsmD2
  have hae_weak := ae_sliceWeakDeriv hJ hc tr hb0'_hr hbq_hr hbη_hr hD2_hr
    hsm0 hsmq hsmη hsmD2 hwU_q hwU_η
  filter_upwards [hae_norms, hae_weak] with s hnorms hweak hs
  obtain ⟨hH1, hXm⟩ := hnorms hs
  have hw := hweak hs hH1
  have hint := sliceCurl_integrableOn hm tr hsm0 hsmq hsmη hsmD2 hs hXm
  have hzero := sliceCurl_integral_zero hc tr hsm0 hsmq hsmη hs hH1 hw hint
  exact ⟨hH1, hXm, hw, hint, hzero⟩

/-- **Target of `PartII-b:F5/2/2/2`**: Fubini slice disintegration and zero cell circulation for
`flatBv`. -/
theorem flatBvSliceGoodAe_proof : UnforcedLeray.Short.IIb.FlatBvSliceGoodAe :=
  flatBvSliceGoodAe_of FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof

end UnforcedLeray.Short.IIb

end
