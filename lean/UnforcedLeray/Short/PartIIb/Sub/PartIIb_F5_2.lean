import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5

/-!
# Part II-b, task `PartII-b:F5/2`: slice-level `L^{22/3}`–`L^{11/4}` Hölder and body source assembly

Source of record: `the November 2 reference manuscript` (SP), lines 2228-2239
(`short-bg:source`), 2050-2052 (`short-bg:train-uniform`), Part I Lemma `sct:heat` (SP 437-481).

## Proved here (zero `sorry`)

* `flatBvQ`, `flatBvEta`: the formal Leibniz weak `q`- and `η`-derivatives of the unprojected
  convective interaction `flatBv tr b0' b0q b0η = (v·∇_{q,η})b0' + (b0'·∇_{q,η})v`;
* `trainJetPt`: pointwise spatial jet envelope of `tr.v` up to second spatial derivatives,
  continuity/measurability `continuous_trainJetPt` / `measurable_trainJetPt`, and pointwise norm
  bounds `norm_flatBv_le`, `norm_flatBvQ_le`, `norm_flatBvEta_le`, `norm_profCurl_flatBv_le`;
* `cell_holder_22_3`: the spatial Hölder inequality (`1/2 = 3/22 + 4/11`) on `B0579.cell c`,
  converting from `volume.restrict (B0579.cell c)` to `Cyl.avgμ c` with factor `c^{4/11}`;
* `sliceH1Norm_flatBv_le` and `sliceXmNorm_flatBv_curl_le`: slice-level `H¹` and `X_m` bounds on
  `flatBv` and its curl in terms of the weighted `L^{22/3}` train factor `trainSliceNorm22_3` and
  the seven `sliceLpNorm`s of `b0', b0q, b0η, D2 i j`;
* `isBodySource_congr_b0`: transfer of `IsBodySource` from `b0'` to `b0` when `b0' = b0` a.e. on
  `s > 0`;
* `sLpNorm_add_le`, `sLpNorm_const_mul`, `sLpNorm_mono_Ioc`: Minkowski subadditivity, scaling, and
  monotonicity on `(0, T]` for `sLpNorm`;
* `bodySourceSliceHolder_of`: complete assembly of `BodySourceSliceHolder` (`PartII-b:F5/2`) from
  `TrainWeightedLp22over3` (`PartII-b:F5/2/1`, the Part I weighted `L^{22/3}` train bound on
  `(0, Σ/ν]`), the local train bound on compact age bands `[a, b] ⊂ (0, ∞)` (body of
  `FlatBvSliceGoodAeNeeded.TrainWeightedLp22over3Loc`, `PartII-b:F5/2/2/2/org/1`), and
  `CylBodySourceProjection` (`PartII-b:F5/2/2`, the cylinder Leray projection
  `g = -P_0(flatBv ...)` on `H¹(C_c)` with zero-circulation curl, for trains with that local bound).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ## 1. Formal Leibniz spatial derivatives of `flatBv` and pointwise jet bounds -/

/-- First spatial partial of `tr.v` in direction `d ∈ {(1,0), (0,1)}`. -/
def trD1 {ν c : ℝ} (tr : B0140.TrainSol ν c) (d : ℝ × ℝ) (s : ℝ) (z : ℝ × ℝ) (i : Fin 2) : ℝ :=
  fderiv ℝ (fun w => tr.v s w i) z d

/-- Second spatial partial of `tr.v` in directions `d₁, d₂ ∈ {(1,0), (0,1)}`. -/
def trD2 {ν c : ℝ} (tr : B0140.TrainSol ν c) (d₁ d₂ : ℝ × ℝ) (s : ℝ) (z : ℝ × ℝ) (i : Fin 2) : ℝ :=
  fderiv ℝ (fun w => fderiv ℝ (fun y => tr.v s y i) w d₁) z d₂

/-- Formal Leibniz `q`-derivative `∂_q(v·∇b0' + b0'·∇v)` using `d00 = ∂_q b0q`, `d10 = ∂_q b0η`. -/
def flatBvQ {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η d00 d10 : CProf) (x : Coord) : CMerid :=
  WithLp.toLp 2 fun i : Fin 2 =>
    ((trD1 tr (1, 0) x.1 x.2 0 : ℝ) : ℂ) * b0q x i +
    ((tr.v x.1 x.2 0 : ℝ) : ℂ) * d00 x i +
    ((trD1 tr (1, 0) x.1 x.2 1 : ℝ) : ℂ) * b0η x i +
    ((tr.v x.1 x.2 1 : ℝ) : ℂ) * d10 x i +
    b0q x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) +
    b0' x 0 * ((trD2 tr (1, 0) (1, 0) x.1 x.2 i : ℝ) : ℂ) +
    b0q x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ) +
    b0' x 1 * ((trD2 tr (0, 1) (1, 0) x.1 x.2 i : ℝ) : ℂ)

/-- Formal Leibniz `η`-derivative `∂_η(v·∇b0' + b0'·∇v)` using `d01 = ∂_η b0q`, `d11 = ∂_η b0η`. -/
def flatBvEta {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η d01 d11 : CProf) (x : Coord) : CMerid :=
  WithLp.toLp 2 fun i : Fin 2 =>
    ((trD1 tr (0, 1) x.1 x.2 0 : ℝ) : ℂ) * b0q x i +
    ((tr.v x.1 x.2 0 : ℝ) : ℂ) * d01 x i +
    ((trD1 tr (0, 1) x.1 x.2 1 : ℝ) : ℂ) * b0η x i +
    ((tr.v x.1 x.2 1 : ℝ) : ℂ) * d11 x i +
    b0η x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) +
    b0' x 0 * ((trD2 tr (1, 0) (0, 1) x.1 x.2 i : ℝ) : ℂ) +
    b0η x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ) +
    b0' x 1 * ((trD2 tr (0, 1) (0, 1) x.1 x.2 i : ℝ) : ℂ)

/-- Componentwise spatial jet envelope of `tr.v s z i` up to second spatial derivatives. -/
def trainJetComp {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ) (i : Fin 2) : ℝ :=
  |tr.v s z i| +
    |trD1 tr (1, 0) s z i| + |trD1 tr (0, 1) s z i| +
    |trD2 tr (1, 0) (1, 0) s z i| + |trD2 tr (1, 0) (0, 1) s z i| +
    |trD2 tr (0, 1) (1, 0) s z i| + |trD2 tr (0, 1) (0, 1) s z i|

/-- Pointwise spatial jet envelope of `tr.v s z` up to second spatial derivatives. -/
def trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 2,
    (|tr.v s z i| +
      |trD1 tr (1, 0) s z i| + |trD1 tr (0, 1) s z i| +
      |trD2 tr (1, 0) (1, 0) s z i| + |trD2 tr (1, 0) (0, 1) s z i| +
      |trD2 tr (0, 1) (1, 0) s z i| + |trD2 tr (0, 1) (0, 1) s z i|)

theorem trainJetComp_nonneg {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ) (i : Fin 2) :
    0 ≤ trainJetComp tr s z i := by
  unfold trainJetComp; positivity

theorem trainJetPt_nonneg {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ) :
    0 ≤ trainJetPt tr s z := by
  unfold trainJetPt
  refine Finset.sum_nonneg fun i _ => ?_
  positivity

theorem trainJetComp_le_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : trainJetComp tr s z i ≤ trainJetPt tr s z :=
  Finset.single_le_sum (fun j _ => trainJetComp_nonneg tr s z j) (Finset.mem_univ i)

theorem abs_tr_v_le_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |tr.v s z i| ≤ trainJetPt tr s z := by
  refine (le_trans ?_ (trainJetComp_le_trainJetPt tr s z i))
  unfold trainJetComp
  linarith [abs_nonneg (trD1 tr (1, 0) s z i), abs_nonneg (trD1 tr (0, 1) s z i),
    abs_nonneg (trD2 tr (1, 0) (1, 0) s z i), abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD1_10_le_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD1 tr (1, 0) s z i| ≤ trainJetPt tr s z := by
  refine (le_trans ?_ (trainJetComp_le_trainJetPt tr s z i))
  unfold trainJetComp
  linarith [abs_nonneg (tr.v s z i), abs_nonneg (trD1 tr (0, 1) s z i),
    abs_nonneg (trD2 tr (1, 0) (1, 0) s z i), abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD1_01_le_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD1 tr (0, 1) s z i| ≤ trainJetPt tr s z := by
  refine (le_trans ?_ (trainJetComp_le_trainJetPt tr s z i))
  unfold trainJetComp
  linarith [abs_nonneg (tr.v s z i), abs_nonneg (trD1 tr (1, 0) s z i),
    abs_nonneg (trD2 tr (1, 0) (1, 0) s z i), abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD2_10_10_le_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD2 tr (1, 0) (1, 0) s z i| ≤ trainJetPt tr s z := by
  refine (le_trans ?_ (trainJetComp_le_trainJetPt tr s z i))
  unfold trainJetComp
  linarith [abs_nonneg (tr.v s z i), abs_nonneg (trD1 tr (1, 0) s z i),
    abs_nonneg (trD1 tr (0, 1) s z i), abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD2_10_01_le_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD2 tr (1, 0) (0, 1) s z i| ≤ trainJetPt tr s z := by
  refine (le_trans ?_ (trainJetComp_le_trainJetPt tr s z i))
  unfold trainJetComp
  linarith [abs_nonneg (tr.v s z i), abs_nonneg (trD1 tr (1, 0) s z i),
    abs_nonneg (trD1 tr (0, 1) s z i), abs_nonneg (trD2 tr (1, 0) (1, 0) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD2_01_10_le_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD2 tr (0, 1) (1, 0) s z i| ≤ trainJetPt tr s z := by
  refine (le_trans ?_ (trainJetComp_le_trainJetPt tr s z i))
  unfold trainJetComp
  linarith [abs_nonneg (tr.v s z i), abs_nonneg (trD1 tr (1, 0) s z i),
    abs_nonneg (trD1 tr (0, 1) s z i), abs_nonneg (trD2 tr (1, 0) (1, 0) s z i),
    abs_nonneg (trD2 tr (1, 0) (0, 1) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD2_01_01_le_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD2 tr (0, 1) (0, 1) s z i| ≤ trainJetPt tr s z := by
  refine (le_trans ?_ (trainJetComp_le_trainJetPt tr s z i))
  unfold trainJetComp
  linarith [abs_nonneg (tr.v s z i), abs_nonneg (trD1 tr (1, 0) s z i),
    abs_nonneg (trD1 tr (0, 1) s z i), abs_nonneg (trD2 tr (1, 0) (1, 0) s z i),
    abs_nonneg (trD2 tr (1, 0) (0, 1) s z i), abs_nonneg (trD2 tr (0, 1) (1, 0) s z i)]

theorem contDiff_train_v_coord {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (i : Fin 2) : ContDiff ℝ ∞ (fun z : B0579.Plane => tr.v s z i) := by
  have hslice : ContDiffOn ℝ ∞ (fun z : B0579.Plane => tr.v s z) univ :=
    tr.isTrain.smooth_v.comp ((contDiffOn_const (c := s)).prodMk contDiffOn_id)
      (fun z _ => (⟨hs, mem_univ z⟩ : ((s, z) : ℝ × B0579.Plane) ∈ Ici 0 ×ˢ univ))
  have hS : ContDiff ℝ ∞ (fun z : B0579.Plane => tr.v s z) := contDiffOn_univ.1 hslice
  have hproj : ContDiff ℝ ∞ (fun f : Fin 2 → ℝ => f i) := by fun_prop
  exact (hproj.comp (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (n := ∞))).comp hS

theorem contDiff_trD1 {ν c : ℝ} (tr : B0140.TrainSol ν c) (d : ℝ × ℝ) {s : ℝ} (hs : 0 ≤ s)
    (i : Fin 2) : ContDiff ℝ ∞ (fun z : B0579.Plane => trD1 tr d s z i) := by
  unfold trD1
  exact ((contDiff_train_v_coord tr hs i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_trD2 {ν c : ℝ} (tr : B0140.TrainSol ν c) (d₁ d₂ : ℝ × ℝ) {s : ℝ} (hs : 0 ≤ s)
    (i : Fin 2) : ContDiff ℝ ∞ (fun z : B0579.Plane => trD2 tr d₁ d₂ s z i) := by
  change ContDiff ℝ ∞ (fun z : B0579.Plane => fderiv ℝ (fun w => trD1 tr d₁ s w i) z d₂)
  exact ((contDiff_trD1 tr d₁ hs i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem continuous_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    Continuous (trainJetPt tr s) := by
  unfold trainJetPt
  refine continuous_finsetSum _ fun i _ => ?_
  have h0 := (contDiff_train_v_coord tr hs i).continuous.abs
  have h10 := (contDiff_trD1 tr (1, 0) hs i).continuous.abs
  have h01 := (contDiff_trD1 tr (0, 1) hs i).continuous.abs
  have h1010 := (contDiff_trD2 tr (1, 0) (1, 0) hs i).continuous.abs
  have h1001 := (contDiff_trD2 tr (1, 0) (0, 1) hs i).continuous.abs
  have h0110 := (contDiff_trD2 tr (0, 1) (1, 0) hs i).continuous.abs
  have h0101 := (contDiff_trD2 tr (0, 1) (0, 1) hs i).continuous.abs
  exact (((((h0.add h10).add h01).add h1010).add h1001).add h0110).add h0101

theorem measurable_trainJetPt {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    Measurable (trainJetPt tr s) :=
  (continuous_trainJetPt tr hs).measurable

/-- Weighted `L^{22/3}(B0579.cell c)` norm of `⟨z⟩^m · trainJetPt tr s z`. -/
def trainSliceNorm22_3 {ν : ℝ} (c m : ℝ) (tr : B0140.TrainSol ν c) (s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun z : B0579.Plane => B0579.jb z ^ (m / 2) * trainJetPt tr s z)
    (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c))

/-! ### Pointwise norm bounds on `flatBv`, `flatBvQ`, `flatBvEta`, and `profCurl` -/

theorem cmerid_norm_le_sum (w : CMerid) : ‖w‖ ≤ ‖w 0‖ + ‖w 1‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg (norm_nonneg (w 0)) (norm_nonneg (w 1))]

theorem norm_real_mul_cmerid_le {a J : ℝ} (ha : |a| ≤ J) (w : CMerid) (i : Fin 2) :
    ‖(a : ℂ) * w i‖ ≤ J * ‖w‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul ha (PiLp.norm_apply_le w i) (norm_nonneg _) ((abs_nonneg a).trans ha)

theorem norm_cmerid_mul_real_le {a J : ℝ} (ha : |a| ≤ J) (w : CMerid) (i : Fin 2) :
    ‖w i * (a : ℂ)‖ ≤ J * ‖w‖ := by
  rw [mul_comm]
  exact norm_real_mul_cmerid_le ha w i

theorem norm_flatBv_apply_le {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf)
    (x : Coord) (i : Fin 2) :
    ‖flatBv tr b0' b0q b0η x i‖ ≤
      trainJetPt tr x.1 x.2 * (2 * ‖b0' x‖ + ‖b0q x‖ + ‖b0η x‖) := by
  have h1 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 0) (b0q x) i
  have h2 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 1) (b0η x) i
  have h3 := norm_cmerid_mul_real_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 i) (b0' x) 0
  have h4 := norm_cmerid_mul_real_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 i) (b0' x) 1
  change ‖((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i +
      b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) +
      b0' x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)‖ ≤ _
  have htri : ‖((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i +
      b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) +
      b0' x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)‖ ≤
      ‖((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i‖ + ‖((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i‖ +
      ‖b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ)‖ +
      ‖b0' x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)‖ := by
    linarith [norm_add_le (((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i +
        ((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i +
        b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ))
        (b0' x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)),
      norm_add_le (((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i +
        ((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i)
        (b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ)),
      norm_add_le (((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i)
        (((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i)]
  linarith

theorem norm_flatBv_le {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf) (x : Coord) :
    ‖flatBv tr b0' b0q b0η x‖ ≤
      4 * trainJetPt tr x.1 x.2 * (‖b0' x‖ + ‖b0q x‖ + ‖b0η x‖) := by
  have hsum := cmerid_norm_le_sum (flatBv tr b0' b0q b0η x)
  have h0 := norm_flatBv_apply_le tr b0' b0q b0η x 0
  have h1 := norm_flatBv_apply_le tr b0' b0q b0η x 1
  have hJ := trainJetPt_nonneg tr x.1 x.2
  nlinarith [norm_nonneg (b0q x), norm_nonneg (b0η x)]

theorem norm_flatBvQ_apply_le {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η d00 d10 : CProf)
    (x : Coord) (i : Fin 2) :
    ‖flatBvQ tr b0' b0q b0η d00 d10 x i‖ ≤
      trainJetPt tr x.1 x.2 * (2 * ‖b0' x‖ + 3 * ‖b0q x‖ + ‖b0η x‖ + ‖d00 x‖ + ‖d10 x‖) := by
  have h1 := norm_real_mul_cmerid_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 0) (b0q x) i
  have h2 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 0) (d00 x) i
  have h3 := norm_real_mul_cmerid_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 1) (b0η x) i
  have h4 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 1) (d10 x) i
  have h5 := norm_cmerid_mul_real_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 i) (b0q x) 0
  have h6 := norm_cmerid_mul_real_le (abs_trD2_10_10_le_trainJetPt tr x.1 x.2 i) (b0' x) 0
  have h7 := norm_cmerid_mul_real_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 i) (b0q x) 1
  have h8 := norm_cmerid_mul_real_le (abs_trD2_01_10_le_trainJetPt tr x.1 x.2 i) (b0' x) 1
  unfold flatBvQ
  set t1 := ((trD1 tr (1, 0) x.1 x.2 0 : ℝ) : ℂ) * b0q x i
  set t2 := ((tr.v x.1 x.2 0 : ℝ) : ℂ) * d00 x i
  set t3 := ((trD1 tr (1, 0) x.1 x.2 1 : ℝ) : ℂ) * b0η x i
  set t4 := ((tr.v x.1 x.2 1 : ℝ) : ℂ) * d10 x i
  set t5 := b0q x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ)
  set t6 := b0' x 0 * ((trD2 tr (1, 0) (1, 0) x.1 x.2 i : ℝ) : ℂ)
  set t7 := b0q x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)
  set t8 := b0' x 1 * ((trD2 tr (0, 1) (1, 0) x.1 x.2 i : ℝ) : ℂ)
  linarith [norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8,
    norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7,
    norm_add_le (t1 + t2 + t3 + t4 + t5) t6,
    norm_add_le (t1 + t2 + t3 + t4) t5,
    norm_add_le (t1 + t2 + t3) t4,
    norm_add_le (t1 + t2) t3,
    norm_add_le t1 t2]

theorem norm_flatBvQ_le {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η d00 d10 : CProf)
    (x : Coord) :
    ‖flatBvQ tr b0' b0q b0η d00 d10 x‖ ≤
      6 * trainJetPt tr x.1 x.2 *
        (‖b0' x‖ + ‖b0q x‖ + ‖b0η x‖ + ‖d00 x‖ + ‖d10 x‖) := by
  have hsum := cmerid_norm_le_sum (flatBvQ tr b0' b0q b0η d00 d10 x)
  have h0 := norm_flatBvQ_apply_le tr b0' b0q b0η d00 d10 x 0
  have h1 := norm_flatBvQ_apply_le tr b0' b0q b0η d00 d10 x 1
  have hJ := trainJetPt_nonneg tr x.1 x.2
  nlinarith [norm_nonneg (b0' x), norm_nonneg (b0η x), norm_nonneg (d00 x), norm_nonneg (d10 x)]

theorem norm_flatBvEta_apply_le {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η d01 d11 : CProf)
    (x : Coord) (i : Fin 2) :
    ‖flatBvEta tr b0' b0q b0η d01 d11 x i‖ ≤
      trainJetPt tr x.1 x.2 * (2 * ‖b0' x‖ + ‖b0q x‖ + 3 * ‖b0η x‖ + ‖d01 x‖ + ‖d11 x‖) := by
  have h1 := norm_real_mul_cmerid_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 0) (b0q x) i
  have h2 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 0) (d01 x) i
  have h3 := norm_real_mul_cmerid_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 1) (b0η x) i
  have h4 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 1) (d11 x) i
  have h5 := norm_cmerid_mul_real_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 i) (b0η x) 0
  have h6 := norm_cmerid_mul_real_le (abs_trD2_10_01_le_trainJetPt tr x.1 x.2 i) (b0' x) 0
  have h7 := norm_cmerid_mul_real_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 i) (b0η x) 1
  have h8 := norm_cmerid_mul_real_le (abs_trD2_01_01_le_trainJetPt tr x.1 x.2 i) (b0' x) 1
  unfold flatBvEta
  set t1 := ((trD1 tr (0, 1) x.1 x.2 0 : ℝ) : ℂ) * b0q x i
  set t2 := ((tr.v x.1 x.2 0 : ℝ) : ℂ) * d01 x i
  set t3 := ((trD1 tr (0, 1) x.1 x.2 1 : ℝ) : ℂ) * b0η x i
  set t4 := ((tr.v x.1 x.2 1 : ℝ) : ℂ) * d11 x i
  set t5 := b0η x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ)
  set t6 := b0' x 0 * ((trD2 tr (1, 0) (0, 1) x.1 x.2 i : ℝ) : ℂ)
  set t7 := b0η x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)
  set t8 := b0' x 1 * ((trD2 tr (0, 1) (0, 1) x.1 x.2 i : ℝ) : ℂ)
  linarith [norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8,
    norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7,
    norm_add_le (t1 + t2 + t3 + t4 + t5) t6,
    norm_add_le (t1 + t2 + t3 + t4) t5,
    norm_add_le (t1 + t2 + t3) t4,
    norm_add_le (t1 + t2) t3,
    norm_add_le t1 t2]

theorem norm_flatBvEta_le {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η d01 d11 : CProf)
    (x : Coord) :
    ‖flatBvEta tr b0' b0q b0η d01 d11 x‖ ≤
      6 * trainJetPt tr x.1 x.2 *
        (‖b0' x‖ + ‖b0q x‖ + ‖b0η x‖ + ‖d01 x‖ + ‖d11 x‖) := by
  have hsum := cmerid_norm_le_sum (flatBvEta tr b0' b0q b0η d01 d11 x)
  have h0 := norm_flatBvEta_apply_le tr b0' b0q b0η d01 d11 x 0
  have h1 := norm_flatBvEta_apply_le tr b0' b0q b0η d01 d11 x 1
  have hJ := trainJetPt_nonneg tr x.1 x.2
  nlinarith [norm_nonneg (b0' x), norm_nonneg (b0q x), norm_nonneg (d01 x), norm_nonneg (d11 x)]

/-- Pointwise sum of the seven norms of `b0', b0q, b0η, D2 i j`. -/
def ptD2Sum (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) : ℝ :=
  ‖b0' x‖ + ‖b0q x‖ + ‖b0η x‖ + ∑ i : Fin 2, ∑ j : Fin 2, ‖D2 i j x‖

theorem ptD2Sum_nonneg (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) :
    0 ≤ ptD2Sum b0' b0q b0η D2 x := by
  unfold ptD2Sum
  positivity

theorem norm_profCurl_flatBv_le {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) :
    ‖profCurl (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
        (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) x‖ ≤
      4 * trainJetPt tr x.1 x.2 * ptD2Sum b0' b0q b0η D2 x := by
  unfold profCurl ptD2Sum
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have hsub := norm_sub_le
    (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) x 1)
    (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) x 0)
  have hq := norm_flatBvQ_apply_le tr b0' b0q b0η (D2 0 0) (D2 1 0) x 1
  have hη := norm_flatBvEta_apply_le tr b0' b0q b0η (D2 0 1) (D2 1 1) x 0
  have hJ := trainJetPt_nonneg tr x.1 x.2
  nlinarith [norm_nonneg (D2 0 0 x), norm_nonneg (D2 0 1 x),
    norm_nonneg (D2 1 0 x), norm_nonneg (D2 1 1 x)]

/-! ## 2. Congruence of `IsBodySource` under a.e. equality on `s > 0` -/

theorem cdot_flatBv_ae_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) {b0 b0' : CProf} (b0q b0η : CProf)
    (hae : ∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : IsPlanarSolTest Ψ) :
    cdot (flatBv tr b0' b0q b0η) Ψ =ᵐ[volume] cdot (flatBv tr b0 b0q b0η) Ψ := by
  filter_upwards [hae] with x hx
  by_cases hp : 0 < x.1
  · simp [cdot, flatBv, hx hp]
  · unfold cdot
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : Ψ x i = 0 :=
      Function.notMem_support.mp (fun h => hp ((hΨ.smooth i).supp (subset_tsupport _ h)).1)
    simp [h0]

theorem isBodySource_congr_b0 {ν c : ℝ} {tr : B0140.TrainSol ν c} {b0 b0' b0q b0η g : CProf}
    (hae : ∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x)
    (h : IsBodySource tr b0' b0q b0η g) : IsBodySource tr b0 b0q b0η g := by
  refine ⟨h.solenoidal, fun Ψ hΨ => ?_⟩
  obtain ⟨hi1, hi2, heq⟩ := h.equation Ψ hΨ
  have hcongr := cdot_flatBv_ae_eq tr b0q b0η hae hΨ
  exact ⟨hi1, hi2.congr hcongr, heq.trans (congrArg Neg.neg (integral_congr_ae hcongr))⟩

/-! ## 3. Spatial Hölder (`1/2 = 3/22 + 4/11`) on the cylinder cell -/

theorem cell_eq_cylCell (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

theorem lintegral_cell_eq_mul_avgμ {c : ℝ} (hc : 0 < c) (f : B0579.Plane → ℝ≥0∞) :
    ∫⁻ z in B0579.cell c, f z =
      ENNReal.ofReal c * ∫⁻ z, f z ∂UnforcedLeray.Cyl.avgμ c := by
  rw [cell_eq_cylCell, UnforcedLeray.Cyl.lintegral_avgμ, ← mul_assoc,
    ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

theorem sliceLpNorm_eq_lintegral' (c : ℝ) (u : CProf) (s : ℝ) :
    sliceLpNorm c u s =
      (∫⁻ z, ‖u (s, z)‖ₑ ^ bgp ∂UnforcedLeray.Cyl.avgμ c) ^ (4 / 11 : ℝ) := by
  unfold sliceLpNorm
  have hp0 : ENNReal.ofReal bgp ≠ 0 := by norm_num [bgp]
  have hpt : ENNReal.ofReal bgp ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hto : (ENNReal.ofReal bgp).toReal = bgp :=
    ENNReal.toReal_ofReal (by norm_num [bgp])
  have hinv : 1 / bgp = (4 / 11 : ℝ) := by norm_num [bgp]
  rw [hto, hinv]

/-- Spatial Hölder on `B0579.cell c` with exponents `22/3` and `bgp = 11/4` (`1/2 = 3/22 + 4/11`):
`‖W · u(s, ·)‖_{L²(cell)} ≤ ‖W‖_{L^{22/3}(cell)} · c^{4/11} · sliceLpNorm c u s`. -/
theorem cell_holder_22_3 {c : ℝ} (hc : 0 < c) {W : B0579.Plane → ℝ}
    (hW : Measurable W) (hW0 : ∀ z, 0 ≤ W z) {u : CProf} (hu : StronglyMeasurable u) (s : ℝ) :
    eLpNorm (fun z : B0579.Plane => ENNReal.ofReal (W z) * ‖u (s, z)‖ₑ) 2
        (volume.restrict (B0579.cell c)) ≤
      eLpNorm W (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ)) * sliceLpNorm c u s := by
  set μ := volume.restrict (B0579.cell c)
  have hpq : Real.HolderConjugate (11 / 3 : ℝ) (11 / 8 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h2_0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2_0 h2_t]
  simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  have hm1 : Measurable (fun z : B0579.Plane => ENNReal.ofReal (W z) ^ (2 : ℝ)) := by fun_prop
  have hm2 : Measurable (fun z : B0579.Plane => ‖u (s, z)‖ₑ ^ (2 : ℝ)) := by
    have : Measurable (fun z : B0579.Plane => u (s, z)) :=
      hu.measurable.comp (measurable_const.prodMk measurable_id)
    exact (this.enorm).pow_const 2
  have hmul_sq : ∀ z : B0579.Plane,
      (ENNReal.ofReal (W z) * ‖u (s, z)‖ₑ) ^ (2 : ℝ) =
        ENNReal.ofReal (W z) ^ (2 : ℝ) * ‖u (s, z)‖ₑ ^ (2 : ℝ) :=
    fun z => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  simp_rw [hmul_sq]
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hm1.aemeasurable hm2.aemeasurable
  have hW_pow : ∀ z : B0579.Plane,
      (ENNReal.ofReal (W z) ^ (2 : ℝ)) ^ (11 / 3 : ℝ) =
        ‖W z‖ₑ ^ (22 / 3 : ℝ) := by
    intro z
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (11 / 3 : ℝ) = 22 / 3 by norm_num,
      ← ofReal_norm, Real.norm_of_nonneg (hW0 z)]
  have hu_pow : ∀ z : B0579.Plane,
      (‖u (s, z)‖ₑ ^ (2 : ℝ)) ^ (11 / 8 : ℝ) = ‖u (s, z)‖ₑ ^ bgp := by
    intro z
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (11 / 8 : ℝ) = bgp by norm_num [bgp]]
  simp_rw [hW_pow, hu_pow] at hhold
  have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  refine (ENNReal.rpow_le_rpow hhold h12).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ h12, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  have he1 : (1 / (11 / 3 : ℝ)) * (1 / 2 : ℝ) = 1 / (ENNReal.ofReal (22 / 3)).toReal := by
    rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num
  have he2 : (1 / (11 / 8 : ℝ)) * (1 / 2 : ℝ) = 4 / 11 := by norm_num
  rw [he1, he2]
  have hW_norm : eLpNorm W (ENNReal.ofReal (22 / 3)) μ =
      (∫⁻ z, ‖W z‖ₑ ^ (22 / 3 : ℝ) ∂μ) ^ (1 / (ENNReal.ofReal (22 / 3)).toReal) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 22 / 3)]
  rw [← hW_norm]
  have hu_cell : (∫⁻ z, ‖u (s, z)‖ₑ ^ bgp ∂μ) ^ (4 / 11 : ℝ) =
      ENNReal.ofReal (c ^ (4 / 11 : ℝ)) * sliceLpNorm c u s := by
    rw [lintegral_cell_eq_mul_avgμ hc,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4 / 11),
      ENNReal.ofReal_rpow_of_nonneg hc.le (by norm_num : (0 : ℝ) ≤ 4 / 11),
      ← sliceLpNorm_eq_lintegral' c u s]
  rw [hu_cell, ← mul_assoc]

theorem cell_holder_22_3_real {c : ℝ} (hc : 0 < c) {W : B0579.Plane → ℝ}
    (hW : Measurable W) (hW0 : ∀ z, 0 ≤ W z) {u : CProf} (hu : StronglyMeasurable u) (s : ℝ) :
    eLpNorm (fun z : B0579.Plane => W z * ‖u (s, z)‖) 2 (volume.restrict (B0579.cell c)) ≤
      (eLpNorm W (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceLpNorm c u s := by
  have heq : eLpNorm (fun z : B0579.Plane => W z * ‖u (s, z)‖) 2 (volume.restrict (B0579.cell c)) =
      eLpNorm (fun z : B0579.Plane => ENNReal.ofReal (W z) * ‖u (s, z)‖ₑ) 2
        (volume.restrict (B0579.cell c)) := by
    rw [← eLpNorm_enorm]
    congr 1; funext z
    rw [enorm_mul, Real.enorm_eq_ofReal (hW0 z), enorm_norm]
  rw [heq]
  exact cell_holder_22_3 hc hW hW0 hu s

/-! ## 4. Minkowski subadditivity and monotonicity for `sLpNorm` -/

theorem sLpNorm_add_le (b T : ℝ) {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    sLpNorm b T (fun s => f s + g s) ≤ sLpNorm b T f + sLpNorm b T g := by
  unfold sLpNorm
  have hinv : (4 / 11 : ℝ) = 1 / bgp := by norm_num [bgp]
  rw [hinv]
  exact ENNReal.lintegral_Lp_add_le hf.aemeasurable hg.aemeasurable bgp_gt_one.le

theorem sLpNorm_const_mul (b T : ℝ) (K : ℝ≥0∞) (hK : K ≠ ⊤) (f : ℝ → ℝ≥0∞) :
    sLpNorm b T (fun s => K * f s) = K * sLpNorm b T f := by
  unfold sLpNorm
  have hbgp : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have h411 : (0 : ℝ) ≤ 4 / 11 := by norm_num
  have hmul : bgp * (4 / 11 : ℝ) = 1 := by norm_num [bgp]
  have hpow : ∀ s, (K * f s) ^ bgp = K ^ bgp * f s ^ bgp :=
    fun s => ENNReal.mul_rpow_of_nonneg _ _ hbgp
  simp_rw [hpow]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hbgp hK).ne,
    ENNReal.mul_rpow_of_nonneg _ _ h411, ← ENNReal.rpow_mul, hmul, ENNReal.rpow_one]

theorem sLpNorm_mono_Ioc (b T : ℝ) {f g : ℝ → ℝ≥0∞}
    (h : ∀ s ∈ Ioc 0 T, f s ≤ g s) :
    sLpNorm b T f ≤ sLpNorm b T g := by
  unfold sLpNorm
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  exact ENNReal.rpow_le_rpow (h s hs) (by norm_num [bgp])

/-! ## 5. Slice-level `H¹` and `X_m` bounds on `flatBv` and `profCurl` -/

/-- Sum of the seven `sliceLpNorm`s of `b0', b0q, b0η, D2 i j` at age `s`. -/
def sliceD2Sum (c : ℝ) (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf) (s : ℝ) : ℝ≥0∞ :=
  sliceLpNorm c b0' s + sliceLpNorm c b0q s + sliceLpNorm c b0η s +
    ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s

theorem measurable_sliceD2Sum (c : ℝ) {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hm0 : Measurable (sliceLpNorm c b0'))
    (hmq : Measurable (sliceLpNorm c b0q))
    (hmη : Measurable (sliceLpNorm c b0η))
    (hmD2 : ∀ i j, Measurable (sliceLpNorm c (D2 i j))) :
    Measurable (sliceD2Sum c b0' b0q b0η D2) := by
  unfold sliceD2Sum
  exact ((hm0.add hmq).add hmη).add
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hmD2 i j)

theorem sLpNorm_sliceD2Sum_le (b T c : ℝ) {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hm0 : Measurable (sliceLpNorm c b0'))
    (hmq : Measurable (sliceLpNorm c b0q))
    (hmη : Measurable (sliceLpNorm c b0η))
    (hmD2 : ∀ i j, Measurable (sliceLpNorm c (D2 i j))) :
    sLpNorm b T (sliceD2Sum c b0' b0q b0η D2) ≤
      sLpNorm b T (sliceLpNorm c b0') +
        sLpNorm b T (sliceLpNorm c b0q) +
        sLpNorm b T (sliceLpNorm c b0η) +
        ∑ i : Fin 2, ∑ j : Fin 2, sLpNorm b T (sliceLpNorm c (D2 i j)) := by
  have hD2_eq : (fun s => ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s) =
      fun s => (sliceLpNorm c (D2 0 0) s + sliceLpNorm c (D2 0 1) s) +
        (sliceLpNorm c (D2 1 0) s + sliceLpNorm c (D2 1 1) s) := by
    funext s
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have hm_0 : Measurable (fun s => sliceLpNorm c (D2 0 0) s + sliceLpNorm c (D2 0 1) s) :=
    (hmD2 0 0).add (hmD2 0 1)
  have hm_1 : Measurable (fun s => sliceLpNorm c (D2 1 0) s + sliceLpNorm c (D2 1 1) s) :=
    (hmD2 1 0).add (hmD2 1 1)
  have hm_D2 : Measurable (fun s => ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s) := by
    rw [hD2_eq]; exact hm_0.add hm_1
  have hm_0q : Measurable (fun s => sliceLpNorm c b0' s + sliceLpNorm c b0q s) := hm0.add hmq
  have hm_0qη : Measurable (fun s =>
      sliceLpNorm c b0' s + sliceLpNorm c b0q s + sliceLpNorm c b0η s) := hm_0q.add hmη
  unfold sliceD2Sum
  calc sLpNorm b T (fun s =>
          (sliceLpNorm c b0' s + sliceLpNorm c b0q s + sliceLpNorm c b0η s) +
            ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s)
      ≤ sLpNorm b T (fun s => sliceLpNorm c b0' s + sliceLpNorm c b0q s + sliceLpNorm c b0η s) +
          sLpNorm b T (fun s => ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s) :=
        sLpNorm_add_le b T hm_0qη hm_D2
    _ ≤ (sLpNorm b T (fun s => sliceLpNorm c b0' s + sliceLpNorm c b0q s) +
          sLpNorm b T (sliceLpNorm c b0η)) +
          sLpNorm b T (fun s => ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s) := by
        gcongr; exact sLpNorm_add_le b T hm_0q hmη
    _ ≤ (sLpNorm b T (sliceLpNorm c b0') + sLpNorm b T (sliceLpNorm c b0q) +
          sLpNorm b T (sliceLpNorm c b0η)) +
          sLpNorm b T (fun s => ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s) := by
        gcongr; exact sLpNorm_add_le b T hm0 hmq
    _ ≤ (sLpNorm b T (sliceLpNorm c b0') + sLpNorm b T (sliceLpNorm c b0q) +
          sLpNorm b T (sliceLpNorm c b0η)) +
          ∑ i : Fin 2, ∑ j : Fin 2, sLpNorm b T (sliceLpNorm c (D2 i j)) := by
        gcongr
        rw [hD2_eq, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
        calc sLpNorm b T (fun s =>
              (sliceLpNorm c (D2 0 0) s + sliceLpNorm c (D2 0 1) s) +
                (sliceLpNorm c (D2 1 0) s + sliceLpNorm c (D2 1 1) s))
            ≤ sLpNorm b T (fun s => sliceLpNorm c (D2 0 0) s + sliceLpNorm c (D2 0 1) s) +
                sLpNorm b T (fun s => sliceLpNorm c (D2 1 0) s + sliceLpNorm c (D2 1 1) s) :=
              sLpNorm_add_le b T hm_0 hm_1
          _ ≤ (sLpNorm b T (sliceLpNorm c (D2 0 0)) + sLpNorm b T (sliceLpNorm c (D2 0 1))) +
                (sLpNorm b T (sliceLpNorm c (D2 1 0)) + sLpNorm b T (sliceLpNorm c (D2 1 1))) :=
              add_le_add (sLpNorm_add_le b T (hmD2 0 0) (hmD2 0 1))
                (sLpNorm_add_le b T (hmD2 1 0) (hmD2 1 1))

theorem eLpNorm_mul_ptD2Sum_le {c : ℝ} (hc : 0 < c) {W : B0579.Plane → ℝ}
    (hW : Measurable W) (hW0 : ∀ z, 0 ≤ W z) {b0' b0q b0η : CProf}
    {D2 : Fin 2 → Fin 2 → CProf} (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j)) (s : ℝ) :
    eLpNorm (fun z : B0579.Plane => W z * ptD2Sum b0' b0q b0η D2 (s, z)) 2
        (volume.restrict (B0579.cell c)) ≤
      (eLpNorm W (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceD2Sum c b0' b0q b0η D2 s := by
  set μ := volume.restrict (B0579.cell c)
  have hm_u : ∀ {u : CProf}, StronglyMeasurable u →
      AEStronglyMeasurable (fun z : B0579.Plane => W z * ‖u (s, z)‖) μ := fun hu =>
    (hW.mul ((hu.measurable.comp (measurable_const.prodMk measurable_id)).norm)).aestronglyMeasurable
  have h12 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
  have hm0 := hm_u hsm0
  have hmq := hm_u hsmq
  have hmη := hm_u hsmη
  have hm00 := hm_u (hsmD2 0 0)
  have hm01 := hm_u (hsmD2 0 1)
  have hm10 := hm_u (hsmD2 1 0)
  have hm11 := hm_u (hsmD2 1 1)
  have heq : (fun z : B0579.Plane => W z * ptD2Sum b0' b0q b0η D2 (s, z)) =
      (((fun z => W z * ‖b0' (s, z)‖) + (fun z => W z * ‖b0q (s, z)‖) +
        (fun z => W z * ‖b0η (s, z)‖)) +
        (((fun z => W z * ‖D2 0 0 (s, z)‖) + (fun z => W z * ‖D2 0 1 (s, z)‖)) +
          ((fun z => W z * ‖D2 1 0 (s, z)‖) + (fun z => W z * ‖D2 1 1 (s, z)‖)))) := by
    funext z
    unfold ptD2Sum
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Pi.add_apply]
    ring
  rw [heq]
  have h_add1 := eLpNorm_add_le ((hm0.add hmq).add hmη)
    ((hm00.add hm01).add (hm10.add hm11)) h12
  have h_add2 := eLpNorm_add_le (hm0.add hmq) hmη h12
  have h_add3 := eLpNorm_add_le hm0 hmq h12
  have h_add4 := eLpNorm_add_le (hm00.add hm01) (hm10.add hm11) h12
  have h_add5 := eLpNorm_add_le hm00 hm01 h12
  have h_add6 := eLpNorm_add_le hm10 hm11 h12
  have hb0 := cell_holder_22_3_real hc hW hW0 hsm0 s
  have hbq := cell_holder_22_3_real hc hW hW0 hsmq s
  have hbη := cell_holder_22_3_real hc hW hW0 hsmη s
  have hb00 := cell_holder_22_3_real hc hW hW0 (hsmD2 0 0) s
  have hb01 := cell_holder_22_3_real hc hW hW0 (hsmD2 0 1) s
  have hb10 := cell_holder_22_3_real hc hW hW0 (hsmD2 1 0) s
  have hb11 := cell_holder_22_3_real hc hW hW0 (hsmD2 1 1) s
  unfold sliceD2Sum
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  calc eLpNorm (((fun z => W z * ‖b0' (s, z)‖) + (fun z => W z * ‖b0q (s, z)‖) +
          (fun z => W z * ‖b0η (s, z)‖)) +
          (((fun z => W z * ‖D2 0 0 (s, z)‖) + (fun z => W z * ‖D2 0 1 (s, z)‖)) +
            ((fun z => W z * ‖D2 1 0 (s, z)‖) + (fun z => W z * ‖D2 1 1 (s, z)‖)))) 2 μ
      ≤ (eLpNorm (fun z => W z * ‖b0' (s, z)‖) 2 μ +
          eLpNorm (fun z => W z * ‖b0q (s, z)‖) 2 μ +
          eLpNorm (fun z => W z * ‖b0η (s, z)‖) 2 μ) +
          ((eLpNorm (fun z => W z * ‖D2 0 0 (s, z)‖) 2 μ +
            eLpNorm (fun z => W z * ‖D2 0 1 (s, z)‖) 2 μ) +
          (eLpNorm (fun z => W z * ‖D2 1 0 (s, z)‖) 2 μ +
            eLpNorm (fun z => W z * ‖D2 1 1 (s, z)‖) 2 μ)) := by
        refine h_add1.trans (add_le_add ?_ ?_)
        · exact h_add2.trans (add_le_add h_add3 le_rfl)
        · exact h_add4.trans (add_le_add h_add5 h_add6)
    _ ≤ ((eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c b0' s +
          eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c b0q s +
          eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c b0η s) +
          ((eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c (D2 0 0) s +
            eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c (D2 0 1) s) +
          (eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c (D2 1 0) s +
            eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c (D2 1 1) s))) := by
        gcongr
    _ = (eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          (sliceLpNorm c b0' s + sliceLpNorm c b0q s + sliceLpNorm c b0η s +
            ((sliceLpNorm c (D2 0 0) s + sliceLpNorm c (D2 0 1) s) +
              (sliceLpNorm c (D2 1 0) s + sliceLpNorm c (D2 1 1) s))) := by
        ring

theorem eLpNorm_trainJetPt_le_trainSliceNorm22_3 {ν c m : ℝ} (hm : 0 ≤ m)
    (tr : B0140.TrainSol ν c) (s : ℝ) :
    eLpNorm (trainJetPt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) ≤
      trainSliceNorm22_3 c m tr s := by
  unfold trainSliceNorm22_3
  refine eLpNorm_mono_real fun z => ?_
  have hJ := trainJetPt_nonneg tr s z
  have hjb1 : 1 ≤ B0579.jb z := by
    unfold B0579.jb
    nlinarith [sq_nonneg z.1, sq_nonneg z.2]
  have hpow1 : 1 ≤ B0579.jb z ^ (m / 2) := Real.one_le_rpow hjb1 (by positivity)
  rw [Real.norm_of_nonneg hJ]
  exact le_mul_of_one_le_left hJ hpow1

theorem eLpNorm_le_of_norm_le_jet_ptD2Sum {ν c m K : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (hK : 0 ≤ K)
    (tr : B0140.TrainSol ν c) {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    {s : ℝ} (hs : 0 ≤ s) {E : Type*} [NormedAddCommGroup E] (F : B0579.Plane → E)
    (hF : ∀ z : B0579.Plane,
      ‖F z‖ ≤ K * (trainJetPt tr s z * ptD2Sum b0' b0q b0η D2 (s, z))) :
    eLpNorm F 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal K *
        (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
        sliceD2Sum c b0' b0q b0η D2 s := by
  set μ := volume.restrict (B0579.cell c)
  have hsmul : (fun z : B0579.Plane => K * (trainJetPt tr s z * ptD2Sum b0' b0q b0η D2 (s, z))) =
      K • (fun z : B0579.Plane => trainJetPt tr s z * ptD2Sum b0' b0q b0η D2 (s, z)) := by
    funext z; simp [smul_eq_mul]
  calc eLpNorm F 2 μ
      ≤ eLpNorm (fun z : B0579.Plane =>
          K * (trainJetPt tr s z * ptD2Sum b0' b0q b0η D2 (s, z))) 2 μ :=
        eLpNorm_mono_real hF
    _ = ENNReal.ofReal K *
          eLpNorm (fun z : B0579.Plane =>
            trainJetPt tr s z * ptD2Sum b0' b0q b0η D2 (s, z)) 2 μ := by
        rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal hK]
    _ ≤ ENNReal.ofReal K *
          ((eLpNorm (trainJetPt tr s) (ENNReal.ofReal (22 / 3)) μ *
            ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceD2Sum c b0' b0q b0η D2 s) := by
        gcongr
        exact eLpNorm_mul_ptD2Sum_le hc (measurable_trainJetPt tr hs)
          (trainJetPt_nonneg tr s) hsm0 hsmq hsmη hsmD2 s
    _ ≤ ENNReal.ofReal K *
          ((trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
            sliceD2Sum c b0' b0q b0η D2 s) := by
        gcongr
        exact eLpNorm_trainJetPt_le_trainSliceNorm22_3 hm tr s
    _ = ENNReal.ofReal K *
          (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          sliceD2Sum c b0' b0q b0η D2 s := by
        ring

/-- **Slice-level `H¹(C_c)` bound on `flatBv` and its formal Leibniz derivatives** (`1/2 = 3/22 + 4/11`
spatial Hölder on `B0579.cell c`). -/
theorem sliceH1Norm_flatBv_le {ν c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    (tr : B0140.TrainSol ν c) {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    {s : ℝ} (hs : 0 ≤ s) :
    sliceH1Norm c (flatBv tr b0' b0q b0η)
        (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
        (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s ≤
      ENNReal.ofReal 16 *
        (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
        sliceD2Sum c b0' b0q b0η D2 s := by
  have hb0 : eLpNorm (fun z => flatBv tr b0' b0q b0η (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal 4 *
        (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
        sliceD2Sum c b0' b0q b0η D2 s := by
    refine eLpNorm_le_of_norm_le_jet_ptD2Sum hc hm (by norm_num) tr hsm0 hsmq hsmη hsmD2 hs _
      fun z => ?_
    have hpt := norm_flatBv_le tr b0' b0q b0η (s, z)
    have hJ := trainJetPt_nonneg tr s z
    have hD2 : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖D2 i j (s, z)‖ :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
    unfold ptD2Sum
    nlinarith
  have hbq : eLpNorm (fun z => flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) (s, z)) 2
        (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal 6 *
        (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
        sliceD2Sum c b0' b0q b0η D2 s := by
    refine eLpNorm_le_of_norm_le_jet_ptD2Sum hc hm (by norm_num) tr hsm0 hsmq hsmη hsmD2 hs _
      fun z => ?_
    have hpt := norm_flatBvQ_le tr b0' b0q b0η (D2 0 0) (D2 1 0) (s, z)
    have hJ := trainJetPt_nonneg tr s z
    unfold ptD2Sum
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    nlinarith [norm_nonneg (D2 0 1 (s, z)), norm_nonneg (D2 1 1 (s, z))]
  have hbη : eLpNorm (fun z => flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) (s, z)) 2
        (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal 6 *
        (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
        sliceD2Sum c b0' b0q b0η D2 s := by
    refine eLpNorm_le_of_norm_le_jet_ptD2Sum hc hm (by norm_num) tr hsm0 hsmq hsmη hsmD2 hs _
      fun z => ?_
    have hpt := norm_flatBvEta_le tr b0' b0q b0η (D2 0 1) (D2 1 1) (s, z)
    have hJ := trainJetPt_nonneg tr s z
    unfold ptD2Sum
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    nlinarith [norm_nonneg (D2 0 0 (s, z)), norm_nonneg (D2 1 0 (s, z))]
  unfold sliceH1Norm
  have h16 : ENNReal.ofReal 4 + ENNReal.ofReal 6 + ENNReal.ofReal 6 = ENNReal.ofReal 16 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  calc eLpNorm (fun z => flatBv tr b0' b0q b0η (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) (s, z)) 2
          (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) (s, z)) 2
          (volume.restrict (B0579.cell c))
      ≤ ENNReal.ofReal 4 * (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          sliceD2Sum c b0' b0q b0η D2 s +
        ENNReal.ofReal 6 * (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          sliceD2Sum c b0' b0q b0η D2 s +
        ENNReal.ofReal 6 * (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          sliceD2Sum c b0' b0q b0η D2 s := add_le_add (add_le_add hb0 hbq) hbη
    _ = (ENNReal.ofReal 4 + ENNReal.ofReal 6 + ENNReal.ofReal 6) *
          (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          sliceD2Sum c b0' b0q b0η D2 s := by ring
    _ = ENNReal.ofReal 16 *
          (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          sliceD2Sum c b0' b0q b0η D2 s := by rw [h16]

/-- **Slice-level `X_m` bound on the curl of `flatBv`** (`1/2 = 3/22 + 4/11` weighted spatial
Hölder on `B0579.cell c`). -/
theorem sliceXmNorm_flatBv_curl_le {ν c m : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    {s : ℝ} (hs : 0 ≤ s) :
    sliceXmNorm c m
        (profCurl (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
          (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1))) s ≤
      ENNReal.ofReal 4 *
        (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
        sliceD2Sum c b0' b0q b0η D2 s := by
  unfold sliceXmNorm
  set w := profCurl (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
    (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1))
  set μ := volume.restrict (B0579.cell c)
  set W : B0579.Plane → ℝ := fun z => B0579.jb z ^ (m / 2) * trainJetPt tr s z
  have hW_meas : Measurable W :=
    (B0579.continuous_jb_rpow (m / 2)).measurable.mul (measurable_trainJetPt tr hs)
  have hW_nonneg : ∀ z, 0 ≤ W z := fun z =>
    mul_nonneg (Real.rpow_nonneg (B0579.jb_pos z).le _) (trainJetPt_nonneg tr s z)
  have hxm : eLpNorm (fun z => w (s, z)) 2 (B0579.cellMeasure c m) =
      eLpNorm (fun z => B0579.jb z ^ (m / 2) * ‖w (s, z)‖) 2 μ := by
    rw [← eLpNorm_norm (fun z => w (s, z)), B0579.eLpNorm_cellMeasure]
  rw [hxm]
  have hsmul : (fun z : B0579.Plane => 4 * (W z * ptD2Sum b0' b0q b0η D2 (s, z))) =
      (4 : ℝ) • (fun z : B0579.Plane => W z * ptD2Sum b0' b0q b0η D2 (s, z)) := by
    funext z; simp [smul_eq_mul]
  calc eLpNorm (fun z => B0579.jb z ^ (m / 2) * ‖w (s, z)‖) 2 μ
      ≤ eLpNorm (fun z : B0579.Plane => 4 * (W z * ptD2Sum b0' b0q b0η D2 (s, z))) 2 μ := by
        refine eLpNorm_mono_real fun z => ?_
        have hjb : 0 ≤ B0579.jb z ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos z).le _
        have h1 : 0 ≤ B0579.jb z ^ (m / 2) * ‖w (s, z)‖ := mul_nonneg hjb (norm_nonneg _)
        rw [Real.norm_of_nonneg h1]
        have hpt := norm_profCurl_flatBv_le tr b0' b0q b0η D2 (s, z)
        have hmul := mul_le_mul_of_nonneg_left hpt hjb
        dsimp [W]
        linarith
    _ = ENNReal.ofReal 4 *
          eLpNorm (fun z : B0579.Plane => W z * ptD2Sum b0' b0q b0η D2 (s, z)) 2 μ := by
        rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ ENNReal.ofReal 4 *
          ((trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
            sliceD2Sum c b0' b0q b0η D2 s) := by
        gcongr
        exact eLpNorm_mul_ptD2Sum_le hc hW_meas hW_nonneg hsm0 hsmq hsmη hsmD2 s
    _ = ENNReal.ofReal 4 *
          (trainSliceNorm22_3 c m tr s * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          sliceD2Sum c b0' b0q b0η D2 s := by
        ring

/-! ## 6. Leaf propositions and conditional assembly of `BodySourceSliceHolder` -/

/-- **Sub-leaf A (`PartII-b:F5/2/1`, `TrainWeightedLp22over3`)**: Part I weighted `L^{22/3}` bound
on the train jets up to order 2 on the slow-age band `(0, Σ/ν]` (SP 2228-2233, 2050-2052, Part I
Lemma `sct:heat` SP 437-481). -/
def TrainWeightedLp22over3 : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_tr : ℝ) (k_tr : ℕ) (ν₀ : ℝ), 0 < C_tr ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ s ∈ Ioc 0 (Sig / p.ν),
        trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) ≤
          ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹)

/-- **Sub-leaf B (`PartII-b:F5/2/2`, `CylBodySourceProjection`)**: cylinder Leray projection
`g = -P_0(flatBv ...)` in `H¹(C_c)` with `curl g = -curl(flatBv ...)`, zero circulation on the
cell, and slice `H¹` and `X_m` bounds controlled by `trainSliceNorm22_3 · c^{4/11} · sliceD2Sum`
(SP 2228-2239, using `sliceH1Norm_flatBv_le` and `sliceXmNorm_flatBv_curl_le` proved above).
The train enters through its weighted `L^{22/3}` jet norm (SP 2228-2233: "Spatial Hölder with
`22/3`"), assumed bounded on every compact age band `[a, b] ⊂ (0, ∞)`; an arbitrary
`B0140.TrainSol` has no such bound. In `bodySourceSliceHolder_of` this hypothesis is supplied by
the local train bound `FlatBvSliceGoodAeNeeded.TrainWeightedLp22over3Loc`. -/
def CylBodySourceProjection : Prop :=
  ∃ K_proj : ℝ, 0 < K_proj ∧
    ∀ (m : ℝ), 8 < m → ∀ (p : Params) (T : ℝ), 0 < p.c → 0 < T →
    (∀ a b : ℝ, 0 < a → ∃ C : ℝ, ∀ s ∈ Icc a b,
      trainSliceNorm22_3 p.c m p.train s ≤ ENNReal.ofReal C) →
    ∀ (b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
      InFlatClass p.c bgp b0 →
      (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
      InHr p.c bgp b0' → InHr p.c bgp (sqrtS b0q) → InHr p.c bgp (sqrtS b0η) →
      (∀ i j, InHr p.c bgp (mulS (D2 i j))) →
      StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
      (∀ i j, StronglyMeasurable (D2 i j)) →
      HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
      HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
      HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
      ∃ g gq gη : CProf,
        QPeriodic p.c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
        IsBodySource p.train b0' b0q b0η g ∧
        Measurable (sliceH1Norm p.c g gq gη) ∧
        Measurable (sliceXmNorm p.c m (profCurl gq gη)) ∧
        (∀ s ∈ Ioc 0 T,
          sliceH1Norm p.c g gq gη s ≤
            ENNReal.ofReal K_proj *
              (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
              sliceD2Sum p.c b0' b0q b0η D2 s ∧
          sliceXmNorm p.c m (profCurl gq gη) s ≤
            ENNReal.ofReal K_proj *
              (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
              sliceD2Sum p.c b0' b0q b0η D2 s) ∧
        (∀ᵐ s ∂volume, s ∈ Ioc 0 T →
          IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell p.c) volume ∧
            ∫ z in B0579.cell p.c, profCurl gq gη (s, z) = 0)

/-- Reduction of `CylBodySourceProjection` to the cylinder Leray projection `P_0` stability in
`H¹(C_c)` and curl preservation in `X_m(C_c)`, using `sliceH1Norm_flatBv_le` and
`sliceXmNorm_flatBv_curl_le`. -/
theorem cylBodySourceProjection_of_leray
    (hL : ∃ K_L : ℝ, 0 < K_L ∧
      ∀ (m : ℝ), 8 < m → ∀ (p : Params) (T : ℝ), 0 < p.c → 0 < T →
      (∀ a b : ℝ, 0 < a → ∃ C : ℝ, ∀ s ∈ Icc a b,
        trainSliceNorm22_3 p.c m p.train s ≤ ENNReal.ofReal C) →
      ∀ (b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
        InFlatClass p.c bgp b0 →
        (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
        InHr p.c bgp b0' → InHr p.c bgp (sqrtS b0q) → InHr p.c bgp (sqrtS b0η) →
        (∀ i j, InHr p.c bgp (mulS (D2 i j))) →
        StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
        (∀ i j, StronglyMeasurable (D2 i j)) →
        HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
        HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
        HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
        ∃ g gq gη : CProf,
          QPeriodic p.c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
          IsBodySource p.train b0' b0q b0η g ∧
          Measurable (sliceH1Norm p.c g gq gη) ∧
          Measurable (sliceXmNorm p.c m (profCurl gq gη)) ∧
          (∀ s ∈ Ioc 0 T,
            sliceH1Norm p.c g gq gη s ≤
              ENNReal.ofReal K_L *
                sliceH1Norm p.c (flatBv p.train b0' b0q b0η)
                  (flatBvQ p.train b0' b0q b0η (D2 0 0) (D2 1 0))
                  (flatBvEta p.train b0' b0q b0η (D2 0 1) (D2 1 1)) s ∧
            sliceXmNorm p.c m (profCurl gq gη) s ≤
              ENNReal.ofReal K_L *
                sliceXmNorm p.c m
                  (profCurl (flatBvQ p.train b0' b0q b0η (D2 0 0) (D2 1 0))
                    (flatBvEta p.train b0' b0q b0η (D2 0 1) (D2 1 1))) s) ∧
          (∀ᵐ s ∂volume, s ∈ Ioc 0 T →
            IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell p.c) volume ∧
              ∫ z in B0579.cell p.c, profCurl gq gη (s, z) = 0)) :
    CylBodySourceProjection := by
  obtain ⟨K_L, hKL, hL_ex⟩ := hL
  refine ⟨16 * K_L, by positivity,
    fun m hm p T hcp hTp hTrp b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 => ?_⟩
  obtain ⟨g, gq, gη, hgper, hgwq, hgwη, hgsrc, hmg1, hmgc, hbd, hcirc⟩ :=
    hL_ex m hm p T hcp hTp hTrp b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11
  refine ⟨g, gq, gη, hgper, hgwq, hgwη, hgsrc, hmg1, hmgc, fun s hs => ?_, hcirc⟩
  have hm0 : 0 ≤ m := by linarith
  have hs0 : 0 ≤ s := hs.1.le
  have h16KL : ENNReal.ofReal K_L * ENNReal.ofReal 16 = ENNReal.ofReal (16 * K_L) := by
    rw [← ENNReal.ofReal_mul hKL.le, mul_comm]
  have h4le16 : ENNReal.ofReal K_L * ENNReal.ofReal 4 ≤ ENNReal.ofReal (16 * K_L) := by
    rw [← h16KL]
    gcongr
    norm_num
  refine ⟨?_, ?_⟩
  · calc sliceH1Norm p.c g gq gη s
        ≤ ENNReal.ofReal K_L *
            sliceH1Norm p.c (flatBv p.train b0' b0q b0η)
              (flatBvQ p.train b0' b0q b0η (D2 0 0) (D2 1 0))
              (flatBvEta p.train b0' b0q b0η (D2 0 1) (D2 1 1)) s := (hbd s hs).1
      _ ≤ ENNReal.ofReal K_L *
            (ENNReal.ofReal 16 *
              (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
              sliceD2Sum p.c b0' b0q b0η D2 s) := by
          gcongr
          exact sliceH1Norm_flatBv_le hcp hm0 p.train hsm0 hsmq hsmη hsmD2 hs0
      _ = ENNReal.ofReal (16 * K_L) *
            (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
            sliceD2Sum p.c b0' b0q b0η D2 s := by
          rw [← mul_assoc, ← mul_assoc, h16KL]
  · calc sliceXmNorm p.c m (profCurl gq gη) s
        ≤ ENNReal.ofReal K_L *
            sliceXmNorm p.c m
              (profCurl (flatBvQ p.train b0' b0q b0η (D2 0 0) (D2 1 0))
                (flatBvEta p.train b0' b0q b0η (D2 0 1) (D2 1 1))) s := (hbd s hs).2
      _ ≤ ENNReal.ofReal K_L *
            (ENNReal.ofReal 4 *
              (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
              sliceD2Sum p.c b0' b0q b0η D2 s) := by
          gcongr
          exact sliceXmNorm_flatBv_curl_le hcp p.train hsm0 hsmq hsmη hsmD2 hs0
      _ = (ENNReal.ofReal K_L * ENNReal.ofReal 4) *
            (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
            sliceD2Sum p.c b0' b0q b0η D2 s := by
          rw [← mul_assoc, ← mul_assoc]
      _ ≤ ENNReal.ofReal (16 * K_L) *
            (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
            sliceD2Sum p.c b0' b0q b0η D2 s := by
          gcongr

/-- **Conditional assembly of `BodySourceSliceHolder` (`PartII-b:F5/2`)** from
`TrainWeightedLp22over3` (`PartII-b:F5/2/1`), the local train bound `hTrLoc` (the body of
`FlatBvSliceGoodAeNeeded.TrainWeightedLp22over3Loc`, task `PartII-b:F5/2/2/2/org/1`; SP 2228-2233,
Part I Lemma `sct:heat` SP 437-481), and `CylBodySourceProjection` (`PartII-b:F5/2/2`).
Composed by `PartII-b:F5/2` (`Tasks/BodySource/SliceHolder.lean`). -/
theorem bodySourceSliceHolder_of (hTr : TrainWeightedLp22over3)
    (hTrLoc : ∀ m : ℝ, 8 < m → ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ a b : ℝ, 0 < a → ∃ C : ℝ, ∀ s ∈ Icc a b,
        trainSliceNorm22_3 p.c m p.train s ≤ ENNReal.ofReal C)
    (hProj : CylBodySourceProjection) :
    UnforcedLeray.Short.IIb.BodySourceSliceHolder := by
  intro m hm Sig hSig dm dp hdm
  obtain ⟨C_tr, k_tr, ν₀, hCtr, hν₀, hTr_bd⟩ := hTr m hm Sig hSig dm dp hdm
  obtain ⟨ν₁, hν₁, hTrLoc_bd⟩ := hTrLoc m hm dm dp hdm
  obtain ⟨K_proj, hKproj, hProj_ex⟩ := hProj
  refine ⟨2 * K_proj * C_tr, k_tr, min ν₀ ν₁, by positivity, lt_min hν₀ hν₁,
    fun p d hreg hνmin b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 hm0 hmq hmη hmD2 => ?_⟩
  have hν : p.ν ≤ ν₀ := hνmin.trans (min_le_left _ _)
  have hνp : 0 < p.ν := p.ν_pos
  have hcp : 0 < p.c := by rw [hreg.c_eq]; positivity
  set T : ℝ := Sig / p.ν
  have hTp : 0 < T := div_pos hSig hνp
  obtain ⟨g, gq, gη, hgper, hgwq, hgwη, hgsrc', hmg1, hmgc, hslice_bd, hg_circ⟩ :=
    hProj_ex m hm p T hcp hTp (hTrLoc_bd p d hreg (hνmin.trans (min_le_right _ _)))
      b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11
  have hgsrc : IsBodySource p.train b0 b0q b0η g := isBodySource_congr_b0 hae0 hgsrc'
  refine ⟨g, gq, gη, hgper, hgwq, hgwη, hgsrc, hmg1, hmgc, ?_, hg_circ⟩
  set M_ν : ℝ := K_proj * C_tr * (p.ν ^ k_tr)⁻¹
  have hMν_pos : 0 ≤ M_ν := by positivity
  have h_pt_1 : ∀ s ∈ Ioc 0 T,
      sliceH1Norm p.c g gq gη s ≤
        ENNReal.ofReal M_ν * sliceD2Sum p.c b0' b0q b0η D2 s := by
    intro s hs
    calc sliceH1Norm p.c g gq gη s
        ≤ ENNReal.ofReal K_proj *
            (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
            sliceD2Sum p.c b0' b0q b0η D2 s := (hslice_bd s hs).1
      _ ≤ ENNReal.ofReal K_proj * ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹) *
            sliceD2Sum p.c b0' b0q b0η D2 s := by
          gcongr; exact hTr_bd p d hreg hν s hs
      _ = ENNReal.ofReal M_ν * sliceD2Sum p.c b0' b0q b0η D2 s := by
          rw [← ENNReal.ofReal_mul hKproj.le]
          dsimp [M_ν]
          rw [mul_assoc]
  have h_pt_c : ∀ s ∈ Ioc 0 T,
      sliceXmNorm p.c m (profCurl gq gη) s ≤
        ENNReal.ofReal M_ν * sliceD2Sum p.c b0' b0q b0η D2 s := by
    intro s hs
    calc sliceXmNorm p.c m (profCurl gq gη) s
        ≤ ENNReal.ofReal K_proj *
            (trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) *
            sliceD2Sum p.c b0' b0q b0η D2 s := (hslice_bd s hs).2
      _ ≤ ENNReal.ofReal K_proj * ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹) *
            sliceD2Sum p.c b0' b0q b0η D2 s := by
          gcongr; exact hTr_bd p d hreg hν s hs
      _ = ENNReal.ofReal M_ν * sliceD2Sum p.c b0' b0q b0η D2 s := by
          rw [← ENNReal.ofReal_mul hKproj.le]
          dsimp [M_ν]
          rw [mul_assoc]
  have h1_sLp : sLpNorm (13 / 8) T (sliceH1Norm p.c g gq gη) ≤
      ENNReal.ofReal M_ν * sLpNorm (13 / 8) T (sliceD2Sum p.c b0' b0q b0η D2) := by
    calc sLpNorm (13 / 8) T (sliceH1Norm p.c g gq gη)
        ≤ sLpNorm (13 / 8) T (fun s => ENNReal.ofReal M_ν * sliceD2Sum p.c b0' b0q b0η D2 s) :=
          sLpNorm_mono_Ioc (13 / 8) T h_pt_1
      _ = ENNReal.ofReal M_ν * sLpNorm (13 / 8) T (sliceD2Sum p.c b0' b0q b0η D2) :=
          sLpNorm_const_mul (13 / 8) T _ ENNReal.ofReal_ne_top _
  have hc_sLp : sLpNorm (13 / 8) T (sliceXmNorm p.c m (profCurl gq gη)) ≤
      ENNReal.ofReal M_ν * sLpNorm (13 / 8) T (sliceD2Sum p.c b0' b0q b0η D2) := by
    calc sLpNorm (13 / 8) T (sliceXmNorm p.c m (profCurl gq gη))
        ≤ sLpNorm (13 / 8) T (fun s => ENNReal.ofReal M_ν * sliceD2Sum p.c b0' b0q b0η D2 s) :=
          sLpNorm_mono_Ioc (13 / 8) T h_pt_c
      _ = ENNReal.ofReal M_ν * sLpNorm (13 / 8) T (sliceD2Sum p.c b0' b0q b0η D2) :=
          sLpNorm_const_mul (13 / 8) T _ ENNReal.ofReal_ne_top _
  have htwo_M : ENNReal.ofReal M_ν + ENNReal.ofReal M_ν =
      ENNReal.ofReal (2 * K_proj * C_tr * (p.ν ^ k_tr)⁻¹) := by
    rw [← ENNReal.ofReal_add hMν_pos hMν_pos]
    congr 1; dsimp [M_ν]; ring
  calc sLpNorm (13 / 8) T (sliceH1Norm p.c g gq gη) +
        sLpNorm (13 / 8) T (sliceXmNorm p.c m (profCurl gq gη))
      ≤ ENNReal.ofReal M_ν * sLpNorm (13 / 8) T (sliceD2Sum p.c b0' b0q b0η D2) +
          ENNReal.ofReal M_ν * sLpNorm (13 / 8) T (sliceD2Sum p.c b0' b0q b0η D2) :=
        add_le_add h1_sLp hc_sLp
    _ = ENNReal.ofReal (2 * K_proj * C_tr * (p.ν ^ k_tr)⁻¹) *
          sLpNorm (13 / 8) T (sliceD2Sum p.c b0' b0q b0η D2) := by
        rw [← add_mul, htwo_M]
    _ ≤ ENNReal.ofReal (2 * K_proj * C_tr * (p.ν ^ k_tr)⁻¹) *
          (sLpNorm (13 / 8) T (sliceLpNorm p.c b0') +
            sLpNorm (13 / 8) T (sliceLpNorm p.c b0q) +
            sLpNorm (13 / 8) T (sliceLpNorm p.c b0η) +
            ∑ i : Fin 2, ∑ j : Fin 2, sLpNorm (13 / 8) T (sliceLpNorm p.c (D2 i j))) := by
        gcongr
        exact sLpNorm_sliceD2Sum_le (13 / 8) T p.c hm0 hmq hmη hmD2

end UnforcedLeray.Short.IIb

end
