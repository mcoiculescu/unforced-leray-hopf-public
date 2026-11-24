import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison.RemainderBound.Leaves
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.BEpsFlat
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.TrainDiff
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T20
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8.WeakDq
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# `PartII-b:T20/2`: the pointwise chart algebra of `s(B_ε - B_0)`

Source of record: `the November 2 reference manuscript` (SP), lines 2007-2023:
"Exact chart substitution writes the second as `ε` times polynomially bounded coefficients
multiplying `b, ∂_qb, ∂_ηb, Sb`".

With `b_raw = v + εHe_z` (`rawProf_eq`), `Q_ε = ∂_q - ε(K+1)`, the chart output `kOutChart`
(`= sB_εb`, `TransverseTail/Leaves.lean`) and the flat output `flatK` (`= sB_0b`) evaluated with
`∂_qb = Q_εb + ε(2Sb + η∂_ηb + b)` (`dqOf`) differ by `εs·remW`, where `remW` is linear in
`b, Sb, ∂_ηb` with coefficients from the first-order chart jets of `v` and `He_z`.  The flat
divergence `∂_qv_r + ∂_ηv_z = 0` of the train (`IsTrain.solenoidal`) removes the only `O(1)` term.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

namespace RemBd

/-- The train velocity at a fixed age `s ≥ 0` is smooth in the plane variable. -/
theorem train_slice_contDiff (p : Params) {s : ℝ} (hs : 0 ≤ s) (l : Fin 2) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => p.train.v s z l) := by
  have h1 : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => p.train.v s z) univ := by
    have hg : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ))) univ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact p.train.isTrain.smooth_v.comp hg (fun z _ => ⟨hs, trivial⟩)
  have h2 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => p.train.v s z) := contDiffOn_univ.1 h1
  exact (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff.comp h2

/-- On `s > 0` the plane-slice derivative of a train component is the chart derivative. -/
theorem slice_fderiv_eq {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) {x : Coord}
    (hx : 0 < x.1) (i : Fin 2) (e : ℝ × ℝ) :
    fderiv ℝ (fun z => p.train.v x.1 z i) x.2 e = fderiv ℝ (trainProf p) x (0, e) i := by
  have hT : DifferentiableAt ℝ (trainProf p) x := (trainDiff p d dm dp hbg x hx).1
  rcases x with ⟨s, z⟩
  have hG : HasFDerivAt (fun w : ℝ × ℝ => trainProf p (s, w))
      ((fderiv ℝ (trainProf p) (s, z)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) z :=
    hT.hasFDerivAt.comp z ((hasFDerivAt_const s z).prodMk (hasFDerivAt_id z))
  have hP : HasFDerivAt (fun w : ℝ × ℝ => p.train.v s w i)
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp ((fderiv ℝ (trainProf p) (s, z)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))))) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hG
  rw [hP.fderiv]
  simp

/-- The flat divergence of the train vanishes in chart form: `∂_qv_r + ∂_ηv_z = 0` on `s > 0`. -/
theorem train_div_chart {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) {x : Coord}
    (hx : 0 < x.1) :
    Axi.dQ (trainProf p) x 0 + Axi.dEta (trainProf p) x 1 = 0 := by
  have hsol := p.train.isTrain.solenoidal x.1 hx.le x.2
  unfold UnforcedLeray.Cyl.divergence at hsol
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv
      ((train_slice_contDiff p hx.le 0).differentiable (by simp)),
    UnforcedLeray.Cyl.partialEta_eq_fderiv
      ((train_slice_contDiff p hx.le 1).differentiable (by simp))] at hsol
  rw [slice_fderiv_eq hbg hx 0 (1, 0), slice_fderiv_eq hbg hx 1 (0, 1)] at hsol
  exact hsol

/-- The raised field `He_z` has no radial component. -/
theorem raisedMerid_zero (p : Params) (x : Coord) : raisedMerid p x 0 = 0 := by
  simp [raisedMerid, Axi.m1]

/-- `b_raw = v + εHe_z` and its first-order chart jets, on `s > 0`. -/
theorem raw_ids {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) {x : Coord}
    (hx : 0 < x.1) :
    rawProf p x = trainProf p x + p.ε • raisedMerid p x ∧
    Axi.dQ (rawProf p) x = Axi.dQ (trainProf p) x + p.ε • Axi.dQ (raisedMerid p) x ∧
    Axi.dEta (rawProf p) x = Axi.dEta (trainProf p) x + p.ε • Axi.dEta (raisedMerid p) x ∧
    kAge (rawProf p) x = kAge (trainProf p) x + p.ε • kAge (raisedMerid p) x := by
  obtain ⟨hT, hR⟩ := trainDiff p d dm dp hbg x hx
  rw [rawProf_eq p]
  exact ⟨rfl, beF_dQ_add_smul hT hR, beF_dEta_add_smul hT hR, beF_kAge_add_smul hT hR⟩

/-- The `O(1)` coefficient vector of `s(B_ε - B_0)b / ε` (SP 2015-2018). -/
def remW (p : Params) (b Sb Eb : CProf) (x : Coord) : CMerid :=
  WithLp.toLp 2 fun i =>
    ((raisedMerid p x 1 : ℝ) : ℂ) * Eb x i
      - ((trainProf p x 0 : ℝ) : ℂ) * (2 * Sb x i + ((x.2.2 : ℝ) : ℂ) * Eb x i + b x i)
      + b x 0 * ((Axi.dQ (raisedMerid p) x i - kAge (trainProf p) x i
          - p.ε * kAge (raisedMerid p) x i - trainProf p x i - p.ε * raisedMerid p x i : ℝ) : ℂ)
      + b x 1 * ((Axi.dEta (raisedMerid p) x i : ℝ) : ℂ)
      + ((Axi.dQ (raisedMerid p) x 0 - kAge (trainProf p) x 0 - p.ε * kAge (raisedMerid p) x 0
          + Axi.dEta (raisedMerid p) x 1 : ℝ) : ℂ) * b x i

theorem remW_apply (p : Params) (b Sb Eb : CProf) (x : Coord) (i : Fin 2) :
    remW p b Sb Eb x i =
      ((raisedMerid p x 1 : ℝ) : ℂ) * Eb x i
        - ((trainProf p x 0 : ℝ) : ℂ) * (2 * Sb x i + ((x.2.2 : ℝ) : ℂ) * Eb x i + b x i)
        + b x 0 * ((Axi.dQ (raisedMerid p) x i - kAge (trainProf p) x i
            - p.ε * kAge (raisedMerid p) x i - trainProf p x i - p.ε * raisedMerid p x i : ℝ) : ℂ)
        + b x 1 * ((Axi.dEta (raisedMerid p) x i : ℝ) : ℂ)
        + ((Axi.dQ (raisedMerid p) x 0 - kAge (trainProf p) x 0 - p.ε * kAge (raisedMerid p) x 0
            + Axi.dEta (raisedMerid p) x 1 : ℝ) : ℂ) * b x i := rfl

/-- **Exact chart substitution** (SP 2007-2018): on `s > 0`,
`kOutChart b Qb Eb - flatK b (∂_qb) (∂_ηb) = εs·remW` with `∂_qb = dqOf`. -/
theorem diff_apply {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) {x : Coord}
    (hx : 0 < x.1) (b Sb Qb Eb : CProf) (i : Fin 2) :
    (kOutChart p b Qb Eb x - flatK p.train b (dqOf p.ε b Sb Qb Eb) Eb x) i =
      ((p.ε * x.1 : ℝ) : ℂ) * remW p b Sb Eb x i := by
  obtain ⟨h1, h2, h3, h4⟩ := raw_ids hbg hx
  have hdiv := train_div_chart hbg hx
  have hR0 := raisedMerid_zero p x
  have e1 : ∀ j, rawProf p x j = trainProf p x j + p.ε * raisedMerid p x j := by
    intro j; rw [h1]; simp
  have e3 : ∀ j, qEps p.ε (rawProf p) x j = Axi.dQ (trainProf p) x j
      + p.ε * Axi.dQ (raisedMerid p) x j - p.ε * (kAge (trainProf p) x j
        + p.ε * kAge (raisedMerid p) x j + (trainProf p x j + p.ε * raisedMerid p x j)) := by
    intro j; unfold qEps; rw [h2, h4, h1]; simp; ring
  have e4 : ∀ j, Axi.dEta (rawProf p) x j =
      Axi.dEta (trainProf p) x j + p.ε * Axi.dEta (raisedMerid p) x j := by
    intro j; rw [h3]; simp
  have e5 : chartDivR p.ε (rawProf p) x = p.ε * (Axi.dQ (raisedMerid p) x 0
      - kAge (trainProf p) x 0 - p.ε * kAge (raisedMerid p) x 0
        + Axi.dEta (raisedMerid p) x 1) := by
    unfold chartDivR; rw [e3 0, e1 0, e4 1, hR0]; linear_combination hdiv
  have hs0 := slice_fderiv_eq hbg hx i (1, 0)
  have hs1 := slice_fderiv_eq hbg hx i (0, 1)
  have hv : ∀ j, p.train.v x.1 x.2 j = trainProf p x j := fun j => rfl
  have hR0C : ((raisedMerid p x 0 : ℝ) : ℂ) = 0 := by rw [hR0]; simp
  simp only [kOutChart, flatK, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    cplx, dqOf_apply]
  rw [remW_apply, e1 0, e1 1, e3 i, e4 i, e5, hs0, hs1, hv 0, hv 1]
  change _ = _ * (_ + _ * ((Axi.dQ (raisedMerid p) x i - _ - _ - _ - _ : ℝ) : ℂ) + _ + _)
  push_cast
  simp only [Axi.dQ, Axi.dEta] at *
  linear_combination ((x.1 : ℂ) * (p.ε : ℂ) * Qb x i) * hR0C

/-- `‖w‖ ≤ ‖w₀‖ + ‖w₁‖` on `ℂ²`. -/
theorem cmerid_norm_le (w : CMerid) : ‖w‖ ≤ ‖w 0‖ + ‖w 1‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 := norm_nonneg (w 0)
  have h1 := norm_nonneg (w 1)
  calc Real.sqrt (‖w 0‖ ^ 2 + ‖w 1‖ ^ 2) ≤ Real.sqrt ((‖w 0‖ + ‖w 1‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = ‖w 0‖ + ‖w 1‖ := Real.sqrt_sq (by positivity)

/-- The scalar estimate of one component of `remW`. -/
theorem scalar_bound (a c r1 r2 r3 η J B S E : ℝ) (e s bb b0 b1 : ℂ) (hJ : 0 ≤ J)
    (ha : |a| ≤ J) (hc : |c| ≤ J) (hr1 : |r1| ≤ 5 * J) (hr2 : |r2| ≤ J) (hr3 : |r3| ≤ 4 * J)
    (he : ‖e‖ ≤ E) (hs : ‖s‖ ≤ S) (hb : ‖bb‖ ≤ B) (hb0 : ‖b0‖ ≤ B) (hb1 : ‖b1‖ ≤ B) :
    ‖(a : ℂ) * e - (c : ℂ) * (2 * s + (η : ℂ) * e + bb) + b0 * (r1 : ℂ) + b1 * (r2 : ℂ)
        + (r3 : ℂ) * bb‖ ≤ 11 * J * (1 + |η|) * (B + S + E) := by
  have hE : 0 ≤ E := (norm_nonneg e).trans he
  have hS : 0 ≤ S := (norm_nonneg s).trans hs
  have hB : 0 ≤ B := (norm_nonneg bb).trans hb
  have t1 : ‖(a : ℂ) * e‖ ≤ J * E := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul ha he (norm_nonneg _) hJ
  have hinner : ‖2 * s + (η : ℂ) * e + bb‖ ≤ 2 * S + |η| * E + B := by
    have h2 : ‖(2 : ℂ) * s‖ ≤ 2 * S := by
      rw [norm_mul]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]
      linarith
    have h3 : ‖(η : ℂ) * e‖ ≤ |η| * E := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
    calc ‖2 * s + (η : ℂ) * e + bb‖ ≤ ‖2 * s + (η : ℂ) * e‖ + ‖bb‖ := norm_add_le _ _
      _ ≤ ‖(2 : ℂ) * s‖ + ‖(η : ℂ) * e‖ + ‖bb‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 2 * S + |η| * E + B := by linarith
  have t2 : ‖(c : ℂ) * (2 * s + (η : ℂ) * e + bb)‖ ≤ J * (2 * S + |η| * E + B) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hc hinner (norm_nonneg _) hJ
  have t3 : ‖b0 * (r1 : ℂ)‖ ≤ B * (5 * J) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hb0 hr1 (abs_nonneg _) hB
  have t4 : ‖b1 * (r2 : ℂ)‖ ≤ B * J := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hb1 hr2 (abs_nonneg _) hB
  have t5 : ‖(r3 : ℂ) * bb‖ ≤ (4 * J) * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hr3 hb (norm_nonneg _) (by linarith)
  have htri : ‖(a : ℂ) * e - (c : ℂ) * (2 * s + (η : ℂ) * e + bb) + b0 * (r1 : ℂ)
        + b1 * (r2 : ℂ) + (r3 : ℂ) * bb‖ ≤ ‖(a : ℂ) * e‖ + ‖(c : ℂ) * (2 * s + (η : ℂ) * e + bb)‖
          + ‖b0 * (r1 : ℂ)‖ + ‖b1 * (r2 : ℂ)‖ + ‖(r3 : ℂ) * bb‖ := by
    have n1 := norm_sub_le ((a : ℂ) * e) ((c : ℂ) * (2 * s + (η : ℂ) * e + bb))
    have n2 := norm_add_le ((a : ℂ) * e - (c : ℂ) * (2 * s + (η : ℂ) * e + bb)) (b0 * (r1 : ℂ))
    have n3 := norm_add_le (((a : ℂ) * e - (c : ℂ) * (2 * s + (η : ℂ) * e + bb))
      + b0 * (r1 : ℂ)) (b1 * (r2 : ℂ))
    have n4 := norm_add_le ((((a : ℂ) * e - (c : ℂ) * (2 * s + (η : ℂ) * e + bb))
      + b0 * (r1 : ℂ)) + b1 * (r2 : ℂ)) ((r3 : ℂ) * bb)
    linarith
  have hη := abs_nonneg η
  calc _ ≤ _ := htri
    _ ≤ J * E + J * (2 * S + |η| * E + B) + B * (5 * J) + B * J + (4 * J) * B := by
        linarith [t1, t2, t3, t4, t5]
    _ ≤ 11 * J * (1 + |η|) * (B + S + E) := by
        nlinarith [mul_nonneg hJ hE, mul_nonneg hJ hS, mul_nonneg hJ hB,
          mul_nonneg (mul_nonneg hJ hE) hη, mul_nonneg (mul_nonneg hJ hS) hη,
          mul_nonneg (mul_nonneg hJ hB) hη]

theorem abs_apply_le (v : Axi.Merid) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _

/-- `‖remW‖ ≤ 22 J (1 + |η|)(‖b‖ + ‖Sb‖ + ‖∂_ηb‖)`, `J` the two chart jets. -/
theorem remW_norm_le (p : Params) (b Sb Eb : CProf) (x : Coord) (hε0 : 0 ≤ p.ε)
    (hε1 : p.ε ≤ 1) :
    ‖remW p b Sb Eb x‖ ≤ 22 * (chartJet (trainProf p) x + chartJet (raisedMerid p) x) *
      (1 + |x.2.2|) * (‖b x‖ + ‖Sb x‖ + ‖Eb x‖) := by
  set J := chartJet (trainProf p) x + chartJet (raisedMerid p) x with hJdef
  have jT := beF_chartJet_nonneg (trainProf p) x
  have jR := beF_chartJet_nonneg (raisedMerid p) x
  have hJ0 : 0 ≤ J := add_nonneg jT jR
  have lT : chartJet (trainProf p) x ≤ J := le_add_of_nonneg_right jR
  have lR : chartJet (raisedMerid p) x ≤ J := le_add_of_nonneg_left jT
  have nT : ∀ i, |trainProf p x i| ≤ J := fun i =>
    (abs_apply_le _ i).trans ((beF_cj_norm _ x).trans lT)
  have nR : ∀ i, |raisedMerid p x i| ≤ J := fun i =>
    (abs_apply_le _ i).trans ((beF_cj_norm _ x).trans lR)
  have nQR : ∀ i, |Axi.dQ (raisedMerid p) x i| ≤ J := fun i =>
    (abs_apply_le _ i).trans ((beF_cj_dQ _ x).trans lR)
  have nER : ∀ i, |Axi.dEta (raisedMerid p) x i| ≤ J := fun i =>
    (abs_apply_le _ i).trans ((beF_cj_dEta _ x).trans lR)
  have nKT : ∀ i, |kAge (trainProf p) x i| ≤ J := fun i =>
    (abs_apply_le _ i).trans ((beF_cj_kAge _ x).trans lT)
  have nKR : ∀ i, |kAge (raisedMerid p) x i| ≤ J := fun i =>
    (abs_apply_le _ i).trans ((beF_cj_kAge _ x).trans lR)
  have eps_le : ∀ y : ℝ, |y| ≤ J → |p.ε * y| ≤ J := fun y hy => by
    rw [abs_mul, abs_of_nonneg hε0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hε1).trans hy
  have comp : ∀ i, ‖remW p b Sb Eb x i‖ ≤ 11 * J * (1 + |x.2.2|) * (‖b x‖ + ‖Sb x‖ + ‖Eb x‖) := by
    intro i
    rw [remW_apply]
    have r1 : |Axi.dQ (raisedMerid p) x i - kAge (trainProf p) x i
        - p.ε * kAge (raisedMerid p) x i - trainProf p x i - p.ε * raisedMerid p x i| ≤ 5 * J := by
      have a1 := abs_le.mp (nQR i)
      have a2 := abs_le.mp (nKT i)
      have a3 := abs_le.mp (eps_le _ (nKR i))
      have a4 := abs_le.mp (nT i)
      have a5 := abs_le.mp (eps_le _ (nR i))
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have r3 : |Axi.dQ (raisedMerid p) x 0 - kAge (trainProf p) x 0
        - p.ε * kAge (raisedMerid p) x 0 + Axi.dEta (raisedMerid p) x 1| ≤ 4 * J := by
      have a1 := abs_le.mp (nQR 0)
      have a2 := abs_le.mp (nKT 0)
      have a3 := abs_le.mp (eps_le _ (nKR 0))
      have a4 := abs_le.mp (nER 1)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact scalar_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ0 (nR 1) (nT 0) r1 (nER i) r3
      (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
      (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
  calc ‖remW p b Sb Eb x‖ ≤ ‖remW p b Sb Eb x 0‖ + ‖remW p b Sb Eb x 1‖ := cmerid_norm_le _
    _ ≤ _ := by linarith [comp 0, comp 1]

/-- **The pointwise `O(ε)` remainder** (SP 2007-2018): on `s > 0`,
`‖kOutChart b Qb Eb - flatK b (∂_qb) (∂_ηb)‖ ≤ 22εsJ(1+|η|)(‖b‖ + ‖Sb‖ + ‖∂_ηb‖)`. -/
theorem diff_norm_le {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) {x : Coord}
    (hx : 0 < x.1) (b Sb Qb Eb : CProf) :
    ‖kOutChart p b Qb Eb x - flatK p.train b (dqOf p.ε b Sb Qb Eb) Eb x‖ ≤
      22 * p.ε * x.1 * (chartJet (trainProf p) x + chartJet (raisedMerid p) x) *
        (1 + |x.2.2|) * (‖b x‖ + ‖Sb x‖ + ‖Eb x‖) := by
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hε1 : p.ε ≤ 1 := bgRegime_eps_le_one hbg
  have heq : kOutChart p b Qb Eb x - flatK p.train b (dqOf p.ε b Sb Qb Eb) Eb x =
      ((p.ε * x.1 : ℝ) : ℂ) • remW p b Sb Eb x := by
    ext i
    rw [diff_apply hbg hx b Sb Qb Eb i]
    simp
  rw [heq, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := remW_norm_le p b Sb Eb x hε0 hε1
  calc p.ε * x.1 * ‖remW p b Sb Eb x‖
      ≤ p.ε * x.1 * (22 * (chartJet (trainProf p) x + chartJet (raisedMerid p) x) *
        (1 + |x.2.2|) * (‖b x‖ + ‖Sb x‖ + ‖Eb x‖)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

end RemBd

end UnforcedLeray.Short.IIb

end
