import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_8
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.VecDiffJet

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace VecDiffJet1Help

open VecDiffJetHelp

theorem contDiff_dir {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (v : Coord) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ F y v) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem iter_dir_le {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (v : Coord) (hv : ‖v‖ ≤ 1)
    (l : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ l (fun y => fderiv ℝ F y v) x‖ ≤ ‖iteratedFDeriv ℝ (l + 1) F x‖ := by
  let L : (Coord →L[ℝ] Axi.Merid) →L[ℝ] Axi.Merid := ContinuousLinearMap.apply ℝ Axi.Merid v
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
    simp only [L, ContinuousLinearMap.apply_apply, one_mul]
    exact (T.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)
  have hc : ContDiffAt ℝ ∞ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := ∞) (by simp)).contDiffAt
  have h := L.norm_iteratedFDeriv_comp_left (n := l) hc (by exact_mod_cast le_top)
  have e : (fun y => fderiv ℝ F y v) = L ∘ fderiv ℝ F := rfl
  rw [e]
  refine h.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_of_le_one_left (norm_nonneg _) hL

theorem n1 (G : Coord → Axi.Merid) (x : Coord) :
    ‖fderiv ℝ G x‖ = ‖iteratedFDeriv ℝ 1 G x‖ := (norm_iteratedFDeriv_one G).symm

theorem n2 (G : Coord → Axi.Merid) (x : Coord) :
    ‖fderiv ℝ (fderiv ℝ G) x‖ = ‖iteratedFDeriv ℝ 2 G x‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem contDiff_kAge {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun y => kAge F y) := by
  have : (fun y => kAge F y) = fun y => (2 * y.1) • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
      y.2.2 • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := rfl
  rw [this]
  exact ((contDiff_const.mul contDiff_fst).smul (contDiff_dir hF _)).add
    ((contDiff_snd.comp contDiff_snd).smul (contDiff_dir hF _))

/-- operator norm form of the first derivative of `kAge` -/
theorem kAge_fderiv_clm {G : Coord → Axi.Merid} (hG : ContDiff ℝ ∞ G) (x : Coord) :
    ‖fderiv ℝ (fun y => kAge G y) x‖ ≤
      3 * ‖fderiv ℝ G x‖ + (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ (fderiv ℝ G) x‖ := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm ?_ fun w hw => ?_
  · have := norm_nonneg (fderiv ℝ G x)
    have := norm_nonneg (fderiv ℝ (fderiv ℝ G) x)
    positivity
  · exact kAge_fderiv_bound hG x w hw.le

/-- second derivative of one term of `kAge`. -/
theorem iter2_term {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (ℓ : Coord →L[ℝ] ℝ)
    (v : Coord) (hv : ‖v‖ ≤ 1) (x : Coord) :
    ‖iteratedFDeriv ℝ 2 (fun y => ℓ y • fderiv ℝ F y v) x‖ ≤
      2 * ‖ℓ‖ * ‖iteratedFDeriv ℝ 2 F x‖ + |ℓ x| * ‖iteratedFDeriv ℝ 3 F x‖ := by
  have hℓ : ContDiff ℝ ∞ (fun y => ℓ y) := ℓ.contDiff
  have h := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hℓ (contDiff_dir hF v) x
    (n := 2) (N := ∞) (by simp)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose, Nat.reduceSub] at h
  have e0 : ‖iteratedFDeriv ℝ 0 (fun y => ℓ y) x‖ = |ℓ x| := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have e1 : ‖iteratedFDeriv ℝ 1 (fun y => ℓ y) x‖ ≤ ‖ℓ‖ := by
    rw [norm_iteratedFDeriv_one, ℓ.fderiv]
  have e2 : ‖iteratedFDeriv ℝ 2 (fun y => ℓ y) x‖ = 0 := by
    have : fderiv ℝ (fun y => ℓ y) = fun _ => ℓ := by
      funext y; exact ℓ.fderiv
    have h2 : ‖iteratedFDeriv ℝ 2 (fun y => ℓ y) x‖ =
        ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fun y => ℓ y)) x‖ := by
      rw [norm_iteratedFDeriv_fderiv]
    rw [h2, this, norm_iteratedFDeriv_one]
    simp
  have d1 := iter_dir_le hF v hv 1 x
  have d2 := iter_dir_le hF v hv 2 x
  have d0 := iter_dir_le hF v hv 0 x
  rw [e2] at h
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  norm_num at h
  have hn := norm_nonneg (iteratedFDeriv ℝ 1 (fun y => fderiv ℝ F y v) x)
  have hn' := norm_nonneg (iteratedFDeriv ℝ 2 (fun y => fderiv ℝ F y v) x)
  have hn3 := norm_nonneg (iteratedFDeriv ℝ 3 F x)
  have hn2 := norm_nonneg (iteratedFDeriv ℝ 2 F x)
  have hℓn := norm_nonneg ℓ
  have a1 := mul_le_mul e1 d1 hn hℓn
  have a2 := mul_le_mul_of_nonneg_left d2 (abs_nonneg (ℓ x))
  norm_num at d1 d2
  nlinarith [a1, a2]

/-- second derivative of `kAge F + F`. -/
theorem iter2_G {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x : Coord) :
    ‖iteratedFDeriv ℝ 2 (fun y => kAge F y + F y) x‖ ≤
      7 * ‖iteratedFDeriv ℝ 2 F x‖ + (2 * |x.1| + |x.2.2|) * ‖iteratedFDeriv ℝ 3 F x‖ := by
  let ℓ1 : Coord →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let ℓ2 : Coord →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have n1' : ‖ℓ1‖ ≤ 2 := by
    refine (norm_smul_le (2 : ℝ) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))).trans ?_
    have := ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)
    norm_num
  have n2' : ‖ℓ2‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
    have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
    nlinarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ ℝ),
      norm_nonneg (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]
  have hk : (fun y => kAge F y) = fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
      ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    funext y
    simp [kAge, Axi.dS, Axi.dEta, ℓ1, ℓ2]
  have hA : ContDiff ℝ ∞ (fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) :=
    (ℓ1.contDiff).smul (contDiff_dir hF _)
  have hB : ContDiff ℝ ∞ (fun y => ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) :=
    (ℓ2.contDiff).smul (contDiff_dir hF _)
  have hAB := hA.add hB
  have hc : (fun y => kAge F y + F y) =
      fun y => (ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
        ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) + F y := by
    funext y; simp [kAge, Axi.dS, Axi.dEta, ℓ1, ℓ2]
  rw [hc]
  have t1 : iteratedFDeriv ℝ 2 (fun y => (ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
        ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) + F y) x =
      iteratedFDeriv ℝ 2 (fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
        ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) x + iteratedFDeriv ℝ 2 F x :=
    iteratedFDeriv_add_apply (i := 2) (hAB.contDiffAt.of_le (by simp)) (hF.contDiffAt.of_le (by simp))
  have t2 : iteratedFDeriv ℝ 2 (fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
        ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) x =
      iteratedFDeriv ℝ 2 (fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) x + iteratedFDeriv ℝ 2 (fun y => ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) x :=
    iteratedFDeriv_add_apply (i := 2) (hA.contDiffAt.of_le (by simp)) (hB.contDiffAt.of_le (by simp))
  have a := iter2_term hF ℓ1 ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) (by simp) x
  have b := iter2_term hF ℓ2 ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) (by simp) x
  have hl1 : |ℓ1 x| = 2 * |x.1| := by
    simp [ℓ1, abs_mul]
  have hl2 : |ℓ2 x| = |x.2.2| := by simp [ℓ2]
  rw [hl1] at a
  rw [hl2] at b
  have e1 := norm_add_le (iteratedFDeriv ℝ 2 (fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) x)
    (iteratedFDeriv ℝ 2 (fun y => ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) x)
  have e2 := norm_add_le (iteratedFDeriv ℝ 2 (fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
        ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) x) (iteratedFDeriv ℝ 2 F x)
  have h2 := norm_nonneg (iteratedFDeriv ℝ 2 F x)
  have h3 := norm_nonneg (iteratedFDeriv ℝ 3 F x)
  rw [t1]
  have hX : ‖iteratedFDeriv ℝ 2 (fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
        ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) x‖ ≤
      ‖iteratedFDeriv ℝ 2 (fun y => ℓ1 y • fderiv ℝ F y ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) x‖ +
      ‖iteratedFDeriv ℝ 2 (fun y => ℓ2 y • fderiv ℝ F y ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) x‖ := by
    rw [t2]; exact norm_add_le _ _
  have m1 := mul_le_mul_of_nonneg_right n1' h2
  have m2 := mul_le_mul_of_nonneg_right n2' h2
  nlinarith [a, b, hX, e2, m1, m2]


theorem dd {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (v w : Coord) (hv : ‖v‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) (x : Coord) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ F z v) y w) x‖ ≤
      ‖iteratedFDeriv ℝ 3 F x‖ := by
  rw [n1]
  exact (iter_dir_le (contDiff_dir hF v) w hw 1 x).trans (iter_dir_le hF v hv 2 x)

theorem d1 {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (v : Coord) (hv : ‖v‖ ≤ 1) (x : Coord) :
    ‖fderiv ℝ (fun z => fderiv ℝ F z v) x‖ ≤ ‖iteratedFDeriv ℝ 2 F x‖ := by
  rw [n1]; exact iter_dir_le hF v hv 1 x

theorem d2 {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (v : Coord) (hv : ‖v‖ ≤ 1) (x : Coord) :
    ‖fderiv ℝ (fderiv ℝ (fun z => fderiv ℝ F z v)) x‖ ≤ ‖iteratedFDeriv ℝ 3 F x‖ := by
  rw [n2]; exact iter_dir_le hF v hv 2 x

def Lh : Axi.Merid →L[ℝ] Axi.Merid :=
  (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).smulRight Axi.m0

theorem Lh_apply (v : Axi.Merid) : Lh v = hoopR v := by simp [Lh, hoopR]

theorem Lh_le (v : Axi.Merid) : ‖Lh v‖ ≤ ‖v‖ := by
  rw [Lh_apply]
  have hm0 : ‖Axi.m0‖ = 1 := by simp [Axi.m0]
  have hv0 : |v 0| ≤ ‖v‖ := by
    have := PiLp.norm_apply_le v 0
    rwa [Real.norm_eq_abs] at this
  unfold hoopR
  rw [norm_smul, hm0, Real.norm_eq_abs, mul_one]
  exact hv0

theorem hoop_fderiv {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (x : Coord) :
    ‖fderiv ℝ (fun y => hoopR (F y)) x‖ ≤ ‖fderiv ℝ F x‖ := by
  have hFd : DifferentiableAt ℝ F x := (hF.differentiable (by simp)) x
  have h : HasFDerivAt (fun y => Lh (F y)) (Lh.comp (fderiv ℝ F x)) x :=
    Lh.hasFDerivAt.comp x hFd.hasFDerivAt
  have e : (fun y => hoopR (F y)) = fun y => Lh (F y) := by
    funext y; rw [Lh_apply]
  rw [e, h.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  simp only [ContinuousLinearMap.comp_apply]
  exact (Lh_le _).trans ((fderiv ℝ F x).le_opNorm w)

theorem contDiff_vecDiffEps (ε : ℝ) {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (vecDiffEps ε F) := by
  have cQ : ContDiff ℝ ∞ (Axi.dQ F) := contDiff_dir hF _
  have cE : ContDiff ℝ ∞ (Axi.dEta F) := contDiff_dir hF _
  have cQQ : ContDiff ℝ ∞ (Axi.dQ (Axi.dQ F)) := contDiff_dir cQ _
  have cEE : ContDiff ℝ ∞ (Axi.dEta (Axi.dEta F)) := contDiff_dir cE _
  have kQ : ContDiff ℝ ∞ (fun y => kAge (Axi.dQ F) y) := contDiff_kAge cQ
  have kF : ContDiff ℝ ∞ (fun y => kAge F y) := contDiff_kAge hF
  have kG : ContDiff ℝ ∞ (fun y => kAge (fun z => kAge F z + F z) y) :=
    contDiff_kAge (kF.add hF)
  have hh : ContDiff ℝ ∞ (fun y => hoopR (F y)) := by
    have : (fun y => hoopR (F y)) = fun y => Lh (F y) := by
      funext y; rw [Lh_apply]
    rw [this]; exact Lh.contDiff.comp hF
  have : vecDiffEps ε F = fun y => Axi.dQ (Axi.dQ F) y + Axi.dEta (Axi.dEta F) y -
      (2 * ε) • (kAge (Axi.dQ F) y + Axi.dQ F y) +
      ε ^ 2 • (kAge (fun z => kAge F z + F z) y + (kAge F y + F y) - hoopR (F y)) := rfl
  rw [this]
  exact ((cQQ.add cEE).sub ((kQ.add cQ).const_smul _)).add
    (((kG.add (kF.add hF)).sub hh).const_smul _)

set_option maxHeartbeats 1600000 in
theorem fderiv_body {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (x : Coord) :
    ‖fderiv ℝ (vecDiffEps ε F) x‖ ≤
      2 * ‖iteratedFDeriv ℝ 3 F x‖ +
      2 * (4 * ‖iteratedFDeriv ℝ 2 F x‖ + (2 * |x.1| + |x.2.2|) * ‖iteratedFDeriv ℝ 3 F x‖) +
      (17 * ‖iteratedFDeriv ℝ 1 F x‖ + 11 * ((2 * |x.1| + |x.2.2|) * ‖iteratedFDeriv ℝ 2 F x‖)
        + (2 * |x.1| + |x.2.2|) ^ 2 * ‖iteratedFDeriv ℝ 3 F x‖) := by
  set Q := 2 * |x.1| + |x.2.2| with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have cQ : ContDiff ℝ ∞ (Axi.dQ F) := contDiff_dir hF _
  have cE : ContDiff ℝ ∞ (Axi.dEta F) := contDiff_dir hF _
  have cQQ : ContDiff ℝ ∞ (Axi.dQ (Axi.dQ F)) := contDiff_dir cQ _
  have cEE : ContDiff ℝ ∞ (Axi.dEta (Axi.dEta F)) := contDiff_dir cE _
  have kQ : ContDiff ℝ ∞ (fun y => kAge (Axi.dQ F) y) := contDiff_kAge cQ
  have kF : ContDiff ℝ ∞ (fun y => kAge F y) := contDiff_kAge hF
  have cG : ContDiff ℝ ∞ (fun z => kAge F z + F z) := kF.add hF
  have kG : ContDiff ℝ ∞ (fun y => kAge (fun z => kAge F z + F z) y) := contDiff_kAge cG
  have hh : ContDiff ℝ ∞ (fun y => hoopR (F y)) := by
    have : (fun y => hoopR (F y)) = fun y => Lh (F y) := by
      funext y; rw [Lh_apply]
    rw [this]; exact Lh.contDiff.comp hF
  have dif : ∀ {G : Coord → Axi.Merid}, ContDiff ℝ ∞ G → DifferentiableAt ℝ G x :=
    fun hG => (hG.differentiable (by simp)) x
  have H1 := (dif cQQ).hasFDerivAt
  have H2 := (dif cEE).hasFDerivAt
  have H3 := ((dif kQ).add (dif cQ)).hasFDerivAt
  have H4 := (((dif kG).add ((dif kF).add (dif hF))).sub (dif hh)).hasFDerivAt
  have hH : HasFDerivAt (vecDiffEps ε F)
      (fderiv ℝ (Axi.dQ (Axi.dQ F)) x + fderiv ℝ (Axi.dEta (Axi.dEta F)) x -
        (2 * ε) • (fderiv ℝ (fun y => kAge (Axi.dQ F) y) x + fderiv ℝ (Axi.dQ F) x) +
        ε ^ 2 • (fderiv ℝ (fun y => kAge (fun z => kAge F z + F z) y) x +
          (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x) -
          fderiv ℝ (fun y => hoopR (F y)) x)) x := by
    have a := ((H1.add H2).sub (((dif kQ).hasFDerivAt.add (dif cQ).hasFDerivAt).const_smul (2 * ε))).add
      ((((dif kG).hasFDerivAt.add (((dif kF).hasFDerivAt).add (dif hF).hasFDerivAt)).sub
        (dif hh).hasFDerivAt).const_smul (ε ^ 2))
    exact a
  rw [hH.fderiv]
  have b1 : ‖fderiv ℝ (Axi.dQ (Axi.dQ F)) x‖ ≤ ‖iteratedFDeriv ℝ 3 F x‖ :=
    dd hF _ _ eQ_le eQ_le x
  have b2 : ‖fderiv ℝ (Axi.dEta (Axi.dEta F)) x‖ ≤ ‖iteratedFDeriv ℝ 3 F x‖ :=
    dd hF _ _ eE_le eE_le x
  have m1 : ‖fderiv ℝ (Axi.dQ F) x‖ ≤ ‖iteratedFDeriv ℝ 2 F x‖ := d1 hF _ eQ_le x
  have m2 : ‖fderiv ℝ (fderiv ℝ (Axi.dQ F)) x‖ ≤ ‖iteratedFDeriv ℝ 3 F x‖ := d2 hF _ eQ_le x
  have k3 := kAge_fderiv_clm cQ x
  have k1 := kAge_fderiv_clm hF x
  rw [n1 F, n2 F] at k1
  have kG1 := kAge_fderiv_clm cG x
  have DG : ‖fderiv ℝ (fun z => kAge F z + F z) x‖ ≤
      4 * ‖iteratedFDeriv ℝ 1 F x‖ + Q * ‖iteratedFDeriv ℝ 2 F x‖ := by
    have hh1 : HasFDerivAt (fun z => kAge F z + F z)
        (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x) x :=
      (dif kF).hasFDerivAt.add (dif hF).hasFDerivAt
    rw [hh1.fderiv]
    have := norm_add_le (fderiv ℝ (fun y => kAge F y) x) (fderiv ℝ F x)
    rw [n1 F] at this
    linarith
  have D2G : ‖fderiv ℝ (fderiv ℝ (fun z => kAge F z + F z)) x‖ ≤
      7 * ‖iteratedFDeriv ℝ 2 F x‖ + Q * ‖iteratedFDeriv ℝ 3 F x‖ := by
    rw [n2]; exact iter2_G hF x
  have KG : ‖fderiv ℝ (fun y => kAge (fun z => kAge F z + F z) y) x‖ ≤
      12 * ‖iteratedFDeriv ℝ 1 F x‖ + 10 * (Q * ‖iteratedFDeriv ℝ 2 F x‖) +
        Q ^ 2 * ‖iteratedFDeriv ℝ 3 F x‖ := by
    nlinarith [mul_le_mul_of_nonneg_left D2G hQ0]
  have hf := hoop_fderiv hF x
  rw [n1 F] at hf
  have s1 := norm_add_le (fderiv ℝ (Axi.dQ (Axi.dQ F)) x + fderiv ℝ (Axi.dEta (Axi.dEta F)) x -
        (2 * ε) • (fderiv ℝ (fun y => kAge (Axi.dQ F) y) x + fderiv ℝ (Axi.dQ F) x))
    (ε ^ 2 • (fderiv ℝ (fun y => kAge (fun z => kAge F z + F z) y) x +
          (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x) -
          fderiv ℝ (fun y => hoopR (F y)) x))
  have s2 := norm_sub_le (fderiv ℝ (Axi.dQ (Axi.dQ F)) x + fderiv ℝ (Axi.dEta (Axi.dEta F)) x)
    ((2 * ε) • (fderiv ℝ (fun y => kAge (Axi.dQ F) y) x + fderiv ℝ (Axi.dQ F) x))
  have s3 := norm_add_le (fderiv ℝ (Axi.dQ (Axi.dQ F)) x) (fderiv ℝ (Axi.dEta (Axi.dEta F)) x)
  have T3 : ‖(2 * ε) • (fderiv ℝ (fun y => kAge (Axi.dQ F) y) x + fderiv ℝ (Axi.dQ F) x)‖ ≤
      2 * (4 * ‖iteratedFDeriv ℝ 2 F x‖ + Q * ‖iteratedFDeriv ℝ 3 F x‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hZ := norm_add_le (fderiv ℝ (fun y => kAge (Axi.dQ F) y) x) (fderiv ℝ (Axi.dQ F) x)
    have hZ' : ‖fderiv ℝ (fun y => kAge (Axi.dQ F) y) x + fderiv ℝ (Axi.dQ F) x‖ ≤
        4 * ‖iteratedFDeriv ℝ 2 F x‖ + Q * ‖iteratedFDeriv ℝ 3 F x‖ := by
      nlinarith [mul_le_mul_of_nonneg_left m2 hQ0]
    have hZ0 := norm_nonneg (fderiv ℝ (fun y => kAge (Axi.dQ F) y) x + fderiv ℝ (Axi.dQ F) x)
    have h2 : 0 ≤ 4 * ‖iteratedFDeriv ℝ 2 F x‖ + Q * ‖iteratedFDeriv ℝ 3 F x‖ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hZ' (by linarith : (0:ℝ) ≤ 2 * ε),
      mul_le_mul_of_nonneg_right hε1 h2]
  have T4 : ‖ε ^ 2 • (fderiv ℝ (fun y => kAge (fun z => kAge F z + F z) y) x +
          (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x) -
          fderiv ℝ (fun y => hoopR (F y)) x)‖ ≤
      17 * ‖iteratedFDeriv ℝ 1 F x‖ + 11 * (Q * ‖iteratedFDeriv ℝ 2 F x‖) +
        Q ^ 2 * ‖iteratedFDeriv ℝ 3 F x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have w1 := norm_sub_le (fderiv ℝ (fun y => kAge (fun z => kAge F z + F z) y) x +
          (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x)) (fderiv ℝ (fun y => hoopR (F y)) x)
    have w2 := norm_add_le (fderiv ℝ (fun y => kAge (fun z => kAge F z + F z) y) x)
      (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x)
    have w3 := norm_add_le (fderiv ℝ (fun y => kAge F y) x) (fderiv ℝ F x)
    rw [n1 F] at w3
    have hW : ‖fderiv ℝ (fun y => kAge (fun z => kAge F z + F z) y) x +
          (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x) -
          fderiv ℝ (fun y => hoopR (F y)) x‖ ≤
        17 * ‖iteratedFDeriv ℝ 1 F x‖ + 11 * (Q * ‖iteratedFDeriv ℝ 2 F x‖) +
          Q ^ 2 * ‖iteratedFDeriv ℝ 3 F x‖ := by
      linarith
    have hW0 := norm_nonneg (fderiv ℝ (fun y => kAge (fun z => kAge F z + F z) y) x +
          (fderiv ℝ (fun y => kAge F y) x + fderiv ℝ F x) -
          fderiv ℝ (fun y => hoopR (F y)) x)
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hε2 hW0]
  linarith [s1, s2, s3, b1, b2, T3, T4]

theorem final_ineq1 (a b N0 N1 N2 N3 V : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 ≤ N0)
    (h1 : 0 ≤ N1) (h2 : 0 ≤ N2) (h3 : 0 ≤ N3)
    (hV : V ≤ 20 * (1 + a + b) ^ 2 * (N0 + N1 + N2)) (D : ℝ)
    (hD : D ≤ 2 * N3 + 2 * (4 * N2 + (2 * a + b) * N3) +
      (17 * N1 + 11 * ((2 * a + b) * N2) + (2 * a + b) ^ 2 * N3)) :
    V + D ≤ 60 * (1 + a + b) ^ 2 * (N0 + N1 + N2 + N3) := by
  have hQ0 : 0 ≤ 2 * a + b := by linarith
  have hQL : 2 * a + b ≤ 2 * (1 + a + b) := by linarith
  have hΛ2 : 1 ≤ (1 + a + b) ^ 2 := by nlinarith
  have hΛL : (1 + a + b) ≤ (1 + a + b) ^ 2 := by nlinarith
  have hQ2 : (2 * a + b) ^ 2 ≤ 4 * (1 + a + b) ^ 2 := by nlinarith
  have q1 : 2 * a + b ≤ 2 * (1 + a + b) ^ 2 := by linarith
  have e1 := mul_le_mul_of_nonneg_right q1 h2
  have e2 := mul_le_mul_of_nonneg_right q1 h3
  have e3 := mul_le_mul_of_nonneg_right hQ2 h3
  have e4 := mul_le_mul_of_nonneg_right hΛ2 h1
  have e5 := mul_le_mul_of_nonneg_right hΛ2 h2
  have e6 := mul_le_mul_of_nonneg_right hΛ2 h3
  have e7 := mul_le_mul_of_nonneg_right hΛ2 h0
  nlinarith [e1, e2, e3, e4, e5, e6, e7]

end VecDiffJet1Help

open VecDiffJet1Help VecDiffJetHelp in
theorem vecDiffJet1 : UnforcedLeray.Short.IIb.VecDiffJet1 := by
  refine ⟨60, by norm_num, ?_⟩
  intro ε hε0 hε1 F hF x
  have hc := contDiff_vecDiffEps ε hF
  refine ⟨(hc.differentiable (by simp)) x, ?_⟩
  have hv := vecDiffJet_body hF ε hε0 hε1 x
  have hd := fderiv_body hF ε hε0 hε1 x
  have h0 : ‖iteratedFDeriv ℝ 0 F x‖ = ‖F x‖ := norm_iteratedFDeriv_zero
  have h1 : ‖iteratedFDeriv ℝ 1 F x‖ = ‖fderiv ℝ F x‖ := norm_iteratedFDeriv_one F
  have h2 : ‖iteratedFDeriv ℝ 2 F x‖ = ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0]
  rw [h1] at hd ⊢
  rw [h2] at hd ⊢
  have := final_ineq1 |x.1| |x.2.2| ‖F x‖ ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖
    ‖iteratedFDeriv ℝ 3 F x‖ _ (abs_nonneg _) (abs_nonneg _) (norm_nonneg _) (by positivity)
    (by positivity) (norm_nonneg _) hv _ hd
  exact this

end UnforcedLeray.Short.IIb

end
