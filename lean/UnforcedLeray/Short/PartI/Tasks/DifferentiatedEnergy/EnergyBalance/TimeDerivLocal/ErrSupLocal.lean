import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcSmooth
import UnforcedLeray.Units.B0147

/-!
# Part I, task `PartI:T08/4/1/1/2` (`TrainErrSupLocal`): conditional reduction

Source `the November 2 reference manuscript` lines 261-288, 326-329.

`e(r) = v(r) - V_c(r)`. The velocity part is bounded locally uniformly in `r` by
`vjl_wordBoundedOn` (BUC, applied on `[0, s+1]`). The remaining input is the `V_c` part, which is
a leaf here: smoothness of `V_c(r)` for `r > 0` and a local uniform sup bound on its word
derivatives (for `a(r) > c²` the bounds `Train.Vc_bounds` do not apply).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- `V_c(r)` is smooth for every `r > 0`. -/
def VcSmoothPos : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (Vc ν c r)

/-- Word derivatives of `V_c` are bounded uniformly for `r` near `s > 0` and all `z`. -/
def VcWordSupLocal : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ s : ℝ, 0 < s →
    ∀ (w : List Bool) (k : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      ∀ z : Plane, |wordComp w (Vc ν c r) k z| ≤ M

theorem vcSmoothPos : VcSmoothPos := by
  intro ν c hν hc r hr
  have h := UnforcedLeray.Short.IIb.vcSmooth_proof ν c hν hc
  have h2 : ContDiff ℝ ∞ (fun z : Plane => Vc ν c (r, z).1 (r, z).2) :=
    h.comp_contDiff (f := fun z : Plane => (r, z)) (contDiff_const.prodMk contDiff_id)
      (fun z => ⟨hr, trivial⟩)
  exact h2

open UnforcedLeray.B0147 in
open UnforcedLeray.B0146 (latticeSum periodicVelocity vcomp) in
theorem vcWordSupLocal : VcWordSupLocal := by
  intro ν c hν hc s hs w k
  have hc0 : 0 < c := by linarith
  obtain ⟨g, hg, hw⟩ := (GP_U k).derivWord_lattice w
  obtain ⟨K, β, hK, hβ, hb⟩ := hg.bound
  set a2 : ℝ := 1 + ν * (s + 1) with ha2
  have ha2p : 0 < a2 := by rw [ha2]; positivity
  have hβ' : 0 < β / a2 := by positivity
  refine ⟨1, one_pos, K * (2 + theta (β / a2 / 8)), fun r hr hrs z => ?_⟩
  have hrs' := abs_lt.mp hrs
  have hrw : 1 ≤ B0113.heatWidth ν r := by
    show 1 ≤ 1 + ν * r
    nlinarith
  have hra : B0113.heatWidth ν r ≤ a2 := by
    show 1 + ν * r ≤ 1 + ν * (s + 1)
    nlinarith
  have ha : 0 < B0113.heatWidth ν r := by linarith
  set a := B0113.heatWidth ν r with hadef
  have hl := lam_pos ha
  have hl1 : lam a ≤ 1 := by
    unfold lam
    apply inv_le_one_of_one_le₀
    rw [Real.one_le_sqrt]; exact hrw
  have hlsq := lam_sq ha
  have hLne : lam a * c ≠ 0 := by positivity
  have e : wordComp w (Vc ν c r) k = B0151.derivWord w
      (fun x => vcomp (periodicVelocity ν c r x) k) := by
    unfold wordComp
    exact congrArg (B0151.derivWord w) (Train.Vc_comp_eq ν c r k)
  rw [e, derivWord_velocity hc0.ne' ha k w hw]
  show |lam a ^ 3 * lam a ^ w.length * latticeSum (lam a * c) g (lam a * z.1, lam a * z.2)| ≤ _
  have h1 := latticeSum_abs_le (L := lam a * c) hK hβ hLne hb (lam a * z.1, lam a * z.2)
  have hsum : ∑' n : ℤ, Real.exp (-(β * (lam a * z.1 - n * (lam a * c)) ^ 2)) ≤
      ∑' n : ℤ, Real.exp (-(β / a2 * (z.1 - n * c) ^ 2)) := by
    refine (B0146.summable_exp_shift hβ hLne _).tsum_le_tsum (fun n => ?_)
      (B0146.summable_exp_shift hβ' hc0.ne' z.1)
    apply Real.exp_le_exp.mpr
    have : β * (lam a * z.1 - n * (lam a * c)) ^ 2 = β * a⁻¹ * (z.1 - n * c) ^ 2 := by
      rw [← hlsq]; ring
    rw [this]
    have : β / a2 ≤ β * a⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ ha hra) hβ.le
    have h0 := sq_nonneg (z.1 - n * c)
    nlinarith
  have hsup := lattice1D_sup hβ' hc z.1
  have hy : Real.exp (-(β * (lam a * z.2) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (lam a * z.2)])
  have hS0 : 0 ≤ ∑' n : ℤ, Real.exp (-(β * (lam a * z.1 - n * (lam a * c)) ^ 2)) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  have hθ := theta_nonneg (β / a2 / 8)
  have hlat : |latticeSum (lam a * c) g (lam a * z.1, lam a * z.2)| ≤
      K * (2 + theta (β / a2 / 8)) := by
    refine h1.trans ?_
    calc K * Real.exp (-(β * (lam a * z.2) ^ 2)) *
          ∑' n : ℤ, Real.exp (-(β * (lam a * z.1 - n * (lam a * c)) ^ 2))
        ≤ K * 1 * (2 + theta (β / a2 / 8)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hy hK) (hsum.trans hsup) hS0 (by positivity)
      _ = _ := by ring
  have hp : lam a ^ 3 * lam a ^ w.length ≤ 1 := by
    rw [← pow_add]; exact pow_le_one₀ hl.le hl1
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ lam a ^ 3 * lam a ^ w.length)]
  calc lam a ^ 3 * lam a ^ w.length * |latticeSum (lam a * c) g (lam a * z.1, lam a * z.2)|
      ≤ 1 * (K * (2 + theta (β / a2 / 8))) :=
        mul_le_mul hp hlat (abs_nonneg _) zero_le_one
    _ = _ := by ring

/-- Conditional proof of `TrainErrSupLocal` from the two `V_c` leaves. -/
theorem trainErrSupLocal_of (hS : VcSmoothPos) (hV : VcWordSupLocal) : TrainErrSupLocal := by
  intro ν c hν hc tr htr s hs w k
  have hc0 : 0 < c := by linarith
  obtain ⟨Mv, hMv⟩ := vjl_wordBoundedOn htr (S := s + 1) (by linarith) w k
  obtain ⟨eV, heV, MV, hMV⟩ := hV ν c hν hc s hs w k
  refine ⟨min eV 1, lt_min heV one_pos, Mv + MV, ?_⟩
  intro r hr hrs z
  have hr1 : |r - s| < eV := lt_of_lt_of_le hrs (min_le_left _ _)
  have hr2 : |r - s| < 1 := lt_of_lt_of_le hrs (min_le_right _ _)
  have hrS : r ∈ Icc (0 : ℝ) (s + 1) := by
    rw [abs_lt] at hr2
    exact ⟨hr.le, by linarith [hr2.2]⟩
  have hsm : ContDiff ℝ ∞ (tr.v r) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hr.le
  have hVc : ContDiff ℝ ∞ (Vc ν c r) := hS ν c hν hc0 r hr
  have hcompV : ContDiff ℝ ∞ (fun x => tr.v r x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm
  have hcompW : ContDiff ℝ ∞ (fun x => Vc ν c r x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hVc
  have e : wordComp w (trainErr tr r) k =
      fun x => wordComp w (tr.v r) k x - wordComp w (Vc ν c r) k x := by
    funext x
    have h := derivWord_sub_smooth hcompV hcompW w x
    simpa [wordComp, trainErr] using h
  rw [e]
  have h1 := hMv r hrS z
  have h2 := hMV r hr hr1 z
  calc |wordComp w (tr.v r) k z - wordComp w (Vc ν c r) k z|
      ≤ |wordComp w (tr.v r) k z| + |wordComp w (Vc ν c r) k z| := abs_sub _ _
    _ ≤ Mv + MV := add_le_add h1 h2

/-- `TrainErrSupLocal`. -/
theorem trainErrSupLocal_proof : UnforcedLeray.Short.PartI.TrainErrSupLocal :=
  trainErrSupLocal_of vcSmoothPos vcWordSupLocal

end UnforcedLeray.Short.PartI
