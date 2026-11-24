import UnforcedLeray.Lib.CZL2.NewtonConv
import UnforcedLeray.Lib.CZL2.TestOffSupport
import UnforcedLeray.Lib.Kernels.NewtonDerivatives
import UnforcedLeray.Lib.Kernels.IterApply
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# Far-field derivative bound for the Newton pair potential

Source `the November 2 reference manuscript`
lines 1393-1400: `∂^α ∂_i N(y-x) = O(|y|^{-2-|α|})` for `|y| ≥ 2R`, integrated against a test
supported in `|x| ≤ R` (no cancellation).  Proof: write `newtonPair i f z = ∫ Fam x z dx` with
`Fam x z = -(f x) * ∂_iN(z - x)`, differentiate under the integral on `{R < |z|}`
(`L09.iteratedFDeriv_integral_eq`), and use `|D^n ∂_iN(w)| ≤ C|w|^{-2-n}` (from
`Kernels.norm_iteratedFDeriv_newton_le`) together with `|y - x| ≥ |y|/2`.
-/

set_option autoImplicit false

noncomputable section

/-- Alias used in the statement of the target. -/
abbrev UnforcedLeray.RieszLp.IsSpatialTest (φ : UnforcedLeray.Space → ℝ) : Prop :=
  UnforcedLeray.IsSpatialTest φ

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace NewtonPairFar

open UnforcedLeray.PressureAnalysis UnforcedLeray.RieszLp

theorem norm_e (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

theorem hG_smooth (i : Fin 3) {w : Space} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (newtonGradientKernel i) w := by
  have hN := Kernels.contDiffAt_newton hw
  have h1 : ContDiffAt ℝ ∞ (fderiv ℝ newtonPotential) w :=
    hN.fderiv_right Kernels.infty_add_one_le
  have h2 : ContDiffAt ℝ ∞ (fun y => fderiv ℝ newtonPotential y (coordinateVector i)) w :=
    h1.clm_apply contDiffAt_const
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with y hy
  exact (fderiv_newtonPotential_coordinate hy i).symm

theorem hG_bound (i : Fin 3) (n : ℕ) : ∃ C : ℝ, ∀ w : Space, w ≠ 0 →
    ‖iteratedFDeriv ℝ n (newtonGradientKernel i) w‖ ≤ C * ‖w‖ ^ (-(2 + (n : ℝ))) := by
  obtain ⟨C, hC⟩ := Kernels.norm_iteratedFDeriv_newton_le (n + 1)
  refine ⟨C, fun w hw => ?_⟩
  have hev : newtonGradientKernel i =ᶠ[𝓝 w]
      fun y => iteratedFDeriv ℝ 1 newtonPotential y (fun _ => coordinateVector i) := by
    filter_upwards [isOpen_ne.mem_nhds hw] with y hy
    simp only [iteratedFDeriv_one_apply]
    exact (fderiv_newtonPotential_coordinate hy i).symm
  rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
  have h := Kernels.norm_iteratedFDeriv_apply_le 1 newtonPotential w
    (Kernels.contDiffAt_newton hw) (fun _ => coordinateVector i) n
  simp only [norm_e, Finset.univ_unique, Finset.prod_singleton, mul_one] at h
  refine h.trans ?_
  have := hC w hw
  have hexp : (-(1 + ((n + 1 : ℕ) : ℝ))) = -(2 + (n : ℝ)) := by push_cast; ring
  rw [hexp] at this
  exact this

/-- The integrand family. -/
def Fam (i : Fin 3) (f : Space → ℝ) (x z : Space) : ℝ := -(f x) * newtonGradientKernel i (z - x)

theorem newtonPair_eq (i : Fin 3) (f : Space → ℝ) :
    newtonPair i f = fun z => ∫ x, Fam i f x z := by
  funext z
  unfold newtonPair
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [Fam, show x - z = -(z - x) by abel, newtonGradientKernel_neg]
  ring

theorem Fam_zero (i : Fin 3) {f : Space → ℝ} {x : Space} (h : f x = 0) :
    Fam i f x = fun _ => 0 := by
  funext z; simp [Fam, h]

theorem iter_Fam (i : Fin 3) (f : Space → ℝ) {R : ℝ} {x z : Space} (hx : ‖x‖ ≤ R) (hz : R < ‖z‖)
    (n : ℕ) :
    iteratedFDeriv ℝ n (Fam i f x) z =
      (-(f x)) • iteratedFDeriv ℝ n (newtonGradientKernel i) (z - x) := by
  have hzx : z - x ≠ 0 := by
    intro h
    have : z = x := sub_eq_zero.1 h
    rw [this] at hz; linarith
  have hs : ContDiffAt ℝ ∞ (fun z' => newtonGradientKernel i (z' - x)) z :=
    ContDiffAt.comp z (hG_smooth i hzx) (contDiffAt_id.sub contDiffAt_const)
  have hF : Fam i f x = fun z' => (-(f x)) • newtonGradientKernel i (z' - x) := by
    funext z'; simp [Fam, smul_eq_mul]
  rw [hF, iteratedFDeriv_const_smul_apply' (hs.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_comp_sub]

theorem pointwise_bound (i : Fin 3) (f : Space → ℝ) {R : ℝ} {x z : Space} (hx : ‖x‖ ≤ R)
    (hz : R < ‖z‖) (n : ℕ) {C δ : ℝ} (hC : ∀ w : Space, w ≠ 0 →
      ‖iteratedFDeriv ℝ n (newtonGradientKernel i) w‖ ≤ C * ‖w‖ ^ (-(2 + (n : ℝ))))
    (hδ : 0 < δ) (hd : δ ≤ ‖z - x‖) :
    ‖iteratedFDeriv ℝ n (Fam i f x) z‖ ≤ |f x| * (|C| * δ ^ (-(2 + (n : ℝ)))) := by
  have hzx : z - x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδ hd)
  rw [iter_Fam i f hx hz, norm_smul, norm_neg, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine (hC _ hzx).trans ?_
  have h1 : ‖z - x‖ ^ (-(2 + (n : ℝ))) ≤ δ ^ (-(2 + (n : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos hδ hd (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  calc C * ‖z - x‖ ^ (-(2 + (n : ℝ))) ≤ |C| * ‖z - x‖ ^ (-(2 + (n : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * δ ^ (-(2 + (n : ℝ))) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

end NewtonPairFar

open NewtonPairFar UnforcedLeray.PressureAnalysis UnforcedLeray.RieszLp in
/-- **Far-field derivative bound** for the Newton pair potential. -/
theorem newtonPair_iteratedFDeriv_far (i : Fin 3) (k : ℕ) : ∃ C : ℝ, ∀ (R : ℝ) (f : UnforcedLeray.Space → ℝ), UnforcedLeray.RieszLp.IsSpatialTest f → (∀ x, R < ‖x‖ → f x = 0) → ∀ y : UnforcedLeray.Space, 2 * R ≤ ‖y‖ → y ≠ 0 → ‖iteratedFDeriv ℝ k (UnforcedLeray.RieszLp.newtonPair i f) y‖ ≤ C * (∫ x, |f x|) * ‖y‖ ^ (-(2 + (k : ℝ))) := by
  obtain ⟨C0, hC0⟩ := hG_bound i k
  refine ⟨|C0| * 2 ^ (2 + (k : ℝ)), ?_⟩
  intro R f hf hsupp y hy hy0
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rcases lt_or_ge R 0 with hR | hR
  · have hf0 : f = 0 := funext fun x => hsupp x (lt_of_lt_of_le hR (norm_nonneg x))
    subst hf0
    have : newtonPair i (0 : Space → ℝ) = 0 := by
      funext z; simp [newtonPair]
    rw [this]
    simp
  have hf' : UnforcedLeray.IsSpatialTest f := hf
  have hfc : Continuous f := hf'.smooth.continuous
  have hfi : Integrable f volume := hfc.integrable_of_hasCompactSupport hf'.compact
  set U : Set Space := {z | R < ‖z‖} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hyU : y ∈ U := by
    show R < ‖y‖
    linarith
  have hsmooth : ∀ᵐ x ∂(volume : Measure Space), ContDiffOn ℝ ∞ (Fam i f x) U := by
    refine Eventually.of_forall fun x => ?_
    by_cases hx : R < ‖x‖
    · rw [Fam_zero i (hsupp x hx)]; exact contDiffOn_const
    · push Not at hx
      intro z hz
      have hzx : z - x ≠ 0 := by
        intro h
        have : z = x := sub_eq_zero.1 h
        have hz' : R < ‖z‖ := hz
        rw [this] at hz'; linarith
      have hs : ContDiffAt ℝ ∞ (fun z' => -(f x) * newtonGradientKernel i (z' - x)) z :=
        contDiffAt_const.mul
          (ContDiffAt.comp z (hG_smooth i hzx) (contDiffAt_id.sub contDiffAt_const))
      exact hs.contDiffWithinAt
  have hmeas : ∀ n : ℕ, ∀ z ∈ U,
      AEStronglyMeasurable (fun x => iteratedFDeriv ℝ n (Fam i f x) z) volume := by
    intro n z hz
    have hz' : R < ‖z‖ := hz
    have hS : MeasurableSet (closedBall (0 : Space) R) := measurableSet_closedBall
    have hfun : (fun x => iteratedFDeriv ℝ n (Fam i f x) z) =
        (closedBall (0 : Space) R).indicator
          (fun x => (-(f x)) • iteratedFDeriv ℝ n (newtonGradientKernel i) (z - x)) := by
      funext x
      by_cases hx : R < ‖x‖
      · have hn : x ∉ closedBall (0 : Space) R := by
          rw [mem_closedBall, dist_zero_right, not_le]; exact hx
        rw [indicator_of_notMem hn, Fam_zero i (hsupp x hx)]
        simp
      · have hm : x ∈ closedBall (0 : Space) R := by
          rw [mem_closedBall, dist_zero_right]; exact not_lt.1 hx
        rw [indicator_of_mem hm]
        exact iter_Fam i f (not_lt.1 hx) hz' n
    rw [hfun, aestronglyMeasurable_indicator_iff hS]
    refine ContinuousOn.aestronglyMeasurable ?_ hS
    intro x hx
    have hx' : ‖x‖ ≤ R := by
      rw [mem_closedBall, dist_zero_right] at hx; exact hx
    have hzx : z - x ≠ 0 := by
      intro h
      have : z = x := sub_eq_zero.1 h
      rw [this] at hz'; linarith
    have hcd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ n (newtonGradientKernel i)) (z - x) :=
      (hG_smooth i hzx).iteratedFDeriv_right (m := ∞) (i := n) Kernels.infty_add_nat_le
    have hc : ContinuousAt (fun x => iteratedFDeriv ℝ n (newtonGradientKernel i) (z - x)) x :=
      ContinuousAt.comp (g := iteratedFDeriv ℝ n (newtonGradientKernel i)) (f := fun x => z - x)
        hcd.continuousAt (continuous_const.sub continuous_id).continuousAt
    exact (hfc.neg.continuousAt.smul hc).continuousWithinAt
  have hdom : L09.LocDominated volume (Fam i f) U := by
    intro n x' hx'
    have hx'' : R < ‖x'‖ := hx'
    obtain ⟨Cn, hCn⟩ := hG_bound i n
    set δ : ℝ := (‖x'‖ - R) / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; linarith
    refine ⟨{z | R + δ < ‖z‖}, ?_, fun x => |f x| * (|Cn| * δ ^ (-(2 + (n : ℝ)))), ?_, ?_⟩
    · refine (isOpen_lt continuous_const continuous_norm).mem_nhds ?_
      show R + δ < ‖x'‖
      rw [hδdef]; linarith
    · exact hfi.abs.mul_const _
    · refine Eventually.of_forall fun x z hz => ?_
      have hz' : R + δ < ‖z‖ := hz
      by_cases hx : R < ‖x‖
      · rw [Fam_zero i (hsupp x hx)]
        have h0 := Real.rpow_nonneg hδ.le (-(2 + (n : ℝ)))
        simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
        positivity
      · push Not at hx
        refine pointwise_bound i f hx (by linarith) n hCn hδ ?_
        have := norm_sub_norm_le z x
        linarith
  have heq := L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hdom k hyU
  rw [newtonPair_eq, heq]
  set e : ℝ := -(2 + (k : ℝ)) with he
  have hk0 : (0 : ℝ) ≤ 2 + (k : ℝ) := by positivity
  have hpt : ∀ x, ‖iteratedFDeriv ℝ k (Fam i f x) y‖ ≤
      |f x| * (|C0| * 2 ^ (2 + (k : ℝ)) * ‖y‖ ^ e) := by
    intro x
    by_cases hx : R < ‖x‖
    · rw [Fam_zero i (hsupp x hx)]
      simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      positivity
    · push Not at hx
      have hd : ‖y‖ / 2 ≤ ‖y - x‖ := by
        have := norm_sub_norm_le y x
        linarith
      have hb := pointwise_bound i f hx (show R < ‖y‖ from hyU) k hC0 (by positivity) hd
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h2 := Kernels.rpow_neg_le_of_half_le hyn (le_refl (‖y‖ / 2)) hk0
      calc |C0| * (‖y‖ / 2) ^ e ≤ |C0| * (2 ^ (2 + (k : ℝ)) * ‖y‖ ^ e) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |C0| * 2 ^ (2 + (k : ℝ)) * ‖y‖ ^ e := by ring
  have hint : Integrable (fun x => |f x| * (|C0| * 2 ^ (2 + (k : ℝ)) * ‖y‖ ^ e)) volume :=
    hfi.abs.mul_const _
  calc ‖∫ x, iteratedFDeriv ℝ k (Fam i f x) y‖
      ≤ ∫ x, ‖iteratedFDeriv ℝ k (Fam i f x) y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |f x| * (|C0| * 2 ^ (2 + (k : ℝ)) * ‖y‖ ^ e) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = |C0| * 2 ^ (2 + (k : ℝ)) * (∫ x, |f x|) * ‖y‖ ^ e := by
        rw [integral_mul_const]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
