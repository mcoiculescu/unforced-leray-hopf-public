import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3

/-!
# Cutoff facts for `kf3GradOrth` (source 117-120)

The reference bump `chiB` is `1` on the unit ball and `0` off the ball of radius `2`.  The
cutoff at scale `N` is `cut N x = chiB (N⁻¹ • x)`.  For a smooth `p` on `ℝ³ × ℝ`, the spatial
gradient of `cut N x · p(x,τ)` differs from that of `p` by the Riesz vector of
`(cut N x - 1) · (∇ₓp) + p · ∇ₓ(cut N)`, an exact identity (`gradX_mul_cut_sub`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.GradOrthAux

open UnforcedLeray.B0226

/-- The reference bump: `1` on `closedBall 0 1`, `0` off `closedBall 0 2`. -/
def chiB : ContDiffBump (0 : Space) :=
  { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := by norm_num }

theorem chiB_nonneg (z : Space) : 0 ≤ chiB z := chiB.nonneg

theorem chiB_le_one (z : Space) : chiB z ≤ 1 := chiB.le_one

theorem chiB_eq_one {z : Space} (hz : ‖z‖ ≤ 1) : chiB z = 1 :=
  chiB.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hz)

theorem chiB_eq_zero {z : Space} (hz : 2 ≤ ‖z‖) : chiB z = 0 :=
  chiB.zero_of_le_dist (by rw [dist_zero_right]; exact hz)

theorem chiB_contDiff : ContDiff ℝ ∞ chiB := chiB.contDiff

theorem chiB_cs : HasCompactSupport chiB := chiB.hasCompactSupport

theorem chiB_tsupport : tsupport chiB = Metric.closedBall 0 2 := chiB.tsupport_eq

theorem chiB_fderiv_bound : ∃ K : ℝ, ∀ z : Space, ‖fderiv ℝ chiB z‖ ≤ K := by
  obtain ⟨K, hK⟩ := (chiB_contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (chiB_cs.fderiv (𝕜 := ℝ))
  exact ⟨K, hK⟩

theorem chiB_fderiv_eq_zero_of_lt {z : Space} (hz : ‖z‖ < 1) : fderiv ℝ chiB z = 0 := by
  have hev : chiB =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) hz)
      (fun w hw => chiB_eq_one (le_of_lt hw))
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev]
  simp

theorem chiB_fderiv_eq_zero_of_gt {z : Space} (hz : 2 < ‖z‖) : fderiv ℝ chiB z = 0 := by
  apply fderiv_of_notMem_tsupport ℝ
  rw [chiB_tsupport, mem_closedBall_zero_iff]
  intro h
  linarith

/-- The cutoff at scale `N`. -/
def cut (N : ℝ) (x : Space) : ℝ := chiB (N⁻¹ • x)

theorem cut_contDiff (N : ℝ) : ContDiff ℝ ∞ (cut N) :=
  chiB_contDiff.comp (contDiff_id.const_smul N⁻¹)

theorem cut_nonneg (N : ℝ) (x : Space) : 0 ≤ cut N x := chiB_nonneg _

theorem cut_le_one (N : ℝ) (x : Space) : cut N x ≤ 1 := chiB_le_one _

theorem cut_eq_one {N : ℝ} {x : Space} (hN : 0 < N) (hx : ‖x‖ ≤ N) : cut N x = 1 := by
  apply chiB_eq_one
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hN.le)]
  calc N⁻¹ * ‖x‖ ≤ N⁻¹ * N := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hN.le)
    _ = 1 := inv_mul_cancel₀ hN.ne'

theorem cut_eq_zero {N : ℝ} {x : Space} (hN : 0 < N) (hx : 2 * N ≤ ‖x‖) : cut N x = 0 := by
  apply chiB_eq_zero
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hN.le)]
  calc (2 : ℝ) = N⁻¹ * (2 * N) := by field_simp
    _ ≤ N⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hN.le)

theorem cut_fderiv_zero_of_lt {N : ℝ} {x : Space} (hN : 0 < N) (hx : ‖x‖ < N) :
    fderiv ℝ (cut N) x = 0 := by
  have h1 : ‖N⁻¹ • x‖ < 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hN.le)]
    calc N⁻¹ * ‖x‖ < N⁻¹ * N := mul_lt_mul_of_pos_left hx (inv_pos.2 hN)
      _ = 1 := inv_mul_cancel₀ hN.ne'
  have hd : DifferentiableAt ℝ (fun x : Space => N⁻¹ • x) x := by fun_prop
  show fderiv ℝ (chiB ∘ fun x : Space => N⁻¹ • x) x = 0
  rw [fderiv_comp x ((chiB_contDiff.differentiable (by simp)) _) hd,
    chiB_fderiv_eq_zero_of_lt h1, ContinuousLinearMap.zero_comp]

theorem cut_fderiv_zero_of_gt {N : ℝ} {x : Space} (hN : 0 < N) (hx : 2 * N < ‖x‖) :
    fderiv ℝ (cut N) x = 0 := by
  have h1 : 2 < ‖N⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hN.le)]
    calc (2 : ℝ) = N⁻¹ * (2 * N) := by field_simp
      _ < N⁻¹ * ‖x‖ := mul_lt_mul_of_pos_left hx (inv_pos.2 hN)
  have hd : DifferentiableAt ℝ (fun x : Space => N⁻¹ • x) x := by fun_prop
  show fderiv ℝ (chiB ∘ fun x : Space => N⁻¹ • x) x = 0
  rw [fderiv_comp x ((chiB_contDiff.differentiable (by simp)) _) hd,
    chiB_fderiv_eq_zero_of_gt h1, ContinuousLinearMap.zero_comp]

theorem cut_fderiv_bound {K : ℝ} (hK : ∀ z : Space, ‖fderiv ℝ chiB z‖ ≤ K) {N : ℝ} (hN : 0 < N)
    (x : Space) : ‖fderiv ℝ (cut N) x‖ ≤ K * N⁻¹ := by
  have hd : DifferentiableAt ℝ (fun x : Space => N⁻¹ • x) x := by fun_prop
  have hfd : fderiv ℝ (fun x : Space => N⁻¹ • x) x = N⁻¹ • ContinuousLinearMap.id ℝ Space :=
    ((hasFDerivAt_id x).const_smul N⁻¹).fderiv
  have heq : fderiv ℝ (cut N) x =
      (fderiv ℝ chiB (N⁻¹ • x)).comp (N⁻¹ • ContinuousLinearMap.id ℝ Space) := by
    show fderiv ℝ (chiB ∘ fun x : Space => N⁻¹ • x) x = _
    rw [fderiv_comp x ((chiB_contDiff.differentiable (by simp)) _) hd, hfd]
  have hB : ‖N⁻¹ • ContinuousLinearMap.id ℝ Space‖ ≤ N⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hN.le)]
    exact mul_le_of_le_one_right (inv_nonneg.2 hN.le) ContinuousLinearMap.norm_id_le
  rw [heq]
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  calc ‖(fderiv ℝ chiB (N⁻¹ • x)).comp (N⁻¹ • ContinuousLinearMap.id ℝ Space)‖
      ≤ ‖fderiv ℝ chiB (N⁻¹ • x)‖ * ‖N⁻¹ • ContinuousLinearMap.id ℝ Space‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * N⁻¹ := mul_le_mul (hK _) hB (norm_nonneg _) hK0

/-- The Riesz vector of the cutoff product: `(fderiv (cut·p) y)` restricted to the spatial
directions. -/
theorem fderiv_mul_cut_inl (p : Space × ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (N : ℝ)
    (y : Space × ℝ) :
    (fderiv ℝ (fun z : Space × ℝ => cut N z.1 * p z) y).comp (ContinuousLinearMap.inl ℝ Space ℝ) =
      cut N y.1 • (fderiv ℝ p y).comp (ContinuousLinearMap.inl ℝ Space ℝ) +
        p y • fderiv ℝ (cut N) y.1 := by
  have hcut : HasFDerivAt (fun z : Space × ℝ => cut N z.1)
      ((fderiv ℝ (cut N) y.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)) y :=
    ((cut_contDiff N).differentiable (by simp) y.1).hasFDerivAt.comp y hasFDerivAt_fst
  have hpd : HasFDerivAt p (fderiv ℝ p y) y := ((hp.differentiable (by simp)) y).hasFDerivAt
  have hprod : HasFDerivAt (fun z : Space × ℝ => cut N z.1 * p z)
      (cut N y.1 • fderiv ℝ p y + p y • (fderiv ℝ (cut N) y.1).comp
        (ContinuousLinearMap.fst ℝ Space ℝ)) y := hcut.mul hpd
  rw [hprod.fderiv]
  ext w
  simp

/-- The exact identity `∇ₓ(cut·p) - ∇ₓp = (cut - 1)∇ₓp + p∇ₓcut`, in Riesz form. -/
theorem gradX_mul_cut_sub (p : Space × ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (N : ℝ) (y : Space × ℝ) :
    gradX (fun z : Space × ℝ => cut N z.1 * p z) y - gradX p y =
      (InnerProductSpace.toDual ℝ Space).symm
        ((cut N y.1 - 1) • (fderiv ℝ p y).comp (ContinuousLinearMap.inl ℝ Space ℝ) +
          p y • fderiv ℝ (cut N) y.1) := by
  unfold gradX
  rw [← map_sub, fderiv_mul_cut_inl p hp N y]
  congr 1
  rw [sub_smul, one_smul]
  abel

/-- The pointwise gradient bound `|∇ₓ(cut·p) - ∇ₓp| ≤ |∇ₓp| + |p| |∇ₓcut|`. -/
theorem norm_gradX_mul_cut_sub_le (p : Space × ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (N : ℝ)
    (y : Space × ℝ) :
    ‖gradX (fun z : Space × ℝ => cut N z.1 * p z) y - gradX p y‖ ≤
      ‖gradX p y‖ + |p y| * ‖fderiv ℝ (cut N) y.1‖ := by
  rw [gradX_mul_cut_sub p hp N y, LinearIsometryEquiv.norm_map]
  have hc : |cut N y.1 - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [cut_nonneg N y.1, cut_le_one N y.1]
  have hL : ‖(fderiv ℝ p y).comp (ContinuousLinearMap.inl ℝ Space ℝ)‖ = ‖gradX p y‖ := by
    unfold gradX
    rw [LinearIsometryEquiv.norm_map]
  calc ‖(cut N y.1 - 1) • (fderiv ℝ p y).comp (ContinuousLinearMap.inl ℝ Space ℝ) +
          p y • fderiv ℝ (cut N) y.1‖
      ≤ ‖(cut N y.1 - 1) • (fderiv ℝ p y).comp (ContinuousLinearMap.inl ℝ Space ℝ)‖ +
          ‖p y • fderiv ℝ (cut N) y.1‖ := norm_add_le _ _
    _ = |cut N y.1 - 1| * ‖(fderiv ℝ p y).comp (ContinuousLinearMap.inl ℝ Space ℝ)‖ +
          |p y| * ‖fderiv ℝ (cut N) y.1‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖(fderiv ℝ p y).comp (ContinuousLinearMap.inl ℝ Space ℝ)‖ +
          |p y| * ‖fderiv ℝ (cut N) y.1‖ := by
        gcongr
    _ = ‖gradX p y‖ + |p y| * ‖fderiv ℝ (cut N) y.1‖ := by rw [one_mul, hL]

/-- The decay weight `((1 + |x|)^4)⁻¹` is integrable against one physical period. -/
theorem integrable_decay4 (ε c : ℝ) :
    Integrable (fun y : Space × ℝ => ((1 + ‖y.1‖) ^ 4)⁻¹)
      (UnforcedLeray.B0220.physMeasure ε c) := by
  have hm : UnforcedLeray.B0220.physMeasure ε c =
      ((volume : Measure Space).restrict univ).prod
        ((volume : Measure ℝ).restrict (Ioc 0 (2 * ε * c))) := by
    rw [UnforcedLeray.B0220.physMeasure, UnforcedLeray.B0220.physDomain, Measure.prod_restrict,
      ← Measure.volume_eq_prod]
  have hI1 : Integrable (fun x : Space => ((1 + ‖x‖) ^ 4)⁻¹)
      ((volume : Measure Space).restrict univ) := by
    rw [Measure.restrict_univ]
    refine (integrable_one_add_norm (E := Space) (μ := volume) (r := 4) (by
      simp [finrank_euclideanSpace]; norm_num)).congr (ae_of_all _ fun x => ?_)
    have h4 : (1 + ‖x‖) ^ (-(4:ℝ)) = ((1 + ‖x‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      congr 1
      exact_mod_cast Real.rpow_natCast (1 + ‖x‖) 4
    exact h4
  have hI2 : Integrable (fun _ : ℝ => (1 : ℝ))
      ((volume : Measure ℝ).restrict (Ioc 0 (2 * ε * c))) := by
    have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc 0 (2 * ε * c))) :=
      ⟨by rw [Measure.restrict_apply_univ]; simp⟩
    exact integrable_const 1
  have hprod := MeasureTheory.Integrable.mul_prod hI1 hI2
  rw [hm]
  refine hprod.congr (ae_of_all _ fun y => ?_)
  simp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.GradOrthAux
