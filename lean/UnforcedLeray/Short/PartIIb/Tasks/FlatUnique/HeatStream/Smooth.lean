import UnforcedLeray.Short.PartIIb.Sub.T11_3
import UnforcedLeray.Lib.Kernels.ParamIntegral
import UnforcedLeray.Lib.HeatCylinder.SmoothBounds

/-!
# Part II-b, leaf `PartII-b:T11/3/2` (`HeatConvSmooth`): the planar heat flow is smooth for `τ > 0`

Source of record: `the November 2 reference manuscript`, the heat semigroup
`e^{ν(s-t)Δ}` of the causal formula at line 1924.

Proof. With `θ = ντ`, substitute `w = √(2θ) v` in the planar Gaussian. The kernel `heatKernel2 θ`
becomes the fixed Gaussian `heatKernel2 (1/2)`, so `H(τ, z) = Φ(√(2ντ), z)` with
`Φ(σ, z) = ∫ G(v) ζ(z - σ v) dv`. The map `(σ, z) ↦ z - σ v` is linear in `(σ, z)`, so every
derivative of the integrand is `G(v)` times a bounded derivative of `ζ` times a polynomial in `v`.
Then `Lib/Kernels/ParamIntegral.lean` (`contDiffOn_integral`) gives smoothness of `Φ` on all of
`ℝ × (ℝ × ℝ)`, and `τ ↦ √(2ντ)` is smooth on `τ > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ### Global bounds on the derivatives of a nice stream -/

theorem hcs_nice_iteratedFDeriv_bound {c : ℝ} (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ n ζ z‖ ≤ M := by
  obtain ⟨L, hL⟩ := hζ.compact
  have hper : ∀ p : ℝ × ℝ, ζ (p + (c, 0)) = ζ p := fun p => by
    rw [show p + (c, 0) = (p.1 + c, p.2) from Prod.ext rfl (add_zero _)]
    exact hζ.periodic p
  have hfun : (fun w : ℝ × ℝ => ζ (w + (c, 0))) = ζ := funext hper
  have hu : UnforcedLeray.Sob.IsCylSmooth c (iteratedFDeriv ℝ n ζ) := by
    refine ⟨hζ.smooth.iteratedFDeriv_right (m := ∞) (by simp), fun z => ?_, ⟨L, fun z hz => ?_⟩⟩
    · have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := ζ) n (c, 0) z
      rw [hfun] at h
      exact h.symm
    · have hopen : IsOpen {w : ℝ × ℝ | L < |w.2|} :=
        isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
      have hev : ζ =ᶠ[𝓝 z] fun _ : ℝ × ℝ => (0 : ℝ) := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        exact hL w (le_of_lt hw)
      have h0 : iteratedFDeriv ℝ n (fun _ : ℝ × ℝ => (0 : ℝ)) = 0 := iteratedFDeriv_fun_zero
      calc iteratedFDeriv ℝ n ζ z = iteratedFDeriv ℝ n (fun _ : ℝ × ℝ => (0 : ℝ)) z :=
            (hev.iteratedFDeriv ℝ n).eq_of_nhds
        _ = 0 := by simp [h0]
  obtain ⟨M, hM0, hM⟩ := UnforcedLeray.HeatCylinder.exists_global_bound_of_cylSmooth hc hu
  exact ⟨M, hM0, hM⟩

/-! ### The linear shift `(σ, z) ↦ z - σ • v` -/

/-- The map `(σ, z) ↦ z - σ • v` on `ℝ × (ℝ × ℝ)`. -/
def hcs_shiftCLM (v : ℝ × ℝ) : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ) -
    ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) v

theorem hcs_shiftCLM_apply (v : ℝ × ℝ) (y : ℝ × (ℝ × ℝ)) : hcs_shiftCLM v y = y.2 - y.1 • v := by
  simp [hcs_shiftCLM]

theorem hcs_norm_shiftCLM_le (v : ℝ × ℝ) : ‖hcs_shiftCLM v‖ ≤ 1 + ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [hcs_shiftCLM_apply]
  have h2 : ‖y.1‖ ≤ ‖y‖ := norm_fst_le y
  have h4 : 0 ≤ ‖v‖ := norm_nonneg v
  have h3 : ‖y.2 - y.1 • v‖ ≤ ‖y.2‖ + ‖y.1‖ * ‖v‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul]
  have h1 : ‖y.2‖ ≤ ‖y‖ := norm_snd_le y
  nlinarith [mul_le_mul_of_nonneg_right h2 h4]

/-! ### Integrability of polynomial times Gaussian -/

theorem hcs_one_add_abs_pow_mul_gauss_le (n : ℕ) (x : ℝ) :
    (1 + |x|) ^ n * Real.exp (-(1 / 2) * x ^ 2) ≤
      Real.exp ((n : ℝ) ^ 2) * Real.exp (-(1 / 4) * x ^ 2) := by
  have h1 : (1 + |x|) ^ n ≤ Real.exp ((n : ℝ) * |x|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp |x|]) n
  have h2 : Real.exp ((n : ℝ) * |x|) * Real.exp (-(1 / 2) * x ^ 2) ≤
      Real.exp ((n : ℝ) ^ 2) * Real.exp (-(1 / 4) * x ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (|x| - 2 * (n : ℝ)), sq_abs x]
  calc (1 + |x|) ^ n * Real.exp (-(1 / 2) * x ^ 2)
      ≤ Real.exp ((n : ℝ) * |x|) * Real.exp (-(1 / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ _ := h2

theorem hcs_integrable_one_add_abs_pow_mul_gauss (n : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n * Real.exp (-(1 / 2) * x ^ 2)) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).const_mul
      (Real.exp ((n : ℝ) ^ 2))) ?_ (Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ n *
      Real.exp (-(1 / 2) * x ^ 2)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact hcs_one_add_abs_pow_mul_gauss_le n x

theorem hcs_heatKernel_half_eq (x : ℝ) :
    UnforcedLeray.B0191.heatKernel 1 (1 / 2) x =
      (Real.sqrt (4 * Real.pi * 1 * (1 / 2)))⁻¹ * Real.exp (-(1 / 2) * x ^ 2) := by
  unfold UnforcedLeray.B0191.heatKernel
  congr 2
  ring

theorem hcs_integrable_one_add_abs_pow_heatKernel_half (n : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n * UnforcedLeray.B0191.heatKernel 1 (1 / 2) x) := by
  refine ((hcs_integrable_one_add_abs_pow_mul_gauss n).const_mul
    (Real.sqrt (4 * Real.pi * 1 * (1 / 2)))⁻¹).congr (Eventually.of_forall fun x => ?_)
  simp only [hcs_heatKernel_half_eq]
  ring

theorem hcs_integrable_heatKernel2_half_pow (n : ℕ) (M : ℝ) :
    Integrable (fun v : ℝ × ℝ => M * ((1 + |v.1|) ^ n * UnforcedLeray.B0191.heatKernel 1 (1 / 2) v.1 *
      ((1 + |v.2|) ^ n * UnforcedLeray.B0191.heatKernel 1 (1 / 2) v.2))) := by
  have h := (hcs_integrable_one_add_abs_pow_heatKernel_half n).mul_prod
    (hcs_integrable_one_add_abs_pow_heatKernel_half n)
  rw [← MeasureTheory.Measure.volume_eq_prod] at h
  exact h.const_mul M

/-! ### Change of variables `w = √(2θ) v` in the planar heat kernel -/

theorem hcs_heatKernel_scale_pointwise {θ : ℝ} (hθ : 0 < θ) {s : ℝ} (hs : s ^ 2 = 2 * θ) (x y : ℝ) :
    2 * θ * (UnforcedLeray.B0191.heatKernel 1 θ (s * x) *
        UnforcedLeray.B0191.heatKernel 1 θ (s * y)) =
      UnforcedLeray.B0191.heatKernel 1 (1 / 2) x * UnforcedLeray.B0191.heatKernel 1 (1 / 2) y := by
  have hθ' : θ ≠ 0 := hθ.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsq : ∀ a : ℝ, 0 ≤ a → (Real.sqrt a)⁻¹ * (Real.sqrt a)⁻¹ = a⁻¹ := fun a ha => by
    rw [← mul_inv, Real.mul_self_sqrt ha]
  have hA : 2 * θ * ((Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) =
      (Real.sqrt (4 * Real.pi * 1 * (1 / 2)))⁻¹ * (Real.sqrt (4 * Real.pi * 1 * (1 / 2)))⁻¹ := by
    rw [hsq (4 * Real.pi * 1 * θ) (by positivity), hsq (4 * Real.pi * 1 * (1 / 2)) (by positivity)]
    field_simp
  have ex : -(s * x) ^ 2 / (4 * 1 * θ) = -x ^ 2 / (4 * 1 * (1 / 2)) := by
    rw [mul_pow, hs]
    field_simp
  have ey : -(s * y) ^ 2 / (4 * 1 * θ) = -y ^ 2 / (4 * 1 * (1 / 2)) := by
    rw [mul_pow, hs]
    field_simp
  unfold UnforcedLeray.B0191.heatKernel
  rw [ex, ey]
  linear_combination (Real.exp (-x ^ 2 / (4 * 1 * (1 / 2))) *
    Real.exp (-y ^ 2 / (4 * 1 * (1 / 2)))) * hA

theorem hcs_heatKernel2_scale {θ : ℝ} (hθ : 0 < θ) (f : ℝ × ℝ → ℝ) :
    ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f w =
      ∫ v : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (1 / 2) v * f (Real.sqrt (2 * θ) • v) := by
  have hs2 : Real.sqrt (2 * θ) ^ 2 = 2 * θ := Real.sq_sqrt (by linarith)
  have hcov := MeasureTheory.Measure.integral_comp_smul (volume : Measure (ℝ × ℝ))
    (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w * f w) (Real.sqrt (2 * θ))
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hfin, hs2, abs_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < 2 * θ)), smul_eq_mul] at hcov
  have hpt : ∀ v : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (1 / 2) v =
      2 * θ * UnforcedLeray.B0284.heatKernel2 θ (Real.sqrt (2 * θ) • v) := by
    intro v
    have := hcs_heatKernel_scale_pointwise hθ hs2 v.1 v.2
    simp only [UnforcedLeray.B0284.heatKernel2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact this.symm
  have hR : ∫ v : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (1 / 2) v * f (Real.sqrt (2 * θ) • v) =
      2 * θ * ∫ v : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ (Real.sqrt (2 * θ) • v) *
        f (Real.sqrt (2 * θ) • v) := by
    rw [← integral_const_mul]
    congr 1
    funext v
    rw [hpt v]
    ring
  rw [hR, hcov, ← mul_assoc, mul_inv_cancel₀ (by linarith : (2 : ℝ) * θ ≠ 0), one_mul]

/-! ### The integrand `hcs_Fk` and its derivative bounds -/

/-- The integrand of `Φ`: `hcs_Fk ζ v (σ, z) = G(v) ζ(z - σ v)` with `G = heatKernel2 (1/2)`. -/
def hcs_Fk (ζ : ℝ × ℝ → ℝ) (v : ℝ × ℝ) (y : ℝ × (ℝ × ℝ)) : ℝ :=
  UnforcedLeray.B0284.heatKernel2 (1 / 2) v * ζ (hcs_shiftCLM v y)

theorem hcs_norm_iteratedFDeriv_Fk_le {ζ : ℝ × ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ) {n : ℕ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ n ζ z‖ ≤ M) (v : ℝ × ℝ)
    (y : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ n (hcs_Fk ζ v) y‖ ≤
      UnforcedLeray.B0284.heatKernel2 (1 / 2) v * (M * (1 + ‖v‖) ^ n) := by
  have hK0 : 0 ≤ UnforcedLeray.B0284.heatKernel2 (1 / 2) v :=
    UnforcedLeray.B0284.heatKernel2_nonneg (by norm_num) v
  have hζc : ContDiffAt ℝ n (ζ ∘ hcs_shiftCLM v) y :=
    ((hζ.comp (hcs_shiftCLM v).contDiff).contDiffAt).of_le (by exact_mod_cast le_top)
  have hfun : hcs_Fk ζ v = fun y => UnforcedLeray.B0284.heatKernel2 (1 / 2) v • (ζ ∘ hcs_shiftCLM v) y :=
    funext fun y => by simp [hcs_Fk]
  rw [hfun, iteratedFDeriv_const_smul_apply' hζc, norm_smul, Real.norm_of_nonneg hK0]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (hcs_shiftCLM v) hζ y
    (by exact_mod_cast le_top)]
  calc ‖(iteratedFDeriv ℝ n ζ (hcs_shiftCLM v y)).compContinuousLinearMap (fun _ => hcs_shiftCLM v)‖
      ≤ ‖iteratedFDeriv ℝ n ζ (hcs_shiftCLM v y)‖ * ∏ _i : Fin n, ‖hcs_shiftCLM v‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ M * (1 + ‖v‖) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul (hM _) (pow_le_pow_left₀ (norm_nonneg _) (hcs_norm_shiftCLM_le v) n)
          (by positivity) hM0

theorem hcs_Fk_bound_le (n : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (v : ℝ × ℝ) :
    UnforcedLeray.B0284.heatKernel2 (1 / 2) v * (M * (1 + ‖v‖) ^ n) ≤
      M * ((1 + |v.1|) ^ n * UnforcedLeray.B0191.heatKernel 1 (1 / 2) v.1 *
        ((1 + |v.2|) ^ n * UnforcedLeray.B0191.heatKernel 1 (1 / 2) v.2)) := by
  have hK0 : 0 ≤ UnforcedLeray.B0284.heatKernel2 (1 / 2) v :=
    UnforcedLeray.B0284.heatKernel2_nonneg (by norm_num) v
  have hnorm : (1 + ‖v‖) ^ n ≤ (1 + |v.1|) ^ n * (1 + |v.2|) ^ n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have a0 := abs_nonneg v.1
    have b0 := abs_nonneg v.2
    rcases le_total |v.1| |v.2| with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg a0 b0]
    · rw [max_eq_left h]
      nlinarith [mul_nonneg a0 b0]
  have hfac : UnforcedLeray.B0284.heatKernel2 (1 / 2) v * (M * (1 + ‖v‖) ^ n) ≤
      UnforcedLeray.B0284.heatKernel2 (1 / 2) v * (M * ((1 + |v.1|) ^ n * (1 + |v.2|) ^ n)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm hM0) hK0
  refine hfac.trans (le_of_eq ?_)
  unfold UnforcedLeray.B0284.heatKernel2
  ring

/-! ### Smoothness of the integrand in the parameters -/

theorem hcs_contDiff_Hj {ζ : ℝ × ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => hcs_Fk ζ p.1 p.2) := by
  have hK : ContDiff ℝ ∞ (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 (1 / 2) w) := by
    unfold UnforcedLeray.B0284.heatKernel2
    exact (((UnforcedLeray.B0191.contDiff_heatKernel 1 (1 / 2)).comp contDiff_fst).mul
      ((UnforcedLeray.B0191.contDiff_heatKernel 1 (1 / 2)).comp contDiff_snd)).of_le le_top
  have hA : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => p.2.2 - p.2.1 • p.1) := by
    fun_prop
  have hEq : (fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => hcs_Fk ζ p.1 p.2) =
      fun p => (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 (1 / 2) w) p.1 *
        ζ (p.2.2 - p.2.1 • p.1) :=
    funext fun p => by simp only [hcs_Fk, hcs_shiftCLM_apply]
  rw [hEq]
  exact (hK.comp contDiff_fst).mul (hζ.comp hA)

theorem hcs_continuous_iteratedFDeriv_Fk {ζ : ℝ × ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ) (n : ℕ)
    (x : ℝ × (ℝ × ℝ)) :
    Continuous fun v : ℝ × ℝ => iteratedFDeriv ℝ n (hcs_Fk ζ v) x := by
  have hH := hcs_contDiff_Hj hζ
  have key : ∀ v : ℝ × ℝ, iteratedFDeriv ℝ n (hcs_Fk ζ v) x =
      (iteratedFDeriv ℝ n (fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => hcs_Fk ζ p.1 p.2) (v, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × (ℝ × ℝ))) := by
    intro v
    have hK : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) =>
        (fun q : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => hcs_Fk ζ q.1 q.2)
          (((v, 0) : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) + p)) :=
      hH.comp (contDiff_const.add contDiff_id)
    have h1 : hcs_Fk ζ v = (fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) =>
        (fun q : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => hcs_Fk ζ q.1 q.2)
          (((v, 0) : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) + p)) ∘
          ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × (ℝ × ℝ)) := by
      funext y
      simp
    have hA := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
      (f := fun q : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => hcs_Fk ζ q.1 q.2) n
      ((v, 0) : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × (ℝ × ℝ)) x)
    rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hK x (by exact_mod_cast le_top), hA]
    simp
  have hcont : Continuous fun v : ℝ × ℝ =>
      iteratedFDeriv ℝ n (fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => hcs_Fk ζ p.1 p.2) (v, x) :=
    (ContDiff.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top) hH).comp
      (Continuous.prodMk continuous_id continuous_const)
  have hfun : (fun v : ℝ × ℝ => iteratedFDeriv ℝ n (hcs_Fk ζ v) x) = fun v =>
      (iteratedFDeriv ℝ n (fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => hcs_Fk ζ p.1 p.2) (v, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × (ℝ × ℝ))) := funext key
  rw [hfun]
  exact (ContinuousMultilinearMap.continuous_precomp _).comp hcont

/-! ### The main theorem -/

theorem heatConvSmooth : UnforcedLeray.Short.IIb.HeatConvSmooth := by
  intro c ν ζ hc hν hζ
  have hζs : ContDiff ℝ ∞ ζ := hζ.smooth
  have hsmooth : ∀ᵐ v ∂(volume : Measure (ℝ × ℝ)), ContDiff ℝ ∞ (hcs_Fk ζ v) :=
    Eventually.of_forall fun v => by
      have h : hcs_Fk ζ v = fun y => UnforcedLeray.B0284.heatKernel2 (1 / 2) v *
          (ζ ∘ hcs_shiftCLM v) y := funext fun y => rfl
      rw [h]
      exact contDiff_const.mul (hζs.comp (hcs_shiftCLM v).contDiff)
  have hmeas : ∀ (n : ℕ) (x : ℝ × (ℝ × ℝ)),
      AEStronglyMeasurable (fun v : ℝ × ℝ => iteratedFDeriv ℝ n (hcs_Fk ζ v) x)
        (volume : Measure (ℝ × ℝ)) :=
    fun n x => (hcs_continuous_iteratedFDeriv_Fk hζs n x).aestronglyMeasurable
  have hdom : UnforcedLeray.Kernels.LocDominated (volume : Measure (ℝ × ℝ)) (hcs_Fk ζ) univ := by
    intro n x _
    obtain ⟨M, hM0, hM⟩ := hcs_nice_iteratedFDeriv_bound hc hζ n
    refine ⟨univ, univ_mem, fun v => M * ((1 + |v.1|) ^ n *
      UnforcedLeray.B0191.heatKernel 1 (1 / 2) v.1 *
      ((1 + |v.2|) ^ n * UnforcedLeray.B0191.heatKernel 1 (1 / 2) v.2)),
      hcs_integrable_heatKernel2_half_pow n M, Eventually.of_forall fun v y _ => ?_⟩
    exact (hcs_norm_iteratedFDeriv_Fk_le hζs hM0 hM v y).trans (hcs_Fk_bound_le n hM0 v)
  have hΦ : ContDiff ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => ∫ v : ℝ × ℝ, hcs_Fk ζ v y) := by
    rw [← contDiffOn_univ]
    exact UnforcedLeray.Kernels.contDiffOn_integral isOpen_univ hsmooth hmeas hdom
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => (Real.sqrt (2 * (ν * x.1)), x.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    refine ContDiffOn.prodMk ?_ contDiff_snd.contDiffOn
    refine ContDiffOn.sqrt ?_ ?_
    · exact (contDiff_const.mul (contDiff_const.mul contDiff_fst)).contDiffOn
    · intro x hx
      have h0 : 0 < x.1 := hx.1
      positivity
  have hcomp := hΦ.comp_contDiffOn hg
  refine hcomp.congr ?_
  intro x hx
  have h0 : 0 < x.1 := hx.1
  have hsc := hcs_heatKernel2_scale (θ := ν * x.1) (mul_pos hν h0) (fun w => ζ (x.2 - w))
  beta_reduce at hsc
  simp only [heatStreamH, h0, ↓reduceIte, Function.comp_apply, hcs_Fk, hcs_shiftCLM_apply]
  rw [hsc]
