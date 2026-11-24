import UnforcedLeray.Lib.HeatR3B.WeakLap
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# Heat interpolation of the gradient for smooth bounded fields (INF11 S9b, part 2)

Helper for target **S9b** (`gradient_interp`, D15) of

`scoping/INF01-CZ.md` §4.4 (manuscript `paper/main.tex` lines 7541–7548, `eq:free-stress-19`,
B0428; the manuscript calls it "spatial heat interpolation" at line 3816):

`∂ₑv = ∂ₑe^{tΔ}v - ∫_0^t ∂ₑe^{sΔ}Δv ds`, hence
`‖∂ₑv‖_q ≤ c t^{-1/2}|e| ‖v‖_q + 2c t^{1/2}|e| ‖Δv‖_q` (Young for `∂G_s ∈ L¹` and Minkowski).

Main results:
* `norm_iteratedFDeriv_average_bounded`, `bounded_derivs_average`: for `w ∈ L^q`, `q < ∞`, every
  derivative of `e^{θΔ}w` is bounded (`a ≤ 1 + a^q`);
* `fderiv_eq_heat_formula`: the identity above at every point, for `C³` fields with bounded
  derivatives (from the compiled heat FTC `average_sub_eq_integral` of T7);
* `eLpNorm_fderiv_le_interp`: the `L^q` bound, `1 ≤ q < ∞`, with `c = derivLpConst 3 1 1`
  (`= ‖∇G_1‖_{L¹}`).

Status: infrastructure for S9b.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Bounded derivatives of `e^{θΔ}w` for `w ∈ L^q` -/

theorem le_one_add_rpow_self {a q : ℝ} (ha : 0 ≤ a) (hq : 1 ≤ q) : a ≤ 1 + a ^ q := by
  rcases le_total a 1 with h | h
  · have := Real.rpow_nonneg ha q
    linarith
  · have : a ≤ a ^ q := by
      calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
        _ ≤ a ^ q := Real.rpow_le_rpow_of_exponent_le h hq
    linarith

theorem integrable_norm_iteratedFDeriv_kernel {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    Integrable (fun z : Space => ‖iteratedFDeriv ℝ k (kernel θ) z‖) := by
  have h := Gaussian.memLp_iteratedFDeriv_gaussKernel (d := 3) k hθ 1
  rw [memLp_one_iff_integrable, Gaussian.gaussKernel_three_eq] at h
  exact h.norm

theorem norm_iteratedFDeriv_kernel_le {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    ∃ S : ℝ, 0 < S ∧ ∀ z : Space, ‖iteratedFDeriv ℝ k (kernel θ) z‖ ≤ S := by
  obtain ⟨S, hS0, hS⟩ := norm_iteratedFDeriv_gaussKernel_le_weight 3 k hθ (m := 0) le_rfl
  refine ⟨S, hS0, fun z => ?_⟩
  have := hS z
  rw [Gaussian.gaussKernel_three_eq] at this
  simpa using this

/-- Every derivative of `e^{θΔ}w`, `w ∈ L^q` (`1 ≤ q < ∞`), `θ > 0`, is bounded. -/
theorem norm_iteratedFDeriv_average_bounded {w : Space → E} {q : ℝ≥0∞} (hq1 : 1 ≤ q)
    (hq : q ≠ ⊤) (hw : MemLp w q volume) {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (average θ w) x‖ ≤ M := by
  have hadm := HeatAdmissible.of_memLp hq1 hw
  set a : Space → ℝ := fun z => ‖iteratedFDeriv ℝ k (kernel θ) z‖ with ha
  have ha_int : Integrable a := integrable_norm_iteratedFDeriv_kernel hθ k
  obtain ⟨S, hS0, hS⟩ := norm_iteratedFDeriv_kernel_le hθ k
  have hq0 : q ≠ 0 := (lt_of_lt_of_le one_pos hq1).ne'
  set qr : ℝ := q.toReal with hqr_def
  have hqr : 1 ≤ qr := by
    have := ENNReal.toReal_mono hq hq1
    rwa [ENNReal.toReal_one] at this
  have hpow : Integrable (fun y => ‖w y‖ ^ qr) := hw.integrable_norm_rpow hq0 hq
  refine ⟨(∫ z, a z) + S * ∫ y, ‖w y‖ ^ qr, fun x => ?_⟩
  refine (norm_iteratedFDeriv_average_le_kernel hadm hθ k x).trans ?_
  have hint : Integrable (fun y => a (x - y) + S * ‖w y‖ ^ qr) :=
    (ha_int.comp_sub_left x).add (hpow.const_mul S)
  calc ∫ y, ‖iteratedFDeriv ℝ k (kernel θ) (x - y)‖ * ‖w y‖
      ≤ ∫ y, (a (x - y) + S * ‖w y‖ ^ qr) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) hint
          (Eventually.of_forall fun y => ?_)
        have h1 := le_one_add_rpow_self (norm_nonneg (w y)) hqr
        have h2 : 0 ≤ ‖w y‖ ^ qr := Real.rpow_nonneg (norm_nonneg _) _
        calc a (x - y) * ‖w y‖ ≤ a (x - y) * (1 + ‖w y‖ ^ qr) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = a (x - y) + a (x - y) * ‖w y‖ ^ qr := by ring
          _ ≤ a (x - y) + S * ‖w y‖ ^ qr := by
              gcongr
              exact hS _
    _ = (∫ z, a z) + S * ∫ y, ‖w y‖ ^ qr := by
        rw [integral_add (ha_int.comp_sub_left x) (hpow.const_mul S),
          integral_sub_left_eq_self a volume x, integral_const_mul]

/-- Uniform bound for the derivatives of order `≤ 3` of `e^{θΔ}w`, `w ∈ L^q`. -/
theorem bounded_derivs_average {w : Space → E} {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hq : q ≠ ⊤)
    (hw : MemLp w q volume) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k (average θ w) x‖ ≤ M := by
  choose M hM using fun k => norm_iteratedFDeriv_average_bounded hq1 hq hw hθ k
  refine ⟨∑ j ∈ Finset.range 4, |M j|, fun k hk x => (hM k x).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))

/-! ### The Laplacian as a linear image of the Hessian -/

/-- `Δu = A(D²u)` with the fixed continuous linear map `A(H) = ∑ᵢ H(eᵢ, eᵢ)`. -/
def vlapCLM : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) E →L[ℝ] E :=
  ∑ i : Fin 3, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) E
    ![coordinateVector i, coordinateVector i]

theorem vlap_eq_vlapCLM (u : Space → E) :
    vlap u = fun x => (vlapCLM : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) E →L[ℝ] E)
      (iteratedFDeriv ℝ 2 u x) := by
  funext x
  simp [vlap, vlapCLM]

theorem contDiff_vlap {u : Space → E} {n : ℕ} (hu : ContDiff ℝ (n + 2) u) :
    ContDiff ℝ n (vlap u) := by
  rw [vlap_eq_vlapCLM]
  exact (vlapCLM (E := E)).contDiff.comp (hu.iteratedFDeriv_right (by norm_cast))

theorem norm_vlap_le' (u : Space → E) (x : Space) :
    ‖vlap u x‖ ≤ ‖(vlapCLM : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) E →L[ℝ] E)‖ *
      ‖iteratedFDeriv ℝ 2 u x‖ := by
  rw [vlap_eq_vlapCLM]
  exact ContinuousLinearMap.le_opNorm _ _

theorem norm_fderiv_vlap_le {u : Space → E} (hu : ContDiff ℝ 3 u) (x : Space) :
    ‖fderiv ℝ (vlap u) x‖ ≤
      ‖(vlapCLM : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) E →L[ℝ] E)‖ *
      ‖iteratedFDeriv ℝ 3 u x‖ := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) x :=
    ((hu.iteratedFDeriv_right (m := 1) (i := 2) (by norm_num)).differentiable
      (by norm_num)) x
  have h : HasFDerivAt (vlap u) ((vlapCLM (E := E)).comp (fderiv ℝ (iteratedFDeriv ℝ 2 u) x)) x := by
    rw [vlap_eq_vlapCLM]
    exact (vlapCLM (E := E)).hasFDerivAt.comp x hd.hasFDerivAt
  rw [h.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [norm_fderiv_iteratedFDeriv]

/-! ### The heat formula for the gradient -/

/-- `(e^{sΔ}g)(x)e = e^{sΔ}(g(·)e)(x)` for bounded continuous operator-valued `g`. -/
theorem average_apply_eq {g : Space → Space →L[ℝ] E} (hg : Continuous g) {M : ℝ}
    (hM : ∀ y, ‖g y‖ ≤ M) {s : ℝ} (hs : 0 < s) (x e : Space) :
    average s g x e = average s (fun y => g y e) x := by
  simp only [average]
  rw [ContinuousLinearMap.integral_apply (integrable_average_of_bound hs hg hM x)]
  rfl

/-- **The heat formula for the gradient.** For `v ∈ C³` with `|D^k v| ≤ M` (`k ≤ 3`), `t > 0`:
`∂ₑv(x) = ∂ₑ(e^{tΔ}v)(x) - ∫_0^t e^{sΔ}(∂ₑΔv)(x) ds`. -/
theorem fderiv_eq_heat_formula {v : Space → E} (hv : ContDiff ℝ 3 v) {M : ℝ}
    (hb : ∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M) {t : ℝ} (ht : 0 < t) (x e : Space) :
    fderiv ℝ v x e = fderiv ℝ (average t v) x e -
      ∫ s in (0)..t, average s (fun y => fderiv ℝ (vlap v) y e) x := by
  set Λ : Space → E := vlap v with hΛdef
  have hb2 : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M := fun k hk => hb k (by omega)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hb0 : ∀ y, ‖v y‖ ≤ M := fun y => by
    simpa only [norm_iteratedFDeriv_zero] using hb 0 (by norm_num) y
  have hb1 : ∀ y, ‖fderiv ℝ v y‖ ≤ M := fun y => by
    simpa only [norm_iteratedFDeriv_one] using hb 1 (by norm_num) y
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hb0 0)
  have hΛ : ContDiff ℝ 1 Λ := contDiff_vlap (n := 1) (hv.of_le (by norm_num))
  set A : ℝ := ‖(vlapCLM : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) E →L[ℝ] E)‖
    with hAdef
  have hA0 : 0 ≤ A := norm_nonneg (vlapCLM (E := E))
  have hΛb0 : ∀ y, ‖Λ y‖ ≤ A * M := fun y =>
    (norm_vlap_le' (E := E) v y).trans
      (mul_le_mul_of_nonneg_left (hb 2 (by norm_num) y) hA0)
  have hΛb1 : ∀ y, ‖fderiv ℝ Λ y‖ ≤ A * M := fun y =>
    (norm_fderiv_vlap_le (E := E) hv y).trans
      (mul_le_mul_of_nonneg_left (hb 3 le_rfl y) hA0)
  have hΛc : Continuous Λ := hΛ.continuous
  have hΛ'c : Continuous (fderiv ℝ Λ) := hΛ.continuous_fderiv one_ne_zero
  have hsub : Ι (0 : ℝ) t ⊆ Ioi 0 := fun s hs => by
    rw [uIoc_of_le ht.le] at hs; exact hs.1
  -- the FTC of T7
  have hftc : ∀ y, v y = average t v y - ∫ s in (0)..t, average s Λ y := fun y => by
    have := average_sub_eq_integral hv2 hb2 ht y
    rw [← this]; abel
  -- derivative of the time integral
  have hcontΛ : ∀ y, ContinuousOn (fun s : ℝ => average s Λ y) (Ioi 0) := fun y =>
    continuousOn_average_time_of_bound hΛc.aestronglyMeasurable hΛb0 y
  have hcontΛ' : ContinuousOn (fun s : ℝ => average s (fderiv ℝ Λ) x) (Ioi 0) :=
    continuousOn_average_time_of_bound hΛ'c.aestronglyMeasurable hΛb1 x
  have hiiΛ' : IntervalIntegrable (fun s => average s (fderiv ℝ Λ) x) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    refine ⟨(hcontΛ'.mono fun s hs => hs.1).aestronglyMeasurable measurableSet_Ioc, ?_⟩
    refine HasFiniteIntegral.restrict_of_bounded (C := A * M) measure_Ioc_lt_top ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact norm_average_le_of_bound hs.1 hΛb1 x
  have hI : HasFDerivAt (fun y => ∫ s in (0)..t, average s Λ y)
      (∫ s in (0)..t, average s (fderiv ℝ Λ) x) x := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
      (𝕜 := ℝ) (F := fun y s => average s Λ y) (F' := fun y s => average s (fderiv ℝ Λ) y)
      (x₀ := x) (s := univ) (bound := fun _ => A * M) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun y =>
        ((hcontΛ y).mono hsub).aestronglyMeasurable measurableSet_uIoc
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
      refine ⟨((hcontΛ x).mono fun s hs => hs.1).aestronglyMeasurable measurableSet_Ioc, ?_⟩
      refine HasFiniteIntegral.restrict_of_bounded (C := A * M) measure_Ioc_lt_top ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact norm_average_le_of_bound hs.1 hΛb0 x
    · exact (hcontΛ'.mono hsub).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun s hs y _ =>
        norm_average_le_of_bound (mem_Ioi.1 (hsub hs)) hΛb1 y
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun s hs y _ =>
        hasFDerivAt_average (mem_Ioi.1 (hsub hs)) hΛ hΛb0 hΛb1 y
  have hT : HasFDerivAt (average t v) (average t (fderiv ℝ v) x) x :=
    hasFDerivAt_average ht hv1 hb0 hb1 x
  have hD : HasFDerivAt v (average t (fderiv ℝ v) x - ∫ s in (0)..t, average s (fderiv ℝ Λ) x) x :=
    (hT.sub hI).congr_of_eventuallyEq (Eventually.of_forall hftc)
  rw [hD.fderiv, ContinuousLinearMap.sub_apply, fderiv_average ht hv1 hb0 hb1,
    ContinuousLinearMap.intervalIntegral_apply hiiΛ' e]
  congr 1
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
  exact average_apply_eq hΛ'c hΛb1 (mem_Ioi.1 (hsub hs)) x e

/-! ### The `L^q` bound -/

/-- `∫_0^t s^{-1/2} ds = 2 t^{1/2}` in `ℝ≥0∞`, with a constant factor. -/
theorem lintegral_rpow_neg_half {t : ℝ} (ht : 0 < t) (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ s in Ioc 0 t, ENNReal.ofReal (K * s ^ (-(1 : ℝ) / 2)) =
      ENNReal.ofReal (K * (2 * t ^ (1 / 2 : ℝ))) := by
  have hint : IntegrableOn (fun s : ℝ => K * s ^ (-(1 : ℝ) / 2)) (Ioc 0 t) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
      (r := -(1 : ℝ) / 2) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at h
    exact h.const_mul K
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_const_mul, ← intervalIntegral.integral_of_le ht.le,
      integral_rpow (Or.inl (by norm_num))]
    rw [Real.zero_rpow (by norm_num), show (-(1 : ℝ) / 2 + 1) = 1 / 2 by norm_num]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg hK (Real.rpow_nonneg hs.1.le _)

/-- **Heat interpolation of the gradient, smooth case** (`scoping/INF01-CZ.md` §4.4). For
`v ∈ C³` with bounded derivatives, `v, Δv ∈ L^q` (`1 ≤ q < ∞`), `t > 0` and a direction `e`:
`‖∂ₑv‖_q ≤ c t^{-1/2}|e| ‖v‖_q + 2c t^{1/2}|e| ‖Δv‖_q`, `c = ‖∇G_1‖_{L¹}`. -/
theorem eLpNorm_fderiv_le_interp {v : Space → E} (hv : ContDiff ℝ 3 v) {M : ℝ}
    (hb : ∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M) {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hq : q ≠ ⊤)
    (hvq : MemLp v q volume) (hΛq : MemLp (vlap v) q volume) {t : ℝ} (ht : 0 < t) (e : Space) :
    eLpNorm (fun x => fderiv ℝ v x e) q volume ≤
      ENNReal.ofReal (Gaussian.derivLpConst 3 1 1 * t ^ (-(1 : ℝ) / 2) * ‖e‖) *
          eLpNorm v q volume +
        ENNReal.ofReal (2 * Gaussian.derivLpConst 3 1 1 * t ^ (1 / 2 : ℝ) * ‖e‖) *
          eLpNorm (vlap v) q volume := by
  set c : ℝ := Gaussian.derivLpConst 3 1 1 with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  set Λ : Space → E := vlap v with hΛdef
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hΛ : ContDiff ℝ 1 Λ := contDiff_vlap (n := 1) (hv.of_le (by norm_num))
  set g : Space → E := fun y => fderiv ℝ Λ y e with hg
  have hgc : Continuous g := (hΛ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  set A : ℝ := ‖(vlapCLM : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) E →L[ℝ] E)‖
    with hAdef
  have hA0 : 0 ≤ A := norm_nonneg (vlapCLM (E := E))
  have hΛb0 : ∀ y, ‖Λ y‖ ≤ A * M := fun y =>
    (norm_vlap_le' (E := E) v y).trans
      (mul_le_mul_of_nonneg_left (hb 2 (by norm_num) y) hA0)
  have hΛb1 : ∀ y, ‖fderiv ℝ Λ y‖ ≤ A * M := fun y =>
    (norm_fderiv_vlap_le (E := E) hv y).trans
      (mul_le_mul_of_nonneg_left (hb 3 le_rfl y) hA0)
  have hgb : ∀ y, ‖g y‖ ≤ A * M * ‖e‖ := fun y =>
    ((fderiv ℝ Λ y).le_opNorm e).trans (mul_le_mul_of_nonneg_right (hΛb1 y) (norm_nonneg _))
  set F : Space → ℝ → E := fun x s => average s g x with hF
  set Afun : Space → E := fun x => fderiv ℝ (average t v) x e with hAfun
  set Bfun : Space → E := fun x => ∫ s in (0)..t, F x s with hBfun
  have hform : (fun x => fderiv ℝ v x e) = fun x => Afun x - Bfun x :=
    funext fun x => fderiv_eq_heat_formula hv hb ht x e
  have hAc : Continuous Afun := by
    have hadm := HeatAdmissible.of_memLp hq1 hvq
    exact ((contDiff_average hadm ht).continuous_fderiv (by simp)).clm_apply continuous_const
  have hBc : Continuous Bfun := by
    have : Bfun = fun x => Afun x - fderiv ℝ v x e := by
      funext x; rw [congrFun hform x]; abel
    rw [this]
    exact hAc.sub ((hv1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  rw [hform]
  refine (eLpNorm_sub_le hAc.aestronglyMeasurable hBc.aestronglyMeasurable hq1).trans ?_
  refine add_le_add (eLpNorm_fderiv_average_apply_le hq1 hvq ht e) ?_
  -- the time integral, by Minkowski
  have hBeq : Bfun = fun x => ∫ s, F x s ∂(volume.restrict (Ioc 0 t)) := by
    funext x; rw [hBfun]; dsimp only; rw [intervalIntegral.integral_of_le ht.le]
  have hgadm : HeatAdmissible g := HeatAdmissible.of_memLp (p := ⊤) le_top
    (memLp_top_of_bound hgc.aestronglyMeasurable _ (Eventually.of_forall hgb))
  have hjoint : ContinuousOn (Function.uncurry F) (univ ×ˢ Ioi 0) := by
    have h := continuousOn_average_joint hgadm
    have hmaps : MapsTo Prod.swap (univ ×ˢ Ioi (0 : ℝ)) (Ioi 0 ×ˢ (univ : Set Space)) :=
      fun p hp => ⟨hp.2, trivial⟩
    exact h.comp continuous_swap.continuousOn hmaps
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure Space).prod (volume.restrict (Ioc 0 t))) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure Space)), Measure.prod_restrict]
    exact (hjoint.mono (prod_mono subset_rfl fun s hs => hs.1)).aestronglyMeasurable
      (MeasurableSet.univ.prod measurableSet_Ioc)
  rw [hBeq]
  refine (PlanarBS.Conv.eLpNorm_integral_le hmeas hq1 hq).trans ?_
  have hslice : ∀ s ∈ Ioc 0 t, eLpNorm (fun x => F x s) q volume ≤
      ENNReal.ofReal (c * ‖e‖ * s ^ (-(1 : ℝ) / 2)) * eLpNorm Λ q volume := by
    intro s hs
    have heq : (fun x => F x s) = fun x => fderiv ℝ (average s Λ) x e := by
      funext x
      simp only [hF, hg]
      rw [← average_apply_eq (hΛ.continuous_fderiv one_ne_zero) hΛb1 hs.1 x e,
        fderiv_average hs.1 hΛ hΛb0 hΛb1]
    rw [heq]
    refine (eLpNorm_fderiv_average_apply_le hq1 hΛq hs.1 e).trans (le_of_eq ?_)
    congr 2
    ring
  calc ∫⁻ s, eLpNorm (fun x => F x s) q volume ∂(volume.restrict (Ioc 0 t))
      ≤ ∫⁻ s in Ioc 0 t, ENNReal.ofReal (c * ‖e‖ * s ^ (-(1 : ℝ) / 2)) * eLpNorm Λ q volume :=
        setLIntegral_mono' measurableSet_Ioc hslice
    _ = (∫⁻ s in Ioc 0 t, ENNReal.ofReal (c * ‖e‖ * s ^ (-(1 : ℝ) / 2))) *
          eLpNorm Λ q volume := by
        rw [lintegral_mul_const' _ _ hΛq.eLpNorm_ne_top]
    _ = ENNReal.ofReal (2 * c * t ^ (1 / 2 : ℝ) * ‖e‖) * eLpNorm Λ q volume := by
        rw [lintegral_rpow_neg_half ht _ (by positivity)]
        congr 2
        ring

end UnforcedLeray.Heat
