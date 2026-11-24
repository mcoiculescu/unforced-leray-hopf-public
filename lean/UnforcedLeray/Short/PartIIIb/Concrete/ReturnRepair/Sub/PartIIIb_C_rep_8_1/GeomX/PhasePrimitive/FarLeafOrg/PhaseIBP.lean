import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Defs
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

/-- A zero-mean periodic integrable function has all its interval integrals bounded by one
period of `|f|`. -/
theorem phaseIBP_abs_le (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ)
    (hper : ∀ q, f (q + c) = f q) (hint : IntervalIntegrable f volume 0 c)
    (hmean : (∫ q in (0:ℝ)..c, f q) = 0) (x y : ℝ) :
    |∫ t in x..y, f t| ≤ ∫ q in (0:ℝ)..c, |f q| := by
  have hpc : Function.Periodic f c := hper
  have hfi : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    hpc.intervalIntegrable (t := 0) hc.ne' (by rw [zero_add]; exact hint) a b
  set P : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, f s with hP
  have hPper : Function.Periodic P c := by
    intro t
    have h1 : P (t + c) - P t = ∫ s in t..t + c, f s := by
      simp only [hP]
      exact intervalIntegral.integral_interval_sub_left (hfi 0 (t + c)) (hfi 0 t)
    have h2 : ∫ s in t..t + c, f s = ∫ s in (0:ℝ)..0 + c, f s :=
      hpc.intervalIntegral_add_eq t 0
    rw [zero_add] at h2
    linarith [h2, hmean]
  have hdiff : ∀ a b : ℝ, ∫ t in a..b, f t = P b - P a := by
    intro a b
    simp only [hP]
    exact (intervalIntegral.integral_interval_sub_left (hfi 0 b) (hfi 0 a)).symm
  -- bound for ordered points in `[0, c]`
  have hord : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ c →
      |∫ t in u..v, f t| ≤ ∫ q in (0:ℝ)..c, |f q| := by
    intro u v hu huv hv
    have hnn : (0 : ℝ) ≤ ∫ q in (0:ℝ)..c, |f q| :=
      intervalIntegral.integral_nonneg hc.le (fun _ _ => abs_nonneg _)
    calc |∫ t in u..v, f t| ≤ ∫ t in u..v, |f t| :=
          intervalIntegral.abs_integral_le_integral_abs huv
      _ ≤ ∫ q in (0:ℝ)..c, |f q| := by
          apply intervalIntegral.integral_mono_interval hu huv hv
          · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
          · exact (hfi 0 c).abs
  obtain ⟨x₀, hx₀, hPx⟩ := hPper.exists_mem_Ico₀ hc x
  obtain ⟨y₀, hy₀, hPy⟩ := hPper.exists_mem_Ico₀ hc y
  rw [hdiff x y, hPx, hPy, ← hdiff x₀ y₀]
  rcases le_total x₀ y₀ with h | h
  · exact hord x₀ y₀ hx₀.1 h hy₀.2.le
  · rw [intervalIntegral.integral_symm, abs_neg]
    exact hord y₀ x₀ hy₀.1 h hx₀.2.le

/-- Change of variables `l = exp (ε (s - q₀))` on `Ioc`. -/
theorem phaseIBP_cv (ε q₀ : ℝ) (hε : 0 < ε) (A S : ℝ) (G : ℝ → ℝ) :
    ∫ l in Ioc (Real.exp (ε * (A - q₀))) (Real.exp (ε * (S - q₀))), G l =
      ∫ s in Ioc A S, ε * Real.exp (ε * (s - q₀)) * G (Real.exp (ε * (s - q₀))) := by
  have hd : ∀ s ∈ Ioc A S, HasDerivWithinAt (fun x => Real.exp (ε * (x - q₀)))
      (ε * Real.exp (ε * (s - q₀))) (Ioc A S) s := by
    intro s _
    have h1 : HasDerivAt (fun x : ℝ => ε * (x - q₀)) (ε * 1) s :=
      ((hasDerivAt_id s).sub_const q₀).const_mul ε
    have h2 := h1.exp
    exact h2.hasDerivWithinAt.congr_deriv (by ring)
  have hinj : InjOn (fun x => Real.exp (ε * (x - q₀))) (Ioc A S) := by
    intro x _ y _ hxy
    have h := mul_left_cancel₀ hε.ne' (Real.exp_injective hxy)
    linarith
  have himg : (fun x => Real.exp (ε * (x - q₀))) '' Ioc A S =
      Ioc (Real.exp (ε * (A - q₀))) (Real.exp (ε * (S - q₀))) := by
    ext x
    constructor
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
      exact ⟨Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (by linarith) hε),
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hε.le)⟩
    · rintro ⟨h1, h2⟩
      have hxpos : 0 < x := lt_trans (Real.exp_pos _) h1
      have hkey : ε * (q₀ + ε⁻¹ * Real.log x - q₀) = Real.log x := by
        rw [show q₀ + ε⁻¹ * Real.log x - q₀ = ε⁻¹ * Real.log x by ring, ← mul_assoc,
          mul_inv_cancel₀ hε.ne', one_mul]
      refine ⟨q₀ + ε⁻¹ * Real.log x, ⟨?_, ?_⟩, ?_⟩
      · have hl := (Real.lt_log_iff_exp_lt hxpos).2 h1
        have h3 := mul_lt_mul_of_pos_left hl (inv_pos.2 hε)
        have hk2 : ε⁻¹ * (ε * (A - q₀)) = A - q₀ := by
          rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
        linarith
      · have hl := (Real.log_le_iff_le_exp hxpos).2 h2
        have h3 := mul_le_mul_of_nonneg_left hl (inv_pos.2 hε).le
        have hk2 : ε⁻¹ * (ε * (S - q₀)) = S - q₀ := by
          rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
        linarith
      · show Real.exp (ε * (q₀ + ε⁻¹ * Real.log x - q₀)) = x
        rw [hkey, Real.exp_log hxpos]
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hd hinj G]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
  simp only [smul_eq_mul]
  rw [abs_of_pos (mul_pos hε (Real.exp_pos _))]

theorem phaseIBP_fi (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ) (hper : ∀ q, f (q + c) = f q)
    (hint : IntervalIntegrable f volume 0 c) : ∀ x y : ℝ, IntervalIntegrable f volume x y :=
  fun x y => (show Function.Periodic f c from hper).intervalIntegrable (t := 0) hc.ne'
    (by rw [zero_add]; exact hint) x y

/-- Integration by parts on `[A, S]`, `f` integrable, `g` of class `C¹`. -/
theorem phaseIBP_ibp (f : ℝ → ℝ) (A S : ℝ) (hAS : A ≤ S) (hfi : IntervalIntegrable f volume A S)
    (g : ℝ → ℝ) (hg : ContDiffOn ℝ 1 g (uIcc A S)) :
    ∫ x in A..S, g x * f x =
      g S * (∫ t in A..S, f t) - ∫ x in A..S, deriv g x * (∫ t in A..x, f t) := by
  have hJ : AbsolutelyContinuousOnInterval (fun x => ∫ t in A..x, f t) A S :=
    hfi.absolutelyContinuousOnInterval_intervalIntegral (c := A) left_mem_uIcc
  have hgac : AbsolutelyContinuousOnInterval g A S := hg.absolutelyContinuousOnInterval
  have key := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hgac hJ
  simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at key
  have hae : ∫ x in A..S, g x * deriv (fun x => ∫ t in A..x, f t) x =
      ∫ x in A..S, g x * f x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfi.ae_hasDerivAt_integral] with x hx hxI
    have hxc : x ∈ uIcc A S := Set.uIoc_subset_uIcc hxI
    rw [(hx hxc A left_mem_uIcc).deriv]
  rw [← hae]
  exact key

/-- The finite-interval bound, in the substituted variable. -/
theorem phaseIBP_finite (ε q₀ c : ℝ) (hε : 0 < ε) (hc : 0 < c) (f : ℝ → ℝ)
    (hper : ∀ q, f (q + c) = f q) (hint : IntervalIntegrable f volume 0 c)
    (hmean : (∫ q in (0:ℝ)..c, f q) = 0) (u : ℝ → ℝ) (a b A S : ℝ)
    (hA : Real.exp (ε * (A - q₀)) = a) (hS : Real.exp (ε * (S - q₀)) = b)
    (hAS : A < S) (ha : 0 < a) (hab : a < b) (hb1 : b < 1) (hu : ContDiffOn ℝ 1 u (Ioo 0 1)) :
    |∫ l in Ioc a b, u l * f (q₀ + ε⁻¹ * Real.log l)| ≤
      ε * (∫ q in (0:ℝ)..c, |f q|) * (b * |u b| + ∫ l in Ioc a b, |u l + l * deriv u l|) := by
  have hb0 : 0 < b := by rw [← hS]; exact Real.exp_pos _
  have hfi := phaseIBP_fi c hc f hper hint
  have hfs : ∀ s : ℝ, f (q₀ + ε⁻¹ * Real.log (Real.exp (ε * (s - q₀)))) = f s := by
    intro s
    have h : ε⁻¹ * (ε * (s - q₀)) = s - q₀ := by
      rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    rw [Real.log_exp, h]
    congr 1
    ring
  have hcv := phaseIBP_cv ε q₀ hε A S (fun l => u l * f (q₀ + ε⁻¹ * Real.log l))
  rw [hA, hS] at hcv
  beta_reduce at hcv
  simp only [hfs] at hcv
  have hR : ∫ s in Ioc A S, ε * Real.exp (ε * (s - q₀)) * (u (Real.exp (ε * (s - q₀))) * f s) =
      ε * ∫ x in A..S, (u (Real.exp (ε * (x - q₀))) * Real.exp (ε * (x - q₀))) * f x := by
    rw [intervalIntegral.integral_of_le hAS.le, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
    ring
  have hmaps : MapsTo (fun x => Real.exp (ε * (x - q₀))) (uIcc A S) (Ioo 0 1) := by
    intro x hx
    rw [uIcc_of_le hAS.le] at hx
    refine ⟨Real.exp_pos _, lt_of_le_of_lt ?_ hb1⟩
    rw [← hS]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hx.2]) hε.le)
  have hφC : ContDiff ℝ 1 (fun x : ℝ => Real.exp (ε * (x - q₀))) :=
    Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hgC : ContDiffOn ℝ 1
      (fun x => u (Real.exp (ε * (x - q₀))) * Real.exp (ε * (x - q₀))) (uIcc A S) :=
    (hu.comp hφC.contDiffOn hmaps).mul hφC.contDiffOn
  have hder : ∀ s ∈ uIcc A S,
      HasDerivAt (fun x => u (Real.exp (ε * (x - q₀))) * Real.exp (ε * (x - q₀)))
        (ε * Real.exp (ε * (s - q₀)) * (u (Real.exp (ε * (s - q₀))) +
          Real.exp (ε * (s - q₀)) * deriv u (Real.exp (ε * (s - q₀))))) s := by
    intro s hs
    have hl : Real.exp (ε * (s - q₀)) ∈ Ioo (0:ℝ) 1 := hmaps hs
    have hud : HasDerivAt u (deriv u (Real.exp (ε * (s - q₀)))) (Real.exp (ε * (s - q₀))) :=
      ((hu.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hl)).hasDerivAt
    have hφd : HasDerivAt (fun x : ℝ => Real.exp (ε * (x - q₀)))
        (Real.exp (ε * (s - q₀)) * (ε * 1)) s := by
      have h1 : HasDerivAt (fun x : ℝ => ε * (x - q₀)) (ε * 1) s :=
        ((hasDerivAt_id s).sub_const q₀).const_mul ε
      exact h1.exp
    have hc1 := hud.comp s hφd
    have hc2 := hc1.mul hφd
    refine hc2.congr_deriv ?_
    simp only [Function.comp_apply]
    ring
  have hWc : ContinuousOn (fun l => u l + l * deriv u l) (Ioo 0 1) :=
    hu.continuousOn.add (continuousOn_id.mul (hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)))
  have hφcont : ContinuousOn (fun x : ℝ => Real.exp (ε * (x - q₀))) (uIcc A S) :=
    hφC.continuous.continuousOn
  have hZc : ContinuousOn (fun s => ε * Real.exp (ε * (s - q₀)) *
      |u (Real.exp (ε * (s - q₀))) + Real.exp (ε * (s - q₀)) *
        deriv u (Real.exp (ε * (s - q₀)))|) (uIcc A S) :=
    (continuousOn_const.mul hφcont).mul
      (continuous_abs.comp_continuousOn (hWc.comp hφcont hmaps))
  have hZI := hZc.intervalIntegrable (μ := volume)
  have hJ : ∀ x, |∫ t in A..x, f t| ≤ ∫ q in (0:ℝ)..c, |f q| :=
    fun x => phaseIBP_abs_le c hc f hper hint hmean A x
  have hK : ‖∫ x in A..S, deriv (fun x => u (Real.exp (ε * (x - q₀))) * Real.exp (ε * (x - q₀))) x
        * (∫ t in A..x, f t)‖ ≤
      ∫ x in A..S, (∫ q in (0:ℝ)..c, |f q|) * (ε * Real.exp (ε * (x - q₀)) *
        |u (Real.exp (ε * (x - q₀))) + Real.exp (ε * (x - q₀)) *
          deriv u (Real.exp (ε * (x - q₀)))|) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hAS.le
    · apply Filter.Eventually.of_forall
      intro t ht
      have ht' : t ∈ uIcc A S := by
        rw [uIcc_of_le hAS.le]
        exact Set.Ioc_subset_Icc_self ht
      have hdgabs : |deriv (fun x => u (Real.exp (ε * (x - q₀))) * Real.exp (ε * (x - q₀))) t| =
          ε * Real.exp (ε * (t - q₀)) *
            |u (Real.exp (ε * (t - q₀))) + Real.exp (ε * (t - q₀)) *
              deriv u (Real.exp (ε * (t - q₀)))| := by
        rw [(hder t ht').deriv, abs_mul, abs_mul, abs_of_pos hε, abs_of_pos (Real.exp_pos _)]
      have hZn : 0 ≤ ε * Real.exp (ε * (t - q₀)) *
            |u (Real.exp (ε * (t - q₀))) + Real.exp (ε * (t - q₀)) *
              deriv u (Real.exp (ε * (t - q₀)))| :=
        mul_nonneg (mul_nonneg hε.le (Real.exp_pos _).le) (abs_nonneg _)
      have h1 := mul_le_mul_of_nonneg_left (hJ t) (abs_nonneg
        (deriv (fun x => u (Real.exp (ε * (x - q₀))) * Real.exp (ε * (x - q₀))) t))
      rw [Real.norm_eq_abs, abs_mul, hdgabs] at *
      linarith [h1]
    · exact hZI.const_mul _
  rw [intervalIntegral.integral_const_mul] at hK
  have hZeq : ∫ x in A..S, ε * Real.exp (ε * (x - q₀)) *
      |u (Real.exp (ε * (x - q₀))) + Real.exp (ε * (x - q₀)) *
        deriv u (Real.exp (ε * (x - q₀)))| =
      ∫ l in Ioc a b, |u l + l * deriv u l| := by
    have hcv2 := phaseIBP_cv ε q₀ hε A S (fun l => |u l + l * deriv u l|)
    rw [hA, hS] at hcv2
    beta_reduce at hcv2
    rw [intervalIntegral.integral_of_le hAS.le, hcv2]
  rw [hZeq] at hK
  have hibp := phaseIBP_ibp f A S hAS.le (hfi A S) _ hgC
  beta_reduce at hibp
  rw [hS] at hibp
  rw [hcv, hR, hibp, abs_mul, abs_of_pos hε]
  have hgS : |u b * b * (∫ t in A..S, f t)| ≤ b * |u b| * (∫ q in (0:ℝ)..c, |f q|) := by
    rw [abs_mul, abs_mul, abs_of_pos hb0]
    have := mul_le_mul_of_nonneg_left (hJ S) (mul_nonneg (abs_nonneg (u b)) hb0.le)
    linarith [this]
  refine le_trans (mul_le_mul_of_nonneg_left (abs_sub _ _) hε.le) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hgS hK) hε.le) ?_
  apply le_of_eq
  ring

theorem phaseIBP_exp_inv (ε q₀ : ℝ) (hε : 0 < ε) (x : ℝ) (hx : 0 < x) :
    Real.exp (ε * (q₀ + ε⁻¹ * Real.log x - q₀)) = x := by
  rw [show ε * (q₀ + ε⁻¹ * Real.log x - q₀) = Real.log x by
    rw [show q₀ + ε⁻¹ * Real.log x - q₀ = ε⁻¹ * Real.log x by ring, ← mul_assoc,
      mul_inv_cancel₀ hε.ne', one_mul], Real.exp_log hx]

theorem phaseIBP_lt (ε q₀ : ℝ) (hε : 0 < ε) (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    q₀ + ε⁻¹ * Real.log x < q₀ + ε⁻¹ * Real.log y := by
  have h := mul_lt_mul_of_pos_left (Real.log_lt_log hx hxy) (inv_pos.2 hε)
  linarith

theorem phaseIBP_int_of_bound (b δ M : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hδ : 0 < δ)
    (V : ℝ → ℝ) (hV : ContinuousOn V (Ioo 0 1))
    (hbd : ∀ l ∈ Ioc 0 b, |V l| ≤ M * l ^ (δ - 1)) : IntegrableOn V (Ioc 0 b) := by
  have hI : IntervalIntegrable (fun l : ℝ => M * l ^ (δ - 1)) volume 0 b :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < δ - 1)).const_mul M
  have hI' : IntegrableOn (fun l : ℝ => M * l ^ (δ - 1)) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0.le).1 hI
  refine hI'.mono' ?_ ?_
  · exact (hV.mono (fun l hl => ⟨hl.1, lt_of_le_of_lt hl.2 hb1⟩)).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    exact hbd l hl

theorem phaseIBP_abs_re (θ z : ℂ) (hθ : ‖θ‖ ≤ 1) : |(θ * z).re| ≤ ‖z‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hθ

theorem phaseIBP_main (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ) (hfm : Measurable f)
    (hper : ∀ q, f (q + c) = f q) (hint : IntervalIntegrable f volume 0 c)
    (hmean : (∫ q in (0:ℝ)..c, f q) = 0) (q₀ : ℝ) (ω : ℝ → ℂ) (b δ M : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hω : ContDiffOn ℝ 1 ω (Ioo 0 1))
    (hbd1 : ∀ l ∈ Ioc (0 : ℝ) b, ‖ω l‖ ≤ M * l ^ (δ - 1))
    (hbd2 : ∀ l ∈ Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖ ≤ M * l ^ (δ - 1)) :
    ‖∫ l in Ioc (0 : ℝ) b, ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)‖ ≤
      ε * (∫ q in (0 : ℝ)..c, |f q|) *
        (b * ‖ω b‖ + ∫ l in Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖) := by
  have hI0 : 0 ≤ ∫ q in (0 : ℝ)..c, |f q| :=
    intervalIntegral.integral_nonneg hc.le (fun _ _ => abs_nonneg _)
  have hWn : 0 ≤ ∫ l in Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun _ _ => norm_nonneg _)
  have hR0 : 0 ≤ ε * (∫ q in (0 : ℝ)..c, |f q|) *
      (b * ‖ω b‖ + ∫ l in Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖) :=
    mul_nonneg (mul_nonneg hε.le hI0) (add_nonneg (mul_nonneg hb0.le (norm_nonneg _)) hWn)
  by_cases hF : IntegrableOn (fun l => ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)) (Ioc 0 b)
  swap
  · rw [MeasureTheory.integral_undef hF, norm_zero]
    exact hR0
  obtain ⟨X, hXdef⟩ : ∃ X : ℂ, X = ∫ l in Ioc (0 : ℝ) b,
      ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ) := ⟨_, rfl⟩
  rw [← hXdef]
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℂ, θ = ((‖X‖ : ℝ) : ℂ) / X := ⟨_, rfl⟩
  have hθ1 : ‖θ‖ ≤ 1 := by
    by_cases hX : X = 0
    · rw [hθdef, hX, div_zero, norm_zero]
      exact zero_le_one
    · have : ‖θ‖ = 1 := by
        rw [hθdef, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          div_self (norm_ne_zero_iff.2 hX)]
      exact this.le
  have hθX : θ * X = ((‖X‖ : ℝ) : ℂ) := by
    by_cases hX : X = 0
    · simp [hX]
    · rw [hθdef, div_mul_cancel₀ _ hX]
  -- real part representation of `‖X‖`
  have hXre : ‖X‖ = ∫ l in Ioc (0 : ℝ) b, (θ * ω l).re * f (q₀ + ε⁻¹ * Real.log l) := by
    calc ‖X‖ = (θ * X).re := by rw [hθX, Complex.ofReal_re]
      _ = (∫ l in Ioc (0 : ℝ) b, θ * (ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ))).re := by
          rw [MeasureTheory.integral_const_mul, ← hXdef]
      _ = ∫ l in Ioc (0 : ℝ) b, (θ * (ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ))).re := by
          exact (integral_re (hF.const_mul θ)).symm
      _ = ∫ l in Ioc (0 : ℝ) b, (θ * ω l).re * f (q₀ + ε⁻¹ * Real.log l) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun l _ => ?_)
          rw [← mul_assoc, Complex.re_mul_ofReal]
  -- the real part function `u`
  obtain ⟨u, hudef⟩ : ∃ u : ℝ → ℝ, u = fun l => (θ * ω l).re := ⟨_, rfl⟩
  have hu_C : ContDiffOn ℝ 1 u (Ioo 0 1) := by
    rw [hudef]
    exact Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hω)
  have hdu : ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt u (θ * deriv ω l).re l := by
    intro l hl
    have hωd : HasDerivAt ω (deriv ω l) l :=
      ((hω.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hl)).hasDerivAt
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt l (hωd.const_mul θ)
    rw [hudef]
    exact h1
  have hWu : ∀ l ∈ Ioo (0:ℝ) 1, u l + l * deriv u l = (θ * (ω l + (l:ℂ) * deriv ω l)).re := by
    intro l hl
    have e1 : θ * (ω l + (l:ℂ) * deriv ω l) = θ * ω l + (l:ℂ) * (θ * deriv ω l) := by ring
    rw [e1, Complex.add_re, Complex.re_ofReal_mul, (hdu l hl).deriv, hudef]
  have hWuabs : ∀ l ∈ Ioc (0:ℝ) b, |u l + l * deriv u l| ≤ ‖ω l + (l:ℂ) * deriv ω l‖ := by
    intro l hl
    rw [hWu l ⟨hl.1, lt_of_le_of_lt hl.2 hb1⟩]
    exact phaseIBP_abs_re θ _ hθ1
  have hub : |u b| ≤ ‖ω b‖ := by
    have hub' : u b = (θ * ω b).re := by rw [hudef]
    rw [hub']
    exact phaseIBP_abs_re θ _ hθ1
  have hWc : ContinuousOn (fun l : ℝ => ω l + (l:ℂ) * deriv ω l) (Ioo 0 1) :=
    hω.continuousOn.add ((Complex.continuous_ofReal.continuousOn).mul
      (hω.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)))
  have hWn_int : IntegrableOn (fun l => ‖ω l + (l:ℂ) * deriv ω l‖) (Ioc 0 b) :=
    phaseIBP_int_of_bound b δ M hb0 hb1 hδ (fun l => ‖ω l + (l:ℂ) * deriv ω l‖) hWc.norm
      (fun l hl => by rw [abs_norm]; exact hbd2 l hl)
  have hWuc : ContinuousOn (fun l => |u l + l * deriv u l|) (Ioo 0 1) :=
    continuous_abs.comp_continuousOn (hu_C.continuousOn.add (continuousOn_id.mul
      (hu_C.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num))))
  have hWu_int : IntegrableOn (fun l => |u l + l * deriv u l|) (Ioc 0 b) :=
    phaseIBP_int_of_bound b δ M hb0 hb1 hδ (fun l => |u l + l * deriv u l|) hWuc
      (fun l hl => by rw [abs_abs]; exact (hWuabs l hl).trans (hbd2 l hl))
  have hWbd : ∫ l in Ioc (0:ℝ) b, |u l + l * deriv u l| ≤
      ∫ l in Ioc (0:ℝ) b, ‖ω l + (l:ℂ) * deriv ω l‖ :=
    MeasureTheory.setIntegral_mono_on hWu_int hWn_int measurableSet_Ioc (fun l hl => hWuabs l hl)
  have hXre' : ‖X‖ = ∫ l in Ioc (0 : ℝ) b, u l * f (q₀ + ε⁻¹ * Real.log l) := by
    rw [hXre]
    simp only [hudef]
  -- the sequence of lower limits `b / (n + 2)`
  have ha_pos : ∀ n : ℕ, 0 < b / ((n:ℝ) + 2) := fun n => by positivity
  have ha_lt : ∀ n : ℕ, b / ((n:ℝ) + 2) < b := fun n => by
    rw [div_lt_iff₀ (by positivity)]
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have ha_anti : ∀ m n : ℕ, m ≤ n → b / ((n:ℝ) + 2) ≤ b / ((m:ℝ) + 2) := by
    intro m n hmn
    have : (m:ℝ) ≤ n := by exact_mod_cast hmn
    exact div_le_div_of_nonneg_left hb0.le (by positivity) (by linarith)
  have hU : (⋃ n : ℕ, Ioc (b / ((n:ℝ) + 2)) b) = Ioc 0 b := by
    ext l
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨(ha_pos n).trans h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (b / l)
      refine ⟨n, ?_, h2⟩
      have h3 : b < (n:ℝ) * l := (div_lt_iff₀ h1).1 hn
      rw [div_lt_iff₀ (by positivity)]
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
  have hmono : Monotone (fun n : ℕ => Ioc (b / ((n:ℝ) + 2)) b) :=
    fun m n hmn => Set.Ioc_subset_Ioc_left (ha_anti m n hmn)
  have hmono_u : ∀ n : ℕ, ∫ l in Ioc (b / ((n:ℝ) + 2)) b, |u l + l * deriv u l| ≤
      ∫ l in Ioc (0:ℝ) b, |u l + l * deriv u l| := fun n =>
    MeasureTheory.setIntegral_mono_set hWu_int (Filter.Eventually.of_forall (fun l => abs_nonneg _))
      (Set.Ioc_subset_Ioc_left (ha_pos n).le).eventuallyLE
  have hfin : ∀ n : ℕ, |∫ l in Ioc (b / ((n:ℝ) + 2)) b, u l * f (q₀ + ε⁻¹ * Real.log l)| ≤
      ε * (∫ q in (0:ℝ)..c, |f q|) *
        (b * |u b| + ∫ l in Ioc (0:ℝ) b, |u l + l * deriv u l|) := by
    intro n
    have h := phaseIBP_finite ε q₀ c hε hc f hper hint hmean u (b / ((n:ℝ) + 2)) b
      (q₀ + ε⁻¹ * Real.log (b / ((n:ℝ) + 2))) (q₀ + ε⁻¹ * Real.log b)
      (phaseIBP_exp_inv ε q₀ hε _ (ha_pos n)) (phaseIBP_exp_inv ε q₀ hε _ hb0)
      (phaseIBP_lt ε q₀ hε _ _ (ha_pos n) (ha_lt n)) (ha_pos n) (ha_lt n) hb1 hu_C
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hε.le hI0))
    linarith [hmono_u n]
  have hfin' : ∀ n : ℕ, |∫ l in Ioc (b / ((n:ℝ) + 2)) b, u l * f (q₀ + ε⁻¹ * Real.log l)| ≤
      ε * (∫ q in (0:ℝ)..c, |f q|) *
        (b * |u b| + ∫ l in Ioc (0:ℝ) b, |u l + l * deriv u l|) := hfin
  have hUint : IntegrableOn (fun l => u l * f (q₀ + ε⁻¹ * Real.log l)) (Ioc 0 b) := by
    have hre := (hF.const_mul θ).re
    refine hre.congr (Filter.Eventually.of_forall (fun l => ?_))
    show (θ * (ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ))).re =
      u l * f (q₀ + ε⁻¹ * Real.log l)
    rw [hudef, ← mul_assoc, Complex.re_mul_ofReal]
  have hlim : Tendsto (fun n : ℕ => ∫ l in Ioc (b / ((n:ℝ) + 2)) b,
      u l * f (q₀ + ε⁻¹ * Real.log l)) atTop
      (𝓝 (∫ l in Ioc (0:ℝ) b, u l * f (q₀ + ε⁻¹ * Real.log l))) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone (μ := volume)
      (s := fun n : ℕ => Ioc (b / ((n:ℝ) + 2)) b)
      (f := fun l => u l * f (q₀ + ε⁻¹ * Real.log l))
      (fun n => measurableSet_Ioc) hmono (by rw [hU]; exact hUint)
    rw [hU] at h
    exact h
  have hcore : |∫ l in Ioc (0:ℝ) b, u l * f (q₀ + ε⁻¹ * Real.log l)| ≤
      ε * (∫ q in (0:ℝ)..c, |f q|) *
        (b * |u b| + ∫ l in Ioc (0:ℝ) b, |u l + l * deriv u l|) :=
    le_of_tendsto hlim.abs (Filter.Eventually.of_forall hfin')
  calc ‖X‖ = |‖X‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ = |∫ l in Ioc (0:ℝ) b, u l * f (q₀ + ε⁻¹ * Real.log l)| := by rw [hXre']
    _ ≤ ε * (∫ q in (0:ℝ)..c, |f q|) *
        (b * |u b| + ∫ l in Ioc (0:ℝ) b, |u l + l * deriv u l|) := hcore
    _ ≤ ε * (∫ q in (0:ℝ)..c, |f q|) *
        (b * ‖ω b‖ + ∫ l in Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hub hb0.le) hWbd)
        (mul_nonneg hε.le hI0)

/-- **(b) One phase primitive in the dilation variable** (target `phaseIBP`). -/
theorem phaseIBP : UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg.PhaseIBP := by
  intro ε hε c hc f hfm hper hint hmean q₀ ω b δ M hb0 hb1 hδ hM hω hbd1 hbd2
  exact phaseIBP_main ε hε c hc f hfm hper hint hmean q₀ ω b δ M hb0 hb1 hδ hM hω hbd1 hbd2

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
