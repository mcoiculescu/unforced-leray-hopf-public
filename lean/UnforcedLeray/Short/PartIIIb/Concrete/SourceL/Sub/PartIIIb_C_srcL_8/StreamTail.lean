import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8.NewtonAdd

/-!
# Integrability of the outward stream tail (`StreamTailInt`, source 4180-4183, 4917-4937)

For `y` with `(ε cylR y)² > 5ν/6` and `ρ > cylR y`, the point `w = ε • rayPt y ρ` has horizontal
norm `ερ`, and `|w_h - t x'| ≥ (1 - R/(ε cylR y)) ερ` on the disk `|x'|² ≤ 5ν/6`, `t ∈ [0,1]`.
With the homogeneous bound `|∂³N(p)| ≲ |p|⁻⁴`, the ray integral `ρ · (youngW_μ - youngW_{μ+1})`
is dominated by `C ρ⁻³`, which is integrable on `(cylR y, ∞)`.  Measurability in `ρ` comes from
replacing the a.e. measurable Cartesian source by a measurable representative.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace STI

theorem abs_sub_le_add' (p q : ℝ) : |p - q| ≤ |p| + |q| := by
  rw [abs_le]
  constructor <;> linarith [abs_nonneg p, abs_nonneg q, le_abs_self p, le_abs_self q,
    neg_abs_le p, neg_abs_le q]

theorem sub_abs_bound (a b e : ℝ) (he : 0 ≤ e) : |e * a - e * b| ≤ e * |a| + e * |b| := by
  have h := abs_sub_le_add' (e * a) (e * b)
  rw [abs_mul, abs_mul, abs_of_nonneg he] at h
  exact h

theorem rpow_mul_neg4 (ρ : ℝ) (hρ : 0 < ρ) : ρ * ρ ^ (-(4:ℝ)) = ρ ^ (-(3:ℝ)) := by
  rw [show (-(3:ℝ)) = -(4:ℝ) + 1 by norm_num, Real.rpow_add_one hρ.ne']
  ring

theorem cylR_nonneg (y : Vec3) : 0 ≤ cylR y := Real.sqrt_nonneg _

theorem rayPt_continuous (y : Vec3) : Continuous (fun ρ : ℝ => rayPt y ρ) := by
  unfold rayPt
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

theorem affine3_cont :
    Continuous (fun q : (Vec3 × ℝ) × (ℝ × ℝ) => q.1.1 - q.1.2 • embPlane q.2) :=
  (continuous_fst.comp continuous_fst).sub
    ((continuous_snd.comp continuous_fst).smul (NVA.embPlane_continuous.comp continuous_snd))

/-- The decay of the third Newton derivative, `|∂³N(p)| ≤ C |p|⁻⁴`, with `C ≥ 0`. -/
theorem decay_exists : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ w : Vec3, w ≠ 0 → ∀ i j k : Fin 3,
    |newtonD3 w i j k| ≤ C0 * (Real.sqrt (eucSq w)) ^ (-(4:ℝ)) := by
  obtain ⟨C, hC⟩ := newtonD3_bound 0
  refine ⟨|C|, abs_nonneg _, fun w hw i j k => ?_⟩
  have h := (hC w hw i j k).2
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.cast_zero, sub_zero] at h
  have hs : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4:ℝ)) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hs)

theorem horiz_lower (A R m t p0 p1 x0 x1 : ℝ) (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hm2 : m ^ 2 = x0 ^ 2 + x1 ^ 2) (hmR : m ≤ R) (hAR : R ≤ A) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : p0 ^ 2 + p1 ^ 2 = A ^ 2) :
    (A - R) ^ 2 ≤ (p0 - t * x0) ^ 2 + (p1 - t * x1) ^ 2 := by
  have hsq : (A * m) ^ 2 = (p0 ^ 2 + p1 ^ 2) * (x0 ^ 2 + x1 ^ 2) := by
    rw [mul_pow, ← hp, hm2]
  have hP2 : (p0 * x0 + p1 * x1) ^ 2 ≤ (A * m) ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (p0 * x1 - p1 * x0)]
  have hP : p0 * x0 + p1 * x1 ≤ A * m := by nlinarith [mul_nonneg hA hm]
  have hid : (p0 - t * x0) ^ 2 + (p1 - t * x1) ^ 2
      = A ^ 2 - 2 * t * (p0 * x0 + p1 * x1) + t ^ 2 * m ^ 2 := by
    linear_combination hp - t ^ 2 * hm2
  have hA2 : (A - t * m) ^ 2 ≤ A ^ 2 - 2 * t * (p0 * x0 + p1 * x1) + t ^ 2 * m ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hP ht0]
  have htm : t * m ≤ m := mul_le_of_le_one_left hm ht1
  have hTm : (A - R) ^ 2 ≤ (A - t * m) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.2 hAR) (by linarith) 2
  rw [hid]
  linarith

/-- Kernel bound on the moving disk, with the horizontal norm `A` of `w` large compared to the
disk radius `R`. -/
theorem kernel_bound (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hdec : ∀ w : Vec3, w ≠ 0 → ∀ i j k : Fin 3,
      |newtonD3 w i j k| ≤ C0 * (Real.sqrt (eucSq w)) ^ (-(4:ℝ)))
    (w : Vec3) (A R θ : ℝ) (hθ : 0 < θ) (hA : 0 < A) (hR0 : 0 ≤ R)
    (hwA : w 0 ^ 2 + w 1 ^ 2 = A ^ 2) (hRA : R ≤ (1 - θ) * A)
    (i j k : Fin 3) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x' : ℝ × ℝ)
    (hx' : x'.1 ^ 2 + x'.2 ^ 2 ≤ R ^ 2) :
    |newtonD3 (w - t • embPlane x') i j k| ≤ C0 * (θ * A) ^ (-(4:ℝ)) := by
  have hθA : 0 < θ * A := mul_pos hθ hA
  have hAR : R ≤ A := by nlinarith [hθA]
  have hm : Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) ≤ R := by
    have := Real.sqrt_le_sqrt hx'
    rwa [Real.sqrt_sq hR0] at this
  have hm2 : (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) ^ 2 = x'.1 ^ 2 + x'.2 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hL := horiz_lower A R (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) t (w 0) (w 1) x'.1 x'.2 hA.le
    (Real.sqrt_nonneg _) hm2 hm hAR ht0 ht1 hwA
  have hsq : (θ * A) ^ 2 ≤ (A - R) ^ 2 := pow_le_pow_left₀ hθA.le (by nlinarith [hRA]) 2
  have hE : eucSq (w - t • embPlane x')
      = (w 0 - t * x'.1) ^ 2 + (w 1 - t * x'.2) ^ 2 + w 2 ^ 2 := by
    simp [eucSq, Fin.sum_univ_three, embPlane]
  have hEuc : (θ * A) ^ 2 ≤ eucSq (w - t • embPlane x') := by
    rw [hE]
    nlinarith [sq_nonneg (w 2)]
  have hne : w - t • embPlane x' ≠ 0 := by
    intro h
    have h0 : eucSq (w - t • embPlane x') = 0 := by
      rw [h]
      simp [eucSq]
    have : 0 < (θ * A) ^ 2 := pow_pos hθA 2
    linarith
  have hsqrt : θ * A ≤ Real.sqrt (eucSq (w - t • embPlane x')) := by
    rw [← Real.sqrt_sq hθA.le]
    exact Real.sqrt_le_sqrt hEuc
  have hpow : (Real.sqrt (eucSq (w - t • embPlane x'))) ^ (-(4:ℝ)) ≤ (θ * A) ^ (-(4:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hθA hsqrt (by norm_num)
  exact (hdec _ hne i j k).trans (mul_le_mul_of_nonneg_left hpow hC0)

theorem W_norm (ε ρ : ℝ) (y : Vec3) (ha : cylR y ≠ 0) :
    (ε • rayPt y ρ) 0 ^ 2 + (ε • rayPt y ρ) 1 ^ 2 = (ε * ρ) ^ 2 := by
  have e0 : (ε • rayPt y ρ) 0 = ε * (ρ * (y 0 / cylR y)) := by simp [rayPt]
  have e1 : (ε • rayPt y ρ) 1 = ε * (ρ * (y 1 / cylR y)) := by simp [rayPt]
  rw [e0, e1]
  calc (ε * (ρ * (y 0 / cylR y))) ^ 2 + (ε * (ρ * (y 1 / cylR y))) ^ 2
      = (ε * ρ) ^ 2 * ((y 0 ^ 2 + y 1 ^ 2) / cylR y ^ 2) := by ring
    _ = (ε * ρ) ^ 2 * (cylR y ^ 2 / cylR y ^ 2) := by rw [cylR_sq y]
    _ = (ε * ρ) ^ 2 := by rw [div_self (pow_ne_zero 2 ha), mul_one]

/-- Uniform bound on the zero-width Newton field along a ray point with horizontal norm `A`. -/
theorem V_bound (c ν μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) (hμ : 0 < μ)
    (hσ : ∀ j k, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k))
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hdec : ∀ w : Vec3, w ≠ 0 → ∀ i j k : Fin 3,
      |newtonD3 w i j k| ≤ C0 * (Real.sqrt (eucSq w)) ^ (-(4:ℝ)))
    (w : Vec3) (A R θ : ℝ) (hθ : 0 < θ) (hA : 0 < A) (hR0 : 0 ≤ R) (hR2 : R ^ 2 = 5 * ν / 6)
    (hwA : w 0 ^ 2 + w 1 ^ 2 = A ^ 2) (hRA : R ≤ (1 - θ) * A) :
    |newtonV c ν μ χo M w 2| ≤
      2 * (C0 * (θ * A) ^ (-(4:ℝ))) * ∫ x' : ℝ × ℝ, ∑ j, ∑ k, ‖sigmaM c ν χo M x' j k‖ := by
  have hI : ∀ t ∈ Ioc (0:ℝ) 1, ‖∫ x', NVA.innerF c ν χo M 2 w t x'‖ ≤
      C0 * (θ * A) ^ (-(4:ℝ)) * ∫ x' : ℝ × ℝ, ∑ j, ∑ k, ‖sigmaM c ν χo M x' j k‖ := by
    intro t ht
    have hg : Integrable (fun x' : ℝ × ℝ =>
        C0 * (θ * A) ^ (-(4:ℝ)) * ∑ j, ∑ k, ‖sigmaM c ν χo M x' j k‖) :=
      (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hσ j k).norm).const_mul _
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun x' => ?_)
    show ‖∑ j, ∑ k, newtonD3 (w - t • embPlane x') 2 j k * sigmaM c ν χo M x' j k‖ ≤
      C0 * (θ * A) ^ (-(4:ℝ)) * ∑ j, ∑ k, ‖sigmaM c ν χo M x' j k‖
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    simp only [Real.norm_eq_abs]
    exact NVA.term_bound c ν hχo hν M w t 2 j k _
      (fun x'' hx'' => kernel_bound C0 hC0 hdec w A R θ hθ hA hR0 hwA hRA 2 j k t ht.1.le ht.2 x''
        (by rw [hR2]; exact hx'')) x'
  have hvol : volume.real (Ioc (0:ℝ) 1) = 1 := by simp
  have hJ : ‖∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) * ∫ x', NVA.innerF c ν χo M 2 w t x'‖ ≤
      (C0 * (θ * A) ^ (-(4:ℝ)) * ∫ x' : ℝ × ℝ, ∑ j, ∑ k, ‖sigmaM c ν χo M x' j k‖) *
        volume.real (Ioc (0:ℝ) 1) := by
    refine norm_setIntegral_le_of_norm_le_const (by simp) (fun t ht => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    have h1 : t ^ (2 * μ + 2) ≤ 1 := Real.rpow_le_one ht.1.le ht.2 (by linarith)
    calc t ^ (2 * μ + 2) * ‖∫ x', NVA.innerF c ν χo M 2 w t x'‖
        ≤ 1 * ‖∫ x', NVA.innerF c ν χo M 2 w t x'‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖∫ x', NVA.innerF c ν χo M 2 w t x'‖ := one_mul _
      _ ≤ _ := hI t ht
  have habs : |(-2:ℝ) * ∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) * ∫ x', NVA.innerF c ν χo M 2 w t x'|
      = 2 * ‖∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) * ∫ x', NVA.innerF c ν χo M 2 w t x'‖ := by
    rw [abs_mul, Real.norm_eq_abs]
    norm_num
  rw [NVA.newtonV_eq, habs, hvol, mul_one] at *
  linarith [hJ]

/-- The zero-width Newton field, third component, is measurable in the point `w`. -/
theorem V_measurable (c ν μ : ℝ) {χo : ℝ → ℝ} (M : Chart → Mat3)
    (hσ : ∀ j k, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k)) :
    Measurable (fun w : Vec3 => newtonV c ν μ χo M w 2) := by
  obtain ⟨g, hgm, hgae⟩ : ∃ g : Fin 3 → Fin 3 → ℝ × ℝ → ℝ,
      (∀ j k, StronglyMeasurable (g j k)) ∧
        ∀ j k, (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k) =ᵐ[volume] g j k :=
    ⟨fun j k => (hσ j k).aestronglyMeasurable.mk (fun x' => sigmaM c ν χo M x' j k),
      fun j k => (hσ j k).aestronglyMeasurable.stronglyMeasurable_mk,
      fun j k => (hσ j k).aestronglyMeasurable.ae_eq_mk⟩
  have hae : ∀ᵐ x' ∂(volume : Measure (ℝ × ℝ)), ∀ j k, sigmaM c ν χo M x' j k = g j k x' := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    exact hgae j k
  have hIg : ∀ (w : Vec3) (t : ℝ), ∫ x', NVA.innerF c ν χo M 2 w t x' =
      ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (w - t • embPlane x') 2 j k * g j k x' := by
    intro w t
    apply integral_congr_ae
    filter_upwards [hae] with x' hx'
    simp only [NVA.innerF, hx']
  have hVg : (fun w : Vec3 => newtonV c ν μ χo M w 2) = fun w : Vec3 =>
      -2 * ∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) *
        ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (w - t • embPlane x') 2 j k * g j k x' := by
    funext w
    rw [NVA.newtonV_eq]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [hIg]
  rw [hVg]
  have H1m : Measurable (fun q : (Vec3 × ℝ) × (ℝ × ℝ) =>
      ∑ j, ∑ k, newtonD3 (q.1.1 - q.1.2 • embPlane q.2) 2 j k * g j k q.2) := by
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
    exact ((NVA.newtonD3_measurable 2 j k).comp affine3_cont.measurable).mul
      ((hgm j k).measurable.comp measurable_snd)
  have I1 : StronglyMeasurable (fun q' : Vec3 × ℝ =>
      ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (q'.1 - q'.2 • embPlane x') 2 j k * g j k x') :=
    StronglyMeasurable.integral_prod_right' (ν := (volume : Measure (ℝ × ℝ)))
      (f := fun q : (Vec3 × ℝ) × (ℝ × ℝ) =>
        ∑ j, ∑ k, newtonD3 (q.1.1 - q.1.2 • embPlane q.2) 2 j k * g j k q.2) H1m.stronglyMeasurable
  have F2 : StronglyMeasurable (fun q' : Vec3 × ℝ => q'.2 ^ (2 * μ + 2) *
      ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (q'.1 - q'.2 • embPlane x') 2 j k * g j k x') :=
    (measurable_snd.pow_const _).stronglyMeasurable.mul I1
  have V1 : StronglyMeasurable (fun w : Vec3 => ∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) *
      ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (w - t • embPlane x') 2 j k * g j k x') :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) 1))
      (f := fun q' : Vec3 × ℝ => q'.2 ^ (2 * μ + 2) *
        ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (q'.1 - q'.2 • embPlane x') 2 j k * g j k x') F2
  exact (V1.const_mul (-2)).measurable

end STI

end UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.Concrete STI in
theorem streamTail_int : UnforcedLeray.Short.PartIIIb.Concrete.StreamTailInt := by
  intro c ν ε μ χo hc hν hε hμ hχo M hM y hy
  have hσ : ∀ j k, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k) :=
    fun j k => sigmaM_integrable c ν χo hc hν hχo M hM j k
  obtain ⟨C0, hC0, hdec⟩ := STI.decay_exists
  have ha : 0 < cylR y := by
    by_contra h
    rw [not_lt] at h
    have h0 : cylR y = 0 := le_antisymm h (cylR_nonneg y)
    rw [h0] at hy
    have : (ε * 0) ^ 2 = (0:ℝ) := by ring
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = Real.sqrt (5 * ν / 6) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 5 * ν / 6 := by rw [hRdef]; exact Real.sq_sqrt (by linarith)
  have hεa : 0 < ε * cylR y := mul_pos hε ha
  have hRa : R < ε * cylR y := by
    have h := Real.sqrt_lt_sqrt (by linarith) hy
    rw [Real.sqrt_sq hεa.le] at h
    rw [hRdef]
    exact h
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = 1 - R / (ε * cylR y) := ⟨_, rfl⟩
  have hθ : 0 < θ := by
    have h1 : R / (ε * cylR y) < 1 := (div_lt_one hεa).2 hRa
    rw [hθdef]
    linarith
  have hR1θ : 1 - θ = R / (ε * cylR y) := by rw [hθdef]; ring
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∫ x' : ℝ × ℝ, ∑ j, ∑ k, ‖sigmaM c ν χo M x' j k‖ := ⟨_, rfl⟩
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, Kb = 2 * C0 * (θ * ε) ^ (-(4:ℝ)) * G := ⟨_, rfl⟩
  -- uniform decay of the zero-width field along the ray
  have hdecay : ∀ ρ : ℝ, cylR y < ρ → ∀ μ' : ℝ, 0 < μ' →
      |newtonV c ν μ' χo M (ε • rayPt y ρ) 2| ≤ Kb * ρ ^ (-(4:ℝ)) := by
    intro ρ hρ μ' hμ'
    have hρ0 : 0 < ρ := lt_trans ha hρ
    have hwA := W_norm ε ρ y ha.ne'
    have hRA : R ≤ (1 - θ) * (ε * ρ) := by
      rw [hR1θ]
      have e : R / (ε * cylR y) * (ε * ρ) = R * (ρ / cylR y) := by
        field_simp
      rw [e]
      exact le_mul_of_one_le_right hR0 ((one_le_div ha).2 hρ.le)
    have hV := V_bound c ν μ' hχo hν M hμ' hσ C0 hC0 hdec (ε • rayPt y ρ) (ε * ρ) R θ hθ
      (mul_pos hε hρ0) hR0 hR2 hwA hRA
    rw [← hG] at hV
    refine hV.trans (le_of_eq ?_)
    rw [hKb, show θ * (ε * ρ) = (θ * ε) * ρ by ring,
      Real.mul_rpow (mul_pos hθ hε).le hρ0.le]
    ring
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = 2 * ε ^ 2 * Kb := ⟨_, rfl⟩
  have hfeq : ∀ ρ : ℝ, (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (rayPt y ρ) 2 =
      ε ^ 2 * newtonV c ν μ χo M (ε • rayPt y ρ) 2 -
        ε ^ 2 * newtonV c ν (μ + 1) χo M (ε • rayPt y ρ) 2 := by
    intro ρ
    simp only [youngW, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hVμ : Measurable (fun w : Vec3 => newtonV c ν μ χo M w 2) :=
    V_measurable c ν μ M hσ
  have hVμ1 : Measurable (fun w : Vec3 => newtonV c ν (μ + 1) χo M w 2) :=
    V_measurable c ν (μ + 1) M hσ
  have hpath : Measurable (fun ρ : ℝ => ε • rayPt y ρ) :=
    (Continuous.const_smul (rayPt_continuous y) ε).measurable
  have hmeas : Measurable (fun ρ : ℝ =>
      ρ * (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (rayPt y ρ) 2) := by
    have e : (fun ρ : ℝ => ρ * (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (rayPt y ρ) 2)
        = fun ρ : ℝ => ρ * (ε ^ 2 * newtonV c ν μ χo M (ε • rayPt y ρ) 2 -
            ε ^ 2 * newtonV c ν (μ + 1) χo M (ε • rayPt y ρ) 2) := by
      funext ρ
      rw [hfeq ρ]
    rw [e]
    exact measurable_id.mul (((hVμ.comp hpath).const_mul _).sub ((hVμ1.comp hpath).const_mul _))
  have hfin : Integrable (fun ρ : ℝ => K1 * ρ ^ (-(3:ℝ))) (volume.restrict (Ioi (cylR y))) :=
    Integrable.const_mul
      (integrableOn_Ioi_rpow_of_lt (a := -(3:ℝ)) (by norm_num) ha) K1
  show Integrable (fun ρ : ℝ =>
      ρ * (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (rayPt y ρ) 2)
    (volume.restrict (Ioi (cylR y)))
  refine Integrable.mono' hfin hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun ρ hρ => ?_)
  show ‖ρ * (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (rayPt y ρ) 2‖ ≤
    K1 * ρ ^ (-(3:ℝ))
  have hρpos : 0 < ρ := lt_trans ha hρ
  have hb1 := hdecay ρ hρ μ hμ
  have hb2 := hdecay ρ hρ (μ + 1) (by linarith)
  rw [Real.norm_eq_abs, hfeq ρ]
  calc |ρ * (ε ^ 2 * newtonV c ν μ χo M (ε • rayPt y ρ) 2 -
        ε ^ 2 * newtonV c ν (μ + 1) χo M (ε • rayPt y ρ) 2)|
      = ρ * |ε ^ 2 * newtonV c ν μ χo M (ε • rayPt y ρ) 2 -
          ε ^ 2 * newtonV c ν (μ + 1) χo M (ε • rayPt y ρ) 2| := by
        rw [abs_mul, abs_of_pos hρpos]
    _ ≤ ρ * (ε ^ 2 * |newtonV c ν μ χo M (ε • rayPt y ρ) 2| +
          ε ^ 2 * |newtonV c ν (μ + 1) χo M (ε • rayPt y ρ) 2|) :=
        mul_le_mul_of_nonneg_left (sub_abs_bound _ _ _ (sq_nonneg ε)) hρpos.le
    _ ≤ ρ * (ε ^ 2 * (Kb * ρ ^ (-(4:ℝ))) + ε ^ 2 * (Kb * ρ ^ (-(4:ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hb1 (sq_nonneg ε))
            (mul_le_mul_of_nonneg_left hb2 (sq_nonneg ε))) hρpos.le
    _ = K1 * ρ ^ (-(3:ℝ)) := by
        rw [← rpow_mul_neg4 ρ hρpos, hK1]
        ring
