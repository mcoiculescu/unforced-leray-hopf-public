import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rpow_neg_nat_eq {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ (-((n : ℕ) : ℝ)) = (x ^ n)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_natCast]

theorem integrableOn_inv_pow_Ioi {r : ℝ} (hr : 0 < r) (n : ℕ) (hn : 2 ≤ n) :
    IntegrableOn (fun ρ : ℝ => (ρ ^ n)⁻¹) (Ioi r) := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := integrableOn_Ioi_rpow_of_lt (a := -((n : ℕ) : ℝ)) (c := r) (by linarith) hr
  exact h.congr_fun (fun ρ hρ => rpow_neg_nat_eq (lt_trans hr hρ) n) measurableSet_Ioi

theorem pw_five (ρ W C : ℝ) (hρ : 0 < ρ) (hW : ρ / 2 ≤ W) :
    ρ * (|C| * (W ^ 5)⁻¹) ≤ 32 * |C| * (ρ ^ 4)⁻¹ := by
  have hne : ρ ≠ 0 := hρ.ne'
  have hW0 : 0 < ρ / 2 := by positivity
  have h1 : (W ^ 5)⁻¹ ≤ ((ρ / 2) ^ 5)⁻¹ := inv_anti₀ (pow_pos hW0 5) (pow_le_pow_left₀ hW0.le hW 5)
  have h2 : ((ρ / 2) ^ 5)⁻¹ = 32 * (ρ ^ 5)⁻¹ := by
    field_simp
    norm_num
  have h3 : ρ * (ρ ^ 5)⁻¹ = (ρ ^ 4)⁻¹ := by
    field_simp
  have hC : 0 ≤ |C| := abs_nonneg C
  calc ρ * (|C| * (W ^ 5)⁻¹) ≤ ρ * (|C| * (32 * (ρ ^ 5)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h1.trans h2.le) hC) hρ.le
    _ = 32 * |C| * (ρ ^ 4)⁻¹ := by rw [← h3]; ring

theorem pw_four (ρ W C : ℝ) (hρ : 0 < ρ) (hW : ρ / 2 ≤ W) :
    ρ * (|C| * (W ^ 4)⁻¹) ≤ 16 * |C| * (ρ ^ 3)⁻¹ := by
  have hne : ρ ≠ 0 := hρ.ne'
  have hW0 : 0 < ρ / 2 := by positivity
  have h1 : (W ^ 4)⁻¹ ≤ ((ρ / 2) ^ 4)⁻¹ := inv_anti₀ (pow_pos hW0 4) (pow_le_pow_left₀ hW0.le hW 4)
  have h2 : ((ρ / 2) ^ 4)⁻¹ = 16 * (ρ ^ 4)⁻¹ := by
    field_simp
    norm_num
  have h3 : ρ * (ρ ^ 4)⁻¹ = (ρ ^ 3)⁻¹ := by
    field_simp
  have hC : 0 ≤ |C| := abs_nonneg C
  calc ρ * (|C| * (W ^ 4)⁻¹) ≤ ρ * (|C| * (16 * (ρ ^ 4)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h1.trans h2.le) hC) hρ.le
    _ = 16 * |C| * (ρ ^ 3)⁻¹ := by rw [← h3]; ring

theorem norm_le_of_sq_cylR (w : Vec3) (ρ : ℝ) (hρ : 0 ≤ ρ) (hc : cylR w = ρ) :
    ρ ≤ 2 * ‖w‖ := by
  have hsq : cylR w ^ 2 = w 0 ^ 2 + w 1 ^ 2 := cylR_sq_sum w
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  have h0 : |w 0| ≤ ‖w‖ := by
    have := norm_le_pi_norm (f := w) 0
    simpa [Real.norm_eq_abs] using this
  have h1 : |w 1| ≤ ‖w‖ := by
    have := norm_le_pi_norm (f := w) 1
    simpa [Real.norm_eq_abs] using this
  have hA : |w 0| * |w 0| ≤ ‖w‖ * ‖w‖ := mul_le_mul h0 h0 (abs_nonneg _) hn
  have hB : |w 1| * |w 1| ≤ ‖w‖ * ‖w‖ := mul_le_mul h1 h1 (abs_nonneg _) hn
  have hA' : w 0 ^ 2 = |w 0| * |w 0| := by rw [← sq_abs (w 0)]; ring
  have hB' : w 1 ^ 2 = |w 1| * |w 1| := by rw [← sq_abs (w 1)]; ring
  have hρ2 : ρ ^ 2 ≤ 2 * ‖w‖ * ‖w‖ := by
    rw [← hc, hsq, hA', hB']
    nlinarith
  nlinarith

theorem norm_le_pi_two (v : Vec3) : ‖v 2‖ ≤ ‖v‖ := norm_le_pi_norm (f := v) 2

theorem streamPsiDzInt : StreamPsiDzInt := by
  intro b Z hb hZs hdec y hy
  have hr : 0 < cylR y := cylR_pos_of_lt hb hy
  obtain ⟨e, he⟩ : ∃ e : Vec3, e = Pi.single 2 1 := ⟨_, rfl⟩
  rw [← he]
  have he0 : e 0 = 0 := by rw [he]; simp
  have he1 : e 1 = 0 := by rw [he]; simp
  have he2 : e 2 = 1 := by rw [he]; simp
  have hene : ‖e‖ ≤ 1 := by
    rw [he]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    by_cases hi : i = 2
    · subst hi; simp
    · simp [hi]
  -- translation along the axis
  have hcy : ∀ t : ℝ, cylR (y + t • e) = cylR y := by
    intro t
    unfold cylR
    congr 1
    simp [he0, he1]
  have hrt : ∀ t ρ : ℝ, rayPt (y + t • e) ρ = rayPt y ρ + t • e := by
    intro t ρ
    funext i
    fin_cases i
    · simp [rayPt, hcy t, he0]
    · simp [rayPt, hcy t, he1]
    · simp [rayPt, he2]
  have hpos : ∀ t : ℝ, 0 < cylR (y + t • e) := fun t => by rw [hcy t]; exact hr
  have hcylw : ∀ (t ρ : ℝ), 0 < ρ → cylR (rayPt y ρ + t • e) = ρ := by
    intro t ρ hρ
    rw [← hrt, cylR_rayPt _ _ (hpos t), abs_of_pos hρ]
  have hmem : ∀ (t ρ : ℝ), cylR y < ρ → b < cylR (rayPt y ρ + t • e) ^ 2 := by
    intro t ρ hρ
    rw [hcylw t ρ (lt_trans hr hρ)]
    nlinarith
  -- continuity and differentiability
  have hZc : ContinuousOn Z {w : Vec3 | b < cylR w ^ 2} := hZs.continuousOn
  have hZdiff : ∀ w : Vec3, b < cylR w ^ 2 → DifferentiableAt ℝ Z w := fun w hw =>
    (hZs.contDiffAt ((isOpen_cylSq b).mem_nhds hw)).differentiableAt (by simp)
  have hDc : ContinuousOn (fderiv ℝ Z) {w : Vec3 | b < cylR w ^ 2} :=
    hZs.continuousOn_fderiv_of_isOpen (isOpen_cylSq b) (by simp)
  have hrc : Continuous (rayPt y) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [rayPt] <;> fun_prop
  have hshift : ∀ t : ℝ, Continuous (fun ρ : ℝ => rayPt y ρ + t • e) := fun t =>
    hrc.add continuous_const
  have hmapsto : ∀ t : ℝ, MapsTo (fun ρ : ℝ => rayPt y ρ + t • e) (Ioi (cylR y))
      {w : Vec3 | b < cylR w ^ 2} := fun t ρ hρ => hmem t ρ hρ
  have hFc : ∀ t : ℝ, ContinuousOn (fun ρ : ℝ => ρ * Z (rayPt y ρ + t • e) 2) (Ioi (cylR y)) := by
    intro t
    have h1 : ContinuousOn (fun ρ : ℝ => Z (rayPt y ρ + t • e)) (Ioi (cylR y)) :=
      hZc.comp (hshift t).continuousOn (hmapsto t)
    exact continuousOn_id.mul ((continuous_apply 2).comp_continuousOn h1)
  have hGc : ∀ t : ℝ, ContinuousOn
      (fun ρ : ℝ => ρ * fderiv ℝ Z (rayPt y ρ + t • e) e 2) (Ioi (cylR y)) := by
    intro t
    have h1 : ContinuousOn (fun ρ : ℝ => fderiv ℝ Z (rayPt y ρ + t • e)) (Ioi (cylR y)) :=
      hDc.comp (hshift t).continuousOn (hmapsto t)
    have h2 : ContinuousOn (fun ρ : ℝ => fderiv ℝ Z (rayPt y ρ + t • e) e 2) (Ioi (cylR y)) :=
      ((continuous_apply 2).comp (ContinuousLinearMap.apply ℝ Vec3 e).continuous).comp_continuousOn h1
    exact continuousOn_id.mul h2
  -- derivative in the translation parameter
  have hder : ∀ (ρ : ℝ), cylR y < ρ → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => ρ * Z (rayPt y ρ + s • e) 2)
        (ρ * fderiv ℝ Z (rayPt y ρ + t • e) e 2) t := by
    intro ρ hρ t
    have hl : HasDerivAt (fun s : ℝ => rayPt y ρ + s • e) e t := by
      have h := ((hasDerivAt_id' t).smul_const e).const_add (rayPt y ρ)
      exact h.congr_deriv (one_smul ℝ e)
    have hZw : HasFDerivAt Z (fderiv ℝ Z (rayPt y ρ + t • e)) (rayPt y ρ + t • e) :=
      (hZdiff _ (hmem t ρ hρ)).hasFDerivAt
    have hc : HasDerivAt (fun s : ℝ => Z (rayPt y ρ + s • e))
        (fderiv ℝ Z (rayPt y ρ + t • e) e) t :=
      hZw.comp_hasDerivAt t hl
    exact (hasDerivAt_pi.1 hc 2).const_mul ρ
  -- decay bounds
  obtain ⟨C0, hC0⟩ := hdec (cylR y ^ 2) hy 0
  obtain ⟨C1, hC1⟩ := hdec (cylR y ^ 2) hy 1
  have hbd1 : ∀ (ρ : ℝ), cylR y < ρ → ∀ t : ℝ,
      ‖ρ * fderiv ℝ Z (rayPt y ρ + t • e) e 2‖ ≤ 32 * |C1| * (ρ ^ 4)⁻¹ := by
    intro ρ hρ t
    have hρ0 : 0 < ρ := lt_trans hr hρ
    have hcw : cylR y ^ 2 ≤ cylR (rayPt y ρ + t • e) ^ 2 := by
      rw [hcylw t ρ hρ0]
      nlinarith
    have hd := hC1 _ hcw
    rw [norm_iteratedFDeriv_one] at hd
    have hW0 : 0 < 1 + ‖rayPt y ρ + t • e‖ := by positivity
    have hWn : ρ / 2 ≤ 1 + ‖rayPt y ρ + t • e‖ := by
      have := norm_le_of_sq_cylR (rayPt y ρ + t • e) ρ hρ0.le (hcylw t ρ hρ0)
      linarith
    rw [show (-(4 + ((1 : ℕ) : ℝ))) = -((5 : ℕ) : ℝ) by norm_num, rpow_neg_nat_eq hW0] at hd
    have hX : 0 ≤ ((1 + ‖rayPt y ρ + t • e‖) ^ 5)⁻¹ := by positivity
    have hcomp : ‖fderiv ℝ Z (rayPt y ρ + t • e) e 2‖ ≤ ‖fderiv ℝ Z (rayPt y ρ + t • e)‖ := by
      calc ‖fderiv ℝ Z (rayPt y ρ + t • e) e 2‖ ≤ ‖fderiv ℝ Z (rayPt y ρ + t • e) e‖ :=
            norm_le_pi_two _
        _ ≤ ‖fderiv ℝ Z (rayPt y ρ + t • e)‖ * ‖e‖ :=
            (fderiv ℝ Z (rayPt y ρ + t • e)).le_opNorm e
        _ ≤ ‖fderiv ℝ Z (rayPt y ρ + t • e)‖ * 1 :=
            mul_le_mul_of_nonneg_left hene (norm_nonneg _)
        _ = ‖fderiv ℝ Z (rayPt y ρ + t • e)‖ := mul_one _
    have hC1abs : ‖fderiv ℝ Z (rayPt y ρ + t • e)‖ ≤ |C1| * ((1 + ‖rayPt y ρ + t • e‖) ^ 5)⁻¹ :=
      hd.trans (mul_le_mul_of_nonneg_right (le_abs_self C1) hX)
    have hnorm : ‖ρ * fderiv ℝ Z (rayPt y ρ + t • e) e 2‖
        = ρ * ‖fderiv ℝ Z (rayPt y ρ + t • e) e 2‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hρ0]
    rw [hnorm]
    calc ρ * ‖fderiv ℝ Z (rayPt y ρ + t • e) e 2‖
        ≤ ρ * (|C1| * ((1 + ‖rayPt y ρ + t • e‖) ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_left (hcomp.trans hC1abs) hρ0.le
      _ ≤ 32 * |C1| * (ρ ^ 4)⁻¹ := pw_five ρ _ C1 hρ0 hWn
  have hbd0 : ∀ (ρ : ℝ), cylR y < ρ → ∀ t : ℝ,
      ‖ρ * Z (rayPt y ρ + t • e) 2‖ ≤ 16 * |C0| * (ρ ^ 3)⁻¹ := by
    intro ρ hρ t
    have hρ0 : 0 < ρ := lt_trans hr hρ
    have hcw : cylR y ^ 2 ≤ cylR (rayPt y ρ + t • e) ^ 2 := by
      rw [hcylw t ρ hρ0]
      nlinarith
    have hd := hC0 _ hcw
    rw [norm_iteratedFDeriv_zero] at hd
    have hW0 : 0 < 1 + ‖rayPt y ρ + t • e‖ := by positivity
    have hWn : ρ / 2 ≤ 1 + ‖rayPt y ρ + t • e‖ := by
      have := norm_le_of_sq_cylR (rayPt y ρ + t • e) ρ hρ0.le (hcylw t ρ hρ0)
      linarith
    rw [show (-(4 + ((0 : ℕ) : ℝ))) = -((4 : ℕ) : ℝ) by norm_num, rpow_neg_nat_eq hW0] at hd
    have hX : 0 ≤ ((1 + ‖rayPt y ρ + t • e‖) ^ 4)⁻¹ := by positivity
    have hZabs : |Z (rayPt y ρ + t • e) 2| ≤ |C0| * ((1 + ‖rayPt y ρ + t • e‖) ^ 4)⁻¹ := by
      have h2 := norm_le_pi_two (Z (rayPt y ρ + t • e))
      rw [Real.norm_eq_abs] at h2
      exact le_trans (le_trans h2 hd) (mul_le_mul_of_nonneg_right (le_abs_self C0) hX)
    have hnorm : ‖ρ * Z (rayPt y ρ + t • e) 2‖ = ρ * |Z (rayPt y ρ + t • e) 2| := by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hρ0]
    rw [hnorm]
    calc ρ * |Z (rayPt y ρ + t • e) 2| ≤ ρ * (|C0| * ((1 + ‖rayPt y ρ + t • e‖) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left hZabs hρ0.le
      _ ≤ 16 * |C0| * (ρ ^ 3)⁻¹ := pw_four ρ _ C0 hρ0 hWn
  -- differentiation under the integral
  have hFm : ∀ t : ℝ, AEStronglyMeasurable (fun ρ : ℝ => ρ * Z (rayPt y ρ + t • e) 2)
      (volume.restrict (Ioi (cylR y))) :=
    fun t => (hFc t).aestronglyMeasurable measurableSet_Ioi
  have hbi : Integrable (fun ρ : ℝ => 32 * |C1| * (ρ ^ 4)⁻¹) (volume.restrict (Ioi (cylR y))) :=
    (integrableOn_inv_pow_Ioi hr 4 (by norm_num)).const_mul (32 * |C1|)
  have hbi0 : Integrable (fun ρ : ℝ => 16 * |C0| * (ρ ^ 3)⁻¹) (volume.restrict (Ioi (cylR y))) :=
    (integrableOn_inv_pow_Ioi hr 3 (by norm_num)).const_mul (16 * |C0|)
  have hF0int : Integrable (fun ρ : ℝ => ρ * Z (rayPt y ρ + (0 : ℝ) • e) 2)
      (volume.restrict (Ioi (cylR y))) := by
    refine Integrable.mono' hbi0 (hFm 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    exact hbd0 ρ hρ 0
  have hIlem := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (cylR y)))
    (F := fun t ρ => ρ * Z (rayPt y ρ + t • e) 2)
    (F' := fun t ρ => ρ * fderiv ℝ Z (rayPt y ρ + t • e) e 2)
    (x₀ := (0 : ℝ)) (s := univ) (bound := fun ρ : ℝ => 32 * |C1| * (ρ ^ 4)⁻¹)
    univ_mem
    (Eventually.of_forall fun t => hFm t)
    hF0int
    ((hGc 0).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      intro t _
      exact hbd1 ρ hρ t)
    hbi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      intro t _
      exact hder ρ hρ t)
  obtain ⟨hint, hderiv⟩ := hIlem
  -- identify the outward primitive along the axis
  have hΦ : ∀ s : ℝ, streamPsi Z (y + s • e) = -∫ ρ in Ioi (cylR y), ρ * Z (rayPt y ρ + s • e) 2 := by
    intro s
    unfold streamPsi
    rw [hcy s]
    simp only [hrt s]
  have hΨ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (streamPsi Z) {w : Vec3 | b < cylR w ^ 2} :=
    xsStreamPsi b Z hb hZs hdec
  have hΨd : DifferentiableAt ℝ (streamPsi Z) y :=
    (hΨ.contDiffAt ((isOpen_cylSq b).mem_nhds hy)).differentiableAt (by simp)
  have hf' : HasFDerivAt (streamPsi Z) (fderiv ℝ (streamPsi Z) y) (y + (0 : ℝ) • e) := by
    rw [zero_smul, add_zero]
    exact hΨd.hasFDerivAt
  have hline0 : HasDerivAt (fun s : ℝ => y + s • e) e 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).smul_const e).const_add y
    exact h.congr_deriv (one_smul ℝ e)
  have hD0 := hf'.comp_hasDerivAt (0 : ℝ) hline0
  have hD : HasDerivAt (fun s : ℝ => streamPsi Z (y + s • e)) (fderiv ℝ (streamPsi Z) y e) 0 :=
    hD0
  have hfun : (fun s : ℝ => streamPsi Z (y + s • e)) =
      (fun s : ℝ => -∫ ρ in Ioi (cylR y), ρ * Z (rayPt y ρ + s • e) 2) := funext hΦ
  rw [hfun] at hD
  have hI := hderiv.neg
  have huniq := hD.unique hI
  simp only [zero_smul, add_zero] at huniq hint
  exact ⟨hint, huniq⟩

end UnforcedLeray.Short.PartIIIb.Concrete
