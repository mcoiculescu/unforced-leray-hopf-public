import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYDiff.Comm

/-!
# `PartIII-b:C/rep/2/7`, derivative bounds for the cutoff coefficients

Source `the November 2 reference manuscript` 3684-3712, 4203-4214.
The coefficients `A₁, A₂, B₁, B₂` of the commutator `tcComm` are smooth in `r`; on the transition
annulus `L ≤ r ≤ 2L` (`L = R√ν`) their derivatives are bounded by `C L⁻¹, C L⁻², C L⁻³, C L⁻¹`.
Scaling: `c(r) = c₁(r/L)`, `F(r) = L⁻² f₁(r/L)` with `c₁ = tcC0 1 1 χ`, `f₁ = tcF0 1 1 χ`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma wgyc_dscale (g : ℝ → ℝ) (s : ℝ) :
    deriv (fun r => g (s * r)) = fun r => s * deriv g (s * r) := by
  funext r
  simpa using deriv_comp_mul_left (c := s) (f := g) (x := r)

lemma wgyc_c_scale (ν R : ℝ) (χ : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (hLsq : ν * R ^ 2 = L ^ 2) :
    tcC0 ν R χ = fun r => tcC0 1 1 χ (L⁻¹ * r) := by
  funext r
  unfold tcC0
  congr 1
  by_cases hr : r = 0
  · simp [hr]
  · have : ν * (R ^ 2 / r ^ 2) = L ^ 2 / r ^ 2 := by rw [← hLsq]; ring
    rw [this]; field_simp

lemma wgyc_f_scale (ν R : ℝ) (χ : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (hLsq : ν * R ^ 2 = L ^ 2) :
    tcF0 ν R χ = fun r => (L⁻¹) ^ 2 * tcF0 1 1 χ (L⁻¹ * r) := by
  funext r
  unfold tcF0
  by_cases hr : r = 0
  · simp [hr]
  · have e : ν * (R ^ 2 / r ^ 2) = 1 * (1 ^ 2 / (L⁻¹ * r) ^ 2) := by
      have : ν * (R ^ 2 / r ^ 2) = L ^ 2 / r ^ 2 := by rw [← hLsq]; ring
      rw [this]; field_simp
    rw [e]
    have e2 : -2 * ν * R ^ 2 = -2 * L ^ 2 := by rw [mul_assoc, hLsq]
    rw [e2]
    field_simp

lemma wgyc_d1 (c : ℝ → ℝ) (c1 : ℝ → ℝ) (s : ℝ) (h : c = fun r => c1 (s * r)) :
    deriv c = fun r => s * deriv c1 (s * r) := by
  rw [h]; exact wgyc_dscale c1 s

lemma wgyc_d2 (c1 : ℝ → ℝ) (s : ℝ) :
    deriv (fun r => s * deriv c1 (s * r)) = fun r => s * (s * deriv (deriv c1) (s * r)) := by
  funext r
  rw [deriv_const_mul_field', wgyc_dscale (deriv c1) s]

lemma wgyc_d3 (c1 : ℝ → ℝ) (s : ℝ) :
    deriv (fun r => s * (s * deriv (deriv c1) (s * r))) =
      fun r => s * (s * (s * deriv (deriv (deriv c1)) (s * r))) := by
  funext r
  rw [deriv_const_mul_field', deriv_const_mul_field', wgyc_dscale (deriv (deriv c1)) s]

lemma wgyc_bounded (f : ℝ → ℝ) (hf : ContinuousOn f (Ioi 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc (1 : ℝ) 2, |f u| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (hf.mono (fun u hu => lt_of_lt_of_le one_pos hu.1))
  refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
  have := hC u hu
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem wgyc_profile (χ : ℝ → ℝ) (hχ : IsStreamCutoff χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc (1 : ℝ) 2,
      |deriv (tcC0 1 1 χ) u| ≤ M ∧ |deriv (deriv (tcC0 1 1 χ)) u| ≤ M ∧
      |deriv (deriv (deriv (tcC0 1 1 χ))) u| ≤ M ∧
      |tcF0 1 1 χ u| ≤ M ∧ |deriv (tcF0 1 1 χ) u| ≤ M ∧ |deriv (deriv (tcF0 1 1 χ)) u| ≤ M ∧
      |deriv (deriv (deriv (tcF0 1 1 χ))) u| ≤ M := by
  have hc0 := Sub8_1_1_2_3.tcC0_cdOn (ν := 1) (R := 1) hχ
  have hc1 := Sub8_1_1_2_3.cdOn_deriv hc0
  have hc2 := Sub8_1_1_2_3.cdOn_deriv hc1
  have hc3 := Sub8_1_1_2_3.cdOn_deriv hc2
  have hf0 := Sub8_1_1_2_3.tcF0_cdOn (ν := 1) (R := 1) hχ
  have hf1 := Sub8_1_1_2_3.cdOn_deriv hf0
  have hf2 := Sub8_1_1_2_3.cdOn_deriv hf1
  have hf3 := Sub8_1_1_2_3.cdOn_deriv hf2
  have cont : ∀ {f : ℝ → ℝ}, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi 0) →
      ContinuousOn f (Ioi 0) := fun h => h.continuousOn
  obtain ⟨M1, h1, b1⟩ := wgyc_bounded _ (cont hc1)
  obtain ⟨M2, h2, b2⟩ := wgyc_bounded _ (cont hc2)
  obtain ⟨M3, h3, b3⟩ := wgyc_bounded _ (cont hc3)
  obtain ⟨N0, g0, d0⟩ := wgyc_bounded _ (cont hf0)
  obtain ⟨N1, g1, d1⟩ := wgyc_bounded _ (cont hf1)
  obtain ⟨N2, g2, d2⟩ := wgyc_bounded _ (cont hf2)
  obtain ⟨N3, g3, d3⟩ := wgyc_bounded _ (cont hf3)
  refine ⟨M1 + M2 + M3 + N0 + N1 + N2 + N3, by positivity, fun u hu => ?_⟩
  have := b1 u hu; have := b2 u hu; have := b3 u hu
  have := d0 u hu; have := d1 u hu; have := d2 u hu; have := d3 u hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [b1 u hu, b2 u hu, b3 u hu, d0 u hu, d1 u hu,
    d2 u hu, d3 u hu]

/-! ## Algebraic derivative bounds -/

lemma wgyc_pieces (c1 c2 c3 M s ν r : ℝ) (hs : 0 < s) (hM : 0 ≤ M) (h1 : |c1| ≤ M * s)
    (h2 : |c2| ≤ M * s ^ 2) (h3 : |c3| ≤ M * s ^ 3) (hr1 : 1 ≤ s * r) (hr2 : s * r ≤ 2)
    (hν0 : 0 ≤ ν) (hν : ν * s ^ 2 ≤ 1) :
    |r * c2| ≤ 2 * (M * s) ∧ |ν * c3| ≤ M * s ∧ |ν * c2 / r| ≤ M * s ∧
      |ν * c1 / r ^ 2| ≤ M * s := by
  have hr : 0 < r := by
    by_contra h
    push Not at h
    nlinarith
  have hr' : 1 / r ≤ s := by
    rw [div_le_iff₀ hr]; linarith
  have hr'' : 1 / r ^ 2 ≤ s ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hMs : 0 ≤ M * s := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hr]
    calc r * |c2| ≤ r * (M * s ^ 2) := by gcongr
      _ = M * s * (s * r) := by ring
      _ ≤ M * s * 2 := by gcongr
      _ = 2 * (M * s) := by ring
  · rw [abs_mul, abs_of_nonneg hν0]
    calc ν * |c3| ≤ ν * (M * s ^ 3) := by gcongr
      _ = M * s * (ν * s ^ 2) := by ring
      _ ≤ M * s * 1 := by gcongr
      _ = M * s := by ring
  · rw [abs_div, abs_mul, abs_of_nonneg hν0, abs_of_pos hr]
    calc ν * |c2| / r = ν * |c2| * (1 / r) := by ring
      _ ≤ ν * (M * s ^ 2) * s := by gcongr
      _ = M * s * (ν * s ^ 2) := by ring
      _ ≤ M * s * 1 := by gcongr
      _ = M * s := by ring
  · rw [abs_div, abs_mul, abs_of_nonneg hν0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2)]
    calc ν * |c1| / r ^ 2 = ν * |c1| * (1 / r ^ 2) := by ring
      _ ≤ ν * (M * s) * s ^ 2 := by gcongr
      _ = M * s * (ν * s ^ 2) := by ring
      _ ≤ M * s * 1 := by gcongr
      _ = M * s := by ring

lemma wgyc_A1_bound (c1 c2 c3 M s ν r : ℝ) (hs : 0 < s) (hM : 0 ≤ M) (h1 : |c1| ≤ M * s)
    (h2 : |c2| ≤ M * s ^ 2) (h3 : |c3| ≤ M * s ^ 3) (hr1 : 1 ≤ s * r) (hr2 : s * r ≤ 2)
    (hν0 : 0 ≤ ν) (hν : ν * s ^ 2 ≤ 1) :
    |-(1 / 2) * c1 - (1 / 2) * r * c2 - ν * (c3 + c2 / r - c1 / r ^ 2)| ≤ 5 * (M * s) := by
  obtain ⟨p2, p3, p4, p5⟩ := wgyc_pieces c1 c2 c3 M s ν r hs hM h1 h2 h3 hr1 hr2 hν0 hν
  have e : -(1 / 2) * c1 - (1 / 2) * r * c2 - ν * (c3 + c2 / r - c1 / r ^ 2) =
      -(1 / 2) * c1 - (1 / 2) * (r * c2) - ν * c3 - ν * c2 / r + ν * c1 / r ^ 2 := by ring
  rw [e]
  have := abs_le.1 h1; have := abs_le.1 p2; have := abs_le.1 p3; have := abs_le.1 p4
  have := abs_le.1 p5
  rw [abs_le]; constructor <;> nlinarith [abs_le.1 h1, abs_le.1 p2, abs_le.1 p3, abs_le.1 p4,
    abs_le.1 p5]

lemma wgyc_B1_bound (f1 f2 f3 M s ν r : ℝ) (hs : 0 < s) (hM : 0 ≤ M) (h1 : |f1| ≤ M * s ^ 3)
    (h2 : |f2| ≤ M * s ^ 4) (h3 : |f3| ≤ M * s ^ 5) (hr1 : 1 ≤ s * r) (hr2 : s * r ≤ 2)
    (hν0 : 0 ≤ ν) (hν : ν * s ^ 2 ≤ 1) :
    |-(1 / 2) * (3 * f1 + r * f2) - ν * (f3 + f2 / r - f1 / r ^ 2)| ≤ 6 * (M * s ^ 3) := by
  have hM' : 0 ≤ M * s ^ 2 := by positivity
  obtain ⟨p2, p3, p4, p5⟩ := wgyc_pieces f1 f2 f3 (M * s ^ 2) s ν r hs hM'
    (by calc |f1| ≤ M * s ^ 3 := h1
          _ = M * s ^ 2 * s := by ring)
    (by calc |f2| ≤ M * s ^ 4 := h2
          _ = M * s ^ 2 * s ^ 2 := by ring)
    (by calc |f3| ≤ M * s ^ 5 := h3
          _ = M * s ^ 2 * s ^ 3 := by ring) hr1 hr2 hν0 hν
  have e : -(1 / 2) * (3 * f1 + r * f2) - ν * (f3 + f2 / r - f1 / r ^ 2) =
      -(3 / 2) * f1 - (1 / 2) * (r * f2) - ν * f3 - ν * f2 / r + ν * f1 / r ^ 2 := by ring
  have q : M * s ^ 2 * s = M * s ^ 3 := by ring
  rw [e]
  rw [q] at p2 p3 p4 p5
  rw [abs_le]; constructor <;> nlinarith [abs_le.1 h1, abs_le.1 p2, abs_le.1 p3, abs_le.1 p4,
    abs_le.1 p5]

lemma wgyc_e1 (k s : ℝ) (g : ℝ → ℝ) :
    deriv (fun r => k * g (s * r)) = fun r => k * (s * deriv g (s * r)) := by
  funext r
  rw [deriv_const_mul_field', wgyc_dscale g s]

lemma wgyc_e2 (k s : ℝ) (g : ℝ → ℝ) :
    deriv (fun r => k * (s * deriv g (s * r))) = fun r => k * (s * (s * deriv (deriv g) (s * r))) := by
  funext r
  rw [deriv_const_mul_field', deriv_const_mul_field', wgyc_dscale (deriv g) s]

lemma wgyc_e3 (k s : ℝ) (g : ℝ → ℝ) :
    deriv (fun r => k * (s * (s * deriv (deriv g) (s * r)))) =
      fun r => k * (s * (s * (s * deriv (deriv (deriv g)) (s * r)))) := by
  funext r
  rw [deriv_const_mul_field', deriv_const_mul_field', deriv_const_mul_field',
    wgyc_dscale (deriv (deriv g)) s]

theorem wgy_coeff_deriv {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν R : ℝ, 0 < ν → ν ≤ 1 → 1 ≤ R → ∀ r : ℝ,
      R * Real.sqrt ν ≤ r → r ≤ 2 * (R * Real.sqrt ν) →
      ∃ a1 a2 b1 b2 : ℝ, HasDerivAt (tcA1 ν R χ) a1 r ∧ HasDerivAt (tcA2 ν R χ) a2 r ∧
        HasDerivAt (tcB1 ν R χ) b1 r ∧ HasDerivAt (tcB2 ν R χ) b2 r ∧
        |a1| ≤ C * (R * Real.sqrt ν)⁻¹ ∧ |a2| ≤ C * ((R * Real.sqrt ν)⁻¹) ^ 2 ∧
        |b1| ≤ C * ((R * Real.sqrt ν)⁻¹) ^ 3 ∧ |b2| ≤ C * (R * Real.sqrt ν)⁻¹ := by
  obtain ⟨M, hM0, hM⟩ := wgyc_profile χ hχ
  refine ⟨8 * M, by positivity, ?_⟩
  intro ν R hν hν1 hR1 r hr1 hr2
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hL : 0 < L := by rw [hLdef]; have := Real.sqrt_pos.2 hν; positivity
  have hLsq : ν * R ^ 2 = L ^ 2 := by
    rw [hLdef, mul_pow, Real.sq_sqrt hν.le]; ring
  set s : ℝ := L⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 hL
  have hsL : s * L = 1 := inv_mul_cancel₀ hL.ne'
  have hr : 0 < r := lt_of_lt_of_le hL hr1
  have hsr1 : 1 ≤ s * r := by
    calc 1 = s * L := hsL.symm
      _ ≤ s * r := by gcongr
  have hsr2 : s * r ≤ 2 := by
    calc s * r ≤ s * (2 * L) := by gcongr
      _ = 2 := by rw [mul_left_comm, hsL]; ring
  have hνs : ν * s ^ 2 ≤ 1 := by
    have h1 : ν * R ^ 2 * s ^ 2 = 1 := by
      rw [hLsq]
      have : L ^ 2 * s ^ 2 = (s * L) ^ 2 := by ring
      rw [this, hsL]; norm_num
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    have : ν * s ^ 2 ≤ ν * R ^ 2 * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hR2 hν.le
      nlinarith [sq_nonneg s]
    linarith
  -- scaling
  have hc : tcC0 ν R χ = fun r => 1 * tcC0 1 1 χ (s * r) := by
    funext r; rw [one_mul]; exact congrFun (wgyc_c_scale ν R χ hL hLsq) r
  have hf : tcF0 ν R χ = fun r => s ^ 2 * tcF0 1 1 χ (s * r) := wgyc_f_scale ν R χ hL hLsq
  have hc1 : deriv (tcC0 ν R χ) = fun r => 1 * (s * deriv (tcC0 1 1 χ) (s * r)) := by
    rw [hc]; exact wgyc_e1 _ _ _
  have hc2 : deriv (deriv (tcC0 ν R χ)) =
      fun r => 1 * (s * (s * deriv (deriv (tcC0 1 1 χ)) (s * r))) := by
    rw [hc1]; exact wgyc_e2 _ _ _
  have hc3 : deriv (deriv (deriv (tcC0 ν R χ))) =
      fun r => 1 * (s * (s * (s * deriv (deriv (deriv (tcC0 1 1 χ))) (s * r)))) := by
    rw [hc2]; exact wgyc_e3 _ _ _
  have hf1 : deriv (tcF0 ν R χ) = fun r => s ^ 2 * (s * deriv (tcF0 1 1 χ) (s * r)) := by
    rw [hf]; exact wgyc_e1 _ _ _
  have hf2 : deriv (deriv (tcF0 ν R χ)) =
      fun r => s ^ 2 * (s * (s * deriv (deriv (tcF0 1 1 χ)) (s * r))) := by
    rw [hf1]; exact wgyc_e2 _ _ _
  have hf3 : deriv (deriv (deriv (tcF0 ν R χ))) =
      fun r => s ^ 2 * (s * (s * (s * deriv (deriv (deriv (tcF0 1 1 χ))) (s * r)))) := by
    rw [hf2]; exact wgyc_e3 _ _ _
  obtain ⟨m1, m2, m3, n0, n1, n2, n3⟩ := hM (s * r) ⟨hsr1, hsr2⟩
  -- bounds on the derivatives at r
  have bc1 : |deriv (tcC0 ν R χ) r| ≤ M * s := by
    rw [hc1]; simp only; rw [abs_mul, abs_mul, abs_of_pos hs0]
    calc |(1 : ℝ)| * (s * |deriv (tcC0 1 1 χ) (s * r)|) ≤ 1 * (s * M) := by
          rw [abs_one]; gcongr
      _ = M * s := by ring
  have bc2 : |deriv (deriv (tcC0 ν R χ)) r| ≤ M * s ^ 2 := by
    rw [hc2]; simp only; rw [abs_mul, abs_mul, abs_mul, abs_of_pos hs0]
    calc |(1 : ℝ)| * (s * (s * |deriv (deriv (tcC0 1 1 χ)) (s * r)|)) ≤ 1 * (s * (s * M)) := by
          rw [abs_one]; gcongr
      _ = M * s ^ 2 := by ring
  have bc3 : |deriv (deriv (deriv (tcC0 ν R χ))) r| ≤ M * s ^ 3 := by
    rw [hc3]; simp only; rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hs0]
    calc |(1 : ℝ)| * (s * (s * (s * |deriv (deriv (deriv (tcC0 1 1 χ))) (s * r)|))) ≤
          1 * (s * (s * (s * M))) := by
          rw [abs_one]; gcongr
      _ = M * s ^ 3 := by ring
  have bf1 : |deriv (tcF0 ν R χ) r| ≤ M * s ^ 3 := by
    rw [hf1]; simp only; rw [abs_mul, abs_mul, abs_of_pos hs0, abs_of_pos (by positivity : 0 < s ^ 2)]
    calc s ^ 2 * (s * |deriv (tcF0 1 1 χ) (s * r)|) ≤ s ^ 2 * (s * M) := by gcongr
      _ = M * s ^ 3 := by ring
  have bf2 : |deriv (deriv (tcF0 ν R χ)) r| ≤ M * s ^ 4 := by
    rw [hf2]; simp only; rw [abs_mul, abs_mul, abs_mul, abs_of_pos hs0,
      abs_of_pos (by positivity : 0 < s ^ 2)]
    calc s ^ 2 * (s * (s * |deriv (deriv (tcF0 1 1 χ)) (s * r)|)) ≤ s ^ 2 * (s * (s * M)) := by
          gcongr
      _ = M * s ^ 4 := by ring
  have bf3 : |deriv (deriv (deriv (tcF0 ν R χ))) r| ≤ M * s ^ 5 := by
    rw [hf3]; simp only; rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hs0,
      abs_of_pos (by positivity : 0 < s ^ 2)]
    calc s ^ 2 * (s * (s * (s * |deriv (deriv (deriv (tcF0 1 1 χ))) (s * r)|))) ≤
          s ^ 2 * (s * (s * (s * M))) := by gcongr
      _ = M * s ^ 5 := by ring
  -- differentiability
  have hmem : Ioi (0 : ℝ) ∈ 𝓝 r := isOpen_Ioi.mem_nhds hr
  have cd0 := Sub8_1_1_2_3.tcC0_cdOn (ν := ν) (R := R) hχ
  have cd1 := Sub8_1_1_2_3.cdOn_deriv cd0
  have cd2 := Sub8_1_1_2_3.cdOn_deriv cd1
  have fd0 := Sub8_1_1_2_3.tcF0_cdOn (ν := ν) (R := R) hχ
  have fd1 := Sub8_1_1_2_3.cdOn_deriv fd0
  have fd2 := Sub8_1_1_2_3.cdOn_deriv fd1
  have dd : ∀ {f : ℝ → ℝ}, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi 0) →
      DifferentiableAt ℝ f r := fun {f} h => (h.contDiffAt hmem).differentiableAt (by simp)
  have hr0 : r ≠ 0 := hr.ne'
  have hid : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id' r
  have hC1 := (dd cd1).hasDerivAt
  have hC2 := (dd cd2).hasDerivAt
  have hF0 := (dd fd0).hasDerivAt
  have hF1 := (dd fd1).hasDerivAt
  have hF2 := (dd fd2).hasDerivAt
  have hA1 : HasDerivAt (tcA1 ν R χ)
      (-(1 / 2) * deriv (tcC0 ν R χ) r - (1 / 2) * r * deriv (deriv (tcC0 ν R χ)) r -
        ν * (deriv (deriv (deriv (tcC0 ν R χ))) r + deriv (deriv (tcC0 ν R χ)) r / r -
          deriv (tcC0 ν R χ) r / r ^ 2)) r := by
    have h := (((hid.const_mul (-(1 / 2 : ℝ))).mul hC1).sub
      ((hC2.add (hC1.div hid hr0)).const_mul ν))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hA2 : HasDerivAt (tcA2 ν R χ) (-2 * ν * deriv (deriv (tcC0 ν R χ)) r) r := by
    have h := hC1.const_mul (-2 * ν)
    exact h
  have hB1 : HasDerivAt (tcB1 ν R χ)
      (-(1 / 2) * (3 * deriv (tcF0 ν R χ) r + r * deriv (deriv (tcF0 ν R χ)) r) -
        ν * (deriv (deriv (deriv (tcF0 ν R χ))) r + deriv (deriv (tcF0 ν R χ)) r / r -
          deriv (tcF0 ν R χ) r / r ^ 2)) r := by
    have h := ((((hid.mul hF1).add (hF0.const_mul 2)).const_mul (-(1 / 2 : ℝ))).sub
      ((hF2.add (hF1.div hid hr0)).const_mul ν))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hB2 : HasDerivAt (tcB2 ν R χ)
      (-2 * ν * (1 * deriv (tcF0 ν R χ) r + r * deriv (deriv (tcF0 ν R χ)) r +
        deriv (tcF0 ν R χ) r)) r := by
    have h := ((hid.mul hF1).add hF0).const_mul (-2 * ν)
    exact h
  have hLs : (R * Real.sqrt ν)⁻¹ = s := rfl
  refine ⟨_, _, _, _, hA1, hA2, hB1, hB2, ?_, ?_, ?_, ?_⟩
  · have := wgyc_A1_bound _ _ _ M s ν r hs0 hM0 bc1 bc2 bc3 hsr1 hsr2 hν.le hνs
    calc _ ≤ 5 * (M * s) := this
      _ ≤ 8 * M * s := by nlinarith [mul_nonneg hM0 hs0.le]
  · have e : |-2 * ν * deriv (deriv (tcC0 ν R χ)) r| = 2 * ν * |deriv (deriv (tcC0 ν R χ)) r| := by
      rw [abs_mul, abs_mul, abs_of_pos hν]; norm_num
    rw [e]
    calc 2 * ν * |deriv (deriv (tcC0 ν R χ)) r| ≤ 2 * 1 * (M * s ^ 2) := by gcongr
      _ ≤ 8 * M * s ^ 2 := by nlinarith [mul_nonneg hM0 (sq_nonneg s)]
  · have := wgyc_B1_bound _ _ _ M s ν r hs0 hM0 bf1 bf2 bf3 hsr1 hsr2 hν.le hνs
    calc _ ≤ 6 * (M * s ^ 3) := this
      _ ≤ 8 * M * s ^ 3 := by nlinarith [mul_nonneg hM0 (pow_nonneg hs0.le 3)]
  · have hM' : 0 ≤ M * s ^ 2 := by positivity
    obtain ⟨p2, -, -, -⟩ := wgyc_pieces (deriv (tcF0 ν R χ) r) (deriv (deriv (tcF0 ν R χ)) r)
      (deriv (deriv (deriv (tcF0 ν R χ))) r) (M * s ^ 2) s ν r hs0 hM'
      (by calc _ ≤ M * s ^ 3 := bf1
            _ = M * s ^ 2 * s := by ring)
      (by calc _ ≤ M * s ^ 4 := bf2
            _ = M * s ^ 2 * s ^ 2 := by ring)
      (by calc _ ≤ M * s ^ 5 := bf3
            _ = M * s ^ 2 * s ^ 3 := by ring) hsr1 hsr2 hν.le hνs
    have e3 : |1 * deriv (tcF0 ν R χ) r + r * deriv (deriv (tcF0 ν R χ)) r +
        deriv (tcF0 ν R χ) r| ≤ 4 * (M * s ^ 3) := by
      rw [abs_le]; constructor <;> linarith [abs_le.1 bf1, abs_le.1 p2]
    have e : |-2 * ν * (1 * deriv (tcF0 ν R χ) r + r * deriv (deriv (tcF0 ν R χ)) r +
        deriv (tcF0 ν R χ) r)| = 2 * ν * |1 * deriv (tcF0 ν R χ) r +
          r * deriv (deriv (tcF0 ν R χ)) r + deriv (tcF0 ν R χ) r| := by
      rw [abs_mul, abs_mul, abs_of_pos hν]; norm_num
    rw [e]
    calc 2 * ν * |1 * deriv (tcF0 ν R χ) r + r * deriv (deriv (tcF0 ν R χ)) r +
          deriv (tcF0 ν R χ) r| ≤ 2 * ν * (4 * (M * s ^ 3)) := by gcongr
      _ = 8 * M * s * (ν * s ^ 2) := by ring
      _ ≤ 8 * M * s * 1 := by gcongr
      _ = 8 * M * s := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
