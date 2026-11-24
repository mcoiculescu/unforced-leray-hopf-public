import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonV

/-!
# `μ`-Lipschitz bound of the zero-width Newton field on the receiver region
(helper of `Continuity/Lj.lean`, source 4776-4782, 4870-4900, 4917-4937, 5701-5704)

Source of record: `the November 2 reference manuscript` (73 pages).

For `t ∈ [0, 1]` and `μ, μ' ≥ 0`, `|t^{2μ+2} - t^{2μ'+2}| ≤ 2 |μ - μ'|`, so the integrand difference
`Fker c ν μ χo M a - Fker c ν μ' χo M a` satisfies the same `|y|^{-4-m}` jet bound as `Fker` with
an extra factor `2 |μ - μ'|`.  Since `iteratedFDeriv` of `newtonV` is the integral of
`iteratedFDeriv` of `Fker` (`UnforcedLeray.L09.iteratedFDeriv_integral_eq`), subtracting at `μ` and
`μ'` gives `‖∂^m (newtonV_μ - newtonV_{μ'})(w)‖ ≤ C_m |μ - μ'| N₀(M) |w|^{-4-m}` on
`{|w|² > 11ν/12}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Axi
open scoped Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace NewtonVGeom

/-- Auxiliary ordered bound: for `t ∈ [0, 1]` and `0 ≤ μ ≤ μ'`,
`|t^{2μ+2} - t^{2μ'+2}| ≤ 2 (μ' - μ)`. -/
theorem rpow_two_mu_sub_le_of_le {t μ μ' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hμ : 0 ≤ μ) (hle : μ ≤ μ') :
    |t ^ (2 * μ + 2) - t ^ (2 * μ' + 2)| ≤ 2 * (μ' - μ) := by
  rcases ht0.eq_or_lt with rfl | ht
  · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), sub_self, abs_zero]
    linarith
  · set L : ℝ := -Real.log t with hL
    have hL0 : 0 ≤ L := by
      rw [hL, neg_nonneg]
      exact Real.log_nonpos ht.le ht1
    have hp1 : t ^ (2 * μ + 2) = Real.exp (-((2 * μ + 2) * L)) := by
      rw [Real.rpow_def_of_pos ht, hL]; ring_nf
    have hp2 : t ^ (2 * μ' + 2) = Real.exp (-((2 * μ' + 2) * L)) := by
      rw [Real.rpow_def_of_pos ht, hL]; ring_nf
    have hsub_eq : Real.exp (-((2 * μ + 2) * L)) - Real.exp (-((2 * μ' + 2) * L)) =
        Real.exp (-((2 * μ + 2) * L)) * (1 - Real.exp (-(2 * (μ' - μ) * L))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2
      ring
    have hd0 : 0 ≤ 2 * (μ' - μ) * L := by
      have : 0 ≤ μ' - μ := sub_nonneg.2 hle
      positivity
    have hexp_d_le : Real.exp (-(2 * (μ' - μ) * L)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith)
    have h1_sub_nn : 0 ≤ 1 - Real.exp (-(2 * (μ' - μ) * L)) := sub_nonneg.2 hexp_d_le
    have h1_sub_le : 1 - Real.exp (-(2 * (μ' - μ) * L)) ≤ 2 * (μ' - μ) * L := by
      linarith [Real.add_one_le_exp (-(2 * (μ' - μ) * L))]
    have hexp_mu_le : Real.exp (-((2 * μ + 2) * L)) ≤ Real.exp (-L) := by
      apply Real.exp_le_exp.2
      nlinarith
    have hL_exp : Real.exp (-L) * L ≤ 1 := by
      have h1 : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
      calc Real.exp (-L) * L ≤ Real.exp (-L) * Real.exp L :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = Real.exp (-L + L) := (Real.exp_add (-L) L).symm
        _ = 1 := by simp
    rw [hp1, hp2, hsub_eq, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h1_sub_nn)]
    calc Real.exp (-((2 * μ + 2) * L)) * (1 - Real.exp (-(2 * (μ' - μ) * L)))
        ≤ Real.exp (-L) * (2 * (μ' - μ) * L) :=
          mul_le_mul hexp_mu_le h1_sub_le h1_sub_nn (Real.exp_pos _).le
      _ = 2 * (μ' - μ) * (Real.exp (-L) * L) := by ring
      _ ≤ 2 * (μ' - μ) * 1 :=
          mul_le_mul_of_nonneg_left hL_exp (by linarith)
      _ = 2 * (μ' - μ) := mul_one _

/-- For `t ∈ [0, 1]` and `μ, μ' ≥ 0`, `|t^{2μ+2} - t^{2μ'+2}| ≤ 2 |μ - μ'|`. -/
theorem rpow_two_mu_sub_le {t μ μ' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hμ : 0 ≤ μ) (hμ' : 0 ≤ μ') :
    |t ^ (2 * μ + 2) - t ^ (2 * μ' + 2)| ≤ 2 * |μ - μ'| := by
  rcases le_total μ μ' with hle | hle
  · rw [abs_sub_comm μ μ', abs_of_nonneg (sub_nonneg.2 hle)]
    exact rpow_two_mu_sub_le_of_le ht0 ht1 hμ hle
  · rw [abs_sub_comm (t ^ (2 * μ + 2)), abs_of_nonneg (sub_nonneg.2 hle)]
    exact rpow_two_mu_sub_le_of_le ht0 ht1 hμ' hle

theorem norm_gOp_sub_le {c ν μ μ' : ℝ} {χo : ℝ → ℝ} (hμ : 0 ≤ μ) (hμ' : 0 ≤ μ')
    (M : Chart → Mat3) {a : ℝ × (ℝ × ℝ)} (ht0 : 0 ≤ a.1) (ht1 : a.1 ≤ 1) :
    ‖gOp c ν μ χo M a - gOp c ν μ' χo M a‖ ≤ 36 * |μ - μ'| * frob (sigmaM c ν χo M a.2) := by
  have hsub : gOp c ν μ χo M a - gOp c ν μ' χo M a =
      (-2 * (a.1 ^ (2 * μ + 2) - a.1 ^ (2 * μ' + 2))) • Lmat (sigmaM c ν χo M a.2) := by
    unfold gOp
    ext v i
    simp only [sub_apply, smul_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsub, norm_smul, Real.norm_eq_abs]
  have hp := rpow_two_mu_sub_le ht0 ht1 hμ hμ'
  have hf := frob_nonneg' (sigmaM c ν χo M a.2)
  calc |-2 * (a.1 ^ (2 * μ + 2) - a.1 ^ (2 * μ' + 2))| * ‖Lmat (sigmaM c ν χo M a.2)‖
      ≤ (2 * (2 * |μ - μ'|)) * (9 * frob (sigmaM c ν χo M a.2)) := by
        refine mul_le_mul ?_ (norm_Lmat _) (norm_nonneg _) (by positivity)
        rw [abs_mul, abs_neg, abs_two]
        exact mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 36 * |μ - μ'| * frob (sigmaM c ν χo M a.2) := by ring

theorem Fker_sub_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (c ν μ μ' : ℝ) (χo : ℝ → ℝ)
    (M : Chart → Mat3), 0 < ν → IsOutwardCutoff χo → 0 ≤ μ → 0 ≤ μ' →
    ∀ (a : ℝ × (ℝ × ℝ)), 0 ≤ a.1 → a.1 ≤ 1 → ∀ y : Vec3, ν * (11 / 12) < eucSq y →
    ‖iteratedFDeriv ℝ n (Fker c ν μ χo M a) y - iteratedFDeriv ℝ n (Fker c ν μ' χo M a) y‖ ≤
      K * |μ - μ'| * frob (sigmaM c ν χo M a.2) * (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n) := by
  obtain ⟨K, hK0, hK⟩ := D3t_shift_bound n
  refine ⟨36 * K, by positivity, ?_⟩
  intro c ν μ μ' χo M hν hχ hμ hμ' a ht0 ht1 y hy
  have hp : 0 ≤ (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hf := frob_nonneg' (sigmaM c ν χo M a.2)
  rw [iter_Fker n hν hχ M ht0 ht1 hy, iter_Fker n hν hχ M ht0 ht1 hy]
  by_cases h : a.2.1 ^ 2 + a.2.2 ^ 2 ≤ 5 * ν / 6
  · have hsub : (gOp c ν μ χo M a).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun x => D3t (x - a.1 • embPlane a.2)) y) -
        (gOp c ν μ' χo M a).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun x => D3t (x - a.1 • embPlane a.2)) y) =
        (gOp c ν μ χo M a - gOp c ν μ' χo M a).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun x => D3t (x - a.1 • embPlane a.2)) y) := by
      ext m; simp
    rw [hsub]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have h1 := norm_gOp_sub_le (c := c) (ν := ν) (χo := χo) hμ hμ' M ht0 ht1
    have h2 := hK ν a.1 y a.2 hν ht0 ht1 hy h
    calc ‖gOp c ν μ χo M a - gOp c ν μ' χo M a‖ *
            ‖iteratedFDeriv ℝ n (fun x => D3t (x - a.1 • embPlane a.2)) y‖
        ≤ (36 * |μ - μ'| * frob (sigmaM c ν χo M a.2)) *
            (K * (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 36 * K * |μ - μ'| * frob (sigmaM c ν χo M a.2) *
            (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n) := by ring
  · have h0 := gOp_eq_zero (c := c) (μ := μ) hν hχ M h
    have h0' := gOp_eq_zero (c := c) (μ := μ') hν hχ M h
    have hz : ∀ φ : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec3) T3,
        (0 : T3 →L[ℝ] Vec3).compContinuousMultilinearMap φ = 0 := fun φ => by ext m; simp
    rw [h0, h0', hz, sub_self, norm_zero]
    positivity

end NewtonVGeom

open NewtonVGeom in
/-- `μ`-Lipschitz bound for the zero-width Newton field on `{|w|² > 11ν/12}`. -/
theorem newtonV_sub_regionBound (χo : ℝ → ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ (c ν μ μ' : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
      0 ≤ μ → 0 ≤ μ' → ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ContDiffOn ℝ 7 (newtonV c ν μ χo M - newtonV c ν μ' χo M) {w | ν * (11 / 12) < eucSq w} ∧
      ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
        ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M - newtonV c ν μ' χo M) w‖ ≤
          C m * |μ - μ'| * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
  choose K hK0 hK using NewtonVGeom.Fker_sub_bound
  refine ⟨fun n => K n * Real.pi, fun n => mul_nonneg (hK0 n) Real.pi_pos.le, ?_⟩
  intro c ν μ μ' hc hν hχ hμ hμ' M hM
  obtain ⟨-, hint, hl1⟩ := sigmaM_l1 c ν χo hc hν hχ M hM
  have hopen := isOpen_regU ν
  have hsm : ∀ μ'' : ℝ, ∀ᵐ a ∂mu2, ContDiffOn ℝ NewtonD3.ii (Fker c ν μ'' χo M a)
      {w | ν * (11 / 12) < eucSq w} := by
    intro μ''
    filter_upwards [ae_good] with a ha
    exact contDiffOn_Fker hν hχ M ha.1.le ha.2
  have hmeas : ∀ μ'' : ℝ, ∀ (n : ℕ), ∀ x ∈ {w : Vec3 | ν * (11 / 12) < eucSq w},
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (Fker c ν μ'' χo M a) x) mu2 :=
    fun μ'' n x hx => aesm_iter_Fker n hν hχ M hint.aestronglyMeasurable hx
  have hdom1 := locDominated_Fker hν hχ hμ M hint
  have hdom2 := locDominated_Fker hν hχ hμ' M hint
  have heq : ∀ μ'' : ℝ, 0 ≤ μ'' → ∀ y ∈ {w : Vec3 | ν * (11 / 12) < eucSq w},
      newtonV c ν μ'' χo M y = ∫ a, Fker c ν μ'' χo M a y ∂mu2 :=
    fun μ'' hμ'' y hy => newtonV_eq_integral hν hχ hμ'' M hint hy
  have hcd1 := (UnforcedLeray.L09.contDiffOn_integral hopen (hsm μ) (hmeas μ) hdom1).congr
    (heq μ hμ)
  have hcd2 := (UnforcedLeray.L09.contDiffOn_integral hopen (hsm μ') (hmeas μ') hdom2).congr
    (heq μ' hμ')
  have hnv1 : ContDiffOn ℝ 7 (newtonV c ν μ χo M) {w | ν * (11 / 12) < eucSq w} :=
    hcd1.of_le (by simp)
  have hnv2 : ContDiffOn ℝ 7 (newtonV c ν μ' χo M) {w | ν * (11 / 12) < eucSq w} :=
    hcd2.of_le (by simp)
  refine ⟨hnv1.sub hnv2, fun m hm w hw => ?_⟩
  have hat1 : ContDiffAt ℝ 7 (newtonV c ν μ χo M) w := hnv1.contDiffAt (hopen.mem_nhds hw)
  have hat2 : ContDiffAt ℝ 7 (newtonV c ν μ' χo M) w := hnv2.contDiffAt (hopen.mem_nhds hw)
  have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
  rw [iteratedFDeriv_sub_apply (hat1.of_le hmle) (hat2.of_le hmle)]
  have hEv1 : newtonV c ν μ χo M =ᶠ[nhds w] fun y => ∫ a, Fker c ν μ χo M a y ∂mu2 := by
    filter_upwards [hopen.mem_nhds hw] with y hy using heq μ hμ y hy
  have hEv2 : newtonV c ν μ' χo M =ᶠ[nhds w] fun y => ∫ a, Fker c ν μ' χo M a y ∂mu2 := by
    filter_upwards [hopen.mem_nhds hw] with y hy using heq μ' hμ' y hy
  rw [(hEv1.iteratedFDeriv ℝ m).eq_of_nhds, (hEv2.iteratedFDeriv ℝ m).eq_of_nhds,
    UnforcedLeray.L09.iteratedFDeriv_integral_eq hopen (hsm μ) (hmeas μ) hdom1 m hw,
    UnforcedLeray.L09.iteratedFDeriv_integral_eq hopen (hsm μ') (hmeas μ') hdom2 m hw,
    ← integral_sub (hdom1.integrable (hmeas μ) m hw) (hdom2.integrable (hmeas μ') m hw)]
  refine (norm_integral_le_integral_norm _).trans ?_
  set P := (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hr : ∫ a, ‖iteratedFDeriv ℝ m (Fker c ν μ χo M a) w -
        iteratedFDeriv ℝ m (Fker c ν μ' χo M a) w‖ ∂mu2 ≤
      ∫ a, (K m * |μ - μ'| * P) * frob (sigmaM c ν χo M a.2) ∂mu2 := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (integrable_const_frob _ hint) ?_
    filter_upwards [ae_good] with a ha
    have := hK m c ν μ μ' χo M hν hχ hμ hμ' a ha.1.le ha.2 w hw
    calc _ ≤ _ := this
      _ = _ := by ring
  have hc' : ∫ a, (K m * |μ - μ'| * P) * frob (sigmaM c ν χo M a.2) ∂mu2 =
      K m * |μ - μ'| * P * ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x') := by
    have := integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := (volume : Measure (ℝ × ℝ))) (fun _ => (1 : ℝ))
      (fun x' => K m * |μ - μ'| * P * frob (sigmaM c ν χo M x'))
    have e1 : (fun z : ℝ × (ℝ × ℝ) => (fun _ : ℝ => (1 : ℝ)) z.1 *
        (fun x' : ℝ × ℝ => K m * |μ - μ'| * P * frob (sigmaM c ν χo M x')) z.2) =
        fun a => (K m * |μ - μ'| * P) * frob (sigmaM c ν χo M a.2) := by
      funext a; simp
    rw [e1] at this
    rw [this, integral_const_mul]
    simp
  refine hr.trans (hc'.le.trans ?_)
  calc K m * |μ - μ'| * P * ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x')
      ≤ K m * |μ - μ'| * P * (Real.pi * oldN0 c ν M) :=
        mul_le_mul_of_nonneg_left hl1
          (mul_nonneg (mul_nonneg (hK0 m) (abs_nonneg _)) hP0)
    _ = K m * Real.pi * |μ - μ'| * oldN0 c ν M * P := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
