import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.SmoothDecay
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Age
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b_4

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/6/2/1`: the Duhamel identity of the flux pairing (`AdjFluxPairDuhamel`)

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Pointwise Duhamel for the smoothed tests (`Exist.cylHeatSmooth_duhamel`,
`Exist.pd_cylHeatSmooth_duhamel`) is integrated against `y = (F, h) in AdjY`; Fubini on
`cell c x [0, theta]` is justified by the decay `AdjSmoothDecay`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem fdj_jb_le_cell {c : ℝ} {x : ℝ × ℝ} (hx : x ∈ B0579.cell c) :
    B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by
  have hx' : -(c / 2) ≤ x.1 ∧ x.1 < c / 2 := by
    have h := hx
    simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at h
    exact ⟨by linarith [h.1], h.2⟩
  have hprod : 0 ≤ (c / 2 - x.1) * (x.1 + c / 2) :=
    mul_nonneg (by linarith [hx'.2]) (by linarith [hx'.1])
  unfold B0579.jb
  nlinarith [sq_nonneg x.2, mul_nonneg (sq_nonneg c) (sq_nonneg x.2)]

/-- A decay bound on the whole plane gives a power bound of `jb` on the cell. -/
theorem fdj_cell_decay {c k C : ℝ} (hc : 0 < c) (hk : 0 ≤ k) {h : ℝ × ℝ → ℝ}
    (hh : ∀ x : ℝ × ℝ, |h x| ≤ C * (1 + x.2 ^ 2) ^ (-k)) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c) :
    |h x| ≤ (|C| * (1 + c ^ 2 / 4) ^ k) * B0579.jb x ^ (-k) := by
  have hK : 0 < 1 + c ^ 2 / 4 := by positivity
  have ht : 0 < 1 + x.2 ^ 2 := by positivity
  have hjb : B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := fdj_jb_le_cell hx
  have hjbpos : 0 < B0579.jb x := B0579.jb_pos x
  have h1 : ((1 + c ^ 2 / 4) * (1 + x.2 ^ 2)) ^ (-k) ≤ B0579.jb x ^ (-k) :=
    Real.rpow_le_rpow_of_nonpos hjbpos hjb (by linarith)
  have h2 : ((1 + c ^ 2 / 4) * (1 + x.2 ^ 2)) ^ (-k)
      = (1 + c ^ 2 / 4) ^ (-k) * (1 + x.2 ^ 2) ^ (-k) := Real.mul_rpow hK.le ht.le
  have h3 : (1 + c ^ 2 / 4) ^ k * (1 + c ^ 2 / 4) ^ (-k) = 1 := by
    rw [← Real.rpow_add hK, add_neg_cancel, Real.rpow_zero]
  have h4 : (1 + x.2 ^ 2) ^ (-k) ≤ (1 + c ^ 2 / 4) ^ k * B0579.jb x ^ (-k) := by
    have e : (1 + x.2 ^ 2) ^ (-k)
        = (1 + c ^ 2 / 4) ^ k * (((1 + c ^ 2 / 4) * (1 + x.2 ^ 2)) ^ (-k)) := by
      rw [h2, ← mul_assoc, h3, one_mul]
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h0 : |h x| ≤ |C| * (1 + x.2 ^ 2) ^ (-k) :=
    le_trans (hh x) (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg ht.le _))
  calc |h x| ≤ |C| * (1 + x.2 ^ 2) ^ (-k) := h0
    _ ≤ |C| * ((1 + c ^ 2 / 4) ^ k * B0579.jb x ^ (-k)) :=
        mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
    _ = (|C| * (1 + c ^ 2 / 4) ^ k) * B0579.jb x ^ (-k) := by ring

/-- `L²(cellMeasure c m)` membership of a continuous function with a `jb^{-k}` cell bound,
`k = m/2 + 1`, so that `jb^m h² ≤ D² jb^{-2}`. -/
theorem fdj_memLp {c m k D : ℝ} (hm : 0 ≤ m) (hk : k = m / 2 + 1) {h : ℝ × ℝ → ℝ}
    (hcont : Continuous h) (hbd : ∀ x ∈ B0579.cell c, |h x| ≤ D * B0579.jb x ^ (-k)) :
    MemLp (fun x => ((h x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := by
  have hint : Integrable (fun x : ℝ × ℝ => D ^ 2 * B0579.jb x ^ (-(2:ℝ))) :=
    Lam0B.integrable_jb_neg_two.const_mul (D ^ 2)
  have key : IntegrableOn (fun x => B0579.jb x ^ m * h x ^ 2) (B0579.cell c) := by
    refine Integrable.mono' hint.integrableOn
      ((B0579.continuous_jb_rpow m).mul (hcont.pow 2)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
    have hb := hbd x hx
    have hA : B0579.jb x ^ m * (B0579.jb x ^ (-k)) ^ 2 = B0579.jb x ^ (-(2:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos x).le,
        ← Real.rpow_add (B0579.jb_pos x)]
      congr 1
      rw [hk]
      push_cast
      ring
    have hsq : h x ^ 2 ≤ (D * B0579.jb x ^ (-k)) ^ 2 := by
      have h1 : |h x| * |h x| ≤ (D * B0579.jb x ^ (-k)) * (D * B0579.jb x ^ (-k)) :=
        mul_le_mul hb hb (abs_nonneg _) (le_trans (abs_nonneg _) hb)
      nlinarith [abs_mul_abs_self (h x), sq_abs (h x)]
    have hnn : 0 ≤ B0579.jb x ^ m * h x ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    calc B0579.jb x ^ m * h x ^ 2 ≤ B0579.jb x ^ m * (D * B0579.jb x ^ (-k)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg (B0579.jb_pos x).le _)
      _ = D ^ 2 * (B0579.jb x ^ m * (B0579.jb x ^ (-k)) ^ 2) := by ring
      _ = D ^ 2 * B0579.jb x ^ (-(2:ℝ)) := by rw [hA]
  refine (memLp_two_iff_integrable_sq_norm
    (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable).2 ?_
  rw [B0579.integrable_cellMeasure_iff]
  refine key.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
  simp [NNReal.smul_def, B0579.coe_density, Complex.norm_real, sq_abs]

/-- The pairing of a fixed `w ∈ X_{-m,c}` with a continuous function with the decay bound. -/
theorem fdj_integrable_mul {c m D : ℝ} (hc : 0 < c) (hm : 0 ≤ m) {w : ℝ × ℝ → ℂ}
    (hw : MemLp w 2 (B0579.cellMeasure c (-m))) {h : ℝ × ℝ → ℝ} (hcont : Continuous h)
    (hbd : ∀ x : ℝ × ℝ, |h x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) :
    IntegrableOn (fun x => w x * ((h x : ℝ) : ℂ)) (B0579.cell c) := by
  have hk : (0:ℝ) ≤ m / 2 + 1 := by linarith
  have hF : MemLp (fun x => ((h x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    fdj_memLp hm rfl hcont (fun x hx => fdj_cell_decay hc hk hbd hx)
  have hH := PairContAux.holder hF hw
  exact hH.1.congr_fun (fun x _ => mul_comm _ _) (B0579.measurableSet_cell c)

/-- The joint integrability of `(x, η) ↦ w(x) b_η(x)` on `cell c × (0, θ]`. -/
theorem fdj_prod {c m θ D : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (hθ : 0 ≤ θ)
    {w : ℝ × ℝ → ℂ} (hw : MemLp w 2 (B0579.cellMeasure c (-m)))
    {b : ℝ → ℝ × ℝ → ℝ} (hb : Continuous (fun p : ℝ × (ℝ × ℝ) => b p.1 p.2))
    (hbd : ∀ η ∈ Icc (0:ℝ) θ, ∀ x : ℝ × ℝ, |b η x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => w p.1 * ((b p.2 p.1 : ℝ) : ℂ))
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (Ioc (0:ℝ) θ))) := by
  have hk : (0:ℝ) ≤ m / 2 + 1 := by linarith
  have hcont : Continuous (fun x : ℝ × ℝ => |D| * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) := by
    apply Continuous.mul continuous_const
    apply Continuous.rpow_const (by fun_prop)
    intro x
    left
    positivity
  have hint1 : Integrable (fun x : ℝ × ℝ => ‖w x‖ * (|D| * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))))
      (volume.restrict (B0579.cell c)) := by
    have hfun : IntegrableOn (fun x => w x * ((|D| * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) : ℝ) : ℂ))
        (B0579.cell c) :=
      fdj_integrable_mul hc hm hw hcont (fun x => le_of_eq (abs_of_nonneg (by positivity)))
    refine hfun.norm.congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) θ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hint2 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ioc (0:ℝ) θ)) :=
    integrable_const 1
  have hprod := Integrable.mul_prod hint1 hint2
  have hwm : AEStronglyMeasurable w (volume.restrict (B0579.cell c)) :=
    hw.1.mono_ac (B0579.ac_cellMeasure c (-m))
  refine Integrable.mono' hprod ?_ ?_
  · exact hwm.comp_fst.mul
      (Complex.continuous_ofReal.comp (hb.comp (continuous_snd.prodMk continuous_fst))).aestronglyMeasurable
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem ((B0579.measurableSet_cell c).prod measurableSet_Ioc) ?_
    intro p hp
    have hbp := hbd p.2 (Ioc_subset_Icc_self hp.2) p.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_one]
    exact mul_le_mul_of_nonneg_left
      (le_trans hbp (mul_le_mul_of_nonneg_right (le_abs_self D)
        (Real.rpow_nonneg (by positivity) _))) (norm_nonneg _)

theorem fdj_int_eta {c m θ D : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (hθ : 0 ≤ θ)
    {w : ℝ × ℝ → ℂ} (hw : MemLp w 2 (B0579.cellMeasure c (-m)))
    {b : ℝ → ℝ × ℝ → ℝ} (hb : Continuous (fun p : ℝ × (ℝ × ℝ) => b p.1 p.2))
    (hbd : ∀ η ∈ Icc (0:ℝ) θ, ∀ x : ℝ × ℝ, |b η x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) :
    IntervalIntegrable (fun η => ∫ x in B0579.cell c, w x * ((b η x : ℝ) : ℂ)) volume 0 θ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hθ]
  exact (fdj_prod hc hm hθ hw hb hbd).integral_prod_right

/-- Fubini-Duhamel for one component: the integral of `w (a + ∫_0^θ b_η)` splits. -/
theorem fdj_term {c m θ D₀ D : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (hθ : 0 ≤ θ)
    {w : ℝ × ℝ → ℂ} (hw : MemLp w 2 (B0579.cellMeasure c (-m)))
    {a : ℝ × ℝ → ℝ} (ha : Continuous a)
    (ha_bd : ∀ x : ℝ × ℝ, |a x| ≤ D₀ * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)))
    {b : ℝ → ℝ × ℝ → ℝ} (hb : Continuous (fun p : ℝ × (ℝ × ℝ) => b p.1 p.2))
    (hbd : ∀ η ∈ Icc (0:ℝ) θ, ∀ x : ℝ × ℝ, |b η x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) :
    ∫ x in B0579.cell c, w x * ((a x + ∫ η in (0:ℝ)..θ, b η x : ℝ) : ℂ) =
      (∫ x in B0579.cell c, w x * ((a x : ℝ) : ℂ)) +
        ∫ η in (0:ℝ)..θ, ∫ x in B0579.cell c, w x * ((b η x : ℝ) : ℂ) := by
  have hI := fdj_prod hc hm hθ hw hb hbd
  have hA : IntegrableOn (fun x => w x * ((a x : ℝ) : ℂ)) (B0579.cell c) :=
    fdj_integrable_mul hc hm hw ha ha_bd
  have hB : Integrable (fun x => ∫ η in Ioc (0:ℝ) θ, w x * ((b η x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    hI.integral_prod_left
  have hpt : ∀ x : ℝ × ℝ, w x * ((a x + ∫ η in (0:ℝ)..θ, b η x : ℝ) : ℂ)
      = w x * ((a x : ℝ) : ℂ) + ∫ η in Ioc (0:ℝ) θ, w x * ((b η x : ℝ) : ℂ) := by
    intro x
    rw [intervalIntegral.integral_of_le hθ, Complex.ofReal_add, ← integral_complex_ofReal, mul_add,
      integral_const_mul]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hA hB,
    intervalIntegral.integral_of_le hθ]
  congr 1
  exact integral_integral_swap (f := fun x η => w x * ((b η x : ℝ) : ℂ)) hI

/-- **(H6.2a) The Duhamel identity of the flux pairing** (SP 2819-2836): for `y = (F, h) ∈ AdjY`,
a cylinder test `φ` and `θ ≥ 0`, `ℓ(y; P_θφ) = ℓ(y; φ) + ∫_0^θ ℓ(y; P_η Δφ) dη`. -/
theorem adjFluxPairDuhamel (m : ℝ) (hm : 8 < m) : AdjFluxPairDuhamel m := by
  intro c hc y φ hφ θ hθ
  have hm0 : 0 ≤ m := by linarith
  have hk : (0:ℝ) ≤ m / 2 + 1 := by linarith
  have hΔ : B0579.IsCylTest c (lapP φ) := Exist.cylTest_lapP hφ
  -- the bound of a test at time zero
  have hzero : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∃ D : ℝ, ∀ x : ℝ × ℝ,
      |ψ x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) := by
    intro ψ hψ
    obtain ⟨C, hC⟩ := adjSmoothDecay c hc ψ hψ 0 (m / 2 + 1) le_rfl hk
    refine ⟨|C|, fun x => ?_⟩
    have h0 := hC 0 ⟨le_rfl, le_rfl⟩ x
    rw [Exist.cylHeatSmooth_zero] at h0
    exact le_trans h0 (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _))
  -- the uniform bound of the smoothed tests on [0, θ]
  have hθbd : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∃ D : ℝ, ∀ η ∈ Icc (0:ℝ) θ, ∀ x : ℝ × ℝ,
      |Exist.cylHeatSmooth c η ψ x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) := by
    intro ψ hψ
    obtain ⟨C, hC⟩ := adjSmoothDecay c hc ψ hψ θ (m / 2 + 1) hθ hk
    refine ⟨|C|, fun η hη x => ?_⟩
    exact le_trans (hC η hη x) (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _))
  have hPjoint : Continuous (fun p : ℝ × (ℝ × ℝ) => Exist.cylHeatSmooth c p.1 (lapP φ) p.2) :=
    Exist.continuous_cylHeatSmooth_joint_test hc hΔ
  have hpdjoint : ∀ j : Fin 2, Continuous
      (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (Exist.cylHeatSmooth c p.1 (lapP φ)) p.2) :=
    fun j => Exist.continuous_pd_cylHeatSmooth_joint hc hΔ j
  have hpdbd : ∀ j : Fin 2, ∃ D : ℝ, ∀ η ∈ Icc (0:ℝ) θ, ∀ x : ℝ × ℝ,
      |B0579.pd j (Exist.cylHeatSmooth c η (lapP φ)) x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) := by
    intro j
    obtain ⟨D, hD⟩ := hθbd (B0579.pd j (lapP φ)) ((Exist.cylTest_lapP hφ).pd j)
    refine ⟨D, fun η hη x => ?_⟩
    rw [Exist.pd_cylHeatSmooth hc hΔ j]
    exact hD η hη x
  obtain ⟨D₀, hD₀⟩ := hzero (B0579.pd 0 φ) (hφ.pd 0)
  obtain ⟨D₁, hD₁⟩ := hzero (B0579.pd 1 φ) (hφ.pd 1)
  obtain ⟨D₂, hD₂⟩ := hzero φ hφ
  obtain ⟨E₀, hE₀⟩ := hpdbd 0
  obtain ⟨E₁, hE₁⟩ := hpdbd 1
  obtain ⟨E₂, hE₂⟩ := hθbd (lapP φ) hΔ
  have E0 := fdj_term hc hm0 hθ (Lp.memLp (y.1 0)) ((hφ.pd 0).continuous) hD₀
    (hpdjoint 0) hE₀
  have E1 := fdj_term hc hm0 hθ (Lp.memLp (y.1 1)) ((hφ.pd 1).continuous) hD₁
    (hpdjoint 1) hE₁
  have E2 := fdj_term hc hm0 hθ (Lp.memLp y.2) hφ.continuous hD₂ hPjoint hE₂
  beta_reduce at E0 E1 E2
  have I0 := fdj_int_eta hc hm0 hθ (Lp.memLp (y.1 0)) (hpdjoint 0) hE₀
  have I1 := fdj_int_eta hc hm0 hθ (Lp.memLp (y.1 1)) (hpdjoint 1) hE₁
  have I2 := fdj_int_eta hc hm0 hθ (Lp.memLp y.2) hPjoint hE₂
  beta_reduce at I0 I1 I2
  simp only [adjFluxPair]
  simp only [Exist.pd_cylHeatSmooth_duhamel hc hφ hθ 0, Exist.pd_cylHeatSmooth_duhamel hc hφ hθ 1,
    Exist.cylHeatSmooth_duhamel (c := c) (θ := θ) hc hφ hθ]
  rw [E0, E1, E2, intervalIntegral.integral_add (I0.add I1) I2,
    intervalIntegral.integral_add I0 I1]
  ring

end UnforcedLeray.Short.IIIa
