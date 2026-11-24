import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.Joint

/-!
# `PDYKerBound` helpers (2): the `h`-derivative of the outward primitive

Source `the November 2 reference manuscript` 4178-4186 (the outward primitive),
3604-3610 (order-four kernel bounds).

At the normalized receiver radius `ϱ = 1` and for sources `ϱ z ≤ √(5/6)`, the outward primitive
`h ↦ sKer ν μ h 1 y₃ z M = -∫_{u>0} (1+u) xKer(h, q + u e₀ - λ(h) z)_z du` (`q = (1,0,y₃)`) is
differentiable, with the derivative under the integral sign (dominated by `(1+u)(κ+u)^{-4}`,
`κ = 1 - √(5/6)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `ρ₀ = √(5/6)`. -/
def ykR0 : ℝ := Real.sqrt (5 / 6)

/-- `κ = 1 - √(5/6)`. -/
def ykKap : ℝ := 1 - ykR0

theorem ykR0_nonneg : 0 ≤ ykR0 := Real.sqrt_nonneg _

theorem ykR0_lt_one : ykR0 < 1 := by
  unfold ykR0
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

theorem ykKap_pos : 0 < ykKap := by unfold ykKap; linarith [ykR0_lt_one]

theorem ykKap_le_one : ykKap ≤ 1 := by unfold ykKap; linarith [ykR0_nonneg]

theorem ykb_comp2 {f : ℝ → Space} {f' : Space} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => f s 2) (f' 2) t :=
  (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hf

theorem ykb_cont2 {α : Type*} [TopologicalSpace α] {G : α → Space} (hG : Continuous G) :
    Continuous (fun a => G a 2) :=
  (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp hG

theorem ykb_abs2_le (v : Space) : |v 2| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v 2
  rwa [Real.norm_eq_abs] at this

theorem ykb_z0_le {z : Space} (hz : ϱ z ≤ ykR0) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    (l • z) 0 ≤ ykR0 := by
  have h1 : |z 0| ≤ ϱ z := by
    unfold ϱ
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 1)])
  have h2 : l * z 0 ≤ |z 0| := by
    have := le_abs_self (z 0)
    have := abs_nonneg (z 0)
    nlinarith [abs_mul l (z 0), abs_of_pos hl0]
  simp only [PiLp.smul_apply, smul_eq_mul]
  linarith

theorem ykb_pdLam_le_one {h : ℝ} (hh : 0 ≤ h) : pdLam h ≤ 1 := by
  unfold pdLam; rw [Real.exp_le_one_iff]; linarith

/-- Lower bound of the source distance along the outward ray, at `q₀ = 1`. -/
theorem ykb_xlow {q w : Space} (hq0 : q 0 = 1) (hw : w 0 ≤ ykR0) {u : ℝ} (hu : 0 ≤ u) :
    (ykKap + u) ^ 2 + (q 2 - w 2) ^ 2 ≤ ‖q + (u • primE0 - w)‖ ^ 2 ∧
      ykKap + u ≤ ‖q + (u • primE0 - w)‖ := by
  have hρ : ykR0 ≤ q 0 + u := by rw [hq0]; linarith [ykR0_lt_one]
  have h := prim_shift_lower q w u ykR0 hw hρ
  have e : q 0 + u - ykR0 = ykKap + u := by rw [hq0]; unfold ykKap; ring
  rw [e] at h
  refine ⟨h, ?_⟩
  have hk : 0 ≤ ykKap + u := by linarith [ykKap_pos]
  have h2 : (ykKap + u) ^ 2 ≤ ‖q + (u • primE0 - w)‖ ^ 2 := by nlinarith [sq_nonneg (q 2 - w 2)]
  nlinarith [norm_nonneg (q + (u • primE0 - w))]

/-- `(1+u)(κ+u)^{-4}` is integrable on `(0,∞)`. -/
theorem ykb_int1 {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    IntegrableOn (fun u : ℝ => (1 + u) * ((κ + u) ^ 4)⁻¹) (Ioi 0) := by
  have hJ := (primJ2 hκ 0).1
  refine Integrable.mono' (hJ.const_mul κ⁻¹) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.inv₀ (by fun_prop) ?_)
    intro u hu
    have : 0 < κ + u := by have : (0 : ℝ) < u := hu; linarith
    positivity
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hk : 0 < κ + u := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have e : ((κ + u) ^ 2 + 0 ^ 2) ^ 2 = (κ + u) ^ 4 := by ring
    rw [e]
    have h1 : 1 + u ≤ κ⁻¹ * (κ + u) := by
      rw [le_inv_mul_iff₀ hκ]; nlinarith
    have h4 : 0 ≤ ((κ + u) ^ 4)⁻¹ := by positivity
    calc (1 + u) * ((κ + u) ^ 4)⁻¹ ≤ κ⁻¹ * (κ + u) * ((κ + u) ^ 4)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 h4
      _ = κ⁻¹ * ((κ + u) * ((κ + u) ^ 4)⁻¹) := by ring

/-- The `h`-derivative integrand of the outward primitive. -/
def ykFh (ν μ : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (z q : Space) (t u : ℝ) : ℝ :=
  (q 0 + u) * (fderiv ℝ (ykJ ν μ M) (t, q + (u • primE0 - pdLam t • z))
    (1, (pdLam t / 2) • z)) 2

theorem ykb_primF_eq (ν μ t : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (z q : Space) (u : ℝ) :
    primF (xKerA ν μ t M) (pdLam t • z) q u =
      (q 0 + u) * xKer ν μ t ((q + u • primE0) - pdLam t • z) M 2 := by
  unfold primF xKerA
  rw [add_sub_assoc]

theorem ykb_Fh_hasDeriv (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) (z q : Space)
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t' => primF (xKerA ν μ t' M) (pdLam t' • z) q u) (ykFh ν μ M z q t u) t := by
  have hB := ykb_comp2 (ykb_partB ν μ hν M ht (q + u • primE0) z)
  have h2 := hB.const_mul (q 0 + u)
  have e : (fun t' => primF (xKerA ν μ t' M) (pdLam t' • z) q u) =
      fun t' => (q 0 + u) * xKer ν μ t' ((q + u • primE0) - pdLam t' • z) M 2 := by
    funext t'; exact ykb_primF_eq ν μ t' M z q u
  rw [e]
  unfold ykFh
  rw [add_sub_assoc] at h2
  exact h2

/-- **Part 2 `h`-derivative** (normalized radius `1`). -/
theorem ykb_partC {C : ℝ} (hC : YKB C) (ν μ : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ)
    (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h) (z : Space)
    (hz : ϱ z ≤ ykR0) (y3 : ℝ) :
    Integrable (fun u => ykFh ν μ M z !₂[1, 0, y3] h u) (volume.restrict (Ioi 0)) ∧
    HasDerivAt (fun t => sKer ν μ t 1 y3 z M)
      (-∫ u in Ioi (0 : ℝ), ykFh ν μ M z !₂[1, 0, y3] h u) h := by
  set q : Space := !₂[1, 0, y3] with hqdef
  have hq0 : q 0 = 1 := by simp [hqdef]
  have hκ := ykKap_pos
  have hM0 := kb_tensor_nonneg M
  have hCM : 0 ≤ C * IIIa.tensorNorm M := mul_nonneg hC.1 hM0
  set B : ℝ := C * IIIa.tensorNorm M * (1 + ν * (ykKap ^ 2)⁻¹ + ‖z‖ * ykKap⁻¹) with hB
  have hBi : Integrable (fun u : ℝ => B * ((1 + u) * ((ykKap + u) ^ 4)⁻¹))
      (volume.restrict (Ioi 0)) :=
    (ykb_int1 hκ ykKap_le_one).const_mul B
  -- the pointwise domination of the derivative
  have hdom : ∀ t : ℝ, 0 < t → ∀ u : ℝ, 0 < u →
      ‖ykFh ν μ M z q t u‖ ≤ B * ((1 + u) * ((ykKap + u) ^ 4)⁻¹) := by
    intro t ht u hu
    have hl0 := pdLam_pos t
    have hl1 := ykb_pdLam_le_one ht.le
    obtain ⟨-, hx⟩ := ykb_xlow (w := pdLam t • z) hq0 (ykb_z0_le hz hl0 hl1) hu.le
    have hD := ykb_DJ_bound' hC ν μ hν hμ0 hμ1 M ht hκ (le_add_of_nonneg_right hu.le) hx
      ((pdLam t / 2) • z)
    have hv : ‖(pdLam t / 2) • z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have := norm_nonneg z
      nlinarith
    have hp1 := ykb_pdLam_rpow_le_one μ t hμ0 ht.le
    have hp0 := ykb_rpow_nonneg μ t
    unfold ykFh
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hq0, abs_of_pos (by linarith)]
    have h2 := (ykb_abs2_le (fderiv ℝ (ykJ ν μ M) (t, q + (u • primE0 - pdLam t • z))
      (1, (pdLam t / 2) • z))).trans hD
    have hk4 : 0 ≤ ((ykKap + u) ^ 4)⁻¹ := by positivity
    have hzk : ‖(pdLam t / 2) • z‖ * ykKap⁻¹ ≤ ‖z‖ * ykKap⁻¹ :=
      mul_le_mul_of_nonneg_right hv (inv_nonneg.2 hκ.le)
    have hP : 0 ≤ 1 + ν * (ykKap ^ 2)⁻¹ + ‖(pdLam t / 2) • z‖ * ykKap⁻¹ := by positivity
    have hQ : 0 ≤ (C * IIIa.tensorNorm M) *
        (1 + ν * (ykKap ^ 2)⁻¹ + ‖(pdLam t / 2) • z‖ * ykKap⁻¹) * ((ykKap + u) ^ 4)⁻¹ := by
      positivity
    have h3 : C * pdLam t ^ (2 * μ + 3) * IIIa.tensorNorm M *
        ((1 + ν * (ykKap ^ 2)⁻¹ + ‖(pdLam t / 2) • z‖ * ykKap⁻¹) * ((ykKap + u) ^ 4)⁻¹) ≤
        B * ((ykKap + u) ^ 4)⁻¹ := by
      have e1 : C * pdLam t ^ (2 * μ + 3) * IIIa.tensorNorm M *
          ((1 + ν * (ykKap ^ 2)⁻¹ + ‖(pdLam t / 2) • z‖ * ykKap⁻¹) * ((ykKap + u) ^ 4)⁻¹) =
          pdLam t ^ (2 * μ + 3) * ((C * IIIa.tensorNorm M) *
            (1 + ν * (ykKap ^ 2)⁻¹ + ‖(pdLam t / 2) • z‖ * ykKap⁻¹) * ((ykKap + u) ^ 4)⁻¹) := by
        ring
      rw [e1]
      calc pdLam t ^ (2 * μ + 3) * ((C * IIIa.tensorNorm M) *
            (1 + ν * (ykKap ^ 2)⁻¹ + ‖(pdLam t / 2) • z‖ * ykKap⁻¹) * ((ykKap + u) ^ 4)⁻¹)
          ≤ 1 * ((C * IIIa.tensorNorm M) *
            (1 + ν * (ykKap ^ 2)⁻¹ + ‖(pdLam t / 2) • z‖ * ykKap⁻¹) * ((ykKap + u) ^ 4)⁻¹) :=
            mul_le_mul_of_nonneg_right hp1 hQ
        _ ≤ B * ((ykKap + u) ^ 4)⁻¹ := by
            rw [one_mul, hB]
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCM) hk4
    calc (1 + u) * |(fderiv ℝ (ykJ ν μ M) (t, q + (u • primE0 - pdLam t • z))
          (1, (pdLam t / 2) • z)) 2| ≤ (1 + u) * (B * ((ykKap + u) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (by linarith)
      _ = B * ((1 + u) * ((ykKap + u) ^ 4)⁻¹) := by ring
  -- apply the dominated differentiation lemma
  have hball : Metric.ball h (h / 2) ∈ 𝓝 h := Metric.ball_mem_nhds h (by linarith)
  have hpos : ∀ t ∈ Metric.ball h (h / 2), 0 < t := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := (abs_lt.1 ht).1
    linarith
  have hFcont : ∀ t : ℝ, 0 < t →
      Continuous (fun u => primF (xKerA ν μ t M) (pdLam t • z) q u) := by
    intro t ht
    have hA := (xKerA_props C hC.1 hC.2 ν μ t hν hμ0 hμ1 ht M).1
    unfold primF
    exact (continuous_const.add continuous_id).mul (hA.continuous.comp (by fun_prop))
  have hF'cont : Continuous (fun u => ykFh ν μ M z q h u) := by
    unfold ykFh
    refine (continuous_const.add continuous_id).mul (ykb_cont2 ?_)
    have hpath : Continuous (fun u : ℝ => (h, q + (u • primE0 - pdLam h • z))) := by fun_prop
    have hmaps : ∀ u : ℝ, (h, q + (u • primE0 - pdLam h • z)) ∈ {p : ℝ × Space | 0 < p.1} :=
      fun u => hh
    exact ((ykJ_continuousOn_fderiv ν μ hν M).comp_continuous hpath hmaps).clm_apply
      continuous_const
  have hFint : Integrable (fun u => primF (xKerA ν μ h M) (pdLam h • z) q u)
      (volume.restrict (Ioi 0)) := by
    have hbd := (xKerA_props C hC.1 hC.2 ν μ h hν hμ0 hμ1 hh M).2.1
    refine Integrable.mono' ((ykb_int1 hκ ykKap_le_one).const_mul (C * IIIa.tensorNorm M))
      (hFcont h hh).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hl0 := pdLam_pos h
    have hl1 := ykb_pdLam_le_one hh.le
    obtain ⟨-, hx⟩ := ykb_xlow (w := pdLam h • z) hq0 (ykb_z0_le hz hl0 hl1) hu0.le
    have hxne : q + (u • primE0 - pdLam h • z) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx; linarith
    have hb := hbd _ hxne
    obtain ⟨p4, -, -⟩ := ykb_pow_inv hκ (le_add_of_nonneg_right hu0.le) hx
    have hp1 := ykb_pdLam_rpow_le_one μ h hμ0 hh.le
    have hp0 := ykb_rpow_nonneg μ h
    unfold primF
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hq0, abs_of_pos (by linarith)]
    have hk4 : 0 ≤ ((ykKap + u) ^ 4)⁻¹ := by positivity
    have hle : C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M ≤ C * IIIa.tensorNorm M := by
      have := mul_le_mul_of_nonneg_left hp1 hCM
      nlinarith
    have h5 : |xKerA ν μ h M (q + (u • primE0 - pdLam h • z))| ≤
        C * IIIa.tensorNorm M * ((ykKap + u) ^ 4)⁻¹ :=
      hb.trans (mul_le_mul hle p4 (by positivity) hCM)
    calc (1 + u) * |xKerA ν μ h M (q + (u • primE0 - pdLam h • z))|
        ≤ (1 + u) * (C * IIIa.tensorNorm M * ((ykKap + u) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left h5 (by linarith)
      _ = C * IIIa.tensorNorm M * ((1 + u) * ((ykKap + u) ^ 4)⁻¹) := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun t u => primF (xKerA ν μ t M) (pdLam t • z) q u)
    (F' := fun t u => ykFh ν μ M z q t u) (x₀ := h)
    (bound := fun u => B * ((1 + u) * ((ykKap + u) ^ 4)⁻¹)) hball
    (Filter.eventually_of_mem (Ioi_mem_nhds hh) fun t ht => (hFcont t ht).aestronglyMeasurable)
    hFint hF'cont.aestronglyMeasurable ?_ hBi ?_
  · refine ⟨key.1, ?_⟩
    have e : (fun t => sKer ν μ t 1 y3 z M) =
        fun t => -∫ u in Ioi (0 : ℝ), primF (xKerA ν μ t M) (pdLam t • z) q u := by
      funext t
      rw [sKer_eq_primInt]
      rfl
    rw [e]
    exact key.2.neg
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu t ht => ?_)
    exact hdom t (hpos t ht) u hu
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu t ht => ?_)
    exact ykb_Fh_hasDeriv ν μ hν M z q u (hpos t ht)

end UnforcedLeray.Short.PartIIIb.Concrete

end
