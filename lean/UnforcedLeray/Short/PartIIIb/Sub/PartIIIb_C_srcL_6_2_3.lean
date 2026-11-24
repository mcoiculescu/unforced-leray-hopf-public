import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonD3
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3.Helpers
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_5
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# `PartIII-b:C/srcL/6/2/3`: derivative decay of the zero-width Young field

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
Target `XSYoungWDecay`: for `a` above the threshold `5ν/(6ε²)` and every `k`, the `k`-th derivative
of `youngW` is `≤ C (1+‖w‖)^{-(4+k)}` on `{a ≤ cylR w²}`.

Plan: (1) kernel lower bound `(1+‖x‖)² ≤ C₂ eucSq(x - t(a,0))` on the region;
(2) pointwise bound of the `k`-th derivative of each kernel integrand (`newtonD3_bound`);
(3) integration in `a` and `t` by `L09.norm_iteratedFDeriv_integral_le`;
(4) componentwise bound for the `Vec3`-valued field; (5) scaling `youngW = ε² • newtonV (ε • ·)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace YoungDecay

/-- The constant `1 + (1+√P)/(√m - √P)` of the kernel lower bound. -/
def kconst (P m : ℝ) : ℝ := 1 + (1 + Real.sqrt P) / (Real.sqrt m - Real.sqrt P)

/-- Kernel lower bound on the region. -/
theorem kernel_lower (P m : ℝ) (hP : 0 < P) (hPm : P < m) (x : Vec3)
    (hx : m ≤ x 0 ^ 2 + x 1 ^ 2) (a : ℝ × ℝ) (ha : a.1 ^ 2 + a.2 ^ 2 < P) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + ‖x‖) ^ 2 ≤ 2 * kconst P m ^ 2 * eucSq (x - t • embPlane a) := by
  have hPx : P < x 0 ^ 2 + x 1 ^ 2 := lt_of_lt_of_le hPm hx
  have hsP : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hsPm : Real.sqrt P < Real.sqrt m := Real.sqrt_lt_sqrt hP.le hPm
  have hδ : 0 < Real.sqrt m - Real.sqrt P := sub_pos.2 hsPm
  have hu := NewtonFam.kernel_sq_uniform (x 0) (x 1) a.1 a.2 t P (x 0 ^ 2 + x 1 ^ 2) ht0 ht1
    hPx le_rfl ha
  have hρm : Real.sqrt m ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := Real.sqrt_le_sqrt hx
  have hu1 : Real.sqrt m - Real.sqrt P ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P := by
    linarith
  have hS : (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) ^ 2 + x 2 ^ 2
      ≤ eucSq (x - t • embPlane a) := by
    unfold eucSq
    rw [Fin.sum_univ_three, NewtonFam.embPlane_apply0, NewtonFam.embPlane_apply1,
      NewtonFam.embPlane_apply2]
    nlinarith [hu]
  have hnn : 0 ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := Real.sqrt_nonneg _
  have hnorm : ‖x‖ ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) + |x 2| := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i => ?_)
    have h0 : |x 0| ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 1)])
    have h1 : |x 1| ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 0)])
    have h2 : 0 ≤ |x 2| := abs_nonneg _
    rw [Real.norm_eq_abs]
    fin_cases i <;> simp <;> linarith
  set δ := Real.sqrt m - Real.sqrt P with hδdef
  set K0 := kconst P m with hK0def
  have hK0 : K0 = 1 + (1 + Real.sqrt P) / δ := rfl
  have hc0 : 0 ≤ (1 + Real.sqrt P) / δ := div_nonneg (by positivity) hδ.le
  have e1 : (1 + Real.sqrt P) / δ * δ = 1 + Real.sqrt P := div_mul_cancel₀ _ hδ.ne'
  have e2 : (1 + Real.sqrt P) / δ * δ ≤ (1 + Real.sqrt P) / δ *
      (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) :=
    mul_le_mul_of_nonneg_left hu1 hc0
  have hv : 0 ≤ (1 + Real.sqrt P) / δ * |x 2| := mul_nonneg hc0 (abs_nonneg _)
  have hK : 1 + ‖x‖ ≤ K0 * ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) + |x 2|) := by
    rw [hK0]
    nlinarith [e1, e2, hv, hnorm]
  have hcs : ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) + |x 2|) ^ 2
      ≤ 2 * ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) ^ 2 + x 2 ^ 2) := by
    nlinarith [sq_nonneg ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) - |x 2|), sq_abs (x 2)]
  have hK2 : 0 ≤ K0 ^ 2 := sq_nonneg _
  calc (1 + ‖x‖) ^ 2
      ≤ (K0 * ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) + |x 2|)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hK 2
    _ = K0 ^ 2 * (((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) + |x 2|) ^ 2) := by ring
    _ ≤ K0 ^ 2 * (2 * ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt P) ^ 2 + x 2 ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hK2
    _ ≤ 2 * K0 ^ 2 * eucSq (x - t • embPlane a) := by
        nlinarith [hS, hK2]

theorem kconst_pos (P m : ℝ) (hP : 0 < P) (hPm : P < m) : 0 < kconst P m := by
  unfold kconst
  have hδ : 0 ≤ Real.sqrt m - Real.sqrt P := sub_nonneg.2 (Real.sqrt_le_sqrt hPm.le)
  have : 0 ≤ (1 + Real.sqrt P) / (Real.sqrt m - Real.sqrt P) :=
    div_nonneg (by positivity) hδ
  linarith

/-- Power step: from `1 + R ≤ L s` we get `s^{-p} ≤ L^p (1+R)^{-p}`. -/
theorem rpow_neg_bound (L R s p : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hp : 0 ≤ p)
    (h : 1 + R ≤ L * s) : s ^ (-p) ≤ L ^ p * (1 + R) ^ (-p) := by
  have hLs : 0 < L * s := by linarith
  have hs : 0 < s := pos_of_mul_pos_right hLs hL.le
  have hq0 : 0 < (1 + R) / L := div_pos (by linarith) hL
  have hqs : (1 + R) / L ≤ s := (div_le_iff₀ hL).2 (by linarith [mul_comm L s])
  have h1 : s ^ (-p) ≤ ((1 + R) / L) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hq0 hqs (by linarith)
  have h2 : ((1 + R) / L) ^ (-p) = L ^ p * (1 + R) ^ (-p) := by
    rw [Real.div_rpow (by linarith) hL.le, Real.rpow_neg hL.le p, div_inv_eq_mul, mul_comm]
  rw [h2] at h1
  exact h1

/-- Pointwise bound on the `n`-th derivative of one kernel integrand `famF t i a` on the
region `{m ≤ x₀² + x₁²}`, for `m > 5ν/6`, `t ∈ (0,1]`. -/
theorem famF_deriv_pt (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (n : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ w : Vec3, w ≠ 0 → ∀ i j k : Fin 3,
      ‖iteratedFDeriv ℝ n (fun x => newtonD3 x i j k) w‖ ≤ C * (Real.sqrt (eucSq w)) ^ (-(4:ℝ) - n))
    (m : ℝ) (hPm : 5 * ν / 6 < m) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (i : Fin 3)
    (a : ℝ × ℝ) (x : Vec3) (hx : m ≤ x 0 ^ 2 + x 1 ^ 2) :
    ‖iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) x‖ ≤
      (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) *
        (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
          (1 + ‖x‖) ^ (-(4 + (n:ℝ))))) := by
  have hP : 0 < 5 * ν / 6 := by positivity
  have hPx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2 := lt_of_lt_of_le hPm hx
  have hkc := kconst_pos (5 * ν / 6) m hP hPm
  have hL : 0 < Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2) :=
    Real.sqrt_pos.2 (mul_pos two_pos (pow_pos hkc 2))
  by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
  · have hne : x - t • embPlane a ≠ 0 :=
      NewtonFam.kernel_arg_ne_zero x a t (5 * ν / 6) ht.1.le ht.2 ha hPx
    rw [NewtonFam.fam_iter_eq c ν χo M t i n a x (Or.inr hne)]
    have hK := kernel_lower (5 * ν / 6) m hP hPm x hx a ha t ht.1.le ht.2
    have hpt : ∀ j k : Fin 3, ‖iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k)
        (x - t • embPlane a)‖ ≤
        C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
          (1 + ‖x‖) ^ (-(4 + (n:ℝ)))) := by
      intro j k
      have h1 := hC (x - t • embPlane a) hne i j k
      have hexp : (-(4:ℝ) - (n:ℝ)) = -(4 + (n:ℝ)) := by ring
      rw [hexp] at h1
      refine h1.trans ?_
      have hs0 : 0 ≤ eucSq (x - t • embPlane a) :=
        Finset.sum_nonneg fun l _ => sq_nonneg _
      have hsq : Real.sqrt (eucSq (x - t • embPlane a)) ^ 2 = eucSq (x - t • embPlane a) :=
        Real.sq_sqrt hs0
      have hle : 1 + ‖x‖ ≤ Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2) *
          Real.sqrt (eucSq (x - t • embPlane a)) := by
        have hR : 0 ≤ 1 + ‖x‖ := by positivity
        have hRL : 0 ≤ Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2) *
            Real.sqrt (eucSq (x - t • embPlane a)) := by positivity
        have hsq2 : Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2) ^ 2 =
            2 * kconst (5 * ν / 6) m ^ 2 :=
          Real.sq_sqrt (by positivity)
        have hsq3 : (1 + ‖x‖) ^ 2 ≤ (Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2) *
            Real.sqrt (eucSq (x - t • embPlane a))) ^ 2 := by
          rw [mul_pow, hsq2, hsq]
          exact hK
        exact (pow_le_pow_iff_left₀ hR hRL two_ne_zero).1 hsq3
      have hb := rpow_neg_bound (Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ‖x‖
        (Real.sqrt (eucSq (x - t • embPlane a))) (4 + (n:ℝ)) hL (norm_nonneg x)
        (by positivity) hle
      exact mul_le_mul_of_nonneg_left hb hC0
    calc ‖∑ j : Fin 3, ∑ k : Fin 3, sigmaM c ν χo M a j k •
            iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)‖
        ≤ ∑ j : Fin 3, ‖∑ k : Fin 3, sigmaM c ν χo M a j k •
            iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k •
            iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)‖ :=
          Finset.sum_le_sum fun j _ => norm_sum_le _ _
      _ = ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖ *
            ‖iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)‖ := by
          simp only [norm_smul]
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖ *
            (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
              (1 + ‖x‖) ^ (-(4 + (n:ℝ))))) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hpt j k) (norm_nonneg _)
      _ = (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) *
            (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
              (1 + ‖x‖) ^ (-(4 + (n:ℝ))))) := by
          simp only [Finset.sum_mul]
  · have h0 : sigmaM c ν χo M a = 0 := sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)
    have hG : (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) = 0 := by
      simp [h0]
    rw [hG, zero_mul]
    rw [NewtonFam.fam_iter_eq c ν χo M t i n a x (Or.inl h0)]
    simp [h0]

/-- Bound on the `n`-th derivative of one zero-width family `newtonFam i t` on the region. -/
theorem newtonFam_deriv_bound (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c)
    (hν : 0 < ν) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (n : ℕ) (C : ℝ)
    (hC0 : 0 ≤ C)
    (hC : ∀ w : Vec3, w ≠ 0 → ∀ i j k : Fin 3,
      ‖iteratedFDeriv ℝ n (fun x => newtonD3 x i j k) w‖ ≤ C * (Real.sqrt (eucSq w)) ^ (-(4:ℝ) - n))
    (m : ℝ) (hPm : 5 * ν / 6 < m) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1)
    (x : Vec3) (hx : m ≤ x 0 ^ 2 + x 1 ^ 2) :
    ‖iteratedFDeriv ℝ n (newtonFam c ν μ χo M i t) x‖ ≤
      t ^ (2 * μ + 2) * ((∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) *
        (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
          (1 + ‖x‖) ^ (-(4 + (n:ℝ)))))) := by
  have hU := isOpen_newtonRegion ν
  have hyU : x ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := lt_of_lt_of_le hPm hx
  have hsmooth := NewtonFam.famF_integral_contDiffOn c ν χo M hc hν hχ hM t ht i
  have hGat : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y
        ∂(volume : Measure (ℝ × ℝ))) x :=
    (hsmooth.contDiffAt (hU.mem_nhds hyU)).of_le (by exact_mod_cast le_top)
  have e : newtonFam c ν μ χo M i t = (t ^ (2 * μ + 2)) •
      (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y
        ∂(volume : Measure (ℝ × ℝ))) := by
    funext z
    rfl
  rw [e, iteratedFDeriv_const_smul_apply hGat, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.1.le _)
  have h1 := UnforcedLeray.L09.norm_iteratedFDeriv_integral_le
    (μ := (volume : Measure (ℝ × ℝ))) hU
    (Filter.Eventually.of_forall fun a => NewtonFam.famF_contDiffOn c ν χo M hν hχ t ht i a)
    (fun n' y hy => NewtonFam.famF_aesm c ν χo M hc hν hχ hM t ht i n' y hy)
    (NewtonFam.famF_locDom c ν χo M hν hχ hc hM t ht i) n hyU
  have hint := NewtonFam.sigma_norm_sum_integrable c ν χo M hc hν hχ hM
  refine h1.trans ?_
  calc ∫ a : ℝ × ℝ, ‖iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) x‖
        ∂(volume : Measure (ℝ × ℝ))
      ≤ ∫ a : ℝ × ℝ, (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) *
          (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
            (1 + ‖x‖) ^ (-(4 + (n:ℝ)))))
          ∂(volume : Measure (ℝ × ℝ)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => norm_nonneg _)
          (hint.mul_const _)
          (Filter.Eventually.of_forall fun a =>
            famF_deriv_pt c ν χo M hν hχ n C hC0 hC m hPm t ht i a x hx)
    _ = (∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) *
          (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
            (1 + ‖x‖) ^ (-(4 + (n:ℝ))))) :=
        integral_mul_const _ _

/-- Componentwise bound of the `n`-th derivative of the zero-width Newton field `newtonV` on
the region, for one Cartesian component `i`. -/
theorem newtonV_comp_deriv_bound (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c)
    (hν : 0 < ν) (hμ : 0 < μ) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M)
    (n : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ w : Vec3, w ≠ 0 → ∀ i j k : Fin 3,
      ‖iteratedFDeriv ℝ n (fun x => newtonD3 x i j k) w‖ ≤ C * (Real.sqrt (eucSq w)) ^ (-(4:ℝ) - n))
    (m : ℝ) (hPm : 5 * ν / 6 < m) (i : Fin 3) (x : Vec3) (hx : m ≤ x 0 ^ 2 + x 1 ^ 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec3 => newtonV c ν μ χo M y i) x‖ ≤
      2 * ((∫ t in Ioc (0 : ℝ) 1, t ^ (2 * μ + 2)) *
        ((∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) *
          (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
            (1 + ‖x‖) ^ (-(4 + (n:ℝ))))))) := by
  have hU := isOpen_newtonRegion ν
  have hyU : x ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := lt_of_lt_of_le hPm hx
  have hdomO : UnforcedLeray.L09.LocDominated (volume.restrict (Ioc (0 : ℝ) 1))
      (fun t => newtonFam c ν μ χo M i t) {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
    intro n' y hy
    obtain ⟨s, hs, g, hg, hb⟩ := newtonFamDom c ν μ χo M hc hν hμ hχ hM i n' y hy
    refine ⟨s, hs, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hb t ht
  have hsmoothO : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonFam c ν μ χo M i t)
        {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact newtonFamSmooth c ν μ χo M hc hν hμ hχ hM i t ht
  have hmeasO : ∀ (n' : ℕ), ∀ y ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2},
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n' (newtonFam c ν μ χo M i t) y)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
    fun n' y hy => newtonFamMeas c ν μ χo M hc hν hμ hχ hM i n' y hy
  have hF := UnforcedLeray.L09.contDiffOn_integral (μ := volume.restrict (Ioc (0 : ℝ) 1)) hU
    hsmoothO hmeasO hdomO
  have hscal : (fun y : Vec3 => newtonV c ν μ χo M y i) = (-2 : ℝ) •
      (fun y : Vec3 => ∫ t, newtonFam c ν μ χo M i t y ∂(volume.restrict (Ioc (0 : ℝ) 1))) := by
    funext y
    rfl
  have hsmAt : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun y : Vec3 => ∫ t, newtonFam c ν μ χo M i t y ∂(volume.restrict (Ioc (0 : ℝ) 1))) x :=
    (hF.contDiffAt (hU.mem_nhds hyU)).of_le (by exact_mod_cast le_top)
  rw [hscal, iteratedFDeriv_const_smul_apply hsmAt, norm_smul]
  have h2 : ‖(-2 : ℝ)‖ = 2 := by norm_num
  rw [h2]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = (∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      ‖sigmaM c ν χo M a j k‖) *
        (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
          (1 + ‖x‖) ^ (-(4 + (n:ℝ))))) := ⟨_, rfl⟩
  rw [← hQdef]
  have h1 := UnforcedLeray.L09.norm_iteratedFDeriv_integral_le
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) hU hsmoothO hmeasO hdomO n hyU
  refine h1.trans ?_
  have hcont : Continuous (fun t : ℝ => t ^ (2 * μ + 2) * Q) :=
    (continuous_id.rpow_const fun _ => Or.inr (by linarith)).mul continuous_const
  calc ∫ t, ‖iteratedFDeriv ℝ n (newtonFam c ν μ χo M i t) x‖ ∂(volume.restrict (Ioc (0 : ℝ) 1))
      ≤ ∫ t, t ^ (2 * μ + 2) * Q ∂(volume.restrict (Ioc (0 : ℝ) 1)) :=
        integral_mono_of_nonneg
          ((ae_restrict_mem measurableSet_Ioc).mono fun t _ => norm_nonneg _)
          hcont.integrableOn_Ioc
          ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
            rw [hQdef]
            exact newtonFam_deriv_bound c ν μ χo M hc hν hχ hM n C hC0 hC m hPm i t ht x hx)
    _ = (∫ t in Ioc (0 : ℝ) 1, t ^ (2 * μ + 2)) * Q := integral_mul_const _ _

/-- Vector-valued norm bound from componentwise bounds on `ContinuousMultilinearMap`s. -/
theorem pi_cm_norm_le {k : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vec3) Vec3)
    (M : ℝ) (h : ∀ i : Fin 3,
      ‖(ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).compContinuousMultilinearMap T‖ ≤ M) :
    ‖T‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (h 0)
  refine ContinuousMultilinearMap.opNorm_le_bound hM (fun m => ?_)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hM (Finset.prod_nonneg fun j _ => norm_nonneg _))).2
    (fun i => ?_)
  have h1 := ContinuousMultilinearMap.le_opNorm
    ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).compContinuousMultilinearMap T) m
  have h2 : ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).compContinuousMultilinearMap T) m
      = T m i := rfl
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (h i) (Finset.prod_nonneg fun j _ => norm_nonneg _))


/-- Vector-valued bound for the zero-width Newton field: each component bound gives the bound
for `iteratedFDeriv` of `newtonV` on the region. -/
theorem newtonV_iter_le (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c) (hν : 0 < ν)
    (hμ : 0 < μ) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (n : ℕ) (C : ℝ)
    (hC0 : 0 ≤ C)
    (hC : ∀ w : Vec3, w ≠ 0 → ∀ i j k : Fin 3,
      ‖iteratedFDeriv ℝ n (fun x => newtonD3 x i j k) w‖ ≤ C * (Real.sqrt (eucSq w)) ^ (-(4:ℝ) - n))
    (m : ℝ) (hPm : 5 * ν / 6 < m) (x : Vec3) (hx : m ≤ x 0 ^ 2 + x 1 ^ 2) :
    ‖iteratedFDeriv ℝ n (newtonV c ν μ χo M) x‖ ≤
      2 * ((∫ t in Ioc (0 : ℝ) 1, t ^ (2 * μ + 2)) *
        ((∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) *
          (C * ((Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2)) ^ (4 + (n:ℝ)) *
            (1 + ‖x‖) ^ (-(4 + (n:ℝ))))))) := by
  have hU := isOpen_newtonRegion ν
  have hyU : x ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := lt_of_lt_of_le hPm hx
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonV c ν μ χo M)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
    newtonVSmooth c ν μ χo M hc hν hμ hχ hM
  apply pi_cm_norm_le
  intro i
  have hsmW : ContDiffWithinAt ℝ (n : WithTop ℕ∞) (newtonV c ν μ χo M)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} x :=
    (hsm.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)
  have hW := ContinuousLinearMap.iteratedFDerivWithin_comp_left
    (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ) hsmW hU.uniqueDiffOn hyU (le_refl _)
  rw [iteratedFDerivWithin_of_isOpen n hU hyU, iteratedFDerivWithin_of_isOpen n hU hyU] at hW
  rw [← hW]
  exact newtonV_comp_deriv_bound c ν μ χo M hc hν hμ hχ hM n C hC0 hC m hPm i x hx

theorem xsYoungWDecay_aux : XSYoungWDecay := by
  intro c ν ε μ χo M hc hν hε hμ hχ hM a ha k
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 4 + (k : ℝ) := ⟨_, rfl⟩
  rw [← hp]
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  obtain ⟨C0, hCk⟩ := newtonD3_bound k
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Vec3, w ≠ 0 → ∀ i j k' : Fin 3,
      ‖iteratedFDeriv ℝ k (fun x => newtonD3 x i j k') w‖ ≤
        C * (Real.sqrt (eucSq w)) ^ (-(4:ℝ) - k) := by
    refine ⟨|C0|, abs_nonneg _, fun w hw i j k' => ?_⟩
    exact (hCk w hw i j k').2.trans
      (mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ε ^ 2 * a := ⟨_, rfl⟩
  have hPm : 5 * ν / 6 < m := by
    have h6 : (0 : ℝ) < 6 * ε ^ 2 := by positivity
    have h := (div_lt_iff₀ h6).1 ha
    rw [hmdef]
    nlinarith
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * μ + 2) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∫ b : ℝ × ℝ, ∑ j : Fin 3, ∑ k' : Fin 3,
      ‖sigmaM c ν χo M b j k'‖ := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.sqrt (2 * kconst (5 * ν / 6) m ^ 2) := ⟨_, rfl⟩
  have hI : 0 ≤ I := by
    rw [hIdef]
    exact setIntegral_nonneg measurableSet_Ioc (fun t ht => Real.rpow_nonneg ht.1.le _)
  have hB : 0 ≤ B := by
    rw [hBdef]
    exact integral_nonneg fun b => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k' _ => norm_nonneg _
  have hL : 0 < L := by
    rw [hLdef]
    exact Real.sqrt_pos.2 (mul_pos two_pos (pow_pos (kconst_pos _ _ (by positivity) hPm) 2))
  obtain ⟨δ', hδ'def⟩ : ∃ d : ℝ, d = min 1 ε := ⟨_, rfl⟩
  have hδ'pos : 0 < δ' := by rw [hδ'def]; exact lt_min one_pos hε
  have hδ'leε : δ' ≤ ε := by rw [hδ'def]; exact min_le_right _ _
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = ε ^ 2 * (2 * (I * (B * (C * (L ^ p * δ' ^ (-p))))) * ε ^ k) :=
    ⟨_, rfl⟩
  refine ⟨Cf, fun w hw => ?_⟩
  have hcyl : cylR w ^ 2 = w 0 ^ 2 + w 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hxq : (ε • w) 0 ^ 2 + (ε • w) 1 ^ 2 = ε ^ 2 * (w 0 ^ 2 + w 1 ^ 2) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hxm : m ≤ (ε • w) 0 ^ 2 + (ε • w) 1 ^ 2 := by
    rw [hxq, hmdef, ← hcyl]
    exact mul_le_mul_of_nonneg_left hw (by positivity)
  have hbound := newtonV_iter_le c ν μ χo M hc hν hμ hχ hM k C hC0 hC m hPm (ε • w) hxm
  rw [← hIdef, ← hBdef, ← hLdef, ← hp] at hbound
  obtain ⟨Lε, hLε⟩ : ∃ Lε : Vec3 →L[ℝ] Vec3, Lε = ε • ContinuousLinearMap.id ℝ Vec3 :=
    ⟨_, rfl⟩
  have hLapp : ∀ y : Vec3, Lε y = ε • y := by
    intro y
    rw [hLε]
    simp
  have hLnorm : ‖Lε‖ ≤ ε := by
    rw [hLε, norm_smul, Real.norm_of_nonneg hε.le]
    calc ε * ‖ContinuousLinearMap.id ℝ Vec3‖ ≤ ε * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hε.le
      _ = ε := mul_one ε
  have hyoung : youngW c ν ε μ χo M = (ε ^ 2) • (newtonV c ν μ χo M ∘ Lε) := by
    funext y
    simp only [youngW, Pi.smul_apply, Function.comp_apply, hLapp]
  have hU := isOpen_newtonRegion ν
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonV c ν μ χo M)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
    newtonVSmooth c ν μ χo M hc hν hμ hχ hM
  have hLw : Lε w ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
    rw [hLapp]
    exact lt_of_lt_of_le hPm hxm
  have hpre : IsOpen (Lε ⁻¹' {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2}) :=
    hU.preimage Lε.continuous
  have hcomp : iteratedFDeriv ℝ k (newtonV c ν μ χo M ∘ Lε) w =
      (iteratedFDeriv ℝ k (newtonV c ν μ χo M) (Lε w)).compContinuousLinearMap (fun _ => Lε) := by
    have hW := ContinuousLinearMap.iteratedFDerivWithin_comp_right Lε hsm hU.uniqueDiffOn
      hpre.uniqueDiffOn hLw (i := k) (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen k hpre hLw,
      iteratedFDerivWithin_of_isOpen k hU hLw] at hW
    exact hW
  have hsmAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonV c ν μ χo M ∘ Lε) w := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonV c ν μ χo M) (Lε w) :=
      hsm.contDiffAt (hU.mem_nhds hLw)
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Lε w := Lε.contDiff.contDiffAt
    exact h1.comp w h2
  have hsmK : ContDiffAt ℝ (k : WithTop ℕ∞) (newtonV c ν μ χo M ∘ Lε) w :=
    hsmAt.of_le (by exact_mod_cast le_top)
  have hnormc : ‖(iteratedFDeriv ℝ k (newtonV c ν μ χo M) (Lε w)).compContinuousLinearMap
      (fun _ => Lε)‖ ≤ ‖iteratedFDeriv ℝ k (newtonV c ν μ χo M) (Lε w)‖ * ε ^ k := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hLnorm k) (norm_nonneg _)
  have hT : ‖iteratedFDeriv ℝ k (newtonV c ν μ χo M) (Lε w)‖ ≤
      2 * (I * (B * (C * (L ^ p * (1 + ‖ε • w‖) ^ (-p))))) := by
    rw [hLapp]
    exact hbound
  have hrp : (1 + ‖ε • w‖) ^ (-p) ≤ δ' ^ (-p) * (1 + ‖w‖) ^ (-p) := by
    have hsc : δ' * (1 + ‖w‖) ≤ 1 + ‖ε • w‖ := by
      rw [norm_smul, Real.norm_of_nonneg hε.le]
      nlinarith [mul_le_mul_of_nonneg_right hδ'leε (norm_nonneg w), min_le_left 1 ε]
    have hpos : 0 < δ' * (1 + ‖w‖) := mul_pos hδ'pos (by positivity)
    calc (1 + ‖ε • w‖) ^ (-p) ≤ (δ' * (1 + ‖w‖)) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos hpos hsc (by linarith)
      _ = δ' ^ (-p) * (1 + ‖w‖) ^ (-p) := Real.mul_rpow hδ'pos.le (by positivity)
  have hfin2 : 2 * (I * (B * (C * (L ^ p * (1 + ‖ε • w‖) ^ (-p))))) ≤
      2 * (I * (B * (C * (L ^ p * (δ' ^ (-p) * (1 + ‖w‖) ^ (-p)))))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ hI
    refine mul_le_mul_of_nonneg_left ?_ hB
    refine mul_le_mul_of_nonneg_left ?_ hC0
    exact mul_le_mul_of_nonneg_left hrp (Real.rpow_nonneg hL.le _)
  rw [hyoung, iteratedFDeriv_const_smul_apply hsmK, norm_smul,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2), hcomp, hCf]
  calc ε ^ 2 * ‖(iteratedFDeriv ℝ k (newtonV c ν μ χo M) (Lε w)).compContinuousLinearMap
          (fun _ => Lε)‖
      ≤ ε ^ 2 * (2 * (I * (B * (C * (L ^ p * (1 + ‖ε • w‖) ^ (-p))))) * ε ^ k) :=
        mul_le_mul_of_nonneg_left
          (hnormc.trans (mul_le_mul_of_nonneg_right hT (pow_nonneg hε.le k))) (sq_nonneg ε)
    _ ≤ ε ^ 2 * (2 * (I * (B * (C * (L ^ p * (δ' ^ (-p) * (1 + ‖w‖) ^ (-p))))))  * ε ^ k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfin2 (pow_nonneg hε.le k))
          (sq_nonneg ε)
    _ = ε ^ 2 * (2 * (I * (B * (C * (L ^ p * δ' ^ (-p))))) * ε ^ k) * (1 + ‖w‖) ^ (-p) := by
        ring

end YoungDecay

theorem xsYoungWDecay : XSYoungWDecay := YoungDecay.xsYoungWDecay_aux

end UnforcedLeray.Short.PartIIIb.Concrete
