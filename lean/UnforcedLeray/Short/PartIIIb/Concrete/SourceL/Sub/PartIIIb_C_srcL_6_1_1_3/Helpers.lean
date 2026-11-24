import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_4
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_5
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Shared helpers for the Newton-family leaves `PartIII-b:C/srcL/6/1/1/1` and `/3`

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
For a fixed `t ∈ (0,1]` and `a ∈ ℝ²` the integrand of `newtonFam` is the family
`famF t a z = Σ_{jk} ∂_i∂_j∂_k N(z - t(a,0)) Σ_M(a)_{jk}`.  On the region `U = {5ν/6 < z₀²+z₁²}`:
* the kernel argument `z - t(a,0)` stays off the axis when `a₀²+a₁² < 5ν/6` (`kernel_arg_ne_zero`),
  and `Σ_M(a) = 0` otherwise (`sigmaM_eq_zero_of_ge`), so each `famF t a` is `C^∞` on `U`;
* the iterated derivatives are bounded uniformly for `z` near a point of `U` and all `a`, `t`
  (`locDom_unif`), by compactness of a set of kernel arguments avoiding `0`;
* the iterated derivative of `famF t a` is a finite sum of `Σ_M(a)_{jk} • D^n K_{ijk}(z - t(a,0))`
  (`fam_iter_eq`), which is measurable in `a` (`famF_aesm`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.NewtonFam

/-- The integrand of `newtonFam` as a function of the evaluation point `z`, for a fixed `a`. -/
def famF (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (t : ℝ) (i : Fin 3) (a : ℝ × ℝ) :
    Vec3 → ℝ :=
  fun z => ∑ j, ∑ k, newtonD3 (z - t • embPlane a) i j k * sigmaM c ν χo M a j k

theorem embPlane_apply0 (a : ℝ × ℝ) (t : ℝ) (z : Vec3) :
    (z - t • embPlane a) 0 = z 0 - t * a.1 := by
  simp [embPlane]

theorem embPlane_apply1 (a : ℝ × ℝ) (t : ℝ) (z : Vec3) :
    (z - t • embPlane a) 1 = z 1 - t * a.2 := by
  simp [embPlane]

theorem embPlane_apply2 (a : ℝ × ℝ) (t : ℝ) (z : Vec3) :
    (z - t • embPlane a) 2 = z 2 := by
  simp [embPlane]

theorem embPlane_continuous : Continuous embPlane := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [embPlane] <;> fun_prop

/-- Algebra of the kernel argument: for `0 ≤ t ≤ 1` and `|a'| ≤ |y'|` in the plane,
`|y' - t a'| ≥ |y'| - |a'|`, squared. -/
theorem kernel_sq_lower (y0 y1 a0 a1 t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hab : a0 ^ 2 + a1 ^ 2 ≤ y0 ^ 2 + y1 ^ 2) :
    (Real.sqrt (y0 ^ 2 + y1 ^ 2) - Real.sqrt (a0 ^ 2 + a1 ^ 2)) ^ 2
      ≤ (y0 - t * a0) ^ 2 + (y1 - t * a1) ^ 2 := by
  have hA2 : Real.sqrt (y0 ^ 2 + y1 ^ 2) ^ 2 = y0 ^ 2 + y1 ^ 2 := Real.sq_sqrt (by positivity)
  have hB2 : Real.sqrt (a0 ^ 2 + a1 ^ 2) ^ 2 = a0 ^ 2 + a1 ^ 2 := Real.sq_sqrt (by positivity)
  have hA0 : 0 ≤ Real.sqrt (y0 ^ 2 + y1 ^ 2) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ Real.sqrt (a0 ^ 2 + a1 ^ 2) := Real.sqrt_nonneg _
  have hBA : Real.sqrt (a0 ^ 2 + a1 ^ 2) ≤ Real.sqrt (y0 ^ 2 + y1 ^ 2) := Real.sqrt_le_sqrt hab
  set A := Real.sqrt (y0 ^ 2 + y1 ^ 2) with hAdef
  set B := Real.sqrt (a0 ^ 2 + a1 ^ 2) with hBdef
  have hd : y0 * a0 + y1 * a1 ≤ A * B := by
    have h1 : (y0 * a0 + y1 * a1) ^ 2 ≤ (A * B) ^ 2 := by
      rw [mul_pow, hA2, hB2]
      nlinarith [sq_nonneg (y0 * a1 - y1 * a0)]
    nlinarith [mul_nonneg hA0 hB0]
  have key : (y0 - t * a0) ^ 2 + (y1 - t * a1) ^ 2
      = A ^ 2 - 2 * t * (y0 * a0 + y1 * a1) + t ^ 2 * B ^ 2 := by
    rw [hA2, hB2]; ring
  have h2 : A ^ 2 - 2 * t * (A * B) + t ^ 2 * B ^ 2 ≤ (y0 - t * a0) ^ 2 + (y1 - t * a1) ^ 2 := by
    rw [key]
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 hd)]
  have h3 : 0 ≤ 2 * A - B * (1 + t) := by
    nlinarith [mul_nonneg hB0 (sub_nonneg.2 ht1)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ht1) hB0) h3]

/-- Uniform version: the plane part of `y - t(a,0)` is bounded below for `a` in the disc of
squared radius `P` and `y` outside it (squared radius `m > P`). -/
theorem kernel_sq_uniform (y0 y1 a0 a1 t P m : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hPm : P < m) (hy : m ≤ y0 ^ 2 + y1 ^ 2) (ha : a0 ^ 2 + a1 ^ 2 < P) :
    (Real.sqrt m - Real.sqrt P) ^ 2 ≤ (y0 - t * a0) ^ 2 + (y1 - t * a1) ^ 2 := by
  have hab : a0 ^ 2 + a1 ^ 2 ≤ y0 ^ 2 + y1 ^ 2 := by linarith
  have h1 : Real.sqrt m - Real.sqrt P ≤ Real.sqrt (y0 ^ 2 + y1 ^ 2) - Real.sqrt (a0 ^ 2 + a1 ^ 2) := by
    have := Real.sqrt_le_sqrt hy
    have := Real.sqrt_le_sqrt ha.le
    linarith
  have h0 : 0 ≤ Real.sqrt m - Real.sqrt P := by
    have := Real.sqrt_le_sqrt hPm.le
    linarith
  have h2 : (Real.sqrt m - Real.sqrt P) ^ 2
      ≤ (Real.sqrt (y0 ^ 2 + y1 ^ 2) - Real.sqrt (a0 ^ 2 + a1 ^ 2)) ^ 2 := by
    nlinarith
  exact h2.trans (kernel_sq_lower y0 y1 a0 a1 t ht0 ht1 hab)

/-- The kernel argument `y - t(a,0)` is nonzero when `a` is in the disc and `y` is outside it. -/
theorem kernel_arg_ne_zero (y : Vec3) (a : ℝ × ℝ) (t P : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : a.1 ^ 2 + a.2 ^ 2 < P) (hy : P < y 0 ^ 2 + y 1 ^ 2) :
    y - t • embPlane a ≠ 0 := by
  intro h
  have e0 : y 0 - t * a.1 = 0 := by
    have := congrArg (fun w : Vec3 => w 0) h
    simpa [embPlane] using this
  have e1 : y 1 - t * a.2 = 0 := by
    have := congrArg (fun w : Vec3 => w 1) h
    simpa [embPlane] using this
  have hu := kernel_sq_uniform (y 0) (y 1) a.1 a.2 t P (y 0 ^ 2 + y 1 ^ 2) ht0 ht1 hy le_rfl ha
  rw [e0, e1] at hu
  have hP0 : (0 : ℝ) ≤ P := le_trans (by positivity) ha.le
  have hlt : Real.sqrt P < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := Real.sqrt_lt_sqrt hP0 hy
  nlinarith [pow_pos (sub_pos.2 hlt) 2]

/-- The kernel point set: a compact set of arguments of norm at most `R` whose cylindrical
radius is at least `δ`. -/
def kerSet (δ R : ℝ) : Set Vec3 :=
  Metric.closedBall (0 : Vec3) R ∩ {w : Vec3 | δ ^ 2 ≤ w 0 ^ 2 + w 1 ^ 2}

theorem isCompact_kerSet (δ R : ℝ) : IsCompact (kerSet δ R) :=
  (isCompact_closedBall (0 : Vec3) R).inter_right (isClosed_le continuous_const (by fun_prop))

theorem kerSet_ne_zero {δ R : ℝ} (hδ : 0 < δ) : kerSet δ R ⊆ {w : Vec3 | w ≠ 0} := by
  intro w hw
  have hw2 : δ ^ 2 ≤ w 0 ^ 2 + w 1 ^ 2 := hw.2
  intro h0
  rw [h0] at hw2
  simp only [Pi.zero_apply] at hw2
  nlinarith [pow_pos hδ 2]

/-- The third-order kernel is `C^∞` off the origin. -/
theorem ker_contDiffAt (i j k : Fin 3) {w : Vec3} (hw : w ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Vec3 => newtonD3 x i j k) w :=
  (newtonD3_contDiffOn i j k).contDiffAt ((isOpen_ne : IsOpen {x : Vec3 | x ≠ 0}).mem_nhds hw)

theorem ker_iter_cont (n : ℕ) (i j k : Fin 3) :
    ContinuousOn (fun w : Vec3 => iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j k) w)
      {w : Vec3 | w ≠ 0} := by
  intro w hw
  have hA := ((ker_contDiffAt i j k hw).iteratedFDeriv_right (m := 1) (i := n)
    (by exact_mod_cast le_top)).continuousAt
  exact hA.continuousWithinAt

/-- Uniform bound on all `(j,k)` components of the `n`-th derivative of the kernels on `kerSet`. -/
theorem ker_iter_bound_all (n : ℕ) (i : Fin 3) (δ R : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ w ∈ kerSet δ R, ∀ j k : Fin 3,
      ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j k) w‖ ≤ C := by
  have hΦ : ContinuousOn (fun w : Vec3 => ∑ j : Fin 3, ∑ k : Fin 3,
      ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j k) w‖) {w : Vec3 | w ≠ 0} := by
    apply continuousOn_finset_sum
    intro j _
    apply continuousOn_finset_sum
    intro k _
    exact (ker_iter_cont n i j k).norm
  obtain ⟨C, hC⟩ := (isCompact_kerSet δ R).exists_bound_of_continuousOn
    (hΦ.mono (kerSet_ne_zero hδ))
  refine ⟨C, fun w hw j k => ?_⟩
  have h1 : ‖∑ j' : Fin 3, ∑ k' : Fin 3,
      ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j' k') w‖‖ ≤ C := hC w hw
  have h3 : ∑ j' : Fin 3, ∑ k' : Fin 3,
      ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j' k') w‖ ≤ C := by
    rwa [Real.norm_of_nonneg (by positivity)] at h1
  have hA : ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j k) w‖
      ≤ ∑ k' : Fin 3, ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j k') w‖ :=
    Finset.single_le_sum (f := fun k' : Fin 3 =>
      ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j k') w‖)
      (fun k' _ => norm_nonneg _) (Finset.mem_univ k)
  have hB : ∑ k' : Fin 3, ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j k') w‖
      ≤ ∑ j' : Fin 3, ∑ k' : Fin 3, ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j' k') w‖ :=
    Finset.single_le_sum (f := fun j' : Fin 3 =>
      ∑ k' : Fin 3, ‖iteratedFDeriv ℝ n (fun x : Vec3 => newtonD3 x i j' k') w‖)
      (fun j' _ => Finset.sum_nonneg fun k' _ => norm_nonneg _) (Finset.mem_univ j)
  exact hA.trans (hB.trans h3)

/-- Kernel term: `(z ↦ K(z - c) * s)` has `n`-th derivative `s • D^n K(y - c)`. -/
theorem term_contDiffAt (m : ℕ) (i j k : Fin 3) (c : Vec3) (s : ℝ) (y : Vec3) (hne : y - c ≠ 0) :
    ContDiffAt ℝ (m : WithTop ℕ∞) (fun z => newtonD3 (z - c) i j k * s) y := by
  have hK : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => newtonD3 (z - c) i j k) y :=
    (ker_contDiffAt i j k hne).comp y (contDiffAt_id.sub contDiffAt_const)
  exact (hK.of_le (by exact_mod_cast le_top)).mul contDiffAt_const

theorem term_iter (n : ℕ) (i j k : Fin 3) (c : Vec3) (s : ℝ) (y : Vec3) (hne : y - c ≠ 0) :
    iteratedFDeriv ℝ n (fun z => newtonD3 (z - c) i j k * s) y
      = s • iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (y - c) := by
  have hK : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => newtonD3 (z - c) i j k) y :=
    (ker_contDiffAt i j k hne).comp y (contDiffAt_id.sub contDiffAt_const)
  have hf : (fun z => newtonD3 (z - c) i j k * s) = s • (fun z => newtonD3 (z - c) i j k) := by
    funext z
    simp [mul_comm]
  have hcs : iteratedFDeriv ℝ n (fun z => newtonD3 (z - c) i j k) y
      = iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (y - c) :=
    iteratedFDeriv_comp_sub (f := fun w : Vec3 => newtonD3 w i j k) n c y
  rw [hf, iteratedFDeriv_const_smul_apply (hK.of_le (by exact_mod_cast le_top)), hcs]

/-- The iterated derivative of `famF t a` at `y` is a finite sum of scaled kernel derivatives. -/
theorem fam_iter_eq (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (t : ℝ) (i : Fin 3) (n : ℕ)
    (a : ℝ × ℝ) (y : Vec3)
    (h : sigmaM c ν χo M a = 0 ∨ y - t • embPlane a ≠ 0) :
    iteratedFDeriv ℝ n (famF c ν χo M t i a) y =
      ∑ j, ∑ k, sigmaM c ν χo M a j k •
        iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (y - t • embPlane a) := by
  rcases h with h0 | hne
  · unfold famF
    simp [h0]
  · have step1 : ∀ j : Fin 3,
        iteratedFDeriv ℝ n (fun z => ∑ k, newtonD3 (z - t • embPlane a) i j k * sigmaM c ν χo M a j k) y
          = ∑ k, sigmaM c ν χo M a j k •
            iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (y - t • embPlane a) := by
      intro j
      rw [iteratedFDeriv_fun_sum_apply (fun k _ => term_contDiffAt n i j k (t • embPlane a)
        (sigmaM c ν χo M a j k) y hne)]
      exact Finset.sum_congr rfl fun k _ => term_iter n i j k (t • embPlane a) (sigmaM c ν χo M a j k) y hne
    unfold famF
    rw [iteratedFDeriv_fun_sum_apply (fun j _ => ContDiffAt.sum (fun k _ =>
      term_contDiffAt n i j k (t • embPlane a) (sigmaM c ν χo M a j k) y hne))]
    exact Finset.sum_congr rfl fun j _ => step1 j

/-- Each `famF t a` is `C^∞` on the region `U` (for `t ∈ (0,1]`, `χo` an outward cutoff). -/
theorem famF_contDiffOn (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (i : Fin 3) (a : ℝ × ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (famF c ν χo M t i a)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
  by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
  · unfold famF
    refine ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
    refine ContDiffOn.mul ?_ contDiffOn_const
    have hmaps : MapsTo (fun z : Vec3 => z - t • embPlane a)
        {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} {w : Vec3 | w ≠ 0} :=
      fun z hz => kernel_arg_ne_zero z a t (5 * ν / 6) ht.1.le ht.2 ha hz
    exact (newtonD3_contDiffOn i j k).comp (contDiffOn_id.sub contDiffOn_const) hmaps
  · have h0 : sigmaM c ν χo M a = 0 :=
      sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)
    unfold famF
    simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact contDiffOn_const

/-- Entrywise integrability of the Cartesian source. -/
theorem sigma_entry_integrable (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c)
    (hν : 0 < ν) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (j k : Fin 3) :
    Integrable (fun a : ℝ × ℝ => sigmaM c ν χo M a j k) volume := by
  have hmat := (UnforcedLeray.Short.PartIIIb.Concrete.sigmaM_l1 c ν χo hc hν hχ M hM).2.1
  exact MeasureTheory.integrable_pi_iff.1 (MeasureTheory.integrable_pi_iff.1 hmat j) k

theorem sigma_norm_sum_integrable (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c)
    (hν : 0 < ν) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) :
    Integrable (fun a : ℝ × ℝ => ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) volume :=
  integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
    (sigma_entry_integrable c ν χo M hc hν hχ hM j k).norm

/-- Measurability in the parameter `a` of the `n`-th derivative of `famF t a` at `x ∈ U`. -/
theorem famF_aesm (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1)
    (i : Fin 3) (n : ℕ) (x : Vec3) (hx : x ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2}) :
    AEStronglyMeasurable (fun a : ℝ × ℝ => iteratedFDeriv ℝ n (famF c ν χo M t i a) x)
      volume := by
  set S : Set (ℝ × ℝ) := {a : ℝ × ℝ | a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6} with hSdef
  have hS : MeasurableSet S := (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hfun : (fun a : ℝ × ℝ => iteratedFDeriv ℝ n (famF c ν χo M t i a) x) =
      S.indicator (fun a : ℝ × ℝ => ∑ j, ∑ k, sigmaM c ν χo M a j k •
        iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)) := by
    funext a
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha,
        fam_iter_eq c ν χo M t i n a x
          (Or.inr (kernel_arg_ne_zero x a t _ ht.1.le ht.2 ha hx))]
    · rw [Set.indicator_of_notMem ha]
      have h1 : ¬ (a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6) := fun h => ha h
      have h0 : sigmaM c ν χo M a = 0 :=
        sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 h1)
      rw [fam_iter_eq c ν χo M t i n a x (Or.inl h0), h0]
      simp
  rw [hfun, aestronglyMeasurable_indicator_iff hS]
  have hφ : Continuous (fun a : ℝ × ℝ => x - t • embPlane a) := by
    have hE := embPlane_continuous
    fun_prop
  refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  have hσ : AEStronglyMeasurable (fun a : ℝ × ℝ => sigmaM c ν χo M a j k)
      (volume.restrict S) :=
    (sigma_entry_integrable c ν χo M hc hν hχ hM j k).aestronglyMeasurable.restrict
  have hD : AEStronglyMeasurable
      (fun a : ℝ × ℝ => iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a))
      (volume.restrict S) :=
    ContinuousOn.aestronglyMeasurable
      ((ker_iter_cont n i j k).comp hφ.continuousOn
        (fun a ha => kernel_arg_ne_zero x a t _ ht.1.le ht.2 ha hx)) hS
  exact hσ.smul hD

/-- Local uniform domination (`LocDominated`-type bound) of the `n`-th derivatives of `famF t a`
for all `t ∈ (0,1]` at once, on a neighbourhood `s ⊆ U` of `x ∈ U`. -/
theorem locDom_unif (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (i : Fin 3) (n : ℕ) (x : Vec3)
    (hx : x ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2}) :
    ∃ s ∈ nhds x, s ⊆ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} ∧ ∃ C : ℝ,
      ∀ t ∈ Ioc (0 : ℝ) 1, ∀ a : ℝ × ℝ, ∀ y ∈ s,
        ‖iteratedFDeriv ℝ n (famF c ν χo M t i a) y‖
          ≤ (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) * C := by
  have hx' : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2 := hx
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((5 * ν / 6) + (x 0 ^ 2 + x 1 ^ 2)) / 2 := ⟨_, rfl⟩
  have hPm : 5 * ν / 6 < m := by rw [hm]; linarith
  have hmq : m < x 0 ^ 2 + x 1 ^ 2 := by rw [hm]; linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = Real.sqrt m - Real.sqrt (5 * ν / 6) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    have h1 := Real.sqrt_lt_sqrt (by linarith : (0 : ℝ) ≤ 5 * ν / 6) hPm
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = |x 0| + |x 1| + |x 2| + 3 + 5 * ν / 6 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    linarith [abs_nonneg (x 0), abs_nonneg (x 1), abs_nonneg (x 2)]
  obtain ⟨C0, hC0⟩ := ker_iter_bound_all n i δ R hδ
  have hsnhds : {y : Vec3 | m < y 0 ^ 2 + y 1 ^ 2} ∩ Metric.ball x 1 ∈ nhds x :=
    Filter.inter_mem ((isOpen_lt continuous_const (by fun_prop)).mem_nhds
      (show m < x 0 ^ 2 + x 1 ^ 2 from hmq))
      (Metric.ball_mem_nhds x one_pos)
  refine ⟨{y : Vec3 | m < y 0 ^ 2 + y 1 ^ 2} ∩ Metric.ball x 1, hsnhds, ?_, C0, ?_⟩
  · intro y hy
    exact lt_trans hPm hy.1
  intro t ht a y hy
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : t ≤ 1 := ht.2
  obtain ⟨hym, hyb⟩ := hy
  have hy' : 5 * ν / 6 < y 0 ^ 2 + y 1 ^ 2 := lt_trans hPm hym
  have hyc : ∀ j : Fin 3, |y j - x j| < 1 := by
    intro j
    have := (dist_pi_lt_iff one_pos).1 (Metric.mem_ball.1 hyb) j
    simpa [Real.dist_eq] using this
  have hy0 : |y 0| ≤ |x 0| + 1 := by
    have := abs_sub_abs_le_abs_sub (y 0) (x 0)
    linarith [hyc 0]
  have hy1 : |y 1| ≤ |x 1| + 1 := by
    have := abs_sub_abs_le_abs_sub (y 1) (x 1)
    linarith [hyc 1]
  have hy2 : |y 2| ≤ |x 2| + 1 := by
    have := abs_sub_abs_le_abs_sub (y 2) (x 2)
    linarith [hyc 2]
  by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
  · -- the kernel argument lies in `kerSet δ R`
    have hab1 : |a.1| ≤ 1 + 5 * ν / 6 := by
      nlinarith [sq_abs a.1, abs_nonneg a.1, sq_nonneg (|a.1| - 1), sq_nonneg a.2]
    have hab2 : |a.2| ≤ 1 + 5 * ν / 6 := by
      nlinarith [sq_abs a.2, abs_nonneg a.2, sq_nonneg (|a.2| - 1), sq_nonneg a.1]
    have hta1 : |t * a.1| ≤ |a.1| := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
    have hta2 : |t * a.2| ≤ |a.2| := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
    have hcoord0 : |y 0 - t * a.1| ≤ R := by
      have hA := abs_le.1 hy0
      have hB := abs_le.1 (hta1.trans hab1)
      rw [abs_le]
      constructor
      · linarith [hA.1, hB.2, abs_nonneg (x 1), abs_nonneg (x 2)]
      · linarith [hA.2, hB.1, abs_nonneg (x 1), abs_nonneg (x 2)]
    have hcoord1 : |y 1 - t * a.2| ≤ R := by
      have hA := abs_le.1 hy1
      have hB := abs_le.1 (hta2.trans hab2)
      rw [abs_le]
      constructor
      · linarith [hA.1, hB.2, abs_nonneg (x 0), abs_nonneg (x 2)]
      · linarith [hA.2, hB.1, abs_nonneg (x 0), abs_nonneg (x 2)]
    have hcoord2 : |y 2| ≤ R := by
      linarith [abs_nonneg (x 0), abs_nonneg (x 1), abs_nonneg (x 2), hy2]
    have hnorm : ‖y - t • embPlane a‖ ≤ R := by
      rw [pi_norm_le_iff_of_nonneg hR0]
      intro j
      fin_cases j
      · show ‖(y - t • embPlane a) 0‖ ≤ R
        rw [Real.norm_eq_abs, embPlane_apply0]
        exact hcoord0
      · show ‖(y - t • embPlane a) 1‖ ≤ R
        rw [Real.norm_eq_abs, embPlane_apply1]
        exact hcoord1
      · show ‖(y - t • embPlane a) 2‖ ≤ R
        rw [Real.norm_eq_abs, embPlane_apply2]
        exact hcoord2
    have hsq : δ ^ 2 ≤ (y - t • embPlane a) 0 ^ 2 + (y - t • embPlane a) 1 ^ 2 := by
      rw [embPlane_apply0, embPlane_apply1, hδdef]
      exact kernel_sq_uniform (y 0) (y 1) a.1 a.2 t (5 * ν / 6) m ht0 ht1 hPm hym.le ha
    have hmem : y - t • embPlane a ∈ kerSet δ R :=
      ⟨mem_closedBall_zero_iff.2 hnorm, hsq⟩
    have hne : y - t • embPlane a ≠ 0 :=
      kernel_arg_ne_zero y a t (5 * ν / 6) ht0 ht1 ha hy'
    rw [fam_iter_eq c ν χo M t i n a y (Or.inr hne)]
    simp only [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC0 _ hmem j k) (norm_nonneg _)
  · have h1 : ¬ (a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6) := ha
    have h0 : sigmaM c ν χo M a = 0 :=
      sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 h1)
    rw [fam_iter_eq c ν χo M t i n a y (Or.inl h0), h0]
    simp

/-- `famF t a` satisfies the `LocDominated` hypothesis of the parametric integral theorem. -/
theorem famF_locDom (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (hc : 0 < c) (hM : OldThinFinite c ν M) (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) (i : Fin 3) :
    UnforcedLeray.L09.LocDominated (volume : Measure (ℝ × ℝ)) (famF c ν χo M t i)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
  unfold UnforcedLeray.L09.LocDominated
  intro n x hx
  obtain ⟨s, hs, _, C, hC⟩ := locDom_unif c ν χo M hν hχ i n x hx
  refine ⟨s, hs, fun a => (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) * C,
    (sigma_norm_sum_integrable c ν χo M hc hν hχ hM).mul_const C, ?_⟩
  exact Filter.Eventually.of_forall fun a y hy => hC t ht a y hy

/-- The parametric integral `∫ famF t a dа` is `C^∞` on the region `U`. -/
theorem famF_integral_contDiffOn (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c)
    (hν : 0 < ν) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) (i : Fin 3) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Vec3 => ∫ a : ℝ × ℝ, famF c ν χo M t i a y ∂(volume : Measure (ℝ × ℝ)))
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
  UnforcedLeray.L09.contDiffOn_integral (μ := (volume : Measure (ℝ × ℝ)))
    (isOpen_newtonRegion ν)
    (Filter.Eventually.of_forall fun a => famF_contDiffOn c ν χo M hν hχ t ht i a)
    (fun n x hx => famF_aesm c ν χo M hc hν hχ hM t ht i n x hx)
    (famF_locDom c ν χo M hν hχ hc hM t ht i)

end UnforcedLeray.Short.PartIIIb.Concrete.NewtonFam
