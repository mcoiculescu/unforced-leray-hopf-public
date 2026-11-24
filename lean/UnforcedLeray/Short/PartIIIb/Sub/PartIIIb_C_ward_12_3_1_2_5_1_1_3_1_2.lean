import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_2

/-!
# `InletFnFarOfJets` from four product-rule bounds and one absorption inequality

Source `the November 2 reference manuscript`
lines 2542-2548, 2563-2569, 1206-1222.

`inletFn = -∂_j(L₀E + (raw·∇)E + (E·∇)raw)`; the four `Prop`s below are the Leibniz bounds on
slices `x ↦ F(τ,x)` and an inequality of reals; `inletFnFarOfJets_of` assembles them.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params advT)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leibniz bound for `∂_j L₀E` on a slice (2542-2548): `L₀E = ∂_τE - ½ y·∇E - νΔE - ½E`, so
`∂_jL₀E` involves `∂_j∂_τE` (order 1 of `∂_τE`), `∂_jE`, `y ∂_j∂_kE` and `∂_jΔE`. -/
def L0PartBound : Prop :=
  ∀ (ν : ℝ) (E : ℝ × UnforcedLeray.Space → CVec3), ContDiff ℝ ∞ E →
    ∀ (j : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space),
      ‖dy j (UnforcedLeray.B0411.L0 ν E) (τ, y)‖ ≤ 4 * (1 + |ν|) *
        (‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => dτ E (τ, x)) y‖ +
          ‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => E (τ, x)) y‖ +
          ‖y‖ * ‖iteratedFDeriv ℝ 2 (fun x : UnforcedLeray.Space => E (τ, x)) y‖ +
          ‖iteratedFDeriv ℝ 3 (fun x : UnforcedLeray.Space => E (τ, x)) y‖)

/-- Leibniz bound for `∂_j((U·∇)E)` on a slice: `∑ₖ (∂_jU_k ∂_kE + U_k ∂_j∂_kE)`. -/
def AdvPartBound : Prop :=
  ∀ (U E : ℝ × UnforcedLeray.Space → CVec3), ContDiff ℝ ∞ U → ContDiff ℝ ∞ E →
    ∀ (j : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space),
      ‖dy j (advT U E) (τ, y)‖ ≤ 3 *
        (‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => U (τ, x)) y‖ *
            ‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => E (τ, x)) y‖ +
          ‖iteratedFDeriv ℝ 0 (fun x : UnforcedLeray.Space => U (τ, x)) y‖ *
            ‖iteratedFDeriv ℝ 2 (fun x : UnforcedLeray.Space => E (τ, x)) y‖)

/-- Leibniz bound for `∂_j((E·∇)V)` on a slice: `∑ₖ (∂_jE_k ∂_kV + E_k ∂_j∂_kV)`. -/
def GradPartBound : Prop :=
  ∀ (V : ℝ → UnforcedLeray.SpatialField) (E : ℝ × UnforcedLeray.Space → CVec3),
    ContDiff ℝ ∞ E → ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) →
    ∀ (j : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space),
      ‖dy j (gradAlong V E) (τ, y)‖ ≤ 3 *
        (‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => E (τ, x)) y‖ *
            ‖iteratedFDeriv ℝ 1 (V τ) y‖ +
          ‖iteratedFDeriv ℝ 0 (fun x : UnforcedLeray.Space => E (τ, x)) y‖ *
            ‖iteratedFDeriv ℝ 2 (V τ) y‖)

/-- `realC` (coordinatewise inclusion `ℝ³ → ℂ³`, a real-linear isometry) does not increase the
norms of the iterated derivatives. -/
def RealCBound : Prop :=
  ∀ (r : UnforcedLeray.Space → UnforcedLeray.Space) (k : ℕ) (y : UnforcedLeray.Space),
    ContDiff ℝ ∞ r →
      ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => UnforcedLeray.B0412.realC (r x)) y‖ ≤
        ‖iteratedFDeriv ℝ k r y‖

/-- The weight bookkeeping (2542-2548, `N = 3`, `ϱ ≥ 1`, `w = 1 + |y₃|/ϱ ≥ 1`, `‖y‖ ≤ ϱ w`):
every term of the Leibniz bounds is at most `C ϱ^{-3} w^{-2}`; the terms `b1, a1, ay·a2, a3` are
each `≤ C ϱ^{-3}w^{-2}` and the raw factors are `≤ B`. -/
def FarAbsorb : Prop :=
  ∀ (ν C B ϱ w ay a0 a1 a2 a3 b1 c0 c1 c2 : ℝ),
    0 ≤ C → 0 ≤ B → 1 ≤ ϱ → 1 ≤ w → 0 ≤ ay → ay ≤ ϱ * w →
    0 ≤ a0 → 0 ≤ a1 → 0 ≤ a2 → 0 ≤ a3 → 0 ≤ b1 → 0 ≤ c0 → 0 ≤ c1 → 0 ≤ c2 →
    a0 ≤ C * (ϱ ^ (-(3 + ((0 : ℕ) : ℝ))) * w ^ (-((3 : ℕ) : ℝ))) →
    a1 ≤ C * (ϱ ^ (-(3 + ((1 : ℕ) : ℝ))) * w ^ (-((3 : ℕ) : ℝ))) →
    a2 ≤ C * (ϱ ^ (-(3 + ((2 : ℕ) : ℝ))) * w ^ (-((3 : ℕ) : ℝ))) →
    a3 ≤ C * (ϱ ^ (-(3 + ((3 : ℕ) : ℝ))) * w ^ (-((3 : ℕ) : ℝ))) →
    b1 ≤ C * (ϱ ^ (-(2 + ((1 : ℕ) : ℝ))) * w ^ (-((3 : ℕ) : ℝ))) →
    c0 ≤ B → c1 ≤ B → c2 ≤ B →
    30 * (1 + |ν|) * (b1 + a1 + ay * a2 + a3 + (c0 + c1 + c2) * (a0 + a1 + a2)) ≤
      30 * (1 + |ν|) * (C * (4 + 9 * B)) * (ϱ ^ (-3 : ℝ) * w ^ (-2 : ℝ))

theorem inletSrc_parts_contDiff {p : Params} {i : Fin 2}
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hR : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)) :
    ContDiff ℝ ∞ (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) ∧
    ContDiff ℝ ∞ (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) ∧
    ContDiff ℝ ∞ (gradAlong p.raw (p.Efun i)) := by
  have hL : ContDiff ℝ ∞ (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) := by
    unfold UnforcedLeray.B0411.L0 UnforcedLeray.B0411.T0
    exact (((contDiff_dτ hE).sub ((contDiff_radialT hE).const_smul _)).sub
      ((contDiff_lapT hE).const_smul _)).sub (hE.const_smul _)
  have hU : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2)) := contDiff_realC_meas.comp hR
  have hA : ContDiff ℝ ∞ (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) := by
    unfold advT
    exact ContDiff.sum fun k _ =>
      ((contDiff_piLp_apply (p := 2) (i := k)).comp hU).smul (UnforcedLeray.PhaseSpace.contDiff_dy hE k)
  have hG : ContDiff ℝ ∞ (gradAlong p.raw (p.Efun i)) := by
    have := inletSrc_contDiff hE hR
    unfold gradAlong
    apply (contDiff_piLp 2).2
    intro l
    show ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => ∑ k : Fin 3, p.Efun i x k *
      ((fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) l : ℝ) : ℂ))
    refine ContDiff.sum fun k _ => ?_
    have h1 : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.Efun i x k) :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp hE
    have h2 : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
        fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) l) := by
      have h3 : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
          fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) x (0, EuclideanSpace.single k 1)) :=
        (hR.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have h4 := (contDiff_piLp_apply (p := 2) (i := l)).comp h3
      have heq : (fun x : ℝ × UnforcedLeray.Space =>
          fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) l) = fun x =>
          (fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) x
            (0, EuclideanSpace.single k 1)) l := by
        funext x
        have := fderiv_slice_meas (R := fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2)
          (hR.differentiable (by simp)) x.1 x.2 (EuclideanSpace.single k 1)
        exact congrArg (fun v => v l) this
      rw [heq]
      exact h4
    exact h1.mul (Complex.ofRealCLM.contDiff.comp h2)
  exact ⟨hL, hA, hG⟩

theorem inletFn_eq {p : Params} {i : Fin 2} (j : Fin 3)
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hR : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2))
    (τ : ℝ) (y : UnforcedLeray.Space) :
    inletFn p i j (τ, y) =
      -(dy j (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) (τ, y) +
        dy j (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) (τ, y) +
        dy j (gradAlong p.raw (p.Efun i)) (τ, y)) := by
  obtain ⟨hL0, hA0, hG0⟩ := inletSrc_parts_contDiff hE hR
  have h1 : Differentiable ℝ (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) := hL0.differentiable (by simp)
  have h2 : Differentiable ℝ (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) :=
    hA0.differentiable (by simp)
  have h3 : Differentiable ℝ (gradAlong p.raw (p.Efun i)) := hG0.differentiable (by simp)
  have h12 := dy_add h1 h2 j
  have h123 := dy_add (h1.add h2) h3 j
  unfold inletFn inletSrc
  simp only [Pi.neg_apply]
  rw [h123, h12]
  rfl

/-- Pointwise bound on `inletFn` from the four Leibniz bounds. -/
theorem inletFn_pointwise_of (hL : L0PartBound) (hA : AdvPartBound) (hG : GradPartBound)
    (hC : RealCBound) {p : Params} {i : Fin 2} (j : Fin 3)
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hR : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2))
    (τ : ℝ) (y : UnforcedLeray.Space) :
    ‖inletFn p i j (τ, y)‖ ≤ 30 * (1 + |p.ν|) *
      (‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => dτ (p.Efun i) (τ, x)) y‖ +
        ‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ +
        ‖y‖ * ‖iteratedFDeriv ℝ 2 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ +
        ‖iteratedFDeriv ℝ 3 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ +
        (‖iteratedFDeriv ℝ 0 (p.raw τ) y‖ + ‖iteratedFDeriv ℝ 1 (p.raw τ) y‖ +
            ‖iteratedFDeriv ℝ 2 (p.raw τ) y‖) *
          (‖iteratedFDeriv ℝ 0 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ +
            ‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ +
            ‖iteratedFDeriv ℝ 2 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖)) := by
  obtain ⟨hL0, hA0, hG0⟩ := inletSrc_parts_contDiff hE hR
  have hU : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2)) := contDiff_realC_meas.comp hR
  have hRτ : ContDiff ℝ ∞ (p.raw τ) := by
    have this : ContDiff ℝ ∞ (fun x : UnforcedLeray.Space => ((τ, x) : ℝ × UnforcedLeray.Space)) :=
      contDiff_const.prodMk contDiff_id
    have hc := hR.comp this
    have heq : (fun x : UnforcedLeray.Space => p.raw τ x) =
        ((fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) ∘
          fun x : UnforcedLeray.Space => ((τ, x) : ℝ × UnforcedLeray.Space)) := by
      funext x; rfl
    rw [← heq] at hc
    exact hc
  have e1 := inletFn_eq j hE hR τ y
  have b1 := hL p.ν (p.Efun i) hE j τ y
  have b2 := hA _ (p.Efun i) hU hE j τ y
  have b3 := hG p.raw (p.Efun i) hE hR j τ y
  have r0 := hC (p.raw τ) 0 y hRτ
  have r1 := hC (p.raw τ) 1 y hRτ
  have n0 := norm_nonneg (iteratedFDeriv ℝ 0 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y)
  have n1 := norm_nonneg (iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y)
  have n2 := norm_nonneg (iteratedFDeriv ℝ 2 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y)
  have n3 := norm_nonneg (iteratedFDeriv ℝ 3 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y)
  have m1 := norm_nonneg (iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => dτ (p.Efun i) (τ, x)) y)
  have q0 := norm_nonneg (iteratedFDeriv ℝ 0 (p.raw τ) y)
  have q1 := norm_nonneg (iteratedFDeriv ℝ 1 (p.raw τ) y)
  have q2 := norm_nonneg (iteratedFDeriv ℝ 2 (p.raw τ) y)
  have ny := norm_nonneg y
  have nu := abs_nonneg p.ν
  rw [e1, norm_neg]
  have t1 := norm_add_le (dy j (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) (τ, y) +
        dy j (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) (τ, y))
      (dy j (gradAlong p.raw (p.Efun i)) (τ, y))
  have t2 := norm_add_le (dy j (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) (τ, y))
        (dy j (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) (τ, y))
  have u1 : (3:ℝ) * (‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space =>
        UnforcedLeray.B0412.realC (p.raw τ x)) y‖ *
          ‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ +
        ‖iteratedFDeriv ℝ 0 (fun x : UnforcedLeray.Space =>
          UnforcedLeray.B0412.realC (p.raw τ x)) y‖ *
          ‖iteratedFDeriv ℝ 2 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) ≤
      3 * (‖iteratedFDeriv ℝ 1 (p.raw τ) y‖ *
          ‖iteratedFDeriv ℝ 1 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ +
        ‖iteratedFDeriv ℝ 0 (p.raw τ) y‖ *
          ‖iteratedFDeriv ℝ 2 (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) := by
    gcongr
  nlinarith [mul_nonneg q0 n0, mul_nonneg q0 n1, mul_nonneg q0 n2, mul_nonneg q1 n0,
    mul_nonneg q1 n1, mul_nonneg q1 n2, mul_nonneg q2 n0, mul_nonneg q2 n1, mul_nonneg q2 n2,
    mul_nonneg nu m1, mul_nonneg nu n1, mul_nonneg nu n3, mul_nonneg nu (mul_nonneg ny n2),
    mul_nonneg ny n2]

theorem norm_le_rho_add (y : UnforcedLeray.Space) :
    ‖y‖ ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + |y 2| := by
  have h0 : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
  have hs := Real.sq_sqrt h0
  have hn : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have hr := Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2)
  have ha := abs_nonneg (y 2)
  have hsq := sq_abs (y 2)
  by_contra h
  push_neg at h
  have := mul_self_lt_mul_self (by positivity) h
  nlinarith [mul_nonneg hr ha, norm_nonneg y]

/-- `InletFnFarOfJets` from the four Leibniz bounds and the absorption inequality. -/
theorem inletFnFarOfJets_of (hL : L0PartBound) (hA : AdvPartBound) (hG : GradPartBound)
    (hC : RealCBound) (hAb : FarAbsorb) : InletFnFarOfJets := by
  intro h1 hs hb lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν2, hν2, H2⟩ := hs dm dp hdm
  obtain ⟨ν3, hν3, H3⟩ := hb dm dp hdm
  refine ⟨min ν1 (min ν2 (min ν3 1)),
    lt_min hν1 (lt_min hν2 (lt_min hν3 one_pos)), fun p d hreg hν hm z g hg i j => ?_⟩
  have hν1' : p.ν ≤ ν1 := hν.trans (min_le_left _ _)
  have hν2' : p.ν ≤ ν2 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν3' : p.ν ≤ ν3 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν4 : p.ν ≤ 1 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hR := H2 p d hreg hν2'
  have hI := inlet_contDiff_joint lam q hq hreg hν4 hm i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  obtain ⟨C, R0, hR0, hJ⟩ := H1 p d hreg hν1' hm z g hg i 3
  have H3' := H3 p d hreg hν3'
  obtain ⟨B0, hB0⟩ := H3' 0
  obtain ⟨B1, hB1⟩ := H3' 1
  obtain ⟨B2, hB2⟩ := H3' 2
  have hBB0 : B0 ≤ max (max (max B0 B1) B2) 0 := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hBB1 : B1 ≤ max (max (max B0 B1) B2) 0 := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hBB2 : B2 ≤ max (max (max B0 B1) B2) 0 := (le_max_right _ _).trans (le_max_left _ _)
  have hB : 0 ≤ max (max (max B0 B1) B2) 0 := le_max_right _ _
  generalize max (max (max B0 B1) B2) 0 = B at hBB0 hBB1 hBB2 hB
  refine ⟨30 * (1 + |p.ν|) * (max C 0 * (4 + 9 * B)), max R0 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), fun τ hτ y hy => ?_⟩
  have hϱ1 : 1 ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := (le_max_right _ _).trans hy.le
  have hϱR0 : R0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := lt_of_le_of_lt (le_max_left _ _) hy
  have hny := norm_le_rho_add y
  obtain ⟨hj1, hj2⟩ := hJ τ hτ y hϱR0
  have hpt := inletFn_pointwise_of hL hA hG hC j hE hR τ y
  refine hpt.trans ?_
  generalize Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = ϱ at hϱ1 hϱR0 hny hj1 hj2 ⊢
  have hϱ : 0 < ϱ := lt_of_lt_of_le one_pos hϱ1
  have hw1 : 1 ≤ 1 + |y 2| / ϱ := by
    have : 0 ≤ |y 2| / ϱ := by positivity
    linarith
  have hay : ‖y‖ ≤ ϱ * (1 + |y 2| / ϱ) := by
    have : ϱ * (1 + |y 2| / ϱ) = ϱ + |y 2| := by field_simp
    rw [this]; exact hny
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have mono : ∀ (x T : ℝ), 0 ≤ T → x ≤ C * T → x ≤ max C 0 * T := fun x T hT hx =>
    hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hT)
  have hwpos : 0 < 1 + |y 2| / ϱ := lt_of_lt_of_le one_pos hw1
  have tp : ∀ r : ℝ, 0 ≤ ϱ ^ r * (1 + |y 2| / ϱ) ^ (-((3 : ℕ) : ℝ)) := fun r =>
    mul_nonneg (Real.rpow_nonneg hϱ.le _) (Real.rpow_nonneg hwpos.le _)
  have tq : 0 ≤ ϱ ^ (-(2 + ((1 : ℕ) : ℝ))) * (1 + |y 2| / ϱ) ^ (-((3 : ℕ) : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hϱ.le _) (Real.rpow_nonneg hwpos.le _)
  exact hAb p.ν (max C 0) B ϱ (1 + |y 2| / ϱ) ‖y‖ _ _ _ _ _ _ _ _ hC0 hB hϱ1 hw1
    (norm_nonneg _) hay (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (mono _ _ (tp _) (hj1 0 (by norm_num))) (mono _ _ (tp _) (hj1 1 (by norm_num)))
    (mono _ _ (tp _) (hj1 2 (by norm_num))) (mono _ _ (tp _) (hj1 3 (by norm_num)))
    (mono _ _ tq (hj2 1 le_rfl))
    ((hB0 τ y).trans hBB0) ((hB1 τ y).trans hBB1) ((hB2 τ y).trans hBB2)

end UnforcedLeray.Short.PartIIIb.Concrete
