import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.Objects
import Mathlib.Tactic.Module

/-!
# The planar relative evolution (Leaf B3, SP 2926-2935, 2976-2980)

* `c_identity`: for an eigenvector `e^{t𝓛}E = e^{λt}E` (`t ≥ 0`) and any `c`,
  `T(t)E + ∫₀ᵗ e^{cr} T(t-r)(𝒜E + (c-λ)E) dr = e^{ct}E` (Duhamel of the Euler group and FTC).
* `relSol_duhamel`: `V(t) = e^{-γt}e^{t𝓛}𝒬 + e^{-t}𝒫` solves the Duhamel equation of
  `(e^{-γ(t-s)}T(t-s), 𝒜 + Σ (γ-1-λ_i) ℓ_i(·) e_i)`, given the eigen and dual eigen relations.
* `eq_of_isDysonSum`: a Duhamel solution is the Dyson sum (remainder bound `C (Kt)^n/n!`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped Nat

namespace UnforcedLeray.Short.IIIa.PlanarDysonL3

open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3
open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB

theorem continuous_cexp_mul (z : ℂ) : Continuous fun u : ℝ => Complex.exp (z * u) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem hasDerivAt_cexp_mul (z : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (z * u)) (Complex.exp (z * u) * z) u := by
  have h1 : HasDerivAt (fun u : ℝ => z * (u : ℂ)) (z * ((1 : ℝ) : ℂ)) u :=
    ((hasDerivAt_id u).ofReal_comp).const_mul z
  have h2 := h1.cexp
  simpa using h2

/-- **The shifted-exponent identity** for an eigenvector of the Euler group. -/
theorem c_identity {M : ℝ} (hM : 1 < M) (E : Planar.L2w M) (lam c : ℂ)
    (hEig : ∀ t : ℝ, 0 ≤ t → Planar.eulerGroupW hM t E = Complex.exp (lam * t) • E)
    {t : ℝ} (ht : 0 ≤ t) :
    Planar.transportGroupW M t E +
      ∫ r in (0:ℝ)..t, Complex.exp (c * r) •
        Planar.transportGroupW M (t - r) (Planar.couplingW hM E + (c - lam) • E) =
      Complex.exp (c * t) • E := by
  set T := Planar.transportGroupW M with hT
  set b : ℝ → Planar.L2w M := fun u => T u (Planar.couplingW hM E) with hb
  set a : ℝ → Planar.L2w M := fun u => T u E with ha
  have hbc : Continuous b := Planar.continuous_transportGroupW_apply M _
  have hac : Continuous a := Planar.continuous_transportGroupW_apply M _
  set f : ℝ → Planar.L2w M := fun v => Complex.exp (-lam * v) • b v with hf
  have hfc : Continuous f := (continuous_cexp_mul (-lam)).smul hbc
  -- Step 1: `a s = e^{λs}(E - ∫₀ˢ f)`.
  have step1 : ∀ s : ℝ, 0 ≤ s → a s = Complex.exp (lam * s) • (E - ∫ v in (0:ℝ)..s, f v) := by
    intro s hs
    have hd := Planar.eulerGroupW_eq_duhamel hM s E
    rw [hEig s hs] at hd
    have h2 : ∫ τ in (0:ℝ)..s, T (s - τ) (Planar.couplingW hM (Planar.eulerGroupW hM τ E)) =
        ∫ τ in (0:ℝ)..s, (fun v : ℝ => Complex.exp (lam * s) • f v) (s - τ) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      rw [Set.uIcc_of_le hs] at hτ
      simp only [hf, hb, smul_smul, ← Complex.exp_add]
      rw [hEig τ hτ.1, map_smul, map_smul]
      congr 2
      push_cast
      ring
    have h3 := intervalIntegral.integral_comp_sub_left
      (fun v : ℝ => Complex.exp (lam * s) • f v) (a := 0) (b := s) s
    rw [sub_self, sub_zero] at h3
    rw [h2, h3, intervalIntegral.integral_smul] at hd
    show T s E = _
    rw [smul_sub, hd]
    abel
  -- Step 2: FTC for `phi u = e^{(λ-c)u} (E - ∫₀ᵘ f)`.
  set psi : ℝ → Planar.L2w M := fun u => E - ∫ v in (0:ℝ)..u, f v with hpsi
  have hpsid : ∀ u, HasDerivAt psi (-(f u)) u := fun u =>
    ((hfc.integral_hasStrictDerivAt 0 u).hasDerivAt).const_sub E
  set phi : ℝ → Planar.L2w M := fun u => Complex.exp ((lam - c) * u) • psi u with hphi
  set phd : ℝ → Planar.L2w M := fun u =>
    Complex.exp ((lam - c) * u) • (-(f u)) + (Complex.exp ((lam - c) * u) * (lam - c)) • psi u
    with hphd
  have hphid : ∀ u, HasDerivAt phi (phd u) u := fun u =>
    (hasDerivAt_cexp_mul (lam - c) u).smul (hpsid u)
  have hpsic : Continuous psi := continuous_const.sub
    (intervalIntegral.continuous_primitive (fun a b => hfc.intervalIntegrable a b) 0)
  have hphdc : Continuous phd :=
    ((continuous_cexp_mul (lam - c)).smul hfc.neg).add
      (((continuous_cexp_mul (lam - c)).mul continuous_const).smul hpsic)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun u _ => hphid u) (hphdc.intervalIntegrable 0 t)
  have hphdeq : ∀ u : ℝ, 0 ≤ u →
      phd u = -(Complex.exp (-c * u) • (b u + (c - lam) • a u)) := by
    intro u hu
    have e1 : Complex.exp ((lam - c) * u) = Complex.exp (-c * u) * Complex.exp (lam * u) := by
      rw [← Complex.exp_add]
      ring_nf
    have e2 : Complex.exp (-lam * u) * Complex.exp (lam * u) = 1 := by
      rw [← Complex.exp_add]
      ring_nf
      exact Complex.exp_zero
    simp only [hphd, hf]
    rw [step1 u hu, e1]
    simp only [smul_neg, smul_smul, smul_add]
    rw [show Complex.exp (-c * ↑u) * Complex.exp (lam * ↑u) * Complex.exp (-lam * ↑u) =
      Complex.exp (-c * ↑u) by rw [mul_assoc, mul_comm (Complex.exp (lam * ↑u)), e2, mul_one]]
    module
  have hint : ∫ u in (0:ℝ)..t, phd u =
      -∫ u in (0:ℝ)..t, Complex.exp (-c * u) • (b u + (c - lam) • a u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    exact hphdeq u hu.1
  have hphit : phi t = Complex.exp (-c * t) • a t := by
    simp only [hphi]
    rw [step1 t ht, smul_smul, ← Complex.exp_add]
    congr 2
    ring
  have hphi0 : phi 0 = E := by
    simp only [hphi, hpsi, intervalIntegral.integral_same, sub_zero, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul]
  rw [hint, hphit, hphi0] at hftc
  -- hftc : -∫₀ᵗ e^{-cu}(b u + (c-λ) a u) = e^{-ct} a t - E
  -- Step 3: the substitution `u = t - r` in the target integral.
  have h4 : ∫ r in (0:ℝ)..t, Complex.exp (c * r) •
        T (t - r) (Planar.couplingW hM E + (c - lam) • E) =
      ∫ r in (0:ℝ)..t, (fun u : ℝ => Complex.exp (c * t) •
        (Complex.exp (-c * u) • (b u + (c - lam) • a u))) (t - r) := by
    apply intervalIntegral.integral_congr
    intro r _
    simp only [hb, ha, map_add, map_smul, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h5 := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => Complex.exp (c * t) • (Complex.exp (-c * u) • (b u + (c - lam) • a u)))
    (a := 0) (b := t) t
  rw [sub_self, sub_zero] at h5
  rw [h4, h5, intervalIntegral.integral_smul]
  have h6 : ∫ u in (0:ℝ)..t, Complex.exp (-c * u) • (b u + (c - lam) • a u) =
      E - Complex.exp (-c * t) • a t := by
    rw [← neg_neg (∫ u in (0:ℝ)..t, Complex.exp (-c * u) • (b u + (c - lam) • a u)), hftc]
    abel
  rw [h6, smul_sub, smul_smul, ← Complex.exp_add]
  have e3 : c * (t : ℂ) + -c * t = 0 := by ring
  rw [e3, Complex.exp_zero, one_smul]
  show a t + (Complex.exp (c * t) • E - a t) = _
  abel

/-! ### The candidate relative evolution and its Duhamel equation -/

/-- `V(t) = e^{-γt} e^{t𝓛} 𝒬 + e^{-t} 𝒫` (SP 2926-2927), `γ = Re λ`, `𝒬 = 1 - 𝒫`. -/
def relSol (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData) {m : ℝ}
    (hm : 1 < m) (t : ℝ) : Planar.L2w m →L[ℂ] Planar.L2w m :=
  ((Real.exp (-P.eigenvalue.re * t) : ℝ) : ℂ) •
      (Planar.eulerGroupW hm t ∘L (1 - planarProj κ hm)) +
    ((Real.exp (-t) : ℝ) : ℂ) • planarProj κ hm

theorem relSol_apply (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    {m : ℝ} (hm : 1 < m) (t : ℝ) (x : Planar.L2w m) :
    relSol κ P hm t x = ((Real.exp (-P.eigenvalue.re * t) : ℝ) : ℂ) •
        Planar.eulerGroupW hm t (x - planarProj κ hm x) +
      ((Real.exp (-t) : ℝ) : ℂ) • planarProj κ hm x := by
  simp [relSol]

theorem continuous_relSol_apply (κ : PlanarFrameKernels)
    (P : UnforcedLeray.Blueprint.Planar.PlanarData) {m : ℝ} (hm : 1 < m) (x : Planar.L2w m) :
    Continuous fun t => relSol κ P hm t x := by
  simp_rw [relSol_apply]
  refine ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).smul
      (Planar.continuous_eulerGroupW_apply hm _)).add
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).smul
      continuous_const)

theorem dampOp_planarE (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    {m : ℝ} (hm : 1 < m) (lam : ℂ) (i : Fin 2) :
    dampOp κ P hm lam (planarE κ m i) =
      Planar.couplingW hm (planarE κ m i) + dampCoef P lam i • planarE κ m i := by
  rw [dampOp_apply, Fin.sum_univ_two]
  fin_cases i <;> simp [planarEll_planarE]

theorem dampOp_of_ell_zero (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    {m : ℝ} (hm : 1 < m) (lam : ℂ) {v : Planar.L2w m} (hv : ∀ i, planarEll κ hm i v = 0) :
    dampOp κ P hm lam v = Planar.couplingW hm v := by
  rw [dampOp_apply]
  simp [hv]

/-- **Duhamel equation of `V`** for `(e^{-γ(t-s)}T(t-s), 𝒜 + Σ (γ-1-λ_i) ℓ_i(·) e_i)`, from the
eigen relations `e^{t𝓛}e_i = e^{λ_i t}e_i`, `ℓ_i e^{t𝓛} = e^{λ_i t}ℓ_i` (`t ≥ 0`). -/
theorem relSol_duhamel (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    {m : ℝ} (hm : 1 < m) (lam : ℂ)
    (hEig : ∀ (i : Fin 2) (t : ℝ), 0 ≤ t →
      Planar.eulerGroupW hm t (planarE κ m i) = Complex.exp (seedEigen lam i * t) • planarE κ m i)
    (hDual : ∀ (i : Fin 2) (t : ℝ), 0 ≤ t → ∀ f : Planar.L2w m,
      planarEll κ hm i (Planar.eulerGroupW hm t f) =
        Complex.exp (seedEigen lam i * t) * planarEll κ hm i f)
    {t : ℝ} (ht : 0 ≤ t) (x : Planar.L2w m) :
    relSol κ P hm t x = planarRelTransportRe P m t 0 x +
      ∫ r in (0:ℝ)..t, planarRelTransportRe P m t r (dampOp κ P hm lam (relSol κ P hm r x)) := by
  set y := x - planarProj κ hm x with hy
  set a0 := planarEll κ hm 0 x with ha0
  set a1 := planarEll κ hm 1 x with ha1
  set c : ℂ := ((P.eigenvalue.re - 1 : ℝ) : ℂ) with hc
  have hdc : ∀ i, dampCoef P lam i = c - seedEigen lam i := fun i => rfl
  have hPx : planarProj κ hm x = a0 • planarE κ m 0 + a1 • planarE κ m 1 := by
    rw [planarProj_apply, Fin.sum_univ_two]
  have hℓy : ∀ i, planarEll κ hm i y = 0 := by
    intro i
    rw [hy, map_sub, planarEll_planarProj, sub_self]
  have hdG : ∀ r : ℝ, 0 ≤ r → dampOp κ P hm lam (Planar.eulerGroupW hm r y) =
      Planar.couplingW hm (Planar.eulerGroupW hm r y) := by
    intro r hr
    exact dampOp_of_ell_zero κ P hm lam fun i => by rw [hDual i r hr, hℓy, mul_zero]
  have hAV : ∀ r : ℝ, 0 ≤ r → dampOp κ P hm lam (relSol κ P hm r x) =
      ((Real.exp (-P.eigenvalue.re * r) : ℝ) : ℂ) •
          Planar.couplingW hm (Planar.eulerGroupW hm r y) +
        ((Real.exp (-r) : ℝ) : ℂ) •
          (a0 • (Planar.couplingW hm (planarE κ m 0) + (c - seedEigen lam 0) • planarE κ m 0) +
            a1 • (Planar.couplingW hm (planarE κ m 1) + (c - seedEigen lam 1) • planarE κ m 1)) := by
    intro r hr
    rw [relSol_apply, ← hy, hPx]
    simp only [map_add, map_smul]
    rw [hdG r hr, dampOp_planarE, dampOp_planarE, hdc, hdc]
  have hint : ∫ r in (0:ℝ)..t,
      planarRelTransportRe P m t r (dampOp κ P hm lam (relSol κ P hm r x)) =
      ∫ r in (0:ℝ)..t, ((Real.exp (-P.eigenvalue.re * t) : ℝ) : ℂ) •
        (Planar.transportGroupW m (t - r) (Planar.couplingW hm (Planar.eulerGroupW hm r y)) +
          (a0 • (Complex.exp (c * r) • Planar.transportGroupW m (t - r)
              (Planar.couplingW hm (planarE κ m 0) + (c - seedEigen lam 0) • planarE κ m 0)) +
            a1 • (Complex.exp (c * r) • Planar.transportGroupW m (t - r)
              (Planar.couplingW hm (planarE κ m 1) + (c - seedEigen lam 1) • planarE κ m 1)))) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le ht] at hr
    simp only
    rw [hAV r hr.1]
    have e1 : ((Real.exp (-P.eigenvalue.re * (t - r)) : ℝ) : ℂ) *
        ((Real.exp (-P.eigenvalue.re * r) : ℝ) : ℂ) = ((Real.exp (-P.eigenvalue.re * t) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    have e2 : ((Real.exp (-P.eigenvalue.re * (t - r)) : ℝ) : ℂ) * ((Real.exp (-r) : ℝ) : ℂ) =
        ((Real.exp (-P.eigenvalue.re * t) : ℝ) : ℂ) * Complex.exp (c * r) := by
      rw [hc, Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add,
        ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [planarRelTransportRe, ContinuousLinearMap.smul_apply, map_add, map_smul]
    linear_combination (norm := module)
      e1 • Planar.transportGroupW m (t - r) (Planar.couplingW hm (Planar.eulerGroupW hm r y)) +
      (a0 * e2) • (Planar.transportGroupW m (t - r) (Planar.couplingW hm (planarE κ m 0)) +
        (c - seedEigen lam 0) • Planar.transportGroupW m (t - r) (planarE κ m 0)) +
      (a1 * e2) • (Planar.transportGroupW m (t - r) (Planar.couplingW hm (planarE κ m 1)) +
        (c - seedEigen lam 1) • Planar.transportGroupW m (t - r) (planarE κ m 1))
  have hc1 : Continuous fun r : ℝ =>
      Planar.transportGroupW m (t - r) (Planar.couplingW hm (Planar.eulerGroupW hm r y)) :=
    Planar.continuous_apply_of_strong (Planar.continuous_transportGroupW_apply m)
      (fun s => Planar.norm_transportGroupW_le m s)
      ((Planar.couplingW hm).continuous.comp (Planar.continuous_eulerGroupW_apply hm y))
      (continuous_const.sub continuous_id)
  have hc2 : ∀ (v : Planar.L2w m) (a : ℂ), Continuous fun r : ℝ =>
      a • (Complex.exp (c * r) • Planar.transportGroupW m (t - r) v) := fun v a =>
    ((continuous_cexp_mul c).smul ((Planar.continuous_transportGroupW_apply m v).comp
      (continuous_const.sub continuous_id))).const_smul a
  have hc3 : ∀ (v w : Planar.L2w m) (a b : ℂ), Continuous fun r : ℝ =>
      a • (Complex.exp (c * r) • Planar.transportGroupW m (t - r) v) +
        b • (Complex.exp (c * r) • Planar.transportGroupW m (t - r) w) := fun v w a b =>
    (hc2 v a).add (hc2 w b)
  rw [hint, intervalIntegral.integral_smul,
    intervalIntegral.integral_add (hc1.intervalIntegrable 0 t) ((hc3 _ _ a0 a1).intervalIntegrable 0 t),
    intervalIntegral.integral_add ((hc2 _ a0).intervalIntegrable 0 t)
      ((hc2 _ a1).intervalIntegrable 0 t),
    intervalIntegral.integral_smul, intervalIntegral.integral_smul]
  have hci : ∀ i, ∫ r in (0:ℝ)..t, Complex.exp (c * r) • Planar.transportGroupW m (t - r)
      (Planar.couplingW hm (planarE κ m i) + (c - seedEigen lam i) • planarE κ m i) =
      Complex.exp (c * t) • planarE κ m i - Planar.transportGroupW m t (planarE κ m i) := by
    intro i
    have h := c_identity hm (planarE κ m i) (seedEigen lam i) c (hEig i) ht
    rw [← h]
    abel
  rw [hci 0, hci 1]
  have hI1 : ∫ r in (0:ℝ)..t,
      Planar.transportGroupW m (t - r) (Planar.couplingW hm (Planar.eulerGroupW hm r y)) =
      Planar.eulerGroupW hm t y - Planar.transportGroupW m t y := by
    rw [Planar.eulerGroupW_eq_duhamel hm t y]
    abel
  rw [hI1, relSol_apply, ← hy, hPx]
  have hF0 : planarRelTransportRe P m t 0 x =
      ((Real.exp (-P.eigenvalue.re * t) : ℝ) : ℂ) • Planar.transportGroupW m t x := by
    simp only [planarRelTransportRe, sub_zero, ContinuousLinearMap.smul_apply]
  rw [hF0]
  have hx : x = y + (a0 • planarE κ m 0 + a1 • planarE κ m 1) := by
    rw [hy, hPx]
    abel
  have hTx : Planar.transportGroupW m t x = Planar.transportGroupW m t y +
      (a0 • Planar.transportGroupW m t (planarE κ m 0) +
        a1 • Planar.transportGroupW m t (planarE κ m 1)) := by
    conv_lhs => rw [hx]
    simp only [map_add, map_smul]
  rw [hTx]
  have hsc : ((Real.exp (-P.eigenvalue.re * t) : ℝ) : ℂ) * Complex.exp (c * t) =
      ((Real.exp (-t) : ℝ) : ℂ) := by
    rw [hc, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (norm := module) (-hsc) • (a0 • planarE κ m 0 + a1 • planarE κ m 1)

/-! ### A Duhamel solution is the Dyson sum -/

theorem eq_of_isDysonSum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {B : ℝ} {F : Unit → ℝ → ℝ → H →L[ℂ] H} {A : Unit → ℝ → H →L[ℂ] H}
    {U : Unit → ℝ → ℝ → H →L[ℂ] H}
    (hU : UnforcedLeray.B0104.IsDysonSum B F A U) (hD : UnforcedLeray.B0104.DysonDefined B F A)
    {K : ℝ} (hK : ∀ r, ‖A () r‖ ≤ K)
    (hF : ∀ t r, 0 ≤ r → r ≤ t → t ≤ B → ‖F () t r‖ ≤ 1)
    (x : H) (V : ℝ → H) (hVc : ContinuousOn V (Icc 0 B))
    (hVi : ∀ t ∈ Icc (0:ℝ) B,
      IntervalIntegrable (fun r => F () t r (A () r (V r))) volume 0 t)
    (hduh : ∀ t ∈ Icc (0:ℝ) B, V t = F () t 0 x + ∫ r in (0:ℝ)..t, F () t r (A () r (V r))) :
    ∀ t ∈ Icc (0:ℝ) B, U () t 0 x = V t := by
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hVc
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set S : ℕ → ℝ → H := fun n t =>
    ∑ k ∈ Finset.range n, UnforcedLeray.B0104.dysonTerm F A k () t 0 x with hS
  have hrec : ∀ n : ℕ, ∀ t ∈ Icc (0:ℝ) B,
      V t - S (n + 1) t = ∫ r in (0:ℝ)..t, F () t r (A () r (V r - S n r)) := by
    intro n t ht
    have hdT : ∀ k, IntervalIntegrable (fun r => F () t r (A () r
        (UnforcedLeray.B0104.dysonTerm F A k () r 0 x))) volume 0 t :=
      fun k => hD k () 0 t ht.1 (by linarith [ht.2]) x
    have e1 : S (n + 1) t = F () t 0 x + ∑ k ∈ Finset.range n,
        ∫ r in (0:ℝ)..t, F () t r (A () r (UnforcedLeray.B0104.dysonTerm F A k () r 0 x)) := by
      simp only [hS]
      rw [Finset.sum_range_succ', add_comm]
      rfl
    have e2 : ∫ r in (0:ℝ)..t, F () t r (A () r (V r - S n r)) =
        (∫ r in (0:ℝ)..t, F () t r (A () r (V r))) - ∑ k ∈ Finset.range n,
          ∫ r in (0:ℝ)..t, F () t r (A () r (UnforcedLeray.B0104.dysonTerm F A k () r 0 x)) := by
      have hsumi : IntervalIntegrable (fun r => ∑ k ∈ Finset.range n,
          F () t r (A () r (UnforcedLeray.B0104.dysonTerm F A k () r 0 x))) volume 0 t := by
        have h := IntervalIntegrable.sum (Finset.range n) (fun k _ => hdT k)
        simpa only [Finset.sum_fn] using h
      rw [← intervalIntegral.integral_finsetSum (fun k _ => hdT k),
        ← intervalIntegral.integral_sub (hVi t ht) hsumi]
      congr 1
      funext r
      simp only [hS, map_sub, map_sum, Finset.sum_apply]
    rw [e1, e2]
    conv_lhs => rw [hduh t ht]
    abel
  have hbound : ∀ n : ℕ, ∀ t ∈ Icc (0:ℝ) B, ‖V t - S n t‖ ≤ Cb * (K * t) ^ n / n ! := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simpa [hS] using hCb t ht
    | succ n ih =>
      intro t ht
      rw [hrec n t ht]
      have hc : Continuous fun r : ℝ => K * (Cb * (K * r) ^ n / n !) := by fun_prop
      calc ‖∫ r in (0:ℝ)..t, F () t r (A () r (V r - S n r))‖
          ≤ ∫ r in (0:ℝ)..t, K * (Cb * (K * r) ^ n / n !) := by
            refine intervalIntegral.norm_integral_le_of_norm_le ht.1
              (ae_of_all _ fun r hr => ?_) (hc.intervalIntegrable _ _)
            have hrB : r ∈ Icc (0:ℝ) B := ⟨hr.1.le, hr.2.trans ht.2⟩
            calc ‖F () t r (A () r (V r - S n r))‖
                ≤ ‖F () t r‖ * ‖A () r (V r - S n r)‖ := (F () t r).le_opNorm _
              _ ≤ 1 * (K * ‖V r - S n r‖) :=
                  mul_le_mul (hF t r hr.1.le hr.2 ht.2) ((A () r).le_of_opNorm_le (hK r) _)
                    (norm_nonneg _) zero_le_one
              _ ≤ 1 * (K * (Cb * (K * r) ^ n / n !)) := by
                  gcongr
                  exact ih r hrB
              _ = K * (Cb * (K * r) ^ n / n !) := one_mul _
        _ = Cb * (K * t) ^ (n + 1) / (n + 1)! := by
            have e : (fun r : ℝ => K * (Cb * (K * r) ^ n / n !)) =
                fun r => (K * Cb * K ^ n / n !) * r ^ n := by
              funext r
              rw [mul_pow]
              ring
            rw [e, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
            push_cast
            field_simp
            ring
  intro t ht
  have hlim : Tendsto (fun n => S n t) atTop (𝓝 (V t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n : ℕ => Cb * ((K * t) ^ n / n !)) atTop (𝓝 0) := by
      simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (K * t)).const_mul Cb
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    rw [norm_sub_rev, ← mul_div_assoc]
    exact hbound n t ht
  have hsum := (hU () t 0 ht.1 (by linarith [ht.2]) x).tendsto_sum_nat
  exact tendsto_nhds_unique hsum hlim

end UnforcedLeray.Short.IIIa.PlanarDysonL3
