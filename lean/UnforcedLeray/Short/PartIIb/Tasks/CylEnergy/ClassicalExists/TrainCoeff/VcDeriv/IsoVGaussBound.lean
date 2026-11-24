import UnforcedLeray.Short.PartIIb.Sub.T22_1_1_4

/-!
# `PartII-b:T22/1/1/4/1`: Gaussian bound for the isolated vortex

Leaf V1 `IsoVGaussBound` of `TcVcDeriv` (source `the November 2 reference manuscript`,
isolated heat vortex of width `a = 1 + νs`).

Route: `isoV ν s = toVec (u1 a, u2 a)` (`B0146.isoVelocity_eq`, `B0146.vExp_eq`); the first
partial derivatives of the components (`B0146.hx_u1`, `hy_u1`, `hx_u2`, `hy_u2`); the uniform
Gaussian decay `B0146.GF.unif` for the widths in `[1, K]`. The operator norm of the derivative
is bounded by the sum of its values on the basis `(1,0)`, `(0,1)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

/-- The isolated vortex as a pair of explicit components at width `heatWidth ν s`. -/
theorem isoV_eq_uu (ν s : ℝ) :
    UnforcedLeray.Train.isoV ν s = fun z => UnforcedLeray.Train.toVec
      (UnforcedLeray.B0146.u1 (UnforcedLeray.B0113.heatWidth ν s) z,
       UnforcedLeray.B0146.u2 (UnforcedLeray.B0113.heatWidth ν s) z) := by
  funext z
  rw [UnforcedLeray.Train.isoV, UnforcedLeray.B0146.isoVelocity_eq]
  rfl

/-- The Euclidean norm of a vector with components `(p, q)` is at most `|p| + |q|`. -/
theorem norm_toVec_le_abs (p q : ℝ) :
    ‖UnforcedLeray.Train.toVec (p, q)‖ ≤ |p| + |q| := by
  rw [UnforcedLeray.Train.norm_toVec]
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  show p ^ 2 + q ^ 2 ≤ (|p| + |q|) ^ 2
  nlinarith [sq_abs p, sq_abs q, mul_nonneg (abs_nonneg p) (abs_nonneg q)]

/-- Operator norm of a linear map from `ℝ × ℝ` (sup norm) is bounded by the values on the basis. -/
theorem clm_norm_le_basis (F : (ℝ × ℝ) →L[ℝ] UnforcedLeray.Train.Vec) :
    ‖F‖ ≤ ‖F (1, 0)‖ + ‖F (0, 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound F (by positivity) fun x => ?_
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hFx : F x = x.1 • F (1, 0) + x.2 • F (0, 1) := by
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul]
  calc ‖F x‖ = ‖x.1 • F (1, 0) + x.2 • F (0, 1)‖ := by rw [hFx]
    _ ≤ ‖x.1 • F (1, 0)‖ + ‖x.2 • F (0, 1)‖ := norm_add_le _ _
    _ = ‖x.1‖ * ‖F (1, 0)‖ + ‖x.2‖ * ‖F (0, 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖x‖ * ‖F (1, 0)‖ + ‖x‖ * ‖F (0, 1)‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (norm_snd_le x) (norm_nonneg _))
    _ = (‖F (1, 0)‖ + ‖F (0, 1)‖) * ‖x‖ := by ring

theorem diff_u1 (b : ℝ) : Differentiable ℝ (fun z : ℝ × ℝ => UnforcedLeray.B0146.u1 b z) := by
  unfold UnforcedLeray.B0146.u1 UnforcedLeray.B0113.gw UnforcedLeray.GaussianVortex.radiusSq
  fun_prop

theorem diff_u2 (b : ℝ) : Differentiable ℝ (fun z : ℝ × ℝ => UnforcedLeray.B0146.u2 b z) := by
  unfold UnforcedLeray.B0146.u2 UnforcedLeray.B0113.gw UnforcedLeray.GaussianVortex.radiusSq
  fun_prop

theorem diff_isoV (ν s : ℝ) : Differentiable ℝ (UnforcedLeray.Train.isoV ν s) := by
  rw [isoV_eq_uu]
  have h1 : Differentiable ℝ (fun z : ℝ × ℝ => (UnforcedLeray.B0146.u1
      (UnforcedLeray.B0113.heatWidth ν s) z, UnforcedLeray.B0146.u2
      (UnforcedLeray.B0113.heatWidth ν s) z)) :=
    (diff_u1 _).prodMk (diff_u2 _)
  exact ((UnforcedLeray.Train.toVecL : (ℝ × ℝ) →L[ℝ] UnforcedLeray.Train.Vec).differentiable).comp h1

/-- Line derivative in the first variable: `∂_q V = (u1x, u2x)`. -/
theorem line_x (ν s : ℝ) (w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => UnforcedLeray.Train.isoV ν s (t, w.2))
      (UnforcedLeray.Train.toVec (UnforcedLeray.B0146.u1x (UnforcedLeray.B0113.heatWidth ν s) w,
        UnforcedLeray.B0146.u2x (UnforcedLeray.B0113.heatWidth ν s) w)) w.1 := by
  have h := (UnforcedLeray.B0146.hx_u1 (UnforcedLeray.B0113.heatWidth ν s) w).prodMk
    (UnforcedLeray.B0146.hx_u2 (UnforcedLeray.B0113.heatWidth ν s) w)
  have h2 := (UnforcedLeray.Train.toVecL : (ℝ × ℝ) →L[ℝ] UnforcedLeray.Train.Vec).hasFDerivAt.comp_hasDerivAt
    w.1 h
  have e : (fun t : ℝ => UnforcedLeray.Train.isoV ν s (t, w.2)) =
      (UnforcedLeray.Train.toVecL : (ℝ × ℝ) →L[ℝ] UnforcedLeray.Train.Vec) ∘
        (fun t : ℝ => (UnforcedLeray.B0146.u1 (UnforcedLeray.B0113.heatWidth ν s) (t, w.2),
          UnforcedLeray.B0146.u2 (UnforcedLeray.B0113.heatWidth ν s) (t, w.2))) := by
    rw [isoV_eq_uu]
    rfl
  rw [e]
  exact h2

/-- Line derivative in the second variable: `∂_η V = (u1y, u2y)`. -/
theorem line_y (ν s : ℝ) (w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => UnforcedLeray.Train.isoV ν s (w.1, t))
      (UnforcedLeray.Train.toVec (UnforcedLeray.B0146.u1y (UnforcedLeray.B0113.heatWidth ν s) w,
        UnforcedLeray.B0146.u2y (UnforcedLeray.B0113.heatWidth ν s) w)) w.2 := by
  have h := (UnforcedLeray.B0146.hy_u1 (UnforcedLeray.B0113.heatWidth ν s) w).prodMk
    (UnforcedLeray.B0146.hy_u2 (UnforcedLeray.B0113.heatWidth ν s) w)
  have h2 := (UnforcedLeray.Train.toVecL : (ℝ × ℝ) →L[ℝ] UnforcedLeray.Train.Vec).hasFDerivAt.comp_hasDerivAt
    w.2 h
  have e : (fun t : ℝ => UnforcedLeray.Train.isoV ν s (w.1, t)) =
      (UnforcedLeray.Train.toVecL : (ℝ × ℝ) →L[ℝ] UnforcedLeray.Train.Vec) ∘
        (fun t : ℝ => (UnforcedLeray.B0146.u1 (UnforcedLeray.B0113.heatWidth ν s) (w.1, t),
          UnforcedLeray.B0146.u2 (UnforcedLeray.B0113.heatWidth ν s) (w.1, t))) := by
    rw [isoV_eq_uu]
    rfl
  rw [e]
  exact h2

/-- The derivative of `isoV ν s` at `w` on the basis vectors. -/
theorem fderiv_basis (ν s : ℝ) (w : ℝ × ℝ) :
    fderiv ℝ (UnforcedLeray.Train.isoV ν s) w (1, 0) =
        UnforcedLeray.Train.toVec (UnforcedLeray.B0146.u1x (UnforcedLeray.B0113.heatWidth ν s) w,
          UnforcedLeray.B0146.u2x (UnforcedLeray.B0113.heatWidth ν s) w) ∧
    fderiv ℝ (UnforcedLeray.Train.isoV ν s) w (0, 1) =
        UnforcedLeray.Train.toVec (UnforcedLeray.B0146.u1y (UnforcedLeray.B0113.heatWidth ν s) w,
          UnforcedLeray.B0146.u2y (UnforcedLeray.B0113.heatWidth ν s) w) := by
  have hF : HasFDerivAt (UnforcedLeray.Train.isoV ν s)
      (fderiv ℝ (UnforcedLeray.Train.isoV ν s) w) w :=
    (diff_isoV ν s w).hasFDerivAt
  constructor
  · have hl : HasDerivAt (fun t : ℝ => ((t, w.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) w.1 :=
      (hasDerivAt_id' w.1).prodMk (hasDerivAt_const w.1 w.2)
    have h := hF.comp_hasDerivAt w.1 hl
    exact (show HasDerivAt (fun t : ℝ => UnforcedLeray.Train.isoV ν s (t, w.2))
      (fderiv ℝ (UnforcedLeray.Train.isoV ν s) w (1, 0)) w.1 from h).unique (line_x ν s w)
  · have hl : HasDerivAt (fun t : ℝ => ((w.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) w.2 :=
      (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id' w.2)
    have h := hF.comp_hasDerivAt w.2 hl
    exact (show HasDerivAt (fun t : ℝ => UnforcedLeray.Train.isoV ν s (w.1, t))
      (fderiv ℝ (UnforcedLeray.Train.isoV ν s) w (0, 1)) w.2 from h).unique (line_y ν s w)

/-- Monotonicity of the Gaussian weight in the exponent rate. -/
theorem mono_bound {f : ℝ → ℝ × ℝ → ℝ} {Kw C β β' : ℝ} (hC : 0 ≤ C) (hβ : β' ≤ β)
    (h : ∀ a ∈ Set.Icc (1 : ℝ) Kw, ∀ w : ℝ × ℝ, |f a w| ≤ C * Real.exp (-(β * w.1 ^ 2))) :
    ∀ a ∈ Set.Icc (1 : ℝ) Kw, ∀ w : ℝ × ℝ, |f a w| ≤ C * Real.exp (-(β' * w.1 ^ 2)) := by
  intro a ha w
  refine (h a ha w).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
  linarith [mul_le_mul_of_nonneg_right hβ (sq_nonneg w.1)]

/-- **Leaf V1** (Gaussian decay of the isolated vortex and of its derivative, uniform in the
width `1 + νs ∈ [1, K]`). -/
theorem isoVGaussBound : UnforcedLeray.Short.IIb.CylPDE.IsoVGaussBound := by
  intro Kw hKw
  obtain ⟨C1, β1, hC1, hβ1, h1⟩ :=
    (UnforcedLeray.B0146.gf_u1 (A₁ := 1) (A₂ := Kw) one_pos).unif
  obtain ⟨C2, β2, hC2, hβ2, h2⟩ :=
    (UnforcedLeray.B0146.gf_u2 (A₁ := 1) (A₂ := Kw) one_pos).unif
  obtain ⟨C3, β3, hC3, hβ3, h3⟩ :=
    (UnforcedLeray.B0146.gf_u1x (A₁ := 1) (A₂ := Kw) one_pos).unif
  obtain ⟨C4, β4, hC4, hβ4, h4⟩ :=
    (UnforcedLeray.B0146.gf_u1y (A₁ := 1) (A₂ := Kw) one_pos).unif
  obtain ⟨C5, β5, hC5, hβ5, h5⟩ :=
    (UnforcedLeray.B0146.gf_u2x (A₁ := 1) (A₂ := Kw) one_pos).unif
  obtain ⟨C6, β6, hC6, hβ6, h6⟩ :=
    (UnforcedLeray.B0146.gf_u2y (A₁ := 1) (A₂ := Kw) one_pos).unif
  obtain ⟨β, hβ, hb1, hb2, hb3, hb4, hb5, hb6⟩ : ∃ β : ℝ, 0 < β ∧ β ≤ β1 ∧ β ≤ β2 ∧
      β ≤ β3 ∧ β ≤ β4 ∧ β ≤ β5 ∧ β ≤ β6 :=
    ⟨min (min (min β1 β2) (min β3 β4)) (min β5 β6),
      lt_min (lt_min (lt_min hβ1 hβ2) (lt_min hβ3 hβ4)) (lt_min hβ5 hβ6),
      by simp [min_le_iff]⟩
  have m1 := mono_bound (f := UnforcedLeray.B0146.u1) hC1 hb1 h1
  have m2 := mono_bound (f := UnforcedLeray.B0146.u2) hC2 hb2 h2
  have m3 := mono_bound (f := UnforcedLeray.B0146.u1x) hC3 hb3 h3
  have m4 := mono_bound (f := UnforcedLeray.B0146.u1y) hC4 hb4 h4
  have m5 := mono_bound (f := UnforcedLeray.B0146.u2x) hC5 hb5 h5
  have m6 := mono_bound (f := UnforcedLeray.B0146.u2y) hC6 hb6 h6
  refine ⟨C1 + C2 + C3 + C4 + C5 + C6, β, hβ, ?_⟩
  intro ν s hν1 hνK
  have ha : UnforcedLeray.B0113.heatWidth ν s ∈ Set.Icc (1 : ℝ) Kw := ⟨hν1, hνK⟩
  refine ⟨diff_isoV ν s, fun z => ⟨?_, ?_⟩⟩
  · have hE : 0 ≤ Real.exp (-(β * z.1 ^ 2)) := (Real.exp_pos _).le
    have hv : ‖UnforcedLeray.Train.isoV ν s z‖ ≤
        |UnforcedLeray.B0146.u1 (UnforcedLeray.B0113.heatWidth ν s) z| +
          |UnforcedLeray.B0146.u2 (UnforcedLeray.B0113.heatWidth ν s) z| := by
      rw [isoV_eq_uu]
      exact norm_toVec_le_abs _ _
    have e1 := m1 _ ha z
    have e2 := m2 _ ha z
    have hsum : (C1 + C2 + C3 + C4 + C5 + C6) * Real.exp (-(β * z.1 ^ 2)) =
        C1 * Real.exp (-(β * z.1 ^ 2)) + C2 * Real.exp (-(β * z.1 ^ 2)) +
        C3 * Real.exp (-(β * z.1 ^ 2)) + C4 * Real.exp (-(β * z.1 ^ 2)) +
        C5 * Real.exp (-(β * z.1 ^ 2)) + C6 * Real.exp (-(β * z.1 ^ 2)) := by ring
    nlinarith [mul_nonneg hC3 hE, mul_nonneg hC4 hE, mul_nonneg hC5 hE, mul_nonneg hC6 hE]
  · have hd : ‖fderiv ℝ (UnforcedLeray.Train.isoV ν s) z‖ ≤
        ‖fderiv ℝ (UnforcedLeray.Train.isoV ν s) z (1, 0)‖ +
          ‖fderiv ℝ (UnforcedLeray.Train.isoV ν s) z (0, 1)‖ :=
      clm_norm_le_basis _
    rw [(fderiv_basis ν s z).1, (fderiv_basis ν s z).2] at hd
    have hE : 0 ≤ Real.exp (-(β * z.1 ^ 2)) := (Real.exp_pos _).le
    have hb : ‖UnforcedLeray.Train.toVec (UnforcedLeray.B0146.u1x (UnforcedLeray.B0113.heatWidth ν s) z,
        UnforcedLeray.B0146.u2x (UnforcedLeray.B0113.heatWidth ν s) z)‖ +
        ‖UnforcedLeray.Train.toVec (UnforcedLeray.B0146.u1y (UnforcedLeray.B0113.heatWidth ν s) z,
        UnforcedLeray.B0146.u2y (UnforcedLeray.B0113.heatWidth ν s) z)‖ ≤
        (|UnforcedLeray.B0146.u1x (UnforcedLeray.B0113.heatWidth ν s) z| +
          |UnforcedLeray.B0146.u2x (UnforcedLeray.B0113.heatWidth ν s) z|) +
        (|UnforcedLeray.B0146.u1y (UnforcedLeray.B0113.heatWidth ν s) z| +
          |UnforcedLeray.B0146.u2y (UnforcedLeray.B0113.heatWidth ν s) z|) :=
      add_le_add (norm_toVec_le_abs _ _) (norm_toVec_le_abs _ _)
    have e3 := m3 _ ha z
    have e4 := m4 _ ha z
    have e5 := m5 _ ha z
    have e6 := m6 _ ha z
    have hsum : (C1 + C2 + C3 + C4 + C5 + C6) * Real.exp (-(β * z.1 ^ 2)) =
        C1 * Real.exp (-(β * z.1 ^ 2)) + C2 * Real.exp (-(β * z.1 ^ 2)) +
        C3 * Real.exp (-(β * z.1 ^ 2)) + C4 * Real.exp (-(β * z.1 ^ 2)) +
        C5 * Real.exp (-(β * z.1 ^ 2)) + C6 * Real.exp (-(β * z.1 ^ 2)) := by ring
    nlinarith [mul_nonneg hC1 hE, mul_nonneg hC2 hE]

end UnforcedLeray.Short.IIb.CylPDE
