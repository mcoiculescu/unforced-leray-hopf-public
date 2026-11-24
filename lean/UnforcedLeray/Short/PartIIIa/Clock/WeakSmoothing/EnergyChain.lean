import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# The scalar energy chain (SP 3072-3073): proof of `AdjointEnergyChain`

The proof uses monotonicity only (no integrals):
* Step 1: `exp(-Cζ) e0 ζ` is antitone, so `e0 ζ ≤ exp(Cζ) e0 0`.
* Step P: `P ζ = e0 ζ + βζ e1 ζ` has `P' ≤ 3C P`, so `P Δ ≤ exp(3C) P ε` for `ε ∈ (0, Δ)`.
* Step S: for each `M > 0` some `ε ∈ (0, Δ)` has `β ε e1 ε ≤ M`; otherwise
  `e0 + M log ζ - C B ζ` (`B = exp C e0 0`) is antitone while tending to `-∞`.
Combining, `e0 Δ + βΔ e1 Δ ≤ exp(3C) exp(C) e0 0`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIIa

/-- A function continuous on `[a, b]` whose derivative is `≤ 0` on `(a, b)` satisfies `g b ≤ g a`. -/
theorem egc_anti {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, ∃ D : ℝ, HasDerivAt g D x ∧ D ≤ 0) : g b ≤ g a := by
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  have hanti : AntitoneOn g (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hc ?_ ?_
    · rw [hint]
      intro x hx
      obtain ⟨D, hD, _⟩ := hd x hx
      exact hD.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [hint] at hx
      obtain ⟨D, hD, hle⟩ := hd x hx
      rw [hD.deriv]
      exact hle
  exact hanti ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab

/-- Step 1: `e0 ζ ≤ exp(Cζ) e0 0` on `[0, Δ]`. -/
theorem egc_step1 {C β Δ : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) (hΔ1 : Δ ≤ 1)
    {e0 e1 : ℝ → ℝ} (h0c : ContinuousOn e0 (Icc 0 Δ))
    (h1nn : ∀ ζ ∈ Ioc 0 Δ, 0 ≤ e1 ζ)
    (hD0 : ∀ ζ ∈ Ioo 0 Δ, ∃ D : ℝ, HasDerivAt e0 D ζ ∧ D + β * e1 ζ ≤ C * e0 ζ) :
    ∀ ζ ∈ Icc 0 Δ, e0 ζ ≤ Real.exp (C * ζ) * e0 0 := by
  intro ζ hζ
  have hζΔ : ζ ≤ Δ := hζ.2
  have key : Real.exp (-C * ζ) * e0 ζ ≤ e0 0 := by
    have h := egc_anti (g := fun x => Real.exp (-C * x) * e0 x) hζ.1
      (((by fun_prop : Continuous fun x : ℝ => Real.exp (-C * x)).continuousOn).mul
        (h0c.mono (Icc_subset_Icc le_rfl hζΔ)))
      (fun x hx => by
        obtain ⟨D, hD, hle⟩ := hD0 x ⟨hx.1, lt_of_lt_of_le hx.2 hζΔ⟩
        have hE : HasDerivAt (fun y => Real.exp (-C * y)) (Real.exp (-C * x) * (-C * 1)) x :=
          ((hasDerivAt_id' x).const_mul (-C)).exp
        have hM := hE.mul hD
        refine ⟨_, hM, ?_⟩
        have hp := Real.exp_pos (-C * x)
        have he1 : 0 ≤ e1 x := h1nn x ⟨hx.1, (lt_of_lt_of_le hx.2 hζΔ).le⟩
        nlinarith [mul_le_mul_of_nonneg_left (show D - C * e0 x ≤ -(β * e1 x) by linarith) hp.le,
          mul_nonneg (mul_nonneg hβ.le he1) hp.le])
    simpa using h
  have hpos : 0 < Real.exp (C * ζ) := Real.exp_pos _
  have hsum : C * ζ + -C * ζ = 0 := by ring
  have hinv : Real.exp (C * ζ) * Real.exp (-C * ζ) = 1 := by
    rw [← Real.exp_add, hsum, Real.exp_zero]
  calc e0 ζ = Real.exp (C * ζ) * (Real.exp (-C * ζ) * e0 ζ) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ Real.exp (C * ζ) * e0 0 := mul_le_mul_of_nonneg_left key hpos.le

/-- Step P: `P = e0 + βζ e1` satisfies `P' ≤ 3C P`, hence `P Δ ≤ exp(3C) P ε`. -/
theorem egc_stepP {C β Δ ε : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) (hβ1 : β ≤ 1) (hΔ1 : Δ ≤ 1)
    {e0 e1 e2 : ℝ → ℝ} (h0c : ContinuousOn e0 (Icc 0 Δ)) (h1c : ContinuousOn e1 (Ioc 0 Δ))
    (h0nn : ∀ ζ ∈ Icc 0 Δ, 0 ≤ e0 ζ) (h1nn : ∀ ζ ∈ Ioc 0 Δ, 0 ≤ e1 ζ)
    (h2nn : ∀ ζ ∈ Ioo 0 Δ, 0 ≤ e2 ζ)
    (hD0 : ∀ ζ ∈ Ioo 0 Δ, ∃ D : ℝ, HasDerivAt e0 D ζ ∧ D + β * e1 ζ ≤ C * e0 ζ)
    (hD1 : ∀ ζ ∈ Ioo 0 Δ, ∃ D : ℝ, HasDerivAt e1 D ζ ∧ D + β * e2 ζ ≤ C * (e1 ζ + e0 ζ))
    (hε : ε ∈ Ioo 0 Δ) :
    e0 Δ + β * Δ * e1 Δ ≤ Real.exp (3 * C) * (e0 ε + β * ε * e1 ε) := by
  obtain ⟨hε0, hεΔ⟩ := hε
  have hPc : ContinuousOn (fun x => e0 x + β * x * e1 x) (Icc ε Δ) := by
    have h0' : ContinuousOn e0 (Icc ε Δ) := h0c.mono (Icc_subset_Icc hε0.le le_rfl)
    have h1' : ContinuousOn e1 (Icc ε Δ) :=
      h1c.mono (fun x hx => ⟨lt_of_lt_of_le hε0 hx.1, hx.2⟩)
    exact h0'.add ((by fun_prop : ContinuousOn (fun x : ℝ => β * x) (Icc ε Δ)).mul h1')
  have hanti := egc_anti (g := fun x => Real.exp (-(3 * C) * x) * (e0 x + β * x * e1 x))
    hεΔ.le
    ((by fun_prop : ContinuousOn (fun x : ℝ => Real.exp (-(3 * C) * x)) (Icc ε Δ)).mul hPc)
    (fun x hx => by
      have hx0 : 0 < x := lt_trans hε0 hx.1
      have hxΔ : x < Δ := hx.2
      obtain ⟨D0, hD0x, hle0⟩ := hD0 x ⟨hx0, hxΔ⟩
      obtain ⟨D1, hD1x, hle1⟩ := hD1 x ⟨hx0, hxΔ⟩
      have hE : HasDerivAt (fun y => Real.exp (-(3 * C) * y))
          (Real.exp (-(3 * C) * x) * (-(3 * C) * 1)) x :=
        ((hasDerivAt_id' x).const_mul (-(3 * C))).exp
      have hPd : HasDerivAt (fun y => e0 y + β * y * e1 y)
          (D0 + (β * 1 * e1 x + β * x * D1)) x :=
        hD0x.add (((hasDerivAt_id' x).const_mul β).mul hD1x)
      refine ⟨_, hE.mul hPd, ?_⟩
      have hp := Real.exp_pos (-(3 * C) * x)
      have he1 : 0 ≤ e1 x := h1nn x ⟨hx0, hxΔ.le⟩
      have he0 : 0 ≤ e0 x := h0nn x ⟨hx0.le, hxΔ.le⟩
      have he2 : 0 ≤ e2 x := h2nn x ⟨hx0, hxΔ⟩
      have hβx : 0 ≤ β * x := (mul_pos hβ hx0).le
      have hβx1 : β * x ≤ 1 := by nlinarith [mul_le_mul hβ1 hxΔ.le hx0.le zero_le_one]
      have hPdb : D0 + (β * 1 * e1 x + β * x * D1) ≤ 3 * C * (e0 x + β * x * e1 x) := by
        have hD1' : β * x * D1 ≤ β * x * (C * (e1 x + e0 x) - β * e2 x) :=
          mul_le_mul_of_nonneg_left (by linarith) hβx
        nlinarith [mul_nonneg (mul_nonneg hC he0) (sub_nonneg.mpr hβx1),
          mul_nonneg (mul_nonneg hC hβx) he1, mul_nonneg hC he0,
          mul_nonneg hβx (mul_nonneg hβ.le he2)]
      nlinarith [mul_le_mul_of_nonneg_left hPdb hp.le])
  have hgle : Real.exp (-(3 * C) * Δ) * (e0 Δ + β * Δ * e1 Δ) ≤
      Real.exp (-(3 * C) * ε) * (e0 ε + β * ε * e1 ε) := hanti
  have hPε0 : 0 ≤ e0 ε + β * ε * e1 ε :=
    add_nonneg (h0nn ε ⟨hε0.le, hεΔ.le⟩)
      (mul_nonneg (mul_nonneg hβ.le hε0.le) (h1nn ε ⟨hε0, hεΔ.le⟩))
  have hu := Real.exp_pos (3 * C * Δ)
  have hexpk : Real.exp (-(3 * C) * Δ) * Real.exp (3 * C * Δ) = 1 := by
    have h0 : -(3 * C) * Δ + 3 * C * Δ = 0 := by ring
    rw [← Real.exp_add, h0, Real.exp_zero]
  have hexp3 : Real.exp (-(3 * C) * ε + 3 * C * Δ) ≤ Real.exp (3 * C) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hC (show (0 : ℝ) ≤ 1 - Δ + ε by linarith)]
  calc e0 Δ + β * Δ * e1 Δ
      = (e0 Δ + β * Δ * e1 Δ) * (Real.exp (-(3 * C) * Δ) * Real.exp (3 * C * Δ)) := by
        rw [hexpk, mul_one]
    _ = (Real.exp (-(3 * C) * Δ) * (e0 Δ + β * Δ * e1 Δ)) * Real.exp (3 * C * Δ) := by ring
    _ ≤ (Real.exp (-(3 * C) * ε) * (e0 ε + β * ε * e1 ε)) * Real.exp (3 * C * Δ) :=
        mul_le_mul_of_nonneg_right hgle hu.le
    _ = (e0 ε + β * ε * e1 ε) * Real.exp (-(3 * C) * ε + 3 * C * Δ) := by
        rw [Real.exp_add]; ring
    _ ≤ (e0 ε + β * ε * e1 ε) * Real.exp (3 * C) :=
        mul_le_mul_of_nonneg_left hexp3 hPε0
    _ = Real.exp (3 * C) * (e0 ε + β * ε * e1 ε) := mul_comm _ _

/-- Step S: for every `M > 0` some `ε ∈ (0, Δ)` has `β ε e1 ε ≤ M`. -/
theorem egc_select {C β Δ M : ℝ} (hC : 0 ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hM : 0 < M)
    {e0 e1 : ℝ → ℝ} (h0c : ContinuousOn e0 (Icc 0 Δ)) (h0nn : ∀ ζ ∈ Icc 0 Δ, 0 ≤ e0 ζ)
    (hbound : ∀ ζ ∈ Icc 0 Δ, e0 ζ ≤ Real.exp C * e0 0)
    (hD0 : ∀ ζ ∈ Ioo 0 Δ, ∃ D : ℝ, HasDerivAt e0 D ζ ∧ D + β * e1 ζ ≤ C * e0 ζ) :
    ∃ ε ∈ Ioo 0 Δ, β * ε * e1 ε ≤ M := by
  by_contra hcon
  push_neg at hcon
  have hB0' : 0 ≤ Real.exp C * e0 0 := mul_nonneg (Real.exp_pos C).le (h0nn 0 ⟨le_rfl, hΔ.le⟩)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.exp C * e0 0 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; exact hB0'
  have hbB : ∀ ζ ∈ Icc 0 Δ, e0 ζ ≤ B := fun ζ hζ => by rw [hBdef]; exact hbound ζ hζ
  have hMne : M ≠ 0 := hM.ne'
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (e0 Δ + M * Real.log Δ - C * B * Δ - B - 1) / M := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min Δ (Real.exp X) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min hΔ (Real.exp_pos _)
  have hεΔ : ε ≤ Δ := by rw [hε]; exact min_le_left _ _
  have hεX : ε ≤ Real.exp X := by rw [hε]; exact min_le_right _ _
  have hlog : Real.log ε ≤ X := by
    have h := Real.log_le_log hε0 hεX
    rwa [Real.log_exp] at h
  have hML : M * Real.log ε ≤ e0 Δ + M * Real.log Δ - C * B * Δ - B - 1 := by
    have h1 : M * Real.log ε ≤ M * X := mul_le_mul_of_nonneg_left hlog hM.le
    have hMX : M * X = e0 Δ + M * Real.log Δ - C * B * Δ - B - 1 := by
      rw [hX]; field_simp
    linarith
  have hc : ContinuousOn (fun x => e0 x + M * Real.log x - C * B * x) (Icc ε Δ) := by
    have h0' : ContinuousOn e0 (Icc ε Δ) := h0c.mono (Icc_subset_Icc hε0.le le_rfl)
    have hl : ContinuousOn (fun x => Real.log x) (Icc ε Δ) :=
      Real.continuousOn_log.mono (fun x hx => (lt_of_lt_of_le hε0 hx.1).ne')
    exact (h0'.add (continuousOn_const.mul hl)).sub
      (by fun_prop : ContinuousOn (fun x : ℝ => C * B * x) (Icc ε Δ))
  have hd : ∀ x ∈ Ioo ε Δ, ∃ D : ℝ,
      HasDerivAt (fun x => e0 x + M * Real.log x - C * B * x) D x ∧ D ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := lt_trans hε0 hx.1
    obtain ⟨D, hD, hle⟩ := hD0 x ⟨hx0, hx.2⟩
    have hL : HasDerivAt (fun y => M * Real.log y) (M * x⁻¹) x :=
      (Real.hasDerivAt_log hx0.ne').const_mul M
    have hf' := (hD.add hL).sub ((hasDerivAt_id' x).const_mul (C * B))
    refine ⟨_, hf', ?_⟩
    have hinv : M * x⁻¹ < β * e1 x := by
      rw [← div_eq_mul_inv, div_lt_iff₀ hx0]
      nlinarith [hcon x ⟨hx0, hx.2⟩]
    have hb : e0 x ≤ B := hbB x ⟨hx0.le, hx.2.le⟩
    nlinarith [mul_le_mul_of_nonneg_left hb hC]
  have hfa := egc_anti (g := fun x => e0 x + M * Real.log x - C * B * x) hεΔ hc hd
  have hfa' : e0 Δ + M * Real.log Δ - C * B * Δ ≤ e0 ε + M * Real.log ε - C * B * ε := hfa
  have hbε : e0 ε ≤ B := hbB ε ⟨hε0.le, hεΔ⟩
  have hCBε : 0 ≤ C * B * ε := mul_nonneg (mul_nonneg hC hB0) hε0.le
  linarith

/-- The scalar energy chain (SP 3072-3073). -/
theorem adjointEnergyChain : AdjointEnergyChain := by
  intro C hC
  refine ⟨Real.exp (3 * C) * Real.exp C, by positivity, ?_⟩
  intro β Δ hβ hβ1 hΔ hΔ1 e0 e1 e2 h0c h1c h0nn h1nn h2nn hD0 hD1
  have hbound : ∀ ζ ∈ Icc 0 Δ, e0 ζ ≤ Real.exp C * e0 0 := by
    intro ζ hζ
    have h := egc_step1 hC hβ hΔ1 h0c h1nn hD0 ζ hζ
    have hexp : Real.exp (C * ζ) ≤ Real.exp C :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hC (sub_nonneg.mpr (hζ.2.trans hΔ1))])
    exact h.trans (mul_le_mul_of_nonneg_right hexp (h0nn 0 ⟨le_rfl, hΔ.le⟩))
  have key : ∀ M : ℝ, 0 < M →
      e0 Δ + β * Δ * e1 Δ ≤ Real.exp (3 * C) * (Real.exp C * e0 0 + M) := by
    intro M hM
    obtain ⟨ε, hε, hεM⟩ :=
      egc_select hC hΔ hΔ1 hM h0c h0nn hbound hD0
    have h1 := egc_stepP hC hβ hβ1 hΔ1 h0c h1c h0nn h1nn h2nn hD0 hD1 hε
    have h2 : e0 ε + β * ε * e1 ε ≤ Real.exp C * e0 0 + M := by
      have := hbound ε ⟨hε.1.le, hε.2.le⟩
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (3 * C)).le
    linarith
  have hP : e0 Δ + β * Δ * e1 Δ ≤ Real.exp (3 * C) * Real.exp C * e0 0 := by
    by_contra hne
    push_neg at hne
    have hη : 0 < (e0 Δ + β * Δ * e1 Δ) - Real.exp (3 * C) * Real.exp C * e0 0 := by linarith
    have hq : 0 < ((e0 Δ + β * Δ * e1 Δ) - Real.exp (3 * C) * Real.exp C * e0 0) /
        (2 * Real.exp (3 * C)) := div_pos hη (by positivity)
    have hk := key _ hq
    have heq : Real.exp (3 * C) * (Real.exp C * e0 0 +
        ((e0 Δ + β * Δ * e1 Δ) - Real.exp (3 * C) * Real.exp C * e0 0) / (2 * Real.exp (3 * C)))
        = Real.exp (3 * C) * Real.exp C * e0 0 +
          ((e0 Δ + β * Δ * e1 Δ) - Real.exp (3 * C) * Real.exp C * e0 0) / 2 := by
      field_simp
    linarith
  have hβe1 : 0 ≤ β * Δ * e1 Δ :=
    mul_nonneg (mul_nonneg hβ.le hΔ.le) (h1nn Δ ⟨hΔ, le_rfl⟩)
  have he0Δ : 0 ≤ e0 Δ := h0nn Δ ⟨hΔ.le, le_rfl⟩
  have hpos : 0 < β * Δ := mul_pos hβ hΔ
  refine ⟨by linarith, ?_⟩
  rw [show Real.exp (3 * C) * Real.exp C * (β * Δ)⁻¹ * e0 0 =
      (Real.exp (3 * C) * Real.exp C * e0 0) / (β * Δ) by ring]
  rw [le_div_iff₀ hpos]
  nlinarith

end UnforcedLeray.Short.IIIa
