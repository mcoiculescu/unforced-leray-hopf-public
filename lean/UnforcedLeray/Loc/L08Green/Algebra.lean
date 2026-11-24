import UnforcedLeray.Blueprint.Localization.Linear

/-!
# Step L8, algebra: phases and the backward exterior evolution

Helper for `UnforcedLeray.Loc.L08Green` (step `GreenStep`, `paper/main.tex` lines 371–428,
blueprint units B1015, B1016, B1018, B1019).

The manuscript defines, for `τ = k𝒯 + θ`, `s = l𝒯 + φ` (lines 386–389),
`E₊(τ,s)Π₊(s) = F_θ 𝓜₊^{k-l} G_φ`, which the blueprint writes as
`backwardExterior 𝒯 ev N τ s = E(θ,0) N^{(l-k)₊+1} E(𝒯,φ)` with `N = 𝓜₊⁻¹P₊`
(`Blueprint/Localization/Linear.lean`). This file proves, from the evolution law, the double
periodicity and the algebra of the splitting (`IsSpectralSplitting`), the identities the
Green operator of lines 410–417 uses:

* `E_mul_E_phase`: `E(τ,r) E(θ_r,0) = E(θ_τ,0) 𝓜^{k_τ-k_r}` for `r ≤ τ`;
* `E_mul_backwardExterior` ("the evolution law on the exterior fibers", line 385):
  `E(τ,r) E₊(r,s)Π₊(s) = E₊(τ,s)Π₊(s)` for `r ≤ τ ≤ s`;
* `backwardExterior_mul_E_mul_proj`: `E₊(r,s₁)Π₊(s₁) E(s₁,s) Π₊(s) = E₊(r,s)Π₊(s)` for
  `r ≤ s ≤ s₁`, and its case `s₁ = s`, `backwardExterior_mul_proj`;
* `backwardExterior_self`: `E₊(τ,τ)Π₊(τ) = Π₊(τ)`.

The phase lemmas are adapted from

over `ℂ` with `toIcoMod`; here the blueprint's `phaseOf`, `periodIndex` and the real evolution
are used.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Blueprint.L08Green

open UnforcedLeray.Blueprint

/-! ## Phases (line 386) -/

section Phase

variable {P : ℝ}

theorem phaseOf_nonneg (hP : 0 < P) (τ : ℝ) : 0 ≤ phaseOf P τ :=
  mul_nonneg hP.le (Int.fract_nonneg _)

theorem phaseOf_lt (hP : 0 < P) (τ : ℝ) : phaseOf P τ < P := by
  have h := mul_lt_mul_of_pos_left (Int.fract_lt_one (τ / P)) hP
  rwa [mul_one] at h

theorem phaseOf_le (hP : 0 < P) (τ : ℝ) : phaseOf P τ ≤ P := (phaseOf_lt hP τ).le

/-- `τ = k𝒯 + θ` with `k = periodIndex 𝒯 τ`, `θ = phaseOf 𝒯 τ`. -/
theorem index_mul_add_phase (hP : 0 < P) (τ : ℝ) :
    (periodIndex P τ : ℝ) * P + phaseOf P τ = τ := by
  unfold phaseOf periodIndex
  rw [← Int.self_sub_floor, mul_sub, mul_div_cancel₀ _ hP.ne']
  ring

theorem periodIndex_mono (hP : 0 < P) {τ s : ℝ} (h : τ ≤ s) :
    periodIndex P τ ≤ periodIndex P s :=
  Int.floor_le_floor (div_le_div_of_nonneg_right h hP.le)

end Phase

/-! ## The evolution law in multiplicative form -/

section Evolution

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}

theorem E_mul (hev : IsEvolution D c S ev) {s r τ : ℝ} (h1 : s ≤ r) (h2 : r ≤ τ) :
    ev.E τ r * ev.E r s = ev.E τ s :=
  hev.law s r τ h1 h2

theorem E_self (hev : IsEvolution D c S ev) (s : ℝ) : ev.E s s = 1 := hev.at_diag s

/-- Periodicity by any integer number of periods (adapted from
`Infra/PeriodicDichotomy/Basic.lean`, `E_add_intCast_mul`). -/
theorem E_add_intCast_mul (hev : IsEvolution D c S ev) (τ s : ℝ) (n : ℤ) :
    ev.E (τ + n * D.period) (s + n * D.period) = ev.E τ s := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have h1 : τ + ((i + 1 : ℤ) : ℝ) * D.period = (τ + ((i : ℤ) : ℝ) * D.period) + D.period := by
      push_cast; ring
    have h2 : s + ((i + 1 : ℤ) : ℝ) * D.period = (s + ((i : ℤ) : ℝ) * D.period) + D.period := by
      push_cast; ring
    rw [h1, h2, hev.periodic, ih]
  | pred i ih =>
    have h1 : τ + ((-(i : ℤ) : ℤ) : ℝ) * D.period =
        (τ + ((-(i : ℤ) - 1 : ℤ) : ℝ) * D.period) + D.period := by
      push_cast; ring
    have h2 : s + ((-(i : ℤ) : ℤ) : ℝ) * D.period =
        (s + ((-(i : ℤ) - 1 : ℤ) : ℝ) * D.period) + D.period := by
      push_cast; ring
    rw [← ih, h1, h2, hev.periodic]

/-- `E(θ + m𝒯, 0) = E(θ,0) 𝓜^m` for `θ ≥ 0`. -/
theorem E_add_natCast_mul_zero (hev : IsEvolution D c S ev) (hP : 0 < D.period) {θ : ℝ}
    (hθ : 0 ≤ θ) (m : ℕ) :
    ev.E (θ + m * D.period) 0 = ev.E θ 0 * monodromy D ev ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : D.period ≤ θ + ((m + 1 : ℕ) : ℝ) * D.period := by
      have : (0 : ℝ) ≤ m * D.period := mul_nonneg (Nat.cast_nonneg m) hP.le
      push_cast; nlinarith
    rw [← E_mul hev hP.le h1, pow_succ, ← mul_assoc, ← ih]
    have h := hev.periodic (θ + m * D.period) 0
    rw [zero_add] at h
    have h2 : θ + ((m + 1 : ℕ) : ℝ) * D.period = θ + m * D.period + D.period := by
      push_cast; ring
    rw [h2, h]
    rfl

/-- `E(𝒯, φ) E(φ, 0) = 𝓜` for `0 ≤ φ ≤ 𝒯`. -/
theorem E_period_mul_E (hev : IsEvolution D c S ev) {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ D.period) :
    ev.E D.period φ * ev.E φ 0 = monodromy D ev :=
  E_mul hev h0 h1

/-- `E(τ,r) E(θ_r,0) = E(θ_τ,0) 𝓜^{k_τ-k_r}` for `r ≤ τ` (lines 386–389). -/
theorem E_mul_E_phase (hev : IsEvolution D c S ev) (hP : 0 < D.period) {r τ : ℝ}
    (h : r ≤ τ) :
    ev.E τ r * ev.E (phaseOf D.period r) 0 =
      ev.E (phaseOf D.period τ) 0 *
        monodromy D ev ^ (periodIndex D.period τ - periodIndex D.period r).toNat := by
  have hk : periodIndex D.period r ≤ periodIndex D.period τ := periodIndex_mono hP h
  have hm : (((periodIndex D.period τ - periodIndex D.period r).toNat : ℕ) : ℝ) =
      (periodIndex D.period τ : ℝ) - periodIndex D.period r := by
    have h1 : (((periodIndex D.period τ - periodIndex D.period r).toNat : ℕ) : ℤ) =
        periodIndex D.period τ - periodIndex D.period r :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hk)
    rw [← Int.cast_natCast, h1, Int.cast_sub]
  have hτ := index_mul_add_phase hP τ
  have hr := index_mul_add_phase hP r
  set m := (periodIndex D.period τ - periodIndex D.period r).toNat with hm_def
  have e1 : phaseOf D.period τ + (m : ℝ) * D.period =
      τ - (periodIndex D.period r : ℝ) * D.period := by
    rw [hm]; linear_combination hτ
  have ha : phaseOf D.period τ + (m : ℝ) * D.period +
      (periodIndex D.period r : ℝ) * D.period = τ := by linarith
  have hb : phaseOf D.period r + (periodIndex D.period r : ℝ) * D.period = r := by linarith
  have hshift : ev.E τ r = ev.E (phaseOf D.period τ + m * D.period) (phaseOf D.period r) := by
    have := E_add_intCast_mul hev (phaseOf D.period τ + m * D.period) (phaseOf D.period r)
      (periodIndex D.period r)
    rw [ha, hb] at this
    exact this
  have hle : phaseOf D.period r ≤ phaseOf D.period τ + m * D.period := by linarith
  rw [hshift, E_mul hev (phaseOf_nonneg hP r) hle,
    E_add_natCast_mul_zero hev hP (phaseOf_nonneg hP τ)]

end Evolution

/-! ## The algebra of the splitting -/

section Splitting

variable {D : BackgroundData} {ev : Evolution} {sp : SpectralSplitting X}

theorem N_mul_Q (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) :
    sp.MplusInv * sp.Pplus = sp.MplusInv := hsp.inverse_kernel

theorem Q_mul_N (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) :
    sp.Pplus * sp.MplusInv = sp.MplusInv := hsp.inverse_range

theorem M_mul_N (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) :
    monodromy D ev * sp.MplusInv = sp.Pplus := hsp.inverse_right

/-- `𝓜₊⁻¹P₊ 𝓜 = P₊`. -/
theorem N_mul_M (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) :
    sp.MplusInv * monodromy D ev = sp.Pplus := by
  have hc : monodromy D ev * sp.Pplus = sp.Pplus * monodromy D ev := hsp.commutes
  have hl : sp.MplusInv * (monodromy D ev * sp.Pplus) = sp.Pplus := hsp.inverse_left
  calc sp.MplusInv * monodromy D ev = (sp.MplusInv * sp.Pplus) * monodromy D ev := by
        rw [N_mul_Q hsp]
    _ = sp.MplusInv * (monodromy D ev * sp.Pplus) := by rw [mul_assoc, hc]
    _ = sp.Pplus := hl

theorem commute_Q_M_pow (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (m : ℕ) :
    sp.Pplus * monodromy D ev ^ m = monodromy D ev ^ m * sp.Pplus := by
  have hc : Commute sp.Pplus (monodromy D ev) := (show monodromy D ev * sp.Pplus =
    sp.Pplus * monodromy D ev from hsp.commutes).symm
  exact (hc.pow_right m).eq

/-- `𝓜 N^{b+2} = N^{b+1}`. -/
theorem M_mul_N_pow (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (b : ℕ) :
    monodromy D ev * sp.MplusInv ^ (b + 1 + 1) = sp.MplusInv ^ (b + 1) := by
  rw [pow_succ' sp.MplusInv (b + 1), ← mul_assoc, M_mul_N hsp, pow_succ' sp.MplusInv b,
    ← mul_assoc, Q_mul_N hsp]

/-- `𝓜^m N^{b+1+m} = N^{b+1}`. -/
theorem M_pow_mul_N_pow (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (b m : ℕ) : monodromy D ev ^ m * sp.MplusInv ^ (b + 1 + m) = sp.MplusInv ^ (b + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, show b + 1 + (m + 1) = (b + m) + 1 + 1 by omega, mul_assoc,
      M_mul_N_pow hsp, show b + m + 1 = b + 1 + m by omega, ih]

/-- `N^{a+m} 𝓜^m N = N^{a+1}`. -/
theorem N_pow_mul_M_pow_mul_N (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (a m : ℕ) :
    sp.MplusInv ^ (a + m) * monodromy D ev ^ m * sp.MplusInv = sp.MplusInv ^ (a + 1) := by
  induction m with
  | zero => simp [pow_succ]
  | succ m ih =>
    rw [show a + (m + 1) = a + m + 1 by omega, pow_succ sp.MplusInv (a + m),
      pow_succ' (monodromy D ev) m]
    calc sp.MplusInv ^ (a + m) * sp.MplusInv * (monodromy D ev * monodromy D ev ^ m) *
          sp.MplusInv
        = sp.MplusInv ^ (a + m) * (sp.MplusInv * monodromy D ev) * monodromy D ev ^ m *
            sp.MplusInv := by simp only [mul_assoc]
      _ = sp.MplusInv ^ (a + m) * (sp.Pplus * monodromy D ev ^ m) * sp.MplusInv := by
            rw [N_mul_M hsp]; simp only [mul_assoc]
      _ = sp.MplusInv ^ (a + m) * monodromy D ev ^ m * (sp.Pplus * sp.MplusInv) := by
            rw [commute_Q_M_pow hsp]; simp only [mul_assoc]
      _ = sp.MplusInv ^ (a + 1) := by rw [Q_mul_N hsp, ih]

end Splitting

/-! ## The backward exterior evolution (lines 386–389) -/

section Backward

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}
  {sp : SpectralSplitting X}

theorem backwardExterior_eq (N : X →L[ℝ] X) (τ s : ℝ) :
    backwardExterior D.period ev N τ s =
      ev.E (phaseOf D.period τ) 0 *
        (N ^ ((periodIndex D.period s - periodIndex D.period τ).toNat + 1) *
          ev.E D.period (phaseOf D.period s)) := rfl

theorem exteriorProjection_eq (N : X →L[ℝ] X) (τ : ℝ) :
    exteriorProjection D.period ev N τ =
      ev.E (phaseOf D.period τ) 0 * (N * ev.E D.period (phaseOf D.period τ)) := rfl

/-- `E₊(τ,τ)Π₊(τ) = Π₊(τ)`. -/
theorem backwardExterior_self (N : X →L[ℝ] X) (τ : ℝ) :
    backwardExterior D.period ev N τ τ = exteriorProjection D.period ev N τ := by
  rw [backwardExterior_eq, exteriorProjection_eq, sub_self, Int.toNat_zero, zero_add, pow_one]

/-- The evolution law on the exterior fibers: `E(τ,r) E₊(r,s)Π₊(s) = E₊(τ,s)Π₊(s)` for
`r ≤ τ ≤ s` (line 385). -/
theorem E_mul_backwardExterior (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hP : 0 < D.period)
    {r τ s : ℝ} (hrτ : r ≤ τ) (hτs : τ ≤ s) :
    ev.E τ r * backwardExterior D.period ev sp.MplusInv r s =
      backwardExterior D.period ev sp.MplusInv τ s := by
  have k1 := periodIndex_mono hP hrτ
  have k2 := periodIndex_mono hP hτs
  have e : (periodIndex D.period s - periodIndex D.period r).toNat + 1 =
      (periodIndex D.period s - periodIndex D.period τ).toNat + 1 +
        (periodIndex D.period τ - periodIndex D.period r).toNat := by omega
  rw [backwardExterior_eq, backwardExterior_eq, ← mul_assoc, E_mul_E_phase hev hP hrτ, e,
    mul_assoc, ← mul_assoc (monodromy D ev ^ _), M_pow_mul_N_pow hsp]

/-- `E₊(r,s₁)Π₊(s₁) E(s₁,s) Π₊(s) = E₊(r,s)Π₊(s)` for `r ≤ s ≤ s₁`. -/
theorem backwardExterior_mul_E_mul_proj (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hP : 0 < D.period)
    {r s s₁ : ℝ} (hrs : r ≤ s) (hss : s ≤ s₁) :
    backwardExterior D.period ev sp.MplusInv r s₁ * ev.E s₁ s *
        exteriorProjection D.period ev sp.MplusInv s =
      backwardExterior D.period ev sp.MplusInv r s := by
  have k1 := periodIndex_mono hP hrs
  have k2 := periodIndex_mono hP hss
  have e : (periodIndex D.period s₁ - periodIndex D.period r).toNat + 1 =
      (periodIndex D.period s - periodIndex D.period r).toNat +
        ((periodIndex D.period s₁ - periodIndex D.period s).toNat + 1) := by omega
  rw [backwardExterior_eq, backwardExterior_eq, exteriorProjection_eq]
  simp only [mul_assoc]
  rw [← mul_assoc (ev.E s₁ s), E_mul_E_phase hev hP hss, mul_assoc (ev.E (phaseOf D.period s₁) 0),
    ← mul_assoc (ev.E D.period (phaseOf D.period s₁)),
    E_period_mul_E hev (phaseOf_nonneg hP s₁) (phaseOf_le hP s₁), ← mul_assoc (monodromy D ev),
    ← pow_succ', e, ← mul_assoc (sp.MplusInv ^ _), ← mul_assoc (sp.MplusInv ^ _ * _),
    N_pow_mul_M_pow_mul_N hsp]

/-- `E₊(τ,s)Π₊(s) Π₊(s) = E₊(τ,s)Π₊(s)` for `τ ≤ s`. -/
theorem backwardExterior_mul_proj (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hP : 0 < D.period)
    {τ s : ℝ} (hτs : τ ≤ s) :
    backwardExterior D.period ev sp.MplusInv τ s * exteriorProjection D.period ev sp.MplusInv s =
      backwardExterior D.period ev sp.MplusInv τ s := by
  have h := backwardExterior_mul_E_mul_proj hev hsp hP hτs le_rfl
  rwa [E_self hev, mul_one] at h

end Backward

end UnforcedLeray.Blueprint.L08Green
