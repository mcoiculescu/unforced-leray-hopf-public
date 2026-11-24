import UnforcedLeray.Blueprint.Localization.Linear
import UnforcedLeray.Infra.EvolutionContinuity.Abstract

/-!
# Step L7 `ProjectionStep`: the phase projections and the dichotomy bounds

`paper/main.tex`, lines 371–404 (`loc:eq:projections`, `loc:eq:past-bound`,
`loc:eq:future-bound`); blueprint units B1015, B1016, B1017.

The step (`UnforcedLeray.Blueprint.ProjectionStep`, `Blueprint/Localization/Linear.lean`) receives
an evolution `E(τ,s)` with the properties of step L3 and a real spectral splitting of the
monodromy `𝓜 = E(𝒯,0)` with the properties of step L6, and asks for the properties of the
explicit `Π₊(τ) = F_θ G_θ = E(θ,0) 𝓜₊⁻¹P₊ E(𝒯,θ)` and of the explicit backward exterior
evolution `E₊(τ,s)Π₊(s) = E(θ,0) N^{l-k+1} E(𝒯,φ)` (`N = 𝓜₊⁻¹P₊`), together with a `Z`-valued
lift of the latter. Everything is proved here from the clauses of `IsEvolution` and
`IsSpectralSplitting`; nothing else is assumed.

Proof outline (the manuscript's, lines 371–404):
* algebra of `N`: `𝓜N = N𝓜 = P₊`, `N𝓜N = N`, `P₊N = N`, `𝓜ʲN^{j+1} = N`;
* factorization of a forward interval (`E_split`): with `τ = k𝒯 + θ`, `s = l𝒯 + φ`, either
  `k = l` and `E(τ,s) = E(θ,φ)`, or `k = l + n + 1` and `E(τ,s) = E(θ,0) 𝓜ⁿ E(𝒯,φ)`;
* projections, intertwining, the backward range and inverse, from this factorization;
* strong continuity of `θ ↦ Π₊(θ)f` on one closed period, then across the seam
  (`Infra/EvolutionContinuity/Abstract.lean`: `continuous_apply_of_periodic`,
  `continuousWithinAt_clm_apply`);
* `loc:eq:past-bound`: `‖E(τ,s)(1 - Π₊(s))‖_{X→X} ≤ K e^{β₋(τ-s)}` from
  `‖𝓜ⁿ(1-P₊)‖ ≤ C e^{β₋ n𝒯}`, then `E_Z(τ,s) = E_Z(τ,τ-1) E(τ-1,s)` for `τ - s > 1` and the
  short-time smoothing for `τ - s ≤ 1`;
* `loc:eq:future-bound`: the lift is `E_Z(θ+𝒯,0) N^{l-k+2} E(𝒯,φ)` (one-period smoothing,
  `N^{m+1} = 𝓜 N^{m+2}`, line 393), bounded by `‖N^n‖ ≤ C e^{-β₊ n𝒯}`.

The complex-space infrastructure `Infra/PeriodicDichotomy`, `Infra/SmoothedDichotomy` and
`Infra/RealProjections` builds `P₊` as a Riesz projection on a complexification. Step L7 is stated
for an arbitrary real splitting satisfying `IsSpectralSplitting`, so its proof here works directly
on the real space `X` with the abstract clauses (it follows the same factorization as
`Infra/PeriodicDichotomy/Rates.lean`); only the continuity lemmas of
`Infra/EvolutionContinuity/Abstract.lean` are imported.

Main result: `UnforcedLeray.Loc.L07.projectionStep : UnforcedLeray.Blueprint.ProjectionStep`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Loc.L07

open UnforcedLeray.Blueprint

/-! ## Phases (lines 384–388) -/

section Phase

variable {T : ℝ}

theorem phaseOf_nonneg (hT : 0 < T) (τ : ℝ) : 0 ≤ phaseOf T τ :=
  mul_nonneg hT.le (Int.fract_nonneg _)

theorem phaseOf_lt (hT : 0 < T) (τ : ℝ) : phaseOf T τ < T := by
  unfold phaseOf
  calc T * Int.fract (τ / T) < T * 1 := mul_lt_mul_of_pos_left (Int.fract_lt_one _) hT
    _ = T := mul_one T

/-- `τ = k𝒯 + θ` (line 387). -/
theorem index_mul_add_phase (hT : 0 < T) (τ : ℝ) :
    (periodIndex T τ : ℝ) * T + phaseOf T τ = τ := by
  unfold periodIndex phaseOf
  have h : T * (τ / T) = τ := by field_simp
  rw [← Int.self_sub_floor]
  linear_combination h

theorem periodIndex_mono (hT : 0 < T) {τ s : ℝ} (h : τ ≤ s) :
    periodIndex T τ ≤ periodIndex T s :=
  Int.floor_mono (div_le_div_of_nonneg_right h hT.le)

theorem phaseOf_add_period (hT : 0 < T) (τ : ℝ) : phaseOf T (τ + T) = phaseOf T τ := by
  unfold phaseOf
  rw [add_div, div_self hT.ne', Int.fract_add_one]

theorem phaseOf_of_mem (hT : 0 < T) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < T) : phaseOf T θ = θ := by
  unfold phaseOf
  rw [Int.fract_eq_self.mpr ⟨div_nonneg h0 hT.le, (div_lt_one hT).mpr h1⟩]
  field_simp

theorem phaseOf_self (hT : 0 < T) : phaseOf T T = 0 := by
  unfold phaseOf
  rw [div_self hT.ne', Int.fract_one, mul_zero]

end Phase

/-! ## The inclusion `Z ⊂ X` is injective -/

theorem ιZ_injective : Function.Injective ιZ := by
  intro g g' h
  have h1 : Zclass g = Zclass g' := by rw [← Xclass_ιZ, ← Xclass_ιZ, h]
  have h2 : g.toH2 = g'.toH2 := SobolevGraph.H2.ext h1
  exact (Subtype.ext h2 : (show ↥Zsub from g) = (show ↥Zsub from g'))

/-! ## Algebra of the splitting (lines 359–370) -/

section Algebra

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : E →L[ℝ] E} {T σ : ℝ}
  {sp : SpectralSplitting E}

theorem M_mul_N (hsp : IsSpectralSplitting M T σ sp) : M * sp.MplusInv = sp.Pplus :=
  hsp.inverse_right

theorem N_mul_P (hsp : IsSpectralSplitting M T σ sp) : sp.MplusInv * sp.Pplus = sp.MplusInv :=
  hsp.inverse_kernel

theorem P_mul_N (hsp : IsSpectralSplitting M T σ sp) : sp.Pplus * sp.MplusInv = sp.MplusInv :=
  hsp.inverse_range

/-- `𝓜₊⁻¹P₊ 𝓜 = P₊`. -/
theorem N_mul_M (hsp : IsSpectralSplitting M T σ sp) : sp.MplusInv * M = sp.Pplus := by
  have hk : sp.MplusInv * sp.Pplus = sp.MplusInv := hsp.inverse_kernel
  have hc : M * sp.Pplus = sp.Pplus * M := hsp.commutes
  have hl : sp.MplusInv * (M * sp.Pplus) = sp.Pplus := hsp.inverse_left
  calc sp.MplusInv * M = sp.MplusInv * sp.Pplus * M := by rw [hk]
    _ = sp.MplusInv * (M * sp.Pplus) := by rw [mul_assoc, hc]
    _ = sp.Pplus := hl

theorem commute_M_N (hsp : IsSpectralSplitting M T σ sp) : Commute M sp.MplusInv :=
  (M_mul_N hsp).trans (N_mul_M hsp).symm

theorem NMN_mul (hsp : IsSpectralSplitting M T σ sp) (Y : E →L[ℝ] E) :
    sp.MplusInv * (M * (sp.MplusInv * Y)) = sp.MplusInv * Y := by
  rw [← mul_assoc, ← mul_assoc, N_mul_M hsp, P_mul_N hsp]

theorem MN_mul (hsp : IsSpectralSplitting M T σ sp) (Y : E →L[ℝ] E) :
    M * (sp.MplusInv * Y) = sp.Pplus * Y := by
  rw [← mul_assoc, M_mul_N hsp]

theorem P_mul_N_pow (hsp : IsSpectralSplitting M T σ sp) (j : ℕ) :
    sp.Pplus * sp.MplusInv ^ (j + 1) = sp.MplusInv ^ (j + 1) := by
  rw [pow_succ', ← mul_assoc, P_mul_N hsp]

/-- `𝓜 N^{j+2} = N^{j+1}`. -/
theorem M_N_pow_mul (hsp : IsSpectralSplitting M T σ sp) (j : ℕ) (Y : E →L[ℝ] E) :
    M * (sp.MplusInv ^ (j + 1 + 1) * Y) = sp.MplusInv ^ (j + 1) * Y := by
  rw [pow_succ' sp.MplusInv (j + 1), mul_assoc, ← mul_assoc M, M_mul_N hsp, ← mul_assoc,
    P_mul_N_pow hsp]

/-- `𝓜ʲ N^{j+1} = N`. -/
theorem M_pow_N_pow_mul (hsp : IsSpectralSplitting M T σ sp) (j : ℕ) (Y : E →L[ℝ] E) :
    M ^ j * (sp.MplusInv ^ (j + 1) * Y) = sp.MplusInv * Y := by
  induction j with
  | zero => rw [pow_zero, one_mul, zero_add, pow_one]
  | succ j ih => rw [pow_succ, mul_assoc, M_N_pow_mul hsp j, ih]

/-- `N𝓜 N^{j+1} = N^{j+1}`. -/
theorem NM_N_pow_mul (hsp : IsSpectralSplitting M T σ sp) (j : ℕ) (Y : E →L[ℝ] E) :
    sp.MplusInv * (M * (sp.MplusInv ^ (j + 1) * Y)) = sp.MplusInv ^ (j + 1) * Y := by
  rw [← mul_assoc, ← mul_assoc, N_mul_M hsp, P_mul_N_pow hsp]

theorem M_pow_comm (hsp : IsSpectralSplitting M T σ sp) (n : ℕ) (Y : E →L[ℝ] E) :
    M ^ n * (M * (sp.MplusInv * Y)) = sp.MplusInv * (M * (M ^ n * Y)) := by
  have h : M ^ (n + 1) * sp.MplusInv = sp.MplusInv * M ^ (n + 1) :=
    ((commute_M_N hsp).pow_left (n + 1)).eq
  calc M ^ n * (M * (sp.MplusInv * Y)) = M ^ (n + 1) * sp.MplusInv * Y := by
        rw [pow_succ]; simp only [mul_assoc]
    _ = sp.MplusInv * M ^ (n + 1) * Y := by rw [h]
    _ = sp.MplusInv * (M * (M ^ n * Y)) := by rw [pow_succ']; simp only [mul_assoc]

end Algebra

/-! ## The evolution on whole periods (lines 299–306, 386–392) -/

section Evolution

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}

theorem E_congr {a b a' b' : ℝ} (ha : a = a') (hb : b = b') : ev.E a b = ev.E a' b' := by
  subst ha hb; rfl

theorem E_mul_E (hev : IsEvolution D c S ev) {s r τ : ℝ} (h1 : s ≤ r) (h2 : r ≤ τ) :
    ev.E τ r * ev.E r s = ev.E τ s := hev.law s r τ h1 h2

theorem E_mul_E_mul (hev : IsEvolution D c S ev) {s r τ : ℝ} (h1 : s ≤ r) (h2 : r ≤ τ)
    (Y : X →L[ℝ] X) : ev.E τ r * (ev.E r s * Y) = ev.E τ s * Y := by
  rw [← mul_assoc, E_mul_E hev h1 h2]

/-- `E(𝒯,θ) E(θ,0) = 𝓜` for `0 ≤ θ ≤ 𝒯`. -/
theorem E_period_mul (hev : IsEvolution D c S ev) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ D.period)
    (Y : X →L[ℝ] X) : ev.E D.period θ * (ev.E θ 0 * Y) = monodromy D ev * Y :=
  E_mul_E_mul hev h0 h1 Y

theorem E_add_nat (hev : IsEvolution D c S ev) (n : ℕ) (τ s : ℝ) :
    ev.E (τ + n * D.period) (s + n * D.period) = ev.E τ s := by
  induction n with
  | zero => exact E_congr (by simp) (by simp)
  | succ n ih =>
    rw [← ih, ← hev.periodic (τ + n * D.period) (s + n * D.period)]
    exact E_congr (by push_cast; ring) (by push_cast; ring)

/-- Double periodicity with an integer shift. -/
theorem E_add_int (hev : IsEvolution D c S ev) (n : ℤ) (τ s : ℝ) :
    ev.E (τ + n * D.period) (s + n * D.period) = ev.E τ s := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [Int.cast_natCast]
    exact E_add_nat hev m τ s
  · have h := E_add_nat hev m (τ + (((-(m : ℤ)) : ℤ) : ℝ) * D.period)
      (s + (((-(m : ℤ)) : ℤ) : ℝ) * D.period)
    rw [← h]
    exact E_congr (by push_cast; ring) (by push_cast; ring)

/-- `E(n𝒯, 0) = 𝓜ⁿ`. -/
theorem E_nat_mul (hev : IsEvolution D c S ev) (hT : 0 < D.period) (n : ℕ) :
    ev.E (n * D.period) 0 = monodromy D ev ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact (E_congr (by simp) rfl).trans (hev.at_diag 0)
  | succ n ih =>
    have h1 : ev.E (((n + 1 : ℕ) : ℝ) * D.period) (n * D.period) = monodromy D ev := by
      unfold monodromy
      rw [← E_add_nat hev n D.period 0]
      exact E_congr (by push_cast; ring) (by ring)
    have hn0 : (0 : ℝ) ≤ n * D.period := mul_nonneg (Nat.cast_nonneg n) hT.le
    have hn1 : (n : ℝ) * D.period ≤ ((n + 1 : ℕ) : ℝ) * D.period :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hT.le
    rw [← E_mul_E hev hn0 hn1, h1, ih, pow_succ']

/-- `E(θ + (n+1)𝒯, φ) = E(θ,0) 𝓜ⁿ E(𝒯,φ)` for `θ ≥ 0`, `φ ≤ 𝒯` (lines 390–392). -/
theorem E_factor (hev : IsEvolution D c S ev) (hT : 0 < D.period) {θ φ : ℝ} (hθ : 0 ≤ θ)
    (hφ : φ ≤ D.period) (n : ℕ) :
    ev.E (θ + ((n : ℝ) + 1) * D.period) φ =
      ev.E θ 0 * monodromy D ev ^ n * ev.E D.period φ := by
  have hA : ev.E (θ + ((n : ℝ) + 1) * D.period) (((n : ℝ) + 1) * D.period) = ev.E θ 0 := by
    rw [← E_add_nat hev (n + 1) θ 0]
    exact E_congr (by push_cast; ring) (by push_cast; ring)
  have hB : ev.E (((n : ℝ) + 1) * D.period) D.period = monodromy D ev ^ n := by
    rw [← E_nat_mul hev hT n, ← E_add_nat hev 1 (n * D.period) 0]
    exact E_congr (by push_cast; ring) (by push_cast; ring)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : D.period ≤ ((n : ℝ) + 1) * D.period := by nlinarith
  have h2 : ((n : ℝ) + 1) * D.period ≤ θ + ((n : ℝ) + 1) * D.period := by linarith
  rw [← E_mul_E hev (le_trans hφ h1) h2, hA, ← E_mul_E hev hφ h1, hB, mul_assoc]

/-- **Factorization of a forward interval** (lines 384–392): with `τ = k𝒯 + θ`, `s = l𝒯 + φ`
(phases in `[0,𝒯)`), either `k = l`, `φ ≤ θ` and `E(τ,s) = E(θ,φ)`, or `k = l + n + 1` and
`E(τ,s) = E(θ,0) 𝓜ⁿ E(𝒯,φ)`. -/
theorem E_split (hev : IsEvolution D c S ev) (hT : 0 < D.period) {τ s : ℝ} (h : s ≤ τ) :
    (periodIndex D.period τ = periodIndex D.period s ∧
        phaseOf D.period s ≤ phaseOf D.period τ ∧
        ev.E τ s = ev.E (phaseOf D.period τ) (phaseOf D.period s)) ∨
      ∃ n : ℕ, periodIndex D.period τ = periodIndex D.period s + n + 1 ∧
        ev.E τ s = ev.E (phaseOf D.period τ) 0 * monodromy D ev ^ n *
          ev.E D.period (phaseOf D.period s) := by
  have hτ := index_mul_add_phase hT τ
  have hs := index_mul_add_phase hT s
  have hφT := phaseOf_lt hT s
  have hθ0 := phaseOf_nonneg hT τ
  have hkl := periodIndex_mono hT h
  have hshift : ev.E τ s = ev.E (phaseOf D.period τ +
      ((periodIndex D.period τ : ℝ) - periodIndex D.period s) * D.period)
      (phaseOf D.period s) := by
    rw [← E_add_int hev (-(periodIndex D.period s)) τ s]
    exact E_congr (by push_cast; linear_combination -hτ) (by push_cast; linear_combination -hs)
  rcases eq_or_lt_of_le hkl with heq | hlt
  · left
    refine ⟨heq.symm, ?_, ?_⟩
    · rw [← heq] at hτ
      linarith
    · rw [hshift, heq, sub_self, zero_mul, add_zero]
  · right
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le
      (by omega : (0 : ℤ) ≤ periodIndex D.period τ - periodIndex D.period s - 1)
    refine ⟨n, by omega, ?_⟩
    have hn' : ((periodIndex D.period τ : ℝ) - periodIndex D.period s) = (n : ℝ) + 1 := by
      have : (periodIndex D.period τ : ℤ) - periodIndex D.period s = (n : ℤ) + 1 := by omega
      exact_mod_cast this
    rw [hshift, hn']
    exact E_factor hev hT hθ0 hφT.le n

/-- `E(θ + 𝒯, 0) = E(θ,0) 𝓜`. -/
theorem E_add_period_zero (hev : IsEvolution D c S ev) (hT : 0 < D.period) {θ : ℝ}
    (hθ : 0 ≤ θ) : ev.E (θ + D.period) 0 = ev.E θ 0 * monodromy D ev := by
  have h := hev.periodic θ 0
  rw [zero_add] at h
  rw [← h]
  exact (hev.law 0 D.period (θ + D.period) hT.le (by linarith)).symm

/-- `E_Z(τ,s) = E_Z(τ,r) E(r,s)` for `s ≤ r < τ` (the lift is unique since `Z ⊂ X`). -/
theorem EZ_factor (hev : IsEvolution D c S ev) {s r τ : ℝ} (hsr : s ≤ r) (hrτ : r < τ) :
    ev.EZ τ s = (ev.EZ τ r).comp (ev.E r s) := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply ιZ_injective
  have h1 := DFunLike.congr_fun (hev.EZ_compat s τ (lt_of_le_of_lt hsr hrτ)) x
  have h2 := DFunLike.congr_fun (hev.EZ_compat r τ hrτ) (ev.E r s x)
  have h3 := DFunLike.congr_fun (hev.law s r τ hsr hrτ.le) x
  simp only [ContinuousLinearMap.comp_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3]

/-- One strip constant `C₀` for `E` on strips of length `2𝒯 + 1`, with the smoothing
`‖E_Z(τ,s)‖ ≤ C₀ (τ-s)^{-1/2}` (line 305). -/
theorem strip (hev : IsEvolution D c S ev) (hT : 0 < D.period) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      (∀ s τ, s ≤ τ → τ ≤ s + (2 * D.period + 1) → ‖ev.E τ s‖ ≤ C₀) ∧
      (∀ s τ, s < τ → τ ≤ s + (2 * D.period + 1) →
        ‖ev.EZ τ s‖ ≤ C₀ / Real.sqrt (τ - s)) := by
  obtain ⟨C₀, hC₀⟩ := hev.strip_bounds (2 * D.period + 1) (by linarith)
  exact ⟨C₀, (norm_nonneg _).trans (hC₀ 0 0 le_rfl (by linarith)).1,
    fun s τ h1 h2 => (hC₀ s τ h1 h2).1, fun s τ h1 h2 => ((hC₀ s τ h1.le h2).2 h1).2.1⟩

end Evolution

/-! ## The phase projections (lines 371–383) -/

section Projections

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}
  {sp : SpectralSplitting X}

theorem exteriorProjection_eq (T : ℝ) (ev : Evolution) (N : X →L[ℝ] X) (τ : ℝ) :
    exteriorProjection T ev N τ = ev.E (phaseOf T τ) 0 * (N * ev.E T (phaseOf T τ)) := rfl

theorem backwardExterior_eq (T : ℝ) (ev : Evolution) (N : X →L[ℝ] X) (τ s : ℝ) :
    backwardExterior T ev N τ s = ev.E (phaseOf T τ) 0 *
      (N ^ ((periodIndex T s - periodIndex T τ).toNat + 1) * ev.E T (phaseOf T s)) := rfl

/-- `‖Π₊(τ)‖ ≤ C₀ ‖N‖ C₀` (the strip bounds give uniformly bounded `F_θ`, `G_θ`, line 376). -/
theorem proj_norm_le (hT : 0 < D.period) {C₀ : ℝ} (hC₀nn : 0 ≤ C₀)
    (hE : ∀ s τ, s ≤ τ → τ ≤ s + (2 * D.period + 1) → ‖ev.E τ s‖ ≤ C₀) (N : X →L[ℝ] X)
    (τ : ℝ) : ‖exteriorProjection D.period ev N τ‖ ≤ C₀ * (‖N‖ * C₀) := by
  have h0 := phaseOf_nonneg hT τ
  have h1 := phaseOf_lt hT τ
  rw [exteriorProjection_eq]
  refine (norm_mul_le _ _).trans (mul_le_mul (hE _ _ h0 (by linarith)) ?_ (norm_nonneg _) hC₀nn)
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (hE _ _ h1.le (by linarith)) (norm_nonneg _))

/-- `Π₊(θ)` is a projection (`loc:eq:projections`, lines 379, 382). -/
theorem proj_idempotent (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period) (θ : ℝ) :
    (exteriorProjection D.period ev sp.MplusInv θ).comp
      (exteriorProjection D.period ev sp.MplusInv θ) =
      exteriorProjection D.period ev sp.MplusInv θ := by
  have h0 := phaseOf_nonneg hT θ
  have h1 := (phaseOf_lt hT θ).le
  rw [← ContinuousLinearMap.mul_def]
  simp only [exteriorProjection_eq, mul_assoc]
  rw [E_period_mul hev h0 h1, NMN_mul hsp]

/-- Intertwining `E(τ,s)Π₊(s) = Π₊(τ)E(τ,s)`, `s ≤ τ` (line 383). -/
theorem proj_intertwine (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period)
    {s τ : ℝ} (h : s ≤ τ) :
    (ev.E τ s).comp (exteriorProjection D.period ev sp.MplusInv s) =
      (exteriorProjection D.period ev sp.MplusInv τ).comp (ev.E τ s) := by
  have hθ0 := phaseOf_nonneg hT τ
  have hθT := (phaseOf_lt hT τ).le
  have hφ0 := phaseOf_nonneg hT s
  have hφT := (phaseOf_lt hT s).le
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, exteriorProjection_eq,
    exteriorProjection_eq]
  rcases E_split hev hT h with ⟨-, hle, hEq⟩ | ⟨n, -, hEq⟩
  · rw [hEq, E_mul_E_mul hev hφ0 hle, mul_assoc, mul_assoc, E_mul_E hev hle hθT]
  · rw [hEq]
    simp only [mul_assoc]
    rw [E_period_mul hev hφ0 hφT, M_pow_comm hsp, E_period_mul hev hθ0 hθT]

/-- `θ ↦ Π₊(θ) f` is continuous on `ℝ` (equal endpoint values, periodic extension, line 382). -/
theorem proj_continuous (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period) (f : X) :
    Continuous fun θ => exteriorProjection D.period ev sp.MplusInv θ f := by
  obtain ⟨C₀, -, hE, -⟩ := strip hev hT
  refine UnforcedLeray.Infra.EvolutionContinuity.continuous_apply_of_periodic hT
    (fun t => by rw [exteriorProjection, exteriorProjection, phaseOf_add_period hT]) ?_ f
  intro x
  have hR : ContinuousOn (fun t => ev.E t 0 (sp.MplusInv (ev.E D.period t x)))
      (Icc 0 D.period) := by
    intro t₀ ht₀
    refine UnforcedLeray.Infra.EvolutionContinuity.continuousWithinAt_clm_apply
      (K := fun t => ev.E t 0) (v := fun t => sp.MplusInv (ev.E D.period t x)) ?_ ?_ ?_
    · intro e
      have hc : ContinuousOn (fun t : ℝ => ev.E t 0 e) (Icc 0 D.period) :=
        (hev.strongly_continuous e).comp
          ((continuous_id.prodMk continuous_const).continuousOn)
          (fun t ht => (show (0 : ℝ) ≤ t from ht.1))
      exact hc t₀ ht₀
    · exact ⟨C₀, eventually_nhdsWithin_of_forall fun t ht =>
        hE 0 t ht.1 (by linarith [ht.2])⟩
    · have hc : ContinuousOn (fun t : ℝ => ev.E D.period t x) (Icc 0 D.period) :=
        (hev.strongly_continuous x).comp
          ((continuous_const.prodMk continuous_id).continuousOn)
          (fun t ht => (show t ≤ D.period from ht.2))
      exact (sp.MplusInv.continuous.comp_continuousOn hc) t₀ ht₀
  refine hR.congr ?_
  intro t ht
  dsimp only
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq, exteriorProjection_eq, phaseOf_self hT, hev.at_diag, hev.at_diag]
    exact (DFunLike.congr_fun (N_mul_M hsp) x).trans (DFunLike.congr_fun (M_mul_N hsp) x).symm
  · rw [exteriorProjection_eq, phaseOf_of_mem hT ht.1 hlt]
    rfl

/-! ## The backward exterior evolution (lines 383–389) -/

/-- `Π₊(τ) E₊(τ,s)Π₊(s) = E₊(τ,s)Π₊(s)`, `τ ≤ s`. -/
theorem backward_range (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period)
    (τ s : ℝ) :
    (exteriorProjection D.period ev sp.MplusInv τ).comp
      (backwardExterior D.period ev sp.MplusInv τ s) =
      backwardExterior D.period ev sp.MplusInv τ s := by
  have hθ0 := phaseOf_nonneg hT τ
  have hθT := (phaseOf_lt hT τ).le
  rw [← ContinuousLinearMap.mul_def, exteriorProjection_eq, backwardExterior_eq]
  simp only [mul_assoc]
  rw [E_period_mul hev hθ0 hθT, NM_N_pow_mul hsp]

/-- `E(s,τ) E₊(τ,s)Π₊(s) = Π₊(s)`, `τ ≤ s`. -/
theorem backward_inverse (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period)
    {τ s : ℝ} (h : τ ≤ s) :
    (ev.E s τ).comp (backwardExterior D.period ev sp.MplusInv τ s) =
      exteriorProjection D.period ev sp.MplusInv s := by
  have hθ0 := phaseOf_nonneg hT τ
  have hθT := (phaseOf_lt hT τ).le
  rw [← ContinuousLinearMap.mul_def, exteriorProjection_eq, backwardExterior_eq]
  rcases E_split hev hT h with ⟨hidx, hle, hEq⟩ | ⟨n, hidx, hEq⟩
  · have hm : (periodIndex D.period s - periodIndex D.period τ).toNat = 0 := by
      rw [hidx, sub_self]; rfl
    rw [hm, zero_add, pow_one, hEq, E_mul_E_mul hev hθ0 hle]
  · have hm : (periodIndex D.period s - periodIndex D.period τ).toNat = n + 1 := by
      rw [hidx]; omega
    rw [hm, hEq]
    simp only [mul_assoc]
    rw [E_period_mul hev hθ0 hθT, M_N_pow_mul hsp, M_pow_N_pow_mul hsp]

/-! ## The `Z`-valued lift and `loc:eq:future-bound` (lines 393–404) -/

/-- The `Z`-valued backward exterior evolution `E_Z(θ+𝒯,0) N^{l-k+2} E(𝒯,φ)`: by
`P₊ = 𝓜𝓜₊⁻¹P₊` (line 393), `E₊(τ,s)Π₊(s) = E(θ,0) 𝓜 N^{l-k+2} E(𝒯,φ) = E(θ+𝒯,0) N^{l-k+2} E(𝒯,φ)`,
and `E(θ+𝒯,0)` smooths `X → Z` since `θ + 𝒯 > 0`. -/
def exteriorLift (T : ℝ) (ev : Evolution) (N : X →L[ℝ] X) (τ s : ℝ) : X →L[ℝ] Z :=
  (ev.EZ (phaseOf T τ + T) 0).comp
    ((N ^ ((periodIndex T s - periodIndex T τ).toNat + 1 + 1)).comp (ev.E T (phaseOf T s)))

theorem exteriorLift_lift (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period)
    (τ s : ℝ) :
    ιZ.comp (exteriorLift D.period ev sp.MplusInv τ s) =
      backwardExterior D.period ev sp.MplusInv τ s := by
  have hθ0 := phaseOf_nonneg hT τ
  unfold exteriorLift
  rw [← ContinuousLinearMap.comp_assoc, hev.EZ_compat 0 _ (by linarith),
    ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, backwardExterior_eq,
    E_add_period_zero hev hT hθ0, mul_assoc, M_N_pow_mul hsp]

/-- `loc:eq:future-bound`: `‖E₊(τ,s)Π₊(s)‖_{X→Z} ≤ C e^{β₊(τ-s)}` for `τ ≤ s`. -/
theorem future_bound (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period) :
    ∃ C : ℝ, ∀ τ s, τ ≤ s →
      ‖exteriorLift D.period ev sp.MplusInv τ s‖ ≤ C * Real.exp (sp.βplus * (τ - s)) := by
  obtain ⟨C₀, hC₀nn, hE, hEZ⟩ := strip hev hT
  obtain ⟨K₂, hK₂⟩ := hsp.unstable_rate
  have hK₂nn : 0 ≤ K₂ := by
    have h := (norm_nonneg _).trans (hK₂ 0)
    simpa using h
  refine ⟨C₀ / Real.sqrt D.period * K₂ * C₀ * Real.exp (|sp.βplus| * (3 * D.period)), ?_⟩
  intro τ s hτs
  have hθ0 := phaseOf_nonneg hT τ
  have hθT := phaseOf_lt hT τ
  have hφ0 := phaseOf_nonneg hT s
  have hφT := phaseOf_lt hT s
  have hτ := index_mul_add_phase hT τ
  have hs := index_mul_add_phase hT s
  have hkl := periodIndex_mono hT hτs
  have hm' : (((periodIndex D.period s - periodIndex D.period τ).toNat : ℕ) : ℝ) =
      (periodIndex D.period s : ℝ) - periodIndex D.period τ := by
    have : (((periodIndex D.period s - periodIndex D.period τ).toNat : ℕ) : ℤ) =
        periodIndex D.period s - periodIndex D.period τ :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkl)
    exact_mod_cast this
  have hts : (((periodIndex D.period s - periodIndex D.period τ).toNat : ℕ) : ℝ) * D.period +
      2 * D.period = phaseOf D.period τ - phaseOf D.period s + 2 * D.period - (τ - s) := by
    linear_combination -hτ + hs + D.period * hm'
  have hx : |phaseOf D.period τ - phaseOf D.period s + 2 * D.period| ≤ 3 * D.period :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 : -(sp.βplus * (phaseOf D.period τ - phaseOf D.period s + 2 * D.period)) ≤
      |sp.βplus| * (3 * D.period) :=
    (neg_le_abs _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
  have hexp : -(sp.βplus *
      ((((periodIndex D.period s - periodIndex D.period τ).toNat + 1 + 1 : ℕ) : ℝ) * D.period)) ≤
      |sp.βplus| * (3 * D.period) + sp.βplus * (τ - s) := by
    push_cast
    have e : ((((periodIndex D.period s - periodIndex D.period τ).toNat : ℕ) : ℝ) + 1 + 1) *
        D.period = phaseOf D.period τ - phaseOf D.period s + 2 * D.period - (τ - s) := by
      linear_combination hts
    rw [e]
    linarith
  have hEZ' : ‖ev.EZ (phaseOf D.period τ + D.period) 0‖ ≤ C₀ / Real.sqrt D.period := by
    have := hEZ 0 (phaseOf D.period τ + D.period) (by linarith) (by linarith)
    rw [sub_zero] at this
    exact this.trans (div_le_div_of_nonneg_left hC₀nn (Real.sqrt_pos.mpr hT)
      (Real.sqrt_le_sqrt (by linarith)))
  have hEφ : ‖ev.E D.period (phaseOf D.period s)‖ ≤ C₀ := hE _ _ hφT.le (by linarith)
  have hN := hK₂ ((periodIndex D.period s - periodIndex D.period τ).toNat + 1 + 1)
  have hA : 0 ≤ C₀ / Real.sqrt D.period := div_nonneg hC₀nn (Real.sqrt_nonneg _)
  unfold exteriorLift
  calc _ ≤ ‖ev.EZ (phaseOf D.period τ + D.period) 0‖ *
        (‖sp.MplusInv ^ ((periodIndex D.period s - periodIndex D.period τ).toNat + 1 + 1)‖ *
          ‖ev.E D.period (phaseOf D.period s)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C₀ / Real.sqrt D.period * ((K₂ * Real.exp (-(sp.βplus *
          ((((periodIndex D.period s - periodIndex D.period τ).toNat + 1 + 1 : ℕ) : ℝ) *
            D.period)))) * C₀) :=
        mul_le_mul hEZ' (mul_le_mul hN hEφ (norm_nonneg _)
          (mul_nonneg hK₂nn (Real.exp_pos _).le))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hA
    _ ≤ C₀ / Real.sqrt D.period * ((K₂ * Real.exp (|sp.βplus| * (3 * D.period) +
          sp.βplus * (τ - s))) * C₀) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hK₂nn) hC₀nn) hA
    _ = C₀ / Real.sqrt D.period * K₂ * C₀ * Real.exp (|sp.βplus| * (3 * D.period)) *
          Real.exp (sp.βplus * (τ - s)) := by
        rw [Real.exp_add]; ring

/-! ## `loc:eq:past-bound` (lines 390–400) -/

/-- The `X → X` stable bound `‖E(t,s)(1 - Π₊(s))‖ ≤ K e^{β₋(t-s)}`, `s ≤ t`: factor `[s,t]`
into at most two phase strips and whole periods (lines 390–392). -/
theorem stable_bound_X (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s t, s ≤ t →
      ‖ev.E t s * (1 - exteriorProjection D.period ev sp.MplusInv s)‖ ≤
        K * Real.exp (sp.βminus * (t - s)) := by
  obtain ⟨C₀, hC₀nn, hE, -⟩ := strip hev hT
  obtain ⟨K₁, hK₁⟩ := hsp.stable_rate
  have hK₁nn : 0 ≤ K₁ := by
    have h := (norm_nonneg _).trans (hK₁ 0)
    simpa using h
  have hPi := proj_norm_le hT hC₀nn hE sp.MplusInv
  have hCPi : 0 ≤ C₀ * (‖sp.MplusInv‖ * C₀) :=
    mul_nonneg hC₀nn (mul_nonneg (norm_nonneg _) hC₀nn)
  have hA : 0 ≤ C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀)) * Real.exp (|sp.βminus| * D.period) :=
    mul_nonneg (mul_nonneg hC₀nn (by linarith)) (Real.exp_pos _).le
  have hB : 0 ≤ C₀ * K₁ * C₀ * Real.exp (|sp.βminus| * (2 * D.period)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₀nn hK₁nn) hC₀nn) (Real.exp_pos _).le
  refine ⟨C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀)) * Real.exp (|sp.βminus| * D.period) +
    C₀ * K₁ * C₀ * Real.exp (|sp.βminus| * (2 * D.period)), add_nonneg hA hB, ?_⟩
  intro s t hst
  have hθ0 := phaseOf_nonneg hT t
  have hθT := phaseOf_lt hT t
  have hφ0 := phaseOf_nonneg hT s
  have hφT := phaseOf_lt hT s
  have ht := index_mul_add_phase hT t
  have hs := index_mul_add_phase hT s
  have h1Pi : ‖(1 : X →L[ℝ] X) - exteriorProjection D.period ev sp.MplusInv s‖ ≤
      1 + C₀ * (‖sp.MplusInv‖ * C₀) :=
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (hPi s))
  rcases E_split hev hT hst with ⟨hidx, hle, hEq⟩ | ⟨n, hidx, hEq⟩
  · have hts : t - s = phaseOf D.period t - phaseOf D.period s := by
      rw [hidx] at ht
      linarith
    have hexp : 1 ≤ Real.exp (|sp.βminus| * D.period) * Real.exp (sp.βminus * (t - s)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [mul_nonneg (by linarith [neg_abs_le sp.βminus] : (0 : ℝ) ≤ sp.βminus + |sp.βminus|)
        (by linarith : (0 : ℝ) ≤ t - s),
        mul_nonneg (abs_nonneg sp.βminus) (by linarith : (0 : ℝ) ≤ D.period - (t - s))]
    calc ‖ev.E t s * (1 - exteriorProjection D.period ev sp.MplusInv s)‖
        ≤ ‖ev.E t s‖ * ‖1 - exteriorProjection D.period ev sp.MplusInv s‖ := norm_mul_le _ _
      _ ≤ C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀)) := by
        rw [hEq]
        exact mul_le_mul (hE _ _ hle (by linarith)) h1Pi (norm_nonneg _) hC₀nn
      _ ≤ C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀)) *
          (Real.exp (|sp.βminus| * D.period) * Real.exp (sp.βminus * (t - s))) :=
        le_mul_of_one_le_right (mul_nonneg hC₀nn (by linarith)) hexp
      _ = C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀)) * Real.exp (|sp.βminus| * D.period) *
          Real.exp (sp.βminus * (t - s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · have hk : (periodIndex D.period t : ℝ) = periodIndex D.period s + n + 1 := by
      exact_mod_cast hidx
    have hts : t - s = ((n : ℝ) + 1) * D.period + phaseOf D.period t - phaseOf D.period s := by
      linear_combination -ht + hs + D.period * hk
    have key : ev.E t s * (1 - exteriorProjection D.period ev sp.MplusInv s) =
        ev.E (phaseOf D.period t) 0 * (monodromy D ev ^ n * (1 - sp.Pplus)) *
          ev.E D.period (phaseOf D.period s) := by
      have h2 : ev.E (phaseOf D.period t) 0 * monodromy D ev ^ n *
          ev.E D.period (phaseOf D.period s) * exteriorProjection D.period ev sp.MplusInv s =
          ev.E (phaseOf D.period t) 0 * (monodromy D ev ^ n * sp.Pplus) *
            ev.E D.period (phaseOf D.period s) := by
        rw [exteriorProjection_eq]
        simp only [mul_assoc]
        rw [E_period_mul hev hφ0 hφT.le, MN_mul hsp]
      rw [hEq, mul_sub, mul_one, h2, mul_sub, mul_one, mul_sub, sub_mul]
    have hx : |phaseOf D.period s - phaseOf D.period t - D.period| ≤ 2 * D.period :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 : sp.βminus * (phaseOf D.period s - phaseOf D.period t - D.period) ≤
        |sp.βminus| * (2 * D.period) :=
      (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
    have hbx : sp.βminus * ((n : ℝ) * D.period) ≤
        |sp.βminus| * (2 * D.period) + sp.βminus * (t - s) := by
      rw [hts]
      nlinarith [h1]
    calc ‖ev.E t s * (1 - exteriorProjection D.period ev sp.MplusInv s)‖
        = ‖ev.E (phaseOf D.period t) 0 * (monodromy D ev ^ n * (1 - sp.Pplus)) *
          ev.E D.period (phaseOf D.period s)‖ := by rw [key]
      _ ≤ ‖ev.E (phaseOf D.period t) 0‖ * ‖monodromy D ev ^ n * (1 - sp.Pplus)‖ *
          ‖ev.E D.period (phaseOf D.period s)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ C₀ * (K₁ * Real.exp (sp.βminus * ((n : ℝ) * D.period))) * C₀ :=
        mul_le_mul (mul_le_mul (hE _ _ hθ0 (by linarith)) (hK₁ n) (norm_nonneg _) hC₀nn)
          (hE _ _ hφT.le (by linarith)) (norm_nonneg _)
          (mul_nonneg hC₀nn (mul_nonneg hK₁nn (Real.exp_pos _).le))
      _ ≤ C₀ * (K₁ * Real.exp (|sp.βminus| * (2 * D.period) + sp.βminus * (t - s))) * C₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbx) hK₁nn) hC₀nn) hC₀nn
      _ = C₀ * K₁ * C₀ * Real.exp (|sp.βminus| * (2 * D.period)) *
          Real.exp (sp.βminus * (t - s)) := by rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- `loc:eq:past-bound`: `‖E(τ,s)Π₋(s)‖_{X→Z} ≤ C(1 + (τ-s)^{-1/2}) e^{β₋(τ-s)}`, `τ > s`. -/
theorem past_bound (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp) (hT : 0 < D.period) :
    ∃ C : ℝ, ∀ s τ, s < τ →
      ‖(ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)‖ ≤
        C * (1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s)) := by
  obtain ⟨C₀, hC₀nn, hE, hEZ⟩ := strip hev hT
  obtain ⟨Kx, hKxnn, hKx⟩ := stable_bound_X hev hsp hT
  have hPi := proj_norm_le hT hC₀nn hE sp.MplusInv
  have hCPi : 0 ≤ C₀ * (‖sp.MplusInv‖ * C₀) :=
    mul_nonneg hC₀nn (mul_nonneg (norm_nonneg _) hC₀nn)
  refine ⟨Real.exp |sp.βminus| * C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀) + Kx), ?_⟩
  intro s τ hsτ
  have hu : 0 < τ - s := sub_pos.mpr hsτ
  have hinv : 0 ≤ 1 / Real.sqrt (τ - s) := by positivity
  have hone : 1 ≤ 1 + 1 / Real.sqrt (τ - s) := by linarith
  have hD1 : 0 ≤ Real.exp |sp.βminus| * C₀ := mul_nonneg (Real.exp_pos _).le hC₀nn
  have hD2 : 0 ≤ Real.exp |sp.βminus| * C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀) + Kx) :=
    mul_nonneg hD1 (by linarith)
  have h1Pi : ‖(1 : X →L[ℝ] X) - exteriorProjection D.period ev sp.MplusInv s‖ ≤
      1 + C₀ * (‖sp.MplusInv‖ * C₀) :=
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (hPi s))
  rcases le_or_gt (τ - s) 1 with hle | hgt
  · have hexp : 1 ≤ Real.exp |sp.βminus| * Real.exp (sp.βminus * (τ - s)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [mul_nonneg (by linarith [neg_abs_le sp.βminus] : (0 : ℝ) ≤ sp.βminus + |sp.βminus|)
        hu.le, mul_nonneg (abs_nonneg sp.βminus) (by linarith : (0 : ℝ) ≤ 1 - (τ - s))]
    calc ‖(ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)‖
        ≤ ‖ev.EZ τ s‖ * ‖1 - exteriorProjection D.period ev sp.MplusInv s‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C₀ / Real.sqrt (τ - s) * (1 + C₀ * (‖sp.MplusInv‖ * C₀)) :=
          mul_le_mul (hEZ s τ hsτ (by linarith)) h1Pi (norm_nonneg _)
            (div_nonneg hC₀nn (Real.sqrt_nonneg _))
      _ = C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀)) * (1 / Real.sqrt (τ - s)) := by ring
      _ ≤ C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀) + Kx) * (1 + 1 / Real.sqrt (τ - s)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₀nn) (by linarith) hinv
            (mul_nonneg hC₀nn (by linarith))
      _ ≤ C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀) + Kx) * (1 + 1 / Real.sqrt (τ - s)) *
          (Real.exp |sp.βminus| * Real.exp (sp.βminus * (τ - s))) :=
          le_mul_of_one_le_right (mul_nonneg (mul_nonneg hC₀nn (by linarith)) (by linarith)) hexp
      _ = Real.exp |sp.βminus| * C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀) + Kx) *
          (1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s)) := by ring
  · have hr : s ≤ τ - 1 := by linarith
    have hfac := EZ_factor hev hr (by linarith : τ - 1 < τ)
    have hEZ1 : ‖ev.EZ τ (τ - 1)‖ ≤ C₀ := by
      have := hEZ (τ - 1) τ (by linarith) (by linarith)
      rwa [sub_sub_cancel, Real.sqrt_one, div_one] at this
    have hX := hKx s (τ - 1) hr
    have hexp : Real.exp (sp.βminus * (τ - 1 - s)) ≤
        Real.exp |sp.βminus| * Real.exp (sp.βminus * (τ - s)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [neg_le_abs sp.βminus]
    calc ‖(ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)‖
        = ‖(ev.EZ τ (τ - 1)).comp
            (ev.E (τ - 1) s * (1 - exteriorProjection D.period ev sp.MplusInv s))‖ := by
          rw [hfac, ContinuousLinearMap.comp_assoc]; rfl
      _ ≤ ‖ev.EZ τ (τ - 1)‖ *
          ‖ev.E (τ - 1) s * (1 - exteriorProjection D.period ev sp.MplusInv s)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C₀ * (Kx * Real.exp (sp.βminus * (τ - 1 - s))) :=
          mul_le_mul hEZ1 hX (norm_nonneg _) hC₀nn
      _ ≤ C₀ * (Kx * (Real.exp |sp.βminus| * Real.exp (sp.βminus * (τ - s)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hKxnn) hC₀nn
      _ = Real.exp |sp.βminus| * C₀ * Kx * 1 * Real.exp (sp.βminus * (τ - s)) := by ring
      _ ≤ Real.exp |sp.βminus| * C₀ * (1 + C₀ * (‖sp.MplusInv‖ * C₀) + Kx) *
          (1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hD1)
            hone zero_le_one hD2) (Real.exp_pos _).le

end Projections

/-! ## Step L7 -/

/-- **Step L7** `ProjectionStep` (`paper/main.tex`, lines 371–404; blueprint units B1015, B1016,
B1017). For every unstable background, every evolution `E` with the properties of L3 and every
real spectral splitting of `𝓜 = E(𝒯,0)` with the properties of L6, the explicit phase
projections `Π₊(θ) = E(θ,0)𝓜₊⁻¹P₊E(𝒯,θ)` and the explicit backward exterior evolution
`E₊(τ,s)Π₊(s)` have all the properties of `IsPhaseProjections`, with the `Z`-valued lift
`exteriorLift` (`E_Z(θ+𝒯,0) N^{l-k+2} E(𝒯,φ)`). Only `0 < 𝒯` is used from the background, and
only the clauses of `IsEvolution` and `IsSpectralSplitting`; `IsCoefficients` and
`IsFreeEvolution` are not needed. -/
theorem projectionStep : ProjectionStep := by
  intro D hD c S ev sp _ _ hev hsp
  have hT : 0 < D.period := hD.1.period_pos
  exact ⟨exteriorLift D.period ev sp.MplusInv,
    { idempotent := proj_idempotent hev hsp hT
      strongly_continuous := proj_continuous hev hsp hT
      intertwine := fun s τ h => proj_intertwine hev hsp hT h
      backward_range := fun τ s _ => backward_range hev hsp hT τ s
      backward_inverse := fun τ s h => backward_inverse hev hsp hT h
      future_lift := fun τ s _ => exteriorLift_lift hev hsp hT τ s
      past_bound := past_bound hev hsp hT
      future_bound := future_bound hev hsp hT }⟩

end UnforcedLeray.Loc.L07
