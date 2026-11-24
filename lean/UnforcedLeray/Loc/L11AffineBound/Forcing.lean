import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Step L11, abstract part: the forcings and the correction maps on `(-∞, τ₀]`

`paper/main.tex` lines 493–514 (`loc:eq:local-fixed-point`, line 495; `loc:eq:affine-bound`,
line 511); blueprint units B1021 (the two direct correction maps) and B1023 (the affine,
linear and bilinear bounds in `𝒵_β`).

Everything here is stated for abstract real normed spaces `E` (standing for `Z = H²_div`) and
`F` (standing for `X = H¹_div`), a bounded bilinear map `N : E →L E →L F` (for `𝓝`), an operator
family `K : ℝ → (E →L F)` (for `𝓒(K_loc(τ), ·)`), a force `Gs : ℝ → F` (for `G_*`), a bounded
continuous mode `b : ℝ → E` (for `b̂`) and a bounded operator
`R : (Iic τ₀ →ᵇ F) →L (Iic τ₀ →ᵇ E)` (for `𝓡_β(τ₀)` in weighted coordinates). The weighted
spaces `𝒳_β(τ₀)`, `𝒵_β(τ₀)` of the interface layer are, by definition, `Iic τ₀ →ᵇ X` and
`Iic τ₀ →ᵇ Z`.

With `z = e^{βτ} w` (weighted coordinates), the right-hand side of `loc:eq:local-fixed-point`
is `w ↦ Bq w w + L_j w + G_j` with
* `Bq w₁ w₂ = 𝓡_β[τ ↦ e^{βτ} 𝓝(w₁(τ), w₂(τ))]` (`bilCorr`);
* `L_j w = 𝓡_β[τ ↦ -𝓒(K(τ), w(τ)) + j e^{στ}(𝓝(b(τ), w(τ)) + 𝓝(w(τ), b(τ)))]` (`linCorr`);
* `G_j = 𝓡_β[τ ↦ e^{-βτ}(G_*(τ) + j(e^{2στ}𝓝(b, b) - e^{στ}𝓒(K, b)))]` (`affForcing`).

The bounds (lines 504–514) are the exponential bookkeeping of B1023:
* bilinear: `e^{βτ}‖𝓝‖ ≤ e^{βτ₀}‖𝓝‖`;
* linear: `CK e^{τ/2} + 2e^{στ}‖𝓝‖Mb ≤ CK e^{τ₀/2} + 2e^{στ₀}‖𝓝‖Mb`;
* affine: `e^{-βτ}CG e^{τ/2} ≤ CG e^{(1/2-β)τ₀}` (`β < 1/2`), `e^{-βτ}e^{2στ}‖𝓝‖Mb² ≤
  ‖𝓝‖Mb²e^{(2σ-β)τ₀}` (`β < 2σ`), and the mixed term `e^{-βτ}e^{στ}CK e^{τ/2}Mb ≤
  CK Mb e^{(1/2-β)τ₀}`, absorbed in the first (line 513).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped BoundedContinuousFunction

namespace UnforcedLeray.Loc.L11

/-! ## Elementary facts -/

/-- Monotonicity of `τ ↦ e^{aτ}` for `a ≥ 0`. -/
theorem exp_mul_le_exp_mul {a τ τ₀ : ℝ} (ha : 0 ≤ a) (h : τ ≤ τ₀) :
    Real.exp (a * τ) ≤ Real.exp (a * τ₀) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h ha)

/-- A continuous periodic function with nonzero period is bounded (used for `b̂`, which is
continuous and `𝒯`-periodic by `loc:eq:mode-regularity`, B1011). -/
theorem exists_bound_of_periodic {E : Type} [NormedAddCommGroup E] {f : ℝ → E} {c : ℝ}
    (hp : Function.Periodic f c) (hc : c ≠ 0) (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, ‖f τ‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hp.isBounded_of_continuous hc hf)
  exact ⟨max M 0, le_max_right _ _, fun τ => (hM _ (mem_range_self τ)).trans (le_max_left _ _)⟩

/-- An existential bound `‖f τ‖ ≤ C e^{τ/2}` on `τ ≤ 0` (`loc:eq:force-bound`) holds with a
nonnegative constant. -/
theorem exists_nonneg_bound {E : Type} [NormedAddCommGroup E] {f : ℝ → E}
    (h : ∃ C : ℝ, ∀ τ : ℝ, τ ≤ 0 → ‖f τ‖ ≤ C * Real.exp ((1 / 2) * τ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, τ ≤ 0 → ‖f τ‖ ≤ C * Real.exp ((1 / 2) * τ) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun τ hτ =>
    (hC τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

/-- Restriction to `(-∞, τ₀]`, `τ₀ ≤ 0`, of a function continuous on `(-∞, 0]`. -/
theorem continuous_restrict_Iic {Y : Type} [TopologicalSpace Y] {f : ℝ → Y}
    (hf : ContinuousOn f (Iic 0)) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) :
    Continuous (fun τ : Iic τ₀ => f τ) :=
  hf.comp_continuous continuous_subtype_val (fun τ => mem_Iic.mpr ((mem_Iic.mp τ.2).trans hτ₀))

/-! ## Standing hypotheses -/

section Forcings

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The standing hypotheses of step L11 in abstract form, with constants `CK`, `CG`, `Mb`:
`0 < σ < 1/4` (`paper/main.tex` line 172) and `σ < β < 2σ` (`loc:eq:weight`, B1013);
continuity on `(-∞, 0]` of `K = 𝓒(K_loc(·), ·)` and `Gs = G_*` with
`‖K(τ)‖ ≤ CK e^{τ/2}` (line 506) and `‖Gs(τ)‖ ≤ CG e^{τ/2}` (`loc:eq:force-bound`, B0722)
for `τ ≤ 0`; continuity of `b = b̂` with `‖b(τ)‖ ≤ Mb` (`loc:eq:mode-regularity`, B1011). -/
structure Hyp (K : ℝ → (E →L[ℝ] F)) (Gs : ℝ → F) (b : ℝ → E) (σ β CK CG Mb : ℝ) : Prop where
  σ_pos : 0 < σ
  σ_lt : σ < 1 / 4
  β_gt : σ < β
  β_lt : β < 2 * σ
  K_cont : ContinuousOn K (Iic 0)
  G_cont : ContinuousOn Gs (Iic 0)
  b_cont : Continuous b
  CK_nonneg : 0 ≤ CK
  CG_nonneg : 0 ≤ CG
  Mb_nonneg : 0 ≤ Mb
  K_bound : ∀ τ : ℝ, τ ≤ 0 → ‖K τ‖ ≤ CK * Real.exp ((1 / 2) * τ)
  G_bound : ∀ τ : ℝ, τ ≤ 0 → ‖Gs τ‖ ≤ CG * Real.exp ((1 / 2) * τ)
  b_bound : ∀ τ : ℝ, ‖b τ‖ ≤ Mb

variable {K : ℝ → (E →L[ℝ] F)} {Gs : ℝ → F} {b : ℝ → E} {σ β CK CG Mb : ℝ}

theorem Hyp.β_pos (h : Hyp K Gs b σ β CK CG Mb) : 0 < β := h.σ_pos.trans h.β_gt

theorem Hyp.β_lt_half (h : Hyp K Gs b σ β CK CG Mb) : β < 1 / 2 := by
  have := h.β_lt; have := h.σ_lt; linarith

/-! ## The bilinear part `e^{βτ} 𝓝(w₁, w₂)` -/

theorem norm_bilPt_le (N : E →L[ℝ] E →L[ℝ] F) {β τ₀ : ℝ} (hβ : 0 ≤ β)
    (v w : Iic τ₀ →ᵇ E) (τ : Iic τ₀) :
    ‖Real.exp (β * (τ : ℝ)) • N (v τ) (w τ)‖ ≤ Real.exp (β * τ₀) * ‖N‖ * ‖v‖ * ‖w‖ := by
  have hN : 0 ≤ ‖N‖ := norm_nonneg N
  have h1 : Real.exp (β * (τ : ℝ)) ≤ Real.exp (β * τ₀) :=
    exp_mul_le_exp_mul hβ (mem_Iic.mp τ.2)
  have h2 : ‖N (v τ) (w τ)‖ ≤ ‖N‖ * ‖v‖ * ‖w‖ :=
    (N.le_opNorm₂ (v τ) (w τ)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (v.norm_coe_le_norm τ) hN) (w.norm_coe_le_norm τ)
        (norm_nonneg _) (mul_nonneg hN (norm_nonneg v)))
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (β * (τ : ℝ)) * ‖N (v τ) (w τ)‖
      ≤ Real.exp (β * τ₀) * (‖N‖ * ‖v‖ * ‖w‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (β * τ₀) * ‖N‖ * ‖v‖ * ‖w‖ := by ring

/-- The bilinear forcing `τ ↦ e^{βτ} 𝓝(v(τ), w(τ))` as a bounded continuous function on
`(-∞, τ₀]` (the weighted coordinate of `e^{-βτ}𝓝(z₁, z₂)`, `z_i = e^{βτ}v_i`). -/
def bilForcing (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (v w : Iic τ₀ →ᵇ E) : Iic τ₀ →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun τ => Real.exp (β * (τ : ℝ)) • N (v τ) (w τ))
    ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul
      ((N.continuous.comp v.continuous).clm_apply w.continuous))
    (Real.exp (β * τ₀) * ‖N‖ * ‖v‖ * ‖w‖) (norm_bilPt_le N hβ v w)

theorem bilForcing_apply (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (v w : Iic τ₀ →ᵇ E) (τ : Iic τ₀) :
    bilForcing N hβ v w τ = Real.exp (β * (τ : ℝ)) • N (v τ) (w τ) := rfl

theorem norm_bilForcing_le (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (v w : Iic τ₀ →ᵇ E) :
    ‖bilForcing N hβ v w‖ ≤ Real.exp (β * τ₀) * ‖N‖ * ‖v‖ * ‖w‖ := by
  have h0 : 0 ≤ Real.exp (β * τ₀) * ‖N‖ * ‖v‖ * ‖w‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg N)) (norm_nonneg v))
      (norm_nonneg w)
  refine (BoundedContinuousFunction.norm_le h0).2 (fun τ => ?_)
  rw [bilForcing_apply]
  exact norm_bilPt_le N hβ v w τ

theorem bilForcing_add_left (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (v₁ v₂ w : Iic τ₀ →ᵇ E) :
    bilForcing N hβ (v₁ + v₂) w = bilForcing N hβ v₁ w + bilForcing N hβ v₂ w := by
  ext τ
  simp only [bilForcing_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, map_add,
    _root_.add_apply, smul_add]

theorem bilForcing_add_right (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (v w₁ w₂ : Iic τ₀ →ᵇ E) :
    bilForcing N hβ v (w₁ + w₂) = bilForcing N hβ v w₁ + bilForcing N hβ v w₂ := by
  ext τ
  simp only [bilForcing_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, map_add,
    smul_add]

theorem bilForcing_smul_left (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (c : ℝ) (v w : Iic τ₀ →ᵇ E) :
    bilForcing N hβ (c • v) w = c • bilForcing N hβ v w := by
  ext τ
  simp only [bilForcing_apply, BoundedContinuousFunction.smul_apply, map_smul,
    _root_.smul_apply]
  exact smul_comm _ _ _

theorem bilForcing_smul_right (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (c : ℝ) (v w : Iic τ₀ →ᵇ E) :
    bilForcing N hβ v (c • w) = c • bilForcing N hβ v w := by
  ext τ
  simp only [bilForcing_apply, BoundedContinuousFunction.smul_apply, map_smul]
  exact smul_comm _ _ _

/-- The bilinear correction map `Bq(w₁, w₂) = 𝓡_β[e^{βτ}𝓝(w₁, w₂)]` (B1021). -/
def bilCorr (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (R : (Iic τ₀ →ᵇ F) →L[ℝ] (Iic τ₀ →ᵇ E)) :
    (Iic τ₀ →ᵇ E) →L[ℝ] (Iic τ₀ →ᵇ E) →L[ℝ] (Iic τ₀ →ᵇ E) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w => R (bilForcing N hβ v w))
      (fun v₁ v₂ w => by simp only [bilForcing_add_left, map_add])
      (fun c v w => by simp only [bilForcing_smul_left, map_smul])
      (fun v w₁ w₂ => by simp only [bilForcing_add_right, map_add])
      (fun c v w => by simp only [bilForcing_smul_right, map_smul]))
    (‖R‖ * (Real.exp (β * τ₀) * ‖N‖)) (fun v w => by
      show ‖R (bilForcing N hβ v w)‖ ≤ ‖R‖ * (Real.exp (β * τ₀) * ‖N‖) * ‖v‖ * ‖w‖
      calc ‖R (bilForcing N hβ v w)‖ ≤ ‖R‖ * ‖bilForcing N hβ v w‖ := R.le_opNorm _
        _ ≤ ‖R‖ * (Real.exp (β * τ₀) * ‖N‖ * ‖v‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left (norm_bilForcing_le N hβ v w) (norm_nonneg R)
        _ = ‖R‖ * (Real.exp (β * τ₀) * ‖N‖) * ‖v‖ * ‖w‖ := by ring)

theorem bilCorr_apply (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (R : (Iic τ₀ →ᵇ F) →L[ℝ] (Iic τ₀ →ᵇ E)) (v w : Iic τ₀ →ᵇ E) :
    bilCorr N hβ R v w = R (bilForcing N hβ v w) := rfl

theorem norm_bilCorr_apply_le (N : E →L[ℝ] E →L[ℝ] F) {β : ℝ} (hβ : 0 ≤ β) {τ₀ : ℝ}
    (R : (Iic τ₀ →ᵇ F) →L[ℝ] (Iic τ₀ →ᵇ E)) (v w : Iic τ₀ →ᵇ E) :
    ‖bilCorr N hβ R v w‖ ≤ ‖R‖ * (Real.exp (β * τ₀) * ‖N‖) * ‖v‖ * ‖w‖ := by
  rw [bilCorr_apply]
  calc ‖R (bilForcing N hβ v w)‖ ≤ ‖R‖ * ‖bilForcing N hβ v w‖ := R.le_opNorm _
    _ ≤ ‖R‖ * (Real.exp (β * τ₀) * ‖N‖ * ‖v‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_bilForcing_le N hβ v w) (norm_nonneg R)
    _ = ‖R‖ * (Real.exp (β * τ₀) * ‖N‖) * ‖v‖ * ‖w‖ := by ring

/-! ## The linear part `-𝓒(K, w) + j e^{στ}(𝓝(b̂, w) + 𝓝(w, b̂))` -/

/-- The linear forcing, pointwise: `-K(τ)w(τ) + c e^{στ}(𝓝(b(τ), w(τ)) + 𝓝(w(τ), b(τ)))`. -/
def linPt (N : E →L[ℝ] E →L[ℝ] F) (K : ℝ → (E →L[ℝ] F)) (b : ℝ → E) (σ c : ℝ) {τ₀ : ℝ}
    (w : Iic τ₀ →ᵇ E) (τ : Iic τ₀) : F :=
  -(K τ (w τ)) + (c * Real.exp (σ * (τ : ℝ))) • (N (b τ) (w τ) + N (w τ) (b τ))

/-- The bound of the linear forcing: `CK e^{τ₀/2} + 2 e^{στ₀} ‖𝓝‖ Mb`. -/
def linBound (N : E →L[ℝ] E →L[ℝ] F) (σ CK Mb τ₀ : ℝ) : ℝ :=
  CK * Real.exp ((1 / 2) * τ₀) + Real.exp (σ * τ₀) * (2 * ‖N‖ * Mb)

theorem linBound_nonneg (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) (τ₀ : ℝ) :
    0 ≤ linBound N σ CK Mb τ₀ :=
  add_nonneg (mul_nonneg h.CK_nonneg (Real.exp_pos _).le)
    (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg N)) h.Mb_nonneg))

theorem continuous_linPt (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) (c : ℝ)
    {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (w : Iic τ₀ →ᵇ E) : Continuous (linPt N K b σ c w) := by
  have hb : Continuous (fun τ : Iic τ₀ => b τ) := h.b_cont.comp continuous_subtype_val
  have hK : Continuous (fun τ : Iic τ₀ => K τ) := continuous_restrict_Iic h.K_cont hτ₀
  have he : Continuous (fun τ : Iic τ₀ => c * Real.exp (σ * (τ : ℝ))) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val))
  have h1 : Continuous (fun τ : Iic τ₀ => K τ (w τ)) := hK.clm_apply w.continuous
  have h2 : Continuous (fun τ : Iic τ₀ => N (b τ) (w τ)) :=
    (N.continuous.comp hb).clm_apply w.continuous
  have h3 : Continuous (fun τ : Iic τ₀ => N (w τ) (b τ)) :=
    (N.continuous.comp w.continuous).clm_apply hb
  exact h1.neg.add (he.smul (h2.add h3))

theorem norm_linPt_le (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (w : Iic τ₀ →ᵇ E) (τ : Iic τ₀) :
    ‖linPt N K b σ c w τ‖ ≤ linBound N σ CK Mb τ₀ * ‖w‖ := by
  have hτ : (τ : ℝ) ≤ τ₀ := mem_Iic.mp τ.2
  have hτ0 : (τ : ℝ) ≤ 0 := hτ.trans hτ₀
  have hw : ‖w τ‖ ≤ ‖w‖ := w.norm_coe_le_norm τ
  have hN : 0 ≤ ‖N‖ := norm_nonneg N
  have hb : ‖b τ‖ ≤ Mb := h.b_bound τ
  have hKτ : ‖K τ‖ ≤ CK * Real.exp ((1 / 2) * τ₀) :=
    (h.K_bound τ hτ0).trans
      (mul_le_mul_of_nonneg_left (exp_mul_le_exp_mul (by norm_num) hτ) h.CK_nonneg)
  have h1 : ‖K τ (w τ)‖ ≤ CK * Real.exp ((1 / 2) * τ₀) * ‖w‖ :=
    ((K τ).le_opNorm (w τ)).trans
      (mul_le_mul hKτ hw (norm_nonneg _) (mul_nonneg h.CK_nonneg (Real.exp_pos _).le))
  have h2 : ‖N (b τ) (w τ)‖ ≤ ‖N‖ * Mb * ‖w‖ :=
    (N.le_opNorm₂ (b τ) (w τ)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hb hN) hw (norm_nonneg _) (mul_nonneg hN h.Mb_nonneg))
  have h3b : ‖N‖ * ‖w τ‖ * ‖b τ‖ ≤ ‖N‖ * Mb * ‖w‖ :=
    calc ‖N‖ * ‖w τ‖ * ‖b τ‖ ≤ ‖N‖ * ‖w‖ * Mb :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hN) hb (norm_nonneg _)
            (mul_nonneg hN (norm_nonneg w))
      _ = ‖N‖ * Mb * ‖w‖ := by ring
  have h3 : ‖N (w τ) (b τ)‖ ≤ ‖N‖ * Mb * ‖w‖ := (N.le_opNorm₂ (w τ) (b τ)).trans h3b
  have hsum : ‖N (b τ) (w τ) + N (w τ) (b τ)‖ ≤ 2 * ‖N‖ * Mb * ‖w‖ := by
    have := norm_add_le (N (b τ) (w τ)) (N (w τ) (b τ))
    linarith
  have hce : ‖c * Real.exp (σ * (τ : ℝ))‖ ≤ Real.exp (σ * τ₀) := by
    rw [Real.norm_of_nonneg (mul_nonneg hc0 (Real.exp_pos _).le)]
    calc c * Real.exp (σ * (τ : ℝ)) ≤ 1 * Real.exp (σ * (τ : ℝ)) :=
          mul_le_mul_of_nonneg_right hc1 (Real.exp_pos _).le
      _ = Real.exp (σ * (τ : ℝ)) := one_mul _
      _ ≤ Real.exp (σ * τ₀) := exp_mul_le_exp_mul h.σ_pos.le hτ
  unfold linPt linBound
  calc ‖-(K τ (w τ)) + (c * Real.exp (σ * (τ : ℝ))) • (N (b τ) (w τ) + N (w τ) (b τ))‖
      ≤ ‖K τ (w τ)‖ + ‖c * Real.exp (σ * (τ : ℝ))‖ * ‖N (b τ) (w τ) + N (w τ) (b τ)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg, norm_smul]
    _ ≤ CK * Real.exp ((1 / 2) * τ₀) * ‖w‖ + Real.exp (σ * τ₀) * (2 * ‖N‖ * Mb * ‖w‖) :=
        add_le_add h1 (mul_le_mul hce hsum (norm_nonneg _) (Real.exp_pos _).le)
    _ = (CK * Real.exp ((1 / 2) * τ₀) + Real.exp (σ * τ₀) * (2 * ‖N‖ * Mb)) * ‖w‖ := by ring

/-- The linear forcing as a bounded continuous function on `(-∞, τ₀]`. -/
def linForcing (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (w : Iic τ₀ →ᵇ E) : Iic τ₀ →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (linPt N K b σ c w)
    (continuous_linPt N h c hτ₀ w) (linBound N σ CK Mb τ₀ * ‖w‖)
    (norm_linPt_le N h hc0 hc1 hτ₀ w)

theorem linForcing_apply (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (w : Iic τ₀ →ᵇ E) (τ : Iic τ₀) :
    linForcing N h hc0 hc1 hτ₀ w τ = -(K τ (w τ)) +
      (c * Real.exp (σ * (τ : ℝ))) • (N (b τ) (w τ) + N (w τ) (b τ)) := rfl

theorem norm_linForcing_le (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (w : Iic τ₀ →ᵇ E) :
    ‖linForcing N h hc0 hc1 hτ₀ w‖ ≤ linBound N σ CK Mb τ₀ * ‖w‖ :=
  (BoundedContinuousFunction.norm_le
    (mul_nonneg (linBound_nonneg N h τ₀) (norm_nonneg w))).2
    (fun τ => norm_linPt_le N h hc0 hc1 hτ₀ w τ)

theorem linForcing_add (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (v w : Iic τ₀ →ᵇ E) :
    linForcing N h hc0 hc1 hτ₀ (v + w) =
      linForcing N h hc0 hc1 hτ₀ v + linForcing N h hc0 hc1 hτ₀ w := by
  ext τ
  simp only [linForcing_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, map_add,
    _root_.add_apply]
  module

theorem linForcing_smul (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (r : ℝ) (w : Iic τ₀ →ᵇ E) :
    linForcing N h hc0 hc1 hτ₀ (r • w) = r • linForcing N h hc0 hc1 hτ₀ w := by
  ext τ
  simp only [linForcing_apply, BoundedContinuousFunction.smul_apply, map_smul,
    _root_.smul_apply]
  module

/-- The linear correction map `L_j w = 𝓡_β[-𝓒(K, w) + j e^{στ}(𝓝(b̂, w) + 𝓝(w, b̂))]` (B1021),
with `c = j`. -/
def linCorr (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (R : (Iic τ₀ →ᵇ F) →L[ℝ] (Iic τ₀ →ᵇ E)) :
    (Iic τ₀ →ᵇ E) →L[ℝ] (Iic τ₀ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun w => R (linForcing N h hc0 hc1 hτ₀ w)
      map_add' := fun v w => by simp only [linForcing_add, map_add]
      map_smul' := fun r w => by simp only [RingHom.id_apply, linForcing_smul, map_smul] }
    (‖R‖ * linBound N σ CK Mb τ₀) (fun w => by
      show ‖R (linForcing N h hc0 hc1 hτ₀ w)‖ ≤ ‖R‖ * linBound N σ CK Mb τ₀ * ‖w‖
      calc ‖R (linForcing N h hc0 hc1 hτ₀ w)‖ ≤ ‖R‖ * ‖linForcing N h hc0 hc1 hτ₀ w‖ :=
            R.le_opNorm _
        _ ≤ ‖R‖ * (linBound N σ CK Mb τ₀ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (norm_linForcing_le N h hc0 hc1 hτ₀ w) (norm_nonneg R)
        _ = ‖R‖ * linBound N σ CK Mb τ₀ * ‖w‖ := by ring)

theorem linCorr_apply (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0)
    (R : (Iic τ₀ →ᵇ F) →L[ℝ] (Iic τ₀ →ᵇ E)) (w : Iic τ₀ →ᵇ E) :
    linCorr N h hc0 hc1 hτ₀ R w = R (linForcing N h hc0 hc1 hτ₀ w) := rfl

theorem norm_linCorr_apply_le (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0)
    (R : (Iic τ₀ →ᵇ F) →L[ℝ] (Iic τ₀ →ᵇ E)) (w : Iic τ₀ →ᵇ E) :
    ‖linCorr N h hc0 hc1 hτ₀ R w‖ ≤ ‖R‖ * linBound N σ CK Mb τ₀ * ‖w‖ := by
  rw [linCorr_apply]
  calc ‖R (linForcing N h hc0 hc1 hτ₀ w)‖ ≤ ‖R‖ * ‖linForcing N h hc0 hc1 hτ₀ w‖ :=
        R.le_opNorm _
    _ ≤ ‖R‖ * (linBound N σ CK Mb τ₀ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (norm_linForcing_le N h hc0 hc1 hτ₀ w) (norm_nonneg R)
    _ = ‖R‖ * linBound N σ CK Mb τ₀ * ‖w‖ := by ring

/-! ## The affine part `e^{-βτ}(G_* + j(e^{2στ}𝓝(b̂, b̂) - e^{στ}𝓒(K, b̂)))` -/

/-- The affine forcing in weighted coordinates, pointwise. -/
def affPt (N : E →L[ℝ] E →L[ℝ] F) (K : ℝ → (E →L[ℝ] F)) (Gs : ℝ → F) (b : ℝ → E)
    (σ β c : ℝ) {τ₀ : ℝ} (τ : Iic τ₀) : F :=
  Real.exp (-(β * (τ : ℝ))) •
    (Gs τ + c • (Real.exp (2 * σ * (τ : ℝ)) • N (b τ) (b τ) -
      Real.exp (σ * (τ : ℝ)) • K τ (b τ)))

theorem continuous_affPt (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb)
    (c : ℝ) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) : Continuous (affPt N K Gs b σ β c (τ₀ := τ₀)) := by
  have hb : Continuous (fun τ : Iic τ₀ => b τ) := h.b_cont.comp continuous_subtype_val
  have hK : Continuous (fun τ : Iic τ₀ => K τ) := continuous_restrict_Iic h.K_cont hτ₀
  have hG : Continuous (fun τ : Iic τ₀ => Gs τ) := continuous_restrict_Iic h.G_cont hτ₀
  have he : ∀ a : ℝ, Continuous (fun τ : Iic τ₀ => Real.exp (a * (τ : ℝ))) := fun a =>
    Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)
  have hm : Continuous (fun τ : Iic τ₀ => Real.exp (-(β * (τ : ℝ)))) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val).neg
  have hNbb : Continuous (fun τ : Iic τ₀ => N (b τ) (b τ)) :=
    (N.continuous.comp hb).clm_apply hb
  have hKb : Continuous (fun τ : Iic τ₀ => K τ (b τ)) := hK.clm_apply hb
  exact hm.smul (hG.add (continuous_const.smul (((he (2 * σ)).smul hNbb).sub ((he σ).smul hKb))))

/-- The bound of the affine forcing:
`(CG + CK Mb) e^{(1/2-β)τ₀} + ‖𝓝‖ Mb² e^{(2σ-β)τ₀}`. -/
def affBound (N : E →L[ℝ] E →L[ℝ] F) (σ β CK CG Mb τ₀ : ℝ) : ℝ :=
  (CG + CK * Mb) * Real.exp ((1 / 2 - β) * τ₀) + ‖N‖ * Mb ^ 2 * Real.exp ((2 * σ - β) * τ₀)

theorem affBound_nonneg (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) (τ₀ : ℝ) :
    0 ≤ affBound N σ β CK CG Mb τ₀ :=
  add_nonneg
    (mul_nonneg (add_nonneg h.CG_nonneg (mul_nonneg h.CK_nonneg h.Mb_nonneg)) (Real.exp_pos _).le)
    (mul_nonneg (mul_nonneg (norm_nonneg N) (sq_nonneg Mb)) (Real.exp_pos _).le)

theorem norm_affPt_le (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (τ : Iic τ₀) :
    ‖affPt N K Gs b σ β c τ‖ ≤ affBound N σ β CK CG Mb τ₀ := by
  unfold affPt affBound
  set t : ℝ := (τ : ℝ) with ht
  have hτ : t ≤ τ₀ := mem_Iic.mp τ.2
  have ht0 : t ≤ 0 := hτ.trans hτ₀
  have hN : 0 ≤ ‖N‖ := norm_nonneg N
  have hx : 0 < Real.exp (-(β * t)) := Real.exp_pos _
  have hG : ‖Gs t‖ ≤ CG * Real.exp ((1 / 2) * t) := h.G_bound t ht0
  have hb : ‖b t‖ ≤ Mb := h.b_bound t
  have hA : ‖Real.exp (2 * σ * t) • N (b t) (b t)‖ ≤
      Real.exp (2 * σ * t) * (‖N‖ * Mb * Mb) := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine (N.le_opNorm₂ (b t) (b t)).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hb hN) hb (norm_nonneg _)
      (mul_nonneg hN h.Mb_nonneg)
  have hB : ‖Real.exp (σ * t) • K t (b t)‖ ≤
      Real.exp (σ * t) * (CK * Real.exp ((1 / 2) * t) * Mb) := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact ((K t).le_opNorm (b t)).trans (mul_le_mul (h.K_bound t ht0) hb (norm_nonneg _)
      (mul_nonneg h.CK_nonneg (Real.exp_pos _).le))
  have hin : ‖Gs t + c • (Real.exp (2 * σ * t) • N (b t) (b t) -
      Real.exp (σ * t) • K t (b t))‖ ≤
      CG * Real.exp ((1 / 2) * t) + (Real.exp (2 * σ * t) * (‖N‖ * Mb * Mb) +
        Real.exp (σ * t) * (CK * Real.exp ((1 / 2) * t) * Mb)) := by
    refine (norm_add_le _ _).trans (add_le_add hG ?_)
    rw [norm_smul, Real.norm_of_nonneg hc0]
    have hs := norm_sub_le (Real.exp (2 * σ * t) • N (b t) (b t))
      (Real.exp (σ * t) • K t (b t))
    have hnn : 0 ≤ ‖Real.exp (2 * σ * t) • N (b t) (b t) - Real.exp (σ * t) • K t (b t)‖ :=
      norm_nonneg _
    calc c * ‖Real.exp (2 * σ * t) • N (b t) (b t) - Real.exp (σ * t) • K t (b t)‖
        ≤ 1 * ‖Real.exp (2 * σ * t) • N (b t) (b t) - Real.exp (σ * t) • K t (b t)‖ :=
          mul_le_mul_of_nonneg_right hc1 hnn
      _ ≤ _ := by linarith
  have e1 : Real.exp (-(β * t)) * Real.exp ((1 / 2) * t) = Real.exp ((1 / 2 - β) * t) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(β * t)) * Real.exp (2 * σ * t) = Real.exp ((2 * σ - β) * t) := by
    rw [← Real.exp_add]; ring_nf
  have e3 : Real.exp (-(β * t)) * (Real.exp (σ * t) * Real.exp ((1 / 2) * t)) =
      Real.exp ((1 / 2 + σ - β) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hβh := h.β_lt_half
  have f1 : Real.exp ((1 / 2 - β) * t) ≤ Real.exp ((1 / 2 - β) * τ₀) :=
    exp_mul_le_exp_mul (by linarith) hτ
  have f2 : Real.exp ((2 * σ - β) * t) ≤ Real.exp ((2 * σ - β) * τ₀) :=
    exp_mul_le_exp_mul (by linarith [h.β_lt]) hτ
  have f3 : Real.exp ((1 / 2 + σ - β) * t) ≤ Real.exp ((1 / 2 - β) * τ₀) := by
    refine (exp_mul_le_exp_mul (by linarith [h.σ_pos]) hτ).trans (Real.exp_le_exp.mpr ?_)
    nlinarith [h.σ_pos]
  have hCKMb : 0 ≤ CK * Mb := mul_nonneg h.CK_nonneg h.Mb_nonneg
  have hNMb : 0 ≤ ‖N‖ * Mb ^ 2 := mul_nonneg hN (sq_nonneg _)
  rw [norm_smul, Real.norm_of_nonneg hx.le]
  calc Real.exp (-(β * t)) * ‖Gs t + c • (Real.exp (2 * σ * t) • N (b t) (b t) -
        Real.exp (σ * t) • K t (b t))‖
      ≤ Real.exp (-(β * t)) * (CG * Real.exp ((1 / 2) * t) +
          (Real.exp (2 * σ * t) * (‖N‖ * Mb * Mb) +
            Real.exp (σ * t) * (CK * Real.exp ((1 / 2) * t) * Mb))) :=
        mul_le_mul_of_nonneg_left hin hx.le
    _ = CG * (Real.exp (-(β * t)) * Real.exp ((1 / 2) * t)) +
          ‖N‖ * Mb ^ 2 * (Real.exp (-(β * t)) * Real.exp (2 * σ * t)) +
          CK * Mb * (Real.exp (-(β * t)) * (Real.exp (σ * t) * Real.exp ((1 / 2) * t))) := by
        ring
    _ = CG * Real.exp ((1 / 2 - β) * t) + ‖N‖ * Mb ^ 2 * Real.exp ((2 * σ - β) * t) +
          CK * Mb * Real.exp ((1 / 2 + σ - β) * t) := by
        rw [e1, e2, e3]
    _ ≤ CG * Real.exp ((1 / 2 - β) * τ₀) + ‖N‖ * Mb ^ 2 * Real.exp ((2 * σ - β) * τ₀) +
          CK * Mb * Real.exp ((1 / 2 - β) * τ₀) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left f1 h.CG_nonneg)
          (mul_le_mul_of_nonneg_left f2 hNMb)) (mul_le_mul_of_nonneg_left f3 hCKMb)
    _ = (CG + CK * Mb) * Real.exp ((1 / 2 - β) * τ₀) +
          ‖N‖ * Mb ^ 2 * Real.exp ((2 * σ - β) * τ₀) := by
        ring

/-- The affine forcing `e^{-βτ}(G_* + j(e^{2στ}𝓝(b̂, b̂) - e^{στ}𝓒(K, b̂)))` as an element of
`Iic τ₀ →ᵇ F` (the weighted coordinate in `𝒳_β(τ₀)`), with `c = j`. -/
def affForcing (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) : Iic τ₀ →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (affPt N K Gs b σ β c (τ₀ := τ₀))
    (continuous_affPt N h c hτ₀) (affBound N σ β CK CG Mb τ₀) (norm_affPt_le N h hc0 hc1 hτ₀)

theorem affForcing_apply (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (τ : Iic τ₀) :
    affForcing N h hc0 hc1 hτ₀ τ = Real.exp (-(β * (τ : ℝ))) •
      (Gs τ + c • (Real.exp (2 * σ * (τ : ℝ)) • N (b τ) (b τ) -
        Real.exp (σ * (τ : ℝ)) • K τ (b τ))) := rfl

theorem norm_affForcing_le (N : E →L[ℝ] E →L[ℝ] F) (h : Hyp K Gs b σ β CK CG Mb) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) :
    ‖affForcing N h hc0 hc1 hτ₀‖ ≤ affBound N σ β CK CG Mb τ₀ :=
  (BoundedContinuousFunction.norm_le (affBound_nonneg N h τ₀)).2
    (fun τ => norm_affPt_le N h hc0 hc1 hτ₀ τ)

end Forcings

end UnforcedLeray.Loc.L11
