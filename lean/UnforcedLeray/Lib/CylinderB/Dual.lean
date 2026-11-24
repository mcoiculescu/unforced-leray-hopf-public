import UnforcedLeray.Lib.CylinderB.Space

/-!
# CY07: negative spaces, the pairings `X_m → H^{-k}_m`, and the weak curl


(§5 Layer 1). `Hneg c m k = (H^k_{-m})^*` is defined in `CylinderB/Space` (generic
`Sob.Hneg` of `Lib/SobolevC`, unweighted pairing).

Manuscript: `paper/main.tex` lines 9370–9387 (B0579: `X_m = L²(⟨x⟩^{2m})`,
`H^{-1}_m := (H¹_{-m})^*` under `∫ f φ`), 9389–9405 (B0580:
`|⟨f, φ⟩| ≤ ‖⟨x⟩^m (v·∇b + b·∇v)‖₂ ‖⟨x⟩^{-m} ∇φ‖₂` for `f = −curl(·)`), 9871–9888 (B0749: the
same multiplier bound, weights only on `v₀, ∇v₀`), 13869–13890 (B0656: unweighted pairing).

## Main declarations
* `XR c m`: the real space `X_m = L²(cell, ρw^m)`;
* `pairDer α f`: `φ ↦ ∫ f · ∂^α φ` as an element of `H^{-k}_m`, `‖pairDer α f‖ ≤ ‖f‖`;
  `pairDerL α : X_m →L[ℝ] H^{-k}_m` (bounded with constant `1`), `ofX = pairDerL 0`;
* `curlNeg : X_m × X_m →L[ℝ] H^{-1}_m`, `curlNeg b (φ) = ∫ b₁ ∂_η φ − ∫ b₂ ∂_q φ` (the weak
  curl `∂_q b₂ − ∂_η b₁`), `norm_curlNeg_le : ‖curlNeg b‖ ≤ ‖b₁‖ + ‖b₂‖`;
  `divNeg` likewise;
* `eLpNorm_mul_le_of_weight_bound`: `‖a b‖_{X_m} ≤ A ‖b‖_{L²(cell)}` when `|a| ρw^{m/2} ≤ A`;
  `norm_curlNeg_mul_le` (B0580, B0749): `‖curl(a b)‖_{H^{-1}_m} ≤ A (‖b₁‖₂ + ‖b₂‖₂)`.

Not built: `dual_X_eq` (`X_m ≃ (X_{-m})^*`, B0897).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Cyl

variable {c m : ℝ}

/-- The real space `X_m = L²(cell, ρw^m dq dη)` (B0579, B0656). -/
abbrev XR (c m : ℝ) := Lp ℝ 2 (Sob.wμ (Sob.cylinder c).μ (ρwW c ^ m))

/-- The dual space of `Hneg c m k`. -/
abbrev Hdual (c m : ℝ) (k : ℕ) := Sob.W (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2

theorem norm_deriv_le {k : ℕ} (α : Sob.Idx 2 k) (φ : Hdual c m k) :
    ‖Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2 α φ‖ ≤ ‖φ‖ := by
  rw [Sob.W.deriv_apply]
  exact PiLp.norm_apply_le (φ : Sob.SobTuple (Sob.cylinder c) (ρwW c ^ m).inv ℝ k 2) α

/-- `φ ↦ ∫ f · ∂^α φ` (the unweighted pairing of `f ∈ X_m` with a derivative of `φ ∈ H^k_{-m}`). -/
def pairDer {k : ℕ} (α : Sob.Idx 2 k) (f : XR c m) : Hneg c m k :=
  LinearMap.mkContinuous
    { toFun := fun φ => ∫ x, inner ℝ (f x)
        ((Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2 α φ) x) ∂(Sob.cylinder c).μ
      map_add' := fun φ ψ => by
        simp only [map_add]
        rw [← integral_add (Sob.integrable_inner_wμ (Lp.memLp f) (Lp.memLp _))
          (Sob.integrable_inner_wμ (Lp.memLp f) (Lp.memLp _))]
        refine integral_congr_ae ?_
        filter_upwards [(Sob.ae_eq_wμ_iff _ (ρwW c ^ m).inv).mp (Lp.coeFn_add
          (Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2 α φ)
          (Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2 α ψ))] with x hx
        rw [hx, Pi.add_apply, inner_add_right]
      map_smul' := fun a φ => by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [(Sob.ae_eq_wμ_iff _ (ρwW c ^ m).inv).mp (Lp.coeFn_smul a
          (Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2 α φ))] with x hx
        rw [hx, Pi.smul_apply, inner_smul_right] }
    ‖f‖ fun φ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine (Sob.norm_integral_inner_le (Lp.memLp f) (Lp.memLp _)).trans ?_
      rw [← Lp.norm_def, ← Lp.norm_def]
      exact mul_le_mul_of_nonneg_left (norm_deriv_le α φ) (norm_nonneg _)

theorem pairDer_apply' {k : ℕ} (α : Sob.Idx 2 k) (f : XR c m) (φ : Hdual c m k) :
    pairDer α f φ = ∫ x, inner ℝ (f x)
      ((Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2 α φ) x) ∂(Sob.cylinder c).μ := rfl

theorem pairDer_apply {k : ℕ} (α : Sob.Idx 2 k) (f : XR c m) (φ : Hdual c m k) :
    pairDer α f φ = ∫ x, (Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2 α φ) x * f x
      ∂(Sob.cylinder c).μ := by
  rw [pairDer_apply']
  simp

theorem norm_pairDer_le {k : ℕ} (α : Sob.Idx 2 k) (f : XR c m) :
    ‖(pairDer α f : Hneg c m k)‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- `pairDer α` as a bounded linear map `X_m → H^{-k}_m` of norm `≤ 1`. -/
def pairDerL {k : ℕ} (α : Sob.Idx 2 k) : XR c m →L[ℝ] Hneg c m k :=
  LinearMap.mkContinuous
    { toFun := pairDer α
      map_add' := fun f g => by
        refine ContinuousLinearMap.ext fun φ => ?_
        rw [ContinuousLinearMap.add_apply, pairDer_apply', pairDer_apply', pairDer_apply',
          ← integral_add (Sob.integrable_inner_wμ (Lp.memLp f) (Lp.memLp _))
          (Sob.integrable_inner_wμ (Lp.memLp g) (Lp.memLp _))]
        refine integral_congr_ae ?_
        filter_upwards [(Sob.ae_eq_wμ_iff _ (ρwW c ^ m)).mp (Lp.coeFn_add f g)] with x hx
        rw [hx, Pi.add_apply, inner_add_left]
      map_smul' := fun a f => by
        refine ContinuousLinearMap.ext fun φ => ?_
        rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, pairDer_apply', pairDer_apply',
          smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [(Sob.ae_eq_wμ_iff _ (ρwW c ^ m)).mp (Lp.coeFn_smul a f)] with x hx
        rw [hx, Pi.smul_apply, real_inner_smul_left] }
    1 fun f => by rw [one_mul]; exact norm_pairDer_le α f

theorem pairDerL_apply {k : ℕ} (α : Sob.Idx 2 k) (f : XR c m) :
    pairDerL (c := c) (m := m) α f = pairDer α f := rfl

/-- **`X_m ↪ H^{-k}_m`** (B0579): `f ↦ (φ ↦ ∫ f φ)`, of norm `≤ 1`. -/
def ofX (c m : ℝ) (k : ℕ) : XR c m →L[ℝ] Hneg c m k := pairDerL Sob.Idx.zero

theorem ofX_apply {k : ℕ} (f : XR c m) (φ : Hdual c m k) :
    ofX c m k f φ = ∫ x, (Sob.W.value (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ k 2 φ) x * f x
      ∂(Sob.cylinder c).μ :=
  pairDer_apply _ f φ

/-- **The weak curl** `curl b = ∂_q b₂ − ∂_η b₁` of `b ∈ X_m²` as an element of `H^{-1}_m`:
`⟨curl b, φ⟩ = ∫ b₁ ∂_η φ − ∫ b₂ ∂_q φ` (B0580, B0749). -/
def curlNeg (c m : ℝ) : XR c m × XR c m →L[ℝ] Hneg c m 1 :=
  (pairDerL iEta).comp (ContinuousLinearMap.fst ℝ _ _) -
    (pairDerL iQ).comp (ContinuousLinearMap.snd ℝ _ _)

/-- **The weak divergence** `div b = ∂_q b₁ + ∂_η b₂`: `⟨div b, φ⟩ = −∫ b₁ ∂_q φ − ∫ b₂ ∂_η φ`. -/
def divNeg (c m : ℝ) : XR c m × XR c m →L[ℝ] Hneg c m 1 :=
  -((pairDerL iQ).comp (ContinuousLinearMap.fst ℝ _ _) +
    (pairDerL iEta).comp (ContinuousLinearMap.snd ℝ _ _))

theorem curlNeg_apply (b : XR c m × XR c m) (φ : Hdual c m 1) :
    curlNeg c m b φ =
      (∫ x, (Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ 1 2 iEta φ) x * b.1 x
        ∂(Sob.cylinder c).μ) -
      ∫ x, (Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m).inv ℝ ℝ 1 2 iQ φ) x * b.2 x
        ∂(Sob.cylinder c).μ := by
  simp only [curlNeg, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', pairDerL_apply, pairDer_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem norm_curlNeg_le (b : XR c m × XR c m) : ‖curlNeg c m b‖ ≤ ‖b.1‖ + ‖b.2‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
  have e : curlNeg c m b φ = pairDer (k := 1) iEta b.1 φ - pairDer (k := 1) iQ b.2 φ := rfl
  rw [e]
  have h1 := ((pairDer (k := 1) iEta b.1 : Hneg c m 1)).le_opNorm φ
  have h2 := ((pairDer (k := 1) iQ b.2 : Hneg c m 1)).le_opNorm φ
  have h3 := norm_pairDer_le (c := c) (m := m) (k := 1) iEta b.1
  have h4 := norm_pairDer_le (c := c) (m := m) (k := 1) iQ b.2
  have hφ := norm_nonneg φ
  calc ‖pairDer (k := 1) iEta b.1 φ - pairDer (k := 1) iQ b.2 φ‖
      ≤ ‖pairDer (k := 1) iEta b.1 φ‖ + ‖pairDer (k := 1) iQ b.2 φ‖ := norm_sub_le _ _
    _ ≤ ‖b.1‖ * ‖φ‖ + ‖b.2‖ * ‖φ‖ := by nlinarith
    _ = (‖b.1‖ + ‖b.2‖) * ‖φ‖ := by ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem norm_divNeg_le (b : XR c m × XR c m) : ‖divNeg c m b‖ ≤ ‖b.1‖ + ‖b.2‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
  have e : divNeg c m b φ = -(pairDer (k := 1) iQ b.1 φ + pairDer (k := 1) iEta b.2 φ) := rfl
  rw [e, norm_neg]
  have h1 := ((pairDer (k := 1) iQ b.1 : Hneg c m 1)).le_opNorm φ
  have h2 := ((pairDer (k := 1) iEta b.2 : Hneg c m 1)).le_opNorm φ
  have h3 := norm_pairDer_le (c := c) (m := m) (k := 1) iQ b.1
  have h4 := norm_pairDer_le (c := c) (m := m) (k := 1) iEta b.2
  have hφ := norm_nonneg φ
  calc ‖pairDer (k := 1) iQ b.1 φ + pairDer (k := 1) iEta b.2 φ‖
      ≤ ‖pairDer (k := 1) iQ b.1 φ‖ + ‖pairDer (k := 1) iEta b.2 φ‖ := norm_add_le _ _
    _ ≤ ‖b.1‖ * ‖φ‖ + ‖b.2‖ * ‖φ‖ := by nlinarith
    _ = (‖b.1‖ + ‖b.2‖) * ‖φ‖ := by ring

/-! ### The multiplier bound (B0580, B0749) -/

/-- `‖a b‖_{X_m} ≤ A ‖b‖_{L²(cell)}` when `|a| ρw^{m/2} ≤ A` (weights only on the multiplier). -/
theorem eLpNorm_mul_le_of_weight_bound {a b : Plane → ℝ} {A : ℝ}
    (hA : ∀ z, |a z| * ρw c z ^ (m / 2) ≤ A) :
    eLpNorm (fun z => a z * b z) 2 (wμ c m) ≤ ENNReal.ofReal A * eLpNorm b 2 (cellμ c) := by
  have e1 : eLpNorm (fun z => a z * b z) 2 (wμ c m) =
      eLpNorm (fun z => ((a z * b z : ℝ) : ℂ)) 2 (wμ c m) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun z => by simp)
  rw [e1, eLpNorm_wμ_eq]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => ?_) 2
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (ρw_pos c z).le _), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith [hA z]) (abs_nonneg _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The multiplier bound for the weak curl** (B0580 tex 9389–9405, B0749 tex 9871–9888):
for `a` with `|a| ρw^{m/2} ≤ A` and `b₁, b₂ ∈ L²(cell)`,
`‖curl(a b)‖_{H^{-1}_m} ≤ A (‖b₁‖_{L²(cell)} + ‖b₂‖_{L²(cell)})`. -/
theorem norm_curlNeg_mul_le {a b₁ b₂ : Plane → ℝ} {A : ℝ} (hA : ∀ z, |a z| * ρw c z ^ (m / 2) ≤ A)
    (h₁ : MemLp (fun z => a z * b₁ z) 2 (Sob.wμ (Sob.cylinder c).μ (ρwW c ^ m)))
    (h₂ : MemLp (fun z => a z * b₂ z) 2 (Sob.wμ (Sob.cylinder c).μ (ρwW c ^ m)))
    (hb₁ : MemLp b₁ 2 (cellμ c)) (hb₂ : MemLp b₂ 2 (cellμ c)) :
    ‖curlNeg c m (h₁.toLp _, h₂.toLp _)‖ ≤
      A * ((eLpNorm b₁ 2 (cellμ c)).toReal + (eLpNorm b₂ 2 (cellμ c)).toReal) := by
  have hA0 : 0 ≤ A := (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (ρw_pos c 0).le _)).trans (hA 0)
  have key : ∀ (b : Plane → ℝ) (h : MemLp (fun z => a z * b z) 2
      (Sob.wμ (Sob.cylinder c).μ (ρwW c ^ m))), MemLp b 2 (cellμ c) →
      ‖h.toLp _‖ ≤ A * (eLpNorm b 2 (cellμ c)).toReal := by
    intro b h hb
    rw [Lp.norm_toLp, wμ_ρwW]
    have := eLpNorm_mul_le_of_weight_bound (b := b) hA
    calc (eLpNorm (fun z => a z * b z) 2 (wμ c m)).toReal
        ≤ (ENNReal.ofReal A * eLpNorm b 2 (cellμ c)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb.2.ne) this
      _ = A * (eLpNorm b 2 (cellμ c)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0]
  refine (norm_curlNeg_le _).trans ?_
  rw [mul_add]
  exact add_le_add (key b₁ h₁ hb₁) (key b₂ h₂ hb₂)

end UnforcedLeray.Cyl
