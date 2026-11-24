import UnforcedLeray.Short.PartI.StatementsCanonical
import UnforcedLeray.Units.B0122
import UnforcedLeray.Units.B0123

/-!
# `PartI:C10`: the derivative budget `‖e^{λθ}θ^κ V_can(θ)‖_{X_{G,j}} ≤ C_j (1+θ)^{j/2}`

Source of record: `the November 2 reference manuscript`,
lines 1126-1146.  With `W(θ) = e^{λθ}θ^κ V(θ)`, the Duhamel identity of `V` on `[θ, θ+1]`
(`Spine.CanonicalMild.canonical_duhamel`) becomes the identity `WDuh` below, in which the scalar
`cfac` is bounded for `θ ≥ 1`, `θ ≤ v ≤ θ+1`.  The free term gains one derivative at cost
`a^{-1/2} ≤ (1+θ)^{1/2}` (`a = log(1+1/θ) ≥ 1/(1+θ)`, source line 1143-1145), and the integral term
gains one derivative with an integrable kernel `(v-θ)^{-1/2}`.  Induction on `j` (`WGraphBound`)
needs the interval `[θ, θ+1]` only once per derivative, so no subdivision into `j` pieces is needed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0123

/-- The scalar `e^{λθ}θ^κ (e^{λv}v^κ)⁻¹` turning the Duhamel identity of `V` into one for `W`. -/
def cfac (lam κ : ℂ) (θ v : ℝ) : ℂ :=
  Complex.exp (lam * θ) * (θ : ℂ) ^ κ * (Complex.exp (lam * v) * (v : ℂ) ^ κ)⁻¹

/-- The Duhamel identity (in the variable `log θ`, free part `e^{(log θ' - log θ)D}`) for
`W = e^{λθ}θ^κ V` (source lines 1094-1125 with the rescaling of line 1136). -/
def WDuh (lam κ : ℂ) (W : ℝ → B0010.XG) : Prop :=
  ∀ θ θ' : ℝ, 0 < θ → θ ≤ θ' →
    W θ = cfac lam κ θ θ' • expD (Real.log θ' - Real.log θ) (W θ') +
      ∫ v in θ..θ', cfac lam κ θ v • expD (Real.log v - Real.log θ) (B0012.L0 (W v))

/-- The `X_{G,j}` graph bound with the budget `(1+θ)^{j/2}` for large `θ` (source line 1131). -/
def WGraphBound (W : ℝ → B0010.XG) (j : ℕ) : Prop :=
  ∃ C b : ℝ, 0 < b ∧ ∀ θ : ℝ, b ≤ θ → ∃ hj : W θ ∈ (B0121.fracPow j).domain,
    B0121.graphNormSq j ⟨W θ, hj⟩ ≤ (C * (1 + θ) ^ ((j : ℝ) / 2)) ^ 2

/-- **Free term gain** (source 1139-1145): `x ↦ cfac·e^{aD}x`, `a = log(θ+1) - log θ ∈ (0,1]`,
maps `X_{G,j}` to `X_{G,j+1}` with squared graph norms bounded by `C²(1+θ)` times those at level `j`
(`PlanarSpectral.norm_Dsemigroup_smoothing`, `a^{-1/2} ≤ (1+θ)^{1/2}`, `cfac` bounded). -/
def FreeTermGain (lam κ : ℂ) (j : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 1 ≤ θ → ∀ x : (B0121.fracPow j).domain,
    ∃ h : cfac lam κ θ (θ + 1) • expD (Real.log (θ + 1) - Real.log θ) (x : B0010.XG) ∈
        (B0121.fracPow (j + 1)).domain,
      B0121.graphNormSq (j + 1) ⟨_, h⟩ ≤
        (C * (1 + θ) ^ (1 / 2 : ℝ)) ^ 2 * B0121.graphNormSq j x

/-- **Integral term gain** (source 1139-1146): if `W` is continuous on `(0,∞)` with squared
`X_{G,j}` graph norm `≤ M²` on `[θ, θ+1]` then the Duhamel integral lies in `X_{G,j+1}` with graph
norm `≤ C (1+θ)^{1/2} M`: pointwise `‖e^{aD}L₀W(v)‖_{j+1} ≤ C a^{-1/2} ‖L₀W(v)‖_j`,
`a = log v - log θ ≥ (v-θ)/(1+θ)`, `L₀` bounded on `X_{G,j}`
(`PartI.greenEllipticRegularity`, `B0122.L0_mem_XGj_norm`), and `∫_θ^{θ+1}(v-θ)^{-1/2}dv = 2`. -/
def IntegralTermGain (lam κ : ℂ) (j : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 1 ≤ θ → ∀ W : ℝ → B0010.XG, ContinuousOn W (Ioi 0) →
    ∀ M : ℝ, 0 ≤ M →
    (∀ v ∈ Icc θ (θ + 1), ∃ h : W v ∈ (B0121.fracPow j).domain,
        B0121.graphNormSq j ⟨W v, h⟩ ≤ M ^ 2) →
    ∃ h : (∫ v in θ..θ + 1, cfac lam κ θ v •
          expD (Real.log v - Real.log θ) (B0012.L0 (W v))) ∈ (B0121.fracPow (j + 1)).domain,
      B0121.graphNormSq (j + 1) ⟨_, h⟩ ≤ (C * (1 + θ) ^ (1 / 2 : ℝ) * M) ^ 2

/-- **Minkowski inequality in the graph norm of `X_{G,j}`** (used for the Duhamel integral): if
`F` is interval integrable in `X_G` and `‖F v‖_{X_{G,j}} ≤ g v` for a.e. `v` with `g` interval
integrable, then `∫F ∈ X_{G,j}` and `‖∫F‖_{X_{G,j}} ≤ ∫g`.  Proof idea: apply the finite-dimensional
weighted truncation `P_N f = (w_n ⟨e_n,f⟩)_{n<N}` (a continuous linear map, so `‖∫P_N F‖ ≤ ∫‖P_N F‖`)
and let `N → ∞` (`graphNormSq`, `B0121.inner_fracPow`, `B0121.mem_XGj_iff`). -/
def GraphIntegralBound (j : ℕ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∀ (F : ℝ → B0010.XG) (g : ℝ → ℝ),
    IntervalIntegrable F volume a b → IntervalIntegrable g volume a b →
    (∀ v ∈ Ioc a b, 0 ≤ g v ∧ ∃ h : F v ∈ (B0121.fracPow j).domain,
        B0121.graphNormSq j ⟨F v, h⟩ ≤ (g v) ^ 2) →
    ∃ h : (∫ v in a..b, F v) ∈ (B0121.fracPow j).domain,
      B0121.graphNormSq j ⟨_, h⟩ ≤ (∫ v in a..b, g v) ^ 2

/-- The induction step of the derivative budget. -/
theorem wGraphBound_succ {lam κ : ℂ} {W : ℝ → B0010.XG} (hDuh : WDuh lam κ W)
    (hcont : ContinuousOn W (Ioi 0)) {j : ℕ} (hfree : FreeTermGain lam κ j)
    (hint : IntegralTermGain lam κ j) (hj : WGraphBound W j) : WGraphBound W (j + 1) := by
  obtain ⟨C, b, hb, hW⟩ := hj
  obtain ⟨Cf, hCf, hF⟩ := hfree
  obtain ⟨Ci, hCi, hI⟩ := hint
  refine ⟨2 * (Cf + Ci) * |C| * (2 : ℝ) ^ ((j : ℝ) / 2), max b 1, lt_max_of_lt_right one_pos, ?_⟩
  intro θ hθ
  have hθb : b ≤ θ := le_trans (le_max_left _ _) hθ
  have hθ1 : 1 ≤ θ := le_trans (le_max_right _ _) hθ
  have hθ0 : 0 < θ := by linarith
  set M : ℝ := |C| * (2 + θ) ^ ((j : ℝ) / 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hsq : ∀ v ∈ Icc θ (θ + 1), ∃ h : W v ∈ (B0121.fracPow j).domain,
      B0121.graphNormSq j ⟨W v, h⟩ ≤ M ^ 2 := by
    intro v hv
    obtain ⟨h, hh⟩ := hW v (by linarith [hv.1])
    refine ⟨h, hh.trans ?_⟩
    have h1 : (1 + v) ^ ((j : ℝ) / 2) ≤ (2 + θ) ^ ((j : ℝ) / 2) :=
      Real.rpow_le_rpow (by linarith [hv.1]) (by linarith [hv.2]) (by positivity)
    have h2 : 0 ≤ (1 + v) ^ ((j : ℝ) / 2) := Real.rpow_nonneg (by linarith [hv.1]) _
    rw [hM, mul_pow, mul_pow, sq_abs]
    gcongr
  obtain ⟨hIm, hIb⟩ := hI θ hθ1 W hcont M hM0 hsq
  obtain ⟨h1m, h1b⟩ := hW (θ + 1) (by linarith)
  obtain ⟨hFm, hFb⟩ := hF θ hθ1 ⟨W (θ + 1), h1m⟩
  have hsplit : W θ = (1 : ℂ) • (cfac lam κ θ (θ + 1) • expD (Real.log (θ + 1) - Real.log θ)
        (W (θ + 1))) + (1 : ℂ) • (∫ v in θ..θ + 1, cfac lam κ θ v •
          expD (Real.log v - Real.log θ) (B0012.L0 (W v))) := by
    rw [one_smul, one_smul]
    exact hDuh θ (θ + 1) hθ0 (by linarith)
  have hmem : W θ ∈ (B0121.fracPow (j + 1)).domain := by
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hFm) (Submodule.smul_mem _ _ hIm)
  refine ⟨hmem, ?_⟩
  have e : (⟨W θ, hmem⟩ : (B0121.fracPow (j + 1)).domain) =
      (1 : ℂ) • (⟨_, hFm⟩ : (B0121.fracPow (j + 1)).domain) +
        (1 : ℂ) • (⟨_, hIm⟩ : (B0121.fracPow (j + 1)).domain) := Subtype.ext hsplit
  rw [e]
  refine (B0122.graphNormSq_combo (j + 1) 1 1 _ _).trans ?_
  simp only [norm_one, one_pow, mul_one]
  have hp : (0 : ℝ) ≤ (1 + θ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hFb' : B0121.graphNormSq (j + 1) ⟨_, hFm⟩ ≤ (Cf * (1 + θ) ^ (1 / 2 : ℝ)) ^ 2 * M ^ 2 :=
    hFb.trans (mul_le_mul_of_nonneg_left (by
      obtain ⟨h, hh⟩ := hsq (θ + 1) ⟨by linarith, le_rfl⟩
      exact hh) (by positivity))
  have hM2 : M ≤ |C| * (2 : ℝ) ^ ((j : ℝ) / 2) * (1 + θ) ^ ((j : ℝ) / 2) := by
    rw [hM, mul_assoc, ← Real.mul_rpow (by norm_num) (by linarith)]
    gcongr
    linarith
  set N : ℝ := |C| * (2 : ℝ) ^ ((j : ℝ) / 2) * (1 + θ) ^ ((j : ℝ) / 2) with hN
  have hN0 : 0 ≤ N := by positivity
  have hpj : (1 + θ) ^ (1 / 2 : ℝ) * (1 + θ) ^ ((j : ℝ) / 2) = (1 + θ) ^ (((j + 1 : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_add (by linarith)]
    congr 1
    push_cast
    ring
  have hfin : (2 * (Cf + Ci) * |C| * (2 : ℝ) ^ ((j : ℝ) / 2) *
        (1 + θ) ^ (((j + 1 : ℕ) : ℝ) / 2)) =
      2 * (Cf + Ci) * ((1 + θ) ^ (1 / 2 : ℝ) * N) := by
    rw [hN, ← hpj]; ring
  rw [hfin]
  have hMN : M ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hM0 hM2 2
  have hP : 0 ≤ (1 + θ) ^ (1 / 2 : ℝ) * N := by positivity
  have hPM : (1 + θ) ^ (1 / 2 : ℝ) * M ≤ (1 + θ) ^ (1 / 2 : ℝ) * N :=
    mul_le_mul_of_nonneg_left hM2 hp
  have hPM2 : ((1 + θ) ^ (1 / 2 : ℝ) * M) ^ 2 ≤ ((1 + θ) ^ (1 / 2 : ℝ) * N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hPM 2
  have hA : (Cf * (1 + θ) ^ (1 / 2 : ℝ)) ^ 2 * M ^ 2 ≤
      Cf ^ 2 * ((1 + θ) ^ (1 / 2 : ℝ) * N) ^ 2 :=
    calc _ = Cf ^ 2 * ((1 + θ) ^ (1 / 2 : ℝ) * M) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hPM2 (sq_nonneg _)
  have hB : (Ci * (1 + θ) ^ (1 / 2 : ℝ) * M) ^ 2 ≤
      Ci ^ 2 * ((1 + θ) ^ (1 / 2 : ℝ) * N) ^ 2 :=
    calc _ = Ci ^ 2 * ((1 + θ) ^ (1 / 2 : ℝ) * M) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hPM2 (sq_nonneg _)
  have hrhs : (2 * (Cf + Ci) * ((1 + θ) ^ (1 / 2 : ℝ) * N)) ^ 2 =
      4 * (Cf + Ci) ^ 2 * ((1 + θ) ^ (1 / 2 : ℝ) * N) ^ 2 := by ring
  rw [hrhs]
  nlinarith [mul_nonneg (mul_nonneg hCf.le hCi.le) (sq_nonneg ((1 + θ) ^ (1 / 2 : ℝ) * N))]

/-- **Derivative budget from its pieces**: the `j = 0` bound, the Duhamel identity for `W`, and the
two one-derivative gains give `WGraphBound W j` for every `j` (source lines 1139-1146). -/
theorem wGraphBound_of {lam κ : ℂ} {W : ℝ → B0010.XG} (hDuh : WDuh lam κ W)
    (hcont : ContinuousOn W (Ioi 0)) (h0 : WGraphBound W 0)
    (hfree : ∀ j, FreeTermGain lam κ j) (hint : ∀ j, IntegralTermGain lam κ j) :
    ∀ j, WGraphBound W j := by
  intro j
  induction j with
  | zero => exact h0
  | succ j ih => exact wGraphBound_succ hDuh hcont (hfree j) (hint j) ih

end UnforcedLeray.Short.PartI
