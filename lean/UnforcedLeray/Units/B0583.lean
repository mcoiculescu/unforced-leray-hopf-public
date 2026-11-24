import UnforcedLeray.Units.B0583.ZeroVel
import UnforcedLeray.Units.B0583.Gradient
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# B0583 `prepared:p1.4`: velocity reconstruction from weighted vorticity

Blueprint unit **B0583** (label `prepared:p1.4`), `paper/main.tex` lines 9405–9433
(Section P1, "Weighted negative sources and velocity reconstruction"):

> If `ω ∈ X_m` has zero total circulation and `m > 1`, decompose into horizontal mean and
> nonzero modes. For `k ≠ 0`, the Biot–Savart multiplier has modulus at most
> `|k|^{-1} ≤ c/(2π)` [...]. For `k = 0`, the velocity is a primitive of `ω̄(η)`. Its limits at
> both ends are zero by zero total circulation. The one-dimensional Hardy inequality gives
> [`prepared:p1.3`] [...]. The gradient is bounded by the Fourier multiplier of order zero.
> Hence `‖K_c ω‖_{H¹} ≤ C(1 + c)‖ω‖_{X_m}`.

Dependencies: `B0579` (`X_m`, cylinder test functions, `paper/main.tex:9370-9387`), `B0581`
(nonzero-mode Biot–Savart bound, lines 9407–9412), `B0582` (one-dimensional Hardy inequality,
`prepared:p1.3`, lines 9412–9425).

## The velocity `K_c ω`

`K_c = ∇^⊥Δ^{-1}` on the cylinder `(ℝ/cℤ) × ℝ`, `∇^⊥ = (-∂_η, ∂_q)` (`paper/main.tex:2138`),
computed on the cell `[-c/2, c/2) × ℝ` with unnormalized Lebesgue measure (`cellVol c`).
`velocity c hm ω hcirc` is the sum of

* the nonzero-mode velocity `K_c ω_ne = B0581.velNe c (nonzeroPart c ω)`: the series
  `∑_{k ≠ 0} (√c)⁻¹ e^{2πikq/c} 𝓕⁻¹(bsSymbol c k · 𝓕 (√c ω_k))(η)` of `B0581`;
* the zero-mode velocity `zeroVelLp`: `(-F(η), 0)` with `F(η) = ∫_{-∞}^η ω̄` and
  `ω̄(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq` (`B0583/ZeroMode.lean`, `B0583/ZeroVel.lean`): this is
  `∇^⊥ψ` for the zero-mode stream function `ψ'' = ω̄`.

`velocity_spec` records this description (including the vanishing of `F` at both ends).

## The `H¹` norm

The velocity is `ℂ²`-valued (as in `B0581`; for real `ω` it is the complexification of the
real velocity, which is not needed for the bound and is not proved). `HasWeakVelDeriv c j u g`
says that `g` is the distributional derivative `∂_j u` on the cylinder, componentwise, tested
against all cylinder test functions (`B0579.IsCylTest`): `∫_cell ∂_jφ · u_i = -∫_cell φ · g_i`
(the integrals converge absolutely, `integrable_testLp_mul`, so no junk value enters). For a field
`u` with weak gradient `(g_q, g_η)` its `H¹(cell)` norm is
`h1Norm u g_q g_η = (‖u‖₂² + ‖g_q‖₂² + ‖g_η‖₂²)^{1/2}`.

The weak gradient of `K_c ω` is `velGradQ` (`∂_q`: the order-zero multiplier `iκ_k · bsSymbol`
on the nonzero modes, `B0583/Gradient.lean`) and `velGradEta` (`∂_η`: the order-zero multiplier
`2πiξ · bsSymbol` on the nonzero modes plus `(-ω̄(η), 0)` from the zero mode).

## Main results

* `hasWeakVelDeriv_velocity_q`, `hasWeakVelDeriv_velocity_eta`: the weak-gradient identities.
* `norm_velocity_le` (`‖K_c ω‖₂ ≤ (c/2π + 2)‖ω‖_{X_m}`), `norm_velGradQ_le` (`≤ ‖ω‖_{X_m}`),
  `norm_velGradEta_le` (`≤ 2‖ω‖_{X_m}`).
* `h1Norm_velocity_le`: `‖K_c ω‖_{H¹} ≤ 5(1 + c)‖ω‖_{X_m}`.
* `velocity_reconstruction` (**`prepared:p1.4`**, `paper/main.tex:9427-9431`): there is one
  constant `C` (`C = 5`), independent of `c`, `m` and `ω`, such that for every `c > 0`, `m > 1`
  and `ω ∈ X_m` with zero total circulation, `K_c ω` has a weak gradient in `L²(cell)` and
  `‖K_c ω‖_{H¹} ≤ C(1 + c)‖ω‖_{X_m}`.

## Hypotheses made explicit

`c > 0` (the manuscript's `c = ν^{-ρ}`) is the instance `[Fact (0 < c)]`. Zero total circulation
is `∫_cell ω = 0`; for `m ≥ 1` the integral converges absolutely (`integrable_of_X`), so this
is not a Bochner junk value. The definitions and all intermediate facts need only `m ≥ 1`;
`velocity_reconstruction` assumes the manuscript's `m > 1`. No hypothesis is stronger than the
manuscript's.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate

namespace UnforcedLeray.B0583

open B0581

/-! ### Weak derivatives and the `H¹` norm of `ℂ²`-valued fields on the cylinder -/

/-- `g = ∂_j u` in the sense of distributions on the cylinder `(ℝ/cℤ) × ℝ`, componentwise:
`∫_cell ∂_jφ · u_i = -∫_cell φ · g_i` for every cylinder test function `φ` and `i ∈ {0, 1}`
(`j = 0`: `∂_q`, `j = 1`: `∂_η`; the complex analogue of `B0579.HasWeakCellDeriv`). -/
def HasWeakVelDeriv (c : ℝ) (j : Fin 2) (u g : Lp Vel 2 (cellVol c)) : Prop :=
  ∀ φ : B0579.Plane → ℝ, B0579.IsCylTest c φ → ∀ i : Fin 2,
    ∫ x, (B0579.pd j φ x : ℂ) * (u x : Vel) i ∂cellVol c =
      -∫ x, (φ x : ℂ) * (g x : Vel) i ∂cellVol c

theorem hasWeakVelDeriv_iff_inner (c : ℝ) (j : Fin 2) (u g : Lp Vel 2 (cellVol c)) :
    HasWeakVelDeriv c j u g ↔ ∀ (φ : B0579.Plane → ℝ) (hφ : B0579.IsCylTest c φ) (i : Fin 2),
      ⟪testLp c (hφ.pd j) i, u⟫_ℂ = -⟪testLp c hφ i, g⟫_ℂ := by
  simp only [HasWeakVelDeriv, inner_testLp]

/-- The `H¹(cell)` norm `(‖u‖₂² + ‖∂_q u‖₂² + ‖∂_η u‖₂²)^{1/2}` of a field `u` with weak
gradient `(g_q, g_η)` (`HasWeakVelDeriv`). -/
def h1Norm {c : ℝ} (u gq geta : Lp Vel 2 (cellVol c)) : ℝ :=
  Real.sqrt (‖u‖ ^ 2 + ‖gq‖ ^ 2 + ‖geta‖ ^ 2)

/-! ### The velocity `K_c ω` and its gradient -/

section Velocity

variable (c : ℝ) [hc : Fact (0 < c)] {m : ℝ}

/-- **The velocity `K_c ω`** of `ω ∈ X_m` (`m ≥ 1`, zero total circulation): the Biot–Savart
velocity of the nonzero modes (`B0581.velNe`) plus that of the horizontal mean, `(-∫_{-∞}^η ω̄, 0)`
(`paper/main.tex:9407-9414`). -/
def velocity (hm : 1 ≤ m) (ω : B0579.X c m) (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    Lp Vel 2 (cellVol c) :=
  velNe c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω)) + zeroVelLp c hm ω hcirc

/-- `∂_q K_c ω`: the order-zero multiplier `iκ_k · bsSymbol c k` on the nonzero modes (the zero
mode does not depend on `q`). -/
def velGradQ (hm : 1 ≤ m) (ω : B0579.X c m) : Lp Vel 2 (cellVol c) :=
  gradQ c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω))

/-- `∂_η K_c ω`: the order-zero multiplier `2πiξ · bsSymbol c k` on the nonzero modes, plus
`(-ω̄(η), 0)` from the zero mode. -/
def velGradEta (hm : 1 ≤ m) (ω : B0579.X c m) (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    Lp Vel 2 (cellVol c) :=
  gradEta c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω)) + zeroVelEtaLp c hm ω hcirc

/-- **What `K_c ω` is** (`paper/main.tex:9407-9414`): the nonzero-mode velocity plus the zero-mode
velocity; the zero-mode velocity is `(-F(η), 0)` a.e. with `F(η) = ∫_{-∞}^η ω̄`,
`ω̄(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq`, and `F → 0` at both ends (zero total circulation); the
nonzero-mode velocity has vanishing mean mode and, for `k ≠ 0`, `η`-Fourier transform of its
`k`-th mode equal to the Biot–Savart symbol times that of the `k`-th vorticity mode. -/
theorem velocity_spec (hm : 1 ≤ m) (ω : B0579.X c m) (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    velocity c hm ω hcirc =
        velNe c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω)) + zeroVelLp c hm ω hcirc ∧
      ((zeroVelLp c hm ω hcirc : Lp Vel 2 (cellVol c)) : B0579.Plane → Vel) =ᵐ[cellVol c]
        (fun x => ((-B0582.zeroModePrimitive (omegaBar c ω) x.2 : ℝ) : ℂ) •
          EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) ∧
      (∀ η, omegaBar c ω η = c⁻¹ * ∫ q in qInt c, ω (q, η)) ∧
      (∀ η, B0582.zeroModePrimitive (omegaBar c ω) η = ∫ y in Iic η, omegaBar c ω y) ∧
      Tendsto (B0582.zeroModePrimitive (omegaBar c ω)) atBot (𝓝 0) ∧
      Tendsto (B0582.zeroModePrimitive (omegaBar c ω)) atTop (𝓝 0) ∧
      (modes c (velNe c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω))) : ModeSeq Vel) 0 = 0 ∧
      ∀ k : ℤ, k ≠ 0 →
        ((𝓕 ((modes c (velNe c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω))) :
            ModeSeq Vel) k) : Lp Vel 2 (volume : Measure ℝ)) : ℝ → Vel) =ᵐ[volume]
          fun ξ => ((𝓕 ((modes c (ofX c m (zero_le_one.trans hm) ω) : ModeSeq ℂ) k) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ • bsSymbol c k ξ := by
  obtain ⟨-, -, hbot, htop, -, -, -⟩ := zeroMode_facts hc.out hm ω hcirc
  refine ⟨rfl, coeFn_zeroVelLp c hm ω hcirc, fun η => rfl, fun η => rfl, hbot, htop,
    modes_velNe_zero c _, fun k hk => ?_⟩
  have h := fourier_modes_velNe c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω)) hk
  rw [modes_nonzeroPart, ite_eq_right hk] at h
  exact h

/-- `∂_q K_c ω = velGradQ` weakly on the cylinder. -/
theorem hasWeakVelDeriv_velocity_q (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    HasWeakVelDeriv c 0 (velocity c hm ω hcirc) (velGradQ c hm ω) := by
  rw [hasWeakVelDeriv_iff_inner]
  intro φ hφ i
  rw [velocity, velGradQ, inner_add_right, inner_pd0_velNe c hφ i,
    inner_pd0_zeroVelLp c hm ω hcirc hφ i, add_zero]

/-- `∂_η K_c ω = velGradEta` weakly on the cylinder. -/
theorem hasWeakVelDeriv_velocity_eta (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    HasWeakVelDeriv c 1 (velocity c hm ω hcirc) (velGradEta c hm ω hcirc) := by
  rw [hasWeakVelDeriv_iff_inner]
  intro φ hφ i
  rw [velocity, velGradEta, inner_add_right, inner_add_right, inner_pd1_velNe c hφ i,
    inner_pd1_zeroVelLp c hm ω hcirc hφ i, neg_add]

/-! ### Norm bounds -/

/-- `‖K_c ω‖_{L²(cell)} ≤ (c/2π + 2)‖ω‖_{X_m}`: `B0581` for the nonzero modes, Hardy (`B0582`)
for the zero mode. -/
theorem norm_velocity_le (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    ‖velocity c hm ω hcirc‖ ≤ (c / (2 * π) + 2) * ‖ω‖ := by
  have h1 := norm_velNe_nonzeroPart_le c (ofX c m (zero_le_one.trans hm) ω)
  have h2 := norm_ofX_le c m (zero_le_one.trans hm) ω
  have h3 := norm_zeroVelLp_le c hm ω hcirc
  have hC : 0 ≤ c / (2 * π) := by have := hc.out; positivity
  calc ‖velocity c hm ω hcirc‖
      ≤ ‖velNe c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω))‖ +
          ‖zeroVelLp c hm ω hcirc‖ := norm_add_le _ _
    _ ≤ c / (2 * π) * ‖ω‖ + 2 * ‖ω‖ :=
        add_le_add (h1.1.trans (h1.2.trans (mul_le_mul_of_nonneg_left h2 hC))) h3
    _ = (c / (2 * π) + 2) * ‖ω‖ := by ring

/-- `‖∂_q K_c ω‖_{L²(cell)} ≤ ‖ω‖_{X_m}` (order-zero multiplier). -/
theorem norm_velGradQ_le (hm : 1 ≤ m) (ω : B0579.X c m) : ‖velGradQ c hm ω‖ ≤ ‖ω‖ :=
  (norm_gradQ_le c _).trans ((norm_nonzeroPart_le c _).trans
    (norm_ofX_le c m (zero_le_one.trans hm) ω))

/-- `‖∂_η K_c ω‖_{L²(cell)} ≤ 2‖ω‖_{X_m}` (order-zero multiplier plus the zero mode). -/
theorem norm_velGradEta_le (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) : ‖velGradEta c hm ω hcirc‖ ≤ 2 * ‖ω‖ := by
  calc ‖velGradEta c hm ω hcirc‖
      ≤ ‖gradEta c (nonzeroPart c (ofX c m (zero_le_one.trans hm) ω))‖ +
          ‖zeroVelEtaLp c hm ω hcirc‖ := norm_add_le _ _
    _ ≤ ‖ω‖ + ‖ω‖ :=
        add_le_add ((norm_gradEta_le c _).trans ((norm_nonzeroPart_le c _).trans
          (norm_ofX_le c m (zero_le_one.trans hm) ω))) (norm_zeroVelEtaLp_le c hm ω hcirc)
    _ = 2 * ‖ω‖ := by ring

/-- **`‖K_c ω‖_{H¹} ≤ 5(1 + c)‖ω‖_{X_m}`** for `m ≥ 1` and zero total circulation. -/
theorem h1Norm_velocity_le (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    h1Norm (velocity c hm ω hcirc) (velGradQ c hm ω) (velGradEta c hm ω hcirc) ≤
      5 * (1 + c) * ‖ω‖ := by
  have hcpos := hc.out
  have hW := norm_nonneg ω
  have hpi : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have hc2 : c / (2 * π) ≤ c := div_le_self hcpos.le hpi
  have ha : ‖velocity c hm ω hcirc‖ ≤ (c + 2) * ‖ω‖ :=
    (norm_velocity_le c hm ω hcirc).trans (by gcongr)
  have hb := norm_velGradQ_le c hm ω
  have hd := norm_velGradEta_le c hm ω hcirc
  have ha2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [h1Norm, Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg hcpos.le (sq_nonneg ‖ω‖), mul_nonneg (sq_nonneg c) (sq_nonneg ‖ω‖),
    sq_nonneg ‖ω‖]

end Velocity

/-! ### The unit in the manuscript's form -/

/-- **B0583, `prepared:p1.4`** (`paper/main.tex:9405-9433`). There is a constant `C` (here
`C = 5`), independent of `c`, such that for every `c > 0`, `m > 1` and `ω ∈ X_m` with zero total
circulation `∫_cell ω = 0`, the velocity `K_c ω` (`velocity`: nonzero modes by the Biot–Savart
multiplier, zero mode `(-∫_{-∞}^η ω̄, 0)`) has the weak gradient `(velGradQ, velGradEta)` in
`L²(cell)` and `‖K_c ω‖_{H¹} ≤ C(1 + c)‖ω‖_{X_m}`. -/
theorem velocity_reconstruction :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) [Fact (0 < c)] (m : ℝ) (hm : 1 < m) (ω : B0579.X c m)
      (hcirc : ∫ x in B0579.cell c, ω x = 0),
      HasWeakVelDeriv c 0 (velocity c hm.le ω hcirc) (velGradQ c hm.le ω) ∧
      HasWeakVelDeriv c 1 (velocity c hm.le ω hcirc) (velGradEta c hm.le ω hcirc) ∧
      h1Norm (velocity c hm.le ω hcirc) (velGradQ c hm.le ω) (velGradEta c hm.le ω hcirc) ≤
        C * (1 + c) * ‖ω‖ :=
  ⟨5, by norm_num, fun c _ _ hm ω hcirc =>
    ⟨hasWeakVelDeriv_velocity_q c hm.le ω hcirc, hasWeakVelDeriv_velocity_eta c hm.le ω hcirc,
      h1Norm_velocity_le c hm.le ω hcirc⟩⟩

end UnforcedLeray.B0583
