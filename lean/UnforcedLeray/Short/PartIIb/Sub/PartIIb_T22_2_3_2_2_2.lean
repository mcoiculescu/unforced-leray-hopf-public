import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2085-2093 (bounded drift
derivatives of orders `≤ 2`) and 2100-2105 (estimates for the regular backward problem).

Same scheme as `PartIIb_T22_2_3_2_2_1.lean` with
`Z_{η₀} = ζ_{η₀}(Δφ)² + μ|∇φ|² + κφ²`.  Differentiating the equation twice (`BwdOpPd`) gives
`L(Δφ) = -Σ_k (∂_k²b·∇φ + ∂_k b·∇∂_kφ + ∂_k b·∂_k∇φ)`; then
`L((Δφ)²) = 2Δφ L(Δφ) + 2ν|∇Δφ|²`, the cutoff cross term is absorbed by `ζ|∇Δφ|²` and `θ'² ≤ Cθ`,
the `|D²φ|²` terms by `μ L|∇φ|² ≥ 2μν|D²φ|² - 4μV|∇φ|²`, the `|∇φ|²` terms by `κ L(φ²)`.
`|∇φ|²` is bounded (the gradient hypothesis of `BwdWeightedLap` with `N = 0`), so `Z_{η₀}` is
bounded above.  `localized_decay` with `Q = (Δφ)²` gives the target (`bwdWeightedLap_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- `(Δφ)²` as a function of `(r, x)`. -/
def lapSq (φ : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) : ℝ :=
  lapP (φ r) x * lapP (φ r) x

/-- The localized Bernstein quantity `ζ_{η₀}(Δφ)² + μ|∇φ|² + κφ²`. -/
def lapZ (mu kap η0 : ℝ) (φ : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) : ℝ :=
  cutζ η0 x * lapSq φ r x + (mu * gradSq φ r x + kap * (φ r x * φ r x))

/-- **Leaf `/1`**: the pointwise algebra of the Laplacian Bernstein computation.  With
`ℓ = H₀₀ + H₁₁` (`= Δφ`), `g = ∇Δφ`, `e_{kj} = ∂_k²b_j`, `S = Σ H_{kj}²`, `P = p₀² + p₁²` and
`G = G₀ + G₁` the value of `L(Δφ)`: `2ζℓG ≥ -(ℓ² + G²)`, `G² ≤ 16V²P + 32V²S`,
`2νζ|g|² + 4νℓ z·g ≥ -2νCℓ²` (sum of squares `Σ(ζg_k + z_kℓ)²`, `|z|² ≤ Cζ`),
`ℓ²·Lζ ≥ -ℓ²(νC + V(1+C))`, `ℓ² ≤ 2S`, `μ(2p·F + 2νS) ≥ μ(2νS - 4VP)`. -/
def HessAlg : Prop :=
  ∀ (ν V Cθ mu kap ζ z0 z1 lz b0 b1 d00 d01 d10 d11 e00 e01 e10 e11 p0 p1 H00 H01 H10 H11
      g0 g1 : ℝ),
    0 < ν → 0 ≤ V → 0 ≤ Cθ → 0 ≤ ζ → ζ ≤ 1 → z0 ^ 2 + z1 ^ 2 ≤ Cθ * ζ → |lz| ≤ Cθ →
    |b0| ≤ V → |b1| ≤ V → |d00| ≤ V → |d01| ≤ V → |d10| ≤ V → |d11| ≤ V →
    |e00| ≤ V → |e01| ≤ V → |e10| ≤ V → |e11| ≤ V →
    32 * V ^ 2 + 2 + 6 * ν * Cθ + 2 * V + 2 * V * Cθ ≤ 2 * ν * mu →
    16 * V ^ 2 + 4 * V * mu ≤ 2 * ν * kap →
    0 ≤ ζ * (2 * (H00 + H11) *
            ((-(e00 * p0 + d00 * H00 + e01 * p1 + d01 * H01) - (d00 * H00 + d01 * H10)) +
              (-(e10 * p0 + d10 * H10 + e11 * p1 + d11 * H11) - (d10 * H01 + d11 * H11))) +
          2 * ν * (g0 ^ 2 + g1 ^ 2)) +
        (H00 + H11) ^ 2 * (ν * lz + (b0 * z0 + b1 * z1)) +
        2 * ν * (z0 * (2 * (H00 + H11) * g0) + z1 * (2 * (H00 + H11) * g1)) +
        mu * (2 * p0 * (-(d00 * p0 + d01 * p1)) + 2 * ν * (H00 ^ 2 + H10 ^ 2) +
          (2 * p1 * (-(d10 * p0 + d11 * p1)) + 2 * ν * (H01 ^ 2 + H11 ^ 2))) +
        kap * (2 * ν * (p0 ^ 2 + p1 ^ 2))

/-- **Leaf `/2`** (SP 2100-2105): the localized Laplacian quantity is a subsolution of the
backward operator, for `μ, κ` independent of the centre `η₀`. -/
def LapLocalSub : Prop :=
  ∀ (ν c s t V : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ψ : B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ), 0 < ν → 0 ≤ V → DriftSmoothBdd v s t V →
    BwdSol ν c s t v ψ φ →
    ∃ mu kap : ℝ, 0 ≤ mu ∧ 0 ≤ kap ∧ ∀ η0 : ℝ, ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
      ∃ F : ℝ, 0 ≤ F ∧
        BwdOpAt ν (fun r x => v r x 0) (fun r x => v r x 1) (lapZ mu kap η0 φ) r x F

/-- **Leaf `/3`**: regularity, periodicity and an upper bound for the Laplacian family (given a
global bound on `|∇φ|²`). -/
def LapZRegular : Prop :=
  ∀ (ν c s t : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ψ : B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ), 0 < c → BwdSol ν c s t v ψ φ →
    (∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, gradSq φ r x ≤ C) →
    ∀ mu kap : ℝ, 0 ≤ mu → ∀ η0 : ℝ,
    ContinuousOn (fun z : ℝ × B0579.Plane => lapZ mu kap η0 φ z.1 z.2) (Icc s t ×ˢ univ) ∧
    (∀ r ∈ Ioo s t, ContDiff ℝ 2 (lapZ mu kap η0 φ r)) ∧
    (∀ r ∈ Icc s t, ∀ x : B0579.Plane,
      lapZ mu kap η0 φ r (x.1 + c, x.2) = lapZ mu kap η0 φ r x) ∧
    ∃ M : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, lapZ mu kap η0 φ r x ≤ M

/-- **Leaf `/4`**: the terminal values of the Laplacian family are uniformly bounded and vanish
for `|η| > R`. -/
def LapZTerminal : Prop :=
  ∀ (ν c s t : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ψ : B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ), 0 < c → B0579.IsCylTest c ψ → BwdSol ν c s t v ψ φ →
    ∀ mu kap : ℝ, ∃ M R : ℝ, ∀ η0 : ℝ, ∀ x : B0579.Plane,
      lapZ mu kap η0 φ t x ≤ M ∧ (R < |x.2| → lapZ mu kap η0 φ t x ≤ 0)

/-- `BwdWeightedLap` from the leaves. -/
theorem bwdWeightedLap_of (hMP : BwdMaxPrincipleSub) (hB : BwdBarrier)
    (hD : TrainDriftSmoothBdd) (hLS : LapLocalSub) (hLR : LapZRegular) (hLT : LapZTerminal)
    (hcut : CutProps) : BwdWeightedLap := by
  intro Sg ν c δ V hSg hν hc hδ tr htr hV2 s t hs hst ht ψ hψ φ hφ _hW hG
  have hDS := hD Sg ν c V tr hV2 s t hs ht
  have hV0 : 0 ≤ V := le_trans (abs_nonneg _) (hDS.2 s ⟨le_rfl, hst⟩ (0, 0) 0).1
  have hgb : ∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, gradSq φ r x ≤ C := by
    obtain ⟨C0, hC0⟩ := hG 0
    refine ⟨C0 ^ 2, fun r hr x => ?_⟩
    have h := hC0 r hr x
    simp only [Real.rpow_zero, mul_one] at h
    simp only [gradSq]
    generalize B0579.pd 0 (φ r) x = p0 at h ⊢
    generalize B0579.pd 1 (φ r) x = p1 at h ⊢
    have h1 := abs_nonneg p0
    have h2 := abs_nonneg p1
    nlinarith [sq_abs p0, sq_abs p1, mul_nonneg h1 h2,
      mul_le_mul h h (add_nonneg h1 h2) (le_trans (add_nonneg h1 h2) h)]
  obtain ⟨mu, kap, hmu0, hkap0, hsub⟩ := hLS ν c s t V tr.v ψ φ hν hV0 hDS hφ
  obtain ⟨M, R, hMR⟩ := hLT ν c s t tr.v ψ φ hc hψ hφ mu kap
  have hreg := hLR ν c s t tr.v ψ φ hc hφ hgb mu kap hmu0
  have hdec := localized_decay hMP hB ν c s t V (fun r x => tr.v r x 0) (fun r x => tr.v r x 1)
    hν hc hst hV0 (fun r hr x => ⟨(hDS.2 r hr x 0).1, (hDS.2 r hr x 1).1⟩)
    (fun η0 => lapZ mu kap η0 φ) (fun η0 => (hreg η0).1) (fun η0 => (hreg η0).2.1)
    (fun η0 => (hreg η0).2.2.1) (fun η0 => (hreg η0).2.2.2) hsub M R hMR (lapSq φ)
    (fun r _ x => by
      have h1 : cutζ x.2 x = 1 := by simp [cutζ, hcut.2.1]
      have h2 : 0 ≤ mu * gradSq φ r x :=
        mul_nonneg hmu0 (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      have h3 : 0 ≤ kap * (φ r x * φ r x) := mul_nonneg hkap0 (mul_self_nonneg _)
      show lapSq φ r x ≤ cutζ x.2 x * lapSq φ r x + (mu * gradSq φ r x + kap * (φ r x * φ r x))
      rw [h1, one_mul]; linarith)
  intro N
  obtain ⟨C, hC⟩ := hdec (2 * N)
  refine ⟨1 + C, fun r hr x => ?_⟩
  have hw0 : 0 ≤ (1 + x.2 ^ 2) ^ N := by positivity
  have hw2 : (1 + x.2 ^ 2) ^ (2 * N) = ((1 + x.2 ^ 2) ^ N) ^ 2 := by
    rw [show (2 : ℝ) * N = N * 2 by ring, Real.rpow_mul (by positivity), Real.rpow_two]
  have hCx := hC r hr x
  rw [hw2] at hCx
  simp only [lapSq] at hCx
  generalize lapP (φ r) x = l at hCx ⊢
  generalize (1 + x.2 ^ 2) ^ N = w at hCx hw0 ⊢
  have hq : (|l| * w) ^ 2 = l * l * w ^ 2 := by rw [mul_pow, sq_abs]; ring
  nlinarith [sq_nonneg (|l| * w - 1), sq_nonneg (|l| * w)]

end UnforcedLeray.Short.IIb
